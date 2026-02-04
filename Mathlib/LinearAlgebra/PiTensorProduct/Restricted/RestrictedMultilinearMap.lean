import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

section FiniteSet

abbrev FiniteSet (ι : Type*) := { S : Set ι // Finite ↑S }

variable {ι : Type*}

instance : IsDirectedOrder (FiniteSet ι) where
  directed a b := by
    use ⟨a.val ∪ b.val, by aesop (add safe apply Set.Finite.to_subtype)⟩
    aesop

instance : Nonempty (FiniteSet ι) := ⟨∅, Finite.of_subsingleton⟩

noncomputable instance decidable :
    ∀ s : FiniteSet ι, ∀ m : ι, Decidable (m ∈ s.val) := fun s m =>
  Classical.propDecidable (m ∈ s.val)

end FiniteSet


open RestrictedProduct Filter

namespace RestrictedProduct

variable {ι : Type*} [DecidableEq ι]
variable {E : ι → Type*} {R : Type*} {E₀ : (i : ι) → E i}

lemma update_restricted (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) :
    ∀ᶠ (j : ι) in cofinite, Function.update f i v j ∈ (fun i ↦ ({E₀ i} : Set (E i))) j := by
  simp only [Set.mem_singleton_iff, eventually_cofinite]
  apply Set.Finite.subset (s := ({j | f j ≠ E₀ j} ∪ {i}))
  · simpa using f.prop
  · intro j _
    by_cases j = i <;> simp_all

def update (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) : Πʳ i, [E i, {E₀ i}] :=
  ⟨Function.update f i v, update_restricted ..⟩

@[simp]
lemma update_eq_function_update (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) :
  (update f i v).val = Function.update f i v := rfl

@[simp]
lemma update_apply (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) (j : ι) :
  (update f i v) j = Function.update f i v j := rfl

variable (E₀)
noncomputable def finiteSetMap {S : FiniteSet ι} (f : Π i : S.val, E i) : Πʳ i, [E i, {E₀ i}] :=
  ⟨fun i ↦ if h : i ∈ S.val then f ⟨i, h⟩ else E₀ i, by
    simp only [Set.mem_singleton_iff, dite_eq_right_iff, eventually_cofinite, not_forall]
    exact Set.Finite.subset S.prop (fun _ hi => hi.choose)
  ⟩

omit [DecidableEq ι] in
@[simp]
lemma finiteSetMap_apply {S : FiniteSet ι} (f : Π i : S.val, E i) (i) :
  finiteSetMap E₀ f i = if h : i ∈ S.val then f ⟨i, h⟩ else E₀ i := rfl

@[simp]
lemma finiteSetMap_update {S : FiniteSet ι} [DecidableEq ↑↑S] (f : Π i : S.val, E i) (i v) :
    finiteSetMap E₀ (Function.update f i v) = update (finiteSetMap E₀ f) i v := by
  ext j
  by_cases h : j = i <;> aesop

end RestrictedProduct


variable {ι : Type*} {E : ι → Type*} (R : Type*) {S : Type*} (E₀ : (i : ι) → E i) (M : Type*)
  [AddCommMonoid M] [Semiring R] [Module R M] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]

structure RestrictedMultilinearMap where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : Πʳ i, [E i, {E₀ i}] → M
  /-- A restricted multilinear map is additive in every argument. -/
  map_update_add' :
    ∀ [DecidableEq ι] (m : Πʳ i, [E i, {E₀ i}]) (i : ι) (x y : E i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A restricted multilinear map is compatible with scalar multiplication in every argument. -/
  map_update_smul' :
    ∀ [DecidableEq ι] (m : Πʳ i, [E i, {E₀ i}]) (i : ι) (c : R) (x : E i),
      toFun (update m i (c • x)) = c • toFun (update m i x)

namespace RestrictedMultilinearMap

section instances

instance : FunLike (RestrictedMultilinearMap R E₀ M) (Πʳ (i : ι), [E i, {E₀ i}]) M where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; cases h; rfl

variable {R} {E₀} {M} in
theorem coe_injective :
    Function.Injective ((↑) : RestrictedMultilinearMap R E₀ M → (Πʳ (i : ι), [E i, {E₀ i}]) → M) :=
  DFunLike.coe_injective

variable (f : RestrictedMultilinearMap R E₀ M)

@[simp]
protected theorem map_update_add [DecidableEq ι]
    (m : Πʳ i, [E i, {E₀ i}]) (i : ι) (x y : E i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

@[simp]
protected theorem map_update_smul [DecidableEq ι]
    (m : Πʳ (i : ι), [E i, {E₀ i}]) (i : ι) (c : R) (x : E i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x

instance : Add (RestrictedMultilinearMap R E₀ M) :=
  ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc],
      fun m i c x => by simp [smul_add]⟩⟩

instance : Zero (RestrictedMultilinearMap R E₀ M) :=
  ⟨⟨fun _ => 0, fun _ _ _ _ => by simp, fun _ _ c _ => by simp⟩⟩

instance : Inhabited (RestrictedMultilinearMap R E₀ M) :=
  ⟨0⟩

instance [DistribSMul S M] [SMulCommClass R S M] : SMul S (RestrictedMultilinearMap R E₀ M) :=
  ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M)]⟩⟩

variable {R} {E₀} {M} in
theorem coe_smul [DistribSMul S M] [SMulCommClass R S M]
  (c : S) (f : RestrictedMultilinearMap R E₀ M) : ⇑(c • f) = c • (⇑f) := rfl

instance addCommMonoid : AddCommMonoid (RestrictedMultilinearMap R E₀ M) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

variable {R} {E₀} {M} in
@[simps] def coeAddMonoidHom : RestrictedMultilinearMap R E₀ M →+
    ((Πʳ (i : ι), [E i, {E₀ i}]) → M) where
  toFun := DFunLike.coe; map_zero' := rfl; map_add' _ _ := rfl

instance [Monoid S] [DistribMulAction S M] [Module R M] [SMulCommClass R S M] :
    DistribMulAction S (RestrictedMultilinearMap R E₀ M) := fast_instance%
  coe_injective.distribMulAction coeAddMonoidHom fun _ _ ↦ rfl

variable [Semiring S] [Module S M] [SMulCommClass R S M]

instance : Module S (RestrictedMultilinearMap R E₀ M) := fast_instance%
  coe_injective.module _ coeAddMonoidHom fun _ _ ↦ rfl

instance [Module.IsTorsionFree S M] : Module.IsTorsionFree S (RestrictedMultilinearMap R E₀ M) :=
  coe_injective.moduleIsTorsionFree _ coe_smul

variable {M : Type*} [AddCommGroup M] [∀ i, Module R (E i)] [Module R M]

instance : Neg (RestrictedMultilinearMap R E₀ M) :=
  ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩

instance : Sub (RestrictedMultilinearMap R E₀ M) :=
  ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [RestrictedMultilinearMap.map_update_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [RestrictedMultilinearMap.map_update_smul, smul_sub]⟩⟩

instance : AddCommGroup (RestrictedMultilinearMap R E₀ M) := fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

end instances

@[ext]
theorem ext {f f' : RestrictedMultilinearMap R E₀ M} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

variable {E : ι → Type*} {R : Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
variable {E₀ : (i : ι) → E i} [Module R M]

variable {M} in
@[simps]
noncomputable def toMultilinearMap (S : FiniteSet ι) :
    RestrictedMultilinearMap R E₀ M →ₗ[R] MultilinearMap R (fun i : S.val => E i) M :=
  {
    toFun ml := {
      toFun v := ml (finiteSetMap E₀ v)
      map_update_add'  := by classical simp
      map_update_smul' := by classical simp
    }
    map_add' := by aesop
    map_smul' := by aesop
  }

end RestrictedMultilinearMap

namespace LinearMap

variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
variable {R E₀ M} in
def compRestrictedMultilinearMap (g : M →ₗ[R] M₂) (f : RestrictedMultilinearMap R E₀ M)
    : RestrictedMultilinearMap R E₀ M₂ where
  toFun := g ∘ f
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

@[simp]
theorem compRestrictedMultilinearMap_apply
    (g : M →ₗ[R] M₂) (f : RestrictedMultilinearMap R E₀ M) (v : Πʳ i, [E i, {E₀ i}]) :
  g.compRestrictedMultilinearMap f v = g (f v) := rfl

end LinearMap
