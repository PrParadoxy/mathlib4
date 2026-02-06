import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Restricted.RestrictedMultilinearMap
import Mathlib.LinearAlgebra.PiTensorProduct.Basis




open PiTensorProduct RestrictedProduct
open scoped TensorProduct

variable {ι : Type*}
variable {E : ι → Type*} {R : Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
variable (E₀ : (i : ι) → E i)

instance directedSystem : DirectedSystem
    (fun S : FiniteSet ι ↦ ⨂[R] (i : S.val), E i)
    (fun _ _ hsub ↦ extendTensor hsub E₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor h2 E₀)]
    apply congrFun
    simp [←LinearMap.coe_comp]

variable (R) in
abbrev RestrictedTensor :=
  DirectLimit (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i) (fun _ _ hsub ↦ extendTensor hsub E₀)


namespace RestrictedTensor

noncomputable section

variable (M : Type*) [AddCommMonoid M] [Module R M]
  (g : (S : FiniteSet ι) → (⨂[R] i : S.val, E i) →ₗ[R] M)
  (hg : ∀ (i j : FiniteSet ι) (hij : i ≤ j)
    (x : ⨂[R] (k : i.val), E k), (g j) ((extendTensor hij E₀) x) = (g i) x)

variable {E₀} {M} in
def lift' : RestrictedTensor R E₀ →ₗ[R] M := DirectLimit.Module.lift _ _ _ _ _ hg

@[simp]
def lift'_eq : lift' g hg = DirectLimit.Module.lift _ _ _ _ _ hg := rfl

noncomputable def of (S : FiniteSet ι) :
    (⨂[R] i : ↑S, E i) →ₗ[R] RestrictedTensor R E₀ :=
  DirectLimit.Module.of R _ (fun S : FiniteSet ι ↦ ⨂[R] i : ↑S, E i) ..

theorem of_eq (S : FiniteSet ι) :
  of E₀ S = DirectLimit.Module.of R _ (fun S : FiniteSet ι ↦ ⨂[R] i : ↑S, E i) .. := rfl

variable (R) in
theorem of_f (S : FiniteSet ι) (f : Π i, E i) :
    ∀ J, (hSJ : S ≤ J) →
    (of E₀ S) (⨂ₜ[R] i, f i) = (of E₀ J) ((extendTensor hSJ E₀) (⨂ₜ[R] i, f i)) := by
  intro J hSJ
  simp [of, ← DirectLimit.Module.of_f (hij := hSJ)]

variable (R) {E₀} in
theorem of_f' (f : Πʳ (i : ι), [E i, {E₀ i}]) :
    ∀ J, ⟨_, f.prop⟩ ≤ J → (of E₀ ⟨_, f.prop⟩) (⨂ₜ[R] i, f i) = (of E₀ J) (⨂ₜ[R] i, f i) := by
  intro J hSJ
  simp only [of, ← DirectLimit.Module.of_f (hij := hSJ), extendTensor_tprod, dite_eq_ite]
  congr with j
  split_ifs with hj
  · rfl
  · simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hj
    exact hj.symm

@[simp]
theorem lift'_of {S : FiniteSet ι} {x} : lift' g hg (of E₀ S x) = (g S) x := by
  simp [of_eq]

open RestrictedMultilinearMap
open scoped TensorProduct

open Set in
variable (R) in
noncomputable def tprodr : RestrictedMultilinearMap R E₀ (RestrictedTensor R E₀) where
  toFun f := of E₀ ⟨_, f.prop⟩ (⨂ₜ[R] i, f i)
  map_update_add' f i x y := by
    let sx : FiniteSet ι := ⟨_, (f.update i x).prop⟩
    let sy : FiniteSet ι := ⟨_, (f.update i y).prop⟩
    let sxy : FiniteSet ι := ⟨_, (f.update i (x + y)).prop⟩
    let s : FiniteSet ι := ⟨sx.val ∪ sy.val ∪ sxy.val ∪ {i}, by
      rw [Set.union_singleton]
      exact Finite.insert _ (Finite.union (Finite.union sx.prop sy.prop) sxy.prop)
    ⟩
    conv_lhs => rw [of_f' R (f.update i (x + y)) s (by intro _; grind)]
    conv_rhs => rw [of_f' R (f.update i x) s (by intro _; grind),
      of_f' R (f.update i y) s (by intro _; grind)]
    simp [show ∀ x, (fun j : s.val ↦ Function.update (⇑f) i x j) =
      Function.update (fun i : s.val ↦ f i) ⟨i, by grind⟩ x by grind]
  map_update_smul' f i c x := by
    let sx : FiniteSet ι := ⟨_, (f.update i x).prop⟩
    let sc : FiniteSet ι := ⟨_, (f.update i (c • x)).prop⟩
    let s : FiniteSet ι := ⟨sx.val ∪ sc.val ∪ {i}, by
      rw [Set.union_singleton]
      exact Finite.insert _ (Finite.union sx.prop sc.prop)⟩
    conv_lhs => rw [of_f' R (f.update i (c • x)) s (by intro _; grind)]
    conv_rhs => rw [of_f' R (f.update i x) s (by intro _; grind)]
    simp [show ∀ x, (fun j : s.val ↦ Function.update (⇑f) i x j) =
      Function.update (fun i : s.val ↦ f i) ⟨i, by grind⟩ x by grind]

theorem tprodr_eq_of_tprod_apply {f : Πʳ i, [E i, {E₀ i}]} :
  tprodr R E₀ f = of E₀ ⟨_, f.prop⟩ (⨂ₜ[R] i, f i) := rfl

@[ext]
theorem ext {φ₁ φ₂ : RestrictedTensor R E₀ →ₗ[R] M}
    (H : ∀ f, φ₁ ((tprodr R E₀) f) = φ₂ ((tprodr R E₀) f)) : φ₁ = φ₂ := by
  ext S f
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply]
  convert H (finiteSetMap E₀ f)
  all_goals conv_rhs =>
    rw [tprodr_eq_of_tprod_apply,
      of_f' R (finiteSetMap E₀ f) S (fun _ ↦ by simpa [finiteSetMap] using fun h _ => h)]
    simp [of_eq]

variable (R) in
noncomputable def liftAux : RestrictedMultilinearMap R E₀ M →ₗ[R] RestrictedTensor R E₀ →ₗ[R] M :=
  {
    toFun rm :=  lift' (fun S => PiTensorProduct.lift (rm.toMultilinearMap S))
      (fun _ _ _ x ↦ by
        induction x using PiTensorProduct.induction_on with
        | smul_tprod r f =>
          simp only [map_smul, extendTensor_tprod, lift.tprod, toMultilinearMap_apply_apply]
          congr 2 with _
          aesop (add safe forward Set.mem_of_subset_of_mem)
        | add => grind)
    map_add' := by aesop
    map_smul' := by aesop
  }

@[simp]
theorem liftAux_tprodr (f : Πʳ i, [E i, {E₀ i}]) (rm : RestrictedMultilinearMap R E₀ M) :
    (liftAux R E₀ M) rm ((tprodr R E₀) f) = rm f := by
  simp [liftAux, tprodr_eq_of_tprod_apply, of, toMultilinearMap]

variable {E₀} {M} in
noncomputable def lift : RestrictedMultilinearMap R E₀ M ≃ₗ[R] RestrictedTensor R E₀ →ₗ[R] M where
  toFun := liftAux R E₀ M
  invFun l := l.compRestrictedMultilinearMap (tprodr R E₀)
  left_inv l := by ext _ ; simp
  right_inv ml := by ext _; simp
  map_add' := by simp
  map_smul' := by simp

variable {F : ι → Type*} (F₀ : (i : ι) → F i) [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)]

noncomputable def map {f : Π i, E i →ₗ[R] F i} (hf : ∀ i, (f i) (E₀ i) = F₀ i) :
    RestrictedTensor R E₀ →ₗ[R] RestrictedTensor R F₀ :=
  lift <| (tprodr R F₀).compLinearMap hf



open Module

variable {κ : ι → Type*} (b : ∀ i, Basis (κ i) R (E i))
variable (κ₀ : ∀ i, κ i)
variable (hE₀ : ∀ i, E₀ i = b i (κ₀ i))

noncomputable def toRestrictedFinsupp {S : FiniteSet ι} :
    (((i : S.val) → κ i) →₀ R) →ₗ[R] Πʳ (i : ι), [κ i, {κ₀ i}] →₀ R where
  toFun f := f.mapDomain (finiteSetMap κ₀)
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' _ _ := Finsupp.mapDomain_smul ..

noncomputable
def RestrictedTensorFinsuppEquiv : RestrictedTensor R E₀ ≃ₗ[R] Πʳ (i : ι), [κ i, {κ₀ i}] →₀ R :=
  LinearEquiv.ofLinear
  (lift' (fun S => haveI := S.prop;
    toRestrictedFinsupp κ₀ ∘ₗ ((Basis.piTensorProduct (fun i => b i.val)).repr.toLinearMap))
    ()
  )
  ()
  ()
  ()
