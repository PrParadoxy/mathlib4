import Mathlib.LinearAlgebra.PiTensorProduct.Phelps.Equiv
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Tensor product of partially ordered spaces

See A. Hulanicki & R. R. Phelps. Some applications of tensor products of partially-
ordered linear spaces.

A pointed convex cone with a distinguished element `ref` in its algebraic interior
`core` defines an `OrderCone`. `OrderCone` is `generating` and defines a natural
partial ordering for the vectors. `PosDual` is the set of all dual vectors evaluating
to a nonnegative number and normalized by `ref` on the elements of `OrderCone`.
It is assumed to be separting, therfore `OrderCone` is salient.

Let `PiPosDual` to be the Cartesian product of an infinite family of `PosDual`s.
There are two natural structure to define for tensor product of partially ordered spaces
`∀i, OrderCone i`. That is `MaximalProduct`, which includes tensor products that evaluate
to a nonnegative value when paired with elements of `PiPosDual`; and `MinimalProduct`,
consisting tensor products whose rank decomposition results in pure tensors made of
tensor product of vectors comming from `OrderCone`s.

## Main Definition

* `core` is the algebraic interior. No topology on vector space is needed.
* `OrderCone` a partially ordered vector space with distinguished element in its `core`.
* `PosDual` the set of dual vectors normalized by `ref` and evaluating to nonnegative number on
  elements of `OrderCone`.
* `PiPosDual` Cartesian product of an infinite family of `PosDual`s.
* `MaximalProduct` tensor products evaluating to nonnegative value when paired with `PiPosDual`.
* `MinimalProduct` made of linear combiniation of pure tensors comming from tensor product of
  vectors of `OrderCone`s.
-/


open Module Set Topology WeakBilin

section SingleVectorSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (W : Type*) [AddCommGroup W] [Module ℝ W]

namespace Set
/-- A Set is `generating` if any element in the vector space can be written as a difference between
  two elements of this Set. -/
def generating (S : Set V) := ∀ z : V, ∃ x y, x ∈ S ∧ y ∈ S ∧ z = x - y

section core

variable {vc : V} {S : Set V}

/-- Algebraic interior of a Set. -/
def core (S : Set V) := {vc | ∀ v, ∃ ε : ℝ, 0 < ε ∧ ∀ δ, |δ| ≤ ε → vc + δ • v ∈ S}

@[simp] lemma mem_core :
  vc ∈ core S ↔ ∀ v, ∃ ε : ℝ, 0 < ε ∧ ∀ δ, |δ| ≤ ε → vc + δ • v ∈ S := Iff.rfl

lemma mem_core_mem_self (hvc : vc ∈ core S) : vc ∈ S := by
  have ⟨ε, hε, hδ⟩ := hvc 0
  simpa using hδ 0 (by simp [le_of_lt hε])

lemma mem_core_of_subset_mem_core {s₁ s₂ : Set V}
    (hsub : s₁ ⊆ s₂) (hvc : vc ∈ core s₁) : vc ∈ core s₂ := by
  intro v
  have ⟨ε, hε, hδ⟩ := hvc v
  aesop

end core
end Set


/-- A salient convex cone with a distinguished element `e` in its core.
  For saliency, check `OrderCone.salient`. -/
@[ext]
structure OrderCone extends ConvexCone ℝ W where
  ref : W
  hcore : ref ∈ (core carrier)
  pointed : ConvexCone.Pointed toConvexCone

namespace OrderCone

instance : Membership V (OrderCone V) where
  mem S x := x ∈ S.carrier

@[simp] lemma mem_coe {s : Set W} {x : W} {h₁ h₂ h₃ h₄ h₅} :
  x ∈ (OrderCone.mk (ConvexCone.mk s h₁ h₂) h₃ h₄ h₅) ↔ x ∈ s := Iff.rfl

theorem is_generating (o : OrderCone V) : generating o.carrier := by
  intro v
  have ⟨ε, hε, h⟩ := o.hcore v
  have hε₁ : 0 < (1 / ε) := by simp [hε]
  use (1 / ε) • (o.ref + ε • v), (1 / ε) • (o.ref)
  exact ⟨o.smul_mem' hε₁ (h ε (abs_of_pos hε).le), o.smul_mem' hε₁ (mem_core_mem_self o.hcore),
    by simp [smul_smul, mul_comm, mul_inv_cancel₀ (ne_of_lt hε).symm]⟩

end OrderCone


section AlgWeakDual

/-- A type synonym for `Dual ℝ W`, equipping it with weak topology. -/
abbrev AlgWeakDual := WeakBilin (dualPairing ℝ W)

instance : DFunLike (AlgWeakDual V) V fun _ => ℝ where
  coe v := v.toFun
  coe_injective' := fun _ _ h => by simpa using h

instance : LinearMapClass (AlgWeakDual V) ℝ V ℝ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'

/-- Forgets linear structure of `AlgWeakDual V` for tychonoff's theorem. -/
def dualembed : AlgWeakDual V → (V → ℝ) := DFunLike.coe

theorem dualembed_isclosed_embedding :
    IsClosedEmbedding (dualembed (V := V)) :=
  IsClosedEmbedding.mk (DFunLike.coe_injective.isEmbedding_induced)
    (LinearMap.isClosed_range_coe _ _ _)

/-- A set of dual vectors is compact if it is closed,
    and its image under dualEmbed is a subset of a compact set. -/
theorem isCompact_image_dualembed {s : Set (AlgWeakDual V)} {c : Set (V → ℝ)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : dualembed '' s ⊆ c) : IsCompact s :=
  dualembed_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (dualembed_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)

end AlgWeakDual



section PosDual

/-- Set of all positive dual vectors on the order cone,
    normalized by fixing their evaluation on `OrderCone.e` to 1. -/
def PosDual (o : OrderCone V) : Set (AlgWeakDual V) :=
  {s | ∀ ⦃v⦄, v ∈ o → 0 ≤ s v} ∩ {s | s o.ref = 1}

namespace PosDual

variable (o : OrderCone V) {o' : OrderCone V}

/-- `SeparatingDual` but with no topology on the vector space. -/
def separating : Prop :=
  ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual o, f v ≠ 0

theorem convex : Convex ℝ (PosDual o) := by
  apply Convex.inter
  · exact fun _ hv _ hu _ _ ha hb hab => by
      simpa using fun q hq => add_nonneg (smul_nonneg ha (hv hq)) (smul_nonneg hb (hu hq))
  · exact Convex.linear_preimage (convex_singleton 1) (((dualPairing ℝ V).flip o.ref))

theorem isClosed : IsClosed (PosDual o) := by
  apply IsClosed.inter
  · simpa only [Set.setOf_forall] using (isClosed_biInter fun v hv =>
      (IsClosed.preimage (eval_continuous (dualPairing ℝ V) v) isClosed_nonneg))
  · exact IsClosed.preimage (eval_continuous (dualPairing ℝ V) o.ref) isClosed_singleton

theorem pointwise_bounded : ∀ v, ∃ M : ℝ, ∀ f : PosDual o, |f.val v| ≤ M := fun v => by
  have ⟨ε, hε, hδ⟩ := o.hcore v
  use 1 / ε
  intro f
  have ⟨hfv, hfe⟩ := f.val_prop
  rw [Set.mem_setOf_eq] at hfv hfe
  have hl := hfv (hδ ε (abs_of_pos hε).le)
  have hr := hfv ((hδ (-ε) (by simp [abs_of_pos hε])))
  simp only [smul_eq_mul, map_add, hfe, map_smul] at hr hl
  exact abs_le.mpr (by constructor <;> (field_simp; linarith))

theorem isCompact : IsCompact (PosDual o) := by
  let M : V → ℝ := fun v => (pointwise_bounded o v).choose
  let family : V → Set ℝ := fun v => Metric.closedBall 0 (M v)
  let prod := Set.pi Set.univ family
  have prod_compact : IsCompact prod := by
    simpa [prod, Set.pi] using isCompact_pi_infinite (fun v => isCompact_closedBall 0 (M v))
  have h_subset : dualembed '' (PosDual o) ⊆ prod := by
    simp [dualembed, Set.subset_def, prod, family]
    exact fun fembed hf v => (pointwise_bounded o v).choose_spec ⟨fembed, hf⟩
  exact isCompact_image_dualembed (isClosed o) prod_compact h_subset

lemma exists_separating_of_ne
    {x y : V} (hs : separating o') (h : x ≠ y) : ∃ f ∈ PosDual o', f x ≠ f y := by
  rcases hs (sub_ne_zero_of_ne h) with ⟨f, hf₁, hf₂⟩
  exact ⟨f, hf₁, by simpa [sub_ne_zero] using hf₂⟩

lemma nonempty [Nontrivial V] (hs : separating o') : (PosDual o').Nonempty := by
  have ⟨f, hf, _⟩ := hs (exists_ne (0 : V)).choose_spec
  exact ⟨f, hf⟩

theorem exists_strict_pos (hs : separating o) :
  ∀ v ∈ o, v ≠ 0 → ∃s ∈ PosDual o, 0 < s v := by
  intro v hv₁ hv₂
  have ⟨s, hs₁, hs₂⟩ := hs hv₂
  exact ⟨s, hs₁, lt_of_le_of_ne (hs₁.left hv₁) (hs₂.symm)⟩

end PosDual.PosDual

namespace OrderCone

variable {o : OrderCone V} (hs : PosDual.separating o)
/-
  We do not demand `ConvexCone.salient` on the ordercone definition, since it is provable
  from the existence of seperating functions. Note that the converse is not true,
  as the set of normalized positive dual vectors `PosDual` might be empty.
  Look at `Tensor Products of Compact Convex Sets` by `Isaac Namioka & R. R. Phelps`.
-/
theorem salient (hs : PosDual.separating o) : ∀ x ∈ o, x ≠ 0 → -x ∉ o := by
  intro x hx₁ hx₂ hx₃
  obtain ⟨f, hf₁, hf₂⟩ := PosDual.exists_strict_pos o hs x hx₁ hx₂
  have h : f x ≤ 0 := by simpa using hf₁.left hx₃
  simp [le_antisymm (h) (hf₁.left hx₁)] at hf₂

/-- The canonical order on the salient convex cone -/
def partialOrder : PartialOrder V :=
  ConvexCone.toPartialOrder o.toConvexCone o.pointed (o.salient hs)

def isOrderedAddMonoid : @IsOrderedAddMonoid V _ (partialOrder hs) :=
  ConvexCone.to_isOrderedAddMonoid o.toConvexCone o.pointed (o.salient hs)

end OrderCone
end SingleVectorSpace


section MultiVectorSpace

variable {ι : Type*} {s : ι → Type*}
  [∀ i, AddCommGroup (s i)] [∀ i, Module ℝ (s i)]

variable {S : Set ι} (O : ∀ i : S, OrderCone (s i))

/-- Cartesian product of a `PosDual` family. -/
def PiPosDual :=
  Set.pi Set.univ (fun (i : S) => PosDual (O i))

namespace PiPosDual

theorem convex : Convex ℝ (PiPosDual O) :=
  convex_pi (fun i _ => PosDual.convex (O i))

theorem isCompact : IsCompact (PiPosDual O) :=
  isCompact_univ_pi (fun i :S => PosDual.isCompact (O i))

theorem nonempty [∀ i, Nontrivial (s i)] (hs : ∀ i, PosDual.separating (O i)) :
  (PiPosDual O).Nonempty := Set.univ_pi_nonempty_iff.mpr (fun i => PosDual.nonempty (hs i))

end PiPosDual


open PiTensorProduct Function Finset
open scoped TensorProduct

/-- For `ConvexCone` of tensors, `core` membership can be verified using product tensors alone. -/
theorem ConvexCone.mem_piTensorProduct_core {z} {C : ConvexCone ℝ (⨂[ℝ] i, s i)}
  (smul_tprod : ∀ (r : ℝ) (f : (i : ι) → s i),
    ∃ ε, 0 < ε ∧ ∀ (δ : ℝ), |δ| ≤ ε → z + δ • r • (⨂ₜ[ℝ] i, f i) ∈ C) : z ∈ core C := by
  intro v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => exact smul_tprod r f
  | add a b ha hb =>
    obtain ⟨εa, hεa, ha⟩ := ha
    obtain ⟨εb, hεb, hb⟩ := hb
    use (min εa εb)/2
    simp_all only [lt_inf_iff, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, smul_add, true_and]
    intro δ hδ
    have hδ₁ : |2 * δ| ≤ min εa εb := by simp only [abs_mul, Nat.abs_ofNat]; linarith
    simpa [smul_smul, add_add_add_comm, smul_add, ←two_smul ℝ] using
      C.smul_mem' (show (0 : ℝ) < 1/2 by simp)
        (C.add_mem' (ha (2 * δ) (le_min_iff.mp hδ₁).left) (hb (2 * δ) (le_min_iff.mp hδ₁).right))

section LinearMaps

variable [Fintype ι]

def embedVec : (⨂[ℝ] i, s i) →ₗ[ℝ] (((i : ι) → AlgWeakDual (s i)) → ℝ) :=
  lift (
    {
      toFun vf dv := ∏ i: ι, (dv i) (vf i)
      map_update_add' _ i _ _  := by
        ext _; simpa [update] using Eq.symm (prod_add_prod_eq (mem_univ i) (by simp)
          (by intro _ _ hij; simp [hij]) (by intro _ _ hij; simp [hij]))
      map_update_smul' vf i r vi := by
          ext dv
          simp only [prod_eq_mul_prod_diff_singleton
            (mem_univ i) (fun x => (dv x) (update vf i (r • vi) x)),
            update_self, map_smul, smul_eq_mul, Pi.smul_apply,
            prod_eq_mul_prod_diff_singleton (mem_univ i) (fun x => (dv x) (update vf i vi x)),
            ← mul_assoc]
          congr! 3 with j hj
          aesop
    }
  )

@[simp] theorem embedVec_apply (dv : (i : ι) → AlgWeakDual (s i)) (vf : (i : ι) → s i) :
  embedVec (⨂ₜ[ℝ] i, vf i) dv = ∏ i : ι, (dv i) (vf i) := by simp [embedVec]

end LinearMaps


variable {F : Finset ι} (O : ∀ i : F, OrderCone (s i))

/-- The distinguished vector of tensor product space. -/
def RefTensor := ⨂ₜ[ℝ] i, (O i).ref

/-- The set of tensor products that evaluate to a nonnegative number on `PiPosDual`. -/
def MaximalProduct := {x | ∀ dv ∈ PiPosDual O, 0 ≤ embedVec x dv}

namespace MaximalProduct

theorem smul_mem' : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x⦄,
    x ∈ MaximalProduct O → c • x ∈ MaximalProduct O :=
  fun c hc x hx dv hdv => by simp_all [MaximalProduct]

theorem add_mem' : ∀ ⦃x⦄ (_ : x ∈ MaximalProduct O) ⦃y⦄ (_ : y ∈ MaximalProduct  O),
    x + y ∈ MaximalProduct O :=
  fun x hx y hy dv hdv => by simpa using (add_nonneg (hx dv hdv) (hy dv hdv))

theorem pointed : 0 ∈ MaximalProduct O := by simp [MaximalProduct]

end MaximalProduct

/-- The set of finite sums of product tensors whose components are
  drawn from a family of `OrderCone`s. -/
def MinimalProduct :=
  {x | ∃ (n : ℕ) (vf : Fin n → (i : F) → s i),
    ∑ i, (⨂ₜ[ℝ] j, (vf i j)) = x ∧ ∀ i, ∀ j : F, vf i j ∈ O j}

namespace MinimalProduct

theorem subset_maximalProduct :
  MinimalProduct O ⊆ MaximalProduct O := by
  simp only [MinimalProduct, Subtype.forall, MaximalProduct, SetLike.coe_sort_coe,
    setOf_subset_setOf, forall_exists_index, and_imp]
  intro x n vf hx hvf dv hdv
  simp only [← hx, map_sum, sum_apply, embedVec_apply]
  apply sum_nonneg; intro i _
  apply prod_nonneg; intro j hj
  exact (hdv j (by simp_all)).left (hvf i j j.prop)

/- For the empty index set, `smul_mem'` is not true. Since in that case `MinimalProduct` reduces
  to the set of all natural numbers which is not closed under real real number multiplication. -/
theorem smul_mem' [DecidableEq ι] :
  Nonempty ↥F → ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x⦄, x ∈ MinimalProduct O → c • x ∈ MinimalProduct O := by
  intro _ c hc _ hx
  obtain ⟨n, vf, hx, hvf⟩ := hx
  let j := Classical.arbitrary F
  use n, (fun i => update (vf i) j (c • (vf i j)))
  constructor
  · simpa [Finset.smul_sum] using congr_arg (fun v => c • v) hx
  · intro k q
    unfold update
    split_ifs with h
    · subst h; exact (O j).smul_mem' hc (hvf k j)
    · simp [(hvf k q)]

theorem add_mem' :
  ∀ ⦃x⦄ (_ : x ∈ MinimalProduct O) ⦃y⦄ (_ : y ∈ MinimalProduct O), x + y ∈ MinimalProduct O := by
  intro x hx y hy
  obtain ⟨nx, vfx, hx, hvfx⟩ := hx
  obtain ⟨ny, vfy, hy, hvfy⟩ := hy
  let vf := fun i : Fin (nx + ny) =>
    if h : i.val < nx then vfx ⟨i.val, h⟩
    else vfy ⟨i.val - nx, by omega⟩
  use nx + ny, vf
  constructor
  · simp [Fin.sum_univ_add (fun i => (PiTensorProduct.tprod ℝ) (vf i)), ←hx, ←hy, vf]
  · intro i j
    unfold vf
    split_ifs with h
    · exact hvfx ⟨i.val, h⟩ j
    · exact hvfy ⟨i.val - nx, by omega⟩ j

theorem pointed : 0 ∈ MinimalProduct O := by use 0, 0; aesop

theorem refTensor_mem : RefTensor O ∈ MinimalProduct O :=
  ⟨1, (fun _ j => (O j).ref), by simp [RefTensor], fun _ j => mem_core_mem_self (O j).hcore⟩

section

variable [DecidableEq ι]

theorem extended_mem
  {i₀} (h₀ : i₀ ∉ F)
  (O : (i : ↥(insert i₀ F)) → OrderCone (s i))
  {z : ⨂[ℝ] i : F, s i} {x : s i₀}
  (hz : z ∈ MinimalProduct (fun i => O ⟨i, by simp⟩))
  (hx : x ∈ O ⟨i₀, by simp⟩) :
    tmulFinsetInsertEquiv h₀ (x ⊗ₜ[ℝ] z) ∈ MinimalProduct O := by
  have ⟨n, vf, hz, hvf⟩ := hz
  use n, (fun n i => if h : ↑i = i₀ then cast (by rw [h]) x else vf n ⟨i, by aesop⟩)
  simp only [← hz, TensorProduct.tmul_sum]
  aesop

theorem refTensor_mem_core : Nonempty ↥F → RefTensor O ∈ core (MinimalProduct O) := by
  induction F using Finset.induction_on with
  | empty => simp_all
  | insert i₀ F h₀ ih =>
    intro hne

    -- by_cases hf : Nonempty ↥F
    -- .
    --   replace ih := ih (fun i => O ⟨i, by simp⟩) hf
    --   have ho := (O ⟨i₀, by simp⟩).hcore
    --   have := extended_mem h₀ O (mem_core_mem_self ih) (mem_core_mem_self ho)
