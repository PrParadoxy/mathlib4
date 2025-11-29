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
abbrev dualembed : AlgWeakDual V → (V → ℝ) := DFunLike.coe

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
  {s | ∀ v ∈ o, 0 ≤ s v} ∩ {s | s o.ref = 1}

namespace PosDual

variable (o : OrderCone V) {o' : OrderCone V}

/-- `SeparatingDual` but with no topology on the vector space. -/
abbrev separating : Prop :=
  ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual o, f v ≠ 0

theorem convex : Convex ℝ (PosDual o) := by
  apply Convex.inter
  · exact fun _ hv _ hu _ _ ha hb hab => by
      simpa using fun q hq => add_nonneg (smul_nonneg ha (hv q hq)) (smul_nonneg hb (hu q hq))
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
  have hl := hfv (o.ref + ε • v) (hδ ε (abs_of_pos hε).le)
  have hr := hfv (o.ref - ε • v)
    (by simpa [sub_eq_add_neg] using (hδ (-ε) (by simp [abs_of_pos hε])))
  simp only [map_sub, smul_eq_mul, map_add, hfe, map_smul] at hr hl
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
  exact ⟨s, hs₁, lt_of_le_of_ne (hs₁.left v hv₁) (hs₂.symm)⟩

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
  have h : f x ≤ 0 := by simpa using hf₁.left (-x) hx₃
  simp [le_antisymm (h) (hf₁.left (x) hx₁)] at hf₂

/-- The canonical order on the salient convex cone -/
def partialOrder : PartialOrder V :=
  ConvexCone.toPartialOrder o.toConvexCone o.pointed (o.salient hs)

def isOrderedAddMonoid : @IsOrderedAddMonoid V _ (partialOrder hs) :=
  ConvexCone.to_isOrderedAddMonoid o.toConvexCone o.pointed (o.salient hs)

end OrderCone
end SingleVectorSpace


section MultiVectorSpace

open PiTensorProduct
open scoped TensorProduct

variable {ι : Type*} {S : Set ι} (S' : Set ι) {s : ι → Type*}
  [∀ i, AddCommGroup (s i)] [∀ i, Module ℝ (s i)] (O : ∀ i, OrderCone (s i))

/-- Cartesian product of a `PosDual` family. -/
abbrev PiPosDual := Set.pi Set.univ (fun (i : S') => PosDual (O i))

namespace PiPosDual

theorem convex : Convex ℝ (PiPosDual S O) :=
  convex_pi (fun i _ => PosDual.convex (O i))

theorem isCompact : IsCompact (PiPosDual S O) := by
  exact isCompact_univ_pi (fun i :S => PosDual.isCompact (O i))

theorem nonempty [∀ i, Nontrivial (s i)] (hs : ∀ i, PosDual.separating (O i)) :
  (PiPosDual S O).Nonempty := Set.univ_pi_nonempty_iff.mpr (fun i => PosDual.nonempty (hs i))

end PiPosDual
