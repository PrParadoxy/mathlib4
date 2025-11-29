import Mathlib.LinearAlgebra.PiTensorProduct.Phelps.Equiv
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas


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


open Module Set Topology

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

abbrev dualEmbed : AlgWeakDual V → (V → ℝ) := DFunLike.coe

theorem dualembed_isclosed_embedding :
    IsClosedEmbedding (dualEmbed (V := V)) :=
  IsClosedEmbedding.mk (DFunLike.coe_injective.isEmbedding_induced)
    (LinearMap.isClosed_range_coe _ _ _)

/-- A set of dual vectors is compact if it is closed,
    and its image under dualEmbed is a subset of a compact set. -/
theorem isCompact_image_dualembed {s : Set (AlgWeakDual V)} {c : Set (V → ℝ)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : dualEmbed '' s ⊆ c) : IsCompact s :=
  dualembed_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (dualembed_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)

end AlgWeakDual



