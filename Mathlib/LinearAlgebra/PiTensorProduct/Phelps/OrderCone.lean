import Mathlib.LinearAlgebra.PiTensorProduct.Phelps.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Analysis.Convex.Cone.Basic


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


open Module Set

section SingleVectorSpace

variable (V : Type*) [AddCommGroup V] [Module ℝ V]
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

section core

namespace Set

/-- Algebraic interior of a Set. -/
def core (S : Set W) :=
  {v ∈ S | ∀ w, ∃ ε > (0 : ℝ), ∀ δ, |δ| ≤ ε → v + δ • w ∈ S}

@[simp]
lemma mem_core {v} (S : Set W) :
  v ∈ core S ↔ v ∈ S ∧ ∀ w, ∃ ε > (0 : ℝ), ∀ δ, |δ| ≤ ε → v + δ • w ∈ S := Iff.rfl

theorem mem_core_of_subset_mem_core {w} {s₁ s₂ : Set W}
    (hsub : s₁ ⊆ s₂) (hw : w ∈ core s₁) : w ∈ core s₂ :=
  ⟨mem_of_subset_of_mem hsub hw.left, fun y => by obtain ⟨ε, hε, hδ⟩ := hw.right y; aesop⟩

-- Fixes `δ` to `ε` and remove assumptions on `δ`.
theorem fix_core {S : Set W} {wr : W} (hwr : wr ∈ core S) :
    ∀ w, ∃ ε > (0 : ℝ), wr + ε • w ∈ S ∧ wr - ε • w ∈ S := by
  intro w
  obtain ⟨ε, hε, hδ⟩ := hwr.right w
  have hε₁ := (abs_of_pos hε).le
  exact ⟨ε, hε, hδ ε hε₁, by simpa [←sub_eq_add_neg] using hδ (-ε) (abs_neg ε ▸ hε₁)⟩

end Set

/-- A salient convex cone with a distinguished element `e` in its core.
  For saliency, check `OrderCone.salient`. -/
@[ext]
structure OrderCone extends ConvexCone ℝ V where
  ref : V
  hcore : ref ∈ (core carrier)
  pointed : ConvexCone.Pointed toConvexCone
