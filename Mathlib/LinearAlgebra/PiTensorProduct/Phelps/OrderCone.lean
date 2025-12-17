import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.PiTensorProduct.Phelps.Aux
import Mathlib.LinearAlgebra.PiTensorProduct.Phelps.Dual
import Mathlib.Analysis.Normed.Order.Lattice

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

* `core` is the algebraic interior. No topology on the vector space is needed.
* `OrderCone` a partially ordered vector space with distinguished element in its `core`.
* `PosDual` the set of dual vectors normalized by `ref` and evaluating to nonnegative number on
  elements of `OrderCone`.
* `PiPosDual` Cartesian product of an infinite family of `PosDual`s.
* `MaximalProduct` tensor products evaluating to nonnegative value when paired with `PiPosDual`.
* `MinimalProduct` made of linear combiniation of pure tensors comming from tensor product of
  vectors of `OrderCone`s.
-/


open Set ConvexCone Module WeakBilin

section SingleVectorSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

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

/-- A salient convex cone with a distinguished element `e` in its core.
  For saliency, check `OrderCone.salient`. -/
@[ext]
structure OrderCone (V : Type*) [AddCommGroup V] [Module ℝ V] extends ConvexCone ℝ V where
  ref : V
  hcore : ref ∈ (core carrier)
  pointed : ConvexCone.Pointed toConvexCone

namespace OrderCone

instance : Membership V (OrderCone V) where
  mem S x := x ∈ S.carrier

@[simp] lemma mem_coe {s : Set V} {x : V} {h₁ h₂ h₃ h₄ h₅} :
  x ∈ (OrderCone.mk (ConvexCone.mk s h₁ h₂) h₃ h₄ h₅) ↔ x ∈ s := Iff.rfl

theorem isGenerating (o : OrderCone V) : o.IsGenerating := by
  apply isGenerating_if_exists (fun v => ?_)
  have ⟨ε, hε, h⟩ := o.hcore v
  have hε₁ : 0 < (1 / ε) := by simp [hε]
  exact ⟨(1 / ε) • (o.ref + ε • v), o.smul_mem' hε₁ (h ε (abs_of_pos hε).le),
    (1 / ε) • (o.ref), o.smul_mem' hε₁ (mem_core_mem_self o.hcore),
    by simp [smul_smul, mul_comm, mul_inv_cancel₀ (ne_of_lt hε).symm]⟩

end OrderCone

/-- Set of all positive dual vectors on the order cone,
    normalized by fixing their evaluation on `OrderCone.e` to 1. -/
def PosDual (o : OrderCone V) : Set (AlgWeakDual ℝ V) :=
  {s | ∀ ⦃v⦄, v ∈ o → 0 ≤ s v} ∩ {s | s o.ref = 1}

namespace PosDual

variable (o : OrderCone V)

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

theorem pointwise_bounded (v) : ∃ M : ℝ, ∀ f : PosDual o, |f.val v| ≤ M := by
  have ⟨ε, hε, hδ⟩ := o.hcore v
  use 1 / ε
  intro f
  have ⟨hfv, hfe⟩ := f.prop
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
  have h_subset : DFunLike.coe '' (PosDual o) ⊆ prod := by
    simpa only [subset_def, mem_image, mem_pi, mem_univ, Metric.mem_closedBall, dist_zero_right,
      Real.norm_eq_abs, forall_const, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, prod,
      family] using fun fembed hf v => (pointwise_bounded o v).choose_spec ⟨fembed, hf⟩
  exact AlgWeakDual.isCompact_subset_image_coe (isClosed o) prod_compact h_subset

lemma nonempty [Nontrivial V] {o : OrderCone V} (hs : ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual o, f v ≠ 0)
    : (PosDual o).Nonempty := by
  have ⟨f, hf, _⟩ := hs (exists_ne (0 : V)).choose_spec
  exact ⟨f, hf⟩

theorem exists_strict_pos (hs : ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual o, f v ≠ 0) :
  ∀ v ∈ o, v ≠ 0 → ∃ s ∈ PosDual o, 0 < s v := by
  intro v hv₁ hv₂
  have ⟨s, hs₁, hs₂⟩ := hs hv₂
  exact ⟨s, hs₁, lt_of_le_of_ne (hs₁.left hv₁) (hs₂.symm)⟩

end PosDual

namespace OrderCone

variable {o : OrderCone V}

theorem salient (hs : ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual o, f v ≠ 0) : ∀ x ∈ o, x ≠ 0 → -x ∉ o := by
  intro x hx₁ hx₂ hx₃
  obtain ⟨f, hht₁, hht₂⟩ := PosDual.exists_strict_pos o hs x hx₁ hx₂
  have h : f x ≤ 0 := by simpa using hht₁.left hx₃
  simp [le_antisymm (h) (hht₁.left hx₁)] at hht₂

variable (hs : ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual o, f v ≠ 0)

/-- The canonical order on the salient convex cone -/
def partialOrder : PartialOrder V :=
  ConvexCone.toPartialOrder o.toConvexCone o.pointed (o.salient hs)

def isOrderedAddMonoid : @IsOrderedAddMonoid V _ (partialOrder hs) :=
  ConvexCone.to_isOrderedAddMonoid o.toConvexCone o.pointed (o.salient hs)

end OrderCone
end SingleVectorSpace



section MultiVectorSpace

variable {ι : Type*} {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module ℝ (s i)]

variable {S : Set ι} (O : ∀ i : S, OrderCone (s i))

/-- Cartesian product of a `PosDual` family. -/
def PiPosDual := Set.pi Set.univ (fun (i : S) => PosDual (O i))

namespace PiPosDual

theorem convex : Convex ℝ (PiPosDual O) :=
  convex_pi (fun i _ => PosDual.convex (O i))

theorem isCompact : IsCompact (PiPosDual O) :=
  isCompact_univ_pi (fun i :S => PosDual.isCompact (O i))

theorem nonempty [∀ i, Nontrivial (s i)] {O : ∀ i : S, OrderCone (s i)}
    (hs : ∀ i, ∀ ⦃v⦄, v ≠ 0 → ∃ f ∈ PosDual (O i), f v ≠ 0)
    : (PiPosDual O).Nonempty :=
  Set.univ_pi_nonempty_iff.mpr (fun i => PosDual.nonempty (hs i))

end PiPosDual

