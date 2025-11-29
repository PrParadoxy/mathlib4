import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas


open Module Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (W : Type*) [AddCommGroup W] [Module ℝ W]

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
theorem dualembed_dual_iscompact {s : Set (AlgWeakDual V)} {c : Set (V → ℝ)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : dualEmbed '' s ⊆ c) : IsCompact s :=
  dualembed_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (dualembed_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)
