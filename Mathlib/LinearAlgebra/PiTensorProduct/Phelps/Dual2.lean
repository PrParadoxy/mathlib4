import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas


open Module Topology

variable (R : Type*) [CommSemiring R] [TopologicalSpace R]
  [T2Space R] [ContinuousConstSMul R R] [ContinuousAdd R]
variable (V : Type*) [AddCommGroup V] [Module R V]

/-- A type synonym for `Dual ℝ W`, equipping it with weak topology. -/
abbrev AlgWeakDual := WeakBilin (dualPairing R V)

instance : DFunLike (AlgWeakDual R V) V fun _ => R where
  coe v := v.toFun
  coe_injective' := fun _ _ h => by simpa using h

instance : LinearMapClass (AlgWeakDual R V) R V R where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'


variable {R : Type*} [CommSemiring R] [TopologicalSpace R]
  [T2Space R] [ContinuousConstSMul R R] [ContinuousAdd R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Forgets linear structure of `AlgWeakDual V` for tychonoff's theorem. -/
def dualembed : AlgWeakDual R V → (V → R) := DFunLike.coe

theorem dualembed_isclosed_embedding :
    IsClosedEmbedding (dualembed (R := R) (V := V)) :=
  IsClosedEmbedding.mk (DFunLike.coe_injective.isEmbedding_induced)
    (LinearMap.isClosed_range_coe _ _ _)

/-- A set of dual vectors is compact if it is closed,
    and its image under dualEmbed is a subset of a compact set. -/
theorem isCompact_image_dualembed {s : Set (AlgWeakDual R V)} {c : Set (V → R)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : dualembed '' s ⊆ c) : IsCompact s :=
  dualembed_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (dualembed_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)


