import Mathlib.Geometry.Convex.Cone.Basic


-- Move this to `Mathlib.Geometry.Convex.Cone.Basic` under `IsGenerating`
variable {R : Type*} {M : Type*} [Ring R] [PartialOrder R]
   [AddCommGroup M] [Module R M] {C : ConvexCone R M} in
lemma ConvexCone.isGenerating_if_exists (h : ∀ v, ∃ x ∈ C, ∃ y ∈ C, x - y = v) : C.IsGenerating :=
  IsReproducing.isGenerating (IsReproducing.of_univ_subset
    (Set.univ_subset_iff.mpr (Set.eq_univ_of_forall fun v => Set.mem_sub.mpr (h v))))
