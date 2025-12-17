import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

-- Move this to `Mathlib.Geometry.Convex.Cone.Basic` under `IsGenerating`
variable {R : Type*} {M : Type*} [Ring R] [PartialOrder R]
   [AddCommGroup M] [Module R M] {C : ConvexCone R M} in
lemma ConvexCone.isGenerating_if_exists (h : ∀ v, ∃ x ∈ C, ∃ y ∈ C, x - y = v) : C.IsGenerating :=
  IsReproducing.isGenerating (IsReproducing.of_univ_subset
    (Set.univ_subset_iff.mpr (Set.eq_univ_of_forall fun v => Set.mem_sub.mpr (h v))))



-- Move out to `Mathlib.LinearAlgebra.TensorProduct.Basic`
open scoped TensorProduct

namespace TensorProduct

variable (R : Type*) [CommSemiring R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

lemma add_tmul_add_add_sub_tmul_sub (a b : M) (c d : N) :
  (a + b) ⊗ₜ[R] (c + d) + (a - b) ⊗ₜ[R] (c - d) = (2 : R) • ((a ⊗ₜ[R] c) + (b ⊗ₜ[R] d)) := by
  simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.tmul_sub,
    TensorProduct.sub_tmul, smul_add, two_smul]
  abel

lemma add_tmul_sub_add_sub_tmul_add (a b : M) (c d : N) :
  (a + b) ⊗ₜ[R] (c - d) + (a - b) ⊗ₜ[R] (c + d) = (2 : R) • ((a ⊗ₜ[R] c) - (b ⊗ₜ[R] d)) := by
  simp only [TensorProduct.tmul_sub, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.sub_tmul, smul_sub, two_smul]
  abel

end TensorProduct
