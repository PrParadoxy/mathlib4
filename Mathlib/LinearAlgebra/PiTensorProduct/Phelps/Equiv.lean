import Mathlib.LinearAlgebra.PiTensorProduct.Phelps.Set

open PiTensorProduct Set
open scoped TensorProduct

variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

namespace PiTensorProduct

variable [DecidableEq ι] {F : Finset ι} {i₀} (h₀ : i₀ ∉ F)

-- tmulFinInsertEquiv is necessary because the direct application of tmulInsertEquiv on `Finset`s
-- produces tensors indexed by `↥(insert i₀ ↑F)` whereas `↥↑(insert i₀ F)` might be desirable.
def tmulFinsetInsertEquiv :
    ((s i₀) ⊗[R] (⨂[R] i₁ : F, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ F), s i₁) :=
  tmulInsertEquiv h₀ ≪≫ₗ reindex R _ (Equiv.subtypeEquivProp (Finset.coe_insert i₀ F)).symm

@[simp]
theorem tmulFinsetInsertEquiv_tprod (x : s i₀) (f : (i : F) → s i) :
    (tmulFinsetInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ F),
      if h : i.val ∈ ({i₀} : Set ι) then cast (by aesop) x else f ⟨i, by aesop⟩ := by
  erw [tmulFinsetInsertEquiv, LinearEquiv.trans_apply, tmulInsertEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulFinsetInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ F)) → s i) :
    (tmulFinsetInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : F, f ⟨i, by simp⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulFinsetInsertEquiv_tprod]
  congr with i
  simp only [mem_singleton_iff, SetLike.eta, right_eq_dite_iff]
  intro _
  generalize_proofs _ _
  aesop

end PiTensorProduct
