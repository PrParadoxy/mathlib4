import Mathlib.LinearAlgebra.PiTensorProduct.Set

open PiTensorProduct Set
open scoped TensorProduct


variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

section Finset

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

end Finset

@[elab_as_elim]
theorem set_finite_induction_on
    {S : Set ι} (hS : S.Finite)
    {motive : ∀ {T : Set ι} (_ : T.Finite), (⨂[R] i : T, s i) → Prop}
    (empty : ∀ r : R, motive finite_empty ((isEmptyEquiv (∅ : Set ι)).symm r))
    (insert : ∀ (i₀ : ι) (T : Set ι) (_ : i₀ ∉ T) (hT : T.Finite),
      (∀ (w : ⨂[R] i : T, s i), motive hT w) →
        ∀ (z : ⨂[R] i : ↑(insert i₀ T), s i), motive (hT.insert i₀) z)
    (z : ⨂[R] i : S, s i) : motive hS z := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa [LinearEquiv.symm_apply_apply] using empty (isEmptyEquiv (∅ : Set ι) z)
  | @insert i₀ S hi₀ hs hm => exact insert i₀ S hi₀ hs hm z

@[elab_as_elim]
theorem finset_induction_on
    [DecidableEq ι] (S : Finset ι)
    {motive : ∀ {T : Finset ι}, (⨂[R] i : (T : Set ι), s i) → Prop}
    (empty : ∀ r : R, motive ((isEmptyEquiv (∅ : Finset ι)).symm r))
    (insert : ∀ (i₀ : ι) (T : Finset ι) (_ : i₀ ∉ T),
      (∀ (w : ⨂[R] i : (T : Set ι), s i), motive w) →
        ∀ (z : ⨂[R] i : ↑(insert i₀ T), s i), motive z)
    (z : ⨂[R] i : (S : Set ι), s i) : motive z := by
  induction S using Finset.induction with
  | empty => simpa [LinearEquiv.symm_apply_apply] using empty (isEmptyEquiv (∅ : Finset ι) z)
  | insert i₀ S hi₀ hm => exact insert i₀ S hi₀ hm z
