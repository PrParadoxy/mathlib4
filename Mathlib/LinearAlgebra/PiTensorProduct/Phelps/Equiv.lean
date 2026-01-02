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

-- @[elab_as_elim]
-- theorem set_finite_induction_on
--     {S : Set ι} (hS : S.Finite)
--     {motive : ∀ {T : Set ι} (_ : T.Finite), (⨂[R] i : T, s i) → Prop}
--     (empty : ∀ r : R, motive finite_empty ((isEmptyEquiv (∅ : Set ι)).symm r))
--     (insert : ∀ (i₀ : ι) (T : Set ι) (_ : i₀ ∉ T) (hT : T.Finite),
--       (∀ (w : ⨂[R] i : T, s i), motive hT w) →
--         ∀ (z : ⨂[R] i : ↑(insert i₀ T), s i), motive (hT.insert i₀) z)
--     (z : ⨂[R] i : S, s i) : motive hS z := by
--   induction S, hS using Set.Finite.induction_on with
--   | empty => simpa [LinearEquiv.symm_apply_apply] using empty (isEmptyEquiv (∅ : Set ι) z)
--   | @insert i₀ S hi₀ hs hm => exact insert i₀ S hi₀ hs hm z

-- @[elab_as_elim]
-- theorem finset_induction_on
--     [DecidableEq ι] {F : Finset ι}
--     {motive : ∀ {T : Finset ι}, (⨂[R] i : T, s i) → Prop}
--     (empty : ∀ r : R, motive ((isEmptyEquiv (∅ : Finset ι)).symm r))
--     (insert : ∀ (i₀ : ι) (T : Finset ι) (_ : i₀ ∉ T),
--       (∀ (w : ⨂[R] i : T, s i), motive w) →
--         ∀ (z : ⨂[R] i : ↑(insert i₀ T), s i), motive z)
--     (z : ⨂[R] i : F, s i) : motive z := by
--   induction F using Finset.induction with
--   | empty => simpa [LinearEquiv.symm_apply_apply] using empty (isEmptyEquiv (∅ : Finset ι) z)
--   | insert i₀ S hi₀ hm => exact insert i₀ S hi₀ hm z


section singletonSetEquiv

variable (i₀ : ι)

/-- Tensors indexed by a singleton set `{i₀}` are equivalent to vectors in `s i₀`. -/
def singletonSetEquiv' : (⨂[R] i : ({i₀} : Finset ι), s i) ≃ₗ[R] s i₀ :=
  subsingletonEquiv (⟨i₀, by simp⟩ : ({i₀} : Finset ι))

@[simp]
theorem singletonEquiv_tprod' (f : (i : ({i₀} : Set ι)) → s i) :
    singletonSetEquiv' i₀ (⨂ₜ[R] i, f ⟨i, by aesop⟩) = f ⟨i₀, by simp⟩ := by
  simp [singletonSetEquiv']

@[simp]
theorem singletonEquiv_symm_tprod (x : s i₀) :
    (singletonSetEquiv' i₀).symm x = (⨂ₜ[R] i : ({i₀} : Finset ι), cast (by aesop) x) := by
  rw [LinearEquiv.symm_apply_eq]
  simp [singletonSetEquiv']

end singletonSetEquiv


section tmulInsertEquiv

variable {S : Set ι} {i₀} (h₀ : i₀ ∉ S)
variable [DecidableEq ι]

-- /-- Vectors in `s i₀` times tensors indexed by `S` are equivalent to tensors
-- indexed by `insert i₀ S`, assuming `i₀ ∉ S`. -/
-- def tmulInsertEquiv' :
--     ((s i₀) ⊗[R] (⨂[R] i₁ : S, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ S), s i₁) := by
--   apply (TensorProduct.congr (singletonSetEquiv' i₀).symm (LinearEquiv.refl _ _)) ≪≫ₗ ?_
--   apply TensorProduct.congr
--     (reindex R (fun i : ({i₀} : Finset ι) => s i ) (Finset.equivToSet {i₀}))
--     (LinearEquiv.refl _ _) ≪≫ₗ
--       (tmulUnionEquiv (R := R) (s := s) (S₂ := S) (by aesop)) ≪≫ₗ ?_
--     -- doable but very dirty
--   sorry

-- @[simp]
-- theorem tmulInsertEquiv_tprod (x : s i₀) (f : (i : S) → s i) :
--     (tmulInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ S),
--       if h : i.val ∈ ({i₀} : Set ι) then cast (by aesop) x else f ⟨i, by aesop⟩ := by
--   rw [tmulInsertEquiv, LinearEquiv.trans_apply,
--     TensorProduct.congr_tmul, singletonEquiv_symm_tprod]
--   apply tmulUnionEquiv_tprod

-- @[simp]
-- theorem tmulInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ S)) → s i) :
--     (tmulInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
--     (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : S, f ⟨i, by simp⟩) := by
--   rw [LinearEquiv.symm_apply_eq, tmulInsertEquiv_tprod]
--   grind

end tmulInsertEquiv

#check Finset.equivToSet
