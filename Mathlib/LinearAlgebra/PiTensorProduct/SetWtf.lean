import Mathlib.LinearAlgebra.PiTensorProduct.Set

open PiTensorProduct Set
open scoped TensorProduct


variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

variable (F : Finset ι) [DecidableEq ι] {i₀} (h₀ : i₀ ∉ F) (x : s i₀)

-- Tensor product indexed by a Finset are definitionally the same as tensors indexed by the
-- same Finset coerced into a set.
example : (⨂[R] i : F, s i) = ⨂[R] i : (F : Set ι), s i := rfl

-- After `tmulInsertEquiv`, the tensors on rhs are indexed by `({i₀} : Set ι) ∪ F.toSet`
-- and not `({i₀} : Finset ι).toSet ∪ F.toSet`
#check tmulInsertEquiv h₀ (R := R) (s := s) _

-- Here is the issue!
example : (⨂[R] i : ↑(({i₀} : Set ι) ∪ (F : Set ι)), s i)
  = (⨂[R] i : ↑((({i₀} : Finset ι) : Set ι) ∪ (F : Set ι)), s i) := rfl

-- or more importantly, by `(({i₀} : Finset ι) ∪ F).toSet` that we actually want.
example : (⨂[R] i : ↑(({i₀} : Set ι) ∪ (F : Set ι)), s i)
  = (⨂[R] i : ↑ (((({i₀} : Finset ι) ∪ F) : Set ι)), s i) := rfl


-- `tmulUnionEquiv` is the same, btw!
variable (F₁ F₂ : Finset ι) (hdisj : Disjoint (F₁ : Set ι) (F₂ : Set ι))
#check tmulUnionEquiv hdisj (R := R) (s := s)

example : (⨂[R] i : ↑(F₁ ∪ F₂), s i) =
  (⨂[R] i : ↑((F₁ : Set ι) ∪ (F₂ : Set ι)), s i) := rfl


-- More conceretly, the follwoing becomes unexpressable.
variable (S : Set (⨂[R] i : ↑(insert i₀ F), s i)) (x : s i₀) (v : (⨂[R] i : F, s i))
example : tmulInsertEquiv h₀ (x ⊗ₜ[R] v) ∈ S := sorry
-- Check lemma `extended_mem` in `Phelps/OrderCone` file.
-- had the tensors on rhs of `tmulInsertEquiv` were indexed by `(({i₀} : Finset ι) ∪ F).toSet`
-- there would've been no issue. 



section singletonSetEquiv

variable (i₀ : ι)

/-- Tensors indexed by a singleton set `{i₀}` are equivalent to vectors in `s i₀`. -/
def singletonSetEquiv' : (⨂[R] i : ({i₀} : Finset ι), s i) ≃ₗ[R] s i₀ :=
  subsingletonEquivDep (⟨i₀, by simp⟩ : ({i₀} : Finset ι))

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

variable {S : Set ι} (h₀ : i₀ ∉ S)
variable [DecidableEq ι]

/-- Vectors in `s i₀` times tensors indexed by `S` are equivalent to tensors
indexed by `insert i₀ S`, assuming `i₀ ∉ S`. -/
def tmulInsertEquiv' :
    ((s i₀) ⊗[R] (⨂[R] i₁ : S, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ S), s i₁) := by
  apply (TensorProduct.congr (singletonSetEquiv' i₀).symm (LinearEquiv.refl _ _)) ≪≫ₗ ?_
  apply TensorProduct.congr
    (reindex R (fun i : ({i₀} : Finset ι) => s i ) (Finset.equivToSet {i₀}))
    (LinearEquiv.refl _ _) ≪≫ₗ
      (tmulUnionEquiv (R := R) (s := s) (S₂ := S) (by aesop)) ≪≫ₗ ?_
    -- doable but very dirty
  sorry

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
