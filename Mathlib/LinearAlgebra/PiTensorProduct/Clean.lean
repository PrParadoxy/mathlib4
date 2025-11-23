import Mathlib.LinearAlgebra.PiTensorProduct.Set


section Fin

open Fin PiTensorProduct
open scoped TensorProduct

section tmulFinSumEquiv

variable {n m} {R : Type*} {s : Fin (n + m) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-- Isomorphism between product of tensors indexed by `{1, ..., n} ⊆ Fin (n+m)`
and `{n+1, ..., m} ⊆ Fin (n+m)`, and tensors indexed by `Fin (n + m)`. -/
def tmulFinSumEquiv :
    ((⨂[R] (i₁ : Fin n), s (castAdd m i₁)) ⊗[R] (⨂[R] (i₂ : Fin m), s (natAdd n i₂)))
      ≃ₗ[R] ⨂[R] (i : Fin (n + m)), s i :=
  (tmulEquivDep R (fun i => s (finSumFinEquiv i))).trans
    (reindex R (fun i => s i) (finSumFinEquiv.symm)).symm

@[simp]
theorem tmulFinSumEquiv_tprod
    (lv : (i : Fin n) → s ⟨i, by omega⟩) (rv : (i : Fin m) → s ⟨n + i, by omega⟩) :
      tmulFinSumEquiv ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i : Fin m, rv i))
        = ⨂ₜ[R] i : Fin (n + m), addCases lv rv i := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  -- erw [tmulEquivDep_apply, reindex_tprod] also works.
  conv_lhs => apply tmulEquivDep_apply
  conv_rhs => apply reindex_tprod
  congr with x
  aesop

@[simp]
theorem tmulFinSumEquiv_symm_tprod (av : (i : Fin (n + m)) → s i) :
    (tmulFinSumEquiv).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : Fin n, av (castAdd m i)) ⊗ₜ[R] (⨂ₜ[R] i : Fin m, av (natAdd n i)) := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  conv_lhs => arg 2; apply reindex_tprod
  apply tmulEquivDep_symm_apply

end tmulFinSumEquiv



section tmulFinSuccEquiv

variable {n : Nat} {R : Type*} {s : Fin (n.succ) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

def tmulFinSucc :
    (⨂[R] i : Fin n, s (castSucc i)) ⊗[R] (s (last n)) ≃ₗ[R] ⨂[R] (i : Fin n.succ), s i :=
  (tmulFinSumEquiv.symm ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl _ _ ) (subsingletonEquivDep 0))).symm

@[simp]
theorem tmulFinSucc_tprod (f : (i : Fin n) → s (castSucc i)) (x : s (last n)) :
    haveI := decidableEq_of_subsingleton (α := Fin 1)
    tmulFinSucc ((⨂ₜ[R] i, f i) ⊗ₜ[R] x)
      = ⨂ₜ[R] (i : Fin (n + 1)), addCases f (Function.update 0 0 x) i := by
  simp only [tmulFinSucc, isValue, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  conv_lhs => arg 2; apply TensorProduct.congr_symm_tmul
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, subsingletonEquivDep_symm_apply]
  apply tmulFinSumEquiv_tprod
--   erw [tmulFinSucc, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
--     LinearEquiv.trans_apply, TensorProduct.congr_symm_tmul, tmulFinSumEquiv_tprod]

@[simp]
theorem tmulFinSucc_symm (f : (i : Fin n.succ) → s i) :
    tmulFinSucc.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i, f (castSucc i)) ⊗ₜ[R] f (last n) := by
  simp only [Nat.succ_eq_add_one, tmulFinSucc, isValue, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, tmulFinSumEquiv_symm_tprod]
  conv_lhs => apply TensorProduct.congr_tmul
  aesop

end tmulFinSuccEquiv

/-! Split off last summand of a sigma type over `Fin n.succ` -/
def sigmaFinSumLastEquiv {n : Nat} {t : Fin n.succ → Type*} :
  (Σ k : Fin n.succ, t k) ≃ (Σ k : Fin n, t k.castSucc) ⊕ t (last n) := {
    toFun x :=
      if h : x.1 = last n then .inr (h ▸ x.2) else .inl ⟨⟨x.1, lt_last_iff_ne_last.mpr h⟩, x.2⟩
    invFun := Sum.rec (fun x' ↦ ⟨x'.1.castSucc, x'.2⟩) (⟨last n, ·⟩)
    left_inv _ := by aesop
    right_inv _ := by aesop
  }



variable {n : Nat} {Tf : Fin n → Type*}
variable {R : Type*} {s : (k : Fin n) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- TBD: Is it desirable to reformulate that as a recursive function?
-- TBD: Use `Fintype`? Could always just use `noncomputable def Finset.equivFin`
/-! A nested `PiTensorProduct` is equivalent to a single `PiTensorProduct` over
a sigma type if the outer type is finite. -/
def trpodFinTprodEquiv :
  (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih =>
