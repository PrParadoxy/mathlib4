import Mathlib.LinearAlgebra.PiTensorProduct.Set


open Fin PiTensorProduct
open scoped TensorProduct
namespace PiTensorProduct

section TprodTprod

variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

section RecursionHelpers

/-! Split off last summand of a sigma type over `Fin n.succ` -/
def sigmaFinSumLastEquiv {n : Nat} {t : Fin n.succ → Type*} :
  (Σ k : Fin n.succ, t k) ≃ (Σ k : Fin n, t k.castSucc) ⊕ t (last n) := {
    toFun x :=
      if h : x.1 = last n then .inr (h ▸ x.2) else .inl ⟨⟨x.1, lt_last_iff_ne_last.mpr h⟩, x.2⟩
    invFun := Sum.rec (fun x' ↦ ⟨x'.1.castSucc, x'.2⟩) (⟨last n, ·⟩)
    left_inv _ := by aesop
    right_inv _ := by aesop
  }

variable {n : Nat}
variable {Sf : Fin (n + 1) → Type*}
variable {s : (k : Fin (n + 1)) → (i : Sf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- Move one `Fin` index into binary tensor product
protected def tprodTprodLastEquiv : (⨂[R] k : Fin n.succ, ⨂[R] i, s k i) ≃ₗ[R]
    ((⨂[R] k : Fin n, ⨂[R] i, s k.castSucc i) ⊗[R] (⨂[R] i : Sf (last n), s (last n) i)) :=
  (reindex R (fun k : Fin (n+1) ↦ ⨂[R] i : Sf k, s k i) finSumFinEquiv.symm) ≪≫ₗ
  (tmulEquivDep R (fun j ↦ ⨂[R] i : Sf (finSumFinEquiv j), s (finSumFinEquiv j) i)).symm ≪≫ₗ
  (TensorProduct.congr (LinearEquiv.refl R _) (subsingletonEquivDep 0))

protected lemma tprodTprodLastEquiv_tprod (f : (k : Fin n.succ) → (i : Sf k) → s k i) :
    PiTensorProduct.tprodTprodLastEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) =
    (⨂ₜ[R] k : Fin n, ⨂ₜ[R] i, f k.castSucc i) ⊗ₜ[R] (⨂ₜ[R] i, f (last n) i) := by
  simp only [PiTensorProduct.tprodTprodLastEquiv, LinearEquiv.trans_apply, reindex_tprod]
  conv => arg 1; arg 2; apply tmulEquivDep_symm_apply
  rw [TensorProduct.congr_tmul]
  conv => lhs; arg 3; apply subsingletonEquivDep_apply_tprod
  rfl

-- Move one summand from sigma type into binary tensor product
protected def tprodSigmaLastEquiv : (⨂[R] j : (Σ k : Fin n.succ, Sf k), s j.1 j.2) ≃ₗ[R]
  ((⨂[R] j : (Σ k : Fin n, Sf k.castSucc), s j.1.castSucc j.2) ⊗[R]
   (⨂[R] i : Sf (last n), s (last n) i)) :=
  (reindex R (fun j : (Σ k, Sf k) ↦ s j.1 j.2) sigmaFinSumLastEquiv) ≪≫ₗ
  (tmulEquivDep R (fun i ↦ s (sigmaFinSumLastEquiv.symm i).1 (sigmaFinSumLastEquiv.symm i).2)).symm

protected lemma tprodSigmaLastEquiv_tprod (f : (j : Σ k : Fin n.succ, Sf k) → s j.1 j.2) :
    PiTensorProduct.tprodSigmaLastEquiv (⨂ₜ[R] j, f j) =
    (⨂ₜ[R] j : (Σ k : Fin n, Sf k.castSucc), f ⟨j.1.castSucc, j.2⟩) ⊗ₜ[R]
    (⨂ₜ[R] i, f ⟨(last n), i⟩) := by
  simp only [PiTensorProduct.tprodSigmaLastEquiv, Nat.succ_eq_add_one,
    LinearEquiv.trans_apply, reindex_tprod]
  apply tmulEquivDep_symm_apply

end RecursionHelpers

variable {n : Nat}
variable {Tf : Fin n → Type*}
variable {s : (k : Fin n) → (i : Tf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

/-! A nested `PiTensorProduct` is equivalent to a single `PiTensorProduct` over
a sigma type if the outer type is finite. -/
def tprodFinTprodEquiv : (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih => exact PiTensorProduct.tprodTprodLastEquiv ≪≫ₗ
      (TensorProduct.congr ih (LinearEquiv.refl _ _)) ≪≫ₗ PiTensorProduct.tprodSigmaLastEquiv.symm

@[simp]
theorem tprodFinTprodEquiv_tprod (f : (k : Fin n) → (i : Tf k) → s k i) :
    tprodFinTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [tprodFinTprodEquiv, Nat.rec_zero, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_eq, isEmptyEquiv_apply_tprod]
  | succ m ih =>
    replace ih := @ih (fun i => Tf i.castSucc) (fun i j => s i.castSucc j) _ _
      (fun i j => f i.castSucc j)
    simp only [tprodFinTprodEquiv, LinearEquiv.trans_apply,
      PiTensorProduct.tprodTprodLastEquiv_tprod, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, ←LinearEquiv.eq_symm_apply, LinearEquiv.symm_symm,
      PiTensorProduct.tprodSigmaLastEquiv_tprod]
    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i)) ih)

@[simp]
theorem tprodFinTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

end TprodTprod
end PiTensorProduct
