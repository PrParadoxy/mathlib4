import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Analysis.InnerProductSpace.TensorProduct

open PiTensorProduct
open scoped TensorProduct ComplexConjugate

section tmulFinSucc

open Fin

section tmulFinSumEquiv

variable {n m} {R : Type*} {M : Fin (n + m) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Isomorphism between product of tensors indexed by `{1, ..., n} ⊆ Fin (n+m)`
and `{n+1, ..., m} ⊆ Fin (n+m)`, and tensors indexed by `Fin (n + m)`. -/
def tmulFinSumEquiv :
    ((⨂[R] (i₁ : Fin n), M (castAdd m i₁)) ⊗[R] (⨂[R] (i₂ : Fin m), M (natAdd n i₂)))
      ≃ₗ[R] ⨂[R] (i : Fin (n + m)), M i :=
  (tmulEquivDep R (fun i => M (finSumFinEquiv i))).trans
    (reindex R (fun i => M i) (finSumFinEquiv.symm)).symm

@[simp]
theorem tmulFinSumEquiv_tprod
    (lv : (i : Fin n) → M ⟨i, by omega⟩) (rv : (i : Fin m) → M ⟨n + i, by omega⟩) :
      tmulFinSumEquiv ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i : Fin m, rv i))
        = ⨂ₜ[R] i : Fin (n + m), addCases lv rv i := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  erw [reindex_tprod, tmulEquivDep_apply]
  congr with x
  aesop

@[simp]
theorem tmulFinSumEquiv_symm_tprod (av : (i : Fin (n + m)) → M i) :
    (tmulFinSumEquiv).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : Fin n, av (castAdd m i)) ⊗ₜ[R] (⨂ₜ[R] i : Fin m, av (natAdd n i)) := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  erw [reindex_tprod finSumFinEquiv.symm]
  erw [tmulEquivDep_symm_apply]
  simp

end tmulFinSumEquiv

section tmulFinSuccEquiv

variable {n : Nat} {R : Type*} {M : Fin (n.succ) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

def tmulFinSucc :
    (⨂[R] i : Fin n, M (castSucc i)) ⊗[R] (M (last n)) ≃ₗ[R] ⨂[R] (i : Fin n.succ), M i :=
  (tmulFinSumEquiv.symm ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl _ _) (subsingletonEquiv 0))).symm

@[simp]
theorem tmulFinSucc_tprod (f : (i : Fin n) → M (castSucc i)) (x : M (last n)) :
    haveI := decidableEq_of_subsingleton (α := Fin 1)
    tmulFinSucc ((⨂ₜ[R] i, f i) ⊗ₜ[R] x)
      = ⨂ₜ[R] (i : Fin (n + 1)), addCases f (Pi.single 0 x) i := by
  erw [tmulFinSucc, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, TensorProduct.congr_symm_tmul, tmulFinSumEquiv_tprod]
  rfl

@[simp]
theorem tmulFinSucc_symm (f : (i : Fin n.succ) → M i) :
    tmulFinSucc.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i, f (castSucc i)) ⊗ₜ[R] f (last n) := by
  simp only [Nat.succ_eq_add_one, tmulFinSucc, isValue, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, tmulFinSumEquiv_symm_tprod]
  erw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, subsingletonEquiv_apply_tprod]
  congr

end tmulFinSuccEquiv


end tmulFinSucc

universe u
variable {ι : Type*}
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n} {M : Fin n → Type u} [∀ i, NormedAddCommGroup (M i)] [∀ i, InnerProductSpace 𝕜 (M i)]

def PiTensorProduct.InnerProductspace.Core :
  InnerProductSpace.Core 𝕜 (⨂[𝕜] i, M i) :=
  n.rec (motive := fun n => ∀ (M : Fin n → Type u) [∀ i, NormedAddCommGroup (M i)]
      [∀ i, InnerProductSpace 𝕜 (M i)], InnerProductSpace.Core 𝕜 (⨂[𝕜] i, M i))
    (fun M _ _ => {
      inner a b := innerₛₗ 𝕜 (isEmptyEquiv _ a) (isEmptyEquiv _ b)
      conj_inner_symm := by simp [mul_comm]
      re_inner_nonneg := by simp
      add_left := by simp
      smul_left := by simp [mul_left_comm]
      definite := by simp
    })
    (fun n ih M _ _ =>
      let ih := @ih (fun i => M i.castSucc) _ _
      letI normed := ih.toNormedAddCommGroup
      letI ips := InnerProductSpace.ofCore ih.toCore
      letI tnormed : NormedAddCommGroup ((⨂[𝕜] i : Fin n, M i.castSucc) ⊗[𝕜] M (Fin.last n)) :=
        @TensorProduct.instNormedAddCommGroup 𝕜 _ _ _ normed ips _ _
      letI tips : InnerProductSpace 𝕜 ((⨂[𝕜] i : Fin n, M i.castSucc) ⊗[𝕜] M (Fin.last n)) :=
        @TensorProduct.instInnerProductSpace 𝕜 _ _ _ normed ips _ _
      { inner := fun x y => inner 𝕜 (tmulFinSucc.symm x) (tmulFinSucc.symm y)
        conj_inner_symm := by simp
        re_inner_nonneg := by simp
        add_left x y z := by simp [inner_add_left]
        smul_left := by simp [inner_smul_left]
        definite := by simp })
    M

noncomputable instance : NormedAddCommGroup (⨂[𝕜] (i : Fin n), M i) :=
  PiTensorProduct.InnerProductspace.Core.toNormedAddCommGroup

instance : InnerProductSpace 𝕜 (⨂[𝕜] (i : Fin n), M i) :=
  InnerProductSpace.ofCore PiTensorProduct.InnerProductspace.Core.toCore

private lemma inner_def_zero {M : Fin 0 → Type*}
    [∀ i, NormedAddCommGroup (M i)] [∀ i, InnerProductSpace 𝕜 (M i)]
    (x y : ⨂[𝕜] i : Fin 0, M i) :
    inner 𝕜 x y = inner 𝕜 (isEmptyEquiv _ x) (isEmptyEquiv _ y) := rfl

private lemma inner_def_succ {n : ℕ} {M : Fin (n + 1) → Type*} [∀ i, NormedAddCommGroup (M i)]
    [∀ i, InnerProductSpace 𝕜 (M i)]
    (x y : ⨂[𝕜] i : Fin (n + 1), M i) :
    inner 𝕜 x y = inner 𝕜 (tmulFinSucc.symm x) (tmulFinSucc.symm y) := rfl

@[simp] theorem inner_tprod (v w : ∀ i : Fin n, M i) :
    inner 𝕜 (⨂ₜ[𝕜] i, v i) (⨂ₜ[𝕜] i, w i) = ∏ i, inner 𝕜 (v i) (w i) := by
  induction n with
  | zero => simp [inner_def_zero]
  | succ n ih => simp [inner_def_succ, ih (fun i => v i.castSucc) (fun i => w i.castSucc),
      ← Fin.prod_univ_castSucc (fun i => inner 𝕜 (v i) (w i))]
