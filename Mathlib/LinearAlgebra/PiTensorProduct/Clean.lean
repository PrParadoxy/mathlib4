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
def sigmaFinSuccEquiv {n : Nat} {t : Fin n.succ → Type*} :
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

/-! A nested `PiTensorProduct` is equivalent to a single `PiTensorProduct` over
a sigma type if the outer type is finite. -/
def tprodFinTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih => exact tmulFinSucc.symm ≪≫ₗ TensorProduct.congr ih (LinearEquiv.refl _ _) ≪≫ₗ
      (tmulEquivDep R (fun j => s (sigmaFinSuccEquiv.symm j).1 (sigmaFinSuccEquiv.symm j).2))
      ≪≫ₗ (reindex R (fun j => s j.fst j.snd) sigmaFinSuccEquiv).symm

@[simp]
theorem tprodFinTprodEquiv_tprod (f : (k : Fin n) → (i : Tf k) → s k i) :
    tprodFinTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [tprodFinTprodEquiv, Nat.succ_eq_add_one, Nat.rec_zero, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_eq]
    simp
  | succ m ih =>
    simp only [tprodFinTprodEquiv, LinearEquiv.trans_apply, tmulFinSucc_symm,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, ← LinearEquiv.eq_symm_apply,
      LinearEquiv.symm_symm, reindex_tprod]
    conv_rhs => apply tmulEquivDep_symm_apply
    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i))
      (ih (fun i j => f i.castSucc j)))

@[simp]
theorem tprodFinTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]


section iUnion
open Set

variable {ι : Type*} {s : ι → Type*} {n : Nat} {Sf : Fin n → Set ι}
  (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
  [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
  [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]

def iUnionSigmaEquiv : (Σ k, Sf k) ≃ iUnion Sf where
  toFun s := ⟨s.2, by aesop⟩
  invFun s := ⟨(Fin.find (↑s ∈ Sf ·)).get
        (Fin.isSome_find_iff.mpr ⟨_, (mem_iUnion.mp s.prop).choose_spec⟩),
      ⟨s, by simp [Fin.find_spec (↑s ∈ Sf ·)]⟩⟩
  left_inv := by
    simp_intro s
    generalize_proofs _ h
    congr!
    by_contra hc
    exact (H hc).ne_of_mem h s.2.prop rfl
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

def tprodFiniUnionEquiv :
    (⨂[R] k, (⨂[R] i : Sf k, s i)) ≃ₗ[R] (⨂[R] i : (Set.iUnion Sf), s i) :=
  (tprodFinTprodEquiv ≪≫ₗ reindex R _ (iUnionSigmaEquiv H))

@[simp]
theorem tprodFiniUnionEquiv_tprod (f : (k : Fin n) → (i : Sf k) → s i) :
    tprodFiniUnionEquiv H (⨂ₜ[R] k, ⨂ₜ[R] i, f k i)
    = ⨂ₜ[R] i, f ((iUnionSigmaEquiv H).symm i).fst ((iUnionSigmaEquiv H).symm i).snd := by
  simp only [tprodFiniUnionEquiv, LinearEquiv.trans_apply, tprodFinTprodEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tprodFiniUnionEquiv_symm_tprod (f : (i : (Set.iUnion Sf)) → s i) :
    (tprodFiniUnionEquiv H).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] k, ⨂ₜ[R] i : Sf k, f ⟨i, by aesop⟩ := by
  simp [LinearEquiv.symm_apply_eq, iUnionSigmaEquiv]

end iUnion

section tprodFintypeTprodEquiv

variable {ι : Type*} [Fintype ι] {Tf : ι → Type*}
variable {R : Type*} {s : (k : ι) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

noncomputable def sigmaFintypeEquiv :
    (Σ k : Fin (Fintype.card ι), Tf ((Fintype.equivFin ι).symm k)) ≃ (Σ k, Tf k) :=
  Equiv.sigmaCongrLeft (Fintype.equivFin ι).symm

noncomputable def tprodFintypeTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  apply reindex _ _ (Fintype.equivFin ι) ≪≫ₗ tprodFinTprodEquiv ≪≫ₗ
    ((PiTensorProduct.congr fun i => LinearEquiv.refl _ _) ≪≫ₗ
      (reindex _ _ sigmaFintypeEquiv.symm).symm)

@[simp]
theorem tprodFintypeTprodEquiv_tprod (f : (k : ι) → (i : Tf k) → s k i) :
    tprodFintypeTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  simp only [tprodFintypeTprodEquiv, Equiv.symm_symm, LinearEquiv.trans_apply,
    reindex_tprod, LinearEquiv.symm_apply_eq]
  conv_rhs => apply reindex_tprod
  conv_lhs => arg 2; apply tprodFinTprodEquiv_tprod
  apply congr_tprod

@[simp]
theorem tprodFintypeTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFintypeTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

end tprodFintypeTprodEquiv

end Fin
