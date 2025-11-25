import Mathlib.LinearAlgebra.PiTensorProduct.Set

section Fin

open Fin PiTensorProduct
open scoped TensorProduct

section tmulFinSuccEquiv

variable {n : Nat} {R : Type*} {s : Fin (n + 1) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

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
  | succ m ih => exact
      -- Write index as sum; split off last summand as binary TP:
      (reindex _ _ finSumFinEquiv.symm) ≪≫ₗ (tmulEquivDep _ _).symm ≪≫ₗ
      -- Use `hi` on lhs; remove outer PiTP on rhs, thus exposing inner PiTP:
      (TensorProduct.congr ih (subsingletonEquivDep ↑0)) ≪≫ₗ
      -- Convert to single PiTP:
      (tmulEquivDep R (fun j => s (sigmaFinSuccEquiv.symm j).1 (sigmaFinSuccEquiv.symm j).2)) ≪≫ₗ
      (reindex R (fun j => s j.fst j.snd) sigmaFinSuccEquiv).symm

@[simp]
theorem tprodFinTprodEquiv_tprod (f : (k : Fin n) → (i : Tf k) → s k i) :
    tprodFinTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [tprodFinTprodEquiv, Nat.rec_zero, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_eq, isEmptyEquiv_apply_tprod]
  | succ m ih =>
    simp only [tprodFinTprodEquiv, Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, LinearEquiv.trans_apply]

    -- Final reindex & tmulEquivDep
    rw [LinearEquiv.symm_apply_eq, reindex_tprod, ←LinearEquiv.eq_symm_apply]
    conv_rhs => apply tmulEquivDep_symm_apply

    -- Initial reindex & tmulEquivDep
    rw [←LinearEquiv.eq_symm_apply, ←LinearEquiv.eq_symm_apply]
    conv_lhs => apply reindex_tprod
    rw [←LinearEquiv.symm_apply_eq]
    conv_lhs =>  apply tmulEquivDep_symm_apply

    -- Middle ongruence & subsingletonEquivDep
    simp only [LinearEquiv.eq_symm_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, TensorProduct.congr_tmul,
      subsingletonEquivDep_apply_tprod]

    -- Close goal using induction hypothesis
    replace ih := @ih (fun k ↦ Tf k.castSucc) (fun k i ↦ s k.castSucc i) _ _
      (fun k i ↦ f k.castSucc i)
    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i)) ih)


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

-- #check ⨂[R] i : Fin n.succ, s i
--
-- def tmulFinSumEquiv_1 :
--     ((⨂[R] (i₁ : Fin n), s (castAdd 1 i₁)) ⊗[R] (⨂[R] (i₂ : Fin 1), s (natAdd n i₂)))
--       ≃ₗ[R] ⨂[R] (i : Fin (n + 1)), s i :=
--   (tmulEquivDep R (fun i => s (finSumFinEquiv i))).trans
--     (reindex R (fun i => s i) (finSumFinEquiv.symm)).symm
--
-- def tmulFinSumEquiv_2 :
--       (⨂[R] (i : Fin (n + 1)), s i)
--       ≃ₗ[R]
--       ((⨂[R] (i₁ : Fin n), s (castAdd 1 i₁)) ⊗[R] (⨂[R] (i₂ : Fin 1), s (natAdd n i₂)))
--       :=
--   (reindex R (fun i => s i) (finSumFinEquiv.symm)) ≪≫ₗ
--   (tmulEquivDep R (fun i => s (finSumFinEquiv i))).symm
--
-- def tmulFinSumEquiv_3 :
--       (⨂[R] (i : Fin (n + 1)), s i)
--       ≃ₗ[R]
--       ((⨂[R] (i₁ : Fin n), s (castAdd 1 i₁)) ⊗[R] (s (last n))) :=
--   (reindex R (fun i => s i) (finSumFinEquiv.symm)) ≪≫ₗ
--   (tmulEquivDep R (fun i => s (finSumFinEquiv i))).symm ≪≫ₗ
--   (TensorProduct.congr (LinearEquiv.refl R _) (subsingletonEquivDep 0))
--
--
--   def tmulFinSucc : (⨂[R] i : Fin n.succ, s i) ≃ₗ[R]
--   ⨂[R] i : Fin n, s (castSucc i) ⊗[R] s (last n) :=
--   (reindex R (fun i => s i) (finSumFinEquiv.symm)) ≪≫ₗ
--   (tmulEquivDep R (fun j ↦ s (finSumFinEquiv j))).symm ≪≫ₗ
--   (TensorProduct.congr (N:= ⨂[R] i : Fin 1, s (finSumFinEquiv i)) (LinearEquiv.refl R _) (subsingletonEquivDep (0 : Fin 1)))

-- @[simp]
-- theorem tmulFinSucc_symm_tprod (f : (i : Fin n) → s (castSucc i)) (x : s (last n)) :
--     tmulFinSucc.symm ((⨂ₜ[R] i, f i) ⊗ₜ[R] x)
--     = ⨂ₜ[R] (i : Fin (n + 1)), addCases f (Function.update 0 0 x) i := by
--   rw [LinearEquiv.symm_apply_eq]
--   simp
--   congr
--   . sorry
--   . sorry
