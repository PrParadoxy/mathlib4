import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.Basis.VectorSpace


open scoped TensorProduct
open Module Submodule Free


lemma basis_support_nonempty {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (x : M)
    (b : Basis ι R M) (hx : x ≠ 0) : ((b.repr x).support).Nonempty := by
  contrapose! hx
  simp_all [←Finset.not_nonempty_iff_eq_empty]


variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Nontrivial S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

lemma eq_zero_of_dual_apply_sum_eq_zero (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
    (∀ ψ : Dual R N, ∑ i ∈ ((bm.tensorProduct bn).repr x).support, ψ (bn i.2) • bm i.1 = 0)
    → x = 0 := by
  contrapose!
  intro hx
  obtain ⟨i, hi⟩ := basis_support_nonempty x (bm.tensorProduct bn) hx
  use bn.coord i.2
  classical
  conv_lhs => arg 2; ext x; rw [Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_indicator,  Finsupp.indicator_apply]
  simp only [Finset.mem_singleton, dite_eq_ite, ite_smul, one_smul, zero_smul]
  intro h
  apply_fun bm.coord i.1 at h
  have : (bm.coord i.1) (∑ x ∈ ((bm.tensorProduct bn).repr x).support,
          if i.2 = x.2 then bm x.1 else 0) =
        ∑ x ∈ ((bm.tensorProduct bn).repr x).support,
          if i.2 = x.2 then (bm.coord i.1) (bm x.1) else 0 := by
    simp
    congr with u
    aesop
  rw [this] at h
  clear this
  simp at h
  conv_lhs at h => arg 2; ext x; arg 2; rw [Finsupp.single_apply]
  rw [Finset.sum_eq_single i] at h
  simp at h
  aesop
  aesop










  -- contrapose!
  -- intro hx
  -- obtain ⟨i, hi⟩ := basis_support_nonempty x (bm.tensorProduct bn) hx
  -- use bn.coord i.2
  -- classical
  -- conv_lhs => arg 2; ext x; rw [Basis.coord_apply, Basis.repr_self,
  --   Finsupp.single_eq_indicator,  Finsupp.indicator_apply]
  -- simp only [Finset.mem_singleton, dite_eq_ite, ite_smul, one_smul, zero_smul]
  -- intro h
  -- apply_fun bm.coord i.1 at h
  -- have : (bm.coord i.1) (∑ x ∈ ((bm.tensorProduct bn).repr x).support,
  --         if i.2 = x.2 then bm x.1 else 0) =
  --       ∑ x ∈ ((bm.tensorProduct bn).repr x).support,
  --         if i.2 = x.2 then (bm.coord i.1) (bm x.1) else 0 := by
  --   simp
  --   congr with u
  --   aesop
  -- rw [this] at h
  -- clear this
  -- simp at h
  -- conv_lhs at h => arg 2; ext x; arg 2; rw [Finsupp.single_apply]
  -- rw [Finset.sum_eq_single i] at h
  -- simp at h
  -- aesop
  -- aesop




  -- contrapose!
  -- intro hx
  -- obtain ⟨i, hi⟩ := basis_support_nonempty x (bm.tensorProduct bn) hx
  -- use bn.coord i.2
  -- classical
  -- simp only [Basis.coord_apply, Basis.repr_self]
  -- conv_lhs => arg 2; ext x; rw [single_eq_indicator, indicator_apply]
  -- simp only [mem_singleton, dite_eq_ite, ite_smul, one_smul, zero_smul, ne_eq]
  -- erw [Finset.sum_dite]
  -- simp only [Finset.sum_const_zero, add_zero]


  -- by_cases hi : ∃ i : ι × κ, bn i.2 ≠ 0
  -- · contrapose!
  --   intro hx
  --   obtain ⟨i, hi⟩ := hi


  -- · intros
  --   rw [as_sum_on_basis bm bn x]
  --   apply Finset.sum_eq_zero (fun x hx => ?_)
  --   simp only [not_exists, not_not] at hi
  --   rw [hi x, TensorProduct.tmul_zero, smul_zero]





-- lemma as_sum_on_basis_free [Module.Free R N] [Module.Free S M] (x : M ⊗[R] N) :
--     let bm := chooseBasis S M
--     let bn := chooseBasis R N
--     let b := Basis.tensorProduct bm bn
--     x = ∑ i ∈ (b.repr x).support, (b.repr x) i • (bm i.1 ⊗ₜ[R] bn i.2) := by
--   intro bn bm b
--   nth_rw 1 [← b.linearCombination_repr x, Finsupp.linearCombination_apply S (b.repr x),
--     Finsupp.sum_of_support_subset (b.repr x) (fun _ a ↦ a) _ (by simp)]
--   congr with _
--   simp [b, Module.Basis.tensorProduct_apply']




-- variable {R : Type*} {S : Type*} {M : Type*} {N : Type*}
--   [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
--   [Module S M] [IsScalarTower R S M]
--   [AddCommMonoid N] [Module R N]

-- lemma eq_zero_of_dual_apply_sum_eq_zero
--     [Module.Free R N] [Module.Free S M] (u : M ⊗[R] N) :
--     let bm := chooseBasis S M
--     let bn := chooseBasis R N
--     let b := Basis.tensorProduct bm bn
--     (∀ ψ : Dual R N, ∑ i ∈ (b.repr u).support, ψ (bn i.2) • bm i.1 = 0) → u = 0 := by
--   intro bm bn b
--   by_cases hi : ∃ i : ChooseBasisIndex S M × ChooseBasisIndex R N, bm i.1 ≠ 0
--   . sorry
--   · intro h
--     rw [as_sum_on_basis (R := R) (S := S) u]
--     simp only [ne_eq, Prod.exists, exists_const_iff, exists_and_left, not_and, not_exists, not_not,
--       Nonempty.forall] at hi
--     apply Finset.sum_eq_zero
--     intro x hx
--     rw [hi x.2 x.1]
--     simp


-- variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
--   [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
--   [Module S M] [IsScalarTower R S M]
--   [AddCommMonoid N] [Module R N]

-- lemma as_sum_on_basis (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
--     x = ∑ i ∈ ((bm.tensorProduct bn).repr x).support, ((bm.tensorProduct bn).repr x)
--       i • (bm i.1 ⊗ₜ[R] bn i.2) := by
--   let b := bm.tensorProduct bn
--   nth_rw 1 [← b.linearCombination_repr x, Finsupp.linearCombination_apply S (b.repr x),
--     Finsupp.sum_of_support_subset (b.repr x) (fun _ a ↦ a) _ (by simp)]
--   congr with _
--   simp [b, Module.Basis.tensorProduct_apply']
