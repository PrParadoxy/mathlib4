import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual



open scoped TensorProduct
open Module Submodule Free


theorem exists_dual_vec_ne_zero (R : Type*) {M : Type*}
    [DivisionRing R] [AddCommGroup M] [Module R M] :
    ∀ v, v ≠ 0 → ∃ dv : Dual R M, dv v ≠ 0 := fun v hv => by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (LinearPMap.mkSpanSingleton (K := R) v (1 : R) (hv)).toFun
  use g, fun hc => ?_
  have hp := LinearMap.congr_fun hg ⟨v, mem_span_singleton_self v⟩
  rw [LinearPMap.toFun_eq_coe] at hp
  simp [hc] at hp


variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N]



lemma as_sum_on_basis (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
    x = ∑ i ∈ ((bm.tensorProduct bn).repr x).support, ((bm.tensorProduct bn).repr x)
      i • (bm i.1 ⊗ₜ[R] bn i.2) := by
  let b := bm.tensorProduct bn
  nth_rw 1 [← b.linearCombination_repr x, Finsupp.linearCombination_apply S (b.repr x),
    Finsupp.sum_of_support_subset (b.repr x) (fun _ a ↦ a) _ (by simp)]
  congr with _
  simp [b, Module.Basis.tensorProduct_apply']


variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [Field R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N]
set_option maxHeartbeats 0
lemma eq_zero_of_dual_apply_sum_eq_zero (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
    (∀ ψ : Dual R N, ∑ i ∈ ((bm.tensorProduct bn).repr x).support, ψ (bn i.2) • bm i.1 = 0)
    → x = 0 := by
  by_cases hi : ∃ i : ι × κ, bn i.2 ≠ 0
  · contrapose!
    intro hx
    obtain ⟨i, hi⟩ := hi
    obtain ⟨ψ, hψ⟩ := exists_dual_vec_ne_zero R (bn i.2) hi
    use ψ
    apply?

  · intros
    rw [as_sum_on_basis bm bn x]
    apply Finset.sum_eq_zero (fun x hx => ?_)
    simp only [not_exists, not_not] at hi
    rw [hi x, TensorProduct.tmul_zero, smul_zero]



variable (bn : Basis κ R N) [DecidableEq κ] [Finite κ]
#check bn.dualBasis




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
