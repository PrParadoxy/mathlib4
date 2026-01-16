import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

section norm

#check ContinuousLinearMap.norm_def
variable (𝕜 : Type*) (E : Type*)
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter NormedSpace

theorem norm_seq (v : E) (h : ‖v‖ ≤ ‖inclusionInDoubleDual 𝕜 E v‖) :
  ∃ g : ℕ → StrongDual 𝕜 E,
    Tendsto (fun i => ‖g i v‖) atTop (nhds ‖v‖) := by
  replace h := eq_of_le_of_ge h (double_dual_bound _ _ v)
  by_cases hv : v = 0
  · use 0
    simp [hv]
  ·
    have : ∀ n : ℕ, ∃ f : StrongDual 𝕜 E, ‖f‖ ≤ 1 ∧ ‖v‖ - 1/(n+1) < ‖f v‖ := by
      intro n
      rw [ContinuousLinearMap.norm_def] at h
      -- conv_rhs at h => arg 1; arg 1; ext c; arg 2; ext x; rw [dual_def]
      have : ‖v‖ - 1/(n+1) ∉ {c | 0 ≤ c ∧ ∀ (f : StrongDual 𝕜 E), ‖f v‖ ≤ c * ‖f‖} := by
        intro hmem
        have : ‖v‖ - 1/(n+1) ≥ sInf {c | 0 ≤ c ∧ ∀ (f : StrongDual 𝕜 E), ‖f v‖ ≤ c * ‖f‖} :=
          csInf_le ⟨0, fun c hc => by simp_all⟩ (by simp_all)
        simp_all
        linarith
      simp at this
      
end norm




open scoped TensorProduct
open Module Submodule Free


theorem exists_dual_vec_ne_zero (R : Type*) {M : Type*}
    [DivisionRing R] [AddCommGroup M] [Module R M] :
    ∀ v : M, v ≠ 0 → ∃ dv : Dual R M, dv v ≠ 0 := fun v hv => by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (LinearPMap.mkSpanSingleton (K := R) v (1 : R) (hv)).toFun
  use g, fun hc => ?_
  have hp := LinearMap.congr_fun hg ⟨v, mem_span_singleton_self v⟩
  rw [LinearPMap.toFun_eq_coe] at hp
  simp [hc] at hp


variable {R : Type*} {S : Type*} {M : Type*} {N : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N]

lemma as_sum_on_basis [Module.Free R N] [Module.Free S M] (x : M ⊗[R] N) :
    let bm := chooseBasis S M
    let bn := chooseBasis R N
    let b := Basis.tensorProduct bm bn
    x = ∑ i ∈ (b.repr x).support, (b.repr x) i • (bm i.1 ⊗ₜ[R] bn i.2) := by
  intro bn bm b
  nth_rw 1 [← b.linearCombination_repr x, Finsupp.linearCombination_apply S (b.repr x),
    Finsupp.sum_of_support_subset (b.repr x) (fun _ a ↦ a) _ (by simp)]
  congr with _
  simp [b, Module.Basis.tensorProduct_apply']




variable {R : Type*} {S : Type*} {M : Type*} {N : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N]


-- lemma TensorProduct.eq_zero_of_dual_apply_sum_eq_zero
--     [Module.Free R N] [Module.Free S M] (u : M ⊗[R] N) :
--     let bm := chooseBasis S M
--     let bn := chooseBasis R N
--     let b := Basis.tensorProduct bm bn
--     (∀ ψ : Dual R N, ∑ i ∈ (b.repr u).support, ψ (bn i.2) • bm i.1 = 0) → u = 0 := by
--   intro bm bn b
--   contrapose!
--   intro hu
--   by_cases hi : ∃ i : ChooseBasisIndex S M × ChooseBasisIndex R N, bm i.1 ≠ 0
--   .
