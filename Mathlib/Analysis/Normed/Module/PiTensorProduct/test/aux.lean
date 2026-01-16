import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm

section norm

variable {𝕜 : Type*} {E : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter NormedSpace PiTensorProduct

theorem norm_seq {v : E} (h : ‖v‖ ≤ ‖inclusionInDoubleDual 𝕜 E v‖) :
    ∃ g : ℕ → StrongDual 𝕜 E, Tendsto (fun i => ‖g i v‖ / ‖g i‖) atTop (nhds ‖v‖) := by
  by_cases hv : v = 0
  any_goals aesop
  replace h : ‖v‖ = sInf {c | 0 ≤ c ∧ ∀ (x : StrongDual 𝕜 E), ‖x v‖ ≤ c * ‖x‖} := by
    simp [eq_of_le_of_ge h (double_dual_bound _ _ v), ContinuousLinearMap.norm_def]
  have hs : ∀ n : ℕ, ∃ f : StrongDual 𝕜 E, (‖v‖ - ‖v‖ / (n + 1)) < ‖f v‖ / ‖f‖ := by
    intro n
    have hn : ‖v‖ - ‖v‖ / (n+1) ∉ {c | 0 ≤ c ∧ ∀ (f : StrongDual 𝕜 E), ‖f v‖ ≤ c * ‖f‖} := by
      intro hmem
      have hp := csInf_le ⟨0, fun c hc => hc.1⟩ hmem
      simp only [← h, le_sub_self_iff] at hp
      linarith [show 0 < ‖v‖ / (↑n + 1) by positivity]
    replace hn : ∃ x : StrongDual 𝕜 E, (‖v‖ - ‖v‖ / (↑n + 1)) * ‖x‖ < ‖x v‖ := by
      simp only [Set.mem_setOf_eq, sub_nonneg, not_and, not_forall, not_le] at hn
      exact hn (by field_simp; norm_cast; omega)
    choose f hf using hn
    exact ⟨f, (lt_div_iff₀ (by aesop : 0 < ‖f‖)).mpr hf⟩
  choose g hg using hs
  use g
  apply NormedAddCommGroup.tendsto_atTop.mpr (fun ε hε => ?_)
  have ⟨N, hN⟩ := exists_nat_gt (‖v‖ / ε)
  have hN' : 0 < (N : ℝ) := by linarith [show 0 < ‖v‖ / ε by positivity]
  use N, fun n hn => ?_
  have hu : ‖(g n) v‖ / ‖g n‖ ≤ ‖v‖ := by
    by_cases hz : g n = 0
    · simp [hz]
    · grw [div_le_iff₀ (by positivity), (g n).le_opNorm v, mul_comm]
  simp only [Real.norm_eq_abs, abs_sub_comm, gt_iff_lt]
  rw [abs_of_nonneg (by linarith [hg n])]
  calc
    _ < ‖v‖ / (↑n + 1) := by linarith [hg n]
    _ ≤ ‖v‖ / (↑N + 1) := by gcongr
    _ < ‖v‖ / ↑N := by gcongr; simp
    _ < ε := (div_lt_comm₀ hε hN').mp hN




variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem projectiveSeminorm_tprod_eq_of_normed_space (m : Π i, E i)
    (h_le_bidual : ∀ i, ‖m i‖ ≤ ‖inclusionInDoubleDual 𝕜 _ (m i)‖ ) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  apply eq_of_le_of_ge (projectiveSeminorm_tprod_le m)
  choose g hg using fun i => norm_seq (h_le_bidual i)
  

  -- haveI := nonempty_subtype.mpr (nonempty_lifts (⨂ₜ[𝕜] i, m i))
  -- apply le_ciInf (fun x ↦ ?_)
  -- have := ((mem_lifts_iff _ _).mp x.prop)






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
