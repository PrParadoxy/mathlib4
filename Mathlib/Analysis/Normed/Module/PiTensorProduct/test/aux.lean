import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

section norm

variable {𝕜 : Type*} {E : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter NormedSpace PiTensorProduct

theorem dual_seq_tendsto_norm {v : E} (h : ‖v‖ ≤ ‖inclusionInDoubleDual 𝕜 E v‖) :
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
    _ < ‖v‖ / (n + 1) := by linarith [hg n]
    _ ≤ ‖v‖ / (N + 1) := by gcongr
    _ < ‖v‖ / N := by gcongr; simp
    _ < ε := (div_lt_comm₀ hε hN').mp hN

lemma dual_seq_tendsto_norm_pos {v : E} {g : ℕ → StrongDual 𝕜 E}
    (h₁ : 0 < ‖v‖) (h₂ : Tendsto (fun i => ‖g i v‖ / ‖g i‖) atTop (nhds ‖v‖))
    : ∀ᶠ n : ℕ in atTop, 0 < ‖g n‖ := by
  have hp : ∀ᶠ n in atTop, ‖v‖ / 2 < ‖(g n) v‖ / ‖g n‖ :=
    (h₂).eventually (lt_mem_nhds (by linarith))
  filter_upwards [hp] with n hv
  by_contra! hc
  simp only [show g n = 0 by simp_all, ContinuousLinearMap.zero_apply, norm_zero, div_zero] at hv
  linarith

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem projectiveSeminorm_tprod_eq_of_normed_space (m : Π i, E i)
    (h_le_bidual : ∀ i, ‖m i‖ ≤ ‖inclusionInDoubleDual 𝕜 _ (m i)‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  by_cases hm : ∀ i, m i ≠ 0
  · apply eq_of_le_of_ge (projectiveSeminorm_tprod_le m)
    choose g hg using fun i => dual_seq_tendsto_norm (h_le_bidual i)
    haveI := nonempty_subtype.mpr (nonempty_lifts (⨂ₜ[𝕜] i, m i))
    apply le_ciInf (fun x ↦ le_of_tendsto_of_tendsto
      (tendsto_finset_prod (Finset.univ (α := ι)) (fun i hi => hg i)) tendsto_const_nhds ?_)
    filter_upwards [eventually_all.mpr (fun i => dual_seq_tendsto_norm_pos (by simp [hm]) (hg i))]
    intro n hg
    have hgp : 0 < ∏ i, ‖g i n‖ := Finset.prod_pos fun i a ↦ hg i
    have hx := congr_arg (norm ∘ dualDistrib (⨂ₜ[𝕜] i, g i n)) ((mem_lifts_iff _ _).mp x.prop)
    simp only [Function.comp_apply, dualDistrib_apply, ContinuousLinearMap.coe_coe, norm_prod,
      map_list_sum, List.map_map] at hx
    grw [Finset.prod_div_distrib, ← hx, List.le_sum_of_subadditive norm norm_zero.le norm_add_le,
      List.map_map, div_le_iff₀' hgp, projectiveSeminormAux, ← List.sum_map_mul_left]
    apply List.sum_le_sum (fun _ _ ↦ ?_)
    simp only [Function.comp_apply, map_smul, dualDistrib_apply,
      ContinuousLinearMap.coe_coe, smul_eq_mul, norm_mul, norm_prod,
      ← div_le_iff₀' hgp, ← mul_div_assoc', ← Finset.prod_div_distrib]
    gcongr
    grw [ContinuousLinearMap.le_opNorm, ← mul_div_assoc', mul_div_left_comm,
      div_self (by simp_all), mul_one]
  · simp only [ne_eq, not_forall, not_not] at hm
    obtain ⟨i, hi⟩ := hm
    conv_rhs => rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    rw [tprod_eq_tprodCoeff_one, zero_tprodCoeff' 1 m i hi, norm_zero]


-- theorem projectiveSeminorm_tprod_eq_of_dual_vectors {f : Π i, StrongDual 𝕜 (E i)}
--     (m : Π i, E i) (hf₁ : ∀ i, ‖f i‖ ≤ 1) (hf₂ : ∀ i, ‖f i (m i)‖ = ‖m i‖) :
--     ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
--   apply eq_of_le_of_ge (projectiveSeminorm_tprod_le m)
--   haveI := nonempty_subtype.mpr (nonempty_lifts (⨂ₜ[𝕜] i, m i))
--   apply le_ciInf (fun x ↦ ?_)
--   have hx := congr_arg (norm ∘ dualDistrib (⨂ₜ[𝕜] i, f i)) ((mem_lifts_iff _ _).mp x.prop)
--   simp only [Function.comp_apply, dualDistrib_apply, ContinuousLinearMap.coe_coe, hf₂, norm_prod,
--      map_list_sum, List.map_map] at hx
--   grw [← hx, List.le_sum_of_subadditive norm norm_zero.le norm_add_le, List.map_map]
--   apply List.sum_le_sum (fun _ _ ↦ ?_)
--   simp only [Function.comp_apply, map_smul, dualDistrib_apply, ContinuousLinearMap.coe_coe,
--     smul_eq_mul, norm_mul, norm_prod]
--   gcongr
--   grw [ContinuousLinearMap.le_opNorm, hf₁, one_mul]

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
