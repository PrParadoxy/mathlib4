import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Topology.Order.IsLUB

section norm

open PiTensorProduct

open Filter NormedSpace

section seq

variable {𝕜 : Type*} {E : Type*}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

open ContinuousLinearMap Set in
theorem exists_seq_of_bidual_iso {v : E} (h_bidual : ‖v‖ = ‖inclusionInDoubleDual 𝕜 E v‖) :
    ∃ g : ℕ → StrongDual 𝕜 E, Tendsto (fun i ↦ ‖g i v‖ / ‖g i‖) atTop (nhds ‖v‖) := by
  obtain ⟨u, ⟨_, _, h_tendsto, h_elem⟩⟩ := (IsLUB.exists_seq_monotone_tendsto
    (opNorm_IsLUB (inclusionInDoubleDual 𝕜 E v)) ⟨0, ⟨0, by simp⟩⟩)
  simp only [dual_def, mem_range] at h_elem
  choose g hg using h_elem
  exact ⟨g, by simp_all⟩

end seq

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

open ContinuousLinearMap Set in
theorem projectiveSeminorm_tprod_eq_of_dual_vectors
    (m : Π i, E i) (h_bidual : ∀ i, ‖m i‖ = ‖inclusionInDoubleDual 𝕜 _ (m i)‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  choose g hg using fun i ↦ exists_seq_of_bidual_iso (h_bidual i)
  apply le_antisymm (projectiveSeminorm_tprod_le m)
  apply le_ciInf (fun p ↦ le_of_tendsto_of_tendsto
    (tendsto_finset_prod _ (fun i _ ↦ hg i)) tendsto_const_nhds ?_)
  filter_upwards with n
  have hp := congr_arg (fun x ↦ ‖dualDistrib (⨂ₜ[𝕜] i, g i n) x‖ / (∏ i, ‖g i n‖))
    ((mem_lifts_iff _ _).mp p.prop)
  simp only [dualDistrib_apply, ContinuousLinearMap.coe_coe, norm_prod] at hp
  rw [Finset.prod_div_distrib, ← hp, map_list_sum, List.map_map]
  refine if hz : ∏ i, ‖g i n‖ = 0 then (by simp_all [projectiveSeminormAux_nonneg]) else ?_
  grw [div_le_iff₀' (by positivity), List.le_sum_of_subadditive norm norm_zero.le norm_add_le,
    List.map_map, projectiveSeminormAux, ← List.sum_map_mul_left]
  apply List.sum_le_sum (fun q hq ↦ ?_)
  simp only [Function.comp_apply, map_smul, dualDistrib_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, norm_mul, norm_prod, mul_left_comm, ← Finset.prod_mul_distrib]
  gcongr
  grw [ContinuousLinearMap.le_opNorm, mul_comm]

end norm
