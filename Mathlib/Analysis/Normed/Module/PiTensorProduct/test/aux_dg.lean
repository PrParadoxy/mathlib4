import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Topology.Order.IsLUB

section norm

open PiTensorProduct
open scoped TensorProduct


open Filter NormedSpace ContinuousLinearMap Set

section seq

variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G 𝓕 : Type*}

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup Fₗ]
  [SeminormedAddCommGroup G]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomIsometric σ₁₂]

theorem opNorm_IsLUB (f : E →SL[σ₁₂] F) : IsLUB (Set.range (fun x : E ↦ ‖f x‖ / ‖x‖)) ‖f‖ := by
  refine ⟨fun _ ↦ ?_, fun _ hb ↦ ?_⟩
  · aesop (add safe forward ratio_le_opNorm)
  · simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
    refine opNorm_le_bound' f (by simpa using hb 0) (fun e _ => ?_)
    grw [←div_le_iff₀ (by positivity), hb e]


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
instance (x : ⨂[𝕜] i, E i) : Nonempty ↑x.lifts := nonempty_subtype.mpr (nonempty_lifts x)


open ContinuousLinearMap Set in
theorem projectiveSeminorm_tprod_eq_of_bidual_iso
    (m : Π i, E i) (h_bidual : ∀ i, ‖m i‖ = ‖inclusionInDoubleDual 𝕜 _ (m i)‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  choose g hg using fun i ↦ exists_seq_of_bidual_iso (h_bidual i)
  apply le_antisymm (projectiveSeminorm_tprod_le m)
  apply le_ciInf (fun p ↦ le_of_tendsto_of_tendsto
    (tendsto_finset_prod _ (fun i _ ↦ hg i)) tendsto_const_nhds ?_)
  filter_upwards with n
  have hp := congr_arg (fun x ↦ ‖dualDistrib (⨂ₜ[𝕜] i, g i n) x‖ / (∏ i, ‖g i n‖))
    ((mem_lifts_iff _ _).mp p.prop)
  simp only [dualDistrib_apply, coe_coe, norm_prod] at hp
  rw [Finset.prod_div_distrib, ← hp, map_list_sum, List.map_map]
  refine if hz : ∏ i, ‖g i n‖ = 0 then (by simp_all [projectiveSeminormAux_nonneg]) else ?_
  grw [div_le_iff₀' (by positivity), List.le_sum_of_subadditive norm norm_zero.le norm_add_le,
    List.map_map, projectiveSeminormAux, ← List.sum_map_mul_left]
  apply List.sum_le_sum (fun q hq ↦ ?_)
  simp only [Function.comp_apply, map_smul, dualDistrib_apply, coe_coe, smul_eq_mul, norm_mul,
    norm_prod, mul_left_comm, ← Finset.prod_mul_distrib]
  gcongr
  grw [le_opNorm]


variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem projectiveSeminorm_tprod_eq_of_dual_vectors'
    (m : Π i, E i) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_eq_of_dual_vectors _
    (fun i => show ‖m i‖ = ‖inclusionInDoubleDualLi 𝕜 (m i)‖ by simp)





end norm

section RCLike

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

@[simp]
theorem projectiveSeminorm_tprod(m : Π i, E i) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_eq_of_bidual_iso m
    (fun i ↦ show ‖m i‖ = ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (m i)‖ by simp)

end RCLike
