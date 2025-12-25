import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.HahnBanach




open PiTensorProduct Finset NormedSpace
open scoped TensorProduct

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]


noncomputable def liftedLinearfamily (g : (i : ι) → StrongDual 𝕜 (E i))
    : (⨂[𝕜] i, E i) →ₗ[𝕜] 𝕜 := lift {
  toFun m := ∏ i, (g i) (m i)
  map_update_add' _ i _ _:= by
    simp only [prod_eq_mul_prod_diff_singleton (mem_univ i), Function.update_self, map_add, add_mul]
    congr 2 <;> aesop (add safe apply Finset.prod_congr)
  map_update_smul' := by
    intro _ m i c x
    simp only [prod_eq_mul_prod_diff_singleton (mem_univ i), Function.update_self, map_smul,
      smul_eq_mul, ←mul_assoc]
    congr 1
    aesop (add safe apply Finset.prod_congr)
}

@[simp]
lemma liftedLinearfamily_apply {g : Π i, StrongDual 𝕜 (E i)}
    {m : Π i, E i} (hg : ∀ i, ‖(g i) (m i)‖ = ‖m i‖)
    : ‖liftedLinearfamily g (⨂ₜ[𝕜] i, m i)‖ = ∏ i, ‖m i‖ := by
  simp [liftedLinearfamily, hg]

theorem projectiveSeminorm_tprod (m : Π i, E i) {g : (i : ι) → StrongDual 𝕜 (E i)}
    (hg₁ : ∀ (i : ι), ‖g i‖ = 1) (hg₂ : ∀ (i : ι), ‖(g i) (m i)‖ = ‖m i‖)
    : projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  by_cases hz : ∀ i, m i ≠ 0
  · apply eq_of_le_of_ge (projectiveSeminorm_tprod_le m)
    haveI := nonempty_subtype.mpr (nonempty_lifts (⨂ₜ[𝕜] i, m i))
    apply le_ciInf (fun x => ?_)
    have h : ‖∏ i, (g i) (m i)‖ = ∏ i, ‖m i‖ := by simp [hg₂]
    have hx := congr_arg (‖·‖) (congr_arg (liftedLinearfamily g) ((mem_lifts_iff _ _).mp x.prop))
    simp only [map_list_sum, List.map_map, liftedLinearfamily_apply hg₂] at hx
    rw [← hx]
    trans ((List.map (norm) (List.map (⇑(liftedLinearfamily g) ∘ fun x ↦ x.1 • ⨂ₜ[𝕜] (i : ι), x.2 i)
          (FreeAddMonoid.toList x.val))).sum)
    · apply List.le_sum_nonempty_of_subadditive norm norm_add_le
      intro hx₂
      simp_all only [ne_eq, nonempty_subtype, norm_prod, List.empty_eq, List.sum_nil, norm_zero,
        List.map_eq_nil_iff]
      simpa [hz] using prod_eq_zero_iff.mp hx.symm
    · rw [List.map_map]
      apply List.sum_le_sum (fun p hp => ?_)
      simp only [liftedLinearfamily, Function.comp_apply, map_smul, lift.tprod,
        MultilinearMap.coe_mk, smul_eq_mul, norm_mul, norm_prod]
      gcongr with i hi
      simpa using (ContinuousLinearMap.opNorm_le_iff (by simp : (0 : ℝ) ≤ 1)).mp (hg₁ i).le _
  · simp only [ne_eq, not_forall, not_not] at hz
    rw [show (⨂ₜ[𝕜] (i : ι), m i) = 0 from zero_tprodCoeff' _ _ _ hz.choose_spec]
    simpa using (Finset.prod_eq_zero_iff.mpr ⟨hz.choose, by simp [hz.choose_spec]⟩).symm


variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem projectiveSeminorm_tprod_rclike [∀ i, Nontrivial (E i)] (m : Π i, E i)
    : projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  choose g hg₁ hg₂ using fun i => exists_dual_vector' 𝕜 (m i)
  exact projectiveSeminorm_tprod m hg₁ (by simp [hg₂])
