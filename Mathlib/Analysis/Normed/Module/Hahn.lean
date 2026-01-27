import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Module.HahnBanach

open RCLike Module ContinuousLinearEquiv Submodule

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E)

-- noncomputable def toSpanNonzeroSingleton' (x : E) (h : 0 < ‖x‖) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
--   ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)) ‖x‖ h
--     (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (by aesop))

-- noncomputable def coord' (x : E) (h : 0 < ‖x‖) : StrongDual 𝕜 (𝕜 ∙ x) :=
--   (toSpanNonzeroSingleton' 𝕜 x h).symm

-- @[simp]
-- theorem coord_norm''' (x : E) (h : 0 < ‖x‖) : ‖coord' 𝕜 x h‖ = ‖x‖⁻¹ := by
--   have h_inv (z : 𝕜 ∙ x) : ‖((toSpanNonzeroSingleton' 𝕜 x h).symm : (𝕜 ∙ x) →L[𝕜] 𝕜) z‖
--     = ‖x‖⁻¹ * ‖z.val‖ := by
--     apply ContinuousLinearEquiv.homothety_inverse _ h _
--       (fun _ => LinearEquiv.toSpanNonzeroSingleton_homothety _ _ (by aesop) _)
--   apply eq_of_le_of_ge
--   · exact ContinuousLinearMap.opNorm_le_bound _ (by simp) (fun q => (h_inv q).le)
--   · let z : 𝕜 ∙ x := ⟨(1 : 𝕜) • x, by simp⟩
--     apply (mul_le_mul_iff_left₀ (by simp [z, h] : 0 < ‖(z : E)‖)).mp
--     rw [← h_inv]
--     apply ContinuousLinearMap.le_opNorm

-- @[simp]
-- theorem coord_norm'' {x : E} (h : 0 < ‖x‖) : ‖(‖x‖ : 𝕜) • coord' 𝕜 x h‖ = 1 := by
--   simp [-algebraMap_smul, norm_smul, mul_inv_cancel₀ (ne_of_lt h).symm]

-- @[simp]
-- theorem coord_self' (x : E) (h : 0 < ‖x‖) :
--     (coord' 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
--   LinearEquiv.coord_self 𝕜 E x (by aesop)

-- theorem exists_dual_vector''' (x : E) (h : 0 < ‖x‖) :
--     ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
--   let p : Submodule 𝕜 E := 𝕜 ∙ x
--   let f := (‖x‖ : 𝕜) • coord' 𝕜 x h
--   obtain ⟨g, hg⟩ := exists_extension_norm_eq p f
--   refine ⟨g, ?_, ?_⟩
--   · rw [hg.2, coord_norm'']
--   · calc
--       g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) := by rw [Submodule.coe_mk]
--       _ = ((‖x‖ : 𝕜) • coord' 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) := by rw [← hg.1]
--       _ = ‖x‖ := by simp [-algebraMap_smul]


theorem exists_dual_vector'''' (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖x‖ := by
  by_cases hx : 0 < ‖x‖
  · let coord := (ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)) ‖x‖ hx
      (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (by aesop))).symm.toContinuousLinearMap
    obtain ⟨g, hg⟩ := exists_extension_norm_eq (𝕜 ∙ x) ((‖x‖ : 𝕜) • coord)
    refine ⟨g, ?_, ?_⟩
    · have h_inv (z : 𝕜 ∙ x) : ‖(coord : (𝕜 ∙ x) →L[𝕜] 𝕜) z‖ = ‖x‖⁻¹ * ‖z.val‖ := by
        apply ContinuousLinearEquiv.homothety_inverse _ hx _ (fun _ =>
          LinearEquiv.toSpanNonzeroSingleton_homothety _ x (fun h => by simp [h] at hx) _)
      simpa [hg.2, norm_smul, ←le_div_iff₀' hx, one_div] using
        ContinuousLinearMap.opNorm_le_bound _ (by simp) (fun q => (h_inv q).le)
    · calc
        g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) := by rw [Submodule.coe_mk]
        _ = ((‖x‖ : 𝕜) • coord) (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) := by rw [← hg.1]
        _ = ‖x‖ := by
          simp only [ContinuousLinearMap.coe_smul', coe_coe, Pi.smul_apply, smul_eq_mul, coord]
          conv_lhs => arg 2; apply LinearEquiv.coord_self 𝕜 E x (fun hq => by simp [hq] at hx)
          simp
  · exact ⟨0, by simp, by simp [le_antisymm (not_lt.mp hx) (norm_nonneg x)]⟩

