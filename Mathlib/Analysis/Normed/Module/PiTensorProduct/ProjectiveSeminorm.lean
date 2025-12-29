/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a nontrivially normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"projective seminorm". For `x` an element of `⨂[𝕜] i, Eᵢ`, its projective seminorm is the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.

In particular, every norm `‖.‖` on `⨂[𝕜] i, Eᵢ` satisfying `‖⨂ₜ[𝕜] i, m i‖ ≤ Π i, ‖m i‖`
for every `m` in `Π i, Eᵢ` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `⨂[𝕜] i, Eᵢ`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
  `E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.

## TODO
* The projective seminorm is multiplicative if the evaluation map embedding `Eᵢ`
into its bidual is an isometry for every `i`. Under the slightly stronger
assumption that every `mᵢ` attains its norm over the closed unit ball of the
continuous dual, this is proved by `projectiveSeminorm_tprod_of_dual_vectors`.
(By Hahn-Banach, this always happens over `ℝ` or `ℂ`). TBD: Treat the more
general case where the supremum may not be attained.
* The functoriality.

-/

@[expose] public section

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)]

open scoped TensorProduct

namespace PiTensorProduct

/-- A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to prove the
properties of `projectiveSeminorm`.
-/
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ :=
  fun p => (p.toList.map (fun p ↦ ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum

theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
    0 ≤ projectiveSeminormAux p := by
  simp only [projectiveSeminormAux]
  refine List.sum_nonneg ?_
  intro a
  simp only [List.mem_map, Prod.exists, forall_exists_index,
    and_imp]
  intro x m _ h
  rw [← h]
  exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))

theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
    projectiveSeminormAux (p + q) ≤ projectiveSeminormAux p + projectiveSeminormAux q := by
  simp [projectiveSeminormAux]

theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
    projectiveSeminormAux (p.map (fun (y : 𝕜 × Π i, E i) ↦ (a * y.1, y.2))) =
    ‖a‖ * projectiveSeminormAux p := by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

variable [∀ i, NormedSpace 𝕜 (E i)]

theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
    BddBelow (Set.range (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) := by
  existsi 0
  rw [mem_lowerBounds]
  simp only [Set.mem_range, Subtype.exists, exists_prop, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact fun p _ ↦ projectiveSeminormAux_nonneg p

/-- The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ` to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.
-/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := by
  refine Seminorm.ofSMulLE (fun x ↦ iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) ?_ ?_ ?_
  · refine le_antisymm ?_ ?_
    · refine ciInf_le_of_le (bddBelow_projectiveSemiNormAux (0 : ⨂[𝕜] i, E i)) ⟨0, lifts_zero⟩ ?_
      rfl
    · letI : Nonempty (lifts 0) := ⟨0, lifts_zero (R := 𝕜) (s := E)⟩
      exact le_ciInf (fun p ↦ projectiveSeminormAux_nonneg p.1)
  · intro x y
    letI := nonempty_subtype.mpr (nonempty_lifts x); letI := nonempty_subtype.mpr (nonempty_lifts y)
    exact le_ciInf_add_ciInf (fun p q ↦ ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
      ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))
  · intro a x
    letI := nonempty_subtype.mpr (nonempty_lifts x)
    rw [Real.mul_iInf_of_nonneg (norm_nonneg _)]
    refine le_ciInf ?_
    intro p
    rw [← projectiveSeminormAux_smul]
    exact ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
      ⟨(p.1.map (fun y ↦ (a * y.1, y.2))), lifts_smul p.2 a⟩ (le_refl _)

theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    projectiveSeminorm x = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1) := rfl

theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ := by
  rw [projectiveSeminorm_apply]
  convert ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨FreeAddMonoid.of ((1 : 𝕜), m), ?_⟩
  · simp [projectiveSeminormAux]
  · rw [mem_lifts_iff, FreeAddMonoid.toList_of, List.map_singleton, List.sum_singleton, one_smul]

/- The projective seminorm is multiplicative, `projectiveSeminorm ⨂ₜ[𝕜] i, mᵢ = Π i, ‖mᵢ‖`, if for
every `mᵢ`, there exists a dual vector `gᵢ` of norm at most one, such that `‖gᵢ mᵢ‖ = ‖mᵢ‖`. -/
theorem projectiveSeminorm_tprod_of_dual_vectors {g : Π i, StrongDual 𝕜 (E i)}
    (m : Π i, E i) (hg₁ : ∀ i, ‖g i‖ ≤ 1) (hg₂ : ∀ i, ‖g i (m i)‖ = ‖m i‖) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  apply eq_of_le_of_ge (projectiveSeminorm_tprod_le m)
  haveI := nonempty_subtype.mpr (nonempty_lifts (⨂ₜ[𝕜] i, m i))
  apply le_ciInf (fun x ↦ ?_)
  have hx := congr_arg (norm ∘ dualDistrib (⨂ₜ[𝕜] i, g i)) ((mem_lifts_iff _ _).mp x.prop)
  simp only [Function.comp_apply, dualDistrib_apply, ContinuousLinearMap.coe_coe, hg₂, norm_prod,
     map_list_sum, List.map_map] at hx
  grw [← hx, List.le_sum_of_subadditive norm norm_zero.le norm_add_le, List.map_map]
  apply List.sum_le_sum (fun _ _ ↦ ?_)
  simp only [Function.comp_apply, map_smul, dualDistrib_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, norm_mul, norm_prod]
  gcongr
  grw [ContinuousLinearMap.le_opNorm, hg₁, one_mul]

section RCLike

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem projectiveSeminorm_tprod (m : Π i, E i)
    : projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  choose g hg₁ hg₂ using fun i ↦ exists_dual_vector'' 𝕜 (m i)
  exact projectiveSeminorm_tprod_of_dual_vectors m hg₁ (by simp [hg₂])

end RCLike

theorem norm_eval_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) (G : Type*) [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖lift f.toMultilinearMap x‖ ≤ projectiveSeminorm x * ‖f‖ := by
  letI := nonempty_subtype.mpr (nonempty_lifts x)
  rw [projectiveSeminorm_apply, Real.iInf_mul_of_nonneg (norm_nonneg _)]
  unfold projectiveSeminormAux
  refine le_ciInf ?_
  intro ⟨p, hp⟩
  rw [mem_lifts_iff] at hp
  conv_lhs => rw [← hp, ← List.sum_map_hom, ← Multiset.sum_coe]
  refine le_trans (norm_multiset_sum_le _) ?_
  simp only [Multiset.map_coe, List.map_map, Multiset.sum_coe]
  rw [mul_comm, ← smul_eq_mul, List.smul_sum]
  refine List.Forall₂.sum_le_sum ?_
  simp only [smul_eq_mul, List.map_map, List.forall₂_map_right_iff, Function.comp_apply,
    List.forall₂_map_left_iff, map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe,
    List.forall₂_same, Prod.forall]
  intro a m _
  rw [norm_smul, ← mul_assoc, mul_comm ‖f‖ _, mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)


-- variable {𝕜 : Type u𝕜} [RCLike 𝕜]
-- variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
-- variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
--
-- variable (𝕜 E F)
--
-- noncomputable def liftEquiv_pi : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
--   toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x ↦
--     by -- TBD: simplify
--       grw [mul_comm, norm_eval_le_projectiveSeminorm x F f]
--       rfl
--   map_add' f g := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_add, map_add,
--     LinearMap.mkContinuous_apply, LinearMap.add_apply, ContinuousLinearMap.add_apply]
--   map_smul' a f := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_smul, map_smul,
--     LinearMap.mkContinuous_apply, LinearMap.smul_apply, RingHom.id_apply,
--     ContinuousLinearMap.coe_smul', Pi.smul_apply]
--   invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x ↦ by
--     simp only [lift_symm, LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe]
--     exact ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
--   left_inv f := by ext x; simp only [LinearMap.mkContinuous_coe, LinearEquiv.symm_apply_apply,
--       MultilinearMap.coe_mkContinuous, ContinuousMultilinearMap.coe_coe]
--   right_inv l := by
--     rw [← ContinuousLinearMap.coe_inj]
--     apply PiTensorProduct.ext; ext m
--     simp
--
-- noncomputable def liftIsometry_pi : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
--   { liftEquiv_pi 𝕜 E F with
--     norm_map' := by
--       intro f
--       refine le_antisymm ?_ ?_
--       · simp only [liftEquiv_pi]
--         exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
--       · conv_lhs => rw [← (liftEquiv 𝕜 E F).symm_apply_apply f]
--         rw [liftEquiv_symm_apply]
--         exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _ }



end PiTensorProduct
