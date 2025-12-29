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

theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G)
    (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * projectiveSeminorm x := by
  letI := nonempty_subtype.mpr (nonempty_lifts x)
  rw [projectiveSeminorm_apply, mul_comm, Real.iInf_mul_of_nonneg (norm_nonneg _)]
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

noncomputable instance projectiveSeminormedAddCommGroup :
  SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

noncomputable instance projectiveNormedSpace :
  NormedSpace 𝕜 (⨂[𝕜] i, E i) where
    norm_smul_le a x := by
      change projectiveSeminorm.toFun (a • x) ≤ _
      rw [projectiveSeminorm.smul']
      rfl


variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F)

@[simps]
noncomputable def liftEquiv_pi : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x ↦
      norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_add, map_add,
    LinearMap.mkContinuous_apply, LinearMap.add_apply, ContinuousLinearMap.add_apply]
  map_smul' a f := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_smul, map_smul,
    LinearMap.mkContinuous_apply, LinearMap.smul_apply, RingHom.id_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x ↦ by
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe]
    exact ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
  left_inv f := by ext x; simp only [LinearMap.mkContinuous_coe, LinearEquiv.symm_apply_apply,
      MultilinearMap.coe_mkContinuous, ContinuousMultilinearMap.coe_coe]
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    apply PiTensorProduct.ext; ext m
    simp

noncomputable def liftIsometry_pi : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
  { liftEquiv_pi 𝕜 E F with
    norm_map' := by
      intro f
      refine le_antisymm ?_ ?_
      · simp only [liftEquiv_pi]
        simp only [lift_symm, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
        exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
      · simp only [liftEquiv_pi]
        conv_lhs => rw [← (liftEquiv_pi 𝕜 E F).symm_apply_apply f]
        rw [liftEquiv_pi_symm_apply]
        exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _ }


variable {𝕜 E F}

@[simp]
theorem liftIsometry_pi_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    liftIsometry_pi 𝕜 E F f x = lift f.toMultilinearMap x := by
  simp only [liftIsometry_pi, LinearIsometryEquiv.coe_mk, liftEquiv_pi_apply,
    LinearMap.mkContinuous_apply]

variable (𝕜) in
/-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`.
-/
@[simps!]
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  (liftIsometry_pi 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]
theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
  ext m
  simp only [ContinuousMultilinearMap.coe_coe, tprodL_toFun]

@[simp]
theorem liftIsometry_pi_symm_apply (l : (⨂[𝕜] i, E i) →L[𝕜] F) :
    (liftIsometry_pi 𝕜 E F).symm l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
  rfl

@[simp]
theorem liftIsometry_pi_tprodL :
    liftIsometry_pi 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext _
  simp only [liftIsometry_pi_apply_apply, tprodL_coe, lift_tprod, LinearMap.id_coe, id_eq,
    ContinuousLinearMap.coe_id']

theorem norm_tprodL_le : ‖tprodL 𝕜 (E := E)‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one ?_
  intro m
  simp only [tprodL_toFun, one_mul]
  apply projectiveSeminorm_tprod_le m

section map

variable {E' E'' : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable [∀ i, SeminormedAddCommGroup (E'' i)] [∀ i, NormedSpace 𝕜 (E'' i)]
variable (g : Π i, E' i →L[𝕜] E'' i) (f : Π i, E i →L[𝕜] E' i)

/--
Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.
-/
noncomputable def mapL : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  liftIsometry_pi 𝕜 E _ <| (tprodL 𝕜).compContinuousLinearMap f

@[simp]
theorem mapL_coe : (mapL f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := by
  ext
  simp only [mapL, LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe,
    liftIsometry_pi_apply_apply, lift.tprod, ContinuousMultilinearMap.coe_coe,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, tprodL_toFun, map_tprod]

@[simp]
theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i ↦ (f i).toLinearMap) x := by
  rfl

/-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`.
-/
@[simp]
noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →L[𝕜] ⨂[𝕜] i, E i :=
  mapL fun (i : ι) ↦ (p i).subtypeL

theorem mapL_comp : mapL (fun (i : ι) ↦ g i ∘L f i) = mapL g ∘L mapL f := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp only [mapL_coe, ContinuousLinearMap.coe_comp, LinearMap.compMultilinearMap_apply, map_tprod,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]

theorem liftIsometry_pi_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
    liftIsometry_pi 𝕜 E' F h ∘L mapL f = liftIsometry_pi 𝕜 E F (h.compContinuousLinearMap f) := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp only [ContinuousLinearMap.coe_comp, mapL_coe, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, map_tprod,
    liftIsometry_pi_apply_apply, lift.tprod, ContinuousMultilinearMap.coe_coe,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

@[simp]
theorem mapL_id : mapL (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp only [mapL_coe, ContinuousLinearMap.coe_id, map_id, LinearMap.compMultilinearMap_apply,
    LinearMap.id_coe, id_eq]

@[simp]
theorem mapL_one : mapL (fun (i : ι) ↦ (1 : E i →L[𝕜] E i)) = 1 :=
  mapL_id

theorem mapL_mul (f₁ f₂ : Π i, E i →L[𝕜] E i) :
    mapL (fun i ↦ f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
  mapL_comp f₁ f₂

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
@[simps]
noncomputable def mapLMonoidHom : (Π i, E i →L[𝕜] E i) →* ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E i) where
  toFun := mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]
protected theorem mapL_pow (f : Π i, E i →L[𝕜] E i) (n : ℕ) :
    mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom f n

-- We redeclare `ι` here, and later dependent arguments,
-- to avoid the `[Fintype ι]` assumption present throughout the rest of the file.
open Function in
private theorem mapL_add_smul_aux {ι : Type uι}
    {E : ι → Type uE} [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
    {E' : ι → Type u_1} [(i : ι) → SeminormedAddCommGroup (E' i)] [(i : ι) → NormedSpace 𝕜 (E' i)]
    (f : (i : ι) → E i →L[𝕜] E' i)
    [DecidableEq ι] (i : ι) (u : E i →L[𝕜] E' i) :
    (fun j ↦ (update f i u j).toLinearMap) =
      update (fun j ↦ (f j).toLinearMap) i u.toLinearMap := by
  grind

open Function in
protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i →L[𝕜] E' i) :
    mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
  ext x
  simp only [mapL_apply, mapL_add_smul_aux, ContinuousLinearMap.coe_add,
    PiTensorProduct.map_update_add, LinearMap.add_apply, ContinuousLinearMap.add_apply]

open Function in
protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i →L[𝕜] E' i) :
    mapL (update f i (c • u)) = c • mapL (update f i u) := by
  ext x
  simp only [mapL_apply, mapL_add_smul_aux, ContinuousLinearMap.coe_smul,
    PiTensorProduct.map_update_smul, LinearMap.smul_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply]

theorem mapL_opNorm : ‖mapL f‖ ≤ ∏ i, ‖f i‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro x
  rw [mapL, liftIsometry_pi]
  simp only [LinearIsometryEquiv.coe_mk, liftEquiv_pi_apply, LinearMap.mkContinuous_apply]
  refine le_trans (norm_eval_le_projectiveSeminorm _ _)
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
  rw [ContinuousMultilinearMap.opNorm_le_iff (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))]
  intro m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine le_trans (projectiveSeminorm_tprod_le (fun i ↦ (f i) (m i))) ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ ContinuousLinearMap.le_opNorm _ _)

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
the family.
-/
@[simps!]
noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E i →L[𝕜] E' i)
    ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i) :=
  MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ ↦ PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ ↦ PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f ↦ by rw [one_mul]; exact mapL_opNorm f)

variable {𝕜 E E'}

theorem mapLMultilinear_opNorm : ‖mapLMultilinear 𝕜 E E'‖ ≤ 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

end map

section dualCharacterization

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (F) in
/-- The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`.
-/
@[simps!]
noncomputable def toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := LinearMap.mkContinuous
    ((LinearMap.flip (lift (R := 𝕜) (s := E) (E := F)).toLinearMap x) ∘ₗ
    ContinuousMultilinearMap.toMultilinearMapLinear)
    (projectiveSeminorm x)
    (fun _ ↦ by simp only [LinearMap.coe_comp, Function.comp_apply,
                  ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.flip_apply,
                  LinearEquiv.coe_coe, mul_comm]
                exact norm_eval_le_projectiveSeminorm _ _ )
  map_add' x y := by
    ext _
    simp only [map_add, LinearMap.mkContinuous_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.add_apply,
      LinearMap.flip_apply, LinearEquiv.coe_coe, ContinuousLinearMap.add_apply]
  map_smul' a x := by
    ext _
    simp only [map_smul, LinearMap.mkContinuous_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, LinearEquiv.coe_coe, RingHom.id_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply]

theorem toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMap F x‖ ≤ projectiveSeminorm x := by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (apply_nonneg _ _)


/-- The injective seminorm on `⨂[𝕜] i, Eᵢ`. Morally, it sends `x` in `⨂[𝕜] i, Eᵢ` to the
`sup` of the operator norms of the `PiTensorProduct.toDualContinuousMultilinearMap F x`, for all
normed vector spaces `F`. In fact, we only take in the same universe as `⨂[𝕜] i, Eᵢ`, and then
prove in `PiTensorProduct.norm_eval_le_injectiveSeminorm` that this gives the same result.
-/
noncomputable irreducible_def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | ∃ (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
  (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}

lemma dualSeminorms_bounded : BddAbove {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))} := by
  existsi projectiveSeminorm
  rw [mem_upperBounds]
  simp only [Set.mem_setOf_eq, forall_exists_index]
  intro p G _ _ hp
  rw [hp]
  intro x
  simp only [Seminorm.comp_apply, coe_normSeminorm]
  exact toDualContinuousMultilinearMap_le_projectiveSeminorm _

theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}, p.1 x := by
  simpa only [injectiveSeminorm, Set.coe_setOf, Set.mem_setOf_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

theorem injectiveSeminorm_le_projectiveSeminorm :
    injectiveSeminorm (𝕜 := 𝕜) (E := E) ≤ projectiveSeminorm := by
  rw [injectiveSeminorm]
  refine csSup_le ?_ ?_
  · existsi 0
    simp only [Set.mem_setOf_eq]
    existsi PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    rw [Subsingleton.elim (toDualContinuousMultilinearMap PUnit.{(max (max uE uι) u𝕜) + 1} x) 0,
      norm_zero]
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    obtain ⟨G, _, _, h⟩ := hp
    rw [h]; intro x; simp only [Seminorm.comp_apply, coe_normSeminorm]
    exact toDualContinuousMultilinearMap_le_projectiveSeminorm _

theorem injectiveSeminorm_equals_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
  injectiveSeminorm x = projectiveSeminorm x := by
  apply eq_of_le_of_ge (injectiveSeminorm_le_projectiveSeminorm x)
  dsimp
  rw [injectiveSeminorm_apply]
  refine le_ciSup_of_le ?_ ?_ ?_
  ·
    obtain ⟨M, hM⟩ := dualSeminorms_bounded (𝕜 := 𝕜) (E := E)
    refine ⟨M x, ?_⟩
    intro p hp

    simp_all

    simp only [Set.mem_range, forall_exists_index, Subtype.exists, Set.mem_setOf_eq]

    refine ⟨injectiveSeminorm x, ?_⟩

    exact hM hp x



    refine ⟨injectiveSeminorm x, ?_⟩
    rintro _ ⟨p, rfl⟩
    rw [injectiveSeminorm_apply]

    refine le_ciSup (α:=ℝ) ?_ p
    -- boundedness of the range
    refine ⟨injectiveSeminorm x, ?_⟩
    rintro _ ⟨q, rfl⟩
    -- unfold once, then use the defining property of `sSup`
    simp [injectiveSeminorm_apply]

    refine ⟨injectiveSeminorm x, ?_⟩
    rintro _ ⟨p, rfl⟩
    simp
    rw [injectiveSeminorm_apply]
    refine ⟨injectiveSeminorm x, ?_⟩

    rintro _ ⟨p, rfl⟩
    exact le_iSup (fun q : {p | ∃ G, _} => (q : Seminorm 𝕜 _) x) p



    apply le_iSup

    rw [<-injectiveSeminorm_apply]

    rw [<-injectiveSeminorm_apply]

    exact toDualContinuousMultilinearMap_le_projectiveSeminorm x

    simp [Set.range]
    have h := dualSeminorms_bounded (𝕜:=𝕜) (E:=E)
    sorry

    erw [Seminorm.comp_apply] at h

    erw [<-Seminorm.comp_apply]
    simp [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm] at h
    simp [Seminorm.sSup_apply, dualSeminorms_bounded, h]

  · constructor
    · use (⨂[𝕜] (i : ι), E i)
      use projectiveSeminormedAddCommGroup
      use projectiveNormedSpace
  · have h :=
      ContinuousLinearMap.le_opNorm
        ((toDualContinuousMultilinearMap (⨂[𝕜] (i : ι), E i)) x)
        (tprodL 𝕜)
    grw [norm_tprodL_le] at h
    simp at h
    assumption

end dualCharacterization


end PiTensorProduct
