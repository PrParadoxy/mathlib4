/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.projectiveSeminorm_tprod

/-!
# Tensors with finite support

Given a family of modules `s : ι → Type*`, each with a distinguished element
`(s₀ i) : s i`, the _support_ of a tensor `t : ⨂ i, s i` is the set of indices
`i : ι` where `t` differs from `s₀ i`. (More precisely: the smallest set `S` such
that `t` is of the form `tₛ ⊗ (⨂ₜ i : Sᶜ, s₀ i)` with `tₛ : ⨂ i : S, s i`).
We define the module of tensors whose support is a finite set.

One may think of this type as an interpolation between `PiTensorProduct`s over
finite and over infinite types.

## Background and name

If the modules `s i` are unital algebras, (a suitable norm closure of) the
module of finitely-supported tensors with respect to `s₀ := fun i ↦ 1` is known as the
_infinite tensor product_ of the family `s`. In many-body physics, it is called the
_quasi-local algebra_. If the `s i` are Hilbert spaces and `s₀` a family of unit
vectors, the norm closure of the finitely-supported tensors is sometimes called
the _incomplete tensor product_ associated with the section `s₀`. Such Hilbert
spaces appear in the representation theory of infinite tensor products of C^*
algebras and are connected to superselection sectors of quantum lattice models.

The term "infinite tensor product" does not seem optimal here, given that
Mathlib's `PiTensorProduct` can handle tensors that actually have infinite
support. The term "local" also does not fit, because it refers to a geometric
interpretation of the index type `ι`. The name "incomplete tensor product" does
not seem to have caught on outside a narrow niche.

We tentatively propose to call the module the "finsupp tensor product" of the family `s`
(acknowledging that it doesn't roll off the tongue).

Reference: Guichardet, "Tensor Products of C^*-algebras, Part II: Infinite
Tensor Products".

## Main definitions

* `PiTensorProduct.Finsupp s₀` is the direct limit of the spaces `⨂[R] (i : S), s i` for
`S : Finset ι`. For `S ⊆ T`, tensors with index set `S` are identified with
tensors with index set `T` by padding with vectors provided by `s₀` on `T \ S`.

## Implementation Notes

We define the finsupp tensor product as a `Module.DirectLimit`.

The file builds on the  `Set` API to `PiTensorproduct`, which we have implemented for this purpose.

## TODO

_This file is a stub._

* Actually do anything at all.
* Decide on the name.
-/

open PiTensorProduct
open scoped TensorProduct

variable {ι : Type*}
variable {E : ι → Type*} {𝕜 : Type*}
variable [CommSemiring 𝕜] [∀ i, AddCommMonoid (E i)] [∀ i, Module 𝕜 (E i)]
variable (E₀ : (i : ι) → E i)

namespace PiTensorProduct

-- instance directedSystem [∀ s : Set ι, ∀ i, Decidable (i ∈ s)] (p : Set ι → Prop)
--     : DirectedSystem (fun S : Subtype p ↦ ⨂[R] i : ↑S, s i)
--     (fun _ _ hsub ↦ extendTensor hsub s₀) where
--   map_self := by simp
--   map_map := by
--     intro U T S h1 h2 f
--     rw [←Function.comp_apply (f := extendTensor h2 s₀)]
--     apply congrFun
--     simp [←LinearMap.coe_comp]



section Colimit

/-
There are two distinct, but linearly equivalent, ways of creating a direct limit
of modules in Mathlib:

* The construction in Algebra/Colimit/DirectLimit.lean assumes
  `IsDirectedOrder` on the index type, and uses the theory of direct limits for general types.
* The construction in Algebra/Colimit/Module.lean does not need
  `IsDirectedOrder`. It uses a construction specific for modules.

In this file, we're mainly interested in the index type `{ S ∈ Set ι // Finite S }`.
There is a natural `IsDirectedOrder` instance on it, because the union of finite sets is finite.
Hence, I currently tend to favor the first construction for the theory of
restricted `PiTensorProducts`.
However, for completeness and experimentation, we start by stating the variant
based on "Colimit/Module.lean", which works for general subtypes of `Set ι`.
-/
variable (𝕜) in
-- An `abbrev` for now, to inherit type class instances.
open Classical in
/-- Tensors with finite support (using the `Module.DirectLimit` construction) -/
abbrev Colimit (p : Set ι → Prop) := Module.DirectLimit (fun S : Subtype p ↦ ⨂[𝕜] i : ↑S, E i)
  (fun _ _ hsub ↦ extendTensor hsub E₀)

open Classical in
noncomputable def Colimit.of {p : Set ι → Prop} (S : Subtype p) :
    (⨂[𝕜] i : ↑S, E i) →ₗ[𝕜] Colimit 𝕜 E₀ p :=
  Module.DirectLimit.of 𝕜 _ (fun S : Subtype p ↦ ⨂[𝕜] i : ↑S, E i) ..

end Colimit

section Restricted

instance : IsDirectedOrder { S : Set ι // Finite ↑S } where
  directed a b := by
    use ⟨a.val ∪ b.val, by aesop (add safe apply Set.Finite.to_subtype)⟩
    aesop

instance : Nonempty ({ S : Set ι // Finite ↑S }) := ⟨∅, Finite.of_subsingleton ⟩

open Classical in
instance directedSystem : DirectedSystem
    (fun S : { S : Set ι // Finite S } ↦ ⨂[𝕜] (i : S.val), E i)
    (fun _ _ hsub ↦ extendTensor hsub E₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor h2 E₀)]
    apply congrFun
    simp [←LinearMap.coe_comp]

variable (𝕜) in
open Classical in
/- Tensors with finite support (using the general `DirectLimit` construction) -/
abbrev Restricted :=
  DirectLimit (fun S : { S : Set ι // Finite ↑S } ↦ ⨂[𝕜] (i : ↑S), E i)
    (fun _ _ hsub ↦ extendTensor hsub E₀)

open Classical in
-- A bit unclear which is preferable. But they are equivalent.
noncomputable def equiv : Colimit 𝕜 E₀ (fun S ↦ Finite S) ≃ₗ[𝕜] Restricted 𝕜 E₀ :=
  Module.DirectLimit.linearEquiv _ _

open Classical in
noncomputable def Restricted.of {S : { S : Set ι // Finite ↑S }} :
    (⨂[𝕜] i : ↑S, E i) →ₗ[𝕜] Restricted 𝕜 E₀ :=
  DirectLimit.Module.of 𝕜 _ (fun S : { S : Set ι // Finite ↑S } ↦ ⨂[𝕜] i : ↑S, E i) ..


#check NormedSpace
  /-
  Experimental inner product stuff
  -/

-- # TODO : Define InjectiveSeminorm and ProjectiveSeminorm
namespace Restricted

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*} (E₀ : (i : ι) → E i)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

set_option linter.style.openClassical false
open Classical


-- noncomputable def ee_aux {S₁ S₂ : Set ι} [Fintype ↑S₁] [Fintype ↑S₂]
--     (h : S₁ ≤ S₂) (E₀ : (i : ι) → E i) (g : (i : ↑(S₂ \ S₁)) → StrongDual 𝕜 (E ↑i)) :=
--   extendFunctionalDiff h
--     (dualDistrib (M := fun i : ↑(S₂ \ S₁) ↦ E i) (⨂ₜ[𝕜] i, g i)) ∘ₗ ((extendTensor (R := 𝕜) h E₀))

-- lemma ee_eq {S₁ S₂ : Set ι} {E₀ : (i : ι) → E i} [Fintype ↑S₁] [Fintype ↑S₂]
--     {g : (i : ↑(S₂ \ S₁)) → StrongDual 𝕜 (E ↑i)} (h : S₁ ≤ S₂)
--     (hn : ∀ i, ‖E₀ i‖ = 1) (hg : ∀ (i : ↑(S₂ \ S₁)), (g i) (E₀ i) = ↑‖E₀ i‖)
--     : ee_aux h E₀ g = LinearMap.id := by
--   ext f
--   simp [ee_aux, show ∀ x : ↑(S₂ \ S₁), ¬(↑x : ι) ∈ S₁ by simp, hg, hn]

-- noncomputable def ee {S₁ S₂ : Set ι} [Fintype ↑S₁] [Fintype ↑S₂]
--     (h : S₁ ≤ S₂) (E₀ : (i : ι) → E i) (g : (i : ↑(S₂ \ S₁)) → StrongDual 𝕜 (E ↑i))
--     (hn : ∀ i, ‖E₀ i‖ = 1) (hg : ∀ (i : ↑(S₂ \ S₁)), (g i) (E₀ i) = ↑‖E₀ i‖) :
--   (⨂[𝕜] (i : ↑S₁), E ↑i) →L[𝕜] ⨂[𝕜] (i₂ : ↑S₁), E ↑i₂ := by
--   apply ContinuousLinearMap.mk (ee_aux h E₀ g) ?_
--   rw [ee_eq h hn hg]
--   fun_prop

noncomputable def shrink {S₁ S₂ : Set ι} [Fintype ↑S₁] [Fintype ↑S₂]
    (h : S₁ ≤ S₂) (g : (i : ↑(S₂ \ S₁)) → StrongDual 𝕜 (E ↑i)) :=
  extendFunctionalDiff h (dualDistrib (M := fun i : ↑(S₂ \ S₁) ↦ E i) (⨂ₜ[𝕜] i, g i))

lemma shrink_extend_eq_id {S₁ S₂ : Set ι} {E₀ : (i : ι) → E i} [Fintype ↑S₁] [Fintype ↑S₂]
    {g : (i : ↑(S₂ \ S₁)) → StrongDual 𝕜 (E ↑i)} (h : S₁ ≤ S₂)
    (hn : ∀ i, ‖E₀ i‖ = 1) (hg : ∀ (i : ↑(S₂ \ S₁)), (g i) (E₀ i) = ↑‖E₀ i‖)
    : shrink h g ∘ₗ extendTensor (R := 𝕜) h E₀ = LinearMap.id := by
  ext f
  simp [shrink, show ∀ x : ↑(S₂ \ S₁), ¬(↑x : ι) ∈ S₁ by simp, hg, hn]

noncomputable def shrink_extend {S₁ S₂ : Set ι} [Fintype ↑S₁] [Fintype ↑S₂]
    (h : S₁ ≤ S₂) (E₀ : (i : ι) → E i) (g : (i : ↑(S₂ \ S₁)) → StrongDual 𝕜 (E ↑i))
    (hn : ∀ i, ‖E₀ i‖ = 1) (hg : ∀ (i : ↑(S₂ \ S₁)), (g i) (E₀ i) = ↑‖E₀ i‖) :
  (⨂[𝕜] (i : ↑S₁), E ↑i) →L[𝕜] ⨂[𝕜] (i₂ : ↑S₁), E ↑i₂ := by
  apply ContinuousLinearMap.mk (shrink h g ∘ₗ extendTensor (R := 𝕜) h E₀) ?_
  rw [shrink_extend_eq_id h hn hg]
  fun_prop

lemma compatible [∀ i, Nontrivial (E i)] (hn : ∀ i, ‖E₀ i‖ = 1) :
    ∀ (S₁ S₂ : Set ι) [Fintype ↑S₁] [Fintype ↑S₂] (h : S₁ ≤ S₂) (x : ⨂[𝕜] (i : S₁), E i),
    projectiveSeminorm x = projectiveSeminorm ((extendTensor (R := 𝕜) h E₀) x) := by
  intro S₁ S₂ _ _ hsub x
  apply eq_of_le_of_ge
  · haveI := nonempty_subtype.mpr (nonempty_lifts ((extendTensor (R := 𝕜) hsub E₀) x))
    choose g hg₁ hg₂ using fun i : ↑(S₂ \ S₁) ↦ exists_dual_vector'' 𝕜 (E₀ i)
    have hx : x = shrink_extend hsub E₀ g hn hg₂ x := by
      simp [shrink_extend, shrink_extend_eq_id hsub hn hg₂]
    nth_rewrite 1 [hx]
    dsimp [shrink_extend]
 

    -- have := (mem_lifts_iff _ _).mp p.prop

    -- grw [ContinuousLinearMap.le_opNorm (shrink hsub g) ((extendTensor hsub E₀) x)]
    -- trans ‖ee hsub E₀ g hn hg₂‖ * ‖x‖


  · haveI := nonempty_subtype.mpr (nonempty_lifts x)
    apply le_ciInf (fun p => ?_)
    let pe := (extendTensor_repr S₂ E₀) p.val
    have hpe := extendTensor_repr_lifts (R := 𝕜) hsub x p.prop E₀
    have hexp : projectiveSeminorm (extendTensor (R := 𝕜) hsub E₀ x) ≤ projectiveSeminormAux pe :=
      ciInf_le (bddBelow_projectiveSemiNormAux (extendTensor (R := 𝕜) hsub E₀ x)) ⟨pe, hpe⟩
    grw [hexp]
    simp only [projectiveSeminormAux, extendTensor_repr, FreeAddMonoid.lift_apply,
      FreeAddMonoid.toList_sum, List.map_map, List.map_flatten, List.sum_flatten, ge_iff_le, pe]
    apply List.sum_le_sum (fun a ha => ?_)
    simp only [Function.comp_apply, FreeAddMonoid.toList_of, List.map_cons, apply_dite norm, hn,
      Fintype.prod_dite, Finset.prod_const_one, mul_one, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    gcongr
    exact (Fintype.prod_equiv (Equiv.subtypeSubtypeEquivSubtype
      (fun u => Set.mem_of_subset_of_mem hsub u)) _ _ (by aesop)).le





#check Equiv.subtypeSubtypeEquivSubtype
  -- have ⟨p, hp⟩ := nonempty_lifts x
  -- have hx := (mem_lifts_iff _ _).mp hp
  -- have hxp : projectiveSeminorm x ≤ projectiveSeminormAux p :=
  --   ciInf_le (bddBelow_projectiveSemiNormAux x) ⟨p, hp⟩
  -- let pe := (extendTensor_repr S₂ E₀) p
  -- have hpe := extendTensor_repr_lifts (R := 𝕜) hsub x hp E₀
  -- have hexp : projectiveSeminorm (extendTensor (R := 𝕜) hsub E₀ x) ≤ projectiveSeminormAux pe :=
  --   ciInf_le (bddBelow_projectiveSemiNormAux (extendTensor (R := 𝕜) hsub E₀ x)) ⟨pe, hpe⟩

noncomputable def norm_aux [∀ i, Nontrivial (E i)] (hn : ∀ i, ‖E₀ i‖ = 1)
    : (Restricted 𝕜 E₀) → ℝ := by
  haveI := directedSystem (𝕜 := 𝕜) E₀
  apply DirectLimit.lift
  swap
  · intro S x
    haveI := @Fintype.ofFinite S S.prop
    exact projectiveSeminorm x
  · intro S₁ S₂ hsub x
    letI := @Fintype.ofFinite S₁ S₁.prop
    letI := @Fintype.ofFinite S₂ S₂.prop
    apply compatible E₀ hn S₁ S₂

-- end Restricted
-- end PiTensorProduct




-- variable {ι : Type*}
-- variable {s : ι → Type*} {R : Type*} (s₀ : (i : ι) → s i)
--   [DecidableEq (Set ι)] [RCLike R]
--   [∀ s : Set ι, ∀ i, Decidable (i ∈ s)]
--   [∀ i, SeminormedAddCommGroup (s i)] [∀ i, InnerProductSpace R (s i)]

-- open scoped InnerProductSpace
-- open scoped ComplexConjugate
-- open Function Finset
-- #check starRingEnd R

-- -- This is not true, as one should use →ₗ⋆[R] instead. But the current lift is not general enough.
-- noncomputable def inner_aux₁ {S : Set ι} [Finite S] :
--     (⨂[R] i : S, s i) →ₗ[R] (⨂[R] i : S, s i) →ₗ[R] R :=
--   haveI := Fintype.ofFinite
--   lift {
--     toFun f₁ := lift {
--       toFun f₂ := ∏ i, ⟪f₁ i, f₂ i⟫_R
--       map_update_add' := by
--         intro _ _ i x y
--         symm
--         apply Finset.prod_add_prod_eq (mem_univ i)
--         all_goals aesop (add safe simp (inner_add_right (f₁ i) x y))
--       map_update_smul' := by
--         intro _ _ i c x
--         rw [prod_eq_mul_prod_diff_singleton (mem_univ i)]
--         conv_rhs => rw [prod_eq_mul_prod_diff_singleton (mem_univ i)]
--         simp only [update_self, inner_smul_right, smul_eq_mul, ←mul_assoc]
--         congr 1
--         exact Finset.prod_congr rfl (by grind)
--     }
--     map_update_add' := by
--       intro _ _ i x y
--       ext f
--       simp only [LinearMap.compMultilinearMap_apply, lift.tprod, MultilinearMap.coe_mk,
--         LinearMap.add_compMultilinearMap, MultilinearMap.add_apply]
--       symm
--       apply Finset.prod_add_prod_eq (mem_univ i)
--       all_goals aesop (add safe simp (inner_add_left x y (f i)))
--     map_update_smul' := by
--       intro _ _ i c x
--       ext f
--       simp only [LinearMap.compMultilinearMap_apply, lift.tprod, MultilinearMap.coe_mk,
--         LinearMap.smul_compMultilinearMap, MultilinearMap.smul_apply]
--       rw [prod_eq_mul_prod_diff_singleton (mem_univ i)]
--       conv_rhs => rw [prod_eq_mul_prod_diff_singleton (mem_univ i)]
--       simp only [update_self, ]

--       sorry -- not true!

--   }


-- There is only 1 way to define a function on any `Quotient`, and that is by defining the function
-- on the underlying elements, and lifting the function to `Quotient` space by showing its
-- compatibility. See `Quotient.lift`. The `DirectLimit` is a `Quotient`, and the only way to define
-- a function on it is through `DirectLimit.lift`. This requires defining
-- `(⨂[R] (i : ↑↑S₂), s ↑i) →ₗ[R] (⨂[R] (i : ↑↑S₁), s ↑i) →ₗ[R] R`, which can be done through
-- padding of S₂ and S₁ to S₁ ∪ S₂ and using `inner_aux₁`.
--noncomputable def inner :
--    Restricted R s₀ →ₗ[R] Restricted R s₀ →ₗ[R] R :=
--  Module.DirectLimit.lift _ _ _ _ (fun S₁ =>
--    LinearMap.flip (Module.DirectLimit.lift _ _ _ _ (fun S₂ => sorry) (sorry))) (sorry)
--                                                Look at here ↑
