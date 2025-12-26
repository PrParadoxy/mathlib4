/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
-- import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
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


open Classical in
lemma compatible [∀ i, Nontrivial (E i)] (hn : ∀ i, ‖E₀ i‖ = 1) :
    ∀ (S₁ S₂ : Set ι) [Fintype ↑S₁] [Fintype ↑S₂] (h : S₁ ≤ S₂) (x : ⨂[𝕜] (i : S₁), E i),
    projectiveSeminorm x = projectiveSeminorm ((extendTensor (R := 𝕜) h E₀) x) := by
  intro S₁ S₂ _ _ hsub x
  apply eq_of_le_of_ge
  · haveI := nonempty_subtype.mpr (nonempty_lifts ((extendTensor (R := 𝕜) hsub E₀) x))
    have ⟨p, hp⟩ := nonempty_lifts x
    apply le_ciInf (fun pe => ?_)
    choose g hg₁ hg₂ using fun i : ↑(S₂ \ S₁) ↦ exists_dual_vector' 𝕜 (E₀ i)
    simp only [hn, map_one] at hg₂
    let p := shrinkTensor_repr hsub (fun i => (g i).toLinearMap) pe.val
    have hp := shrinkTensor_repr_lifts hsub E₀ hg₂ pe.prop
    have hxp : projectiveSeminorm x ≤ projectiveSeminormAux p :=
      ciInf_le (bddBelow_projectiveSemiNormAux x) ⟨p, hp⟩
    grw [hxp]
    simp only [projectiveSeminormAux, shrinkTensor_repr, ContinuousLinearMap.coe_coe,
      FreeAddMonoid.lift_apply, FreeAddMonoid.toList_sum, List.map_map, List.map_flatten,
      List.sum_flatten, ge_iff_le, p]
    apply List.sum_le_sum (fun a ha => ?_)
    simp only [Function.comp_apply, FreeAddMonoid.toList_of, List.map_cons, norm_mul, norm_prod,
      mul_assoc, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    gcongr
    rw [← Fintype.prod_subtype_mul_prod_subtype (ι := S₂) (fun i => i.val ∈ S₁), mul_comm]
    gcongr
    · exact (Fintype.prod_equiv ((Equiv.subtypeSubtypeEquivSubtype
        (q := fun i => i ∈ S₁) (fun u => Set.mem_of_subset_of_mem hsub u)).symm) _ _ (by aesop)).le
    · trans ∏ b : ↑(S₂ \ S₁), ‖g ⟨b.val, by simp⟩‖ * ‖a.2 ⟨b.val, by grind⟩‖
      · gcongr
        grw [ContinuousLinearMap.le_opNorm]
      · simp only [subset_refl, Set.coe_inclusion, hg₁, one_mul]
        apply le_of_eq
        let e : ↑(S₂ \ S₁) ≃ { x : S₂ // ↑x ∉ S₁ } :=
          { toFun := fun x => ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
            invFun := fun x => ⟨x.val.val, x.val.prop, x.prop⟩
            left_inv := by intro; rfl
            right_inv := by intro; rfl}
        apply Fintype.prod_equiv e
        aesop
  · haveI := nonempty_subtype.mpr (nonempty_lifts x)
    apply le_ciInf (fun p => ?_)
    let pe := (extendTensor_repr S₂ E₀) p.val
    have hpe := extendTensor_repr_lifts (R := 𝕜) hsub p.prop E₀
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

noncomputable def norm_aux [∀ i, Nontrivial (E i)] (hn : ∀ i, ‖E₀ i‖ = 1)
    : (Restricted 𝕜 E₀) → ℝ :=
  haveI := directedSystem (𝕜 := 𝕜) E₀
  DirectLimit.lift _ _ (fun S₁ S₂ hsub x =>
    letI := @Fintype.ofFinite S₁ S₁.prop
    letI := @Fintype.ofFinite S₂ S₂.prop
    compatible (𝕜 := 𝕜) E₀ hn S₁ S₂ hsub x
  )

