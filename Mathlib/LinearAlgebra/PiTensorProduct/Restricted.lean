/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Set
public import Mathlib.Algebra.Colimit.Module

/-!
# The restricted tensor product

Given a family of modules `s : ι → Type*`, each with a distinguished element
`(s₀ i) : s i`, the _support_ of a tensor `t : ⨂ i, s i` is the set of indices
`i : ι` where `t` differs from `s₀ i`. (More precisely: the smallest set `S` such
that `t` is of the form `tₛ ⊗ (⨂ₜ i : Sᶜ, s₀ i)` with `tₛ : ⨂ i : S, s i`).
We define the module of tensors whose support is a finite set.

## Background and name

If the modules `s i` are unital algebras, (a suitable norm closure of) the
module of finitely-supported tensors with respect to `s₀ := fun i ↦ 1` is known as the
_infinite tensor product_ of the family `s`. In many-body physics, it is called the
_quasi-local algebra_. If the `s i` are Hilbert spaces and `s₀` a family of unit
vectors, the norm closure of the finitely-supported tensors is sometimes called
the _incomplete tensor product_ associated with the section `s₀`. Such Hilbert
spaces appear in the representation theory of infinite tensor products of C^*
algebras and are connected to superselection sectors of quantum lattice models.
In the theory of automorphic representations, the term _restricted tensor product_
is used.

The term "infinite tensor product" does not seem optimal here, given that
Mathlib's `PiTensorProduct` can handle tensors that actually have infinite
support. The term "local" also does not fit, because it refers to a geometric
interpretation of the index type `ι`. The name "incomplete tensor product" does
not seem to have caught on outside a narrow niche. Hence we opt for "restricted".

Reference: Guichardet, "Tensor Products of C^*-algebras, Part II: Infinite
Tensor Products".

## Main definitions

* `PiTensorProduct.Restricted R s₀` is the direct limit of the spaces `⨂[R] (i : S), s i` for
`S : Finset ι`. For `S ⊆ T`, tensors with index set `S` are identified with
tensors with index set `T` by padding with vectors provided by `s₀` on `T \ S`.

## Implementation Notes

We define the finsupp tensor product as a `Module.DirectLimit`.

The file builds on the  `Set` API to `PiTensorproduct`, which we have implemented for this purpose.

Further design decisions are TBD. In particular: The use of `Set`+`Finite` vs
`Finset` and the use of `DirectLimit` vs `Module.DirectLimit`. In this text
file, various variants are defined.

## TODO

_This file is a stub._

* Actually do anything at all.
-/

open PiTensorProduct
open scoped TensorProduct

@[expose] public section

namespace PiTensorProduct

variable {ι : Type*} [DecidableEq ι]
variable (R : Type*)

/- Family of spaces with distinguished elements -/
variable {s : ι → Type*}
variable (s₀ : (i : ι) → s i)

variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-
Version 1: `Finset`
-/

instance : DirectedSystem
    (fun S : Finset ι ↦ ⨂[R] (i : S), s i)
    (fun _ _ hsub ↦ extendTensor hsub s₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor h2 s₀)]
    apply congrFun
    simp only [SetLike.coe_sort_coe, ← LinearMap.coe_comp, DFunLike.coe_fn_eq]
    exact extendTensor_trans h1 h2

/-- Tensors with finite support. V1: Based on `Finset` -/
abbrev Restricted :=
  Module.DirectLimit (fun S : Finset ι ↦ ⨂[R] (i : S), s i) (fun _ _ hsub ↦ extendTensor hsub s₀)


/-
Version 2
-/


-- `open Classical`?
variable [DecidableEq (Set ι)]
variable [∀ s : Set ι, ∀ i, Decidable (i ∈ s)]

instance instSetDirectedSystem (p : Set ι → Prop) :
  DirectedSystem (fun S : Subtype p ↦ ⨂[R] i : ↑S, s i)
    (fun _ _ hsub ↦ extendTensor hsub s₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor h2 s₀)]
    apply congrFun
    simp [←LinearMap.coe_comp]

/-
There are two distinct, but linearly equivalent, ways of creating a direct limit
of modules in Mathlib:

* The construction in Algebra/Colimit/DirectLimit.lean assumes `IsDirectedOrder`
on the index type, and uses the theory of direct limits for general types.
* The construction in Algebra/Colimit/Module.lean does not need
`IsDirectedOrder`. It uses a construction specific for modules.

We're mainly interested in the index type `{ S ∈ Set ι // Finite S }`. There is
a natural `IsDirectedOrder` instance on it, because the union of finite sets is
finite. Hence, the first construction seems to be more appropriate for the
theory of restricted `PiTensorProduct`s.  However, for completeness and
experimentation, we start by stating the variant based on "Colimit/Module.lean",
which works for general subtypes of `Set ι`.
-/

/-- Tensors with index set restricted index set (V2: using the `Module.DirectLimit` construction) -/
abbrev Restricted' (p : Set ι → Prop) := Module.DirectLimit (fun S : Subtype p ↦ ⨂[R] i : ↑S, s i)
  (fun _ _ hsub ↦ extendTensor hsub s₀)

noncomputable def Restricted'.of {p : Set ι → Prop} (S : Subtype p) :
    (⨂[R] i : ↑S, s i) →ₗ[R] Restricted' R s₀ p :=
  Module.DirectLimit.of R _ (fun S : Subtype p ↦ ⨂[R] i : ↑S, s i) ..



instance : IsDirectedOrder { S : Set ι // Finite S } where
  directed a b := by
    use ⟨a.val ∪ b.val, by aesop (add safe apply Set.Finite.to_subtype)⟩
    aesop

instance : Nonempty ({ S : Set ι // Finite S }) := ⟨∅, Finite.of_subsingleton ⟩

/- Tensors with finite support (using the general `DirectLimit` construction) -/
abbrev Restricted'' :=
  DirectLimit
    (fun S : { S : Set ι // Finite ↑S } ↦ ⨂[R] (i : ↑S), s i)
    (fun _ _ hsub ↦ extendTensor (R:=R) hsub s₀)


noncomputable example : Restricted' R s₀ (fun S ↦ Finite S) ≃ₗ[R] Restricted'' R s₀ :=
  Module.DirectLimit.linearEquiv _ _

noncomputable def Restricted''.of {S : { S : Set ι // Finite ↑S }} :
    (⨂[R] i : ↑S, s i) →ₗ[R] Restricted'' R s₀ :=
  DirectLimit.Module.of R _ (fun S : { S : Set ι // Finite ↑S } ↦ ⨂[R] i : ↑S, s i) ..


end PiTensorProduct
