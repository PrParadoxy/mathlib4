/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
import Mathlib.LinearAlgebra.PiTensorProductEquiv.Basic
import Mathlib.Algebra.Colimit.Module

/-!
# Tensors with finite support

Given a family of modules `s : ι → Type*`, each with a distinguished element
`(s₀ i) : s i`, the _support_ of a tensor `t : ⨂ i, s i` is the set of indices
`i : ι` where `t` differs from `s₀ i`. We describe the _quasi-finite tensor
product_ of the family `s`: the module of tensors which are supported on finite
sets.

## Background and name

If the modules `s i` are unital algebras, (a suitable norm closure of) their
quasi-finite tensor product for `s₀ := fun i ↦ 1` is known as the _infinite tensor
product_ of the family `s`, or, in physics, as the _quasi-local algebra_. These
algebras, in turn, are often naturally represented on (the norm closure of)
quasi-finite tensor products of Hilbert spaces.

The term "infinite tensor product" does not seem appropriate here, given that
Mathlib's `PiTensorProduct` can handle tensors that actually are non-trivial on
infinitely many indices. The term "quasi-local" also does not fit, because
"local" refers to a geometric interpretation of the index type `ι`.

We hence propose "quasi-finite" as a descriptive compromise. (Or maybe
`FinSuppTensorProduct` would be better?)

Reference: Guichardet, "Tensor Products of C^*-algebras, Part II: Infinite
Tensor Products".

## Main definitions

* `QuasiFinite s₀` is the direct limit of the spaces `⨂[R] (i : S), s i` for `S : Finset ι`.
For `S ⊆ T`, tensors with index set `S` are mapped to tensors with index set `T`
by padding with vectors provided by `s₀` on `T \ S`.

## Implementation Notes

We define the quasi-finite tensors as a `Module.DirectLimit`.

  *This file is a stub.*

For now, it only constructs the type. It exists, to guide the design of the
`Set` API to `PiTensorproduct`.

## TODO

* Actually do anything at all.
* Decide on the name.
-/

open PiTensorProduct
open scoped TensorProduct

variable {ι : Type*} [DecidableEq ι] {S T : Finset ι} (hsub : S ≤ T)
variable {s : ι → Type*} {R : Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable (s₀ : (i : ι) → s i)

instance QuasiFinite.directedSystem : DirectedSystem
    (fun S : Finset ι ↦ ⨂[R] (i : S), s i)
    (fun _ _ hsub ↦ extendTensor hsub s₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor (R := R) h2 s₀)]
    apply congrFun
    erw [←LinearMap.coe_comp, DFunLike.coe_fn_eq, extendTensor_trans]

/-- Tensors with finite support -/
abbrev QuasiFinite :=
  Module.DirectLimit (fun S : Finset ι ↦ ⨂[R] (i : S), s i) (fun _ _ hsub ↦ extendTensor hsub s₀)
