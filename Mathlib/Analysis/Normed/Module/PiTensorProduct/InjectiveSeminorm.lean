/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm

/-!
# Injective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a nontrivially normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"injective seminorm". It is chosen to satisfy the following property: for every
normed `𝕜`-vector space `F`, the linear equivalence
`MultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, Eᵢ) →ₗ[𝕜] F`
expressing the universal property of the tensor product induces an isometric linear equivalence
`ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, Eᵢ) →L[𝕜] F`.

The idea is the following: Every normed `𝕜`-vector space `F` defines a linear map
from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] F`, which sends `x` to the map
`f ↦ f.lift x`. Thanks to `PiTensorProduct.norm_eval_le_projectiveSeminorm`, this map lands in
`ContinuousMultilinearMap 𝕜 E F →L[𝕜] F`. As this last space has a natural operator (semi)norm,
we get an induced seminorm on `⨂[𝕜] i, Eᵢ`, which, by
`PiTensorProduct.norm_eval_le_projectiveSeminorm`, is bounded above by the projective seminorm
`PiTensorProduct.projectiveSeminorm`. We then take the `sup` of these seminorms as `F` varies;
as this family of seminorms is bounded, its `sup` has good properties.

In fact, we cannot take the `sup` over all normed spaces `F` because of set-theoretical issues,
so we only take spaces `F` in the same universe as `⨂[𝕜] i, Eᵢ`. We prove in
`norm_eval_le_injectiveSeminorm` that this gives the same result, because every multilinear map
from `E = Πᵢ Eᵢ` to `F` factors though a normed vector space in the same universe as
`⨂[𝕜] i, Eᵢ`.

We then prove the universal property and the functoriality of `⨂[𝕜] i, Eᵢ` as a normed vector
space.

## Main definitions

* `PiTensorProduct.toDualContinuousMultilinearMap`: The `𝕜`-linear map from
  `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending `x` to the map
  `f ↦ f x`.
* `PiTensorProduct.injectiveSeminorm`: The injective seminorm on `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.liftEquiv`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as a continuous linear equivalence.
* `PiTensorProduct.liftIsometry`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as an isometric linear equivalence.
* `PiTensorProduct.tprodL`: The canonical continuous multilinear map from `E = Πᵢ Eᵢ`
  to `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.mapL`: The continuous linear map from `⨂[𝕜] i, Eᵢ` to `⨂[𝕜] i, E'ᵢ`
  induced by a family of continuous linear maps `Eᵢ →L[𝕜] E'ᵢ`.
* `PiTensorProduct.mapLMultilinear`: The continuous multilinear map from
  `Πᵢ (Eᵢ →L[𝕜] E'ᵢ)` to `(⨂[𝕜] i, Eᵢ) →L[𝕜] (⨂[𝕜] i, E'ᵢ)` sending a family
  `f` to `PiTensorProduct.mapL f`.

## Main results

* `PiTensorProduct.norm_eval_le_injectiveSeminorm`: The main property of the injective seminorm
  on `⨂[𝕜] i, Eᵢ`: for every `x` in `⨂[𝕜] i, Eᵢ` and every continuous multilinear map `f` from
`E = Πᵢ Eᵢ` to a normed space `F`, we have `‖f.lift x‖ ≤ ‖f‖ * injectiveSeminorm x `.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.mapLMultilinear_opNorm` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

## TODO

* If all `Eᵢ` are separated and satisfy `SeparatingDual`, then the seminorm on
  `⨂[𝕜] i, Eᵢ` is a norm. This uses the construction of a basis of the `PiTensorProduct`, hence
  depends on PR https://github.com/leanprover-community/mathlib4/pull/11156.
  It should probably go in a separate file.

* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.

-/

/-
Ported to `projectiveSeminorm`.
-/
