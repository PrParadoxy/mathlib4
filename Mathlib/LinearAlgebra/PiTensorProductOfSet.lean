/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.Basic -- use for extension of linear maps.

/-!
# PiTensorProducts indexed by sets

Given a family of modules `s : ι → Type*`, we consider tensor products of type
`⨂ (i : S), s i`, where `S : Set ι`.

## Main definitions

We establish a number of linear equivalences.
* `unionEquiv` between tensors with index type `ι` and tensors with index type `univ : Set ι`.
* `tmulUnionEquiv` between products of tensors indexed by two disjoint sets `S₁`, `S₂` and
  tensors indexed by the union `S₁ ∪ S₂`.
* `tmulBipartitionEquiv` between products of tensors indexed by `S`, `Sᶜ` and tensors with
  index type `ι`.
* `tmulUnifyEquiv`: Given sets `S ⊆ T`, a linear equivalence between product of tensors indexed
  by `S` and `T \ S`, and tensors indexed by `T`.
* `singletonEquiv` between tensors indexed by a singleton set `{i₀}` and the module `s i₀`.
* `tmulInsertEquiv` between the product of vectors in `s i₀` with a tensor indexed by `S`,
  and tensors indexed by `insert i₀ S`.

Given sets `S ⊆ T`, various objects can be "extended" from tensors with index set `S` to
tensors with index set `T`.
* `extendLinear` converts a linear map defined on tensors with index set `S` to tensors with
  index set `T`.
* `extendEnd` and `partialContract` are special cases for endomorphisms and linear functionals,
  respectively.
* `extendTensor`: Given a family of distinguished elements `s₀ : (i : ι) → s i`, map a tensor
  with index set `S` to a tensor with index set `T`, by padding with the vectors provided by `s₀`
  on `T \ S`.

## Implementation notes

This file was motivated by the goal to implement a type of "tensors with finite support", see
`PiTensorFinSupp.lean`, and also by this TBD item from `PiTensorProduct.lean`:

  * API for the various ways `ι` can be split into subsets; connect this with the binary
    tensor product.

The fist `section` contains a dependent version of `PiTensorProduct.subsingletonEquiv`,
which is not direct part of the `Set` API.

## TODO

*This file is work in progress.*

* Seek feedback
* Implement nested PiTensorProducts

-/

open PiTensorProduct
open scoped TensorProduct

namespace PiTensorProduct

variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

-- This section contains a dependent version of `PiTensorProduct.subsingletonEquiv`.
-- It is not part of the `Set` API.
section subsingletonEquivDep

-- RFC: We copied the following idiom from PiTensorProduct.lean. What's the reason for
-- using it over `[Unique ι]`?
variable [Subsingleton ι] (i₀ : ι)

/-- Tensor product over a singleton type with element `i₀` is equivalent to `s i₀`.
For non-dependent case, see `PiTensorProduct.subsingletonEquiv` -/
@[simps! symm_apply]
def subsingletonEquivDep : (⨂[R] i, s i) ≃ₗ[R] s i₀ :=
  LinearEquiv.ofLinear
    (
      lift {
      toFun f := f i₀
      map_update_add' := by aesop (add safe forward Subsingleton.allEq)
      map_update_smul' := by aesop (add safe forward Subsingleton.allEq)
    })
    ({
      toFun x := tprod R (Pi.single i₀ x)
      map_add' x y := by simp [Pi.single]
      map_smul' x y := by simp [Pi.single]
    })
    (by ext _; simp)
    (by
      ext f
      have h : Pi.single i₀ (f i₀) = f := by
        ext k; rw [Subsingleton.elim i₀ k]; simp
      simp [h])

-- Note: One could base `PiTensorProduct.subsingletonEquiv` on `subsingletonEquivDep`.
section
variable {M : Type*} [AddCommMonoid M] [Module R M]

def subsingletonEquiv' : (⨂[R] _ : ι, M) ≃ₗ[R] M := subsingletonEquivDep i₀
end

@[simp]
theorem subsingletonEquivDep_tprod (f : (i : ι) → s i) :
    subsingletonEquivDep i₀ (⨂ₜ[R] i, f i) = f i₀ := by simp [subsingletonEquivDep]

/-- Any tensor indexed by a unique type is a pure tensor -/
lemma subsingletonEquivDep_eq_tprod (z : ⨂[R] i, s i) :
    z = ⨂ₜ[R] i, (Pi.single i₀ (subsingletonEquivDep i₀ z)) i := by
  induction z using PiTensorProduct.induction_on
  all_goals rw [←subsingletonEquivDep_symm_apply, LinearEquiv.symm_apply_apply]

end subsingletonEquivDep

section Set

open Set

section univEquiv

/-- Isomorphism between tensors indexed by `ι` and by `univ : Set ι`. -/
def univEquiv : (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i : ↥univ, s i.val := reindex R s (Equiv.Set.univ ι).symm

@[simp]
theorem univEquiv_tprod (f : (i : ι) → s i) : univEquiv (⨂ₜ[R] i, f i) = ⨂ₜ[R] i : ↥univ, f i.val :=
  reindex_tprod (Equiv.Set.univ ι).symm f

@[simp]
theorem univEquiv_symm_tprod (f : (i : ι) → s i) :
    univEquiv.symm (⨂ₜ[R] i : ↥univ, f i.val) = (⨂ₜ[R] i, f i) := by
  rw [LinearEquiv.symm_apply_eq]
  simp

end univEquiv


section tmulUnionEquiv

variable {S₁ S₂ : Set ι} (hdisj : Disjoint S₁ S₂) [(i : ι) → Decidable (i ∈ S₁)]

/-- Isomorphism between products of tensors indexed by two disjoint sets and
tensors indexed by their union. -/
def tmulUnionEquiv :
    ((⨂[R] (i₁ : S₁), s i₁) ⊗[R] (⨂[R] (i₂ : S₂), s i₂))
      ≃ₗ[R] ⨂[R] (i : ↥(S₁ ∪ S₂)), s i :=
  (tmulEquivDep R (fun i => s ((Equiv.Set.union hdisj).symm i))) ≪≫ₗ
  (reindex R (fun i : ↥(S₁ ∪ S₂) => s i) (Equiv.Set.union hdisj)).symm

@[simp]
theorem tmulUnionEquiv_tprod (lv : (i : S₁) → s i) (rv : (i : S₂) → s i) :
    (tmulUnionEquiv hdisj) ((⨂ₜ[R] i : S₁, lv i) ⊗ₜ (⨂ₜ[R] i : S₂, rv i)) =
      ⨂ₜ[R] j : ↥(S₁ ∪ S₂), if h : j.val ∈ S₁ then lv ⟨j, h⟩ else rv ⟨j, by aesop⟩ := by
  erw [tmulUnionEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, reindex_tprod, tmulEquivDep_apply]
  congr with x
  match x with
  | Sum.inl x => simp_all
  | Sum.inr x =>
    have (h : ↑x ∈ S₁) := disjoint_left.mp hdisj h
    simp_all

@[simp]
theorem tmulUnionEquiv_symm_tprod (f : (i : ↥(S₁ ∪ S₂)) → s i) :
    (tmulUnionEquiv hdisj).symm (⨂ₜ[R] i, f i) =
      (⨂ₜ[R] i : S₁, f ⟨i, by aesop⟩) ⊗ₜ (⨂ₜ[R] i : S₂, f ⟨i, by aesop⟩) := by
  simp [tmulUnionEquiv, tmulEquivDep]

end tmulUnionEquiv

section tmulBipartitionEquiv

variable {S : Set ι} [(i : ι) → Decidable (i ∈ S)]

/-- Isomorphism between the product of tensors indexed by a set and tensors
indexed by its complement, and the space of all tensors. -/
def tmulBipartitionEquiv : (⨂[R] i₁ : S, s i₁) ⊗[R] (⨂[R] i₂ : ↥Sᶜ, s i₂) ≃ₗ[R] ⨂[R] i, s i :=
  (tmulUnionEquiv (disjoint_compl_right)) ≪≫ₗ (reindex R (fun i : ↥(S ∪ Sᶜ) ↦ s i)
    (Equiv.trans (Equiv.subtypeEquivProp (Set.union_compl_self S)) (Equiv.Set.univ ι)))

@[simp]
theorem tmulBipartitionEquiv_tprod (lv : (i : S) → s i) (rv : (i : ↥Sᶜ) → s i) :
    tmulBipartitionEquiv ((⨂ₜ[R] i : S, lv i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, rv i)) =
      ⨂ₜ[R] j, if h : j ∈ S then lv ⟨j, h⟩ else rv ⟨j, by aesop⟩ := by
  erw [tmulBipartitionEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod, reindex_tprod]
  rfl

@[simp]
theorem tmulBipartition_symm_tprod (f : (i : ι) → s i) :
    tmulBipartitionEquiv.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i : S, f i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, f i) := by
  simp only [LinearEquiv.symm_apply_eq, tmulBipartitionEquiv_tprod]
  congr
  aesop

end tmulBipartitionEquiv


section tmulUnifyEquiv

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

/-- Isomorphism between product of tensors indexed by `S` and `T \ S` with `S ⊆ T` and
tensors indexed by `T`. -/
def tmulUnifyEquiv :
    ((⨂[R] i₁ : S, s i₁) ⊗[R] (⨂[R] i₂ : ↥(T \ S), s i₂)) ≃ₗ[R] ⨂[R] i : T, s i :=
  (tmulUnionEquiv (disjoint_sdiff_right)) ≪≫ₗ
    (reindex R (fun i : ↥(S ∪ T \ S) => s i) (Equiv.subtypeEquivProp (union_diff_cancel hsub)))

@[simp]
theorem tmulUnifyEquiv_tprod (lv : (i : S) → s i) (rv : (i : ↑(T \ S)) → s i) :
    tmulUnifyEquiv hsub ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i, rv i)) =
      ⨂ₜ[R] i : T, if h : ↑i ∈ S then lv ⟨↑i, by aesop⟩ else rv ⟨↑i, by aesop⟩ := by
  erw [tmulUnifyEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod, reindex_tprod]
  rfl

@[simp]
theorem tmulUnifyEquiv_tprod_symm (av : (i : T) → s i) :
    (tmulUnifyEquiv hsub).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : S, av ⟨i, by aesop⟩) ⊗ₜ (⨂ₜ[R] i : ↥(T \ S), av ⟨i, by aesop⟩) := by
  simp only [LinearEquiv.symm_apply_eq, tmulUnifyEquiv_tprod]
  congr
  aesop

section LinearMap

open Module

variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- Extension of a linear map on tensors with index set `S ⊆ T` to a linear map
on tensors with index set `T`. -/
def extendLinear (l : (⨂[R] i : S, s i) →ₗ[R] M) :
      (⨂[R] i : T, s i) →ₗ[R] (M ⊗[R] (⨂[R] (i₂ : ↑(T \ S)), s i₂)) :=
  (LinearEquiv.congrLeft R (M := (M ⊗[R] (⨂[R] (i₂ : ↑(T \ S)), s i₂))) (tmulUnifyEquiv hsub))
    (TensorProduct.map l (LinearMap.id))

-- TBD: Name?
/-- Extension of a linear map on tensors with index set `S ⊆ T` to a linear map
on tensors with index set `T`. Bundled as a linear map. -/
def extendLinearAsMap : ((⨂[R] i : S, s i) →ₗ[R] M) →ₗ[R]
    ((⨂[R] i : T, s i) →ₗ[R] (M ⊗[R] (⨂[R] (i₂ : ↑(T \ S)), s i₂))) where
  toFun l := extendLinear hsub l
  map_add' := by
    intros
    simp [extendLinear, LinearEquiv.congrLeft, TensorProduct.map_add_left, LinearMap.add_comp]
  map_smul' := by
    intros
    simp [extendLinear, LinearEquiv.congrLeft, TensorProduct.map_smul_left]


theorem extensionInjective [Flat R (⨂[R] (i₂ : ↑(T \ S)), s ↑i₂)]
  (l : ((⨂[R] i : S, s i) →ₗ[R] M)) (h : Function.Injective l) :
  Function.Injective (extendLinearAsMap (R:=R) (s:=s) (M:=M) hsub l) := by
  simpa [extendLinearAsMap, extendLinear, LinearEquiv.congrLeft, ←LinearMap.rTensor_def]
    using Module.Flat.rTensor_preserves_injective_linearMap _ h

theorem extensionInjective' [∀ i, Flat R (s i)] :
  Function.Injective (extendLinearAsMap (R:=R) (s:=s) (M:=M) hsub) :=

  -- `the goal is fun l ↦ TensorProduct.map l LinearMap.id ∘ₗ ↑(tmulUnifyEquiv hsub).symm`
  -- `whereas the flatness proves injectivity of fun l ↦ TensorProduct.map l LinearMap.id`
  -- Strategy:
  -- Use `apply Module.Flat.lTensor_preserves_injective_linearMap`
  -- For this I need that if `f, g` are injective *as linear maps*, then `f.trans g` is injective.
  -- Trouble is that one can't use `Function.Injective.comp`, as it coerces the
  -- linear map to a function.
  -- Maybe use stuff in "Mathlib/Algebra/Module/Submodule/Ker.lean"??

  sorry

/-- Extension of an endomorphism on tensors with index set `S ⊆ T` to one on
tensors with index set `T`. Bundled as a linear map. -/
def extendEnd : End R (⨂[R] i : S, s i) →ₗ[R] End R (⨂[R] i : T, s i) where
  toFun l := LinearEquiv.congrRight (tmulUnifyEquiv hsub) (extendLinearAsMap hsub l)
  map_add' := by simp
  map_smul' := by simp

/-- Partial contraction: a functional on tensors with index set `S ⊆ T` contracts
tensors with index set `T` to tensors with index set `T \ S`. Bundled as a linear map. -/
def partialContract :
    ((⨂[R] i : S, s i) →ₗ[R] R) →ₗ[R] (⨂[R] i : T, s i) →ₗ[R] ⨂[R] (i₂ : ↑(T \ S)), s i₂ where
  toFun l := LinearEquiv.congrRight (TensorProduct.lid _ _) (extendLinearAsMap hsub l)
  map_add' := by simp
  map_smul' := by simp

def partialContractDiff [(i : ι) → Decidable (i ∈ T \ S)] :
    ((⨂[R] (i₂ : ↑(T \ S)), s i₂) →ₗ[R] R) →ₗ[R] (⨂[R] i : T, s i) →ₗ[R] ⨂[R] (i₂ : S), s i₂ where
  toFun l :=
    have h : T \ (T \ S) = S := Set.diff_diff_cancel_left hsub
    (LinearMap.llcomp R _ _ _
      (PiTensorProduct.reindex R (fun i : ↑(T \ (T \ S)) => s i) (Equiv.setCongr h)).toLinearMap)
      ((PiTensorProduct.partialContract (Set.diff_subset)) l)
  map_add' := by simp
  map_smul' := by simp

@[simp]
theorem extendLinear_tprod (l : (⨂[R] i : S, s i) →ₗ[R] M) (f : (i : T) → s i) :
    extendLinearAsMap hsub l (⨂ₜ[R] i, f i)
    = l (⨂ₜ[R] i₁ : S, f ⟨i₁, by aesop⟩) ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨i₂, by aesop⟩) := by
  simp [extendLinearAsMap, extendLinear, LinearEquiv.congrLeft]

@[simp]
theorem extendEnd_tprod (l : End _ (⨂[R] i : S, s i)) (f : (i : T) → s i) :
    extendEnd hsub l (⨂ₜ[R] i, f i)
    = (tmulUnifyEquiv hsub) (l (⨂ₜ[R] i₁ : S, f ⟨i₁, by aesop⟩)
      ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨↑i₂, by aesop⟩)) := by
  simp [extendEnd, LinearEquiv.congrRight]

@[simp]
theorem partialContract_tprod (l : (⨂[R] i : S, s i) →ₗ[R] R) (f : (i : T) → s i) :
    partialContract hsub l (⨂ₜ[R] i, f i)
    = (l (⨂ₜ[R] i : S, f ⟨i, by aesop⟩)) • ⨂ₜ[R] i : ↑(T \ S), f ⟨i, by aesop⟩ := by
  simp [partialContract, LinearEquiv.congrRight]

omit [(i : ι) → Decidable (i ∈ S)] in
@[simp]
theorem partialContractDiff_tprod [(i : ι) → Decidable (i ∈ T \ S)]
    (l : (⨂[R] i : ↑(T \ S), s i) →ₗ[R] R) (f : (i : T) → s i) :
    partialContractDiff hsub l (⨂ₜ[R] i, f i)
    = (l (⨂ₜ[R] i : ↑(T \ S), f ⟨i, by aesop⟩)) • ⨂ₜ[R] i : S, f ⟨i, by aesop⟩ := by
  simp only [partialContractDiff, Equiv.setCongr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.llcomp_apply, partialContract_tprod, map_smul, LinearEquiv.coe_coe]
  erw [reindex_tprod]
  rfl


-- TBD: `self` and `trans` lemmas, as for `extendTensor` below.

variable {κ : Type*} {Sf : κ → Set ι} [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]
variable (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
variable {M : κ → Type*} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

/-- Given a family `(k : κ) → Sf` of disjoint sets and a family of linear maps
where `L k` is defined on tensors indexed by `Sf k`, construct a linear map
defined on tensors indexed by the union of `Sf`. -/
def unifyMaps (L : (k : κ) → ((⨂[R] i : Sf k, s i) →ₗ[R] (M k))) :
  (⨂[R] i : iUnion Sf, s i) →ₗ[R] (⨂[R] k, M k) := lift {
    toFun x := ⨂ₜ[R] k, (L k) (⨂ₜ[R] i : Sf k, x ⟨i, by aesop⟩)
    map_update_add' := sorry
    map_update_smul' := sorry
  }
-- TBD: prove & merge with above
/-- Given a family `(k : κ) → Sf` of disjoint sets, there is a multilinear map
from maps on tensors indexed by `Sf k` to tensors indexed by the union of `Sf`. -/
def unifMaps_ml :
  MultilinearMap R
       (fun k => (⨂[R] i : Sf k, s i) →ₗ[R] (M k))
       ((⨂[R] i : iUnion Sf, s i) →ₗ[R] (⨂[R] k, M k)) := {
    toFun L := unifyMaps L
    map_update_add' := sorry
    map_update_smul' := sorry
  }

end LinearMap

section ExtendTensor

/-- Given a family of distinguished elements `s₀ : (i : ι) → s i`, map a tensor
with index set `S ⊆ T` to a tensor with index set `T`, by padding with vectors
provided by `s₀` on `T \ S`. -/
def extendTensor (s₀ : (i : ι) → s i) : (⨂[R] (i : S), s i) →ₗ[R] (⨂[R] (i : T), s i) where
  toFun t := (tmulUnifyEquiv hsub) (t ⊗ₜ[R] (⨂ₜ[R] i : ↥(T \ S), s₀ i))
  map_add' _ _ := by simp [TensorProduct.add_tmul]
  map_smul' _ _ := by simp [←TensorProduct.smul_tmul']

variable {s₀ : (i : ι) → s i}

@[simp]
theorem extendTensor_self : extendTensor (subset_refl S) s₀ = LinearMap.id (R:=R) :=
  by ext; simp [extendTensor]

/-- Extending along a chain `S ⊆ T ⊆ U` is the same as directly extending from `S` to `U`. -/
@[simp]
theorem extendTensor_trans [(i : ι) → Decidable (i ∈ T)] {U : Set ι} (hsub₂ : T ⊆ U) :
    (extendTensor hsub₂ s₀) ∘ₗ (extendTensor hsub s₀) =
    (extendTensor (R:=R) (subset_trans hsub hsub₂) s₀) := by
  ext f
  simp only [extendTensor, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, tmulUnifyEquiv_tprod]
  congr
  ext j
  split_ifs <;> tauto

-- TBD: Prove injectivity for `extendTensor`.
-- I think that's true under the condition that `s₀ i` is not a multiple of
-- a zero divisor. If that's the case, one should probably introduce this
-- condition for `TensorProduct` first. Also, compare to `Flat` property, which
-- gives related result for maps.

end ExtendTensor
end tmulUnifyEquiv

section singletonEquiv

/- Equivalence between tensors indexed by a singleton set `{i₀}` and `s i₀`. -/
def singletonEquiv (i₀ : ι) : (⨂[R] i : ({i₀} : Set ι), s i) ≃ₗ[R] s i₀ :=
  subsingletonEquivDep (⟨i₀, by aesop⟩ : ({i₀} : Set ι))

@[simp]
theorem singletonEquiv_tprod (i₀ : ι) (f : (i : ({i₀} : Set ι)) → s i) :
    singletonEquiv i₀ (⨂ₜ[R] i, f i) = f ⟨i₀, by aesop⟩ := by
  simp [singletonEquiv]

-- `#lint` complains about this. Remove?
@[simp]
theorem singletonEquiv_tprod' (i₀ : ι) (x : s i₀) :
    singletonEquiv i₀ (⨂ₜ[R] i : ({i₀} : Set ι), cast (by aesop) x) = x := by simp

@[simp]
theorem singletonEquiv_symm_tprod (i₀ : ι) (f : (i : ({i₀} : Set ι)) → s i) :
    (singletonEquiv i₀).symm (f ⟨i₀, by aesop⟩) = (⨂ₜ[R] i, f i) := by
  rw [LinearEquiv.symm_apply_eq, singletonEquiv_tprod]

@[simp]
theorem singletonEquiv_symm_tprod' (i₀ : ι) (x : s i₀) :
    (singletonEquiv i₀).symm x = (⨂ₜ[R] i : ({i₀} : Set ι), cast (by aesop) x) := by
  rw [LinearEquiv.symm_apply_eq, singletonEquiv_tprod, cast_eq]

end singletonEquiv


section tmulInsertEquiv

variable {S : Set ι} {i₀} (h₀ : i₀ ∉ S)

section InsertLeft

variable [DecidableEq ι]

/-- The tensor product of a vector in `s i₀` and a tensor indexed by `S` is equivalent to a
tensor indexed by `insert i₀ S`, assuming `i₀ ∉ S`. -/
def tmulInsertEquiv :
    ((s i₀) ⊗[R] (⨂[R] i₁ : S, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ S), s i₁) :=
  (TensorProduct.congr (singletonEquiv i₀).symm (LinearEquiv.refl _ _)) ≪≫ₗ
  (tmulUnionEquiv (Set.disjoint_singleton_left.mpr h₀))

theorem tmulInsertEquiv_tprod (x : s i₀) (f : (i : S) → s i) :
    (tmulInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ S),
      if h : i.val ∈ ({i₀} : Set ι) then cast (by aesop) x else f ⟨i, by aesop⟩ := by
  rw [tmulInsertEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, singletonEquiv_symm_tprod']
  apply tmulUnionEquiv_tprod

@[simp]
theorem tmulInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ S)) → s i) :
    (tmulInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : S, f ⟨i, by simp⟩) := by
  rw [tmulInsertEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  erw [tmulUnionEquiv_symm_tprod]
  simp

end InsertLeft

-- RFC: Is this section too similar to the section above?
section InsertRight

variable [(i : ι) → Decidable (i ∈ S)]

/-- The tensor product of tensor indexed by `S` and a vector in `s i₀` is equivalent to a
tensor indexed by `S ∪ {i₀}`, assuming `i₀ ∉ S`. -/
def tmulInsertRightEquiv :
    ((⨂[R] i₁ : S, s i₁) ⊗[R] (s i₀)) ≃ₗ[R] ⨂[R] i : ↥(S ∪ {i₀}), s i :=
  (TensorProduct.congr (LinearEquiv.refl _ _) (singletonEquiv i₀).symm) ≪≫ₗ
  (tmulUnionEquiv (Set.disjoint_singleton_right.mpr h₀))

@[simp]
theorem tmulInsertRightEquiv_tprod (x : s i₀) (f : (i : S) → s i) :
    (tmulInsertRightEquiv h₀) ((⨂ₜ[R] i, f i) ⊗ₜ[R] x) = ⨂ₜ[R] i : ↥(S ∪ {i₀}),
        if h : ↑i ∈ S then f ⟨i, h⟩ else cast (by aesop) x := by
  simp [tmulInsertRightEquiv]

@[simp]
theorem tmulInsertRightEquiv_symm_tprod (f : (i : ↥(S ∪ {i₀})) → s i) :
    (tmulInsertRightEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (⨂ₜ[R] i : S, f ⟨i, by simp⟩) ⊗ₜ[R] f ⟨i₀, by simp⟩ := by
  simp [tmulInsertRightEquiv]

end InsertRight
end tmulInsertEquiv

section Perm

variable {S : Set ι}
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (e : Equiv.Perm ι)

/-- An equivalence `e : Equiv.Perm ι` maps tensors indexed by a set `S` to
tensors indexed by `e '' S` -/
def permSetEquiv : (⨂[R] _ : S, M) ≃ₗ[R] ⨂[R] _ : (e '' S), M :=
  reindex R (fun _ ↦ M) (Equiv.image e S)

@[simp]
theorem permSetEquiv_tprod (f : S → M) :
  (permSetEquiv e) (⨂ₜ[R] i, f i) = ⨂ₜ[R] i, f ((Equiv.image e S).symm i) := by simp [permSetEquiv]

@[simp]
theorem permSetEquiv_symm_tprod (f : (e '' S) → M) :
  (permSetEquiv e).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] i, f ((Equiv.image e S) i) := by simp [permSetEquiv]

end Perm


/-

↑↑↑ ------ code above this fold is reasonably polished ------- ↑↑↑

------------------~the~watershed~of~polish~-----------------------

↓↓↓ ------ code below this fold is experimental and messy ---- ↓↓↓

-/

open Set

section Fin

open Fin

section TprodTprod

section RecursionHelpers
-- TBD: The following feels like a very basic fact, but I didn't find an easy
-- way to get it from exsiting lemmas. (Maybe some combination
-- of`finSumFinEquiv` and `Equiv.sumSigmaDistrib` would work?)
/-! Split off last summand of a sigma type over `Fin n.succ` -/
def sigmaFinSumLastEquiv {n : Nat} {t : Fin n.succ → Type*} :
  (Σ k : Fin n.succ, t k) ≃ (Σ k : Fin n, t k.castSucc) ⊕ t (last n) := {
    toFun x :=
      if h : x.1 = last n then .inr (h ▸ x.2) else .inl ⟨⟨x.1, lt_last_iff_ne_last.mpr h⟩, x.2⟩
    invFun := Sum.rec (fun x' ↦ ⟨x'.1.castSucc, x'.2⟩) (⟨last n, ·⟩)
    left_inv _ := by aesop
    right_inv _ := by aesop
  }
-- reverse order to be in line with `finSumFinEquiv`?

variable {n : Nat}
variable {Sf : Fin (n + 1) → Type*}
variable {s : (k : Fin (n + 1)) → (i : Sf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- Move one `Fin` index into binary tensor product
protected def tprodTprodLastEquiv : (⨂[R] k : Fin n.succ, ⨂[R] i, s k i) ≃ₗ[R]
    ((⨂[R] k : Fin n, ⨂[R] i, s k.castSucc i) ⊗[R] (⨂[R] i : Sf (last n), s (last n) i)) :=
  (reindex R (fun k : Fin (n+1) ↦ ⨂[R] i : Sf k, s k i) finSumFinEquiv.symm) ≪≫ₗ
  (tmulEquivDep R (fun j ↦ ⨂[R] i : Sf (finSumFinEquiv j), s (finSumFinEquiv j) i)).symm ≪≫ₗ
  (TensorProduct.congr (LinearEquiv.refl R _) (subsingletonEquivDep 0))

protected lemma tprodTprodLastEquiv_tprod (f : (k : Fin n.succ) → (i : Sf k) → s k i) :
    PiTensorProduct.tprodTprodLastEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) =
    (⨂ₜ[R] k : Fin n, ⨂ₜ[R] i, f k.castSucc i) ⊗ₜ[R] (⨂ₜ[R] i, f (last n) i) := by
  simp only [PiTensorProduct.tprodTprodLastEquiv, LinearEquiv.trans_apply, reindex_tprod]
  erw [tmulEquivDep_symm_apply, TensorProduct.congr_tmul, subsingletonEquivDep_tprod]
  rfl

-- Move one summand from sigma type into binary tensor product

protected def tprodSigmaLastEquiv : (⨂[R] j : (Σ k : Fin n.succ, Sf k), s j.1 j.2) ≃ₗ[R]
  ((⨂[R] j : (Σ k : Fin n, Sf k.castSucc), s j.1.castSucc j.2) ⊗[R]
   (⨂[R] i : Sf (last n), s (last n) i)) :=
  (reindex R (fun j : (Σ k, Sf k) ↦ s j.1 j.2) sigmaFinSumLastEquiv) ≪≫ₗ
  (tmulEquivDep R (fun i ↦ s (sigmaFinSumLastEquiv.symm i).1 (sigmaFinSumLastEquiv.symm i).2)).symm

protected lemma tprodSigmaLastEquiv_tprod (f : (j : Σ k : Fin n.succ, Sf k) → s j.1 j.2) :
    PiTensorProduct.tprodSigmaLastEquiv (⨂ₜ[R] j, f j) =
    ((⨂ₜ[R] j : (Σ k : Fin n, Sf k.castSucc), f ⟨j.1.castSucc, j.2⟩) ⊗ₜ[R]
    (⨂ₜ[R] i, f ⟨(last n), i⟩)) := by
  simp only [PiTensorProduct.tprodSigmaLastEquiv, Nat.succ_eq_add_one,
    LinearEquiv.trans_apply, reindex_tprod]
  erw [tmulEquivDep_symm_apply]
  simp [sigmaFinSumLastEquiv]

-- @[simp] -- remove for local lemma?
-- protected lemma tprodSigmaLastEquiv_symm_tprod
--     (lv : (j : Σ k : Fin n, S k.castSucc) → s j.1.castSucc j.2)
--     (rv : (i : S (last n)) → s (last n) i) :
--   (PiTensorProduct.tprodSigmaLastEquiv.symm
--   ((⨂ₜ[R] j : (Σ k : Fin n, S k.castSucc), lv j) ⊗ₜ[R] (⨂ₜ[R] i, rv i))) =
--      (⨂ₜ[R] j : (Σ k : Fin n.succ, S k),
--       if h : j.1 = (last n) then (rv (cast h j.2)) else (lv j.1 j.2))
--     := sorry

end RecursionHelpers

variable {n : Nat}
variable {Tf : Fin n → Type*}
variable {s : (k : Fin n) → (i : Tf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- TBD: Is it desirable to reformulate that as a recursive function?
-- TBD: Use `Fintype`?
/-! A nested `PiTensorProduct` is equivalent to a single `PiTensorProduct` over
a sigma type if the outer type is finite. -/
def tprodTprodEquiv :
  (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih => exact PiTensorProduct.tprodTprodLastEquiv ≪≫ₗ
      (TensorProduct.congr ih (LinearEquiv.refl _ _)) ≪≫ₗ PiTensorProduct.tprodSigmaLastEquiv.symm

@[simp]
theorem tprodTprodEquiv_tprod (f : (k : Fin n) → (i : Tf k) → s k i) :
    tprodTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [tprodTprodEquiv, Nat.succ_eq_add_one, Nat.rec_zero, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_eq]
    simp
  | succ m ih =>
    replace ih := @ih (fun i => Tf i.castSucc) (fun i j => s i.castSucc j) _ _
      (fun i j => f i.castSucc j)
    have ht : tprodTprodEquiv (R := R) =
      PiTensorProduct.tprodTprodLastEquiv ≪≫ₗ
        (TensorProduct.congr tprodTprodEquiv (LinearEquiv.refl _ _))
          ≪≫ₗ (PiTensorProduct.tprodSigmaLastEquiv (s := s)).symm := by rfl
    simp only [ht, LinearEquiv.trans_apply, PiTensorProduct.tprodTprodLastEquiv_tprod,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, ←LinearEquiv.eq_symm_apply,
      LinearEquiv.symm_symm, PiTensorProduct.tprodSigmaLastEquiv_tprod]
    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i)) ih)

@[simp]
theorem tprodTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

variable {ι : Type*} {s : ι → Type*} {n : Nat} {Sf : Fin n → Set ι}
  (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
  [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
  [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]

def iUnionSigmaEquiv : (Σ k, Sf k) ≃ iUnion Sf where
  toFun s := ⟨s.2, by aesop⟩
  invFun s :=
    have h := mem_iUnion.mp s.prop
    have hg : (Fin.find (fun i => s.val ∈ Sf i)).isSome :=
      Fin.isSome_find_iff.mpr ⟨h.choose, h.choose_spec⟩
    ⟨(Fin.find (fun i => s.val ∈ Sf i)).get hg,
      ⟨s.val, by simp [Fin.find_spec (fun i => s.val ∈ Sf i)]⟩⟩
  left_inv := by
    simp_intro s
    generalize_proofs _ h
    congr!
    by_contra hc
    exact (H hc).ne_of_mem h s.2.prop rfl
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

def tprodFiniUnionEquiv :
    (⨂[R] k, (⨂[R] i : Sf k, s i)) ≃ₗ[R] (⨂[R] i : (Set.iUnion Sf), s i) :=
  (tprodTprodEquiv ≪≫ₗ reindex R _ (iUnionSigmaEquiv H))

@[simp]
theorem tprodFiniUnionEquiv_tprod (f : (k : Fin n) → (i : Sf k) → s i) :
    tprodFiniUnionEquiv H (⨂ₜ[R] k, ⨂ₜ[R] i, f k i)
    = ⨂ₜ[R] i, f ((iUnionSigmaEquiv H).symm i).fst ((iUnionSigmaEquiv H).symm i).snd := by
  simp only [tprodFiniUnionEquiv, LinearEquiv.trans_apply, tprodTprodEquiv_tprod]
  erw [reindex_tprod]

@[simp]
theorem tprodFiniUnionEquiv_symm_tprod (f : (i : (Set.iUnion Sf)) → s i) :
    (tprodFiniUnionEquiv H).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] k, ⨂ₜ[R] i : Sf k, f ⟨i, by aesop⟩ := by
  simp [LinearEquiv.symm_apply_eq, iUnionSigmaEquiv]




end TprodTprod

end Fin
#check LinearMap.rTensor_comp
#check  LinearMap.compLeft
#check finSumFinEquiv
#check Equiv.sigmaNatSucc
