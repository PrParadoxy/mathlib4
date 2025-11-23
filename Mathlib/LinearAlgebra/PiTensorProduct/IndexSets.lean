/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

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

@[expose] public section

open PiTensorProduct
open scoped TensorProduct

namespace PiTensorProduct

variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

open Set

/-- Tensors indexed by `ι` are isomorphic to tensors indexed by `univ : Set ι`. -/
def univEquiv : (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i : ↥univ, s i.val := reindex R s (Equiv.Set.univ ι).symm

@[simp]
theorem univEquiv_tprod (f : (i : ι) → s i) : univEquiv (⨂ₜ[R] i, f i) = ⨂ₜ[R] i : ↥univ, f i.val :=
  reindex_tprod (Equiv.Set.univ ι).symm f

@[simp]
theorem univEquiv_symm_tprod (f : (i : ι) → s i) :
    univEquiv.symm (⨂ₜ[R] i : ↥univ, f i) = (⨂ₜ[R] i, f i) := by simp [LinearEquiv.symm_apply_eq]

section tmulUnionEquiv

variable {S₁ S₂ : Set ι} (hdisj : Disjoint S₁ S₂) [(i : ι) → Decidable (i ∈ S₁)]

/-- Tensors indexed by a set `S₁` times tensors indexed by a disjoint set `S₂`
are isomorphic to tensors indexed by the union `S₁ ∪ S₂`. -/
def tmulUnionEquiv :
    ((⨂[R] (i₁ : S₁), s i₁) ⊗[R] (⨂[R] (i₂ : S₂), s i₂)) ≃ₗ[R] ⨂[R] (i : ↥(S₁ ∪ S₂)), s i :=
  (tmulEquivDep R (fun i ↦ s ((Equiv.Set.union hdisj).symm i))) ≪≫ₗ
  (reindex R (fun i : ↥(S₁ ∪ S₂) ↦ s i) (Equiv.Set.union hdisj)).symm

@[simp]
theorem tmulUnionEquiv_symm_tprod (f : (i : ↥(S₁ ∪ S₂)) → s i) :
    (tmulUnionEquiv hdisj).symm (⨂ₜ[R] i, f i) =
      (⨂ₜ[R] i : S₁, f ⟨i, by aesop⟩) ⊗ₜ (⨂ₜ[R] i : S₂, f ⟨i, by aesop⟩) := by
  simp only [tmulUnionEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, reindex_tprod]
  apply tmulEquivDep_symm_apply

@[simp]
theorem tmulUnionEquiv_tprod (lv : (i : S₁) → s i) (rv : (i : S₂) → s i) :
    (tmulUnionEquiv hdisj) ((⨂ₜ[R] i : S₁, lv i) ⊗ₜ (⨂ₜ[R] i : S₂, rv i)) =
      ⨂ₜ[R] j : ↥(S₁ ∪ S₂), if h : ↑j ∈ S₁ then lv ⟨j, h⟩ else rv ⟨j, by aesop⟩ := by
  rw [<-LinearEquiv.eq_symm_apply, tmulUnionEquiv_symm_tprod]
  congr with i
  · simp
  · simp [disjoint_right.mp hdisj i.property]

end tmulUnionEquiv

section tmulBipartitionEquiv

variable {S : Set ι} [(i : ι) → Decidable (i ∈ S)]

/-- Tensors indexed by a set `S` times tensors indexed by its complement `Sᶜ`
are isomorphic to the space of all tensors. -/
def tmulBipartitionEquiv : (⨂[R] i₁ : S, s i₁) ⊗[R] (⨂[R] i₂ : ↥Sᶜ, s i₂) ≃ₗ[R] ⨂[R] i, s i :=
  (tmulUnionEquiv (disjoint_compl_right)) ≪≫ₗ (reindex R (fun i : ↥(S ∪ Sᶜ) ↦ s i)
    (Equiv.trans (Equiv.subtypeEquivProp (Set.union_compl_self S)) (Equiv.Set.univ ι)))

@[simp]
theorem tmulBipartitionEquiv_tprod (lv : (i : S) → s i) (rv : (i : ↥Sᶜ) → s i) :
    tmulBipartitionEquiv ((⨂ₜ[R] i : S, lv i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, rv i)) =
      ⨂ₜ[R] j, if h : j ∈ S then lv ⟨j, h⟩ else rv ⟨j, by aesop⟩ := by
  rw [tmulBipartitionEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulBipartition_symm_tprod (f : (i : ι) → s i) :
    tmulBipartitionEquiv.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i : S, f i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, f i) := by
  simp [LinearEquiv.symm_apply_eq]

end tmulBipartitionEquiv


section tmulUnifyEquiv

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

/-- For sets `S ⊆ T`, tensors indexed by `S` times tensors indexed by `T \ S`
are isomorphic to tensors indexed by `T`. -/
def tmulUnifyEquiv :
    (⨂[R] i₁ : S, s i₁) ⊗[R] (⨂[R] i₂ : ↥(T \ S), s i₂) ≃ₗ[R] ⨂[R] i : T, s i :=
  (tmulUnionEquiv (disjoint_sdiff_right)) ≪≫ₗ
    (reindex R (fun i : ↥(S ∪ T \ S) ↦ s i) (Equiv.subtypeEquivProp (union_diff_cancel hsub)))

@[simp]
theorem tmulUnifyEquiv_tprod (lv : (i : S) → s i) (rv : (i : ↑(T \ S)) → s i) :
    tmulUnifyEquiv hsub ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i, rv i)) =
      ⨂ₜ[R] i : T, if h : ↑i ∈ S then lv ⟨↑i, by aesop⟩ else rv ⟨↑i, by aesop⟩ := by
  rw [tmulUnifyEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulUnifyEquiv_tprod_symm (av : (i : T) → s i) :
    (tmulUnifyEquiv hsub).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : S, av ⟨i, by aesop⟩) ⊗ₜ (⨂ₜ[R] i : ↥(T \ S), av ⟨i, by aesop⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulUnifyEquiv_tprod]
  congr
  aesop

section LinearMap

open Module

-- TBD: Unify with `map` section of "PiTensorProduct.lean"
-- TBD: And with `TensorProduct.map` section, including notation.
-- TBD: What's up with left / right asymmetry?

variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- Lifts a linear map on tensors with index set `S ⊆ T` to a linear map
on tensors with index set `T`. Bundled as a homomorphism of linear maps. -/
def extendLinearHom : ((⨂[R] i : S, s i) →ₗ[R] M) →ₗ[R]
    ((⨂[R] i : T, s i) →ₗ[R] (M ⊗[R] (⨂[R] (i₂ : ↑(T \ S)), s i₂))) :=
  let TmS := ⨂[R] (i : ↑(T \ S)), s i
  ((tmulUnifyEquiv hsub).congrLeft (M:=M ⊗[R] TmS) R).toLinearMap ∘ₗ LinearMap.rTensorHom TmS

/-- Extension of an endomorphism on tensors with index set `S ⊆ T` to one on
tensors with index set `T`. Bundled as a homomorphism of endomorphisms. -/
def extendEnd : End R (⨂[R] i : S, s i) →ₗ[R] End R (⨂[R] i : T, s i) :=
  (tmulUnifyEquiv hsub).congrRight.toLinearMap ∘ₗ extendLinearHom hsub

/-- Partial contraction: a functional on tensors with index set `S ⊆ T` contracts
tensors with index set `T` to tensors with index set `T \ S`. Bundled as a linear map. -/
def partialContract :
    ((⨂[R] i : S, s i) →ₗ[R] R) →ₗ[R] (⨂[R] i : T, s i) →ₗ[R] ⨂[R] (i₂ : ↑(T \ S)), s i₂ :=
   (TensorProduct.lid _ _).congrRight.toLinearMap ∘ₗ (extendLinearHom hsub)

@[simp]
theorem extendLinear_tprod (l : (⨂[R] i : S, s i) →ₗ[R] M) (f : (i : T) → s i) :
    extendLinearHom hsub l (⨂ₜ[R] i, f i)
    = l (⨂ₜ[R] i₁ : S, f ⟨i₁, by aesop⟩) ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨i₂, by aesop⟩) := by
  simp [extendLinearHom, LinearEquiv.congrLeft]

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

end LinearMap

section ExtendTensor

open TensorProduct

variable {s₀ : (i : ι) → s i}

/-- Given a family of distinguished elements `s₀ : (i : ι) → s i` and sets `S ⊆ T`,
map a tensor with index set to a tensor with index set `T`, by padding with vectors
provided by `s₀` on `T \ S`. -/
def extendTensor (s₀ : (i : ι) → s i) : (⨂[R] (i : S), s i) →ₗ[R] (⨂[R] (i : T), s i) where
  toFun t := (tmulUnifyEquiv hsub) (t ⊗ₜ[R] (⨂ₜ[R] i : ↥(T \ S), s₀ i))
  map_add' := by simp [TensorProduct.add_tmul]
  map_smul' := by simp [←TensorProduct.smul_tmul']

/-- Extending the index set of a tensor from `S` to `S` is trivial. -/
@[simp]
theorem extendTensor_self : extendTensor (subset_refl S) s₀ = LinearMap.id (R:=R) :=
  by ext; simp [extendTensor]

/-- Extending the index set of a tensor along a chain `S ⊆ T ⊆ U` is the same as
directly extending from `S` to `U`. -/
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

end ExtendTensor
end tmulUnifyEquiv

section singletonSetEquiv

variable (i₀ : ι)

/-- Tensors indexed by a singleton set `{i₀}` are equivalent to vectors in `s i₀`. -/
def singletonSetEquiv : (⨂[R] i : ({i₀} : Set ι), s i) ≃ₗ[R] s i₀ :=
  subsingletonEquivDep (⟨i₀, by simp⟩ : ({i₀} : Set ι))

@[simp]
theorem singletonEquiv_tprod (f : (i : ({i₀} : Set ι)) → s i) :
    singletonSetEquiv i₀ (⨂ₜ[R] i, f i) = f ⟨i₀, by simp⟩ := by simp [singletonSetEquiv]

@[simp]
theorem singletonEquiv_symm_tprod (x : s i₀) :
    (singletonSetEquiv i₀).symm x = (⨂ₜ[R] i : ({i₀} : Set ι), cast (by aesop) x) := by
  rw [LinearEquiv.symm_apply_eq, singletonEquiv_tprod, cast_eq]

end singletonSetEquiv

section tmulInsertEquiv

variable {S : Set ι} {i₀} (h₀ : i₀ ∉ S)
variable [DecidableEq ι]

/-- Vectors in `s i₀` times tensors indexed by `S` are equivalent to tensors
indexed by `insert i₀ S`, assuming `i₀ ∉ S`. -/
def tmulInsertEquiv :
    ((s i₀) ⊗[R] (⨂[R] i₁ : S, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ S), s i₁) :=
  (TensorProduct.congr (singletonSetEquiv i₀).symm (LinearEquiv.refl _ _)) ≪≫ₗ
  (tmulUnionEquiv (Set.disjoint_singleton_left.mpr h₀))

@[simp]
theorem tmulInsertEquiv_tprod (x : s i₀) (f : (i : S) → s i) :
    (tmulInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ S),
      if h : i.val ∈ ({i₀} : Set ι) then cast (by aesop) x else f ⟨i, by aesop⟩ := by
  rw [tmulInsertEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, singletonEquiv_symm_tprod]
  apply tmulUnionEquiv_tprod

@[simp]
theorem tmulInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ S)) → s i) :
    (tmulInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : S, f ⟨i, by simp⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulInsertEquiv_tprod]
  grind

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

end PiTensorProduct
