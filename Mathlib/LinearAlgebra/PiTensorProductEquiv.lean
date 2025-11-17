/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator

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

end tmulUnifyEquiv



section singletonEquiv

/- Equivalence between tensors indexed by a singleton set `{i₀}` and `s i₀`. -/
def singletonEquiv (i₀ : ι) : (⨂[R] i : ({i₀} : Set ι), s i) ≃ₗ[R] s i₀ :=
  subsingletonEquivDep (⟨i₀, by aesop⟩ : ({i₀} : Set ι))

@[simp]
theorem singletonEquiv_tprod (i₀ : ι) (f : (i : ({i₀} : Set ι)) → s i) :
    singletonEquiv i₀ (⨂ₜ[R] i, f i) = f ⟨i₀, by aesop⟩ := by
  simp [singletonEquiv]

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



section Fin

open Fin

section tmulFinSumEquiv

variable {n m} {R : Type*} {s : Fin (n + m) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-- Isomorphism between product of tensors indexed by `{1, ..., n} ⊆ Fin (n+m)`
and `{n+1, ..., m} ⊆ Fin (n+m)`, and tensors indexed by `Fin (n + m)`. -/
def tmulFinSumEquiv :
    ((⨂[R] (i₁ : Fin n), s (castAdd m i₁)) ⊗[R] (⨂[R] (i₂ : Fin m), s (natAdd n i₂)))
      ≃ₗ[R] ⨂[R] (i : Fin (n + m)), s i :=
  (tmulEquivDep R (fun i => s (finSumFinEquiv i))).trans
    (reindex R (fun i => s i) (finSumFinEquiv.symm)).symm

@[simp]
theorem tmulFinSumEquiv_tprod
    (lv : (i : Fin n) → s ⟨i, by omega⟩) (rv : (i : Fin m) → s ⟨n + i, by omega⟩) :
      tmulFinSumEquiv ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i : Fin m, rv i))
        = ⨂ₜ[R] i : Fin (n + m), addCases lv rv i := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  erw [reindex_tprod, tmulEquivDep_apply]
  congr with x
  aesop

@[simp]
theorem tmulFinSumEquiv_symm_tprod (av : (i : Fin (n + m)) → s i) :
    (tmulFinSumEquiv).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : Fin n, av (castAdd m i)) ⊗ₜ[R] (⨂ₜ[R] i : Fin m, av (natAdd n i)) := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  erw [reindex_tprod finSumFinEquiv.symm] -- removing argument causes performance issues (v4.25.0)
  erw [tmulEquivDep_symm_apply]
  simp

end tmulFinSumEquiv



section tmulFinSuccEquiv

variable {n : Nat} {R : Type*} {s : Fin (n.succ) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

def tmulFinSucc :
    (⨂[R] i : Fin n, s (castSucc i)) ⊗[R] (s (last n)) ≃ₗ[R] ⨂[R] (i : Fin n.succ), s i :=
  (tmulFinSumEquiv.symm ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl _ _ ) (subsingletonEquivDep 0))).symm

@[simp]
theorem tmulFinSucc_tprod (f : (i : Fin n) → s (castSucc i)) (x : s (last n)) :
    haveI := decidableEq_of_subsingleton (α := Fin 1)
    tmulFinSucc ((⨂ₜ[R] i, f i) ⊗ₜ[R] x)
      = ⨂ₜ[R] (i : Fin (n + 1)), addCases f (Pi.single 0 x) i := by
  erw [tmulFinSucc, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, TensorProduct.congr_symm_tmul, tmulFinSumEquiv_tprod]

@[simp]
theorem tmulFinSucc_symm (f : (i : Fin n.succ) → s i) :
    tmulFinSucc.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i, f (castSucc i)) ⊗ₜ[R] f (last n) := by
  simp only [Nat.succ_eq_add_one, tmulFinSucc, isValue, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, tmulFinSumEquiv_symm_tprod]
  erw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, subsingletonEquivDep_tprod]
  congr



section tprodiUnionEquiv

variable {ι : Type*} {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {n : Nat} {Sf : Fin n → Set ι} [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]
  (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))

instance : DecidablePred fun x ↦ x ∈ ⋃ i, Sf i := by
  intro x
  simp only [mem_iUnion]
  infer_instance

-- move out
protected lemma Set.union_iUnion_fin_succ (Sf : Fin (n + 1) → Set ι) :
    iUnion Sf = iUnion (fun i : Fin n => Sf ⟨i, by omega⟩) ∪ Sf ⟨n, by simp⟩ := by
  ext x
  simp only [mem_iUnion, mem_union]
  constructor
  · intro ⟨i, hi⟩
    by_cases hi₂ : i = n
    · exact Or.inr (by convert hi; simp [hi₂])
    · exact Or.inl (by use ⟨i.val, by omega⟩)
  · rintro (h | _)
    · exact ⟨castAdd 1 h.choose, h.choose_spec⟩
    · use ⟨n, by omega⟩

def tprodFiniUnionEquiv :
    (⨂[R] k, (⨂[R] i : Sf k, s i)) ≃ₗ[R] (⨂[R] i : (Set.iUnion Sf), s i) := by
  induction n with
  | zero =>
    have : IsEmpty (iUnion Sf) := by simp
    exact (isEmptyEquiv (Fin 0)).trans ((isEmptyEquiv (iUnion Sf)).symm)
  | succ k ih =>

    have hd : Disjoint (⋃ i : Fin k, Sf ⟨↑i, by omega⟩) (Sf (last k)) := by
      simpa using fun i : Fin k =>
        @H ⟨i, by omega⟩ ⟨k, by omega⟩ (by simp; omega)

    replace ih := @ih (fun i => Sf ⟨i, by omega⟩) inferInstance (fun i j _ =>
      @H ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp; omega))

    exact (reindex R _ (Equiv.subtypeEquivProp (Set.union_iUnion_fin_succ Sf)) ≪≫ₗ
      (tmulFinSucc.symm ≪≫ₗ (TensorProduct.congr ih (LinearEquiv.refl _ _))
      ≪≫ₗ (tmulUnionEquiv hd)).symm).symm




theorem tprodFiniUnionEquiv_tprod (f : (k : Fin n) → (i : Sf k) → s i):
    tprodFiniUnionEquiv H (⨂ₜ[R] k, ⨂ₜ[R] i, f k i)
      =
    ⨂ₜ[R] i : (Set.iUnion Sf),
      have h := (Set.mem_iUnion.mp i.prop)
      f h.choose ⟨i.val, h.choose_spec⟩ := by
  induction n with
  | zero =>
    simp [tprodFiniUnionEquiv]
    congr with j
    exfalso
    exact IsEmpty.false (self := by simp) j
  | succ k ih =>

    have hdisj : Disjoint (⋃ i : Fin k, Sf ⟨↑i, by omega⟩) (Sf (last k)) := by
      simpa using fun i : Fin k => @H ⟨i, by omega⟩ ⟨k, by omega⟩ (by simp; omega)

    have H' : Pairwise fun (m : Fin k) l ↦ Disjoint (Sf ⟨m, by omega⟩) (Sf ⟨l, by omega⟩) :=
      fun i j _ => @H ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp; omega)

    replace ih := @ih (fun i => Sf ⟨i, by omega⟩) inferInstance H' (fun i j => f ⟨i, by omega⟩ j)

    have hfinal :
      (tprodFiniUnionEquiv H) =
      (reindex R _ (Equiv.subtypeEquivProp (Set.union_iUnion_fin_succ Sf)) ≪≫ₗ
      (tmulFinSucc.symm ≪≫ₗ (TensorProduct.congr (tprodFiniUnionEquiv H') (LinearEquiv.refl _ _))
      ≪≫ₗ (tmulUnionEquiv (s := s) hdisj)).symm).symm := by rfl

    rw [hfinal]
    clear hfinal
    simp_all
    -- now apply all LinearEquiv from lhs to rhs (something like LinearEquiv.symm_apply_eq)
    -- and close the goal with ih.
