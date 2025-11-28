/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.LinearAlgebra.TensorProduct.Associator
import mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

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

@[simp]
theorem subsingletonEquivDep_tprod (f : (i : ι) → s i) :
    subsingletonEquivDep i₀ (⨂ₜ[R] i, f i) = f i₀ := by simp [subsingletonEquivDep]

-- This exposes a quite concrete construction in the signature.
/-- Any tensor indexed by a unique type is a pure tensor -/
lemma subsingletonEquivDep_eq_tprod (z : ⨂[R] i, s i) :
    z = ⨂ₜ[R] i, (Pi.single i₀ (subsingletonEquivDep i₀ z)) i := by
  induction z using PiTensorProduct.induction_on
  all_goals rw [←subsingletonEquivDep_symm_apply, LinearEquiv.symm_apply_apply]


section
variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- Tensor product of `M` over a singleton set is equivalent to `M`. Use
`subsingletonEquivDep` for dependent case. -/
def subsingletonEquiv' : (⨂[R] _ : ι, M) ≃ₗ[R] M := subsingletonEquivDep i₀

@[simp]
theorem subsingletonEquiv'_tprod' (f : (i : ι) → M) :
    subsingletonEquiv' i₀ (⨂ₜ[R] _, f i₀) = f i₀ := by
  simp [subsingletonEquiv']

@[simp]
theorem subsingletonEquiv'_symm' (x : M) :
    (subsingletonEquiv' i₀).symm x = (⨂ₜ[R] _, x) := by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv'_tprod' i₀ (fun _ => x)]

end


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
  simp only [tmulBipartitionEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  erw [reindex_tprod]
  rfl

@[simp]
theorem tmulBipartition_symm_tprod (f : (i : ι) → s i) :
    tmulBipartitionEquiv.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i : S, f i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, f i) := by
  rw [LinearEquiv.symm_apply_eq]; simp

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

@[simp]
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



section Finset

variable [DecidableEq ι] {F : Finset ι} {i₀} (h₀ : i₀ ∉ F)

-- tmulFinInsertEquiv is necessary because the direct application of tmulInsertEquiv on `Finset`s
-- produces tensors indexed by `↥(insert i₀ ↑F)` whereas `↥↑(insert i₀ F)` might be desirable.
def tmulFinsetInsertEquiv :
    ((s i₀) ⊗[R] (⨂[R] i₁ : F, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ F), s i₁) :=
  tmulInsertEquiv h₀ ≪≫ₗ reindex R _ (Equiv.subtypeEquivProp (Finset.coe_insert i₀ F)).symm

@[simp]
theorem tmulFinsetInsertEquiv_tprod (x : s i₀) (f : (i : F) → s i) :
    (tmulFinsetInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ F),
      if h : i.val ∈ ({i₀} : Set ι) then cast (by aesop) x else f ⟨i, by aesop⟩ := by
  erw [tmulFinsetInsertEquiv, LinearEquiv.trans_apply, tmulInsertEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulFinsetInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ F)) → s i) :
    (tmulFinsetInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : F, f ⟨i, by simp⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulFinsetInsertEquiv_tprod]
  congr with i
  simp only [mem_singleton_iff, SetLike.eta, right_eq_dite_iff]
  intro _
  generalize_proofs _ _
  aesop

end Finset



theorem induction_on_set_finite
    {S : Set ι} (hS : S.Finite)
    {motive : ∀ {T : Set ι} (_ : T.Finite), (⨂[R] i : T, s i) → Prop}
    (empty : ∀ r : R, motive finite_empty ((isEmptyEquiv (∅ : Set ι)).symm r))
    (insert : ∀ (i₀ : ι) (T : Set ι) (_ : i₀ ∉ T) (hT : T.Finite),
      (∀ (w : ⨂[R] i : T, s i), motive hT w) →
        ∀ (z : ⨂[R] i : ↑(insert i₀ T), s i), motive (hT.insert i₀) z)
    (z : ⨂[R] i : S, s i) : motive hS z := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa [LinearEquiv.symm_apply_apply] using empty (isEmptyEquiv (∅ : Set ι) z)
  | @insert i₀ S hi₀ hs hm => exact insert i₀ S hi₀ hs hm z

theorem induction_on_finset
    [DecidableEq ι] (S : Finset ι)
    {motive : ∀ {T : Finset ι}, (⨂[R] i : (T : Set ι), s i) → Prop}
    (empty : ∀ r : R, motive ((isEmptyEquiv (∅ : Finset ι)).symm r))
    (insert : ∀ (i₀ : ι) (T : Finset ι) (_ : i₀ ∉ T),
      (∀ (w : ⨂[R] i : (T : Set ι), s i), motive w) →
        ∀ (z : ⨂[R] i : ↑(insert i₀ T), s i), motive z)
    (z : ⨂[R] i : (S : Set ι), s i) : motive z := by
  induction S using Finset.induction with
  | empty => simpa [LinearEquiv.symm_apply_apply] using empty (isEmptyEquiv (∅ : Finset ι) z)
  | insert i₀ S hi₀ hm => exact insert i₀ S hi₀ hm z


open scoped DirectSum TensorProduct
variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

def toDirectSum' : TensorAlgebra R M →ₐ[R] ⨁ n, ⨂[R]^n M :=
  TensorAlgebra.lift R <|
    DirectSum.lof R ℕ (fun n => ⨂[R]^n M) _ ∘ₗ
      (LinearEquiv.symm <| subsingletonEquiv' (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap

@[simp]
theorem toDirectSum_ι' (x : M) :
    toDirectSum' (TensorAlgebra.ι R x) =
      DirectSum.of (fun n => ⨂[R]^n M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => x) := by
  simp [toDirectSum', TensorAlgebra.lift_ι_apply, DirectSum.lof_eq_of]
