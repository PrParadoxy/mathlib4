import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.PiTensorProduct


variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

variable {S : Type*} [SetLike S ι]


open PiTensorProduct
open scoped TensorProduct

namespace PiTensorProduct

open Set


variable {S₁ S₂ : S}
variable (hdisj : Disjoint (S₁ : Set ι) (S₂ : Set ι))
variable [(i : ι) → Decidable (i ∈ S₁)]

/-- Tensors indexed by a SetLike `S₁` times tensors indexed by a disjoint SetLike `S₂`
are isomorphic to tensors indexed by the union `(S₁ : Set α) ∪ (S₂ : Set α)`. -/
def tmulUnionEquivSetLike :
    ((⨂[R] (i₁ : S₁), s i₁) ⊗[R] (⨂[R] (i₂ : S₂), s i₂)) ≃ₗ[R]
    ⨂[R] (i : ↥(((S₁ ∪ S₂) : Set ι))), s i :=
  (tmulEquivDep R (fun i ↦ s ((Equiv.Set.union hdisj).symm i))) ≪≫ₗ
  (reindex R (fun i : ↥(S₁ ∪ S₂ : Set ι) ↦ s i) (Equiv.Set.union hdisj)).symm


variable [DecidableEq ι] (F₁ F₂ : Finset ι) (hdisj : Disjoint (F₁ : Set ι) (F₂ : Set ι))

#check tmulUnionEquivSetLike  hdisj (R := R) (s := s)
