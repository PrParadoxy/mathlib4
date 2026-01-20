import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.Basis.VectorSpace


open scoped TensorProduct
open Module Submodule Free


lemma support_basis_nonempty {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (x : M)
    (b : Basis ι R M) (hx : x ≠ 0) : ((b.repr x).support).Nonempty := by
  contrapose! hx
  simp_all [←Finset.not_nonempty_iff_eq_empty]


variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Nontrivial S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

open Basis

lemma eq_zero_of_forall_dual_eq_zero (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
    (∀ ψ : Dual R N, ∑ i ∈ ((bm.tensorProduct bn).repr x).support, ψ (bn i.2) • bm i.1 = 0)
    → x = 0 := by
  contrapose!
  intro hx
  obtain ⟨i, hi⟩ := support_basis_nonempty x (bm.tensorProduct bn) hx
  use bn.coord i.2
  apply_fun bm.coord i.1
  simp only [coord_apply, repr_self, map_sum, LinearMap.map_smul_of_tower, map_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · classical
    aesop (add safe forward Finsupp.single_apply)
  · simp_all

theorem eq_zero_of_forall_dual_eq_zero_free [Module.Free R N] [Module.Free S M] (x : M ⊗[R] N) :
    let bm := chooseBasis S M
    let bn := chooseBasis R N
    let b := bm.tensorProduct bn
    (∀ ψ : Dual R N, ∑ i ∈ (b.repr x).support, ψ (bn i.2) • bm i.1 = 0) → x = 0 :=
  eq_zero_of_forall_dual_eq_zero _ _ _





