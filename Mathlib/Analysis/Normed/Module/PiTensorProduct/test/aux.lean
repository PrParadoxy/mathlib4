import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.test.ProjectiveSeminorm
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.Basis.VectorSpace


open scoped TensorProduct
open Module Submodule Free Basis

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

lemma as_sum_on_basis (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
    x = ∑ i ∈ ((bm.tensorProduct bn).repr x).support,
      ((bm.tensorProduct bn).repr x) i • (bm i.1 ⊗ₜ[R] bn i.2) := by
  let b := bm.tensorProduct bn
  nth_rw 1 [← b.linearCombination_repr x, Finsupp.linearCombination_apply S (b.repr x),
    Finsupp.sum_of_support_subset (b.repr x) (fun _ a ↦ a) _ (by simp)]
  congr with _
  simp [b, Module.Basis.tensorProduct_apply']

lemma eq_zero_of_forall_dual_eq_zero (bm : Basis ι S M) (bn : Basis κ R N) {x : M ⊗[R] N}
    (hx : ∀ ψ : Dual R N, TensorProduct.rid R M (LinearMap.lTensor M ψ x) = 0) : x = 0 := by
  contrapose! hx
  rw [as_sum_on_basis bm bn x]
  have ⟨i, hi⟩ : (((bm.tensorProduct bn).repr x).support).Nonempty := by simp_all
  use bn.coord i.2
  apply_fun bm.coord i.1
  simp only [map_sum, coord_apply, map_zero, TensorProduct.smul_tmul']
  rw [Finset.sum_eq_single i]
  classical
  all_goals aesop (add safe forward Finsupp.single_apply)

lemma eq_zero_of_forall_dual_eq_zero_free [Module.Free R N] [Module.Free S M] (x : M ⊗[R] N)
    (hx : ∀ ψ : Dual R N, TensorProduct.rid R M (LinearMap.lTensor M ψ x) = 0) : x = 0 :=
  eq_zero_of_forall_dual_eq_zero (chooseBasis S M) (chooseBasis R N) hx











-- lemma support_basis_nonempty {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (x : M)
--     (b : Basis ι R M) (hx : x ≠ 0) : ((b.repr x).support).Nonempty := by
--   contrapose! hx
--   simp_all [←Finset.not_nonempty_iff_eq_empty]


-- variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
--   [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
--   [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

-- open Basis

-- lemma eq_zero_of_forall_dual_eq_zero (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N)
--     (hx : ∀ ψ : Dual R N,
--       ∑ i ∈ ((bm.tensorProduct bn).repr x).support,
--         ((bm.tensorProduct bn).repr x) i • ψ (bn i.2) • bm i.1 = 0)
--     : x = 0 := by
--   contrapose! hx
--   obtain ⟨i, hi⟩ := support_basis_nonempty x (bm.tensorProduct bn) hx
--   use bn.coord i.2
--   apply_fun bm.coord i.1
--   simp only [coord_apply, repr_self, map_sum, LinearMap.map_smul_of_tower, map_zero]
--   rw [Finset.sum_eq_single i]
--   classical
--   all_goals aesop (add safe forward Finsupp.single_apply)

-- theorem eq_zero_of_forall_dual_eq_zero_free [Module.Free R N] [Module.Free S M] (x : M ⊗[R] N) :
--     let bm := chooseBasis S M
--     let bn := chooseBasis R N
--     let b := bm.tensorProduct bn
--     (∀ ψ : Dual R N, ∑ i ∈ (b.repr x).support, (b.repr x) i • ψ (bn i.2) • bm i.1 = 0) → x = 0 :=
--   eq_zero_of_forall_dual_eq_zero _ _ _

-- lemma as_sum_on_basis (bm : Basis ι S M) (bn : Basis κ R N) (x : M ⊗[R] N) :
--     x = ∑ i ∈ ((bm.tensorProduct bn).repr x).support,
--       ((bm.tensorProduct bn).repr x) i • (bm i.1 ⊗ₜ[R] bn i.2) := by
--   let b := bm.tensorProduct bn
--   nth_rw 1 [← b.linearCombination_repr x, Finsupp.linearCombination_apply S (b.repr x),
--     Finsupp.sum_of_support_subset (b.repr x) (fun _ a ↦ a) _ (by simp)]
--   congr with _
--   simp [b, Module.Basis.tensorProduct_apply']

-- lemma eq_zero_of_forall_dual_eq_zero' {α} [Fintype α] {x : α → M} {y : α → N} {z : M ⊗[R] N}
--     (bm : Basis ι S M) (bn : Basis κ R N) (hxy : z = ∑ i, (x i) ⊗ₜ[R] (y i))
--     (hz : ∀ ψ : Dual R N, ∑ i, ψ (y i) • (x i) = 0) : z = 0 := by
--   replace hz : ∀ ψ : Dual R N, TensorProduct.rid R M (LinearMap.lTensor M ψ z) = 0 := by
--     simp [hxy, hz]
--   apply eq_zero_of_forall_dual_eq_zero bm bn z
--   intro ψ
--   convert hz ψ
--   conv_rhs => rw [as_sum_on_basis bm bn z, map_sum, map_sum]
--   congr with _
--   rw [TensorProduct.smul_tmul', smul_comm]
--   simp

-- variable (R S) in
-- lemma eq_zero_of_forall_dual_eq_zero_free' {α} [Fintype α] [Module.Free R N] [Module.Free S M]
--     {x : α → M} {y : α → N} {z : M ⊗[R] N} (hxy : z = ∑ i, (x i) ⊗ₜ[R] (y i))
--     (hz : ∀ ψ : Dual R N, ∑ i, ψ (y i) • (x i) = 0) : z = 0 :=
--   eq_zero_of_forall_dual_eq_zero' (chooseBasis S M) (chooseBasis R N) hxy hz


-- -- Example for vector space
-- variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} [Field R] [Field S]
--   [Algebra R S] [AddCommGroup M] [Module R M]
--   [Module S M] [IsScalarTower R S M] [AddCommGroup N] [Module R N] in

-- example {α} [Fintype α] {x : α → M} {y : α → N} {z : M ⊗[R] N} (hxy : z = ∑ i, (x i) ⊗ₜ[R] (y i))
--     (hz : ∀ ψ : Dual R N, ∑ i, ψ (y i) • (x i) = 0) : z = 0 :=
--   eq_zero_of_forall_dual_eq_zero_free' R S hxy hz



-- section cleaned
