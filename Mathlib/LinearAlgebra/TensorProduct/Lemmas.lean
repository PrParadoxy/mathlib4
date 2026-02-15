import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct


open Module Basis

section prop_02


namespace TensorProduct

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

lemma eq_zero_of_forall_dual_eq_zero_free [Free R N] [Free S M] (x : M ⊗[R] N)
    (hx : ∀ ψ : Dual R N, TensorProduct.rid R M (LinearMap.lTensor M ψ x) = 0) : x = 0 :=
  eq_zero_of_forall_dual_eq_zero (Free.chooseBasis S M) (Free.chooseBasis R N) hx

-- Raymond's version

variable {R : Type*} [CommRing R]
  {M : Type*} {N : Type*} {P : Type*}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P] (f' : M →ₗ[R] N →ₗ[R] P)

def embed : M ⊗[R] N →ₗ[R] (M →ₗ[R] N →ₗ[R] P) →ₗ[R] P :=
  LinearMap.flip (TensorProduct.lift.equiv (RingHom.id R) M N P).toLinearMap

@[simp]
theorem embed_apply {m : M} {n : N} {B : M →ₗ[R] N →ₗ[R] P} : embed (m ⊗ₜ[R] n) B = B m n := by
  simp [embed]

theorem embed_inj [Free R N] [Free R M] :
    Function.Injective (embed (R := R) (M := M) (N := N) (P := R)) := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro m h
  contrapose! h
  intro hc
  let bm := Free.chooseBasis R M
  let bn := Free.chooseBasis R N
  have ⟨i, hi⟩ : (((bm.tensorProduct bn).repr m).support).Nonempty := by simp_all
  replace hc := LinearMap.congr_fun hc ((bm.coord i.1).smulRight (bn.coord i.2))
  rw [as_sum_on_basis bm bn m] at hc
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    embed_apply, LinearMap.coe_smulRight, coord_apply, repr_self, smul_eq_mul,
    LinearMap.zero_apply] at hc
  rw [Finset.sum_eq_single i] at hc <;> grind

lemma eq_zero_of_forall_dual_eq_zero_free' [Free R N] [Free R M] (x : M ⊗[R] N)
    (hr : ∀ B : M →ₗ[R] N →ₗ[R] R, embed x B = 0) : x = 0 :=
  embed_inj (LinearMap.ext (by simp [hr]))

end prop_02.TensorProduct


section prop_03

namespace PiTensorProduct
open scoped TensorProduct
open Set

variable {ι : Type*} {R : Type*} {M : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable {S : Set ι} {i₀} [DecidablePred fun x ↦ x ∈ S \ {i₀}] (h : i₀ ∈ S)

def tmulSingleDiffEquiv :
    ((M i₀) ⊗[R] (⨂[R] i₁ : (S \ {i₀} : Set ι), M i₁)) ≃ₗ[R] (⨂[R] i₁ : S, M i₁) :=
  (TensorProduct.congr (subsingletonEquiv (s := fun _ : PUnit => M i₀) PUnit.unit).symm
  (LinearEquiv.refl _ _)) ≪≫ₗ  (TensorProduct.comm ..) ≪≫ₗ
  (tmulEquivDep R (fun i : (S \ {i₀} : Set ι) ⊕ PUnit => M ((Equiv.Set.insert (by grind)).symm i)))
  ≪≫ₗ (reindex R (fun i : ↑(insert i₀ (S \ {i₀} : Set ι)) => M i)
    ((Equiv.Set.insert (by grind)))).symm ≪≫ₗ (reindex R _ (Equiv.subtypeEquivProp (by grind)))
