import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Restricted.RestrictedMultilinearMap

open PiTensorProduct RestrictedProduct
open scoped TensorProduct

variable {ι : Type*}
variable {E : ι → Type*} {R : Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
variable (E₀ : (i : ι) → E i)

instance directedSystem : DirectedSystem
    (fun S : FiniteSet ι ↦ ⨂[R] (i : S.val), E i)
    (fun _ _ hsub ↦ extendTensor hsub E₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor h2 E₀)]
    apply congrFun
    simp [←LinearMap.coe_comp]

variable (R) in
abbrev Restricted :=
  DirectLimit (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i) (fun _ _ hsub ↦ extendTensor hsub E₀)

namespace Restricted

noncomputable def of {S : FiniteSet ι} :
    (⨂[R] i : ↑S, E i) →ₗ[R] Restricted R E₀ :=
  DirectLimit.Module.of R _ (fun S : FiniteSet ι ↦ ⨂[R] i : ↑S, E i) ..

variable (M : Type*) [AddCommMonoid M] [Module R M]

-- This is phrased in the same manner as `Module.DirectLimit.lift_unique`
-- also similar to `PiTensorProduct.lift.unique'`
/-- A LinearMap `l` on Restricted tensors is uniquely determined by a LinearMap
  `M :=  l.comp (of E₀)` on the PiTensorProducts. Furthermore, `M` can be also
  interpreted as a Multilinearmap on the underlying vectors through the universal property
  of `PiTensorProduct`s, i.e `PiTensorProduct.lift.symm`. So a Multilinearmap
  `ML := lift.symm ( l.comp (of E₀))` uniquely determines `l`.
-/
theorem lift_unique (l : Restricted R E₀ →ₗ[R] M) :
    l = DirectLimit.Module.lift _ _ (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i)
      (fun _ _ hsub ↦ extendTensor hsub E₀) (fun S => l.comp (of E₀))
      (fun i j hij x ↦ by simp [of]) := by
  ext; simp [of]

-- noncomputable def lift : MultilinearMap R E M →ₗ[R] Restricted R E₀ →ₗ[R] M where
--   toFun M := DirectLimit.Module.lift _ _ (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i)
--     (fun _ _ hsub ↦ extendTensor hsub E₀)
--     (fun S => PiTensorProduct.lift (M.domDomRestrictₗ (fun i => i ∈ S.val) (fun i => E₀ i.val)))
--     (fun s1 s2 hsub x ↦ by
--       induction x using PiTensorProduct.induction_on with
--       | smul_tprod r f =>
--         simp only [MultilinearMap.domDomRestrictₗ, MultilinearMap.coe_mk, map_smul,
--           extendTensor_tprod, lift.tprod, MultilinearMap.domDomRestrict_apply]
--         congr with i
--         have (i : ι) (hi : i ∈ s1.val) : i ∈ s2.val := by aesop
--         all_goals aesop
--       | add a b ha hb => simp_all
--     )
--   map_add' := by aesop
--   map_smul' := by aesop

-- open Classical in
-- noncomputable def unlift : (Restricted R E₀ →ₗ[R] M) →ₗ[R] MultilinearMap R E M where
--   toFun l := {
--     toFun v :=
--       if h : ∃ vr : Πʳ i, [E i, {E₀ i}], v = vr then
--         let S : FiniteSet ι := ⟨_, Filter.eventually_cofinite.mp h.choose.prop⟩
--         l.comp (of E₀ (S := S)) (PiTensorProduct.tprod R (fun i => v i))
--       else
--         0
--     map_update_add' := sorry
--     map_update_smul' := sorry
--   }
--   map_add' := by aesop
--   map_smul' := by aesop

open RestrictedMultilinearMap

noncomputable def universal : RestrictedMultilinearMap R E₀ M ≃ₗ[R] Restricted R E₀ →ₗ[R] M :=
  LinearEquiv.ofLinear (M := RestrictedMultilinearMap R E₀ M)
  ({
    toFun rm := DirectLimit.Module.lift _ _ (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i)
      (fun _ _ hsub ↦ extendTensor hsub E₀)
      (fun S => PiTensorProduct.lift (rm.toMultilinearMap S))
      (sorry)
    map_add' := by aesop
    map_smul' := by aesop
    }
    )
  ({
    toFun l := {
      toFun v :=
        let S : FiniteSet ι := ⟨_, Filter.eventually_cofinite.mp v.prop⟩
        l.comp (of E₀ (S := S)) (PiTensorProduct.tprod R (fun i => v i))
      map_update_add' := sorry
      map_update_smul' := sorry

    }
    map_add' := by aesop
    map_smul' := by aesop
  })
  (sorry)
  (sorry)
