import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
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
abbrev RestrictedTensor :=
  DirectLimit (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i) (fun _ _ hsub ↦ extendTensor hsub E₀)

namespace RestrictedTensor

noncomputable def of (S : FiniteSet ι) :
    (⨂[R] i : ↑S, E i) →ₗ[R] RestrictedTensor R E₀ :=
  DirectLimit.Module.of R _ (fun S : FiniteSet ι ↦ ⨂[R] i : ↑S, E i) ..

variable (R) in
theorem of_f (S : FiniteSet ι) (f : Π i, E i) :
    ∀ J, (hSJ : S ≤ J) →
    (of E₀ S) (⨂ₜ[R] i, f i) = (of E₀ J) ((extendTensor hSJ E₀) (⨂ₜ[R] i, f i)) := by
  intro J hSJ
  simp [of, ← DirectLimit.Module.of_f (hij := hSJ)]

variable (R) {E₀} in
theorem of_f' (f : Πʳ (i : ι), [E i, {E₀ i}]) :
    ∀ J, ⟨_, f.prop⟩ ≤ J → (of E₀ ⟨_, f.prop⟩) (⨂ₜ[R] i, f i) = (of E₀ J) (⨂ₜ[R] i, f i) := by
  intro J hSJ
  simp only [of, ← DirectLimit.Module.of_f (hij := hSJ), extendTensor_tprod, dite_eq_ite]
  congr with j
  split_ifs with hj
  · rfl
  · simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hj
    exact hj.symm

variable (M : Type*) [AddCommMonoid M] [Module R M]

open RestrictedMultilinearMap
open scoped TensorProduct

noncomputable def lift : RestrictedMultilinearMap R E₀ M →ₗ[R] RestrictedTensor R E₀ →ₗ[R] M :=
  {
    toFun rm := DirectLimit.Module.lift _ _ (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i)
      (fun _ _ hsub ↦ extendTensor hsub E₀)
      (fun S => PiTensorProduct.lift (rm.toMultilinearMap S))
      (fun s1 s2 hsub x ↦ by
        induction x using PiTensorProduct.induction_on with
        | smul_tprod r f =>
          simp only [map_smul, extendTensor_tprod, lift.tprod, toMultilinearMap_apply_apply]
          congr 2 with _
          have (i : ι) (hi : i ∈ s1.val) : i ∈ s2.val := Set.mem_of_subset_of_mem hsub hi
          aesop
        | add a b ha hb => aesop
      )
    map_add' := by aesop
    map_smul' := by aesop
  }

open Set in
noncomputable def lift.symm :
    (RestrictedTensor R E₀ →ₗ[R] M) →ₗ[R] RestrictedMultilinearMap R E₀ M :=
  {
    toFun l := {
      toFun f := l.comp (of E₀ ⟨_, f.prop⟩) (PiTensorProduct.tprod R (fun i => f i))
      map_update_add' f i x y := by
        let sx : FiniteSet ι := ⟨_, (f.update i x).prop⟩
        let sy : FiniteSet ι := ⟨_, (f.update i y).prop⟩
        let sxy : FiniteSet ι := ⟨_, (f.update i (x + y)).prop⟩
        let s : FiniteSet ι := ⟨sx.val ∪ sy.val ∪ sxy.val ∪ {i}, by
          rw [Set.union_singleton]
          exact Finite.insert _ (Finite.union (Finite.union sx.prop sy.prop) sxy.prop)
        ⟩
        simp only [LinearMap.coe_comp, Function.comp_apply]
        conv_lhs => rw [of_f' R (f.update i (x + y)) s (by intro _; grind)]
        conv_rhs => rw [of_f' R (f.update i x) s (by intro _; grind),
          of_f' R (f.update i y) s (by intro _; grind)]
        have h (x) : (fun j : s.val ↦ Function.update (⇑f) i x j) =
          Function.update (fun i : s.val ↦ f i) ⟨i, by grind⟩ x := by grind
        simp [h]
      map_update_smul' f i c x := by
        let sx : FiniteSet ι := ⟨_, (f.update i x).prop⟩
        let sc : FiniteSet ι := ⟨_, (f.update i (c • x)).prop⟩
        let s : FiniteSet ι := ⟨sx.val ∪ sc.val ∪ {i}, by
            rw [Set.union_singleton]
            exact Finite.insert _ (Finite.union sx.prop sc.prop)⟩
        simp only [LinearMap.coe_comp, Function.comp_apply]
        conv_lhs => rw [of_f' R (f.update i (c • x)) s (by intro _; grind)]
        conv_rhs => rw [of_f' R (f.update i x) s (by intro _; grind)]
        have h (x) : (fun j : s.val ↦ Function.update (⇑f) i x j) =
          Function.update (fun i : s.val ↦ f i) ⟨i, by grind⟩ x := by grind
        simp [h]
    }
    map_add' := by aesop
    map_smul' := by aesop
  }



-- noncomputable def universal : RestrictedMultilinearMap R E₀ M ≃ₗ[R]
-- RestrictedTensor R E₀ →ₗ[R] M :=
--   LinearEquiv.ofLinear (M := RestrictedMultilinearMap R E₀ M)
--   ({
--     toFun rm := DirectLimit.Module.lift _ _ (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i)
--       (fun _ _ hsub ↦ extendTensor hsub E₀)
--       (fun S => PiTensorProduct.lift (rm.toMultilinearMap S))
--       (sorry)
--     map_add' := by aesop
--     map_smul' := by aesop
--     }
--     )
--   ({
--     toFun l := {
--       toFun v :=
--         let S : FiniteSet ι := ⟨_, Filter.eventually_cofinite.mp v.prop⟩
--         l.comp (of E₀ (S := S)) (PiTensorProduct.tprod R (fun i => v i))
--       map_update_add' := sorry
--       map_update_smul' := sorry

--     }
--     map_add' := by aesop
--     map_smul' := by aesop
--   })
--   (by ext j; simp)
--   (by ext j; simp)




-- This is phrased in the same manner as `Module.DirectLimit.lift_unique`
-- also similar to `PiTensorProduct.lift.unique'`
/-- A LinearMap `l` on Restricted tensors is uniquely determined by a LinearMap
  `M :=  l.comp (of E₀)` on the PiTensorProducts. Furthermore, `M` can be also
  interpreted as a Multilinearmap on the underlying vectors through the universal property
  of `PiTensorProduct`s, i.e `PiTensorProduct.lift.symm`. So a Multilinearmap
  `ML := lift.symm ( l.comp (of E₀))` uniquely determines `l`.
-/
-- theorem lift_unique (l : RestrictedTensor R E₀ →ₗ[R] M) :
--     l = DirectLimit.Module.lift _ _ (fun S : FiniteSet ι ↦ ⨂[R] (i : ↑S), E i)
--       (fun _ _ hsub ↦ extendTensor hsub E₀) (fun S => l.comp (of E₀ S))
--       (fun i j hij x ↦ by simp [of]) := by
--   ext; simp [of]
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
