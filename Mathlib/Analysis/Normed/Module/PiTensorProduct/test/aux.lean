import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped TensorProduct
open Module Submodule


variable (R : Type*) [DivisionRing R] {V : Type*} [AddCommGroup V] [Module R V]
theorem exists_dual_vec_ne_zero :
    ∀ v : V, v ≠ 0 → ∃ dv : Dual R V, dv v ≠ 0 := fun v hv => by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (LinearPMap.mkSpanSingleton (K := R) v (1: R) (hv)).toFun
  use g, fun hc => ?_
  have hp := LinearMap.congr_fun hg ⟨v, mem_span_singleton_self v⟩
  rw [LinearPMap.toFun_eq_coe] at hp
  simp [hc] at hp


