import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.LocallyConvex.WeakDual

open Module Submodule WeakBilin Topology

section Dual

variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {V : Type*} [AddCommGroup V] [Module R V]

instance instAddCommGroup : AddCommGroup (Dual R V) :=
  WeakBilin.instAddCommGroup (dualPairing R V)

instance instModule : Module R (Dual R V) :=
  WeakBilin.instModule' (dualPairing R V)

instance instTopologicalSpace : TopologicalSpace (Dual R V) :=
  WeakBilin.instTopologicalSpace (dualPairing R V)

@[simp] theorem dual_coefn_continuous : Continuous fun (x : Dual R V) y => x y :=
  continuous_induced_dom

@[simp] theorem dual_eval_continuous (y : V) : Continuous fun x : Dual R V => x y :=
  continuous_pi_iff.mp dual_coefn_continuous y

variable [IsTopologicalAddGroup R] [ContinuousSMul R R]

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (Dual R V) :=
  WeakBilin.instIsTopologicalAddGroup (dualPairing R V)

instance instContinuousAdd : ContinuousAdd (Dual R V) :=
  WeakBilin.instContinuousAdd (dualPairing R V)

instance instContinuousSMul : ContinuousSMul R (Dual R V) :=
  ⟨continuous_induced_rng.2 <|
    continuous_fst.smul ((WeakBilin.coeFn_continuous (dualPairing R V)).comp continuous_snd)⟩

instance instT2Space [T2Space R] : T2Space (Dual R V) :=
  (WeakBilin.isEmbedding (fun ⦃_ _⦄ a => a)).t2Space
