import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Separation

open Module Topology WeakBilin Submodule

variable (R : Type*) [CommSemiring R]
variable (V : Type*) [AddCommGroup V] [Module R V]

/-- A type synonym for `Dual R W`, equipping it with weak topology. -/
abbrev AlgWeakDual := WeakBilin (dualPairing R V)

instance : DFunLike (AlgWeakDual R V) V fun _ => R where
  coe v := v.toFun
  coe_injective' := fun _ _ h => by simpa using h

instance : LinearMapClass (AlgWeakDual R V) R V R where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'

namespace AlgWeakDual

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]
  [T2Space R] [ContinuousConstSMul R R] [ContinuousAdd R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Forgets linear structure of `AlgWeakDual V` for tychonoff's theorem. -/
def dualembed : AlgWeakDual R V → (V → R) := DFunLike.coe

theorem dualembed_isclosed_embedding :
    IsClosedEmbedding (dualembed (R := R) (V := V)) :=
  IsClosedEmbedding.mk (DFunLike.coe_injective.isEmbedding_induced)
    (LinearMap.isClosed_range_coe _ _ _)

/-- A set of dual vectors is compact if it is closed,
    and its image under dualEmbed is a subset of a compact set. -/
theorem isCompact_image_dualembed {s : Set (AlgWeakDual R V)} {c : Set (V → R)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : dualembed '' s ⊆ c) : IsCompact s :=
  dualembed_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (dualembed_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)

variable {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module R V]

theorem exists_dual_vec_ne_zero :
    ∀ v: V, v ≠ 0 → ∃ dv: AlgWeakDual R V, dv v ≠ 0 := fun v hv => by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (LinearPMap.mkSpanSingleton (K := R) v (1: R) (hv)).toFun
  use g
  intro hc
  have hp := LinearMap.congr_fun hg ⟨v, mem_span_singleton_self v⟩
  rw [LinearPMap.toFun_eq_coe] at hp
  simp [hc] at hp

variable [TopologicalSpace R] [ContinuousConstSMul R R] [IsTopologicalAddGroup R]

theorem eval_dualpairing_injective :
    Function.Injective ((eval (dualPairing R V))) := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro v hv
  by_contra! hc
  obtain ⟨dv, hdv⟩ := exists_dual_vec_ne_zero (R := R) v hc
  exact hdv (congrArg (fun f => f dv) hv)

/-!
# A `Weak* Topology` is a `LocallyConvexSpace`:
1. Weak* topology makes evaluation maps `Bₓ(x*) := x*(x)` continuous.
2. `Uₓ := Bₓ⁻¹' {r: R| |r| < ε} = {x*| |Bₓ(x*)| < ε}` is an open set in `X*`.
    Since `Bₓ` is also linear, an open interval around `0: R` is an open ball
    around `0: X*`. Furthermore `Uₓ` is convex, therefore for each `x: X` we have
    an open convex set around zero. These sets forms a Neighbourhood (Filter) Basis.
    Therefore `Weak* Topology` is a `LocallyConvexSpace`.

# Evaluation maps are Surjective: ∀v: X* →L[R] R, ∃x: X, Bₓ = v
1. The preimage of an arbitrary `v: X* →L[R] R` for an arbitrary open set around zero
   in `R`, is an open ball in `X*` around zero, let's call it `Uᵥ`.
2. Since `Weak* topology` is `LocallyConvexSpace`, there exists an open convex
   set `Uₓ := ⋂ x ∈ (s : Finset X), {x*| |Bₓ(x*)| < ε } ⊆ Uᵥ`.
4. It is true that `⋂ x ∈ (s: Finset X), ker Bₓ ≤ ker v`, since `Uₓ ⊆ Uᵥ`.
5. By linear algebra results, there exists an arbitrary collection of coefficients `c`,
   such that `v = ∑ x ∈ s, c i • Bₓ`
-/

variable {R : Type*} [NormedField R] [ContinuousConstSMul R R]
variable {V : Type*} [AddCommGroup V] [Module R V]

theorem eval_dualpairing_surjective :
  Function.Surjective (eval (dualPairing R V)) := by
  simp [Function.Surjective]
  intro f
  let U := f ⁻¹' (Metric.ball 0 1)
  have hU: U ∈ nhds (0 : AlgWeakDual R V) := ContinuousAt.preimage_mem_nhds
    f.continuous.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
  have ⟨N, ⟨s, ⟨⟨sv, hs₁⟩, hs₂⟩⟩, hNU⟩ :=
    (LinearMap.hasBasis_weakBilin (dualPairing R V)).mem_iff.mp hU
  simp only [← hs₁, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hs₂
  obtain ⟨r, hr, hN⟩ := hs₂
  let vf: Fin sv.card → StrongDual R (AlgWeakDual R V) :=
    fun i => ((eval (dualPairing R V)) (sv.equivFin.symm i).val)
  have hker: ⨅ i, LinearMap.ker (vf i) ≤ LinearMap.ker f := by
    intro dv hdv
    simp_all only [id_eq, Set.subset_def, Seminorm.mem_ball, sub_zero, Set.mem_preimage,
      Metric.mem_ball, dist_zero_right, mem_iInf, LinearMap.mem_ker, U, vf]
    by_contra! hc
    replace hdv : ∀ v ∈ sv, dv v = 0 := by
      intro v hv
      have ⟨i, hi⟩ := Equiv.surjective sv.equivFin.symm ⟨v, hv⟩
      simpa [hi] using hdv i
    replace hNU := hNU ((1 / f dv) • dv)
      (Seminorm.finset_sup_apply_lt hr (fun v hv => by simp [hdv v hv, hr]))
    simp [hc] at hNU
  have ⟨c, hf⟩ := (mem_span_range_iff_exists_fun R).mp (mem_span_of_iInf_ker_le_ker hker)
  use sv.attach.sum (fun v => c (sv.equivFin v) • v)
  refine ContinuousLinearMap.coe_inj.mp ?_
  simpa [←hf, vf] using Finset.sum_equiv sv.equivFin (fun i ↦ by aesop) (by aesop)


/-- The isomorphism between a vector space V and `ContinuousLinearMap`s
  on the algebraic dual of V. -/
noncomputable def StrongWeakDualEquiv : V ≃ₗ[R] StrongDual R (AlgWeakDual R V) :=
  LinearEquiv.ofBijective (WeakBilin.eval (dualPairing R V))
    (And.intro eval_dualpairing_injective eval_dualpairing_surjective)
