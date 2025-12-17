import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.LinearAlgebra.PiTensorProduct.Dual


open Module Topology WeakBilin Submodule

variable (R : Type*) [CommSemiring R]
variable (V : Type*) [AddCommMonoid V] [Module R V]

/-- A type synonym for `Dual R W` equipped with the weak topology. -/
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
variable {V : Type*} [AddCommMonoid V] [Module R V]

theorem coe_isclosed_embedding :
    IsClosedEmbedding (DFunLike.coe : AlgWeakDual R V → (V → R)) :=
  IsClosedEmbedding.mk (DFunLike.coe_injective.isEmbedding_induced)
    (LinearMap.isClosed_range_coe _ _ _)

/-- A set of dual vectors is compact if it is closed,
    and its image under `DFunLike.coe` is a subset of a compact set. -/
theorem isCompact_subset_image_coe {s : Set (AlgWeakDual R V)} {c : Set (V → R)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : DFunLike.coe '' s ⊆ c) : IsCompact s :=
  coe_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (coe_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)

variable (R : Type*) [Field R] {V : Type*} [AddCommGroup V] [Module R V] in
theorem exists_dual_vec_ne_zero :
    ∀ v : V, v ≠ 0 → ∃ dv: AlgWeakDual R V, dv v ≠ 0 := fun v hv => by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (LinearPMap.mkSpanSingleton (K := R) v (1: R) (hv)).toFun
  use g
  intro hc
  have hp := LinearMap.congr_fun hg ⟨v, mem_span_singleton_self v⟩
  rw [LinearPMap.toFun_eq_coe] at hp
  simp [hc] at hp

variable {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [TopologicalSpace R] [ContinuousConstSMul R R] [IsTopologicalAddGroup R]

theorem eval_dualpairing_injective : Function.Injective ((eval (dualPairing R V))) := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro v hv
  by_contra! hc
  obtain ⟨dv, hdv⟩ := exists_dual_vec_ne_zero R v hc
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
@[simps! apply]
noncomputable def StrongWeakDualEquiv : V ≃ₗ[R] StrongDual R (AlgWeakDual R V) :=
  LinearEquiv.ofBijective (WeakBilin.eval (dualPairing R V))
    (And.intro eval_dualpairing_injective eval_dualpairing_surjective)

@[simp] lemma StrongWeakDualEquiv_symm_apply
    (v : StrongDual R (AlgWeakDual R V)) (x : AlgWeakDual R V) :
    x (StrongWeakDualEquiv.symm v) = v x := by
  conv_rhs =>
    rw [← LinearEquiv.apply_symm_apply StrongWeakDualEquiv v, StrongWeakDualEquiv_apply]
  rfl

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {s : Set (AlgWeakDual ℝ V)}

lemma exists_separating_vector {dv : AlgWeakDual ℝ V}
    (hc : dv ∉ topologicalClosure (span ℝ s)) :
    ∃ v ≠ 0, dv v < 0 ∧ ∀ dv ∈ topologicalClosure (span ℝ s), dv v = 0 := by
  obtain ⟨v, u, hvk, hvs⟩ := geometric_hahn_banach_point_closed
    (topologicalClosure (span ℝ s)).convex (span ℝ s).isClosed_topologicalClosure hc
  have hp : ∀ b ∈ ↑(span ℝ s).topologicalClosure, v b = 0 := by
    by_contra! hb
    obtain ⟨b, hb, hvb⟩ := hb
    simpa [hvb] using hvs ((u / v b) • b) (by apply Submodule.smul_mem; exact hb)
  have hu : u < 0 := by simpa using hvs 0 (Submodule.zero_mem _)
  have hvz : v ≠ 0 := fun h => by
    rw [h] at hvk
    simp_all [lt_asymm hu]
  exact ⟨StrongWeakDualEquiv.symm v, by simp [hvz],
    by simpa using lt_trans hvk hu, by simpa using hp⟩

/-- Generelized version of span_eq_top_of_ne_zero for infinite vector spaces. -/
theorem wclosure_span_eq_top_of_ne_zero (h : ∀ v ≠ 0, ∃ dv ∈ s, dv v ≠ 0)
    : topologicalClosure (span ℝ s) = ⊤ := by
  apply eq_top_iff'.mpr (fun x => ?_)
  by_contra! hx
  have ⟨v, hv, _, hvs⟩ := exists_separating_vector hx
  obtain ⟨dv, hdvs, hdv⟩ := h v hv
  exact hdv (hvs dv (subset_closure (subset_span hdvs)))

theorem weak_separating_iff :
    (∀ v ≠ 0, ∃ dv ∈ s, dv v ≠ 0) ↔ (topologicalClosure (span ℝ s) = ⊤) := by
  refine ⟨wclosure_span_eq_top_of_ne_zero, ?_⟩
  intro h v hv
  by_contra! hc
  replace hc : ∀ f ∈ (span ℝ s).topologicalClosure, f v = 0 := by
    intro f hf
    let p := { f : AlgWeakDual ℝ V | f v = 0 }
    have hp : IsClosed p := isClosed_eq (eval_continuous (dualPairing ℝ V) v) (by fun_prop)
    have hpspan : ↑(span ℝ s) ⊆ p := by
      apply span_induction
      iterate 2 aesop
      · intro _ _ _ _ hx hy
        simpa [p] using by rw [LinearMap.add_apply, hx, hy, add_zero]
      · intro _ _ _ hx
        simpa [p] using by rw [LinearMap.smul_apply, hx, smul_eq_mul, mul_zero]
    exact (closure_minimal hpspan hp) hf
  replace hc : ∀ dv : AlgWeakDual ℝ V, dv v = 0 := fun dv => hc dv (h ▸ mem_top)
  obtain ⟨dv, hdv⟩ := exists_dual_vec_ne_zero ℝ v hv
  exact hdv (hc dv)

end AlgWeakDual
