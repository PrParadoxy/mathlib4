import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct


open Module Submodule WeakBilin Topology

/-!
  `Module.WeakDual` requires a topology on the vector space. As this is not available
  in our case, we create similar instances without requiring topology.
-/
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

instance instLocallyConvexSpace {V : Type*} [AddCommGroup V] [Module ℝ V] :
  LocallyConvexSpace ℝ (Dual ℝ V) := WeakBilin.locallyConvexSpace

/-- The closed embedding from dual vectors to plain functions, this is required
    when proving the compactness of a set of dual vectors relies on Tychonoff's theorem. -/
abbrev dualEmbed : Dual R V → (V → R) := DFunLike.coe

theorem dualembed_isclosed_embedding [T2Space R] :
    IsClosedEmbedding (dualEmbed (R := R) (V := V)) :=
  IsClosedEmbedding.mk (DFunLike.coe_injective.isEmbedding_induced)
    (by simp [dualEmbed, LinearMap.isClosed_range_coe])

/-- A set of dual vectors is compact if it is closed,
    and its image under dualEmbed is a subset of a compact set. -/
theorem dualembed_dual_iscompact [T2Space R] {s : Set (Dual R V)} {c : Set (V → R)}
    (hs : IsClosed s) (hc : IsCompact c) (hsc : dualEmbed '' s ⊆ c) : IsCompact s :=
  dualembed_isclosed_embedding.isCompact_iff.mpr
    (IsCompact.of_isClosed_subset hc
      (dualembed_isclosed_embedding.isClosed_iff_image_isClosed.mp hs) hsc)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem exists_dual_vec_ne_zero : ∀ v: V, v ≠ 0 → ∃ dv: Dual ℝ V, dv v ≠ 0 := fun v hv => by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (LinearPMap.mkSpanSingleton (K := ℝ) v (1: ℝ) (hv)).toFun
  use g
  intro hc
  have hp := LinearMap.congr_fun hg ⟨v, mem_span_singleton_self v⟩
  erw [LinearPMap.toFun_eq_coe] at hp
  simp [hc] at hp

theorem WeakBilin.eval_dualpairing_injective : Function.Injective (eval (dualPairing ℝ V)) := by
  intro a b hab
  rw [←sub_eq_zero, ←map_sub ((eval (dualPairing ℝ V)))] at hab
  rw [←sub_eq_zero]
  set c := a - b
  by_contra hc
  obtain ⟨dv, hdv⟩ := exists_dual_vec_ne_zero c hc
  exact hdv (LinearMap.congr_fun (congr_arg (ContinuousLinearMap.toLinearMap) hab) dv)

/-!
# A `Weak* Topology` is a `LocallyConvexSpace`:
1. Weak* topology makes evaluation maps `Bₓ(x*) := x*(x)` continuous.
2. `Uₓ := Bₓ⁻¹' {r: ℝ| |r| < ε} = {x*| |Bₓ(x*)| < ε}` is an open set in `X*`.
    Since `Bₓ` is also linear, an open interval around `0: ℝ` is an open ball
    around `0: X*`. Furthermore `Uₓ` is convex, therefore for each `x: X` we have
    an open convex set around zero. These sets forms a Neighbourhood (Filter) Basis.
    Therefore `Weak* Topology` is a `LocallyConvexSpace`.

# Evaluation maps are Surjective: ∀v: X* →L[ℝ] ℝ, ∃x: X, Bₓ = v
1. The preimage of an arbitrary `v: X* →L[ℝ] ℝ` for an arbitrary open set around zero
   in `ℝ`, is an open ball in `X*` around zero, let's call it `Uᵥ`.
2. Since `Weak* topology` is `LocallyConvexSpace`, there exists an open convex
   set `Uₓ := ⋂ x ∈ (s:Finset X), {x*| |Bₓ(x*)| < ε } ⊆ Uᵥ`.
4. It is true that `⋂ x ∈ (s: Finset X), ker Bₓ ≤ ker v`, since `Uₓ ⊆ Uᵥ`.
5. By linear algebra results, there exists an arbitrary collection of coefficients `c`,
   such that `v = ∑ x ∈ s, c i • Bₓ`
-/
theorem WeakBilin.eval_dualpairing_surjective :
  Function.Surjective (eval (dualPairing ℝ V)) := by
  simp [Function.Surjective, WeakBilin]
  intro f
  let U := f ⁻¹' (Metric.ball 0 1)
  have hU: U ∈ nhds (0 : Module.Dual ℝ V) :=
    ContinuousAt.preimage_mem_nhds f.continuous.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
  obtain ⟨N, ⟨s, ⟨⟨sv, hs₁⟩, hs₂⟩⟩, hNU⟩ :=
    (LinearMap.hasBasis_weakBilin (dualPairing ℝ V)).mem_iff.mp hU
  simp [←hs₁] at hs₂
  obtain ⟨r, hr, hN⟩ := hs₂
  let vf: Fin sv.card → (Dual ℝ V →L[ℝ] ℝ) :=
    fun i => ((eval (dualPairing ℝ V)) (sv.equivFin.symm i).val)
  have hker: ⨅ i, LinearMap.ker (vf i) ≤ LinearMap.ker f := by
    intro dv hdv
    simp [vf, eval] at hdv ⊢
    simp [hN, Set.subset_def, U] at hNU
    by_contra! hc
    replace hdv: ∀v ∈ sv, dv (v) = 0 := by
      intro v hv
      obtain ⟨i, hi⟩: ∃i: Fin sv.card, sv.equivFin.symm i = ⟨v, hv⟩
        := Equiv.surjective sv.equivFin.symm ⟨v, hv⟩
      simpa [hi] using hdv i
    replace hNU := hNU ((1 / f dv) • dv)
      (Seminorm.finset_sup_apply_lt hr (fun v hv => by simp [hdv v hv, hr]))
    simp [hc] at hNU
  obtain ⟨c, hf⟩ := (mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker hker)
  use sv.attach.sum (fun v => c (sv.equivFin v) • v)
  refine ContinuousLinearMap.coe_inj.mp ?_
  simpa [←hf, vf] using Finset.sum_equiv sv.equivFin (fun i ↦ by aesop) (by aesop)

/-- The isomorphism between the vector space and topological dual of the algebraic dual of V.
    Ref: Thm. 1.3 on p. 139 of `Conway, A Course in Functional Analysis`. -/
noncomputable def WeakDualDualEquiv : V ≃ₗ[ℝ] (Dual ℝ V) →L[ℝ] ℝ :=
  LinearEquiv.ofBijective (WeakBilin.eval (dualPairing ℝ V))
    (And.intro eval_dualpairing_injective eval_dualpairing_surjective)

lemma exists_separating_vector
  {s : Set (Dual ℝ V)} {x : Dual ℝ V} (hc : x ∉ topologicalClosure (span ℝ s)) :
    ∃ v, v ≠ 0 ∧ ∃u: ℝ, x v < u ∧ (∀ b ∈ topologicalClosure (span ℝ s), u < b v)  ∧
  ∀ b ∈ topologicalClosure (span ℝ s), b v = 0 := by
  obtain ⟨f, u, hfk, hfs⟩ := geometric_hahn_banach_point_closed
    (topologicalClosure (span ℝ s)).convex (span ℝ s).isClosed_topologicalClosure hc
  have hp: ∀ b ∈ ↑(span ℝ s).topologicalClosure, f b = 0 := by
    by_contra! hb
    obtain ⟨b, hb, hfb⟩ := hb
    simpa [hfb] using hfs ((u / f b) • b) (by apply Submodule.smul_mem; exact hb)
  obtain ⟨v, hvf⟩ := eval_dualpairing_surjective f
  subst hvf
  have hv: v ≠ 0 := fun hv => by
    let b := Classical.arbitrary (span ℝ s).topologicalClosure
    have hcf := hfs b b.prop
    simp [hv] at hcf hfk
    exact lt_asymm hcf hfk
  exact ⟨v, hv, u, hfk, hfs, hp⟩

/-- Generelized version of span_eq_top_of_ne_zero for infinite vector spaces. -/
theorem wclosure_span_eq_top_of_ne_zero {s : Set (Dual ℝ V)} (h : ∀ v ≠ 0, ∃ f ∈ s, f v ≠ 0) :
  topologicalClosure (span ℝ s) = ⊤ := by
  ext x
  simp only [mem_top, iff_true]
  by_contra! hc
  obtain ⟨v, hv, _, _, _, hp⟩ := exists_separating_vector hc
  obtain ⟨b, hb, hvb⟩ := h v hv
  exact hvb (hp b (subset_closure (subset_span hb)))

theorem weak_separating_iff {s : Set (Dual ℝ V)} :
  (∀ v ≠ 0, ∃ f ∈ s, f v ≠ 0) ↔ (topologicalClosure (span ℝ s) = ⊤) := by
  constructor
  · exact wclosure_span_eq_top_of_ne_zero
  · intro h v hv
    by_contra! hc
    replace hc: ∀ f ∈ (span ℝ s).topologicalClosure, f v = 0 := by
      intro f hf
      let p := {f: Dual ℝ V | f v = 0 }
      have hp: IsClosed p := isClosed_eq (dual_eval_continuous v) (by fun_prop)
      have hpspan : ↑(span ℝ s) ⊆ p := by apply span_induction <;> aesop
      exact (closure_minimal hpspan hp) hf
    replace hc: ∀dv: Dual ℝ V, dv v = 0 := by intro dv; exact hc dv (h ▸ mem_top)
    obtain ⟨dv, hdv⟩ := exists_dual_vec_ne_zero v hv
    exact hdv (hc dv)


end Dual




open PiTensorProduct Finset Function
open scoped TensorProduct

variable {ι : Type*} [Fintype ι]
variable {R : Type*} [CommRing R]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

noncomputable section PiTensorProductDual

namespace PiTensorProduct

/-- Embedding of a tensor product to a continuous
  function on Cartasien product of a family of dual vectors -/

def embedVec : (⨂[R] i, V i) →ₗ[R] (((i:ι) → Dual R (V i)) → R) :=
  lift (
    {
      toFun vf dv := ∏ i: ι, (dv i) (vf i)
      map_update_add' _ i _ _  := by
        ext _; simpa [update] using Eq.symm (prod_add_prod_eq (mem_univ i) (by simp)
          (by intro _ _ hij; simp [hij]) (by intro _ _ hij; simp [hij]))
      map_update_smul' vf i r vi := by
          ext dv
          simp only [prod_eq_mul_prod_diff_singleton
            (mem_univ i) (fun x => (dv x) (update vf i (r • vi) x)),
            update_self, map_smul, smul_eq_mul, Pi.smul_apply,
            prod_eq_mul_prod_diff_singleton (mem_univ i) (fun x => (dv x) (update vf i vi x)),
            ← mul_assoc]
          congr! 2 with j hj
          simp [update, show j ≠ i from by simp at hj; exact hj]
    }
  )

@[simp] theorem embedVec_apply (dv : (i : ι) → Dual R (V i)) (vf : (i : ι) → V i) :
  embedVec (⨂ₜ[R] i, vf i) dv = ∏ i : ι, (dv i) (vf i) := by simp [embedVec]

variable [TopologicalSpace R]

instance instTensorTopology : TopologicalSpace (⨂[R] i, V i) :=
  TopologicalSpace.induced (fun x => embedVec x) Pi.topologicalSpace

theorem embedVec_continuous : Continuous (fun (x: ⨂[R] i, V i) dv => embedVec x dv) :=
  continuous_induced_dom

theorem embedVec_eval_continuous (dv : ((i : ι) → Dual R (V i))) :
    Continuous (fun x => embedVec x dv) :=
  continuous_pi_iff.mp continuous_induced_dom dv

end PiTensorProduct

/-- Embedding of a family of dual vectors to a tensor product dual -/
def embedPiDual (dv : (i : ι) → Dual R (V i)) : Dual R (⨂[R] i, V i) :=
 lift (
    { toFun vf := ∏ i: ι, (dv i) (vf i)
      map_update_add' _ i _ _  := by
        simpa [Function.update] using Eq.symm (prod_add_prod_eq (mem_univ i) (by simp)
          (by intro _ _ hij; simp [hij]) (by intro _ _ hij; simp [hij]))
      map_update_smul' vf i r vi := by
        simp only [prod_eq_mul_prod_diff_singleton
            (mem_univ i) (fun x => (dv x) (update vf i (r • vi) x)),
          Function.update_self, map_smul, smul_eq_mul,
          prod_eq_mul_prod_diff_singleton
            (mem_univ i) (fun x => (dv x) (update vf i vi x)), ← mul_assoc]
        congr! 2 with j hj
        simp [Function.update, show j ≠ i from by simp at hj; exact hj]
    }
  )

@[simp] theorem embedPiDual_apply (dv : (i : ι) → Dual R (V i)) (vf : (i : ι) → V i) :
  embedPiDual dv (⨂ₜ[R] i, vf i) =  ∏ i: ι, (dv i) (vf i) := by simp [embedPiDual]

theorem embedPiDual_eq_embedVec {dv : (i : ι) → Dual R (V i)} {v : ⨂[R] i, V i} :
  embedPiDual dv v = embedVec v dv := by
  induction v using PiTensorProduct.induction_on <;> simp_all

@[simp] lemma pidual_prod_update
  [DecidableEq ι] {q} {x} (dv : (i : ι) → Dual R (V i)) (z : (i : ι) → V i) :
  ∏ i, (Function.update dv q x i) (z i) = (x (z q)) * ∏ i ∈ Finset.univ \ {q}, (dv i) (z i) := by
  let f: ι → R := fun i => dv i (z i)
  have hupd: (fun i => (Function.update dv q (x) i) (z i)) =
    Function.update f q ((x) (z q)) := by aesop (add safe unfold Function.update)
  rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ q) (fun i => dv i (z i)) ((x) (z q))]

/-- Embedding tensor product of a family of dual vectors to dual of tensor product. -/
def embedTensorDual : (⨂[R] i, Dual R (V i)) →ₗ[R] Dual R (⨂[R] i, V i) :=
  lift ({
    toFun dv := embedPiDual dv
    map_update_add' dv q x y := by ext z; simp [add_mul]
    map_update_smul' dv q c x := by ext z; simp [mul_assoc]
  })

@[simp] theorem embedTensorDual_apply (dv : (i : ι) → Dual R (V i)) (vf : (i : ι) → V i) :
  embedTensorDual (⨂ₜ[R] i, dv i) (⨂ₜ[R] i, vf i)  = ∏ i: ι, (dv i) (vf i) := by
  simp [embedTensorDual]

lemma embedTensorDual_eq_embedPiDual (dv : (i : ι) → Dual R (V i)) (z : ⨂[R] i, V i) :
  embedPiDual dv z = embedTensorDual (⨂ₜ[R] i, dv i) z := by
  induction z using PiTensorProduct.induction_on <;> simp_all

section instdualTensorTopology

variable [TopologicalSpace R]

instance instdualTensorTopology : TopologicalSpace (⨂[R] i, Dual R (V i)) :=
  TopologicalSpace.induced (fun x => embedTensorDual x) instTopologicalSpace

@[simp] theorem embedTensorDual_continuous : Continuous (embedTensorDual (R := R) (V := V)) :=
  continuous_induced_dom

@[simp] theorem embedTensorDual_continuous_eval (z : ⨂[R] i, V i) :
    Continuous (fun x => embedTensorDual x z) := by
  apply continuous_pi_iff.mp (Continuous.comp' (dual_coefn_continuous) (embedTensorDual_continuous))

end instdualTensorTopology

#check ContinuousLinearMap.toLinearMap
