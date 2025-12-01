import Mathlib.LinearAlgebra.PiTensorProduct.Set

/-!

# Nested PiTensorProducts

Let `T : (k : κ) → Type*` be a family of types. Given a "double-indexed family"
`s : (k : κ) → (i : T k) → Type*` of modules, we analyze the type

 `⨂ k : κ, ⨂ i : T i, s k i`

of nested PiTensorProducts. In particular, we relate it to "tensors with a
double index", i.e. `PiTensorProducts` indexed by a sigma type:

 `⨂ j : Σ (k : κ), T k, s j.fst j.snd`.

-/

/-
## RFCs

### Minor equivalences: Yep or nope?

In `tprodFinTprodEquiv`, we combine six equivalences. These requires some
care to unpack in the first `simp` lemma. Alternatively, one could introduce
intermediate equivalences and prove `simp` lemmas for those.

Trade-offs for the alternative approach:
* Pro -- Slightly more transparent proof; More Truths for Mathlib
* Con -- Proliferation of fairly minor equivalences.

What's the preferred way of handling this?

If #2, one could collect equivalences in a PiTensorProduct/Equiv.lean.


### Type equivalence

The equivalence `sigmaFinSuccEquiv` has nothing to do `PiTensorProduct`s. It is
related to `finSumFinEquiv` and `Equiv.sumSigmaDistrib`, but doesn't seem to
follow easily from those.

Replace by other construction? Keep here? Mark `protected`? Add "_aux" to name?
Move to `Equiv.Fin /Equiv.Sum`?  Restructure entirely?
-/

-- -- doesn't really help. :(
--@[simp, grind =]
--theorem Sigma.curry_apply {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}
--    (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) :  Sigma.curry f x y = f ⟨x, y⟩ := by rfl

section Multilinear

variable {κ : Type*}
variable {T : κ → Type*}
variable {s : (k : κ) → (i : T k) → Type*}

variable [DecidableEq κ] [∀ k : κ, DecidableEq (T k)]
 -- TBD: This should follow from `Sigma.instDecidableEqSigma`, but leaving it out creates trouble
 -- In general, I'm confused about these instances here.
-- variable [DecidableEq (Σ k, T k)]
-- # I don't see any issue ? [DecidableEq ((k : κ) × T k)] must be set as an argument to
-- # apply_sigma_curry_update and update_arg so that the [DecidableEq (Σ k, T k)] instance
-- # produced by map_update_add' itself is consumed by these lemmas, not Sigma.instDecidableEqSigma
-- # instance.  I intentionally removed the global instance to illustrate this point.


section Update

open Function


-- This lemma is closely related to `Sigma.curry_update`
omit [(k : κ) → DecidableEq (T k)] in
lemma apply_sigma_curry_update
  [DecidableEq ((k : κ) × T k)] {β : κ → Type*} (m : (i : Σ k, T k) → s i.1 i.2)
    (j : Σ k, T k) (v : s j.1 j.2) (f : (k : κ) → ((i : T k) → (s k i)) → β k) :
    (fun k ↦ f k (Sigma.curry (update m j v) k)) =
    update (fun k ↦ f k (Sigma.curry m k)) j.1
    (f j.1 (fun i : T j.1 ↦ Sigma.curry (update m j v) j.1 i)) := by
  ext k
  by_cases heq : k = j.1
  · aesop
  · unfold Sigma.curry -- Should one add simp lemmas to `Sigma.curry`?
    simp_all [show ∀ i : T k, ⟨k, i⟩ ≠ j from by grind]

-- TBD: Relate.
-- #check Sigma.curry_update
-- theorem Sigma.curry_update' (j : Σ k, T k) (m : (i : Σ k, T k) → s i.1 i.2) (v : s j.1 j.2) :
--     Sigma.curry (Function.update m j v) =
--       Function.update (Sigma.curry m) j.1 (Function.update (Sigma.curry m j.1) j.2 v) := by
--         have apply_sigma_curry_update m j v id
--         sorry

omit [DecidableEq κ] in
lemma update_arg [DecidableEq ((k : κ) × T k)]
  (m : (i : Σ k, T k) → s i.1 i.2) (j : Σ k, T k) (v : s j.1 j.2) (i : T j.1) :
  update m j v ⟨j.1, i⟩ = update (fun i : T j.1 ↦ m ⟨j.1, i⟩) j.2 v i := by grind

end Update

variable {R : Type*} [CommSemiring R]
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

section Multilinear

namespace Multilinear

variable {M : κ → Type*}
variable [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

variable {N : Type*}
variable [AddCommMonoid N] [Module R N]

/-- Composition of multilinear maps.

If `g` is a multilinear map with index type `κ`, and if for every `k : κ`, we
have a multilinear map `f k` with index type `T k`, then
  `m ↦ g (f₁ m_11 m_12 ...) (f₂ m_21 m_22 ...) ...`
is multilinear with index type `(Σ k : κ, T k)`. -/
@[simps]
def compMultilinearMap
    (g : MultilinearMap R M N) (f : (k : κ) → MultilinearMap R (s k) (M k)) :
      MultilinearMap R (fun j : Σ k, T k ↦ s j.fst j.snd) N where
  toFun m := g fun k ↦ f k (Sigma.curry m k)
  map_update_add' := by simp [apply_sigma_curry_update, Sigma.curry, update_arg]
  map_update_smul' := by simp [apply_sigma_curry_update, Sigma.curry, update_arg]

end Multilinear


open Fin Set Submodule
open scoped TensorProduct

namespace PiTensorProduct

section tprodTprodHom

variable {κ : Type*} {R : Type*} {T : (k : κ) → Type*} {s : (k : κ) → (i : T k) → Type*}
  [DecidableEq κ] [CommSemiring R] [∀ k : κ, DecidableEq (T k)]
  [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

def tprodTprodHom : (⨂[R] j : (Σ k, T k), s j.1 j.2) →ₗ[R] (⨂[R] k, ⨂[R] i, s k i) :=
  lift (Multilinear.compMultilinearMap (tprod R) (fun _ ↦ tprod R))

theorem tprodTprod_tprod (f : (j : (Σ k, T k)) → s j.1 j.2) :
    tprodTprodHom (⨂ₜ[R] j, f j) = ⨂ₜ[R] k, ⨂ₜ[R] i : T k, f ⟨k, i⟩ := by
  simp [tprodTprodHom, Multilinear.compMultilinearMap_apply]
  rfl -- needed, because `Sigma.curry` has no simp lemmas and won't unfold.

end tprodTprodHom


section Fin

/-- Split off last summand of a sigma type over `Fin n.succ` -/
def sigmaFinSuccEquiv {n : Nat} {t : Fin n.succ → Type*} :
  (Σ k : Fin n.succ, t k) ≃ (Σ k : Fin n, t k.castSucc) ⊕ t (last n) := {
    toFun x :=
      if h : x.1 = last n then .inr (h ▸ x.2) else .inl ⟨⟨x.1, lt_last_iff_ne_last.mpr h⟩, x.2⟩
    invFun := Sum.rec (fun y ↦ ⟨y.1.castSucc, y.2⟩) (⟨last n, ·⟩)
    left_inv _ := by aesop
    right_inv _ := by aesop
  }


section TprodFinTrodEquiv

variable {n : Nat} {Tf : Fin n → Type*}
variable {R : Type*} {s : (k : Fin n) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

/-- A nested `PiTensorProduct` with outer index of type `Fin n` is equivalent to
a single `PiTensorProduct` over a sigma type. -/
def tprodFinTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih => exact
      -- Write index as sum; split off last summand as binary TP:
      (reindex _ _ finSumFinEquiv.symm) ≪≫ₗ (tmulEquivDep _ _).symm ≪≫ₗ
      -- Use `ih` on lhs; remove outer PiTP on rhs, thereby exposing inner PiTP:
      (TensorProduct.congr ih (subsingletonEquivDep ↑0)) ≪≫ₗ
      -- Convert to single PiTP:
      (tmulEquivDep R (fun j => s (sigmaFinSuccEquiv.symm j).1 (sigmaFinSuccEquiv.symm j).2)) ≪≫ₗ
      (reindex R (fun j => s j.fst j.snd) sigmaFinSuccEquiv).symm

open LinearEquiv in
@[simp]
theorem tprodFinTprodEquiv_tprod (f : (k : Fin n) → (i : Tf k) → s k i) :
    tprodFinTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [tprodFinTprodEquiv, Nat.rec_zero, trans_apply,
      symm_apply_eq, isEmptyEquiv_apply_tprod]
  | succ m ih =>
    simp only [tprodFinTprodEquiv, Equiv.symm_symm, finSumFinEquiv_apply_left, trans_apply]

    -- Strategy: Repeatedly move equivalences around to obtain the form
    -- `(complicated terms) = aSingleEquiv tprod`, then simp away `aSingleEquiv`.
    -- Stat with final reindex & tmulEquivDep:
    rw [symm_apply_eq, reindex_tprod, ←eq_symm_apply]
    conv_rhs => apply tmulEquivDep_symm_apply
    -- Initial reindex & tmulEquivDep:
    rw [←eq_symm_apply, ←eq_symm_apply]
    conv_lhs => apply reindex_tprod
    rw [←symm_apply_eq]
    conv_lhs => apply tmulEquivDep_symm_apply
    -- Middle congruence & subsingletonEquivDep:
    simp only [eq_symm_apply, finSumFinEquiv_apply_left,
      TensorProduct.congr_tmul, subsingletonEquivDep_apply_tprod]

    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i))
      (ih (fun k i ↦ f k.castSucc i)))

@[simp]
theorem tprodFinTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

end TprodFinTrodEquiv


section tprodFiniteTprodEquiv

variable {ι : Type*} [Finite ι] {Tf : ι → Type*}
variable {R : Type*} {s : (k : ι) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

noncomputable def tprodFiniteTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  let e := Classical.choice (Finite.exists_equiv_fin ι).choose_spec
  apply reindex _ _ e ≪≫ₗ tprodFinTprodEquiv ≪≫ₗ
    ((PiTensorProduct.congr fun i => LinearEquiv.refl _ _) ≪≫ₗ
      (reindex _ _ (Equiv.sigmaCongrLeft e.symm).symm).symm)

@[simp]
theorem tprodFiniteTprodEquiv_tprod (f : (k : ι) → (i : Tf k) → s k i) :
    tprodFiniteTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  simp only [tprodFiniteTprodEquiv, Equiv.symm_symm, LinearEquiv.trans_apply,
    reindex_tprod, LinearEquiv.symm_apply_eq]
  conv_rhs => apply reindex_tprod
  conv_lhs => arg 2; apply tprodFinTprodEquiv_tprod
  apply congr_tprod

@[simp]
theorem tprodFiniteTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFiniteTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

theorem span_tprodFiniteTprod_eq_top :
  (span R (range (fun (f : (k : ι) → (i : Tf k) → s k i) => (⨂ₜ[R] k, ⨂ₜ[R] i, f k i))))
    = (⊤ : Submodule R _) := by
  rw [← tprodFiniteTprodEquiv (R := R) (s := s).symm.range,
    LinearMap.range_eq_map, ← span_tprod_eq_top, ← span_image]
  congr with f
  simp only [mem_range, LinearEquiv.coe_coe, mem_image, exists_exists_eq_and,
    tprodFiniteTprodEquiv_symm_tprod]
  constructor
  · intro ⟨y, hy⟩
    rw [←hy]
    use (fun j => y j.1 j.2)
  · intro ⟨y, hy⟩
    rw [←hy]
    use (fun j k => y ⟨j, k⟩)

@[elab_as_elim]
protected theorem nested_induction_on
    {motive : (⨂[R] k, ⨂[R] i, s k i) → Prop}
    (smul_tprod_tprod : ∀ (r : R) (f : ∀ k, ∀ i, s k i), motive (r • ⨂ₜ[R] k, ⨂ₜ[R] i, (f k i)))
    (add : ∀ (x y), motive x → motive y → motive (x + y))
    (z : ⨂[R] k, ⨂[R] i, s k i) : motive z := by
  have h := span_tprodFiniteTprod_eq_top (s := s) (R := R) ▸ mem_top (x := z)
  let p := fun z =>
    fun (_ : z ∈ span R (range
      fun f : (k : ι) → (i : Tf k) → s k i ↦ ⨂ₜ[R] k, ⨂ₜ[R] i, f k i)) =>
        ∀ r : R, motive (r • z)
  suffices hp : p z h by simpa [p] using hp 1
  induction h using span_induction with
  | mem x h =>
    intro r
    obtain ⟨y, hy⟩ := mem_range.mp h
    simpa [hy] using smul_tprod_tprod r y
  | smul r _ _ hx =>
    intro r'
    simpa [←smul_assoc] using hx (r' • r)
  | zero => simpa [p] using smul_tprod_tprod 0 0
  | add => simp_all [p]

end tprodFiniteTprodEquiv



section iUnion

variable {ι : Type*} {s : ι → Type*} {R : Type*} {n : Nat} {Sf : Fin n → Set ι}
  (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
  [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
  [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]

--# TODO: either move it out, or make it a Private def
def iUnionSigmaEquiv : (Σ k, Sf k) ≃ iUnion Sf where
  toFun s := ⟨s.2, by aesop⟩
  invFun s := ⟨(Fin.find (↑s ∈ Sf ·)).get
        (Fin.isSome_find_iff.mpr ⟨_, (mem_iUnion.mp s.prop).choose_spec⟩),
      ⟨s, by simp [Fin.find_spec (↑s ∈ Sf ·)]⟩⟩
  left_inv := by
    simp_intro s
    generalize_proofs _ h
    congr!
    by_contra hc
    exact (H hc).ne_of_mem h s.2.prop rfl
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

def tprodFiniUnionEquiv :
    (⨂[R] k, (⨂[R] i : Sf k, s i)) ≃ₗ[R] (⨂[R] i : (iUnion Sf), s i) :=
  (tprodFinTprodEquiv ≪≫ₗ reindex R _ (iUnionSigmaEquiv H))

@[simp]
theorem tprodFiniUnionEquiv_tprod (f : (k : Fin n) → (i : Sf k) → s i) :
    tprodFiniUnionEquiv H (⨂ₜ[R] k, ⨂ₜ[R] i, f k i)
    = ⨂ₜ[R] i, f ((iUnionSigmaEquiv H).symm i).fst ((iUnionSigmaEquiv H).symm i).snd := by
  simp only [tprodFiniUnionEquiv, LinearEquiv.trans_apply, tprodFinTprodEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tprodFiniUnionEquiv_symm_tprod (f : (i : (iUnion Sf)) → s i) :
    (tprodFiniUnionEquiv H).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] k, ⨂ₜ[R] i : Sf k, f ⟨i, by aesop⟩ := by
  simp [LinearEquiv.symm_apply_eq, iUnionSigmaEquiv]

end iUnion


section unifyMaps

variable {ι : Type*} {κ : Type*} {R : Type*} {s : ι → Type*} {Sf : κ → Set ι} {M : κ → Type*}
variable (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
  [∀ k, AddCommMonoid (M k)] [CommSemiring R] [∀ k, Module R (M k)] [∀ i, AddCommGroup (s i)]
  [∀ i, Module R (s i)] [DecidableEq κ] [(k : κ) → DecidableEq ↑(Sf k)]

noncomputable def unifyMaps :
    (⨂[R] k, (⨂[R] i : Sf k, s i) →ₗ[R] (M k)) →ₗ[R]
      ((⨂[R] i : iUnion Sf, s i) →ₗ[R] (⨂[R] k, M k)) := lift {
    toFun L := ((map L) ∘ₗ tprodTprodHom) ∘ₗ ((reindex R _ (unionEqSigmaOfDisjoint H))).toLinearMap
    map_update_add' := by simp [PiTensorProduct.map_update_add, LinearMap.add_comp]
    map_update_smul' := by simp [PiTensorProduct.map_update_smul, LinearMap.smul_comp]
  }

end unifyMaps
