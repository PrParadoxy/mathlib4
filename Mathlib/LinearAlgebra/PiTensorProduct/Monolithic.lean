import Mathlib.LinearAlgebra.PiTensorProduct.Set

/-!

# Nested PiTensorProducts

For a family `s : (k : κ) → (i : T k) → Type*` of modules, we analyze the type

 `⨂ k : κ, ⨂ i : T i, s k i`

of nested PiTensorProducts, and its relation to "tensors with a double index"
modelled as sigma types:

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

Replace by other construction? Keep here? Mark `protected`? Move to `Equiv.Fin / Equiv.Sum`?
Restructure entirely?
-/

open Fin
open scoped TensorProduct

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

namespace PiTensorProduct

section TprodFinTrodEquiv

variable {n : Nat} {Tf : Fin n → Type*}
variable {R : Type*} {s : (k : Fin n) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

/-- A nested `PiTensorProduct` is equivalent to a single `PiTensorProduct` over
a sigma type, assuming that the outer type is finite. -/
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

-- Proof strategy: Repeatedly move equivalences around to obtain the form
-- `(complicated terms) = aSingleEquiv tprod`, then simp away `aSingleEquiv`.
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

    -- Final reindex & tmulEquivDep
    rw [symm_apply_eq, reindex_tprod, ←eq_symm_apply]
    conv_rhs => apply tmulEquivDep_symm_apply

    -- Initial reindex & tmulEquivDep
    rw [←eq_symm_apply, ←eq_symm_apply]
    conv_lhs => apply reindex_tprod
    rw [←symm_apply_eq]
    conv_lhs => apply tmulEquivDep_symm_apply

    -- Middle congruence & subsingletonEquivDep
    simp only [eq_symm_apply, finSumFinEquiv_apply_left,
      TensorProduct.congr_tmul, subsingletonEquivDep_apply_tprod]

    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i))
      (ih (fun k i ↦ f k.castSucc i)))

@[simp]
theorem tprodFinTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

end TprodFinTrodEquiv

section iUnion
open Set

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
    (⨂[R] k, (⨂[R] i : Sf k, s i)) ≃ₗ[R] (⨂[R] i : (Set.iUnion Sf), s i) :=
  (tprodFinTprodEquiv ≪≫ₗ reindex R _ (iUnionSigmaEquiv H))

@[simp]
theorem tprodFiniUnionEquiv_tprod (f : (k : Fin n) → (i : Sf k) → s i) :
    tprodFiniUnionEquiv H (⨂ₜ[R] k, ⨂ₜ[R] i, f k i)
    = ⨂ₜ[R] i, f ((iUnionSigmaEquiv H).symm i).fst ((iUnionSigmaEquiv H).symm i).snd := by
  simp only [tprodFiniUnionEquiv, LinearEquiv.trans_apply, tprodFinTprodEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tprodFiniUnionEquiv_symm_tprod (f : (i : (Set.iUnion Sf)) → s i) :
    (tprodFiniUnionEquiv H).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] k, ⨂ₜ[R] i : Sf k, f ⟨i, by aesop⟩ := by
  simp [LinearEquiv.symm_apply_eq, iUnionSigmaEquiv]

end iUnion

section tprodFintypeTprodEquiv

variable {ι : Type*} [Fintype ι] {Tf : ι → Type*}
variable {R : Type*} {s : (k : ι) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

noncomputable def tprodFintypeTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  apply reindex _ _ (Fintype.equivFin ι) ≪≫ₗ tprodFinTprodEquiv ≪≫ₗ
    ((PiTensorProduct.congr fun i => LinearEquiv.refl _ _) ≪≫ₗ
      (reindex _ _ (Equiv.sigmaCongrLeft (Fintype.equivFin ι).symm).symm).symm)

@[simp]
theorem tprodFintypeTprodEquiv_tprod (f : (k : ι) → (i : Tf k) → s k i) :
    tprodFintypeTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  simp only [tprodFintypeTprodEquiv, Equiv.symm_symm, LinearEquiv.trans_apply,
    reindex_tprod, LinearEquiv.symm_apply_eq]
  conv_rhs => apply reindex_tprod
  conv_lhs => arg 2; apply tprodFinTprodEquiv_tprod
  apply congr_tprod

@[simp]
theorem tprodFintypeTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFintypeTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

theorem span_tprodFintypeTprod_eq_top :
  (Submodule.span R
    (Set.range
    (fun (f : (k : ι) → (i : Tf k) → s k i) => (⨂ₜ[R] k, ⨂ₜ[R] i, f k i))))
      = (⊤ : Submodule R (⨂[R] k, ⨂[R] i : Tf k, s k i)) := by
  rw [← tprodFintypeTprodEquiv (R := R) (s := s).symm.range,
    LinearMap.range_eq_map, ← span_tprod_eq_top, ← Submodule.span_image]
  congr with f
  simp only [Set.mem_range, LinearEquiv.coe_coe, Set.mem_image, exists_exists_eq_and,
    tprodFintypeTprodEquiv_symm_tprod]
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
  have h := span_tprodFintypeTprod_eq_top (s := s) (R := R) ▸ Submodule.mem_top (x := z)
  let p := fun z =>
    fun (_ : z ∈ Submodule.span R (Set.range
      fun f : (k : ι) → (i : Tf k) → s k i ↦ ⨂ₜ[R] k, ⨂ₜ[R] i, f k i)) =>
        ∀ r : R, motive (r • z)
  suffices hp : p z h by simpa [p] using hp 1
  induction h using Submodule.span_induction with
  | mem x h =>
    intro r
    obtain ⟨y, hy⟩ := Set.mem_range.mp h
    simpa [hy] using smul_tprod_tprod r y
  | smul r _ _ hx =>
    intro r'
    simpa [←smul_assoc] using hx (r' • r)
  | zero => simpa [p] using smul_tprod_tprod 0 0
  | add => simp_all [p]

end tprodFintypeTprodEquiv
end PiTensorProduct
end Fin
