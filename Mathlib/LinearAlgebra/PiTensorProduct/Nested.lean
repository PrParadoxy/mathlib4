/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/

module

public import Mathlib.LinearAlgebra.PiTensorProduct

/-!

# Nested PiTensorProducts

Let `T : (k : κ) → Type*` be a family of types. We analyze nested tensor products of the form

 `⨂ k : κ, ⨂ i : T k, s k i`.

In particular, we relate them to "tensors with a double index"

 `⨂ j : (Σ k, T k), s j.fst j.snd`.

## Main definitions
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


@[expose] public section

section Sigma

variable {α : Type*} {β : α → Type*}

/-
Implementation note:

This is the analogue of `Function.apply_update` for sigma types.

This could fit to `Data.Sigma`, after `Sigma.curry_update`, and would extend the
parallel treatment of updates / currying for general functions and for functions
of sigma types.
-/
theorem Sigma.apply_update {γ : (a : α) → β a → Type*} [DecidableEq α] [(a : α) → DecidableEq (β a)]
    {δ : α → Type*} (g : (i : Σ a, β a) → γ i.1 i.2) (j : Σ a, β a) (v : γ j.1 j.2)
    (f : (a : α) → ((i : β a) → (γ a i)) → δ a) (a : α) :
    f a (Sigma.curry (Function.update g j v) a) =
    Function.update (fun a ↦ f a (Sigma.curry g a)) j.1
    (f j.1 (fun i : β j.1 ↦ Sigma.curry (Function.update g j v) j.1 i)) a := by
  by_cases a = j.1 <;> aesop (add safe forward Sigma.curry_update)
  -- by_cases h : a = j.1
  -- · subst h
  --   simp
  -- · simp_all [Sigma.curry_update]

end Sigma

section Multilinear

variable {κ : Type*}
variable {T : κ → Type*}
variable {s : (k : κ) → (i : T k) → Type*}

variable {R : Type*} [CommSemiring R]
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

section Multilinear

namespace Multilinear

variable {M : κ → Type*}
variable [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

variable {N : Type*}
variable [AddCommMonoid N] [Module R N]

variable [DecidableEq κ] [∀ k : κ, DecidableEq (T k)]

/-- Composition of multilinear maps.

If `g` is a multilinear map with index type `κ`, and if for every `k : κ`, we
have a multilinear map `f k` with index type `T k`, then
  `m ↦ g (f₁ m_11 m_12 ...) (f₂ m_21 m_22 ...) ...`
is multilinear with index type `(Σ k, T k)`. -/
@[simps]
def compMultilinearMap
    (g : MultilinearMap R M N) (f : (k : κ) → MultilinearMap R (s k) (M k)) :
      MultilinearMap R (fun j : Σ k, T k ↦ s j.fst j.snd) N where
  toFun m := g fun k ↦ f k (Sigma.curry m k)
  map_update_add' := by
    intro hDecEqSigma m j
    rw [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma]
    simp_rw [funext (fun a ↦ Sigma.apply_update m j _ (fun k ↦ f k) a), Sigma.curry_update]
    simp
  map_update_smul' := by
    intro hDecEqSigma m j
    rw [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma]
    simp_rw [funext (fun a ↦ Sigma.apply_update m j _ (fun k ↦ f k) a), Sigma.curry_update]
    simp

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

theorem tprodTprodHom_tprod (f : (j : (Σ k, T k)) → s j.1 j.2) :
    tprodTprodHom (⨂ₜ[R] j, f j) = ⨂ₜ[R] k, ⨂ₜ[R] i : T k, f ⟨k, i⟩ := by
  simp [tprodTprodHom, Multilinear.compMultilinearMap_apply]
  rfl -- needed, because `Sigma.curry` has no simp lemmas and won't unfold.
  -- unfold Sigma.curry; simp only -- this also works.

end tprodTprodHom


section Fin

-- # This should be moved under Equiv.sigmaNatSucc
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
    -- Start with final reindex & tmulEquivDep:
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
    tprodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, Sigma.curry f k i)
    := by simp [LinearEquiv.symm_apply_eq, Sigma.curry]

end TprodFinTrodEquiv


section tprodFiniteTprodEquiv

-- TBD: Settle on `ι` vs `κ` for outer type

variable {ι : Type*} [Finite ι] {Tf : ι → Type*}
variable {R : Type*} {s : (k : ι) → (i : Tf k) → Type*}
  [CommSemiring R] [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

noncomputable def tprodFiniteTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) :=
  let e := Classical.choice (Finite.exists_equiv_fin ι).choose_spec
  let f := (Equiv.sigmaCongrLeft e.symm).symm
  reindex _ _ e ≪≫ₗ tprodFinTprodEquiv ≪≫ₗ (reindex R (fun i ↦ s i.fst i.snd) f).symm

@[simp]
theorem tprodFiniteTprodEquiv_tprod (f : (k : ι) → (i : Tf k) → s k i) :
    tprodFiniteTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.fst j.snd := by
  simp only [tprodFiniteTprodEquiv, Equiv.symm_symm, LinearEquiv.trans_apply,
    reindex_tprod, Equiv.sigmaCongrLeft_apply, tprodFinTprodEquiv_tprod, LinearEquiv.symm_apply_eq]
  conv_rhs => apply reindex_tprod
  congr

@[simp]
theorem tprodFiniteTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodFiniteTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

/-- The totally pure tensors (i.e. products of product tensors) span a nested tensor
product, if the outer index type is finite. -/
theorem span_tprodFiniteTprod_eq_top :
  span R (range fun f : (k : ι) → (i : Tf k) → s k i ↦ ⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⊤ := by
  rw [eq_top_iff, ←tprodFiniteTprodEquiv.symm.range, LinearMap.range_eq_map,
    ←span_tprod_eq_top, ←span_image, LinearEquiv.coe_coe]
  gcongr
  intro f
  simp only [mem_range, mem_image, exists_exists_eq_and, tprodFiniteTprodEquiv_symm_tprod]
  intro ⟨y, hy⟩
  use (fun j k ↦ y ⟨j, k⟩)

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

end Fin

end PiTensorProduct
