module

public import Mathlib.LinearAlgebra.PiTensorProduct.IndexSets

/-!

# Internal notes, and code-that-didn't-make-it.

--/

open PiTensorProduct
open scoped TensorProduct

namespace PiTensorProduct

/-
# Naming conventions

For equivalences, @[simps] defaults to deriving `EQUIV_apply` and `EQUIV_symm_apply`.

See docstring in Mathlib.Tacitcs.Simps.Basic:

  Example: `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
  See `initialize_simps_projections` for more information.

and actual invocation in Mathlib.Logic.Equiv.Defs
-/
-- Used for:
#check isEmptyEquiv_symm_apply
-- The direct function is manually created as
#check isEmptyEquiv_apply_tprod
-- This makes sense, because an auto-generated `isEmptyEquiv_apply` would take
-- general tensors as arguments, not just pure tensors.
--
-- The same convention is used for `singletonEquiv`
--
-- However, for `tmulEquiv` and `tmulEquivDep`, the `_apply` and `_symm_apply`
-- lemmas have no `_tprod` extensions, even though both are restricted to pure tensors.
--
-- Now, `map` doens't use `map_apply_tprod`, but
#check map_tprod
--
-- This seems like a good convention. It doesn't lead to overly long snakes
-- (`someEquiv_symm_apply_tprod`), but still doesn't register a `tprod` lemma
-- with a name (`someEquiv_apply`) that would by general convention be
-- associated with a general argument from the domain.
--
-- Hence, we'll generally use `someHom_tprod`, `someEquiv_tprod`, `someEquiv_symm_tprod`.
--
-- Exception: `subsingletonEquivDep_apply_tprod`, because
-- `subsingletonEquiv_apply_tprod` already existed.

variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]


-- TBD: Why are the signatures so different?
#check LinearEquiv.congrLeft
#check LinearEquiv.congrRight

/-

# Removed code

-/

section subsingletonEquivDep

variable [Subsingleton ι] (i₀ : ι)

/- Any tensor indexed by a unique type is a pure tensor -/
-- lemma subsingletonEquivDep_eq_tprod (z : ⨂[R] i, s i) :
--     z = ⨂ₜ[R] i, (Pi.single i₀ (subsingletonEquivDep i₀ z)) i := by
--   induction z using PiTensorProduct.induction_on
--   all_goals rw [←subsingletonEquivDep_symm_apply, LinearEquiv.symm_apply_apply]

end subsingletonEquivDep

open Set

section tmulUnifyEquiv

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]
-- Too similar to existing
/-- For sets `S ⊆ T`, tensors indexed by `T \ S` times tensors indexed by `S`
are isomorphic to tensors indexed by `T`. -/
def tmulUnify'Equiv : (⨂[R] i₂ : ↥(T \ S), s i₂) ⊗[R] (⨂[R] i₁ : S, s i₁) ≃ₗ[R] ⨂[R] i : T, s i :=
  (TensorProduct.comm ..) ≪≫ₗ (tmulUnifyEquiv hsub)

section LinearMap

open Module

-- TBD: Unify with `map` section of "PiTensorProduct.lean"
-- TBD: And with `TensorProduct.map` section, including notation.
-- TBD: What's up with left / right asymmetry?

variable {M : Type*} [AddCommMonoid M] [Module R M]

def partialContractDiff [(i : ι) → Decidable (i ∈ T \ S)] :
    ((⨂[R] (i₂ : ↑(T \ S)), s i₂) →ₗ[R] R) →ₗ[R] (⨂[R] i : T, s i) →ₗ[R] ⨂[R] (i₂ : S), s i₂ where
  toFun l :=
    have h : T \ (T \ S) = S := Set.diff_diff_cancel_left hsub
    (LinearMap.llcomp R _ _ _
      (PiTensorProduct.reindex R (fun i : ↑(T \ (T \ S)) => s i) (Equiv.setCongr h)).toLinearMap)
      ((PiTensorProduct.partialContract (Set.diff_subset)) l)
  map_add' := by simp
  map_smul' := by simp

omit [(i : ι) → Decidable (i ∈ S)] in
@[simp]
theorem partialContractDiff_tprod [(i : ι) → Decidable (i ∈ T \ S)]
    (l : (⨂[R] i : ↑(T \ S), s i) →ₗ[R] R) (f : (i : T) → s i) :
    partialContractDiff hsub l (⨂ₜ[R] i, f i)
    = (l (⨂ₜ[R] i : ↑(T \ S), f ⟨i, by aesop⟩)) • ⨂ₜ[R] i : S, f ⟨i, by aesop⟩ := by
  simp only [partialContractDiff, Equiv.setCongr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.llcomp_apply, partialContract_tprod, map_smul, LinearEquiv.coe_coe]
  conv => lhs; arg 2; apply reindex_tprod
  simp


end LinearMap

section ExtendTensor

open TensorProduct

variable {s₀ : (i : ι) → s i}
-- Harder to reason about
def extendTensor' (s₀ : (i : ι) → s i) : (⨂[R] (i : S), s i) →ₗ[R] (⨂[R] (i : T), s i) :=
  ((TensorProduct.comm ..) ≪≫ₗ (tmulUnifyEquiv hsub)).toLinearMap ∘ₗ
    (mk _ _ _ (⨂ₜ[R] i : ↥(T \ S), s₀ i))

end ExtendTensor
end tmulUnifyEquiv

section singletonSetEquiv

variable (i₀ : ι)

-- `#lint` complains about this.
@[simp]
theorem singletonEquiv_tprod' (i₀ : ι) (x : s i₀) :
    singletonSetEquiv i₀ (⨂ₜ[R] i : ({i₀} : Set ι), cast (by aesop) x) = x := by simp

@[simp]
theorem singletonEquiv_symm_tprod' (i₀ : ι) (x : s i₀) :
    (singletonSetEquiv i₀).symm x = (⨂ₜ[R] i : ({i₀} : Set ι), cast (by aesop) x) := by
  rw [LinearEquiv.symm_apply_eq, singletonEquiv_tprod, cast_eq]

end singletonSetEquiv

section tmulInsertEquiv

variable {S : Set ι} {i₀} (h₀ : i₀ ∉ S)
variable [DecidableEq ι]

-- Too close to existing
section InsertRight

variable [(i : ι) → Decidable (i ∈ S)]

/-- The tensor product of tensor indexed by `S` and a vector in `s i₀` is equivalent to a
tensor indexed by `S ∪ {i₀}`, assuming `i₀ ∉ S`. -/
def tmulInsertRightEquiv :
    ((⨂[R] i₁ : S, s i₁) ⊗[R] (s i₀)) ≃ₗ[R] ⨂[R] i : ↥(S ∪ {i₀}), s i :=
  (TensorProduct.congr (LinearEquiv.refl _ _) (singletonSetEquiv i₀).symm) ≪≫ₗ
  (tmulUnionEquiv (Set.disjoint_singleton_right.mpr h₀))

@[simp]
theorem tmulInsertRightEquiv_tprod (x : s i₀) (f : (i : S) → s i) :
    (tmulInsertRightEquiv h₀) ((⨂ₜ[R] i, f i) ⊗ₜ[R] x) = ⨂ₜ[R] i : ↥(S ∪ {i₀}),
        if h : ↑i ∈ S then f ⟨i, h⟩ else cast (by aesop) x := by
  simp [tmulInsertRightEquiv]

@[simp]
theorem tmulInsertRightEquiv_symm_tprod (f : (i : ↥(S ∪ {i₀})) → s i) :
    (tmulInsertRightEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (⨂ₜ[R] i : S, f ⟨i, by simp⟩) ⊗ₜ[R] f ⟨i₀, by simp⟩ := by
  simp [tmulInsertRightEquiv]

end InsertRight

end tmulInsertEquiv

/-
↑↑↑ ------ code above this fold is reasonably polished ------- ↑↑↑

------------------~the~watershed~of~polish~-----------------------

↓↓↓ ------ code below this fold is experimental and messy ---- ↓↓↓
-/

open Set

section Fin

open Fin

section TprodTprod

section RecursionHelpers
-- TBD: The following feels like a very basic fact, but I didn't find an easy
-- way to get it from exsiting lemmas. (Maybe some combination
-- of`finSumFinEquiv` and `Equiv.sumSigmaDistrib` would work?)
/-! Split off last summand of a sigma type over `Fin n.succ` -/
def sigmaFinSumLastEquiv {n : Nat} {t : Fin n.succ → Type*} :
  (Σ k : Fin n.succ, t k) ≃ (Σ k : Fin n, t k.castSucc) ⊕ t (last n) := {
    toFun x :=
      if h : x.1 = last n then .inr (h ▸ x.2) else .inl ⟨⟨x.1, lt_last_iff_ne_last.mpr h⟩, x.2⟩
    invFun := Sum.rec (fun x' ↦ ⟨x'.1.castSucc, x'.2⟩) (⟨last n, ·⟩)
    left_inv _ := by aesop
    right_inv _ := by aesop
  }
-- reverse order to be in line with `finSumFinEquiv`?

variable {n : Nat}
variable {Sf : Fin (n + 1) → Type*}
variable {s : (k : Fin (n + 1)) → (i : Sf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- Move one `Fin` index into binary tensor product
protected def tprodTprodLastEquiv : (⨂[R] k : Fin n.succ, ⨂[R] i, s k i) ≃ₗ[R]
    ((⨂[R] k : Fin n, ⨂[R] i, s k.castSucc i) ⊗[R] (⨂[R] i : Sf (last n), s (last n) i)) :=
  (reindex R (fun k : Fin (n+1) ↦ ⨂[R] i : Sf k, s k i) finSumFinEquiv.symm) ≪≫ₗ
  (tmulEquivDep R (fun j ↦ ⨂[R] i : Sf (finSumFinEquiv j), s (finSumFinEquiv j) i)).symm ≪≫ₗ
  (TensorProduct.congr (LinearEquiv.refl R _) (subsingletonEquivDep 0))

protected lemma tprodTprodLastEquiv_tprod (f : (k : Fin n.succ) → (i : Sf k) → s k i) :
    PiTensorProduct.tprodTprodLastEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) =
    (⨂ₜ[R] k : Fin n, ⨂ₜ[R] i, f k.castSucc i) ⊗ₜ[R] (⨂ₜ[R] i, f (last n) i) := by
  simp only [PiTensorProduct.tprodTprodLastEquiv, LinearEquiv.trans_apply, reindex_tprod]
  conv => arg 1; arg 2; apply tmulEquivDep_symm_apply
  rw [TensorProduct.congr_tmul]
  conv => lhs; arg 3; apply subsingletonEquivDep_apply_tprod
  rfl


-- Move one summand from sigma type into binary tensor product

protected def tprodSigmaLastEquiv : (⨂[R] j : (Σ k : Fin n.succ, Sf k), s j.1 j.2) ≃ₗ[R]
  ((⨂[R] j : (Σ k : Fin n, Sf k.castSucc), s j.1.castSucc j.2) ⊗[R]
   (⨂[R] i : Sf (last n), s (last n) i)) :=
  (reindex R (fun j : (Σ k, Sf k) ↦ s j.1 j.2) sigmaFinSumLastEquiv) ≪≫ₗ
  (tmulEquivDep R (fun i ↦ s (sigmaFinSumLastEquiv.symm i).1 (sigmaFinSumLastEquiv.symm i).2)).symm

protected lemma tprodSigmaLastEquiv_tprod (f : (j : Σ k : Fin n.succ, Sf k) → s j.1 j.2) :
    PiTensorProduct.tprodSigmaLastEquiv (⨂ₜ[R] j, f j) =
    ((⨂ₜ[R] j : (Σ k : Fin n, Sf k.castSucc), f ⟨j.1.castSucc, j.2⟩) ⊗ₜ[R]
    (⨂ₜ[R] i, f ⟨(last n), i⟩)) := by
  simp only [PiTensorProduct.tprodSigmaLastEquiv, Nat.succ_eq_add_one,
    LinearEquiv.trans_apply, reindex_tprod]
  apply tmulEquivDep_symm_apply


-- @[simp] -- remove for local lemma?
-- protected lemma tprodSigmaLastEquiv_symm_tprod
--     (lv : (j : Σ k : Fin n, S k.castSucc) → s j.1.castSucc j.2)
--     (rv : (i : S (last n)) → s (last n) i) :
--   (PiTensorProduct.tprodSigmaLastEquiv.symm
--   ((⨂ₜ[R] j : (Σ k : Fin n, S k.castSucc), lv j) ⊗ₜ[R] (⨂ₜ[R] i, rv i))) =
--      (⨂ₜ[R] j : (Σ k : Fin n.succ, S k),
--       if h : j.1 = (last n) then (rv (cast h j.2)) else (lv j.1 j.2))
--     := sorry

end RecursionHelpers

variable {n : Nat}
variable {Tf : Fin n → Type*}
variable {s : (k : Fin n) → (i : Tf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- TBD: Is it desirable to reformulate that as a recursive function?
-- TBD: Use `Fintype`? Could always just use `noncomputable def Finset.equivFin`
/-! A nested `PiTensorProduct` is equivalent to a single `PiTensorProduct` over
a sigma type if the outer type is finite. -/
def trpodFinTprodEquiv :
  (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, Tf k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih => exact PiTensorProduct.tprodTprodLastEquiv ≪≫ₗ
      (TensorProduct.congr ih (LinearEquiv.refl _ _)) ≪≫ₗ PiTensorProduct.tprodSigmaLastEquiv.symm

@[simp]
theorem trpodFinTprodEquiv_tprod (f : (k : Fin n) → (i : Tf k) → s k i) :
    trpodFinTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, Tf k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [trpodFinTprodEquiv, Nat.succ_eq_add_one, Nat.rec_zero, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_eq]
    simp
  | succ m ih =>
    replace ih := @ih (fun i => Tf i.castSucc) (fun i j => s i.castSucc j) _ _
      (fun i j => f i.castSucc j)
    have ht : trpodFinTprodEquiv (R := R) =
      PiTensorProduct.tprodTprodLastEquiv ≪≫ₗ
        (TensorProduct.congr trpodFinTprodEquiv (LinearEquiv.refl _ _))
          ≪≫ₗ (PiTensorProduct.tprodSigmaLastEquiv (s := s)).symm := by rfl
    simp only [ht, LinearEquiv.trans_apply, PiTensorProduct.tprodTprodLastEquiv_tprod,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, ←LinearEquiv.eq_symm_apply,
      LinearEquiv.symm_symm, PiTensorProduct.tprodSigmaLastEquiv_tprod]
    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : Tf (last m), f (last m) i)) ih)

@[simp]
theorem trpodFinTprodEquiv_symm_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    trpodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, Tf k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

-- -- begin ---
section tst

variable {κ : Type*}
variable [DecidableEq κ]
variable {Tf : (k : κ) → Type*}
variable [∀ k : κ, DecidableEq (Tf k)]
variable {s : (k : κ) → (i : Tf k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

-- "All header, no code" (in reference to the American idiom "All hat and no cattle"). :-)
omit [(k : κ) → DecidableEq (Tf k)] in
lemma tprod_update_comm
  [DecidableEq ((k : κ) × Tf k)]
  (f : (i : (k : κ) × Tf k) → s i.fst i.snd)
  (j : (k : κ) × Tf k) (x : s j.1 j.2) :
    (fun k ↦ ⨂ₜ[R] (i : Tf k), (Function.update f j x) ⟨k, i⟩) =
    Function.update (fun k ↦ ⨂ₜ[R] (i : Tf k), f ⟨k, i⟩) j.1
    (⨂ₜ[R] (i : Tf j.1), (Function.update f j x) ⟨j.1, i⟩) := by
  ext k
  by_cases heq : k = j.1
  · aesop
  · simp_all [show ∀ i1 : Tf k, ⟨k, i1⟩ ≠ j from by aesop]

-- generalize this
omit [DecidableEq κ] [(k : κ) → (i : Tf k) → AddCommMonoid (s k i)] in
lemma update_arg
  [DecidableEq ((k : κ) × Tf k)]
  (f : (i : (k : κ) × Tf k) → s i.fst i.snd)
  (j : (k : κ) × Tf k) (x : s j.1 j.2) (x : s j.fst j.snd) :
    (fun i : Tf j.1  => Function.update f j x ⟨j.1, i⟩) =
      Function.update (fun i : Tf j.1 ↦ f ⟨j.1, i⟩) j.2 x := by
    aesop (add safe unfold Function.update)

def tprodTprodHom : (⨂[R] j : (Σ k, Tf k), s j.1 j.2) →ₗ[R] (⨂[R] k, ⨂[R] i, s k i) :=
  lift {
    toFun x := ⨂ₜ[R] k, ⨂ₜ[R] i : Tf k, x ⟨k, i⟩
    map_update_add' := by
      intro _ f j a b
      rw [tprod_update_comm, update_arg (x := a + b)]
      simp only [MultilinearMap.map_update_add]
      apply congrArg₂ HAdd.hAdd
      all_goals
        congr
        ext k
        by_cases h : k = j.fst <;> aesop (add safe forward update_arg)
    map_update_smul' := by
      intro _ f j c x
      rw [tprod_update_comm, update_arg (x := x)]
      simp only [MultilinearMap.map_update_smul]
      congr
      ext k
      by_cases h : k = j.fst <;> aesop (add safe forward update_arg)
    }

def tprodTprod_tprod (f : (j : (Σ k, Tf k)) → s j.1 j.2) :
    tprodTprodHom (⨂ₜ[R] j, f j) = ⨂ₜ[R] k, ⨂ₜ[R] i : Tf k, f ⟨k, i⟩ := by simp [tprodTprodHom]

--- --- Brainstorming section -----
-- TBD: Say something about the span of totally pure tensors.
-- (Which is the entire space assuming `[Fintype κ]`, but not in general)
-- TBD: Convincing pen-and-paper argument that the tensor product of infinitely
-- many non-pure tensors is *not* in that span? It will boil down to some form
-- of "the tensor rank is infinite", but that's not literally true, because in
-- `PiTensorProduct`, we cannot even talk about infinite tensor rank.
variable (R s)
def tprodTprodSpan : Submodule R (⨂[R] k, ⨂[R] i, s k i) := Submodule.span R
    (Set.range fun (f : (k : κ) → (i : Tf k) → s k i) ↦ ⨂ₜ[R] k, ⨂ₜ[R] i : Tf k, f k i)

variable {R s}
def tprodTprodEquiv : (⨂[R] j : (Σ k, Tf k), s j.1 j.2) ≃ₗ[R] tprodTprodSpan R s := sorry

open LinearMap

#check restrict
#check codRestrict
#check rangeRestrict

def myres (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (f : M →ₗ[R] N) : M →ₗ[R] (LinearMap.range f) := rangeRestrict f

theorem tprodTprodHomInjective : Function.Injective (tprodTprodHom (R:=R) (s:=s)) := by
  intros a b h
  sorry
-- maybe construct a left inverse on its range?

--- --- /Brainstorming section ----

variable {M : κ → Type*} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

def unifyMapsSigma (L : (k : κ) → ((⨂[R] i : Tf k, s k i) →ₗ[R] (M k))) :
  (⨂[R] j : (Σ k, Tf k), s j.1 j.2) →ₗ[R] (⨂[R] k, M k) := (map L) ∘ₗ tprodTprodHom

end tst

variable {ι : Type*} {s : ι → Type*} {n : Nat} {Sf : Fin n → Set ι}
  (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
  [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
  [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]

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
  (trpodFinTprodEquiv ≪≫ₗ reindex R _ (iUnionSigmaEquiv H))

@[simp]
theorem tprodFiniUnionEquiv_tprod (f : (k : Fin n) → (i : Sf k) → s i) :
    tprodFiniUnionEquiv H (⨂ₜ[R] k, ⨂ₜ[R] i, f k i)
    = ⨂ₜ[R] i, f ((iUnionSigmaEquiv H).symm i).fst ((iUnionSigmaEquiv H).symm i).snd := by
  simp only [tprodFiniUnionEquiv, LinearEquiv.trans_apply, trpodFinTprodEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tprodFiniUnionEquiv_symm_tprod (f : (i : (Set.iUnion Sf)) → s i) :
    (tprodFiniUnionEquiv H).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] k, ⨂ₜ[R] i : Sf k, f ⟨i, by aesop⟩ := by
  simp [LinearEquiv.symm_apply_eq, iUnionSigmaEquiv]




end TprodTprod
end Fin

section Ring

open Module

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {ι : Type*} {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

/-!
TBD.
-/

theorem extendLinearInjective [∀ U : Set ι, FaithfullyFlat R (⨂[R] i : U, s i)] :
    Function.Injective (extendLinearHom (R:=R) (s:=s) (M:=M) hsub) := by
  apply LinearMap.ker_eq_bot.mp
  simp only [extendLinearHom, LinearEquiv.ker_comp]
  ext f
  simp only [LinearMap.mem_ker, LinearMap.coe_rTensorHom, Submodule.mem_bot]
  symm
  apply Module.FaithfullyFlat.zero_iff_rTensor_zero


section tprodTprodHom

variable {κ : Type*}
variable [DecidableEq κ]
variable {Tf : (k : κ) → Type*}
variable [∀ k : κ, DecidableEq (Tf k)]
variable {s : (k : κ) → (i : Tf k) → Type*}
variable [∀ k, ∀ i, AddCommGroup (s k i)] [∀ k, ∀ i, Module R (s k i)]

variable {M : κ → Type*} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

#check LinearMap.ker_eq_bot
#check LinearMap.injective_domRestrict_iff

-- `LinearMap.ker_eq_bot` requires a `Ring`
-- Lean doesn't really like to talk about injectivity in this semi-ring setup.
-- Hm.
theorem tprodTprodHomInjective' : Function.Injective (tprodTprodHom (R:=R) (s:=s)) := by
  apply LinearMap.ker_eq_bot.mp
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  ·
    simp [tprodTprodHom]
    sorry
  · simp_intro hz

end tprodTprodHom

end Ring

-- Internal test: Does this work for fields?
-- If not, it's currently unclear to me how one would use it.
section Field

open Module

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {ι : Type*} {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

#check (fun U : Set ι => (inferInstance : Flat R (⨂[R] i : U, s i)))

-- #check (fun U : Set ι => (inferInstance : FaithfullyFlat R (⨂[R] i : U, s i)))

end Field


variable {κ : Type*} {Sf : κ → Set ι} [hd : ∀ i, ∀ x, Decidable (x ∈ Sf i)]
variable (H : Pairwise fun k l => Disjoint (Sf k) (Sf l))
variable {M : κ → Type*} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

/-- Given a family `(k : κ) → Sf` of disjoint sets and a family of linear maps
where `L k` is defined on tensors indexed by `Sf k`, construct a linear map
defined on tensors indexed by the union of `Sf`.

Note: `noncomputable` inherited from `unionEqSigmaOfDisjoint`. Could be made
computable by the proof of `unifyMapsSigma`. -/
noncomputable def unifyMaps' [DecidableEq κ] [∀ k : κ, DecidableEq (Sf k)]
    (L : (k : κ) → ((⨂[R] i : Sf k, s i) →ₗ[R] (M k))) :
    (⨂[R] i : iUnion Sf, s i) →ₗ[R] (⨂[R] k, M k) :=
  (unifyMapsSigma L) ∘ₗ ((reindex R _ (Set.unionEqSigmaOfDisjoint H))).toLinearMap


noncomputable def unifMaps_ml' [DecidableEq κ] [∀ k : κ, DecidableEq (Sf k)] :
  MultilinearMap R
       (fun k => (⨂[R] i : Sf k, s i) →ₗ[R] (M k))
       ((⨂[R] i : iUnion Sf, s i) →ₗ[R] (⨂[R] k, M k)) := {
    toFun L := unifyMaps' H L
    map_update_add' := by
      simp [unifyMaps', unifyMapsSigma, PiTensorProduct.map_update_add, LinearMap.add_comp]
    map_update_smul' := by
      simp [unifyMaps', unifyMapsSigma, PiTensorProduct.map_update_smul, LinearMap.smul_comp]
  }

noncomputable def unifMaps_ml'' [DecidableEq κ] [∀ k : κ, DecidableEq (Sf k)] :
  (⨂[R] k, (⨂[R] i : Sf k, s i) →ₗ[R] (M k)) →ₗ[R]
       ((⨂[R] i : iUnion Sf, s i) →ₗ[R] (⨂[R] k, M k)) := lift (unifMaps_ml' H)

end Set

end PiTensorProduct
