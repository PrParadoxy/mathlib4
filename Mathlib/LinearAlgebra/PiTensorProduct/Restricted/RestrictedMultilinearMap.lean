import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

variable {ι : Type*} [DecidableEq ι]
variable {E : ι → Type*} {R : Type*} {E₀ : (i : ι) → E i}

open RestrictedProduct Filter

namespace RestrictedProduct

lemma update_restricted (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) :
    ∀ᶠ (j : ι) in cofinite, Function.update f i v j ∈ (fun i ↦ ({E₀ i} : Set (E i))) j := by
  simp only [Set.mem_singleton_iff, eventually_cofinite]
  apply Set.Finite.subset (s := ({j | f j ≠ E₀ j} ∪ {i}))
  · simpa using f.prop
  · intro j _
    by_cases j = i <;> simp_all

@[simps]
def update (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) : Πʳ i, [E i, {E₀ i}] :=
  ⟨Function.update f i v, update_restricted ..⟩

variable (M : Type*) [AddCommMonoid M] [Semiring R] [Module R M]
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]

structure RestrictedMultilinearMap where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : Πʳ i, [E i, {E₀ i}] → M
  /-- A multilinear map is additive in every argument. -/
  map_update_add' :
    ∀ [DecidableEq ι] (m : Πʳ i, [E i, {E₀ i}]) (i : ι) (x y : E i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A multilinear map is compatible with scalar multiplication in every argument. -/
  map_update_smul' :
    ∀ [DecidableEq ι] (m : Πʳ i, [E i, {E₀ i}]) (i : ι) (c : R) (x : E i),
      toFun (update m i (c • x)) = c • toFun (update m i x)




