import Mathlib.Topology.Algebra.RestrictedProduct.Basic

variable {ι : Type*} [DecidableEq ι]
variable {E : ι → Type*} {R : Type*}
variable (E₀ : (i : ι) → E i)

open RestrictedProduct Function Filter

namespace RestrictedProduct

lemma update_restricted (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) :
    ∀ᶠ (j : ι) in cofinite, update f i v j ∈ (fun i ↦ ({E₀ i} : Set (E i))) j := by
  simp only [Set.mem_singleton_iff, eventually_cofinite]
  apply Set.Finite.subset (s := ({j | f j ≠ E₀ j} ∪ {i}))
  · simpa using f.prop
  · intro j _
    by_cases j = i <;> simp_all



-- def update (f : Πʳ i, [E i, {E₀ i}]) (i : ι) (v : E i) : Πʳ i, [E i, {E₀ i}] :=
--   ⟨Function.update f i v, update_restricted _ _ _ _

--   ⟩


-- Πʳ i, [E i, {E₀ i}]
