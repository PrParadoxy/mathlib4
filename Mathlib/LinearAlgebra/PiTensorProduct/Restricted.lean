import Mathlib.LinearAlgebra.PiTensorProduct.Set
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm



open PiTensorProduct
open scoped TensorProduct

variable {ι : Type*} [DecidableEq ι]
variable {E : ι → Type*} {𝕜 : Type*}
variable [CommSemiring 𝕜] [∀ i, AddCommMonoid (E i)] [∀ i, Module 𝕜 (E i)]
variable (E₀ : (i : ι) → E i)

section FiniteSet

-- If, logically speaking, one should avoid `AlgWeakDual` because of possible instance repetations
-- then one should avoid `FiniteSet`s as evident by its extra redudant instances.
abbrev FiniteSet (ι : Type*) := { S : Set ι // Finite ↑S }

instance : IsDirectedOrder (FiniteSet ι) where
  directed a b := by
    use ⟨a.val ∪ b.val, by aesop (add safe apply Set.Finite.to_subtype)⟩
    aesop

instance : Nonempty (FiniteSet ι) := ⟨∅, Finite.of_subsingleton⟩

noncomputable instance decidable : ∀ s : FiniteSet ι, ∀ m : ι, Decidable (m ∈ s.val) :=
  fun s m =>
    haveI : Fintype s.val := @Fintype.ofFinite s.val s.prop
    Set.decidableMemOfFintype s.val m

end FiniteSet


instance directedSystem : DirectedSystem
    (fun S : FiniteSet ι ↦ ⨂[𝕜] (i : S.val), E i)
    (fun _ _ hsub ↦ extendTensor hsub E₀) where
  map_self := by simp
  map_map := by
    intro U T S h1 h2 f
    rw [←Function.comp_apply (f := extendTensor h2 E₀)]
    apply congrFun
    simp [←LinearMap.coe_comp]
