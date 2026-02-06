
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))

variable {𝓕 𝓖 : Filter ι}

open RestrictedProduct Filter Set

def update [DecidableEq ι] (hG : 𝓖 ≤ cofinite)
    (f : Πʳ i, [R i, A i]_[𝓖]) (i : ι) (a : R i) : Πʳ i, [R i, A i]_[𝓖] :=
    ⟨Function.update f i a, by
  filter_upwards [le_cofinite_iff_compl_singleton_mem.mp hG i, f.prop] with j hj hA
  simpa [notMem_singleton_iff.mp, (mem_compl_iff _ _).mp hj] using hA⟩
