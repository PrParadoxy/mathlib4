import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Analysis.InnerProductSpace.TensorProduct

open PiTensorProduct
open scoped TensorProduct ComplexConjugate

variable {ι : Type*}
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n} {M : Fin n → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, InnerProductSpace 𝕜 (M i)]

instance : InnerProductSpace.Core 𝕜 (⨂[𝕜] i, M i) := by
  induction n with
  | zero => sorry
  | succ n ih => exact {
    inner a b := by
      simp

  }
