import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic

section nontriviallinormed

variable (𝕜 : Type*)

variable [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 10000 in
set_option Elab.async false in
set_option trace.profiler true in
#synth NormSMulClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
--  8M heartbeats

end nontriviallinormed


section rclike

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 10000 in
set_option Elab.async false in
set_option trace.profiler true in
#synth NormSMulClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
-- 12M heartbeats

end rclike


section rclike

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 10000 in
set_option Elab.async false in
set_option trace.profiler true in
#synth NormSMulClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
-- 8M heartbeats

end rclike
#check  @NormedSpace.toNormSMulClass 
