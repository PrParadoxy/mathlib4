
open Module


variable {ι : Type*} [Fintype ι] {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

open Finset in
def embedPiDual (dv : (i : ι) → Dual R (s i)) : Dual R (⨂[R] i, s i) :=
 lift (
    { toFun vf := ∏ i: ι, (dv i) (vf i)
      map_update_add' _ i _ _  := by
        simpa [Function.update] using Eq.symm (Finset.prod_add_prod_eq (Finset.mem_univ i) (by simp)
          (by intro _ _ hij; simp [hij]) (by intro _ _ hij; simp [hij]))
      map_update_smul' vf i r vi := by
        have h₁ := prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)
          (fun x => (dv x) (Function.update vf i (r • vi) x))
        have h₂ := prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)
          (fun x => (dv x) (Function.update vf i vi x))
        simp only [h₁, Function.update_self, map_smul, smul_eq_mul, h₂, ← mul_assoc]
        congr! 2
        aesop
    }
  )

@[simp] theorem embedPiDual_apply (dv : (i : ι) → Dual R (s i)) (vf : (i : ι) → s i) :
  embedPiDual dv (⨂ₜ[R] i, vf i) =  ∏ i: ι, (dv i) (vf i) := by simp [embedPiDual]


variable {V : Type*} (R : Type*) [Field R] [AddCommGroup V] [Module R V]
theorem exists_dual_eval_ne_zero
    {v : V} (hv : v ≠ 0) : ∃ φ : Dual R V, φ v ≠ 0 := by
  have := (LinearMap.dualPairing_nondegenerate (K := R) (V₁ := V)).2 v
  simp_all


variable {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]

def marginalize
    (s₀ : (i : ι) → s i) [∀ i, NeZero (s₀ i)] :
    ∃ dt : Dual R (⨂[R] i, s i), dt (⨂ₜ[R] i, s₀ i) ≠ 0 := by
  choose dv hdv using fun i => (exists_dual_eval_ne_zero R (NeZero.ne (s₀ i)))
  use embedPiDual fun i => dv i
  simpa using Finset.prod_ne_zero_iff.mpr fun i _ => hdv i


variable {ι : Type*} [DecidableEq ι] {S T : Finset ι} (hsub : S ≤ T)
variable {s : ι → Type*} {R : Type*}
variable [Field R] [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]
variable (s₀ : (i : ι) → s i)


theorem extendTensor_injective (s₀ : (i : ι) → s i) [∀ i, NeZero (s₀ i)] :
    Function.Injective (extendTensor (R := R) hsub s₀) := by
  intro a b h
  have ⟨dt, hdt⟩ := marginalize (ι := ↑(SetLike.coe T \ S)) R (fun i => s₀ i)
  simp only [SetLike.coe_sort_coe, extendTensor, LinearMap.coe_mk, AddHom.coe_mk,
    EmbeddingLike.apply_eq_iff_eq] at h
  replace h := congrArg (TensorProduct.rid R _) (congrArg (TensorProduct.map LinearMap.id dt) h)
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, TensorProduct.rid_tmul] at h
  exact (smul_right_inj hdt).mp h
