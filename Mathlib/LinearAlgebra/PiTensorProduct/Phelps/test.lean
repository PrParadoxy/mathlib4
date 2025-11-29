
--# TODO make it shorter
/- This is not true for general sets, consider `S := {1, -1}` and `V := ℝ` then
  for `vc = 0`, mp is true but not the converse. -/
@[simp] theorem ConvexCone.mem_core_iff (C : ConvexCone ℝ V) :
  vc ∈ core C ↔ ∀ v, ∃ ε : ℝ, 0 < ε ∧ vc + ε • v ∈ C ∧ vc - ε • v ∈ C := by
  constructor
  · exact fix_core
  · intro hv v
    have ⟨ε, hε, h₁, h₂⟩ := hv v
    have hε₁ : ε * ε⁻¹ = 1 := by field_simp [hε]
    use ε
    simp only [hε, SetLike.mem_coe, true_and]
    intro δ hδ
    by_cases hδε : δ = ε -- Since ConvexCone is not assumed to be Pointed, this is necessary.
    · aesop
    · by_cases hδ₁ : 0 ≤ δ
      · simp only [abs_eq_self.mpr hδ₁] at hδ
        replace hδ := lt_of_le_of_ne hδ hδε
        convert C.add_mem
          (C.smul_mem (c := (ε - δ) / (2 * ε)) (by field_simp; linarith) h₂)
          (C.smul_mem (c := (ε + δ) / (2 * ε)) (by field_simp; linarith) h₁) using 1
        rw [smul_add, smul_sub, smul_smul, smul_smul, sub_eq_add_neg, add_add_add_comm, ←add_smul]
        congr
        · ring_nf; simp [hε₁]
        · rw [add_comm, ←sub_eq_add_neg, ←sub_smul]
          ring_nf
          field_simp [mul_comm]
      · by_cases hδε₁ : -δ = ε
        · aesop
        · simp [abs_eq_neg_self.mpr (le_of_lt (not_le.mp hδ₁))] at hδ
          replace hδ := lt_of_le_of_ne hδ hδε₁
          convert C.add_mem
            (C.smul_mem (c := (ε - δ) / (2 * ε)) (by field_simp; linarith) h₂)
            (C.smul_mem (c := (ε + δ) / (2 * ε)) (by field_simp; linarith) h₁) using 1
          rw [smul_add, smul_sub, smul_smul, smul_smul, sub_eq_add_neg, add_add_add_comm, ←add_smul]
          congr
          · ring_nf; simp [hε₁]
          · rw [add_comm, ←sub_eq_add_neg, ←sub_smul]
            ring_nf
            field_simp [mul_comm]
