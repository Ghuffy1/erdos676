import Erdos676.GramBound
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Erdos676

theorem complex_gram_row_bound {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset P) (v : P → E) (c : P → ℂ) (C : ℝ)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, ‖⟪v i, v j⟫_ℂ‖) ≤ C) :
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hexpand : ‖∑ i ∈ s, c i • v i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (star (c i) * (c j * ⟪v i, v j⟫_ℂ)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    have hcomplex : ⟪∑ i ∈ s, c i • v i, ∑ i ∈ s, c i • v i⟫_ℂ =
        ∑ i ∈ s, ∑ j ∈ s, star (c i) * (c j * ⟪v i, v j⟫_ℂ) := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [starRingEnd_apply]
      ring
    rw [hcomplex]
    change Complex.reCLM (∑ i ∈ s, ∑ j ∈ s, star (c i) * (c j * ⟪v i, v j⟫_ℂ)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact map_sum Complex.reCLM _ _
  rw [hexpand]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖⟪v i, v j⟫_ℂ‖ * ‖c i‖ * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have h := Complex.re_le_norm (star (c i) * (c j * ⟪v i, v j⟫_ℂ))
      simpa only [norm_mul, norm_star, mul_comm, mul_left_comm, mul_assoc] using h
    _ ≤ _ := symmetric_row_sum_bound s (fun i j => ‖⟪v i, v j⟫_ℂ‖) (fun i => ‖c i‖) C
      (fun _ _ _ _ => norm_nonneg _) (fun i _ j _ => norm_inner_symm _ _) hrow

end Erdos676
