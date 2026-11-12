import Erdos676.BoxSmoothing

open scoped BigOperators ComplexConjugate

namespace Erdos676

theorem character_sum_norm_le (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ n ∈ Finset.range L, χ n‖ ≤ L := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, ‖χ n‖ := norm_sum_le _ _
    _ = _ := by simp only [hχ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem character_sum_decay (L : ℕ) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) :
    ‖∑ n ∈ Finset.range L, χ n‖ ≤ 2 / ‖χ 1 - 1‖ := by
  have hpow (n : ℕ) : χ (n : ℤ) = (χ 1) ^ n := by
    simpa only [nsmul_eq_mul, mul_one] using χ.map_nsmul_eq_pow n (1 : ℤ)
  simp_rw [hpow]
  rw [geom_sum_eq hχ1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖(χ 1) ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hχ, norm_one, one_pow]; norm_num

theorem pair_character_sum (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)) =
      (∑ a ∈ Finset.range L, χ a) * star (∑ b ∈ Finset.range L, χ b) := by
  have hstar : star (∑ b ∈ Finset.range L, χ (b : ℤ)) =
      ∑ b ∈ Finset.range L, star (χ (b : ℤ)) := map_sum (starRingEnd ℂ) _ _
  simp only [AddChar.map_sub_eq_div, div_eq_mul_inv, Complex.inv_eq_conj (hχ _),
    hstar, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [Finset.sum_comm]

theorem pair_character_sum_norm (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)‖ =
      ‖∑ a ∈ Finset.range L, χ a‖ ^ 2 := by
  rw [pair_character_sum L χ hχ, norm_mul, norm_star, pow_two]

theorem pair_character_sum_norm_le (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)‖ ≤ (L : ℝ) ^ 2 := by
  rw [pair_character_sum_norm L χ hχ]
  exact pow_le_pow_left₀ (norm_nonneg _) (character_sum_norm_le L χ hχ) 2

theorem pair_character_sum_decay (L : ℕ) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)‖ ≤
      (2 / ‖χ 1 - 1‖) ^ 2 := by
  rw [pair_character_sum_norm L χ hχ]
  exact pow_le_pow_left₀ (norm_nonneg _) (character_sum_decay L χ hχ hχ1) 2

end Erdos676
