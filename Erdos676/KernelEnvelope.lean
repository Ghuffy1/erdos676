import Erdos676.RealCharacters

open scoped BigOperators

namespace Erdos676

theorem kernel_envelope (L t K : ℝ) (hL : 0 < L) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hbase : K ≤ L ^ 2) (htail : K * t ^ 2 ≤ 1) :
    K ≤ 4 * L ^ 2 / (1 + L * t) ^ 2 := by
  have hden : 0 < 1 + L * t := by positivity
  apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
  by_cases hsmall : L * t ≤ 1
  · have hsquare := pow_le_pow_left₀ hden.le (show 1 + L * t ≤ 2 by linarith) 2
    have hscaled := mul_le_mul_of_nonneg_left hsquare hK
    nlinarith
  · have hlarge : 1 ≤ L * t := (lt_of_not_ge hsmall).le
    have hsquare := pow_le_pow_left₀ hden.le (show 1 + L * t ≤ 2 * L * t by linarith) 2
    have hscaled := mul_le_mul_of_nonneg_left hsquare hK
    have hlast := mul_le_mul_of_nonneg_left htail (show 0 ≤ 4 * L ^ 2 by positivity)
    nlinarith

theorem real_pair_kernel_bound (L : ℕ) (hL : 0 < L) (θ : ℝ) (hθ : |θ| ≤ 1 / 2) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, realCharacter θ ((a : ℤ) - b)‖ ≤
      4 * (L : ℝ) ^ 2 / (1 + L * |θ|) ^ 2 := by
  let K := ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, realCharacter θ ((a : ℤ) - b)‖
  have hbase : K ≤ (L : ℝ) ^ 2 := pair_character_sum_norm_le L _ (realCharacter_norm θ)
  have htail : K * |θ| ^ 2 ≤ 1 := by
    by_cases hz : θ = 0
    · simp [hz]
    · have hpos : 0 < |θ| := abs_pos.mpr hz
      have hgap := realCharacter_gap θ hθ
      have hne : realCharacter θ 1 ≠ 1 := by
        intro heq
        rw [heq, sub_self, norm_zero] at hgap
        linarith
      have hsum := character_sum_decay L (realCharacter θ) (realCharacter_norm θ) hne
      have hnorm : 0 < ‖realCharacter θ 1 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hrecip : 2 / ‖realCharacter θ 1 - 1‖ ≤ 1 / |θ| := by
        apply (div_le_div_iff₀ hnorm hpos).mpr
        linarith
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) (hsum.trans hrecip) 2
      have heq : (1 / |θ|) ^ 2 * |θ| ^ 2 = 1 := by field_simp
      have hscaled := mul_le_mul_of_nonneg_right hsquare (sq_nonneg |θ|)
      rw [← pair_character_sum_norm L (realCharacter θ) (realCharacter_norm θ)] at hscaled
      exact hscaled.trans_eq heq
  exact kernel_envelope L |θ| K (by exact_mod_cast hL) (abs_nonneg _) (norm_nonneg _) hbase htail

end Erdos676
