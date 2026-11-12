import Erdos676.DyadicPrimeBlocks
import Erdos676.BlockParameters

open scoped BigOperators

namespace Erdos676

theorem floor_dyadicCutoff_pos {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    1 ≤ ⌊dyadicCutoff z j⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_dyadicCutoff hz j)

theorem log_floor_dyadicCutoff_le {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    Real.log (⌊dyadicCutoff z j⌋₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j * Real.log z := by
  have hfloor : (0 : ℝ) < ⌊dyadicCutoff z j⌋₊ := by
    exact_mod_cast (by have := floor_dyadicCutoff_pos hz j; omega : 0 < ⌊dyadicCutoff z j⌋₊)
  have hle := Real.log_le_log hfloor (Nat.floor_le (by have := one_le_dyadicCutoff hz j; linarith))
  simpa only [log_dyadicCutoff hz j] using hle

/-- The total CRT error budget for all truncated blocks is independent of the number of blocks. -/
theorem dyadic_error_product_le {z : ℝ} (hz : 1 ≤ z) (L J : ℕ) :
    (∏ j : Fin J, (⌊dyadicCutoff z j.val⌋₊ : ℝ) ^ (4 * (L + j.val))) ≤
      z ^ (8 * L + 8) := by
  have hbasepos (j : Fin J) : (0 : ℝ) < ⌊dyadicCutoff z j.val⌋₊ := by
    exact_mod_cast (by have := floor_dyadicCutoff_pos hz j.val; omega : 0 < ⌊dyadicCutoff z j.val⌋₊)
  have hprodpos : 0 < ∏ j : Fin J, (⌊dyadicCutoff z j.val⌋₊ : ℝ) ^ (4 * (L + j.val)) :=
    Finset.prod_pos (fun j _ => pow_pos (hbasepos j) _)
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hzlog : 0 ≤ Real.log z := Real.log_nonneg hz
  apply (Real.log_le_log_iff hprodpos (pow_pos hzpos _)).mp
  rw [Real.log_prod (fun j _ => ne_of_gt (pow_pos (hbasepos j) _)), Real.log_pow]
  have hbudget : (∑ j : Fin J, (2 * (L + j.val) : ℝ) / 2 ^ j.val) ≤ 4 * L + 4 := by
    simpa only [Finset.sum_range] using block_degree_budget L J
  calc
    _ = ∑ j : Fin J, (4 * (L + j.val) : ℝ) * Real.log (⌊dyadicCutoff z j.val⌋₊ : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow]
      push_cast
      rfl
    _ ≤ ∑ j : Fin J, (4 * (L + j.val) : ℝ) * ((1 / 2 : ℝ) ^ j.val * Real.log z) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (log_floor_dyadicCutoff_le hz j.val) (by positivity)
    _ = 2 * (∑ j : Fin J, (2 * (L + j.val) : ℝ) / 2 ^ j.val) * Real.log z := by
      simp only [Finset.mul_sum, Finset.sum_mul, one_div_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * (4 * L + 4) * Real.log z := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (by norm_num)) hzlog
    _ = (8 * L + 8 : ℕ) * Real.log z := by push_cast; ring

end Erdos676
