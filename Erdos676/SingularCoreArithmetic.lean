import Erdos676.SingularErrorLimits

namespace Erdos676

theorem rpow_div_self {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x ^ r / x = 1 / x ^ (1 - r) := by
  rw [Real.rpow_sub hx 1 r, Real.rpow_one, one_div_div]

theorem first_range_error_bound {x A B : ℝ} (hx : 1 < x)
    (hlogY : 1 ≤ Real.log (logarithmicCutoff x)) (hB0 : 0 ≤ B)
    (hA : A ≤ Real.exp 2 * Real.log x / Real.log (logarithmicCutoff x))
    (hB : B ≤ 2 / logarithmicCutoff x + 1 / x ^ (1 / 2 : ℝ)) :
    4 * A * B ≤ (64 * Real.log 4 * Real.exp 2) / Real.log (logarithmicCutoff x) +
      (4 * Real.exp 2) * (Real.log x / x ^ (1 / 2 : ℝ)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hly : 0 < Real.log (logarithmicCutoff x) := by linarith
  have hupper0 : 0 ≤ Real.exp 2 * Real.log x / Real.log (logarithmicCutoff x) := by positivity
  have hmul := mul_le_mul hA hB hB0 hupper0
  have hscale := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4)
  have hratio : Real.log x / Real.log (logarithmicCutoff x) ≤ Real.log x :=
    div_le_self hlx.le hlogY
  have hterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * Real.exp 2))
    (Real.rpow_nonneg hx0.le (1 / 2 : ℝ))
  calc
    4 * A * B ≤ 4 * (Real.exp 2 * Real.log x / Real.log (logarithmicCutoff x)) *
        (2 / logarithmicCutoff x + 1 / x ^ (1 / 2 : ℝ)) := by nlinarith [hscale]
    _ = (64 * Real.log 4 * Real.exp 2) / Real.log (logarithmicCutoff x) +
        (4 * Real.exp 2) * (Real.log x / Real.log (logarithmicCutoff x)) /
          x ^ (1 / 2 : ℝ) := by
      unfold logarithmicCutoff
      field_simp
      <;> ring
    _ ≤ _ := add_le_add le_rfl (by simpa only [mul_div_assoc] using hterm)

theorem second_range_error_bound {x A B C b : ℝ} (_hx : 0 < x)
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hlog : 0 ≤ Real.log x) (hB0 : 0 ≤ B)
    (hA : A ≤ C * b * Real.log x)
    (hB : B ≤ 2 / x ^ (1 / 4 : ℝ) + 1 / x ^ (1 - b)) :
    4 * A * B ≤ (8 * C * b) * (Real.log x / x ^ (1 / 4 : ℝ)) +
      (4 * C * b) * (Real.log x / x ^ (1 - b)) := by
  have hmul := mul_le_mul hA hB hB0 (mul_nonneg (mul_nonneg hC hb) hlog)
  have hscale := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4)
  convert hscale using 1 <;> ring

end Erdos676
