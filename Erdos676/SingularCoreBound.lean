import Erdos676.SingularCutoffs
import Erdos676.SingularCoreArithmetic

namespace Erdos676

theorem singular_core_bound (H : ℕ) (C b : ℝ) (hH : 1 < (H : ℝ))
    (hC : 0 ≤ C) (hb : (1 / 4 : ℝ) ≤ b)
    (hy : 2 ≤ logarithmicCutoff H) (hlogy : 1 ≤ Real.log (logarithmicCutoff H))
    (hyquarter : logarithmicCutoff H ≤ (H : ℝ) ^ (1 / 4 : ℝ))
    (hmajor1 : singularMajorant (primesUpToReal ((H : ℝ) ^ (1 / 4 : ℝ)) \
        primesUpToReal (logarithmicCutoff H)) ≤
      Real.exp 2 * Real.log H / Real.log (logarithmicCutoff H))
    (hmajor2 : singularMajorant (primesUpToReal ((H : ℝ) ^ b)) ≤ C * b * Real.log H) :
    pairMean H (singularFactorProduct ((H : ℝ) ^ b)) ≤ 1 + singularCoreError C b H := by
  let x : ℝ := H
  let y : ℝ := logarithmicCutoff x
  have hx : 1 < x := hH
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hHnat : 0 < H := by exact_mod_cast (lt_trans zero_lt_one hH)
  have hq : 2 ≤ x ^ (1 / 4 : ℝ) := hy.trans hyquarter
  have hy1 : (1 : ℝ) ≤ y := by dsimp [y, x]; linarith
  have hfloor : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hy1)
  have horder := Real.rpow_le_rpow_of_exponent_le hx.le hb
  have h := singular_cutoff_mean_bound y (x ^ (1 / 4 : ℝ)) (x ^ b) H hyquarter horder hfloor hHnat
  have hM : (primeSquarePeriod y : ℝ) ≤ x ^ (1 / 4 : ℝ) := logarithmic_primeSquarePeriod_le hx.le
  have hbase : (primeSquarePeriod y : ℝ) / x ≤ x ^ (-(3 / 4 : ℝ)) := by
    have hdiv := div_le_div_of_nonneg_right hM hx0.le
    have heq : x ^ (1 / 4 : ℝ) / x = x ^ (-(3 / 4 : ℝ)) := by
      rw [rpow_div_self hx0, Real.rpow_neg hx0.le]
      norm_num
    rwa [heq] at hdiv
  have hinv0 : (⌊y⌋₊ : ℝ)⁻¹ ≤ 2 / y := inverse_floor_le_twice_inverse hy
  have hinv1 : (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ)⁻¹ ≤ 2 / x ^ (1 / 4 : ℝ) :=
    inverse_floor_le_twice_inverse hq
  have hfloor1 : (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hfloor2 : (⌊x ^ b⌋₊ : ℝ) ≤ x ^ b := Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hproduct : (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) * (primeSquarePeriod y : ℝ) / x ≤
      1 / x ^ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul hfloor1 hM (Nat.cast_nonneg (primeSquarePeriod y))
      (Real.rpow_nonneg hx0.le (1 / 4 : ℝ))
    have hdiv := div_le_div_of_nonneg_right hmul hx0.le
    have heq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) / x = 1 / x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
      rw [rpow_div_self hx0]
      norm_num
    rwa [heq] at hdiv
  have hlast : (⌊x ^ b⌋₊ : ℝ) / x ≤ 1 / x ^ (1 - b) := by
    have hdiv := div_le_div_of_nonneg_right hfloor2 hx0.le
    rwa [rpow_div_self hx0] at hdiv
  have herr1 := first_range_error_bound hx hlogy
    (by positivity : 0 ≤ (⌊y⌋₊ : ℝ)⁻¹ + (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) * (primeSquarePeriod y : ℝ) / x)
    hmajor1 (add_le_add hinv0 hproduct)
  have herr2 := second_range_error_bound hx0 hC (by linarith : 0 ≤ b) (Real.log_pos hx).le
    (by positivity : 0 ≤ (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ)⁻¹ + (⌊x ^ b⌋₊ : ℝ) / x)
    hmajor2 (add_le_add hinv1 hlast)
  change pairMean H (singularFactorProduct (x ^ b)) ≤ 1 + singularCoreError C b x
  unfold singularCoreError
  nlinarith

end Erdos676
