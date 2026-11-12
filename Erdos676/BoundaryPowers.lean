import Erdos676.GrowingFourier
import Erdos676.AvoidanceCorrelation

open Filter
open scoped Topology

namespace Erdos676

theorem eventually_box_radius_le {η : ℝ} (hη : η < 1) (J : ℕ) :
    ∀ᶠ x : ℝ in atTop, (J : ℝ) * (powerFloor η x : ℝ) ≤ x := by
  filter_upwards [(tendsto_rpow_atTop (by linarith : 0 < 1 - η)).eventually_ge_atTop (J : ℝ),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hfloor : (powerFloor η x : ℝ) ≤ x ^ η := Nat.floor_le (Real.rpow_nonneg hx0.le η)
  calc
    _ ≤ (J : ℝ) * x ^ η := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg J)
    _ ≤ x ^ (1 - η) * x ^ η := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le η)
    _ = x := by rw [← Real.rpow_add hx0, show 1 - η + η = 1 by ring, Real.rpow_one]

theorem boundary_ratio_bound {x c : ℝ} (hx : 1 ≤ x) (hc : c ≤ 1 / 2) (hlarge : 4 ≤ x ^ c) :
    x / (⌊x ^ c / 2⌋₊ : ℝ) + 2 * x ^ (1 / 2 : ℝ) ≤ 6 * x ^ (1 - c) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hfloor : x ^ c / 4 ≤ (⌊x ^ c / 2⌋₊ : ℝ) := by
    have h := floor_ge_half (show 2 ≤ x ^ c / 2 by linarith)
    nlinarith
  have hden : 0 < x ^ c / 4 := by positivity
  have hdiv := div_le_div_of_nonneg_left hx0.le hden hfloor
  have heq : x / (x ^ c / 4) = 4 * x ^ (1 - c) := by
    rw [Real.rpow_sub hx0, Real.rpow_one]
    ring
  rw [heq] at hdiv
  have hpow := Real.rpow_le_rpow_of_exponent_le hx (show (1 / 2 : ℝ) ≤ 1 - c by linarith)
  linarith

theorem boundary_error_power_bound {x R c η : ℝ} (hx : 1 ≤ x) (hc : c ≤ 1 / 2)
    (hlarge : 4 ≤ x ^ c) (hR : 0 ≤ R) (J : ℕ) (hRupper : R ≤ J * x ^ η) :
    R + 2 * R * (x / (⌊x ^ c / 2⌋₊ : ℝ) + 2 * x ^ (1 / 2 : ℝ)) ≤
      13 * J * x ^ (1 + η - c) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hratio := boundary_ratio_bound hx hc hlarge
  have hp : 1 ≤ x ^ (1 - c) := Real.one_le_rpow hx (by linarith)
  have hterm := mul_le_mul_of_nonneg_left hratio (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hR)
  have hbase := mul_le_mul_of_nonneg_left hp hR
  have hrhs := mul_le_mul_of_nonneg_right hRupper (show 0 ≤ 13 * x ^ (1 - c) by positivity)
  have hprod : x ^ η * x ^ (1 - c) = x ^ (1 + η - c) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [mul_assoc (J : ℝ) (x ^ η) (13 * x ^ (1 - c))] at hrhs
  have hconvert : (J : ℝ) * (x ^ η * (13 * x ^ (1 - c))) = 13 * J * x ^ (1 + η - c) := by
    rw [mul_left_comm (x ^ η) 13, hprod]
    ring
  rw [hconvert] at hrhs
  nlinarith

theorem correlation_sqrt_power_bound {x R ε : ℝ} (hx : 0 < x) (hR : R ≤ x) :
    Real.sqrt ((x + R) * (8200 * x ^ (1 - ε))) ≤ 200 * x ^ (1 - ε / 2) := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right (show x + R ≤ 2 * x by linarith)
    (show 0 ≤ 8200 * x ^ (1 - ε) by positivity)
  have hpow : (x ^ (1 - ε / 2)) ^ 2 = x * x ^ (1 - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num only [Nat.cast_ofNat]
    have heq : (1 - ε / 2) * (2 : ℝ) = 1 + (1 - ε) := by ring
    rw [heq, Real.rpow_add hx, Real.rpow_one]
  rw [mul_pow, hpow]
  nlinarith

end Erdos676
