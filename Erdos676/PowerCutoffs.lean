import Erdos676.DyadicErrorBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Asymptotics
open scoped Topology

namespace Erdos676

noncomputable def powerFloor (r x : ℝ) : ℕ := ⌊x ^ r⌋₊

theorem floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

theorem log_floor_ge_half_log {x : ℝ} (hx : 4 ≤ x) :
    Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hhalf := floor_ge_half (by linarith : 2 ≤ x)
  have hfloorpos : (0 : ℝ) < ⌊x⌋₊ := lt_of_lt_of_le (by positivity : 0 < x / 2) hhalf
  have hlog := Real.log_le_log (by positivity : 0 < x / 2) hhalf
  rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  have hfour : Real.log (4 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlogfour] at hfour
  linarith

theorem half_pow_le_inv_succ (j : ℕ) :
    (1 / 2 : ℝ) ^ j ≤ 1 / ((j : ℝ) + 1) := by
  have hj : j + 1 ≤ 2 ^ j := j.lt_two_pow_self
  have hj' : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by exact_mod_cast hj
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hj'

theorem eventually_log_le_power {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hnorm : Real.log x ≤ ‖Real.log x‖ := le_abs_self _
  have hpow : ‖x ^ r‖ = x ^ r := Real.norm_of_nonneg (Real.rpow_pos_of_pos hxpos r).le
  exact hnorm.trans (by simpa only [hpow] using hx)

theorem eventually_powerFloor_half {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, x ^ r / 2 ≤ (powerFloor r x : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop hr).eventually_ge_atTop 2] with x hx
  exact floor_ge_half hx

theorem eventually_log_powerFloor_lower {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, (r / 2) * Real.log x ≤ Real.log (powerFloor r x : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop hr).eventually_ge_atTop 4,
    eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have h := log_floor_ge_half_log hx
  rw [Real.log_rpow hxpos r] at h
  simpa only [powerFloor, div_mul_eq_mul_div] using h

end Erdos676
