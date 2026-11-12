import Erdos676.MertensBounds
import Erdos676.PrimeSquarePeriod

open Filter Asymptotics
open scoped Topology

namespace Erdos676

noncomputable def logarithmicCutoff (x : ℝ) : ℝ := Real.log x / (8 * Real.log 4)

theorem logarithmicCutoff_tendsto : Tendsto logarithmicCutoff atTop atTop := by
  exact Real.tendsto_log_atTop.atTop_div_const
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

theorem logarithmicCutoff_eventually_le_power {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, logarithmicCutoff x ≤ x ^ b := by
  have h := eventually_log_le_power hb
    (mul_pos (by norm_num : (0 : ℝ) < 8) (Real.log_pos (by norm_num : (1 : ℝ) < 4)))
  filter_upwards [h] with x hx
  exact (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos (by norm_num)))).mpr
    (by simpa only [mul_comm] using hx)

theorem inverse_floor_le_twice_inverse {x : ℝ} (hx : 2 ≤ x) :
    (⌊x⌋₊ : ℝ)⁻¹ ≤ 2 / x := by
  have hx0 : 0 < x := by linarith
  have hfloor := floor_ge_half hx
  have hhalf : 0 < x / 2 := by positivity
  have h := one_div_le_one_div_of_le hhalf hfloor
  simpa only [one_div, inv_div] using h

noncomputable def singularCoreError (C b x : ℝ) : ℝ :=
  x ^ (-(3 / 4 : ℝ)) +
  (64 * Real.log 4 * Real.exp 2) / Real.log (logarithmicCutoff x) +
  (4 * Real.exp 2) * (Real.log x / x ^ (1 / 2 : ℝ)) +
  (8 * C * b) * (Real.log x / x ^ (1 / 4 : ℝ)) +
  (4 * C * b) * (Real.log x / x ^ (1 - b))

theorem singularCoreError_tendsto (C : ℝ) {b : ℝ} (hb : b < 1) :
    Tendsto (singularCoreError C b) atTop (nhds 0) := by
  change Tendsto (fun x => singularCoreError C b x) atTop (nhds 0)
  have hzero := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)
  have hlog := (Real.tendsto_log_atTop.comp logarithmicCutoff_tendsto).inv_tendsto_atTop
  have hhalf := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hquarter := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hlast := (isLittleO_log_rpow_atTop (by linarith : 0 < 1 - b)).tendsto_div_nhds_zero
  have h := (((hzero.add (hlog.const_mul (64 * Real.log 4 * Real.exp 2))).add
    (hhalf.const_mul (4 * Real.exp 2))).add (hquarter.const_mul (8 * C * b))).add
    (hlast.const_mul (4 * C * b))
  simpa only [singularCoreError, div_eq_mul_inv, mul_zero, add_zero,
    Pi.inv_apply, Function.comp_apply] using h

end Erdos676
