import Erdos676.MertensRatios

open Filter
open scoped Topology

namespace Erdos676

theorem survival_power_ratio_limit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => survivalProduct (x ^ a) / survivalProduct (x ^ b))
      atTop (nhds (b / a)) := by
  apply survival_ratio_limit (tendsto_rpow_atTop ha) (tendsto_rpow_atTop hb)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.log_rpow hx0 b, Real.log_rpow hx0 a]
  field_simp

theorem singularMajorant_power_band_limit {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) :
    Tendsto (fun x : ℝ => singularMajorant (primesUpToReal (x ^ b) \ primesUpToReal (x ^ a)))
      atTop (nhds (b / a)) := by
  apply Filter.Tendsto.congr' _ (survival_power_ratio_limit ha hb)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (singularMajorant_band (Real.rpow_le_rpow_of_exponent_le hx hab)).symm

end Erdos676
