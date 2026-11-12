import Erdos676.PowerFloorLog
import Erdos676.MertensRatios

open Filter
open scoped Topology

namespace Erdos676

theorem cast_powerFloor_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => (powerFloor η x : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).comp (powerFloor_tendsto hη)

theorem floor_power_cutoff_le {x η b α : ℝ} (hx : 1 ≤ x) (_hη : 0 < η)
    (hb : 0 < b) (hα : η * b ≤ α) :
    (powerFloor η x : ℝ) ^ b ≤ x ^ α := by
  calc
    _ ≤ (x ^ η) ^ b := Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hx) η)) hb.le
    _ = x ^ (η * b) := (Real.rpow_mul (zero_le_one.trans hx) η b).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx hα

theorem floor_survival_ratio_limit {η b α : ℝ}
    (hη : 0 < η) (hb : 0 < b) (hα : 0 < α) :
    Tendsto (fun x : ℝ => survivalProduct ((powerFloor η x : ℝ) ^ b) /
      survivalProduct (x ^ α)) atTop (nhds (α / (b * η))) := by
  apply survival_ratio_limit ((tendsto_rpow_atTop hb).comp (cast_powerFloor_tendsto hη))
    (tendsto_rpow_atTop hα)
  change Tendsto (fun x : ℝ => Real.log (x ^ α) / Real.log ((powerFloor η x : ℝ) ^ b))
    atTop (nhds (α / (b * η)))
  have hlim : Tendsto (fun x : ℝ => α / (b * (Real.log (powerFloor η x : ℝ) / Real.log x)))
      atTop (nhds (α / (b * η))) :=
    tendsto_const_nhds.div ((log_powerFloor_ratio_tendsto hη).const_mul b) (mul_pos hb hη).ne'
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ), (cast_powerFloor_tendsto hη).eventually_gt_atTop 1]
    with x hx hfloor
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hfloor0 : 0 < (powerFloor η x : ℝ) := lt_trans zero_lt_one hfloor
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlogfloor : Real.log (powerFloor η x : ℝ) ≠ 0 := (Real.log_pos hfloor).ne'
  rw [Real.log_rpow hx0 α, Real.log_rpow hfloor0 b]
  field_simp
  <;> ring

end Erdos676
