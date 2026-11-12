import Erdos676.PowerCutoffs

open Filter
open scoped Topology

namespace Erdos676

theorem powerFloor_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (powerFloor η) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [(tendsto_rpow_atTop hη).eventually_ge_atTop (n : ℝ)] with x hx
  exact Nat.le_floor hx

theorem log_powerFloor_ratio_bounds {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      η - Real.log 2 / Real.log x ≤ Real.log (powerFloor η x : ℝ) / Real.log x ∧
      Real.log (powerFloor η x : ℝ) / Real.log x ≤ η := by
  filter_upwards [(tendsto_rpow_atTop hη).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with x hp hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hpow0 : 0 < x ^ η := Real.rpow_pos_of_pos hx0 η
  have hhalf := floor_ge_half hp
  have hfloor0 : 0 < (powerFloor η x : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < x ^ η / 2) hhalf
  have hlo := Real.log_le_log (by positivity : 0 < x ^ η / 2) hhalf
  have hhi := Real.log_le_log hfloor0 (Nat.floor_le hpow0.le)
  rw [Real.log_div hpow0.ne' (by norm_num), Real.log_rpow hx0 η] at hlo
  rw [Real.log_rpow hx0 η] at hhi
  constructor
  · apply (le_div_iff₀ (Real.log_pos hx)).mpr
    have heq : (η - Real.log 2 / Real.log x) * Real.log x = η * Real.log x - Real.log 2 := by
      field_simp [(Real.log_pos hx).ne']
      <;> ring
    rwa [heq]
  · exact (div_le_iff₀ (Real.log_pos hx)).mpr hhi

theorem log_powerFloor_ratio_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => Real.log (powerFloor η x : ℝ) / Real.log x) atTop (nhds η) := by
  have hsmall : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hlo : Tendsto (fun x : ℝ => η - Real.log 2 / Real.log x) atTop (nhds η) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    ((log_powerFloor_ratio_bounds hη).mono (fun _ h => h.1))
    ((log_powerFloor_ratio_bounds hη).mono (fun _ h => h.2))

end Erdos676
