import Erdos676.SurvivalLower

open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem eventually_log_pow_le_power (q : ℕ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ q ≤ c * x ^ r := by
  have h : (fun x : ℝ => (Real.log x) ^ q) =o[atTop] (fun x => x ^ r) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (q : ℝ) hr
  filter_upwards [h.bound hc, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog0 : 0 ≤ (Real.log x) ^ q := pow_nonneg (Real.log_pos hx1).le q
  have hpow0 : 0 ≤ x ^ r := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx1) r).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hpow0] using hx

theorem eventually_power_error_absorbed_by_survival_pow (q : ℕ) {α β C η : ℝ}
    (hα : 0 < α) (hβ : β < 1) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, C * x ^ β ≤ η * x * (survivalProduct (x ^ α)) ^ q := by
  obtain ⟨c, hc, hsurvival⟩ := exists_eventual_survival_lower
  have hlog := eventually_log_pow_le_power q (by linarith : 0 < 1 - β)
    (div_pos (mul_pos hη (pow_pos hc q)) (mul_pos hC (pow_pos hα q)))
  have hsurvival' := (tendsto_rpow_atTop hα).eventually hsurvival
  filter_upwards [hlog, hsurvival', eventually_gt_atTop (1 : ℝ)] with x hxlog hxV hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hden0 : 0 < α * Real.log x := mul_pos hα (Real.log_pos hx1)
  have hden : 0 < (α * Real.log x) ^ q := pow_pos hden0 q
  rw [Real.log_rpow hx0 α] at hxV
  have hpower : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx0, show β + (1 - β) = 1 by ring, Real.rpow_one]
  have hcancel : (C * α ^ q) * (η * c ^ q / (C * α ^ q)) = η * c ^ q := by
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hxlog
    (by positivity : 0 ≤ C * α ^ q * x ^ β)
  have hrhs : (C * α ^ q * x ^ β) * (η * c ^ q / (C * α ^ q) * x ^ (1 - β)) =
      η * c ^ q * x := by
    calc
      _ = ((C * α ^ q) * (η * c ^ q / (C * α ^ q))) * (x ^ β * x ^ (1 - β)) := by ring
      _ = _ := by rw [hcancel, hpower]
  rw [hrhs] at hscaled
  have hfirst : C * x ^ β ≤ η * c ^ q * x / (α * Real.log x) ^ q := by
    apply (le_div_iff₀ hden).mpr
    rw [mul_pow]
    nlinarith [hscaled]
  have hVpow := pow_le_pow_left₀ (div_nonneg hc.le hden0.le) hxV q
  calc
    _ ≤ η * c ^ q * x / (α * Real.log x) ^ q := hfirst
    _ = (η * x) * (c / (α * Real.log x)) ^ q := by rw [div_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hVpow (mul_nonneg hη.le hx0.le)

end Erdos676
