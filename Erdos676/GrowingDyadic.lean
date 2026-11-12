import Erdos676.PowerCutoffs

open Filter
open scoped Topology

namespace Erdos676

theorem growing_dyadic_covers {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, dyadicCutoff (x ^ α) (powerFloor δ x) < 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / (4 * α) := div_pos hlog2 (by positivity)
  have hlog := eventually_log_le_power hδ hc
  have hfloor := eventually_powerFloor_half hδ
  filter_upwards [hlog, hfloor, eventually_ge_atTop (1 : ℝ)] with x hxlog hxfloor hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hz : 1 ≤ x ^ α := Real.one_le_rpow hx hα.le
  have hnonneg : 0 ≤ α * Real.log x := mul_nonneg hα.le (Real.log_nonneg hx)
  have hden : 0 < (powerFloor δ x : ℝ) + 1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hxlog hα.le
  have hcancel : α * (Real.log 2 / (4 * α)) = Real.log 2 / 4 := by
    field_simp
  have hsmall : α * Real.log x ≤ (Real.log 2 / 4) * x ^ δ := by
    nlinarith [hscaled]
  have hcut : Real.log (dyadicCutoff (x ^ α) (powerFloor δ x)) ≤
      (α * Real.log x) / ((powerFloor δ x : ℝ) + 1) := by
    rw [log_dyadicCutoff hz, Real.log_rpow hxpos α]
    have h := mul_le_mul_of_nonneg_right (half_pow_le_inv_succ (powerFloor δ x)) hnonneg
    convert h using 1 <;> ring
  have hratio : (α * Real.log x) / ((powerFloor δ x : ℝ) + 1) ≤ Real.log 2 / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [hsmall, hxfloor]
  have hstrict : Real.log (dyadicCutoff (x ^ α) (powerFloor δ x)) < Real.log 2 := by
    linarith
  exact (Real.log_lt_log_iff
    (lt_of_lt_of_le zero_lt_one (one_le_dyadicCutoff hz _)) (by norm_num)).mp hstrict

theorem powerFloor_power_le {x : ℝ} (hx : 0 ≤ x) (r : ℝ) (m : ℕ) :
    (powerFloor r x : ℝ) ^ m ≤ x ^ (r * m) := by
  have hfloor : (powerFloor r x : ℝ) ≤ x ^ r := Nat.floor_le (Real.rpow_nonneg hx r)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (powerFloor r x)) hfloor m
  calc
    _ ≤ (x ^ r) ^ m := hpow
    _ = x ^ (r * m) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem growing_first_error_bound {x α δ : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ) (m : ℕ) :
    (2 * (powerFloor δ x : ℝ) + 1) * (x ^ α) ^ m ≤ 3 * x ^ (δ + α * m) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hfloor : (powerFloor δ x : ℝ) ≤ x ^ δ := Nat.floor_le (Real.rpow_nonneg hx0 δ)
  have hone : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ
  have hp : 0 ≤ (x ^ α) ^ m := pow_nonneg (Real.rpow_nonneg hx0 α) m
  have hbound : 2 * (powerFloor δ x : ℝ) + 1 ≤ 3 * x ^ δ := by linarith
  calc
    _ ≤ (3 * x ^ δ) * (x ^ α) ^ m := mul_le_mul_of_nonneg_right hbound hp
    _ = 3 * x ^ (δ + α * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.rpow_add (lt_of_lt_of_le zero_lt_one hx)]
      ring

end Erdos676
