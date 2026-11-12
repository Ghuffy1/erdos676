import Erdos676.SingularCoreAsymptotic
import Erdos676.FloorMertensRatio

open Filter
open scoped Topology

namespace Erdos676

theorem growing_singular_average {η b α ε : ℝ}
    (hη : 0 < η) (hb : (1 / 4 : ℝ) ≤ b) (hb1 : b < 1)
    (hα : 0 < α) (hcut : η * b ≤ α) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      pairMean (powerFloor η x) (singularFactorProduct (x ^ α)) ≤ α / (b * η) + ε := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  obtain ⟨C, hC, hcore⟩ := exists_singular_core_error_bound hb
  have herr := (singularCoreError_tendsto C hb1).comp (cast_powerFloor_tendsto hη)
  have hratio := floor_survival_ratio_limit hη hb0 hα
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlimit : Tendsto (fun x : ℝ =>
      (survivalProduct ((powerFloor η x : ℝ) ^ b) / survivalProduct (x ^ α)) *
        (1 + singularCoreError C b (powerFloor η x))) atTop (nhds (α / (b * η))) := by
    simpa only [add_zero, mul_one, Function.comp_apply] using hratio.mul (hone.add herr)
  have hsmall := (tendsto_order.mp hlimit).2 (α / (b * η) + ε) (by linarith)
  filter_upwards [(powerFloor_tendsto hη).eventually hcore,
    eventually_ge_atTop (1 : ℝ), hsmall] with x hxcore hx hxsmall
  have hcuts := floor_power_cutoff_le hx hη hb0 hcut
  have hext := singular_mean_extension (primesUpToReal ((powerFloor η x : ℝ) ^ b))
    (primesUpToReal (x ^ α)) (primesUpToReal_subset hcuts)
    (fun p hp => ((mem_primesUpToReal (x ^ α) p).mp hp).1) (powerFloor η x)
  change pairMean (powerFloor η x) (singularFactorProduct (x ^ α)) ≤
    singularMajorant (primesUpToReal (x ^ α) \ primesUpToReal ((powerFloor η x : ℝ) ^ b)) *
      pairMean (powerFloor η x) (singularFactorProduct ((powerFloor η x : ℝ) ^ b)) at hext
  rw [singularMajorant_band hcuts] at hext
  have hnonneg : 0 ≤ survivalProduct ((powerFloor η x : ℝ) ^ b) / survivalProduct (x ^ α) :=
    div_nonneg (survivalProduct_pos _).le (survivalProduct_pos _).le
  have hscale := mul_le_mul_of_nonneg_left hxcore hnonneg
  exact (hext.trans hscale).trans hxsmall.le

theorem original_singular_average {α ε : ℝ} (hα : 0 < α) (hsmall : α < 1 / 2)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      pairMean (powerFloor (α * (1 - α ^ 2)) N) (singularFactorProduct ((N : ℝ) ^ α)) ≤
        1 / (1 - α ^ 2) ^ 2 + ε := by
  have hsq : 0 ≤ α ^ 2 := sq_nonneg α
  have hsqsmall : α ^ 2 < 1 / 4 := by nlinarith
  have hb : (1 / 4 : ℝ) ≤ 1 - α ^ 2 := by linarith
  have hb0 : 0 < 1 - α ^ 2 := by linarith
  have hb1 : 1 - α ^ 2 < 1 := by nlinarith
  have hη : 0 < α * (1 - α ^ 2) := mul_pos hα hb0
  have hcut : (α * (1 - α ^ 2)) * (1 - α ^ 2) ≤ α := by
    have hprod := mul_le_mul_of_nonneg_left (show (1 - α ^ 2) ^ 2 ≤ 1 by nlinarith) hα.le
    nlinarith
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (growing_singular_average hη hb hb1 hα hcut hε)
  have heq : α / ((1 - α ^ 2) * (α * (1 - α ^ 2))) = 1 / (1 - α ^ 2) ^ 2 := by
    field_simp
  simpa only [heq] using h

end Erdos676
