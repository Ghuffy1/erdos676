import Erdos676.SingularCoreBound

open Filter
open scoped Topology

namespace Erdos676

theorem exists_singular_core_error_bound {b : ℝ} (hb : (1 / 4 : ℝ) ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop,
      pairMean H (singularFactorProduct ((H : ℝ) ^ b)) ≤ 1 + singularCoreError C b H := by
  obtain ⟨T₁, hT₁, hratio⟩ := exists_survival_ratio_log_bound
  obtain ⟨C, T₂, hC, hT₂, hmajor⟩ := exists_singularMajorant_log_bound
  refine ⟨C, hC, ?_⟩
  have hevent : ∀ᶠ x : ℝ in atTop, 1 < x ∧ 2 ≤ logarithmicCutoff x ∧
      Real.exp 1 ≤ logarithmicCutoff x ∧ T₁ ≤ logarithmicCutoff x ∧
      T₂ ≤ logarithmicCutoff x ∧ logarithmicCutoff x ≤ x ^ (1 / 4 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), logarithmicCutoff_tendsto.eventually_ge_atTop 2,
      logarithmicCutoff_tendsto.eventually_ge_atTop (Real.exp 1),
      logarithmicCutoff_tendsto.eventually_ge_atTop T₁,
      logarithmicCutoff_tendsto.eventually_ge_atTop T₂,
      logarithmicCutoff_eventually_le_power (by norm_num : (0 : ℝ) < 1 / 4)]
      with x hx hy hexp h₁ h₂ hpower
    exact ⟨hx, hy, hexp, h₁, h₂, hpower⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hevent] with H hH
  obtain ⟨hx, hy, hexp, h₁, h₂, hpower⟩ := hH
  have hx0 : 0 < (H : ℝ) := lt_trans zero_lt_one hx
  have hlogy : 1 ≤ Real.log (logarithmicCutoff H) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have horder : (H : ℝ) ^ (1 / 4 : ℝ) ≤ (H : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hx.le hb
  have hmajor1 : singularMajorant (primesUpToReal ((H : ℝ) ^ (1 / 4 : ℝ)) \
      primesUpToReal (logarithmicCutoff H)) ≤
      Real.exp 2 * Real.log H / Real.log (logarithmicCutoff H) := by
    rw [singularMajorant_band hpower]
    have hfirst := hratio (logarithmicCutoff H) ((H : ℝ) ^ (1 / 4 : ℝ)) h₁ (h₁.trans hpower)
    have hlogpower : Real.log ((H : ℝ) ^ (1 / 4 : ℝ)) ≤ Real.log H := by
      rw [Real.log_rpow hx0]
      nlinarith [Real.log_pos hx]
    have hsecond := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hlogpower (by linarith : 0 ≤ Real.log (logarithmicCutoff H)))
      (Real.exp_pos 2).le
    exact hfirst.trans (by simpa only [mul_div_assoc] using hsecond)
  have hmajor2 : singularMajorant (primesUpToReal ((H : ℝ) ^ b)) ≤ C * b * Real.log H := by
    have h := hmajor ((H : ℝ) ^ b) (h₂.trans (hpower.trans horder))
    rw [Real.log_rpow hx0] at h
    simpa only [mul_assoc] using h
  exact singular_core_bound H C b hx hC.le hb hy hlogy hpower hmajor1 hmajor2

theorem singular_core_average_eventually {b ε : ℝ} (hb : (1 / 4 : ℝ) ≤ b)
    (hb1 : b < 1) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop,
      pairMean H (singularFactorProduct ((H : ℝ) ^ b)) ≤ 1 + ε := by
  obtain ⟨C, hC, hbound⟩ := exists_singular_core_error_bound hb
  have hlimit := (singularCoreError_tendsto C hb1).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herr : ∀ᶠ H : ℕ in atTop, singularCoreError C b H < ε :=
    (tendsto_order.mp hlimit).2 ε hε
  filter_upwards [hbound, herr] with H hH hE
  linarith

end Erdos676
