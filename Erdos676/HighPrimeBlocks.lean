import Erdos676.PrimeBlocks
import Erdos676.DyadicRetention

open scoped BigOperators

namespace Erdos676

noncomputable def highPrimeLevel (j : ℕ) : ℝ := (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j
noncomputable def highPrimeBlockUpper (τ : ℝ) (j : ℕ) : ℝ := (1 - τ) * highPrimeLevel j

theorem highPrimeLevel_pos (j : ℕ) : 0 < highPrimeLevel j := by unfold highPrimeLevel; positivity

theorem highPrimeLevel_zero : highPrimeLevel 0 = 1 / 4 := by simp [highPrimeLevel]

theorem highPrimeLevel_succ (j : ℕ) : highPrimeLevel (j + 1) = highPrimeLevel j / 2 := by
  simp only [highPrimeLevel, pow_succ]
  ring

theorem highPrimeLevel_le_quarter (j : ℕ) : highPrimeLevel j ≤ 1 / 4 := by
  have h : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold highPrimeLevel
  linarith

theorem highPrimeLevel_discrete (j : ℕ) : highPrimeLevel j = discreteCutoff (j + 2) := by
  simp only [highPrimeLevel, discreteCutoff, pow_add]
  norm_num
  ring

theorem highPrimeBlock_bounds {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    0 < highPrimeLevel (j + 1) ∧ highPrimeLevel (j + 1) < highPrimeBlockUpper τ j ∧
      highPrimeBlockUpper τ j < highPrimeLevel j ∧ highPrimeLevel j ≤ 1 / 4 := by
  have hj := highPrimeLevel_pos j
  rw [highPrimeLevel_succ]
  dsimp only [highPrimeBlockUpper]
  refine ⟨by positivity, ?_, ?_, highPrimeLevel_le_quarter j⟩ <;> nlinarith

theorem highPrimeBlock_log_mass {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    Real.log (highPrimeBlockUpper τ j) - Real.log (highPrimeLevel (j + 1)) < Real.log 2 := by
  have hj := highPrimeLevel_pos j
  have hone : 0 < 1 - τ := by linarith
  have hden : highPrimeLevel (j + 1) ≠ 0 := (highPrimeLevel_pos (j + 1)).ne'
  have hnum : highPrimeBlockUpper τ j ≠ 0 := mul_ne_zero hone.ne' hj.ne'
  have hratio : highPrimeBlockUpper τ j / highPrimeLevel (j + 1) = 2 * (1 - τ) := by
    rw [highPrimeLevel_succ]
    unfold highPrimeBlockUpper
    field_simp
  rw [← Real.log_div hnum hden, hratio]
  apply Real.log_lt_log (by positivity)
  linarith

theorem highPrimeGap_log_mass {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1) (j : ℕ) :
    Real.log (highPrimeLevel j) - Real.log (highPrimeBlockUpper τ j) = -Real.log (1 - τ) := by
  rw [highPrimeBlockUpper, Real.log_mul (by positivity : 1 - τ ≠ 0) (highPrimeLevel_pos j).ne']
  ring

theorem highPrimeGap_loss_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) :
    -Real.log (1 - τ) ≤ 2 * τ := by
  have hpos : 0 < 1 - τ := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos zero_lt_one hpos)
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hpos.ne', Real.log_one, zero_sub] at h
  have hdiv : 1 / (1 - τ) ≤ 2 * τ + 1 := by
    apply (div_le_iff₀ hpos).mpr
    have hprod := mul_nonneg hτ0 (show 0 ≤ 1 - 2 * τ by linarith)
    nlinarith
  linarith

theorem exists_small_highPrimeGap (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 2 ∧ (N : ℝ) * (-Real.log (1 - τ)) < ε := by
  let τ := min (1 / 4 : ℝ) (ε / (4 * (N + 1)))
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτq : τ ≤ 1 / 4 := min_le_left _ _
  have hτ : τ < 1 / 2 := by linarith
  have hτe : τ ≤ ε / (4 * (N + 1)) := min_le_right _ _
  have hscaled := (le_div_iff₀ (by positivity : 0 < 4 * ((N : ℝ) + 1))).mp hτe
  have hgap := mul_le_mul_of_nonneg_left (highPrimeGap_loss_le hτ0.le hτ.le) (Nat.cast_nonneg N)
  refine ⟨τ, hτ0, hτ, ?_⟩
  nlinarith

end Erdos676
