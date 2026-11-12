import Erdos676.GrowingSingularAverage
import Erdos676.SecondMomentAsymptotic

open Filter
open scoped Topology BigOperators

namespace Erdos676

theorem original_second_moment {α ρ ε : ℝ} (hα : 0 < α) (hsmall : α < 1 / 2)
    (hρ : 0 < ρ) (hcut : 20 * α ≤ ρ) (hρ8 : 8 * ρ < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc N (2 * N),
        (smallAverage ⌊(N : ℝ) ^ α⌋₊ (powerFloor (α * (1 - α ^ 2)) N) n) ^ 2) ≤
      ((1 + 160 * (α / ρ) ^ 2) * (1 / (1 - α ^ 2) ^ 2 + ε) + ε) * N *
        (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
  have hb : 0 < 1 - α ^ 2 := by nlinarith
  have hη : 0 < α * (1 - α ^ 2) := mul_pos hα hb
  have hH : ∀ᶠ N : ℕ in atTop, 0 < powerFloor (α * (1 - α ^ 2)) N :=
    ((powerFloor_tendsto hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 0
  have hmean := original_singular_average hα hsmall hε
  apply second_moment_bound_of_singular_mean hα hρ hcut hρ8 hε
    (fun N => powerFloor (α * (1 - α ^ 2)) N) hH
  simpa only [pairMean] using hmean

theorem original_second_moment_quadratic {α ε : ℝ} (hα : 0 < α)
    (hsmall : α ≤ 1 / 200) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc N (2 * N),
        (smallAverage ⌊(N : ℝ) ^ α⌋₊ (powerFloor (α * (1 - α ^ 2)) N) n) ^ 2) ≤
      (1 + 40000 * α ^ 2 + ε) * N * (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
  let A := 1 + 160 * (α / (1 / 10 : ℝ)) ^ 2
  let δ := ε / (A + 1)
  have hA : 0 < A + 1 := by dsimp [A]; positivity
  have hδ : 0 < δ := div_pos hε hA
  have hhalf : α < 1 / 2 := by linarith
  have h := original_second_moment hα hhalf (by norm_num : (0 : ℝ) < 1 / 10)
    (by linarith : 20 * α ≤ (1 / 10 : ℝ)) (by norm_num : 8 * (1 / 10 : ℝ) < 1) hδ
  have hb : 0 < 1 - α ^ 2 := by nlinarith
  have hu : 0 ≤ α ^ 2 := sq_nonneg α
  have huupper : α ^ 2 ≤ 1 / 4 := by nlinarith
  have hu2 : (α ^ 2) ^ 2 ≤ (α ^ 2) / 4 := by nlinarith
  have hrecip : 1 / (1 - α ^ 2) ^ 2 ≤ 1 + 4 * α ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    have hu3 : 0 ≤ (α ^ 2) ^ 3 := pow_nonneg hu 3
    nlinarith
  have hAeq : A = 1 + 16000 * α ^ 2 := by dsimp [A]; ring
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hrecipA := mul_le_mul_of_nonneg_left hrecip hA0
  have hcoef : A * (1 / (1 - α ^ 2) ^ 2) ≤ 1 + 40000 * α ^ 2 := by
    rw [hAeq] at hrecipA
    nlinarith
  have hδeq : A * δ + δ = ε := by dsimp [δ]; field_simp
  filter_upwards [h] with N hN
  have hweight : 0 ≤ (N : ℝ) * (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by positivity
  have hcoef' : A * (1 / (1 - α ^ 2) ^ 2 + δ) + δ ≤ 1 + 40000 * α ^ 2 + ε := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hcoef' hweight
  dsimp only [A] at hscaled
  nlinarith

end Erdos676
