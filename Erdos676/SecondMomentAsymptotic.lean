import Erdos676.GrowingPairSieve
import Erdos676.SingularFactors
import Erdos676.SurvivalPowers

open Filter
open scoped Topology BigOperators

namespace Erdos676

theorem pairSurvival_average_factorization (z : ℝ) (H : ℕ) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
      pairSurvivalProduct z ((j : ℤ) - i)) / (H : ℝ) ^ 2 =
    (survivalProduct z) ^ 2 *
      ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        singularFactorProduct z ((j : ℤ) - i)) / (H : ℝ) ^ 2) := by
  simp_rw [pairSurvivalProduct_factorization, ← Finset.mul_sum]
  ring

theorem second_moment_bound_of_singular_mean {α ρ K ε : ℝ}
    (hα : 0 < α) (hρ : 0 < ρ) (hsmall : 20 * α ≤ ρ)
    (hρ8 : 8 * ρ < 1) (hε : 0 < ε) (H : ℕ → ℕ)
    (hH : ∀ᶠ N : ℕ in atTop, 0 < H N)
    (hmean : ∀ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.range (H N), ∑ j ∈ Finset.range (H N),
        singularFactorProduct ((N : ℝ) ^ α) ((j : ℤ) - i)) / (H N : ℝ) ^ 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc N (2 * N), (smallAverage ⌊(N : ℝ) ^ α⌋₊ (H N) n) ^ 2) ≤
        ((1 + 160 * (α / ρ) ^ 2) * K + ε) * N *
          (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
  have herr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_power_error_absorbed_by_survival_pow 2 hα hρ8 zero_lt_one hε)
  filter_upwards [smallAverage_second_moment_reduction hα hρ hsmall, hH, hmean, herr]
    with N hred hHN hMN hEN
  have hc : 0 ≤ (1 + 160 * (α / ρ) ^ 2) * (N : ℝ) *
      (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hMN hc
  have h := hred (H N) hHN
  rw [pairSurvival_average_factorization] at h
  have hEN' : (N : ℝ) ^ (8 * ρ) ≤ ε * N * (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
    simpa only [one_mul] using hEN
  nlinarith

end Erdos676
