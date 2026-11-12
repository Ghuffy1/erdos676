import Erdos676.GrowingDyadic
import Erdos676.SurvivalLower
import Erdos676.AveragedFirstMoment

open Filter
open scoped Topology

namespace Erdos676

theorem smallPrimeCount_first_moment {α C η : ℝ} (L : ℕ)
    (hα : 0 < α) (hL : 1 ≤ L) (hη : 0 < η)
    (hdegree : α * (8 * L + 8 : ℕ) ≤ 1 / 2)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ S : ℕ,
      (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) - η) * N *
          survivalProduct ((N : ℝ) ^ α) ≤ smallPrimeCount ⌊(N : ℝ) ^ α⌋₊ S N := by
  have hcover := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (growing_dyadic_covers hα (by norm_num : (0 : ℝ) < 1 / 4))
  have habsorb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_power_error_absorbed hα (by norm_num : (3 / 4 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 3) hη)
  filter_upwards [hcover, habsorb, eventually_ge_atTop (1 : ℕ)] with N hcov habs hN
  intro S
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 1 ≤ (N : ℝ) ^ α := Real.one_le_rpow hNreal hα.le
  have hfinite := smallPrimeCount_finite_lower ((N : ℝ) ^ α) hz
    (powerFloor (1 / 4) N) L hL hcov C hC hsmall S N
  have herror := growing_first_error_bound (α := α) hNreal (by norm_num : (0 : ℝ) ≤ 1 / 4) (8 * L + 8)
  have hexponent : (1 / 4 : ℝ) + α * (8 * L + 8 : ℕ) ≤ 3 / 4 := by linarith
  have hpower := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
  have herror' : (2 * (powerFloor (1 / 4) N : ℝ) + 1) * ((N : ℝ) ^ α) ^ (8 * L + 8) ≤
      3 * (N : ℝ) ^ (3 / 4 : ℝ) :=
    herror.trans (mul_le_mul_of_nonneg_left hpower (by norm_num))
  have hnegligible := herror'.trans habs
  calc
    _ = (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N * survivalProduct ((N : ℝ) ^ α) -
        η * N * survivalProduct ((N : ℝ) ^ α) := by ring
    _ ≤ (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N * survivalProduct ((N : ℝ) ^ α) -
        (2 * (powerFloor (1 / 4) N : ℝ) + 1) * ((N : ℝ) ^ α) ^ (8 * L + 8) :=
      sub_le_sub_left hnegligible _
    _ ≤ _ := hfinite

theorem smallAverage_first_moment {α C η : ℝ} (L : ℕ)
    (hα : 0 < α) (hL : 1 ≤ L) (hη : 0 < η)
    (hdegree : α * (8 * L + 8 : ℕ) ≤ 1 / 2)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, 0 < H →
      (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) - η) * N *
        survivalProduct ((N : ℝ) ^ α) ≤
          ∑ n ∈ Finset.Ioc N (2 * N), smallAverage ⌊(N : ℝ) ^ α⌋₊ H n := by
  filter_upwards [smallPrimeCount_first_moment L hα hL hη hdegree hC hsmall] with N hN
  intro H hH
  exact smallAverage_dyadic_lower _ H N hH _ hN

end Erdos676
