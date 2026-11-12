import Erdos676.BonferroniTail
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

namespace Erdos676

theorem sum_nat_div_two_pow (J : ℕ) :
    (∑ j ∈ Finset.range J, (j : ℝ) / 2 ^ j) = 2 - (2 * J + 2) / (2 : ℝ) ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring

theorem sum_nat_div_two_pow_le (J : ℕ) :
    (∑ j ∈ Finset.range J, (j : ℝ) / 2 ^ j) ≤ 2 := by
  rw [sum_nat_div_two_pow]
  have h : 0 ≤ (2 * (J : ℝ) + 2) / (2 : ℝ) ^ J := by positivity
  linarith

theorem block_degree_budget (L J : ℕ) :
    (∑ j ∈ Finset.range J, (2 * (L + j) : ℝ) / 2 ^ j) ≤ 4 * L + 4 := by
  have hgeometric : (∑ j ∈ Finset.range J, (1 : ℝ) / 2 ^ j) ≤ 2 := by
    simpa only [one_div_pow] using sum_geometric_two_le J
  have hweighted := sum_nat_div_two_pow_le J
  have heq : (∑ j ∈ Finset.range J, (2 * (L + j) : ℝ) / 2 ^ j) =
      2 * L * (∑ j ∈ Finset.range J, (1 : ℝ) / 2 ^ j) +
        2 * (∑ j ∈ Finset.range J, (j : ℝ) / 2 ^ j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  have hscale := mul_le_mul_of_nonneg_left hgeometric (by positivity : 0 ≤ 2 * (L : ℝ))
  linarith

theorem block_error_sum (C : ℝ) (L J : ℕ) :
    (∑ j ∈ Finset.range J, Real.exp (4 * C) / (2 : ℝ) ^ (2 * (L + j))) ≤
      2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) := by
  have hsplit (j : ℕ) : Real.exp (4 * C) / (2 : ℝ) ^ (2 * (L + j)) =
      (Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * (1 / 4 : ℝ) ^ j := by
    rw [Nat.mul_add, pow_add]
    have hp : (2 : ℝ) ^ (2 * j) = 4 ^ j := by rw [pow_mul]; norm_num
    rw [hp, one_div_pow]
    ring
  simp only [hsplit, ← Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j) ≤ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        gcongr <;> norm_num
      _ ≤ 2 := sum_geometric_two_le J
  have h := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ Real.exp (4 * C) / (2 : ℝ) ^ (2 * L))
  convert h using 1
  ring

end Erdos676
