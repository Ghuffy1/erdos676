import Erdos676.PrimeBlocks
import Mathlib.NumberTheory.Chebyshev

open scoped BigOperators

namespace Erdos676

noncomputable def primeSquarePeriod (y : ℝ) : ℕ :=
  ∏ p ∈ primesUpToReal y, p ^ 2

theorem primeSquarePeriod_pos (y : ℝ) : 0 < primeSquarePeriod y := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos ((mem_primesUpToReal y p).mp hp).1.pos 2

theorem log_primeSquarePeriod (y : ℝ) :
    Real.log (primeSquarePeriod y : ℝ) = 2 * Chebyshev.theta y := by
  unfold primeSquarePeriod
  rw [Nat.cast_prod, Real.log_prod]
  · simp_rw [Nat.cast_pow, Real.log_pow]
    change (∑ p ∈ primesUpToReal y, (2 : ℝ) * Real.log p) =
      2 * ∑ p ∈ primesUpToReal y, Real.log p
    rw [Finset.mul_sum]
  · intro p hp
    exact_mod_cast (pow_ne_zero 2 ((mem_primesUpToReal y p).mp hp).1.ne_zero)

theorem primeSquarePeriod_le_exp {y : ℝ} (hy : 0 ≤ y) :
    (primeSquarePeriod y : ℝ) ≤ Real.exp (2 * Real.log 4 * y) := by
  have hp : 0 < (primeSquarePeriod y : ℝ) := by exact_mod_cast primeSquarePeriod_pos y
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  rw [log_primeSquarePeriod]
  nlinarith [Chebyshev.theta_le_log4_mul_x hy]

theorem logarithmic_primeSquarePeriod_le {H : ℝ} (hH : 1 ≤ H) :
    (primeSquarePeriod (Real.log H / (8 * Real.log 4)) : ℝ) ≤ H ^ (1 / 4 : ℝ) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hbound := primeSquarePeriod_le_exp
    (div_nonneg (Real.log_nonneg hH) (by positivity : 0 ≤ 8 * Real.log 4))
  have heq : 2 * Real.log 4 * (Real.log H / (8 * Real.log 4)) = Real.log H * (1 / 4) := by
    field_simp
    ring
  rw [heq, ← Real.rpow_def_of_pos hH0] at hbound
  exact hbound

end Erdos676
