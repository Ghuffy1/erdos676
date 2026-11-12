import Erdos676.SmallPrimeCounts
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace Erdos676

theorem smallAverage_sum_eq_counts (z H S N : ℕ) :
    (∑ n ∈ Finset.range N, smallAverage z H (S + n)) =
      (∑ j ∈ Finset.range H, smallPrimeCount z (S + j) N) / (H : ℝ) := by
  classical
  simp only [smallAverage, smallPrimeCount, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.add_right_comm]

theorem smallAverage_sum_lower (z H S N : ℕ) (hH : 0 < H) (B : ℝ)
    (hcount : ∀ T : ℕ, B ≤ smallPrimeCount z T N) :
    B ≤ ∑ n ∈ Finset.range N, smallAverage z H (S + n) := by
  rw [smallAverage_sum_eq_counts]
  apply (le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)).mpr
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range H) => hcount (S + j))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using h

theorem sum_dyadic_interval_eq_range (X : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc X (2 * X), f n) = ∑ n ∈ Finset.range X, f (X + 1 + n) := by
  have hset : Finset.Ioc X (2 * X) = Finset.Ico (X + 1) (2 * X + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hlength : 2 * X + 1 - (X + 1) = X := by omega
  rw [hlength]

theorem smallAverage_dyadic_lower (z H X : ℕ) (hH : 0 < H) (B : ℝ)
    (hcount : ∀ T : ℕ, B ≤ smallPrimeCount z T X) :
    B ≤ ∑ n ∈ Finset.Ioc X (2 * X), smallAverage z H n := by
  rw [sum_dyadic_interval_eq_range]
  exact smallAverage_sum_lower z H (X + 1) X hH B hcount

end Erdos676
