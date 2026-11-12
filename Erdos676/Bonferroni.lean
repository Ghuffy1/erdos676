import Erdos676.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.Parity

open scoped BigOperators

namespace Erdos676

def alternatingChoose (K m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m + 1), (-1) ^ i * (K.choose i : ℤ)

theorem alternatingChoose_succ (K m : ℕ) :
    alternatingChoose (K + 1) m = (-1) ^ m * (K.choose m : ℤ) := by
  exact Int.alternating_sum_range_choose_eq_choose

theorem alternatingChoose_zero (m : ℕ) : alternatingChoose 0 m = 1 := by
  induction m with
  | zero => simp [alternatingChoose]
  | succ m ih =>
      unfold alternatingChoose at *
      rw [Finset.sum_range_succ]
      simp [ih]

theorem alternatingChoose_even_upper (K m : ℕ) (hm : Even m) :
    (if K = 0 then (1 : ℤ) else 0) ≤ alternatingChoose K m := by
  cases K with
  | zero => simp [alternatingChoose_zero]
  | succ K =>
      rw [alternatingChoose_succ, hm.neg_one_pow]
      simp

theorem alternatingChoose_odd_lower (K m : ℕ) (hm : Odd m) :
    alternatingChoose K m ≤ (if K = 0 then (1 : ℤ) else 0) := by
  cases K with
  | zero => simp [alternatingChoose_zero]
  | succ K =>
      rw [alternatingChoose_succ, hm.neg_one_pow]
      simp

theorem alternatingChoose_nonneg (K m : ℕ) (hm : Even m) :
    0 ≤ alternatingChoose K m := by
  have h := alternatingChoose_even_upper K m hm
  split_ifs at h <;> omega

theorem alternatingChoose_successor_gap (K m : ℕ) (hm : Even (m + 1)) :
    alternatingChoose K (m + 1) - alternatingChoose K m = (K.choose (m + 1) : ℤ) := by
  unfold alternatingChoose
  rw [Finset.sum_range_succ, hm.neg_one_pow]
  ring

end Erdos676
