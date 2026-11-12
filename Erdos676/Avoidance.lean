import Erdos676.ShiftCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic

open scoped BigOperators

namespace Erdos676

def SmallAvoidance (z n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ z → p ≤ n % p ^ 2

def LargeAvoidance (z n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → z < p → p ^ 2 ≤ n → p ≤ n % p ^ 2

theorem exceptional_of_small_large {z n : ℕ}
    (hs : SmallAvoidance z n) (hl : LargeAvoidance z n) : Exceptional n := by
  apply (exceptional_iff_mod n).mpr
  intro p hp hpn
  rcases le_or_gt p z with h | h
  · exact hs p hp h
  · exact hl p hp h hpn

noncomputable def smallAverage (z H n : ℕ) : ℝ := by
  classical
  exact (∑ j ∈ Finset.range H, if SmallAvoidance z (n + j) then 1 else 0) / (H : ℝ)

theorem smallAverage_nonneg (z H n : ℕ) : 0 ≤ smallAverage z H n := by
  classical
  unfold smallAverage
  exact div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)
    (Nat.cast_nonneg _)

/-- Stable large-prime avoidance turns the averaged small-prime mass into actual exceptions. -/
theorem smallAverage_mass_le_exceptions (U E : Finset ℕ) (z H : ℕ) (hH : 0 < H)
    (hlarge : ∀ n ∈ U, ∀ j < H, LargeAvoidance z (n + j))
    (hmem : ∀ n ∈ U, ∀ j < H, Exceptional (n + j) → n + j ∈ E) :
    (∑ n ∈ U, smallAverage z H n) ≤ E.card := by
  classical
  have hsupport :
      (∑ n ∈ U, ∑ j ∈ Finset.range H,
        if SmallAvoidance z (n + j) then (1 : ℕ) else 0) ≤ H * E.card := by
    apply le_trans ?_ (translated_sum_le U E H)
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro j hj
    by_cases hs : SmallAvoidance z (n + j)
    · have he := hmem n hn j (Finset.mem_range.mp hj)
        (exceptional_of_small_large hs (hlarge n hn j (Finset.mem_range.mp hj)))
      simp [hs, he]
    · simp [hs]
  have hcast :
      (∑ n ∈ U, ∑ j ∈ Finset.range H,
        if SmallAvoidance z (n + j) then (1 : ℝ) else 0) ≤ (H : ℝ) * E.card := by
    exact_mod_cast hsupport
  have hHreal : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  simp only [smallAverage, ← Finset.sum_div]
  exact (div_le_iff₀ hHreal).mpr (by simpa [mul_comm] using hcast)

end Erdos676
