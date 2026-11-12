import Erdos676.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Erdos676

/-- For one fixed shift, every successful center maps to a distinct target. -/
theorem translated_count_le (U E : Finset ℕ) (j : ℕ) :
    (U.filter fun n => n + j ∈ E).card ≤ E.card := by
  apply Finset.card_le_card_of_injOn (fun n => n + j)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n _ m _ h
    exact Nat.add_right_cancel h

/-- Each target has at most H preimages among centers and shifts below H. -/
theorem translated_sum_le (U E : Finset ℕ) (H : ℕ) :
    (∑ n ∈ U, ∑ j ∈ Finset.range H, if n + j ∈ E then 1 else 0) ≤ H * E.card := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ j ∈ Finset.range H, (U.filter fun n => n + j ∈ E).card := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ ≤ ∑ _j ∈ Finset.range H, E.card :=
      Finset.sum_le_sum fun j _ => translated_count_le U E j
    _ = H * E.card := by simp

end Erdos676
