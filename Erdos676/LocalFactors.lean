import Erdos676.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Erdos676

section FiniteGroup

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Number of members of A whose translate by k remains in A. -/
def overlap (A : Finset G) (k : G) : ℕ :=
  ∑ x ∈ A, if x + k ∈ A then 1 else 0

omit [Fintype G] in
theorem overlap_le_card (A : Finset G) (k : G) : overlap A k ≤ A.card := by
  unfold overlap
  calc
    _ ≤ ∑ _x ∈ A, 1 := Finset.sum_le_sum fun x hx => by split_ifs <;> omega
    _ = A.card := by simp

omit [Fintype G] in
theorem overlap_zero (A : Finset G) : overlap A 0 = A.card := by
  simp [overlap]

/-- Double counting proves the complete-period mean used in the singular factors. -/
theorem sum_overlap (A : Finset G) : ∑ k : G, overlap A k = A.card ^ 2 := by
  classical
  unfold overlap
  rw [Finset.sum_comm]
  have htranslate (x : G) :
      (∑ k : G, if x + k ∈ A then 1 else 0) = A.card := by
    calc
      _ = ∑ y : G, if y ∈ A then 1 else 0 :=
        Equiv.sum_comp (Equiv.addLeft x) (fun y => if y ∈ A then 1 else 0)
      _ = A.card := by simp
  simp_rw [htranslate]
  simp [pow_two]

end FiniteGroup

end Erdos676
