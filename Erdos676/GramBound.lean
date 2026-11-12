import Erdos676.Gluing

open scoped BigOperators

namespace Erdos676

/-- The row-sum estimate used for the separated-frequency Gram matrix. -/
theorem symmetric_row_sum_bound {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ)
    (r : ι → ℝ) (C : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, K i j) ≤ C) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * r i * r j) ≤ C * ∑ i ∈ s, (r i) ^ 2 := by
  have hfirst : (∑ i ∈ s, ∑ j ∈ s, K i j * (r i) ^ 2) =
      ∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    ring
  have hsecond : (∑ i ∈ s, ∑ j ∈ s, K i j * (r j) ^ 2) =
      ∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
    ring
  have htwice : 2 * (∑ i ∈ s, ∑ j ∈ s, K i j * r i * r j) ≤
      2 * (∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j)) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, K i j * (2 * r i * r j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, K i j * ((r i) ^ 2 + (r j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hK i hi j hj)
        nlinarith [sq_nonneg (r i - r j)]
      _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [hfirst, hsecond]
        ring
  have htotal : (∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j)) ≤
      C * ∑ i ∈ s, (r i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (r i))
    nlinarith
  linarith

end Erdos676
