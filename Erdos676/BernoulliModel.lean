import Erdos676.ProductBrackets
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

namespace Erdos676

noncomputable def bernoulliWeight {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) : ℝ :=
  (∏ i ∈ t, g i) * ∏ i ∈ s \ t, (1 - g i)

theorem sum_bernoulliWeight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) :
    ∑ t ∈ s.powerset, bernoulliWeight s t g = 1 := by
  have h := Finset.prod_add g (fun i => 1 - g i) s
  simpa [bernoulliWeight] using h.symm

theorem bernoulliWeight_nonneg {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (ht : t ⊆ s)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    0 ≤ bernoulliWeight s t g := by
  unfold bernoulliWeight
  exact mul_nonneg (Finset.prod_nonneg fun i hi => hg0 i (ht hi))
    (Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hg1 i (Finset.mem_sdiff.mp hi).1))

/-- Finite weighted Markov bound used on the logarithm of the selected prime product. -/
theorem weighted_square_tail_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w value : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s with R < value i, w i) * R ^ 2 ≤
      ∑ i ∈ s, w i * (value i) ^ 2 := by
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i ∈ s with R < value i, w i * (value i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hlarge⟩ := Finset.mem_filter.mp hi
      apply mul_le_mul_of_nonneg_left _ (hw i his)
      nlinarith
    _ ≤ ∑ i ∈ s, w i * (value i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg _))

end Erdos676
