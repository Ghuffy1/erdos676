import Erdos676.BernoulliModel

open scoped BigOperators

namespace Erdos676

theorem bernoulliWeight_factorization {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (ht : t ⊆ s)
    (hg : ∀ i ∈ s, g i ≠ 1) :
    bernoulliWeight s t g =
      (∏ i ∈ s, (1 - g i)) * ∏ i ∈ t, (g i / (1 - g i)) := by
  have ht0 : (∏ i ∈ t, (1 - g i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (Ne.symm (hg i (ht hi)))
  rw [Finset.prod_div_distrib, ← Finset.prod_sdiff ht]
  unfold bernoulliWeight
  field_simp

/-- Exact normalization of the truncated Selberg sum as a Bernoulli probability. -/
theorem truncated_sieve_normalization {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (keep : Finset ι → Prop) [DecidablePred keep]
    (hg : ∀ i ∈ s, g i ≠ 1) :
    (∑ t ∈ s.powerset with keep t, ∏ i ∈ t, g i / (1 - g i)) *
        (∏ i ∈ s, (1 - g i)) =
      ∑ t ∈ s.powerset with keep t, bernoulliWeight s t g := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [bernoulliWeight_factorization s t g
    (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1) hg]
  ring

/-- A second moment controls the lost mass from truncating the selected product. -/
theorem bernoulli_truncation_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (value : Finset ι → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    (1 - ∑ t ∈ s.powerset with value t ≤ R, bernoulliWeight s t g) * R ^ 2 ≤
      ∑ t ∈ s.powerset, bernoulliWeight s t g * (value t) ^ 2 := by
  classical
  have htotal := Finset.sum_filter_add_sum_filter_not s.powerset
    (fun t => value t ≤ R) (fun t => bernoulliWeight s t g)
  rw [sum_bernoulliWeight] at htotal
  simp only [not_le] at htotal
  have ht := weighted_square_tail_bound s.powerset (fun t => bernoulliWeight s t g)
    value R hR (fun t ht => bernoulliWeight_nonneg s t g
      (Finset.mem_powerset.mp ht) hg0 hg1)
  nlinarith

end Erdos676
