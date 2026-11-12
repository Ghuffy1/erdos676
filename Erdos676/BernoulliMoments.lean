import Erdos676.BernoulliSieve
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

open scoped BigOperators

namespace Erdos676

theorem bernoulliWeight_insert_absent {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (i : ι) (hi : i ∉ s) (ht : t ⊆ s) :
    bernoulliWeight (insert i s) t g = (1 - g i) * bernoulliWeight s t g := by
  have hit : i ∉ t := fun h => hi (ht h)
  have hisdiff : i ∉ s \ t := fun h => hi (Finset.mem_sdiff.mp h).1
  unfold bernoulliWeight
  rw [Finset.insert_sdiff_of_notMem _ hit, Finset.prod_insert hisdiff]
  ring

theorem bernoulliWeight_insert_present {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (i : ι) (hi : i ∉ s) (ht : t ⊆ s) :
    bernoulliWeight (insert i s) (insert i t) g = g i * bernoulliWeight s t g := by
  have hit : i ∉ t := fun h => hi (ht h)
  simp only [bernoulliWeight, Finset.insert_sdiff_insert,
    Finset.sdiff_insert_of_notMem hi, Finset.prod_insert hit]
  ring

theorem bernoulli_expectation_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (F : Finset ι → ℝ) (i : ι) (hi : i ∉ s) :
    (∑ t ∈ (insert i s).powerset, bernoulliWeight (insert i s) t g * F t) =
      (1 - g i) * (∑ t ∈ s.powerset, bernoulliWeight s t g * F t) +
      g i * (∑ t ∈ s.powerset, bernoulliWeight s t g * F (insert i t)) := by
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [bernoulliWeight_insert_absent s t g i hi (Finset.mem_powerset.mp ht)]
    ring
  · apply Finset.sum_congr rfl
    intro t ht
    rw [bernoulliWeight_insert_present s t g i hi (Finset.mem_powerset.mp ht)]
    ring

theorem bernoulli_first_moment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ i ∈ t, f i)) =
      ∑ i ∈ s, g i * f i := by
  induction s using Finset.induction_on with
  | empty => simp [bernoulliWeight]
  | @insert i s hi ih =>
      rw [bernoulli_expectation_insert s g _ i hi]
      have hshift : (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ j ∈ insert i t, f j)) =
          f i + (∑ j ∈ s, g j * f j) := by
        calc
          _ = ∑ t ∈ s.powerset, bernoulliWeight s t g *
              (f i + ∑ j ∈ t, f j) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_insert (fun h => hi (Finset.mem_powerset.mp ht h))]
          _ = f i + (∑ j ∈ s, g j * f j) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
              sum_bernoulliWeight, one_mul, ih]
      rw [ih, hshift, Finset.sum_insert hi]
      ring

theorem bernoulli_second_moment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ i ∈ t, f i) ^ 2) =
      (∑ i ∈ s, g i * f i) ^ 2 + ∑ i ∈ s, g i * (1 - g i) * (f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp [bernoulliWeight]
  | @insert i s hi ih =>
      rw [bernoulli_expectation_insert s g _ i hi]
      have hshift : (∑ t ∈ s.powerset, bernoulliWeight s t g *
          (∑ j ∈ insert i t, f j) ^ 2) =
          (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ j ∈ t, f j) ^ 2) +
          2 * f i * (∑ j ∈ s, g j * f j) + (f i) ^ 2 := by
        calc
          _ = ∑ t ∈ s.powerset,
              (bernoulliWeight s t g * (∑ j ∈ t, f j) ^ 2 +
              (2 * f i) * (bernoulliWeight s t g * (∑ j ∈ t, f j)) +
              bernoulliWeight s t g * (f i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_insert (fun h => hi (Finset.mem_powerset.mp ht h))]
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
              sum_bernoulliWeight, one_mul, bernoulli_first_moment]
      rw [hshift, ih, Finset.sum_insert hi, Finset.sum_insert hi]
      ring

theorem bernoulli_second_moment_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ i ∈ t, f i) ^ 2) ≤
      (∑ i ∈ s, g i * f i) ^ 2 + ∑ i ∈ s, g i * (f i) ^ 2 := by
  rw [bernoulli_second_moment]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i hi
  have h : g i * (1 - g i) ≤ g i := by nlinarith [sq_nonneg (g i)]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- The finite Selberg normalization loses at most the logarithmic second moment. -/
theorem truncated_sieve_second_moment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i < 1) :
    (1 - (∑ t ∈ s.powerset with (∑ i ∈ t, f i) ≤ R,
        ∏ i ∈ t, g i / (1 - g i)) * (∏ i ∈ s, (1 - g i))) * R ^ 2 ≤
      (∑ i ∈ s, g i * f i) ^ 2 + ∑ i ∈ s, g i * (f i) ^ 2 := by
  classical
  rw [truncated_sieve_normalization s g _ (fun i hi => ne_of_lt (hg1 i hi))]
  exact (bernoulli_truncation_bound s g (fun t => ∑ i ∈ t, f i) R hR hg0
    (fun i hi => (hg1 i hi).le)).trans
      (bernoulli_second_moment_le s g f)

end Erdos676
