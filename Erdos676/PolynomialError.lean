import Erdos676.EventMoments

open scoped BigOperators

namespace Erdos676

theorem double_sum_error_bound {A B : Type*} (S : Finset A) (T : Finset B)
    (a : A → ℝ) (b : B → ℝ) (C D : A → B → ℝ) (K : ℝ)
    (h : ∀ i ∈ S, ∀ j ∈ T, |C i j - D i j| ≤ K) :
    |(∑ i ∈ S, ∑ j ∈ T, a i * b j * C i j) -
      (∑ i ∈ S, ∑ j ∈ T, a i * b j * D i j)| ≤
      (∑ i ∈ S, |a i|) * (∑ j ∈ T, |b j|) * K := by
  have heq : (∑ i ∈ S, ∑ j ∈ T, a i * b j * C i j) -
      (∑ i ∈ S, ∑ j ∈ T, a i * b j * D i j) =
      ∑ i ∈ S, ∑ j ∈ T, a i * b j * (C i j - D i j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, |∑ j ∈ T, a i * b j * (C i j - D i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, |a i * b j * (C i j - D i j)| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, |a i| * |b j| * K := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (h i hi j hj) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

theorem eventBasis_inner_error {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (g : P → ℝ) (hg : ∀ p, g p ≠ 0)
    (r u : Finset P) (E : P → N → Prop) (M K : ℝ)
    (happrox : ∀ d ∈ r.powerset, ∀ e ∈ u.powerset,
      |(∑ n ∈ I, eventProduct E (d ∪ e) n) - M * (∏ p ∈ d ∪ e, g p)| ≤ K) :
    |(∑ n ∈ I, eventBasis g r E n * eventBasis g u E n) -
      M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)| ≤
      (∑ d ∈ r.powerset, |basisCoefficient g d|) *
        (∑ e ∈ u.powerset, |basisCoefficient g e|) * K := by
  have hmodel := eventBasis_inner_expansion Finset.univ g r u
    (fun p t => p ∈ t) (fun t => bernoulliWeight Finset.univ t g)
  simp only [eventBasis_pattern] at hmodel
  rw [bernoulliBasis_orthogonal g hg r u] at hmodel
  simp_rw [bernoulli_event_mean] at hmodel
  have hactual := eventBasis_inner_expansion I g r u E (fun _ => 1)
  simp only [one_mul] at hactual
  rw [hactual, hmodel]
  have hscale : M * (∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
      basisCoefficient g d * basisCoefficient g e * (∏ p ∈ d ∪ e, g p)) =
      ∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
        basisCoefficient g d * basisCoefficient g e * (M * ∏ p ∈ d ∪ e, g p) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hscale]
  exact double_sum_error_bound r.powerset u.powerset (basisCoefficient g) (basisCoefficient g)
    (fun d e => ∑ n ∈ I, eventProduct E (d ∪ e) n)
    (fun d e => M * ∏ p ∈ d ∪ e, g p) K happrox

end Erdos676
