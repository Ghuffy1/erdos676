import Erdos676.EventPolynomials

open scoped BigOperators

namespace Erdos676

theorem bernoulli_event_mean {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (d : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g *
      eventProduct (fun p u => p ∈ u) d t) = ∏ p ∈ d, g p := by
  classical
  have hproduct (t : Finset P) :
      (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) =
      eventProduct (fun p u => p ∈ u) d t := by
    by_cases hd : d ⊆ t
    · have hleft : (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) = 1 := by
        apply Finset.prod_eq_one
        intro p _
        by_cases hp : p ∈ t
        · simp [hp]
        · have hpd : p ∉ d := fun h => hp (hd h)
          simp [hp, hpd]
      rw [hleft]
      have hall : ∀ p ∈ d, p ∈ t := hd
      simpa [eventProduct] using hall
    · obtain ⟨p, hpd, hpt⟩ := Finset.not_subset.mp hd
      have hleft : (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ p)
        simp [hpt, hpd]
      rw [hleft]
      have hnot : ¬ ∀ p ∈ d, p ∈ t := fun h => hpt (h p hpd)
      simp [eventProduct, hnot]
  calc
    _ = ∑ t : Finset P, bernoulliWeight Finset.univ t g *
        (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) := by
      simp_rw [hproduct]
    _ = ∏ p : P, (g p * 1 + (1 - g p) * (if p ∈ d then 0 else 1)) := by
      simpa only [Finset.powerset_univ] using
        bernoulli_product_expectation Finset.univ g (fun _ => 1) (fun p => if p ∈ d then 0 else 1)
    _ = ∏ p ∈ d, g p := by
      conv_rhs => rw [← Finset.prod_ite_mem_eq]
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p ∈ d <;> simp [hp]

theorem eventBasis_inner_expansion {P N : Type*} [DecidableEq P]
    (I : Finset N) (g : P → ℝ) (r u : Finset P) (E : P → N → Prop) (w : N → ℝ) :
    (∑ n ∈ I, w n * eventBasis g r E n * eventBasis g u E n) =
      ∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
        basisCoefficient g d * basisCoefficient g e *
          (∑ n ∈ I, w n * eventProduct E (d ∪ e) n) := by
  calc
    _ = ∑ n ∈ I, ∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
        basisCoefficient g d * basisCoefficient g e *
          (w n * eventProduct E (d ∪ e) n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [eventBasis_expansion, eventBasis_expansion, Finset.mul_sum]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      rw [eventProduct_union]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      exact (Finset.mul_sum _ _ _).symm

end Erdos676
