import Erdos676.BernoulliProducts

open scoped BigOperators

namespace Erdos676

theorem bernoulliBasis_orthogonal {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (hg : ∀ p, g p ≠ 0) (r u : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g * bernoulliBasis g r t *
      bernoulliBasis g u t) =
      if r = u then ∏ p ∈ r, (1 - g p) / g p else 0 := by
  rw [bernoulliBasis_product_expectation]
  by_cases hru : r = u
  · subst u
    simp only [ite_true]
    calc
      _ = ∏ p : P, if p ∈ r then (1 - g p) / g p else 1 := by
        apply Finset.prod_congr rfl
        intro p _
        by_cases hp : p ∈ r
        · simp only [hp, ite_true]
          field_simp [hg p]
          ring
        · simp [hp]
      _ = _ := Finset.prod_ite_mem_eq r (fun p => (1 - g p) / g p)
  · simp only [hru, ite_false]
    obtain ⟨p, hp⟩ : ∃ p, (p ∈ r ∧ p ∉ u) ∨ (p ∉ r ∧ p ∈ u) := by
      by_contra! h
      apply hru
      ext p
      have hmem := h p
      tauto
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    rcases hp with ⟨hr, hu⟩ | ⟨hr, hu⟩
    · simp only [hr, hu, ite_true, ite_false, mul_one]
      field_simp [hg p]
      ring
    · simp only [hr, hu, ite_true, ite_false, one_mul]
      field_simp [hg p]
      ring

theorem weighted_square_expansion {A B : Type*}
    (S : Finset A) (T : Finset B) (weight : B → ℝ) (basis : A → B → ℝ)
    (coefficient : A → ℝ) :
    (∑ t ∈ T, weight t * (∑ a ∈ S, coefficient a * basis a t) ^ 2) =
      ∑ a ∈ S, ∑ b ∈ S, coefficient a * coefficient b *
        (∑ t ∈ T, weight t * basis a t * basis b t) := by
  calc
    _ = ∑ t ∈ T, ∑ a ∈ S, ∑ b ∈ S,
        coefficient a * coefficient b * (weight t * basis a t * basis b t) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_two, Finset.mul_sum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a ∈ S, ∑ b ∈ S, coefficient a * coefficient b *
        (∑ t ∈ T, weight t * basis a t * basis b t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact (Finset.mul_sum _ _ _).symm

theorem weighted_orthogonal_square {A B : Type*} [DecidableEq A]
    (S : Finset A) (T : Finset B) (weight : B → ℝ) (basis : A → B → ℝ)
    (coefficient norm : A → ℝ)
    (horth : ∀ a ∈ S, ∀ b ∈ S,
      (∑ t ∈ T, weight t * basis a t * basis b t) = if a = b then norm a else 0) :
    (∑ t ∈ T, weight t * (∑ a ∈ S, coefficient a * basis a t) ^ 2) =
      ∑ a ∈ S, (coefficient a) ^ 2 * norm a := by
  rw [weighted_square_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single a]
  · rw [horth a ha a ha]
    simp [pow_two]
  · intro b hb hba
    rw [horth a ha b hb]
    simp [Ne.symm hba]
  · exact fun h => (h ha).elim

end Erdos676
