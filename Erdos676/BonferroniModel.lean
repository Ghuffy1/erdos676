import Erdos676.BonferroniEvents
import Erdos676.EventMoments

open scoped BigOperators

namespace Erdos676

theorem weighted_sum_linearCombination {A B : Type*}
    (S : Finset A) (T : Finset B) (weight : B → ℝ) (coefficient : A → ℝ) (f : A → B → ℝ) :
    (∑ t ∈ T, weight t * (∑ a ∈ S, coefficient a * f a t)) =
      ∑ a ∈ S, coefficient a * (∑ t ∈ T, weight t * f a t) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem bernoulli_avoidance_mean {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g *
      eventProduct (fun p u => p ∉ u) s t) = ∏ p ∈ s, (1 - g p) := by
  classical
  have hproduct (t : Finset P) :
      (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) =
      eventProduct (fun p u => p ∉ u) s t := by
    by_cases hs : ∀ p ∈ s, p ∉ t
    · have hleft : (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro p _
        by_cases ht : p ∈ t
        · have hps : p ∉ s := fun h => hs p h ht
          simp [ht, hps]
        · simp [ht]
      rw [hleft]
      simpa [eventProduct] using hs
    · push Not at hs
      obtain ⟨p, hps, hpt⟩ := hs
      have hleft : (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ p)
        simp [hps, hpt]
      rw [hleft]
      have hnot : ¬ ∀ p ∈ s, p ∉ t := fun h => h p hps hpt
      simp [eventProduct, hnot]
  calc
    _ = ∑ t : Finset P, bernoulliWeight Finset.univ t g *
        (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) := by simp_rw [hproduct]
    _ = ∏ p : P, (g p * (if p ∈ s then (0 : ℝ) else 1) + (1 - g p) * 1) := by
      simpa only [Finset.powerset_univ] using
        bernoulli_product_expectation Finset.univ g (fun p => if p ∈ s then 0 else 1) (fun _ => 1)
    _ = ∏ p ∈ s, (1 - g p) := by
      conv_rhs => rw [← Finset.prod_ite_mem_eq]
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p ∈ s <;> simp [hp]

noncomputable def bonferroniModel {P : Type*} (s : Finset P) (k : ℕ) (g : P → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (∑ d ∈ s.powersetCard j, ∏ p ∈ d, g p)

theorem bonferroni_model_expectation {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g *
      bonferroniEvent s k (fun p u => p ∈ u) t) = bonferroniModel s k g := by
  unfold bonferroniEvent bonferroniModel
  rw [weighted_sum_linearCombination]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact bernoulli_event_mean g d

theorem bonferroniModel_even_upper {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) (hk : Even k)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    (∏ p ∈ s, (1 - g p)) ≤ bonferroniModel s k g := by
  rw [← bernoulli_avoidance_mean, ← bonferroni_model_expectation]
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (bonferroniEvent_even_upper s k (fun p u => p ∈ u) t hk)
    (bernoulliWeight_nonneg Finset.univ t g (Finset.subset_univ _)
      (fun p _ => hg0 p) (fun p _ => hg1 p))

theorem bonferroniModel_odd_lower {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) (hk : Odd k)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    bonferroniModel s k g ≤ ∏ p ∈ s, (1 - g p) := by
  rw [← bernoulli_avoidance_mean, ← bonferroni_model_expectation]
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (bonferroniEvent_odd_lower s k (fun p u => p ∈ u) t hk)
    (bernoulliWeight_nonneg Finset.univ t g (Finset.subset_univ _)
      (fun p _ => hg0 p) (fun p _ => hg1 p))

theorem bonferroniModel_gap {P : Type*} (g : P → ℝ) (s : Finset P) (k : ℕ)
    (hk : Even (k + 1)) :
    bonferroniModel s (k + 1) g - bonferroniModel s k g =
      ∑ d ∈ s.powersetCard (k + 1), ∏ p ∈ d, g p := by
  unfold bonferroniModel
  rw [Finset.sum_range_succ, hk.neg_one_pow]
  ring

end Erdos676
