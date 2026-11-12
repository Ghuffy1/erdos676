import Erdos676.TriangularMajorant
import Erdos676.PrimeFrequencySeparation

open scoped BigOperators

namespace Erdos676

theorem prime_frequency_sampling_bound {P : Type*} (s : Finset P)
    (p : P → ℕ) (k : P → ℤ) (c : P → ℂ) (S : ℤ) (N : ℕ) (hN : 0 < N)
    (hprime : ∀ i ∈ s, (p i).Prime) (hnonzero : ∀ i ∈ s, k i ≠ 0)
    (hsmall : ∀ i ∈ s, (k i).natAbs < p i)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, p i = p j → k i = k j → i = j)
    (hsize : ∀ i ∈ s, ∀ j ∈ s, (p i : ℝ) ^ 2 * (p j : ℝ) ^ 2 ≤ 2 * N) :
    (∑ n ∈ Finset.range N,
      ‖∑ i ∈ s, c i * realCharacter ((k i : ℝ) / (p i : ℝ) ^ 2) (S + n)‖ ^ 2) ≤
        256 * N * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let θ (i : P) := (k i : ℝ) / (p i : ℝ) ^ 2
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (2 * N : ℕ) * |θ i - θ j| := by
    intro i hi j hj hij
    have hpair : ¬(p i = p j ∧ k i = k j) := fun h => hij (hinj i hi j hj h.1 h.2)
    have h := prime_frequency_separation (p i) (p j) (k i) (k j)
      (hprime i hi) (hprime j hj) (hnonzero i hi) (hsmall i hi) hpair
    have hden : 0 < (p i : ℝ) ^ 2 * (p j : ℝ) ^ 2 := by
      have hi' : (0 : ℝ) < p i := by exact_mod_cast (hprime i hi).pos
      have hj' : (0 : ℝ) < p j := by exact_mod_cast (hprime j hj).pos
      positivity
    have hmul := (div_le_iff₀ hden).mp h
    have hscaled := mul_le_mul_of_nonneg_right (hsize i hi j hj) (abs_nonneg (θ i - θ j))
    change 1 ≤ ((2 * N : ℕ) : ℝ) * |θ i - θ j|
    push_cast
    dsimp [θ] at hscaled ⊢
    nlinarith
  have hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2 := by
    intro i hi j hj
    have hi' := prime_frequency_abs_le_quarter (p i) (k i) (hprime i hi).two_le (hsmall i hi)
    have hj' := prime_frequency_abs_le_quarter (p j) (k j) (hprime j hj).two_le (hsmall j hj)
    have h := abs_sub_le (θ i) 0 (θ j)
    simp only [sub_zero, zero_sub, abs_neg] at h
    dsimp [θ] at h
    linarith
  exact separated_translated_sampling_bound s θ c S N hN hsep hdiam

end Erdos676
