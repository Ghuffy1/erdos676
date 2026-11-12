import Erdos676.AvoidanceIteration
import Erdos676.AvoidanceMargins
import Erdos676.IntervalSums

open scoped BigOperators

namespace Erdos676

theorem prime_witness_interval_upper (p N : ℕ) (hp : p.Prime) (S : ℤ) :
    (∑ n ∈ Finset.range N,
      if (S + (n : ℤ) : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then (1 : ℝ) else 0) ≤
      (N : ℝ) / p + p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := modular_interval_upper (p ^ 2) (initialResidues (p ^ 2) p) S N
  rw [initialResidues_card _ _ (by nlinarith [hp.two_le]), Nat.cast_pow] at h
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have heq : ((N : ℝ) / (p : ℝ) ^ 2 + 1) * p = (N : ℝ) / p + p := by field_simp
  rwa [heq] at h

theorem initial_avoidance_card_lower {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (S : ℤ) (N : ℕ) :
    (N : ℝ) - N * (∑ p : P, 1 / (a p : ℝ)) - (∑ p : P, (a p : ℝ)) ≤
      (originalAvoidSet a S (S + N - 1)).card := by
  classical
  have hcount := avoid_filter_card_lower (Finset.Icc S (S + N - 1))
    (fun p n => (n : ZMod ((a p) ^ 2)) ∈ initialResidues ((a p) ^ 2) (a p))
  have hcount' : ((Finset.Icc S (S + N - 1)).card : ℝ) -
      (∑ n ∈ Finset.Icc S (S + N - 1), ∑ p : P,
        if (n : ZMod ((a p) ^ 2)) ∈ initialResidues ((a p) ^ 2) (a p) then (1 : ℝ) else 0) ≤
      (originalAvoidSet a S (S + N - 1)).card := by
    convert hcount using 1
    apply congrArg (fun s : Finset ℤ => (s.card : ℝ))
    ext n
    simp [originalAvoidSet]
  have hcard : (Finset.Icc S (S + N - 1)).card = N := by rw [Int.card_Icc]; omega
  rw [hcard] at hcount'
  have hsum : (∑ n ∈ Finset.Icc S (S + N - 1), ∑ p : P,
      if (n : ZMod ((a p) ^ 2)) ∈ initialResidues ((a p) ^ 2) (a p) then (1 : ℝ) else 0) ≤
      N * (∑ p : P, 1 / (a p : ℝ)) + (∑ p : P, (a p : ℝ)) := by
    rw [sum_int_interval, Finset.sum_comm]
    have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
      prime_witness_interval_upper (a p) N (hprime p) S)
    simpa only [Finset.sum_add_distrib, div_eq_mul_inv, one_mul, Finset.mul_sum, Int.cast_add] using h
  nlinarith

end Erdos676
