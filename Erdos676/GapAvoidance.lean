import Erdos676.HighPrimeIteration
import Erdos676.HighPrimeGaps

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem primeWitnessCount_nonneg (s : Finset ℕ) (n : ℤ) : 0 ≤ primeWitnessCount s n := by
  classical
  unfold primeWitnessCount
  exact Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)

theorem prime_witness_sum_upper (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (S : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc S (S + N - 1), primeWitnessCount s n) ≤
      N * primeMass s + ∑ p ∈ s, (p : ℝ) := by
  classical
  unfold primeWitnessCount
  rw [sum_int_interval, Finset.sum_comm]
  have h := Finset.sum_le_sum (fun p (hp : p ∈ s) => prime_witness_interval_upper p N (hs p hp) S)
  simpa only [primeMass, Finset.sum_add_distrib, div_eq_mul_inv, one_mul,
    Finset.mul_sum, Int.cast_add] using h

theorem prime_avoidance_gap_lower (s t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (S : ℤ) (N : ℕ) :
    (primeAvoidSet s S (S + N - 1)).card -
      (N * primeMass t + ∑ p ∈ t, (p : ℝ)) ≤
        (primeAvoidSet (s ∪ t) S (S + N - 1)).card := by
  have hsub : primeAvoidSet s S (S + N - 1) ⊆ Finset.Icc S (S + N - 1) := by
    classical
    exact Finset.filter_subset _ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => primeWitnessCount_nonneg t n)
  have hbound := hsum.trans (prime_witness_sum_upper t ht S N)
  have h := prime_avoidance_step s t S (S + N - 1) 0
    (N * primeMass t + ∑ p ∈ t, (p : ℝ)) (by simpa only [zero_mul, zero_add] using hbound)
  simpa only [sub_zero, one_mul] using h

noncomputable def allHighPrimes (X j : ℕ) : Finset ℕ :=
  primesUpToReal (2 * (X : ℝ) ^ (1 / 2 : ℝ)) \ primesUpToReal ((X : ℝ) ^ highPrimeLevel j)

theorem allHighPrimes_covered (X j : ℕ) (τ : ℝ) :
    allHighPrimes X j ⊆ selectedHighPrimes X τ j ∪ omittedHighPrimes X τ j := by
  intro p hp
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hprime, hupper⟩ := (mem_primesUpToReal _ p).mp hhi
  have hlower : (X : ℝ) ^ highPrimeLevel j < p := by
    by_contra h
    exact hlo ((mem_primesUpToReal _ p).mpr ⟨hprime, le_of_not_gt h⟩)
  exact Finset.mem_union.mpr (highPrime_covered X τ j p hprime hlower hupper)

theorem omittedHighPrimes_endpoint_sum {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop, (∑ p ∈ omittedHighPrimes X τ j, (p : ℝ)) ≤ ε * X := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (prime_endpoint_sum_small.{0} hε), eventually_ge_atTop (1 : ℕ)] with X hX hx
  let s := omittedHighPrimes X τ j
  have hb := omittedHighPrimes_bounds hx τ j
  have h := hX s (fun p : s => (p : ℕ)) Subtype.val_injective
    (fun p => (hb p p.property).1) (fun p => (hb p p.property).2)
  simpa only [Finset.sum_coe_sort] using h

theorem allHighPrimes_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ j : ℕ, ∀ᶠ X : ℕ in atTop,
      d * dyadicRetention ^ j * X ≤
        (primeAvoidSet (allHighPrimes X j) ((X : ℤ) + 1) (2 * X)).card := by
  obtain ⟨d, hd, hselected⟩ := selectedHighPrimes_avoidance
  refine ⟨d / 2, by positivity, ?_⟩
  intro j
  let g := d * dyadicRetention ^ j
  have hg : 0 < g := mul_pos hd (pow_pos (by linarith [dyadicRetention_bounds.1]) j)
  have he : 0 < g / 8 := by positivity
  obtain ⟨τ, hτ0, hτ, hgap⟩ := exists_small_highPrimeGap j he
  filter_upwards [hselected τ hτ0 hτ j (g / 8) he,
    omittedHighPrimes_mass_eventually hτ0 hτ he j,
    omittedHighPrimes_endpoint_sum he τ j, eventually_ge_atTop (1 : ℕ)] with X hsel hmass hend hx
  have hb := omittedHighPrimes_bounds hx τ j
  have hlower := prime_avoidance_gap_lower (selectedHighPrimes X τ j) (omittedHighPrimes X τ j)
    (fun p hp => (hb p hp).1) ((X : ℤ) + 1) X
  have heq : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  rw [heq] at hlower
  have hcard : ((primeAvoidSet (selectedHighPrimes X τ j ∪ omittedHighPrimes X τ j)
      ((X : ℤ) + 1) (2 * X)).card : ℝ) ≤
      (primeAvoidSet (allHighPrimes X j) ((X : ℤ) + 1) (2 * X)).card := by
    exact_mod_cast Finset.card_le_card (primeAvoidSet_mono (allHighPrimes_covered X j τ) _ _)
  have hmassX := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg X)
  have hgapX := mul_le_mul_of_nonneg_right hgap.le (Nat.cast_nonneg X)
  dsimp only [g] at *
  nlinarith

end Erdos676
