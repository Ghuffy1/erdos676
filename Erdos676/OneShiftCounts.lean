import Erdos676.ResidueSieve
import Erdos676.PrimeResidues

open scoped BigOperators

namespace Erdos676

theorem one_shift_prime_count_error {P : Type*} [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (d : Finset P) (S N : ℕ) :
    |(∑ n ∈ Finset.range N,
      eventProduct (residueEvent a (fun p => smallResidues (a p)) S) d n) -
      (N : ℝ) * (∏ p ∈ d, (1 : ℝ) / a p)| ≤ ∏ p ∈ d, (a p : ℝ) := by
  let A (p : P) := smallResidues (a p)
  have hcard (p : P) : (A p).card = a p := smallResidues_card (a p) (hprime p).one_lt.le
  have hdensity (p : P) : residueDensity a A p = (1 : ℝ) / a p := by
    unfold residueDensity
    rw [hcard]
    have hp0 : (a p : ℝ) ≠ 0 := by exact_mod_cast (hprime p).ne_zero
    field_simp
  have hcoprime : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun h => hpq (hinj h))).pow 2 2
  have h := residueEvent_count_error a A (fun p => (hprime p).pos) hcoprime d S N
  simpa only [hcard, hdensity, A] using h

end Erdos676
