import Erdos676.PrimeSquareSieve
import Erdos676.LocalResidues

open scoped BigOperators

namespace Erdos676

/-- Uniform two-position sieve bound for the actual prime-square forbidden intervals. -/
theorem two_shift_sieve_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (k : ℤ) (R S N : ℕ) (hR : 2 ≤ R) (z : ℝ) (hz : 2 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N,
      eventProduct (fun p n => ¬ residueEvent a
        (fun p => twoPositionResidues (a p) (k : ZMod ((a p) ^ 2))) S p n) Finset.univ n) ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - twoPositionDensity (a p) (k : ZMod ((a p) ^ 2)))) + (R : ℝ) ^ 8 := by
  let A (p : P) := twoPositionResidues (a p) (k : ZMod ((a p) ^ 2))
  have hmin (p : P) : a p ≤ (A p).card := by
    have h : (smallResidues (a p)).card ≤ (A p).card :=
      Finset.card_le_card Finset.subset_union_left
    rwa [smallResidues_card (a p) (hprime p).one_lt.le] at h
  have hcard (p : P) : (A p).card ≤ 2 * a p := by
    have h := twoPositionResidues_card (a p) (hprime p).one_lt.le (k : ZMod ((a p) ^ 2))
    dsimp [A]
    omega
  have h := prime_square_sieve_upper a hinj hprime A hmin hcard R S N hR z hz hle hlarge hsmall
  simpa only [A, residueDensity, twoPositionDensity] using h

end Erdos676
