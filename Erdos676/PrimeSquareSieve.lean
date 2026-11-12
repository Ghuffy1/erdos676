import Erdos676.PrimeIndexMoments
import Erdos676.TruncationLog

open scoped BigOperators

namespace Erdos676

theorem prime_square_sieve_upper_strict {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hmax : ∀ p, (A p).card < (a p) ^ 2)
    (hcard : ∀ p, (A p).card ≤ 2 * a p)
    (R S N : ℕ) (hR : 2 ≤ R) (z : ℝ) (hz : 2 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - residueDensity a A p)) + (R : ℝ) ^ 8 := by
  have hb (p : P) := residueDensity_bounds a A p (hprime p).pos (hmin p) (hmax p)
  have hg (p : P) : residueDensity a A p ≤ 2 / a p := by
    have hap : (0 : ℝ) < a p := by exact_mod_cast (hprime p).pos
    have hcard' : ((A p).card : ℝ) ≤ 2 * a p := by exact_mod_cast hcard p
    unfold residueDensity
    calc
      _ ≤ (2 * a p) / (a p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcard' (sq_nonneg _)
      _ = 2 / a p := by field_simp
  have hmoment := prime_index_log_moments a hinj hprime hz hle hlarge
    (residueDensity a A) (fun p => (hb p).1.le) hg
  have hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun heq => hpq (hinj heq))).pow 2 2
  exact square_residue_sieve_moment_bound a A (fun p => (hprime p).two_le) hc
    hmin hmax R S N hR (Real.log z) hmoment hsmall

/-- Uniform over all local unions, including a local condition that forbids every residue. -/
theorem prime_square_sieve_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hcard : ∀ p, (A p).card ≤ 2 * a p)
    (R S N : ℕ) (hR : 2 ≤ R) (z : ℝ) (hz : 2 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - residueDensity a A p)) + (R : ℝ) ^ 8 := by
  classical
  by_cases hstrict : ∀ p, (A p).card < (a p) ^ 2
  · exact prime_square_sieve_upper_strict a hinj hprime A hmin hstrict hcard
      R S N hR z hz hle hlarge hsmall
  · obtain ⟨p, hp⟩ := not_forall.mp hstrict
    let : NeZero (a p) := ⟨(hprime p).ne_zero⟩
    have hcap : (A p).card ≤ (a p) ^ 2 := by
      simpa only [ZMod.card] using (A p).card_le_univ
    have heq : (A p).card = (a p) ^ 2 := le_antisymm hcap (Nat.le_of_not_gt hp)
    have hfull : A p = Finset.univ := Finset.eq_univ_of_card _ (by simpa only [ZMod.card] using heq)
    have hevent (n : ℕ) : residueEvent a A S p n := by simp [residueEvent, hfull]
    have hleft : (∑ n ∈ Finset.range N,
        eventProduct (fun q n => ¬ residueEvent a A S q n) Finset.univ n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simpa [eventProduct] using (show ∃ q, residueEvent a A S q n from ⟨p, hevent n⟩)
    have hdensity : residueDensity a A p = 1 := by
      unfold residueDensity
      rw [heq]
      push_cast
      exact div_self (pow_ne_zero 2 (by exact_mod_cast (hprime p).ne_zero))
    have hprod : (∏ q : P, (1 - residueDensity a A q)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      rw [hdensity]
      ring
    rw [hleft, hprod]
    simp

end Erdos676
