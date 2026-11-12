import Erdos676.ResidueSieve
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos676.SieveNormalization

open scoped BigOperators

namespace Erdos676

theorem log_nat_product {P : Type*} (a : P → ℕ) (ha : ∀ p, 0 < a p) (r : Finset P) :
    Real.log ((∏ p ∈ r, a p : ℕ) : ℝ) = ∑ p ∈ r, Real.log (a p) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p _ => by exact_mod_cast (ne_of_gt (ha p)))

theorem product_le_iff_sum_log_le {P : Type*} (a : P → ℕ) (ha : ∀ p, 0 < a p)
    (r : Finset P) {R : ℕ} (hR : 0 < R) :
    (∏ p ∈ r, a p) ≤ R ↔ (∑ p ∈ r, Real.log (a p)) ≤ Real.log R := by
  have hp : (0 : ℝ) < (∏ p ∈ r, a p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p _ => ha p)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  rw [← log_nat_product a ha r, Real.log_le_log_iff hp hR', Nat.cast_le]

theorem selbergNormalizer_bernoulli_probability {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (R : ℕ) (g : P → ℝ) (hg : ∀ p, g p ≠ 1) :
    selbergNormalizer (sieveSubsets a R) g * (∏ p : P, (1 - g p)) =
      ∑ r ∈ sieveSubsets a R, bernoulliWeight Finset.univ r g := by
  have h := truncated_sieve_normalization (Finset.univ : Finset P) g
    (fun r => (∏ p ∈ r, a p) ≤ R) (fun p _ => hg p)
  simpa only [Finset.powerset_univ, selbergNormalizer, sieveSubsets, selbergQ] using h

theorem selbergNormalizer_log_tail {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (ha : ∀ p, 0 < a p) (R : ℕ) (hR : 1 ≤ R) (g : P → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p < 1) :
    (1 - selbergNormalizer (sieveSubsets a R) g * (∏ p : P, (1 - g p))) * (Real.log R) ^ 2 ≤
      (∑ p : P, g p * Real.log (a p)) ^ 2 + ∑ p : P, g p * (Real.log (a p)) ^ 2 := by
  classical
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  have htail := bernoulli_truncation_bound (Finset.univ : Finset P) g
    (fun r => ∑ p ∈ r, Real.log (a p)) (Real.log R) hlogR
    (fun p _ => hg0 p) (fun p _ => (hg1 p).le)
  have hfilter : ((Finset.univ : Finset P).powerset.filter
      (fun r => (∑ p ∈ r, Real.log (a p)) ≤ Real.log R)) = sieveSubsets a R := by
    ext r
    simp only [Finset.powerset_univ, sieveSubsets, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (product_le_iff_sum_log_le a ha r (by omega)).symm
  rw [hfilter, ← selbergNormalizer_bernoulli_probability a R g (fun p => ne_of_lt (hg1 p))] at htail
  exact htail.trans (bernoulli_second_moment_le Finset.univ g (fun p => Real.log (a p)))

theorem square_residue_sieve_moment_bound {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (ha : ∀ p, 2 ≤ a p) (hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hmax : ∀ p, (A p).card < (a p) ^ 2)
    (R S N : ℕ) (hR : 2 ≤ R) (L : ℝ)
    (hmoment : (∑ p : P, residueDensity a A p * Real.log (a p)) ^ 2 +
      (∑ p : P, residueDensity a A p * (Real.log (a p)) ^ 2) ≤ 20 * L ^ 2)
    (hsmall : 20 * L ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (1 + 40 * (L / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - residueDensity a A p)) + (R : ℝ) ^ 8 := by
  have hb (p : P) := residueDensity_bounds a A p (by have := ha p; omega) (hmin p) (hmax p)
  have hEmpty : ∅ ∈ sieveSubsets a R := by simp [sieveSubsets]; omega
  have hG := selbergNormalizer_pos (sieveSubsets a R) (residueDensity a A) hEmpty
    (fun p => (hb p).1.le) (fun p => (hb p).2.1.le)
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have htail := selbergNormalizer_log_tail a (fun p => by have := ha p; omega) R
    (by omega) (residueDensity a A) (fun p => (hb p).1.le) (fun p => (hb p).2.1)
  have hinverse := inverse_normalizer_bound hG hlogR hsmall (htail.trans hmoment)
  have hmain := mul_le_mul_of_nonneg_left hinverse (Nat.cast_nonneg N)
  have hsieve := square_residue_sieve_upper a A ha hc hmin hmax R S N (by omega)
  calc
    _ ≤ (N : ℝ) / selbergNormalizer (sieveSubsets a R) (residueDensity a A) + (R : ℝ) ^ 8 := hsieve
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      calc
        (N : ℝ) / selbergNormalizer (sieveSubsets a R) (residueDensity a A) =
            (N : ℝ) * (1 / selbergNormalizer (sieveSubsets a R) (residueDensity a A)) := by ring
        _ ≤ _ := hmain
        _ = _ := by ring

end Erdos676
