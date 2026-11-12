import Erdos676.EventPolynomials

open scoped BigOperators

namespace Erdos676

theorem nat_prod_union_le {P : Type*} [DecidableEq P]
    (a : P → ℕ) (ha : ∀ p, 1 ≤ a p) (r u : Finset P) :
    (∏ p ∈ r ∪ u, a p) ≤ (∏ p ∈ r, a p) * (∏ p ∈ u, a p) := by
  have h := Finset.prod_union_inter (f := a) (s₁ := r) (s₂ := u)
  have hinter : 1 ≤ ∏ p ∈ r ∩ u, a p := Finset.one_le_prod (fun p _ => ha p)
  simpa only [mul_one] using
    (Nat.mul_le_mul_left (∏ p ∈ r ∪ u, a p) hinter).trans_eq h

theorem nat_prod_subsets_union_le {P : Type*} [DecidableEq P]
    (a : P → ℕ) (ha : ∀ p, 1 ≤ a p) (r u d e : Finset P) (R : ℕ)
    (hd : d ⊆ r) (he : e ⊆ u)
    (hr : (∏ p ∈ r, a p) ≤ R) (hu : (∏ p ∈ u, a p) ≤ R) :
    (∏ p ∈ d ∪ e, a p) ≤ R ^ 2 := by
  have hdprod : (∏ p ∈ d, a p) ≤ ∏ p ∈ r, a p :=
    Finset.prod_le_prod_of_subset_of_one_le hd (fun p _ _ => ha p)
  have heprod : (∏ p ∈ e, a p) ≤ ∏ p ∈ u, a p :=
    Finset.prod_le_prod_of_subset_of_one_le he (fun p _ _ => ha p)
  have hunion := nat_prod_union_le a ha d e
  have hmul := Nat.mul_le_mul (hdprod.trans hr) (heprod.trans hu)
  simpa only [pow_two] using hunion.trans hmul

theorem prime_size_coefficient_bound {P : Type*} [DecidableEq P]
    (a : P → ℕ) (g : P → ℝ) (r : Finset P) (R : ℕ)
    (ha : ∀ p, 2 ≤ a p) (hg : ∀ p, |1 / g p| ≤ a p)
    (hr : (∏ p ∈ r, a p) ≤ R) :
    (∑ d ∈ r.powerset, |basisCoefficient g d|) ≤ (R : ℝ) ^ 2 := by
  have h := basisCoefficient_abs_sum_le g (fun p => (a p : ℝ)) r
    (fun p _ => by exact_mod_cast ha p) (fun p _ => hg p)
  have hprod : (∏ p ∈ r, (a p : ℝ)) ≤ R := by exact_mod_cast hr
  have hprod0 : 0 ≤ ∏ p ∈ r, (a p : ℝ) := Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith

end Erdos676
