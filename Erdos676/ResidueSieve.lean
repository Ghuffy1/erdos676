import Erdos676.CRTCounts
import Erdos676.SelbergFromCounts
import Erdos676.SieveProducts

open scoped BigOperators

namespace Erdos676

noncomputable def residueDensity {P : Type*} (a : P → ℕ)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2))) (p : P) : ℝ :=
  (A p).card / (a p : ℝ) ^ 2

def residueEvent {P : Type*} (a : P → ℕ)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2))) (S : ℕ) (p : P) (n : ℕ) : Prop :=
  ((S + n : ℕ) : ZMod ((a p) ^ 2)) ∈ A p

theorem residueDensity_bounds {P : Type*} (a : P → ℕ)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2))) (p : P)
    (ha : 0 < a p) (hmin : a p ≤ (A p).card) (hmax : (A p).card < (a p) ^ 2) :
    0 < residueDensity a A p ∧ residueDensity a A p < 1 ∧
      |1 / residueDensity a A p| ≤ a p := by
  have ha' : (0 : ℝ) < a p := by exact_mod_cast ha
  have hc : (0 : ℝ) < (A p).card := by exact_mod_cast lt_of_lt_of_le ha hmin
  have hmin' : (a p : ℝ) ≤ (A p).card := by exact_mod_cast hmin
  have hmax' : ((A p).card : ℝ) < (a p : ℝ) ^ 2 := by exact_mod_cast hmax
  have hsq := sq_pos_of_pos ha'
  refine ⟨div_pos hc hsq, (div_lt_one hsq).mpr hmax', ?_⟩
  unfold residueDensity
  rw [one_div, inv_div, abs_of_nonneg (div_nonneg (sq_nonneg _) hc.le)]
  apply (div_le_iff₀ hc).mpr
  nlinarith

theorem residueEvent_count_error {P : Type*} [DecidableEq P]
    (a : P → ℕ) (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (ha : ∀ p, 0 < a p) (hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)))
    (d : Finset P) (S N : ℕ) :
    |(∑ n ∈ Finset.range N, eventProduct (residueEvent a A S) d n) -
      (N : ℝ) * (∏ p ∈ d, residueDensity a A p)| ≤ ∏ p ∈ d, ((A p).card : ℝ) := by
  classical
  let m (p : d) := (a p) ^ 2
  let B (p : d) := A p
  have hm : ∀ p : d, 0 < m p := fun p => pow_pos (ha p) 2
  have hd : Pairwise (fun p q : d => (m p).Coprime (m q)) := by
    intro p q hpq
    exact hc (Subtype.coe_ne_coe.mpr hpq)
  have h := residueCondition_interval_error m B hm hd S N
  have hp (n : ℕ) : residueCondition m B (S + n) ↔
      ∀ p ∈ d, residueEvent a A S p n := by
    constructor
    · intro hn p hpd
      exact hn ⟨p, hpd⟩
    · intro hn p
      exact hn p p.property
  have hsum : (@Nat.count (fun n => residueCondition m B (S + n)) (Classical.decPred _) N : ℝ) =
      ∑ n ∈ Finset.range N, eventProduct (residueEvent a A S) d n := by
    rw [Nat.count_eq_card_filter_range]
    simp only [eventProduct, ← hp]
    simp
  rw [hsum] at h
  have hmod : ((∏ p : d, m p : ℕ) : ℝ) = ∏ p ∈ d, (a p : ℝ) ^ 2 := by
    simp only [m, Nat.cast_prod, Nat.cast_pow]
    exact Finset.prod_coe_sort d (fun p => (a p : ℝ) ^ 2)
  have hcard : ((∏ p : d, (B p).card : ℕ) : ℝ) = ∏ p ∈ d, ((A p).card : ℝ) := by
    simp only [B, Nat.cast_prod]
    exact Finset.prod_coe_sort d (fun p => ((A p).card : ℝ))
  rw [hmod, hcard] at h
  have hdensity : (∏ p ∈ d, residueDensity a A p) =
      (∏ p ∈ d, ((A p).card : ℝ)) / (∏ p ∈ d, (a p : ℝ) ^ 2) := by
    simp only [residueDensity, Finset.prod_div_distrib]
  rw [hdensity]
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using h

noncomputable def sieveSubsets {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (R : ℕ) : Finset (Finset P) :=
  Finset.univ.filter (fun r => (∏ p ∈ r, a p) ≤ R)

/-- A uniform finite sieve bound with a coarse power error, obtained without sharp coefficients. -/
theorem square_residue_sieve_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (ha : ∀ p, 2 ≤ a p) (hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hmax : ∀ p, (A p).card < (a p) ^ 2)
    (R S N : ℕ) (hR : 1 ≤ R) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (N : ℝ) / selbergNormalizer (sieveSubsets a R) (residueDensity a A) + (R : ℝ) ^ 8 := by
  have hb (p : P) := residueDensity_bounds a A p (by have := ha p; omega) (hmin p) (hmax p)
  have hEmpty : ∅ ∈ sieveSubsets a R := by simp [sieveSubsets, hR]
  have hcoef : ∀ r ∈ sieveSubsets a R,
      (∑ d ∈ r.powerset, |basisCoefficient (residueDensity a A) d|) ≤ (R : ℝ) ^ 2 := by
    intro r hr
    exact prime_size_coefficient_bound a (residueDensity a A) r R ha (fun p => (hb p).2.2)
      (Finset.mem_filter.mp hr).2
  have hcounts : ∀ r ∈ sieveSubsets a R, ∀ u ∈ sieveSubsets a R,
      ∀ d ∈ r.powerset, ∀ e ∈ u.powerset,
      |(∑ n ∈ Finset.range N, eventProduct (residueEvent a A S) (d ∪ e) n) -
        (N : ℝ) * (∏ p ∈ d ∪ e, residueDensity a A p)| ≤ (R : ℝ) ^ 4 := by
    intro r hr u hu d hd e he
    have hprod := nat_prod_subsets_union_le a (fun p => by have := ha p; omega) r u d e R
      (Finset.mem_powerset.mp hd) (Finset.mem_powerset.mp he)
      (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hu).2
    have hcard : (∏ p ∈ d ∪ e, (A p).card) ≤ R ^ 4 := by
      calc
        _ ≤ ∏ p ∈ d ∪ e, (a p) ^ 2 :=
          Finset.prod_le_prod (fun p _ => (hmax p).le)
        _ = (∏ p ∈ d ∪ e, a p) ^ 2 := Finset.prod_pow _ _ _
        _ ≤ (R ^ 2) ^ 2 := Nat.pow_le_pow_left hprod 2
        _ = R ^ 4 := by ring
    have hcard' : (∏ p ∈ d ∪ e, ((A p).card : ℝ)) ≤ (R : ℝ) ^ 4 := by exact_mod_cast hcard
    exact (residueEvent_count_error a A (fun p => by have := ha p; omega) hc (d ∪ e) S N).trans hcard'
  have h := selberg_avoidance_upper_from_counts (Finset.range N) (sieveSubsets a R)
    (residueDensity a A) (residueEvent a A S) hEmpty (fun p => (hb p).1)
    (fun p => (hb p).2.1) (N : ℝ) ((R : ℝ) ^ 4) ((R : ℝ) ^ 2)
    (by positivity) (sq_nonneg _) hcoef hcounts
  convert h using 1 <;> ring

end Erdos676
