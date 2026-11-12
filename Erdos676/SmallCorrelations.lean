import Erdos676.TwoShiftSieve
import Erdos676.SmallPrimeCounts

open scoped BigOperators

namespace Erdos676

noncomputable def smallPairCount (z S N i j : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.range N,
    if SmallAvoidance z (S + n + i) ∧ SmallAvoidance z (S + n + j) then 1 else 0

noncomputable def pairSurvivalProduct (z : ℝ) (k : ℤ) : ℝ :=
  ∏ p ∈ primesUpToReal z, (1 - twoPositionDensity p (k : ZMod (p ^ 2)))

theorem pair_residue_membership (p S n i j : ℕ) :
    (((S + i + n : ℕ) : ZMod (p ^ 2)) ∈
      twoPositionResidues p (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p ^ 2))) ↔
        ((S + n + i : ℕ) : ZMod (p ^ 2)) ∈ smallResidues p ∨
        ((S + n + j : ℕ) : ZMod (p ^ 2)) ∈ smallResidues p := by
  have hfirst : ((S + i + n : ℕ) : ZMod (p ^ 2)) = ((S + n + i : ℕ) : ZMod (p ^ 2)) := by
    congr 1
    omega
  have hsecond : ((S + i + n : ℕ) : ZMod (p ^ 2)) + (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p ^ 2)) =
      ((S + n + j : ℕ) : ZMod (p ^ 2)) := by
    push_cast
    ring
  rw [twoPositionResidues, Finset.mem_union, mem_translatedBack, hsecond, hfirst]

theorem smallPairCount_eq_family (z : ℝ) (S N i j : ℕ) :
    smallPairCount ⌊z⌋₊ S N i j =
      ∑ n ∈ Finset.range N, eventProduct
        (fun (p : primesUpToReal z) n => ¬ residueEvent (fun p => p.val)
          (fun p => twoPositionResidues p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2)))
          (S + i) p n) Finset.univ n := by
  classical
  unfold smallPairCount
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : (∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
      ¬ residueEvent (fun p => p.val)
        (fun p => twoPositionResidues p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2))) (S + i) p n) ↔
      SmallAvoidance ⌊z⌋₊ (S + n + i) ∧ SmallAvoidance ⌊z⌋₊ (S + n + j) := by
    simp only [Finset.mem_univ, forall_true_left, residueEvent, pair_residue_membership, not_or]
    rw [forall_and]
    exact and_congr (smallAvoidance_iff_prime_family z (S + n + i)).symm
      (smallAvoidance_iff_prime_family z (S + n + j)).symm
  by_cases hs : SmallAvoidance ⌊z⌋₊ (S + n + i) ∧ SmallAvoidance ⌊z⌋₊ (S + n + j)
  · have hq := hiff.mpr hs
    simpa [eventProduct, hs] using hq
  · have hq : ¬ ∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
        ¬ residueEvent (fun p => p.val)
          (fun p => twoPositionResidues p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2))) (S + i) p n :=
      fun h => hs (hiff.mp h)
    simpa [eventProduct, hs] using hq

theorem smallPairCount_sieve_bound (z : ℝ) (hz : 2 ≤ z) (R S N i j : ℕ)
    (hR : 2 ≤ R) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    smallPairCount ⌊z⌋₊ S N i j ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N * pairSurvivalProduct z ((j : ℤ) - i) +
        (R : ℝ) ^ 8 := by
  let P := primesUpToReal z
  have hprime (p : P) : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hmax (p : P) : (p.val : ℝ) ≤ z := ((mem_primesUpToReal z p.val).mp p.property).2
  have h := two_shift_sieve_upper (fun p : P => p.val) Subtype.val_injective hprime
    ((j : ℤ) - i) R (S + i) N hR z hz hmax hlarge hsmall
  have hprod : (∏ p : P, (1 - twoPositionDensity p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2)))) =
      pairSurvivalProduct z ((j : ℤ) - i) := by
    unfold pairSurvivalProduct
    exact Finset.prod_coe_sort P (fun p : ℕ => 1 - twoPositionDensity p (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p ^ 2)))
  rw [hprod, ← smallPairCount_eq_family] at h
  exact h

end Erdos676
