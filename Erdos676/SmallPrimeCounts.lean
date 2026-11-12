import Erdos676.DyadicFirstMoment
import Erdos676.Avoidance

open scoped BigOperators

namespace Erdos676

noncomputable def smallPrimeCount (z S N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.range N, if SmallAvoidance z (S + n) then 1 else 0

theorem smallAvoidance_iff_prime_family (z : ℝ) (n : ℕ) :
    SmallAvoidance ⌊z⌋₊ n ↔
      ∀ p : primesUpToReal z, ¬ (n : ZMod (p.val ^ 2)) ∈ smallResidues p.val := by
  constructor
  · intro hs p hmem
    have hp := (Finset.mem_filter.mp p.property).2
    have hple := (Finset.mem_Ioc.mp (Finset.mem_filter.mp p.property).1).2
    have hlarge := hs p hp hple
    exact (Nat.not_lt.mpr hlarge) ((mem_smallResidues p n hp.one_lt.le).mp hmem)
  · intro hs p hp hple
    have hmem : p ∈ primesUpToReal z :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, hple⟩, hp⟩
    apply Nat.le_of_not_gt
    intro hsmall
    exact hs ⟨p, hmem⟩ ((mem_smallResidues p n hp.one_lt.le).mpr hsmall)

theorem smallPrimeCount_eq_family (z : ℝ) (S N : ℕ) :
    smallPrimeCount ⌊z⌋₊ S N =
      ∑ n ∈ Finset.range N, eventProduct
        (fun (p : primesUpToReal z) n => ¬ residueEvent (fun p => p.val)
          (fun p => smallResidues p.val) S p n) Finset.univ n := by
  classical
  unfold smallPrimeCount
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : (∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
      ¬ residueEvent (fun p => p.val) (fun p => smallResidues p.val) S p n) ↔
        SmallAvoidance ⌊z⌋₊ (S + n) := by
    simp only [Finset.mem_univ, forall_true_left, residueEvent]
    exact (smallAvoidance_iff_prime_family z (S + n)).symm
  by_cases hs : SmallAvoidance ⌊z⌋₊ (S + n)
  · have hq := hiff.mpr hs
    simpa [eventProduct, hs] using hq
  · have hq : ¬ ∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
        ¬ residueEvent (fun p => p.val) (fun p => smallResidues p.val) S p n :=
      fun h => hs (hiff.mp h)
    simpa [eventProduct, hs] using hq

theorem smallPrimeCount_finite_lower (z : ℝ) (hz : 1 ≤ z)
    (J L : ℕ) (hL : 1 ≤ L) (hcover : dyadicCutoff z J < 2)
    (C : ℝ)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) (S N : ℕ) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N * survivalProduct z -
      (2 * (J : ℝ) + 1) * z ^ (8 * L + 8) ≤ smallPrimeCount ⌊z⌋₊ S N := by
  let P := primesUpToReal z
  have hprime (p : P) : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hmax (p : P) : (p.val : ℝ) ≤ z := ((mem_primesUpToReal z p.val).mp p.property).2
  have h := dyadic_first_moment_lower (fun p : P => p.val) Subtype.val_injective hprime
    z hz hmax J L hL hcover C hC hsmall S N
  have hprod : (∏ p : P, (1 - (1 : ℝ) / p.val)) = survivalProduct z :=
    Finset.prod_coe_sort P (fun p : ℕ => 1 - (1 : ℝ) / p)
  rw [hprod, ← smallPrimeCount_eq_family] at h
  exact h

end Erdos676
