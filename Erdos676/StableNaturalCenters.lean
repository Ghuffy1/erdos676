import Erdos676.StablePrimeAvoidance
import Erdos676.SmallPrimeCounts

open Filter
open scoped BigOperators Topology

namespace Erdos676

noncomputable def stableNaturalCenters (X j : ℕ) (η : ℝ) : Finset ℕ :=
  (stableHighSet X j η).image Int.toNat

theorem stableHighSet_interval {X j : ℕ} {η : ℝ} {n : ℤ} (hn : n ∈ stableHighSet X j η) :
    (X : ℤ) + 1 ≤ n ∧ n ≤ 2 * X - powerFloor η X := by
  classical
  exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1

theorem stableNaturalCenters_card (X j : ℕ) (η : ℝ) :
    (stableNaturalCenters X j η).card = (stableHighSet X j η).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  have ha0 : 0 ≤ a := by have := (stableHighSet_interval ha).1; omega
  have hb0 : 0 ≤ b := by have := (stableHighSet_interval hb).1; omega
  have h := congrArg (fun n : ℕ => (n : ℤ)) hab
  simpa only [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] using h

theorem stableNaturalCenters_shifts {X j : ℕ} {η : ℝ} {n k : ℕ}
    (hn : n ∈ stableNaturalCenters X j η) (hk : k < powerFloor η X) :
    X < n + k ∧ n + k ≤ 2 * X := by
  classical
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hmlo, hmhi⟩ := stableHighSet_interval hm
  have hm0 : 0 ≤ m := by omega
  have hcast := Int.toNat_of_nonneg hm0
  omega

theorem stableNaturalCenters_subset (X j : ℕ) (η : ℝ) :
    stableNaturalCenters X j η ⊆ Finset.Ioc X (2 * X) := by
  classical
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hmlo, hmhi⟩ := stableHighSet_interval hm
  have hm0 : 0 ≤ m := by omega
  have hcast := Int.toNat_of_nonneg hm0
  exact Finset.mem_Ioc.mpr (by omega)

theorem stableNaturalCenters_large_avoidance {X j : ℕ} {η : ℝ} {n k : ℕ}
    (hn : n ∈ stableNaturalCenters X j η) (hk : k < powerFloor η X) :
    LargeAvoidance ⌊(X : ℝ) ^ highPrimeLevel j⌋₊ (n + k) := by
  classical
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  have hm0 : 0 ≤ m := by have := (stableHighSet_interval hm).1; omega
  have hcast := Int.toNat_of_nonneg hm0
  have hshift := lowerAvoidSet_shift (fun p : allHighPrimes X j => (p : ℕ))
    ((X : ℤ) + 1) (2 * X) (powerFloor η X) (k : ℤ) (by omega) (by omega) m hm
  have hres := (Finset.mem_filter.mp hshift).2
  intro p hp hcut hpn
  have hlow : (X : ℝ) ^ highPrimeLevel j < (p : ℝ) :=
    (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg X) _)).mp hcut
  have hupper : (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
    have hinterval := Finset.mem_Icc.mp (Finset.mem_filter.mp hshift).1
    have hnat : m.toNat + k ≤ 2 * X := by omega
    have hp2 : (p : ℝ) ^ 2 ≤ 2 * X := by exact_mod_cast hpn.trans hnat
    have hsquare : ((X : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
      norm_num
    have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 : ℝ)
    nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hmem : p ∈ allHighPrimes X j := by
    apply Finset.mem_sdiff.mpr
    exact ⟨(mem_primesUpToReal _ p).mpr ⟨hp, hupper⟩,
      fun h => (not_le_of_gt hlow) ((mem_primesUpToReal _ p).mp h).2⟩
  have havoid := hres ⟨p, hmem⟩
  have heqm : ((m.toNat : ℕ) : ZMod (p ^ 2)) = (m : ZMod (p ^ 2)) := by
    rw [← Int.cast_natCast, hcast]
  have havoidNat : ((m.toNat + k : ℕ) : ZMod (p ^ 2)) ∉ smallResidues p := by
    simpa only [Nat.cast_add, heqm, Int.cast_add, Int.cast_natCast, initial_prime_square] using havoid
  exact Nat.le_of_not_gt (fun hsmall => havoidNat ((mem_smallResidues p _ hp.one_lt.le).mpr hsmall))

theorem stable_natural_centers :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ (j : ℕ) (η : ℝ), η < highPrimeLevel j →
      ∀ᶠ X : ℕ in atTop, d * dyadicRetention ^ j * X ≤ (stableNaturalCenters X j η).card := by
  obtain ⟨d, hd, hstable⟩ := stable_high_avoidance
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right _ _, ?_⟩
  intro j η hη
  filter_upwards [hstable j η hη] with X hX
  rw [stableNaturalCenters_card]
  have h := mul_le_mul_of_nonneg_right (min_le_left d 1)
    (show 0 ≤ dyadicRetention ^ j * (X : ℝ) by
      apply mul_nonneg (pow_nonneg (by linarith [dyadicRetention_bounds.1]) _) (Nat.cast_nonneg X))
  nlinarith

end Erdos676
