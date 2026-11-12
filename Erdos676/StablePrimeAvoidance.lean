import Erdos676.GapAvoidance
import Erdos676.BoundaryPowers

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem allHighPrimes_bounds {X j p : ℕ} (hp : p ∈ allHighPrimes X j) :
    p.Prime ∧ (X : ℝ) ^ highPrimeLevel j < p ∧
      (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  simp only [allHighPrimes, Finset.mem_sdiff, mem_primesUpToReal] at hp
  aesop

noncomputable def stableHighSet (X j : ℕ) (η : ℝ) : Finset ℤ :=
  lowerAvoidSet (fun p : allHighPrimes X j => (p : ℕ))
    ((X : ℤ) + 1) (2 * X) (powerFloor η X)

theorem stable_high_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ (j : ℕ) (η : ℝ), η < highPrimeLevel j →
      ∀ᶠ X : ℕ in atTop, d * dyadicRetention ^ j * X ≤ (stableHighSet X j η).card := by
  obtain ⟨d, hd, hfull⟩ := allHighPrimes_avoidance
  refine ⟨d / 2, by positivity, ?_⟩
  intro j η hη
  let c := highPrimeLevel j
  have hc0 : 0 < c := highPrimeLevel_pos j
  have hc : c ≤ 1 / 2 := by dsimp [c]; linarith [highPrimeLevel_le_quarter j]
  let g := d * dyadicRetention ^ j
  have hg : 0 < g := mul_pos hd (pow_pos (by linarith [dyadicRetention_bounds.1]) j)
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((tendsto_rpow_atTop hc0).eventually_ge_atTop 4)
  have herror := power_saving_eventually (show 0 < c - η by dsimp [c]; linarith)
    (show 0 < g / 2 by positivity) 13
  filter_upwards [hfull j, hlarge, herror, eventually_ge_atTop (1 : ℕ)] with X hcount hlargeX herr hx
  let s := allHighPrimes X j
  let a : s → ℕ := fun p => (p : ℕ)
  let m := ⌊(X : ℝ) ^ c / 2⌋₊
  let H := powerFloor η X
  have hs (p : s) := allHighPrimes_bounds p.property
  letI (p : s) : NeZero (a p) := ⟨(hs p).1.ne_zero⟩
  have hxreal : (1 : ℝ) ≤ X := by exact_mod_cast hx
  have hmreal : 0 < (m : ℝ) := by
    have hhalf := floor_ge_half (show 2 ≤ (X : ℝ) ^ c / 2 by linarith)
    dsimp [m]
    linarith
  have hm : 0 < m := by exact_mod_cast hmreal
  have hfloor : (m : ℝ) ≤ (X : ℝ) ^ c / 2 := Nat.floor_le (by positivity)
  have hlo (p : s) : m < a p := by
    have hp := (hs p).2.1
    dsimp only [c] at hfloor hlargeX
    have hreal : (m : ℝ) < (a p : ℝ) := by dsimp [a]; linarith
    exact_mod_cast hreal
  have hb := avoidance_boundary_card_bound a (fun p => (hs p).1) Subtype.val_injective
    m hm hlo (2 * (X : ℝ) ^ (1 / 2 : ℝ)) (by positivity)
    (fun p => (hs p).2.2) ((X : ℤ) + 1) X H
  have heq : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  rw [heq] at hb
  have hcards := (avoidance_card_bounds a ((X : ℤ) + 1) (2 * X) H).1
  have hcardsR : ((originalAvoidSet a ((X : ℤ) + 1) (2 * X)).card : ℝ) ≤
      (lowerAvoidSet a ((X : ℤ) + 1) (2 * X) H).card + H +
        (avoidanceBoundarySet a ((X : ℤ) + 1) (2 * X) H).card := by exact_mod_cast hcards
  have hpower := boundary_error_power_bound hxreal hc (by simpa only [c] using hlargeX)
    (Nat.cast_nonneg H) 1 (show (H : ℝ) ≤ (1 : ℕ) * (X : ℝ) ^ η by
      simpa only [H, powerFloor, Nat.cast_one, one_mul] using Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) η))
  have hpowe : 1 + η - c = 1 - (c - η) := by ring
  simp only [Nat.cast_one, mul_one, hpowe] at hpower
  have hcount' : g * X ≤ (originalAvoidSet a ((X : ℤ) + 1) (2 * X)).card := by
    simpa only [a, s, g, primeAvoidSet_subtype] using hcount
  change d / 2 * dyadicRetention ^ j * X ≤ (lowerAvoidSet a ((X : ℤ) + 1) (2 * X) H).card
  dsimp only [g] at herr hcount'
  dsimp only [m] at hb
  nlinarith

end Erdos676
