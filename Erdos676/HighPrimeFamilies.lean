import Erdos676.PrimeAvoidSets
import Erdos676.HighPrimeBlocks
import Erdos676.InitialLargeAvoidance

open Filter
open scoped BigOperators Topology

namespace Erdos676

noncomputable def primeBandSet (x a b : ℝ) : Finset ℕ :=
  primesUpToReal (x ^ b) \ primesUpToReal (x ^ a)

theorem mem_primeBandSet (x a b : ℝ) (p : ℕ) :
    p ∈ primeBandSet x a b ↔ p.Prime ∧ x ^ a < p ∧ (p : ℝ) ≤ x ^ b := by
  simp only [primeBandSet, Finset.mem_sdiff, mem_primesUpToReal]
  aesop

theorem primeBandSet_mass {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) :
    primeMass (primeBandSet x a b) = primeReciprocalSum (x ^ b) - primeReciprocalSum (x ^ a) := by
  have hsub := primesUpToReal_subset (Real.rpow_le_rpow_of_exponent_le hx hab)
  have h := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  change primeMass (primeBandSet x a b) + primeReciprocalSum (x ^ a) =
    primeReciprocalSum (x ^ b) at h
  linarith

noncomputable def initialHighPrimeSet (X : ℕ) : Finset ℕ :=
  primesUpToReal (2 * (X : ℝ) ^ (1 / 2 : ℝ)) \ primesUpToReal ((X : ℝ) ^ (1 / 4 : ℝ))

noncomputable def selectedHighPrimes (X : ℕ) (τ : ℝ) : ℕ → Finset ℕ
  | 0 => initialHighPrimeSet X
  | j + 1 => selectedHighPrimes X τ j ∪ primeBandSet X (highPrimeLevel (j + 1)) (highPrimeBlockUpper τ j)

theorem initialHighPrimeSet_bounds {X p : ℕ} (hp : p ∈ initialHighPrimeSet X) :
    p.Prime ∧ (X : ℝ) ^ (1 / 4 : ℝ) < p ∧ (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  simp only [initialHighPrimeSet, Finset.mem_sdiff, mem_primesUpToReal] at hp
  aesop

theorem selectedHighPrimes_bounds {X : ℕ} (hX : 1 ≤ X) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    ∀ p ∈ selectedHighPrimes X τ j,
      p.Prime ∧ (X : ℝ) ^ highPrimeLevel j < p ∧
        (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  induction j with
  | zero =>
      intro p hp
      simpa only [highPrimeLevel_zero] using initialHighPrimeSet_bounds hp
  | succ j ih =>
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨hprime, hlo, hhi⟩ := ih p hp
        refine ⟨hprime, ?_, hhi⟩
        exact (Real.rpow_le_rpow_of_exponent_le hx (by
          rw [highPrimeLevel_succ]; linarith [highPrimeLevel_pos j])).trans_lt hlo
      · obtain ⟨hprime, hlo, hhi⟩ := (mem_primeBandSet _ _ _ p).mp hp
        refine ⟨hprime, hlo, hhi.trans ?_⟩
        have hbound := highPrimeBlock_bounds hτ0 hτ j
        have hpowers := Real.rpow_le_rpow_of_exponent_le hx (show highPrimeBlockUpper τ j ≤ 1 / 2 by linarith)
        have hpos := Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 : ℝ)
        linarith

theorem highPrimeBlock_mass_eventually {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      primeMass (primeBandSet X (highPrimeLevel (j + 1)) (highPrimeBlockUpper τ j)) ≤ Real.log 2 := by
  have hb := highPrimeBlock_bounds hτ0 hτ j
  have hlim := (prime_power_band_limit _ _ hb.1 (hb.1.trans hb.2.1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnear := (tendsto_order.mp hlim).2 (Real.log 2) (highPrimeBlock_log_mass hτ0 hτ j)
  filter_upwards [hnear, eventually_ge_atTop (1 : ℕ)] with X hX hx
  rw [primeBandSet_mass (by exact_mod_cast hx) hb.2.1.le]
  exact hX.le

theorem initialHighPrimeSet_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      d * X ≤ (primeAvoidSet (initialHighPrimeSet X) ((X : ℤ) + 1) (2 * X)).card := by
  obtain ⟨d, hd, hevent⟩ := initial_large_prime_avoidance.{0}
  refine ⟨d, hd, ?_⟩
  filter_upwards [hevent] with X hX
  let s := initialHighPrimeSet X
  letI (p : s) : NeZero (p : ℕ) := ⟨(initialHighPrimeSet_bounds p.property).1.ne_zero⟩
  have h := hX s (fun p : s => (p : ℕ))
    (fun p => (initialHighPrimeSet_bounds p.property).1) Subtype.val_injective
    (fun p => (initialHighPrimeSet_bounds p.property).2.1.le)
    (fun p => (initialHighPrimeSet_bounds p.property).2.2)
  simpa only [primeAvoidSet_subtype] using h

end Erdos676
