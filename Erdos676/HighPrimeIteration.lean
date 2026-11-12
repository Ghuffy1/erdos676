import Erdos676.HighPrimeFamilies

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem power_saving_eventually {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (K : ℝ) :
    ∀ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (1 - δ) ≤ ε * X := by
  have hlim := ((tendsto_rpow_neg_atTop hδ).const_mul K).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnear : ∀ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (-δ) < ε :=
    (tendsto_order.mp (by simpa only [mul_zero, Function.comp_def] using hlim)).2 ε hε
  filter_upwards [hnear, eventually_ge_atTop (1 : ℕ)] with X hX hx
  have hx0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have h := mul_le_mul_of_nonneg_right hX.le hx0.le
  have heq : (X : ℝ) ^ (-δ) * X = (X : ℝ) ^ (1 - δ) := by
    calc
      (X : ℝ) ^ (-δ) * X = (X : ℝ) ^ (-δ) * (X : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (X : ℝ) ^ (-δ + 1) := (Real.rpow_add hx0 _ _).symm
      _ = (X : ℝ) ^ (1 - δ) := by congr 1; ring
  simpa only [mul_assoc, heq] using h

theorem highPrimeStep_eventually {τ ε : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2)
    (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      dyadicRetention * (primeAvoidSet (selectedHighPrimes X τ j) ((X : ℤ) + 1) (2 * X)).card - ε * X ≤
        (primeAvoidSet (selectedHighPrimes X τ (j + 1)) ((X : ℤ) + 1) (2 * X)).card := by
  have hb := highPrimeBlock_bounds hτ0 hτ j
  let η := (highPrimeBlockUpper τ j + highPrimeLevel j) / 2
  obtain ⟨K, δ, hK, hδ, havg⟩ := prime_set_high_averaging hb.1 hb.2.1.le
    (hb.2.2.1.le.trans hb.2.2.2)
    (show highPrimeBlockUpper τ j < η by dsimp [η]; linarith [hb.2.2.1])
    (show η < highPrimeLevel j by dsimp [η]; linarith [hb.2.2.1])
    (show highPrimeLevel j ≤ 1 / 2 by linarith [hb.2.2.2])
  filter_upwards [havg, power_saving_eventually hδ hε K,
    highPrimeBlock_mass_eventually hτ0 hτ j, eventually_ge_atTop (1 : ℕ)] with X hX herr hmass hx
  let s := selectedHighPrimes X τ j
  let t := primeBandSet X (highPrimeLevel (j + 1)) (highPrimeBlockUpper τ j)
  have hs := selectedHighPrimes_bounds hx hτ0 hτ j
  have ht (p : ℕ) (hp : p ∈ t) := (mem_primeBandSet _ _ _ p).mp hp
  have hbound := hX s t (fun p hp => (hs p hp).1) (fun p hp => (ht p hp).1)
    (fun p hp => (hs p hp).2.1.le) (fun p hp => (hs p hp).2.2)
    (fun p hp => (ht p hp).2.1.le) (fun p hp => (ht p hp).2.2)
  have hcount : (∑ n ∈ primeAvoidSet s ((X : ℤ) + 1) (2 * X), primeWitnessCount t n) ≤
      Real.log 2 * (primeAvoidSet s ((X : ℤ) + 1) (2 * X)).card + ε * X := by
    have hupper := (le_abs_self _).trans hbound
    have hscaled := mul_le_mul_of_nonneg_right hmass
      (Nat.cast_nonneg (primeAvoidSet s ((X : ℤ) + 1) (2 * X)).card)
    linarith
  exact prime_avoidance_step s t _ _ (Real.log 2) (ε * X) hcount

theorem selectedHighPrimes_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ (τ : ℝ), 0 < τ → τ < 1 / 2 → ∀ (j : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ X : ℕ in atTop,
        (d * dyadicRetention ^ j - ε) * X ≤
          (primeAvoidSet (selectedHighPrimes X τ j) ((X : ℤ) + 1) (2 * X)).card := by
  obtain ⟨d, hd, hinit⟩ := initialHighPrimeSet_avoidance
  refine ⟨d, hd, ?_⟩
  intro τ hτ0 hτ j
  induction j with
  | zero =>
      intro ε hε
      filter_upwards [hinit] with X hX
      simp only [pow_zero, mul_one, selectedHighPrimes]
      have hεX : 0 ≤ ε * (X : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg X)
      linarith
  | succ j ih =>
      intro ε hε
      have hε2 : 0 < ε / 2 := by positivity
      filter_upwards [ih (ε / 2) hε2, highPrimeStep_eventually hτ0 hτ hε2 j] with X hprev hstep
      have hd0 : 0 ≤ dyadicRetention := by linarith [dyadicRetention_bounds.1]
      have hscaled := mul_le_mul_of_nonneg_left hprev hd0
      have he := mul_le_mul_of_nonneg_right dyadicRetention_bounds.2.le
        (show 0 ≤ ε / 2 * (X : ℝ) by positivity)
      rw [pow_succ]
      nlinarith

end Erdos676
