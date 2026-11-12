import Erdos676.HighPrimeFamilies

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem primeMass_union_le (s t : Finset ℕ) : primeMass (s ∪ t) ≤ primeMass s + primeMass t := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := fun p : ℕ => 1 / (p : ℝ))
  have hpos : 0 ≤ primeMass (s ∩ t) := Finset.sum_nonneg (fun p hp => by positivity)
  change primeMass (s ∪ t) + primeMass (s ∩ t) = primeMass s + primeMass t at h
  linarith

noncomputable def omittedHighPrimes (X : ℕ) (τ : ℝ) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => omittedHighPrimes X τ j ∪ primeBandSet X (highPrimeBlockUpper τ j) (highPrimeLevel j)

theorem highPrime_covered (X : ℕ) (τ : ℝ) (j p : ℕ) (hp : p.Prime)
    (hlo : (X : ℝ) ^ highPrimeLevel j < p)
    (hhi : (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) :
    p ∈ selectedHighPrimes X τ j ∨ p ∈ omittedHighPrimes X τ j := by
  induction j with
  | zero =>
      left
      simp only [selectedHighPrimes, initialHighPrimeSet, Finset.mem_sdiff, mem_primesUpToReal]
      rw [highPrimeLevel_zero] at hlo
      exact ⟨⟨hp, hhi⟩, fun h => (not_le_of_gt hlo) h.2⟩
  | succ j ih =>
      by_cases hold : (X : ℝ) ^ highPrimeLevel j < p
      · rcases ih hold with hs | hg
        · exact Or.inl (Finset.mem_union_left _ hs)
        · exact Or.inr (Finset.mem_union_left _ hg)
      · have hle : (p : ℝ) ≤ (X : ℝ) ^ highPrimeLevel j := le_of_not_gt hold
        by_cases hblock : (p : ℝ) ≤ (X : ℝ) ^ highPrimeBlockUpper τ j
        · left
          exact Finset.mem_union_right _ ((mem_primeBandSet _ _ _ p).mpr ⟨hp, hlo, hblock⟩)
        · right
          exact Finset.mem_union_right _ ((mem_primeBandSet _ _ _ p).mpr ⟨hp, lt_of_not_ge hblock, hle⟩)

theorem omittedHighPrimes_bounds {X : ℕ} (hX : 1 ≤ X) (τ : ℝ) (j : ℕ) :
    ∀ p ∈ omittedHighPrimes X τ j, p.Prime ∧ (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  induction j with
  | zero => simp [omittedHighPrimes]
  | succ j ih =>
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ih p hp
      · obtain ⟨hprime, hlo, hhi⟩ := (mem_primeBandSet _ _ _ p).mp hp
        refine ⟨hprime, hhi.trans ?_⟩
        have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
        have hpow := Real.rpow_le_rpow_of_exponent_le hx
          (show highPrimeLevel j ≤ 1 / 2 by linarith [highPrimeLevel_le_quarter j])
        have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 : ℝ)
        linarith

theorem highPrimeGap_mass_eventually {τ ε : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2)
    (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      primeMass (primeBandSet X (highPrimeBlockUpper τ j) (highPrimeLevel j)) ≤
        -Real.log (1 - τ) + ε := by
  have hb := highPrimeBlock_bounds hτ0 hτ j
  have hlim := (prime_power_band_limit _ _ (hb.1.trans hb.2.1) (highPrimeLevel_pos j)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [highPrimeGap_log_mass hτ0.le (by linarith)] at hlim
  have hnear := (tendsto_order.mp hlim).2 (-Real.log (1 - τ) + ε) (by linarith)
  filter_upwards [hnear, eventually_ge_atTop (1 : ℕ)] with X hX hx
  rw [primeBandSet_mass (by exact_mod_cast hx) hb.2.2.1.le]
  exact hX.le

theorem omittedHighPrimes_mass_eventually {τ ε : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2)
    (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop, primeMass (omittedHighPrimes X τ j) ≤
      j * (-Real.log (1 - τ)) + ε := by
  induction j generalizing ε with
  | zero =>
      filter_upwards [] with X
      simpa [omittedHighPrimes, primeMass] using hε.le
  | succ j ih =>
      have hε2 : 0 < ε / 2 := by positivity
      filter_upwards [ih hε2, highPrimeGap_mass_eventually hτ0 hτ hε2 j] with X hprev hgap
      have hsum := primeMass_union_le (omittedHighPrimes X τ j)
        (primeBandSet X (highPrimeBlockUpper τ j) (highPrimeLevel j))
      change primeMass (omittedHighPrimes X τ (j + 1)) ≤ _ at hsum
      push_cast
      linarith

end Erdos676
