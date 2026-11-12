import Erdos676.FourierPowers

open Filter
open scoped Topology BigOperators

namespace Erdos676

theorem fourier_threshold_product_le {x β ε η : ℝ} (hx : 0 < x)
    (hH : x ^ η / 2 ≤ (powerFloor η x : ℝ)) (hrelation : η = β + 2 * ε) :
    fourierThreshold η ε x * x ^ β ≤ 2 * x ^ (-ε) := by
  have h := div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le ε)
    (show 0 < x ^ η / 2 by positivity) hH
  have hscaled := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le β)
  have heq : (x ^ ε / (x ^ η / 2)) * x ^ β = 2 * x ^ (-ε) := by
    calc
      _ = 2 * ((x ^ β * x ^ ε) / x ^ η) := by ring
      _ = 2 * x ^ (β + ε - η) := by rw [← Real.rpow_add hx, ← Real.rpow_sub hx]
      _ = _ := by congr 1; congr 1; linarith
  exact hscaled.trans_eq heq

theorem growing_fourier_cutoffs {β ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hrelation : η = β + 2 * ε) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 0 < powerFloor η x ∧
      x ^ η / 2 ≤ (powerFloor η x : ℝ) ∧ 0 < fourierThreshold η ε x ∧
      fourierThreshold η ε x * x ^ β < 1 := by
  have hlimit := (tendsto_rpow_neg_atTop hε).const_mul (2 : ℝ)
  have hsmall : ∀ᶠ x : ℝ in atTop, 2 * x ^ (-ε) < 1 :=
    (tendsto_order.mp (by simpa only [mul_zero] using hlimit)).2 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_powerFloor_half hη, hsmall]
    with x hx hhalf htail
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hHreal : (0 : ℝ) < powerFloor η x := lt_of_lt_of_le (by positivity : 0 < x ^ η / 2) hhalf
  have hHnat : 0 < powerFloor η x := by exact_mod_cast hHreal
  refine ⟨hx, hHnat, hhalf, div_pos (Real.rpow_pos_of_pos hx0 ε) hHreal, ?_⟩
  exact (fourier_threshold_product_le hx0 hhalf hrelation).trans_lt htail

universe u

theorem growing_prime_band_energy {β ε η : ℝ} (hβ : 0 < β) (hβsmall : β ≤ 1 / 4)
    (hε : 0 < ε) (hrelation : η = β + 2 * ε) :
    ∃ J : ℕ, ∀ᶠ X : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (a : P → ℕ) [∀ p, NeZero (a p)],
        (∀ p, (a p).Prime) → Function.Injective a → (∀ p, (a p : ℝ) ≤ (X : ℝ) ^ β) →
        ∀ S : ℤ,
          (∑ n ∈ Finset.range (4 * X),
            ‖boxSmooth (powerFloor η X) J (primeBandSignal a) (S + n) -
              (∑ p : P, 1 / (a p : ℂ))‖ ^ 2) ≤ 8200 * (X : ℝ) ^ (1 - ε) := by
  have hη : 0 < η := by linarith
  obtain ⟨J, hJ⟩ := exists_nat_gt ((4 * β + ε) / (2 * ε))
  have hJ' : 4 * β + ε ≤ ε * (2 * J : ℕ) := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * ε)).mp hJ
    push_cast
    nlinarith
  refine ⟨J, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (growing_fourier_cutoffs hε hη hrelation)] with X hX
  obtain ⟨hx, hH, hhalf, hD, hcut⟩ := hX
  intro P instF instD a instN hprime hinj hle S
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans_le hx
  have hXN : 0 < X := by exact_mod_cast hx0
  have hsize : ((X : ℝ) ^ β) ^ 4 ≤ (X : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
    have hpow := Real.rpow_le_rpow_of_exponent_le hx (show β * (4 : ℝ) ≤ 1 by linarith)
    simpa only [Real.rpow_one, Nat.cast_ofNat] using hpow
  have h := smoothed_prime_band_energy_size a hprime hinj ((X : ℝ) ^ β)
    (fourierThreshold η ε X) (Real.rpow_nonneg (Nat.cast_nonneg X) β) hD hle hcut
    (powerFloor η X) J (4 * X) hH (by omega) S (by push_cast; nlinarith)
  have herr := fourier_error_bound hx hhalf hrelation J hJ'
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  exact h.trans herr

end Erdos676
