import Erdos676.InitialAvoidanceBound
import Erdos676.PrimeEndpointBounds
import Erdos676.PrimeReciprocalBounds

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem log_five_halves_lt_one : Real.log (5 / 2 : ℝ) < 1 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5 / 2)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem initial_prime_cutoff_bounds :
    ∀ᶠ X : ℝ in atTop, X ^ (6 / 25 : ℝ) < X ^ (1 / 4 : ℝ) ∧
      2 * X ^ (1 / 2 : ℝ) ≤ X ^ (3 / 5 : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop 2] with X hX hpow
  refine ⟨Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num), ?_⟩
  have h := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith : 0 ≤ X) (1 / 2 : ℝ))
  have heq : X ^ (1 / 2 : ℝ) * X ^ (1 / 10 : ℝ) = X ^ (3 / 5 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < X)]
    norm_num
  rw [heq] at h
  simpa only [mul_comm] using h

universe u

theorem initial_large_prime_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (a : P → ℕ) [∀ p, NeZero (a p)],
        (∀ p, (a p).Prime) → Function.Injective a →
        (∀ p, (X : ℝ) ^ (1 / 4 : ℝ) ≤ a p) →
        (∀ p, (a p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) →
        d * X ≤ (originalAvoidSet a ((X : ℤ) + 1) (2 * (X : ℤ))).card := by
  let d₀ := 1 - Real.log (5 / 2 : ℝ)
  have hd₀ : 0 < d₀ := by dsimp [d₀]; linarith [log_five_halves_lt_one]
  have hlimit := prime_power_band_limit (6 / 25 : ℝ) (3 / 5 : ℝ) (by norm_num) (by norm_num)
  have hlog : Real.log (3 / 5 : ℝ) - Real.log (6 / 25 : ℝ) = Real.log (5 / 2 : ℝ) := by
    rw [← Real.log_div (by norm_num : (3 / 5 : ℝ) ≠ 0) (by norm_num : (6 / 25 : ℝ) ≠ 0)]
    norm_num
  rw [hlog] at hlimit
  have hnear : ∀ᶠ X : ℝ in atTop, primeReciprocalSum (X ^ (3 / 5 : ℝ)) -
      primeReciprocalSum (X ^ (6 / 25 : ℝ)) < Real.log (5 / 2 : ℝ) + d₀ / 4 :=
    (tendsto_order.mp hlimit).2 _ (by linarith)
  refine ⟨d₀ / 2, by positivity, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hnear,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually initial_prime_cutoff_bounds,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (prime_endpoint_sum_small (by positivity : 0 < d₀ / 4)),
    eventually_ge_atTop (1 : ℕ)] with X hX hcuts hend hpos
  intro P instF instD a instN hprime hinj hlo hhi
  have horder' : (X : ℝ) ^ (6 / 25 : ℝ) ≤ (X : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by norm_num)
  have hmass := prime_family_reciprocal_band_le a hinj hprime _ _ horder'
    (fun p => hcuts.1.trans_le (hlo p)) (fun p => (hhi p).trans hcuts.2)
  have hsum := hend P a hinj hprime hhi
  have hlow := initial_avoidance_card_lower a hprime ((X : ℤ) + 1) X
  have heq : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  rw [heq] at hlow
  have hscaled := mul_le_mul_of_nonneg_left (hmass.trans hX.le) (Nat.cast_nonneg X)
  dsimp only [d₀] at *
  nlinarith

end Erdos676
