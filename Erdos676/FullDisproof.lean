import Erdos676.StableNaturalCenters
import Erdos676.FinalParameters
import Erdos676.OriginalSecondMoment
import Erdos676.QuantitativeGluing

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem eventual_exception_survival_lower :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * X * survivalProduct ((X : ℝ) ^ α) ≤ (dyadicExceptions X).card := by
  obtain ⟨d, hd, hd1, hcenters⟩ := stable_natural_centers
  obtain ⟨C, hC0, hC⟩ := exists_half_power_prime_mass_bound
  obtain ⟨L, hL, hsmall, hdegree, hmargin⟩ := final_parameter_choice hd C
  let α := discreteCutoff L
  let j := L - 2
  let γ := d * dyadicRetention ^ L
  let η := α * (1 - α ^ 2)
  have hα : 0 < α := discreteCutoff_pos L
  have hαsmall : α ≤ 1 / 200 := hsmall
  have hret0 : 0 < dyadicRetention := by linarith [dyadicRetention_bounds.1]
  have hγ : 0 < γ := mul_pos hd (pow_pos hret0 L)
  have hγ1 : γ ≤ 1 := by
    have hpow := pow_le_one₀ hret0.le dyadicRetention_bounds.2.le (n := L)
    dsimp [γ]
    nlinarith
  have hη : 0 < η := mul_pos hα (by dsimp [α] at hαsmall ⊢; nlinarith [sq_nonneg (discreteCutoff L)])
  have hηα : η < α := by
    dsimp [η]
    nlinarith [sq_pos_of_pos hα]
  have hlevel : highPrimeLevel j = α := by
    rw [highPrimeLevel_discrete]
    have hj : j + 2 = L := by dsimp [j]; omega
    rw [hj]
  have hηlevel : η < highPrimeLevel j := by rwa [hlevel]
  have hpow : dyadicRetention ^ L ≤ dyadicRetention ^ j :=
    pow_le_pow_of_le_one hret0.le dyadicRetention_bounds.2.le (by dsimp [j]; omega)
  have hfirstloss : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) < γ / 16 := by
    rw [truncation_loss_discrete]
    dsimp only [γ, α] at *
    have hs : 0 ≤ 40000 * (discreteCutoff L) ^ 2 := by positivity
    nlinarith
  have hsecondloss : 40000 * α ^ 2 < γ / 16 := by
    have hs : 0 ≤ (2 * Real.exp (4 * C)) * α ^ 2 := by positivity
    change 16 * (2 * Real.exp (4 * C) + 40000) * α ^ 2 < γ at hmargin
    nlinarith
  have hfirstsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1 := by linarith
  have hfirst := smallAverage_first_moment L hα (by omega) (show 0 < γ / 16 by positivity)
    hdegree hC hfirstsmall
  have hsecond := original_second_moment_quadratic hα hαsmall (show 0 < γ / 16 by positivity)
  have hH : ∀ᶠ X : ℕ in atTop, 0 < powerFloor η X :=
    ((powerFloor_tendsto hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 0
  refine ⟨α, γ / 8, hα, by positivity, ?_⟩
  filter_upwards [hcenters j η hηlevel, hfirst, hsecond, hH] with X hU hfirstX hsecondX hHX
  let U := stableNaturalCenters X j η
  let H := powerFloor η X
  let V := survivalProduct ((X : ℝ) ^ α)
  have hV : 0 ≤ V := (survivalProduct_pos _).le
  have hUsub : U ⊆ Finset.Ioc X (2 * X) := stableNaturalCenters_subset X j η
  have hsize : γ * X ≤ (U.card : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hpow hd.le
    have hscaledX := mul_le_mul_of_nonneg_right hscaled (Nat.cast_nonneg X)
    exact hscaledX.trans hU
  have hcomp : (((Finset.Ioc X (2 * X)) \ U).card : ℝ) ≤ (1 - γ) * X := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hUsub
    have hI : (Finset.Ioc X (2 * X)).card = X := by rw [Nat.card_Ioc]; omega
    rw [hI] at hsplit
    have hsplitR : (((Finset.Ioc X (2 * X)) \ U).card : ℝ) + U.card = X := by exact_mod_cast hsplit
    nlinarith
  have hfirstBound : (1 - γ / 8) * X * V ≤
      ∑ n ∈ Finset.Ioc X (2 * X), smallAverage ⌊(X : ℝ) ^ α⌋₊ H n := by
    have hcoef : 1 - γ / 8 ≤ 1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) - γ / 16 := by linarith
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg X)) hV).trans
      (hfirstX H hHX)
  have hsecondBound : (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage ⌊(X : ℝ) ^ α⌋₊ H n) ^ 2) ≤
      (1 + γ / 8) * X * V ^ 2 := by
    have hcoef : 1 + 40000 * α ^ 2 + γ / 16 ≤ 1 + γ / 8 := by linarith
    exact hsecondX.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg X)) (sq_nonneg V))
  apply quantitative_dyadic_count X ⌊(X : ℝ) ^ α⌋₊ H U hHX hUsub hV hγ.le hγ1
    (show 0 ≤ γ / 8 by positivity) le_rfl hfirstBound hsecondBound hcomp
  · intro n hn k hk
    have h := stableNaturalCenters_large_avoidance hn hk
    rwa [hlevel] at h
  · exact fun n hn k hk => stableNaturalCenters_shifts hn hk

theorem full_quantitative_disproof : QuantitativeDisproof := by
  obtain ⟨α, c, hα, hc, hcount⟩ := eventual_exception_survival_lower
  obtain ⟨v, hv, hsurvival⟩ := exists_eventual_survival_lower
  refine ⟨c * v / α, by positivity, ?_⟩
  have hsurvival' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((tendsto_rpow_atTop hα).eventually hsurvival)
  filter_upwards [hcount, hsurvival', eventually_ge_atTop (2 : ℕ)] with X hX hV hx
  have hx1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  rw [Real.log_rpow (zero_lt_one.trans hx1) α] at hV
  have hscaled := mul_le_mul_of_nonneg_left hV (show 0 ≤ c * (X : ℝ) by positivity)
  have heq : c * X * (v / (α * Real.log X)) = (c * v / α) * X / Real.log X := by ring
  rw [heq] at hscaled
  exact hscaled.trans hX

theorem full_disproof : ¬ EventualRepresentation :=
  quantitativeDisproof_implies_disproof full_quantitative_disproof

theorem full_unbounded_exceptions : UnboundedExceptions :=
  not_eventual_iff_unbounded.mp full_disproof

end Erdos676
