import Erdos676.SmallCorrelations
import Erdos676.GrowingDyadic
import Erdos676.SecondMomentAverage

open Filter
open scoped Topology

namespace Erdos676

theorem pairSurvivalProduct_nonneg (z : ℝ) (k : ℤ) : 0 ≤ pairSurvivalProduct z k := by
  unfold pairSurvivalProduct
  apply Finset.prod_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  exact sub_nonneg.mpr (twoPositionDensity_le_one p hprime.one_lt.le _)

theorem eventually_pair_cutoff_conditions {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hsmall : 20 * α ≤ ρ) :
    ∀ᶠ x : ℝ in atTop,
      2 ≤ x ^ α ∧ 2 ≤ powerFloor ρ x ∧ Real.log 4 + 4 ≤ Real.log (x ^ α) ∧
      20 * (Real.log (x ^ α)) ^ 2 ≤ (Real.log (powerFloor ρ x : ℝ)) ^ 2 / 2 ∧
      1 + 40 * (Real.log (x ^ α) / Real.log (powerFloor ρ x : ℝ)) ^ 2 ≤
        1 + 160 * (α / ρ) ^ 2 := by
  have hz := (tendsto_rpow_atTop hα).eventually_ge_atTop 2
  have hR := (tendsto_rpow_atTop hρ).eventually_ge_atTop 3
  have hlogz := (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hα)).eventually_ge_atTop (Real.log 4 + 4)
  filter_upwards [hz, hR, hlogz, eventually_log_powerFloor_lower hρ,
    eventually_gt_atTop (1 : ℝ)] with x hxz hxR hxlogz hxlogR hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hxlog : 0 < Real.log x := Real.log_pos hx1
  have hR2 : 2 ≤ powerFloor ρ x := Nat.le_floor (by linarith : (2 : ℝ) ≤ x ^ ρ)
  have hlogRpos : 0 < Real.log (powerFloor ρ x : ℝ) :=
    lt_of_lt_of_le (mul_pos (div_pos hρ (by norm_num)) hxlog) hxlogR
  have hlogzpos : 0 ≤ Real.log (x ^ α) := by rw [Real.log_rpow hx0 α]; positivity
  have hten : 10 * Real.log (x ^ α) ≤ Real.log (powerFloor ρ x : ℝ) := by
    have hs := mul_le_mul_of_nonneg_right hsmall hxlog.le
    rw [Real.log_rpow hx0 α]
    nlinarith
  have hsq : 20 * (Real.log (x ^ α)) ^ 2 ≤ (Real.log (powerFloor ρ x : ℝ)) ^ 2 / 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hten)
      (by linarith : 0 ≤ Real.log (powerFloor ρ x : ℝ) + 10 * Real.log (x ^ α))
    nlinarith [sq_nonneg (Real.log (x ^ α))]
  have hratio : Real.log (x ^ α) / Real.log (powerFloor ρ x : ℝ) ≤ 2 * α / ρ := by
    apply (div_le_div_iff₀ hlogRpos hρ).mpr
    have hs := mul_le_mul_of_nonneg_left hxlogR (by positivity : 0 ≤ 2 * α)
    rw [Real.log_rpow hx0 α]
    nlinarith
  have hratio0 : 0 ≤ Real.log (x ^ α) / Real.log (powerFloor ρ x : ℝ) :=
    div_nonneg hlogzpos hlogRpos.le
  have hratio2 : 0 ≤ 2 * α / ρ := by positivity
  have hsquare := mul_nonneg (sub_nonneg.mpr hratio) (add_nonneg hratio2 hratio0)
  refine ⟨hxz, hR2, hxlogz, hsq, ?_⟩
  have hnormalize : (2 * α / ρ) ^ 2 = 4 * (α / ρ) ^ 2 := by ring
  nlinarith [hnormalize]

theorem smallPairCount_growing_upper {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hsmall : 20 * α ≤ ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ S i j : ℕ,
      smallPairCount ⌊(N : ℝ) ^ α⌋₊ S N i j ≤
        (1 + 160 * (α / ρ) ^ 2) * N * pairSurvivalProduct ((N : ℝ) ^ α) ((j : ℤ) - i) +
          (N : ℝ) ^ (8 * ρ) := by
  have hconditions := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_pair_cutoff_conditions hα hρ hsmall)
  filter_upwards [hconditions] with N hN
  intro S i j
  obtain ⟨hz, hR, hlarge, hsize, hcoef⟩ := hN
  have h := smallPairCount_sieve_bound ((N : ℝ) ^ α) hz (powerFloor ρ N) S N i j
    hR hlarge hsize
  have hV := pairSurvivalProduct_nonneg ((N : ℝ) ^ α) ((j : ℤ) - i)
  have hscaled := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Nat.cast_nonneg N) hV)
  have herror := powerFloor_power_le (Nat.cast_nonneg N) ρ 8
  have herror' : (powerFloor ρ N : ℝ) ^ 8 ≤ (N : ℝ) ^ (8 * ρ) := by
    simpa only [Nat.cast_ofNat, mul_comm] using herror
  nlinarith

theorem smallAverage_second_moment_reduction {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hsmall : 20 * α ≤ ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, 0 < H →
      (∑ n ∈ Finset.Ioc N (2 * N), (smallAverage ⌊(N : ℝ) ^ α⌋₊ H n) ^ 2) ≤
        (1 + 160 * (α / ρ) ^ 2) * N *
          ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
            pairSurvivalProduct ((N : ℝ) ^ α) ((j : ℤ) - i)) / (H : ℝ) ^ 2) +
          (N : ℝ) ^ (8 * ρ) := by
  filter_upwards [smallPairCount_growing_upper hα hρ hsmall] with N hN
  intro H hH
  rw [sum_dyadic_interval_eq_range]
  exact smallAverage_second_upper _ H (N + 1) N hH
    (fun i j => pairSurvivalProduct ((N : ℝ) ^ α) ((j : ℤ) - i))
    ((1 + 160 * (α / ρ) ^ 2) * N) ((N : ℝ) ^ (8 * ρ))
    (fun i hi j hj => hN (N + 1) i j)

end Erdos676
