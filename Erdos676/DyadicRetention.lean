import Erdos676.CutoffParameters
import Mathlib.Analysis.Complex.Exponential

open Filter
open scoped Topology

namespace Erdos676

noncomputable def dyadicRetention : ℝ := 1 - Real.log 2

theorem log_two_lt_three_fourths : Real.log 2 < 3 / 4 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
  norm_num at h
  linarith

theorem dyadicRetention_bounds : (1 / 4 : ℝ) < dyadicRetention ∧ dyadicRetention < 1 := by
  have hlogpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  dsimp [dyadicRetention]
  constructor <;> linarith [log_two_lt_three_fourths]

theorem discreteCutoff_sq (L : ℕ) : (discreteCutoff L) ^ 2 = (1 / 4 : ℝ) ^ L := by
  unfold discreteCutoff
  rw [pow_two, ← mul_pow]
  norm_num

theorem exists_dyadic_retention_margin {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ L : ℕ, 3 ≤ L ∧ discreteCutoff L ≤ 1 / 200 ∧
      discreteCutoff L * (8 * L + 8 : ℕ) ≤ 1 / 2 ∧
      C * (discreteCutoff L) ^ 2 < c * dyadicRetention ^ L := by
  have hd : 0 < dyadicRetention := lt_trans (by norm_num) dyadicRetention_bounds.1
  let r := (1 / 4 : ℝ) / dyadicRetention
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hd).mpr dyadicRetention_bounds.1
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  have hsmall : ∀ᶠ L : ℕ in atTop, C * r ^ L < c := by
    exact (tendsto_order.mp (by simpa only [mul_zero] using hlim)).2 c hc
  have hcut : ∀ᶠ L : ℕ in atTop, discreteCutoff L < 1 / 200 :=
    (tendsto_order.mp discreteCutoff_tendsto).2 _ (by norm_num)
  have hdegree : ∀ᶠ L : ℕ in atTop, discreteCutoff L * (8 * L + 8 : ℕ) < 1 / 2 :=
    (tendsto_order.mp discreteCutoff_degree_tendsto).2 _ (by norm_num)
  obtain ⟨L, hL, hsmallL, hcutL, hdegreeL⟩ :=
    ((eventually_ge_atTop 3).and (hsmall.and (hcut.and hdegree))).exists
  refine ⟨L, hL, hcutL.le, hdegreeL.le, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hsmallL (pow_pos hd L)
  have hid : r ^ L * dyadicRetention ^ L = (discreteCutoff L) ^ 2 := by
    rw [← mul_pow, discreteCutoff_sq]
    dsimp [r]
    rw [div_mul_cancel₀ _ hd.ne']
  nlinarith [hid]

end Erdos676
