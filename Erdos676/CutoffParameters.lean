import Erdos676.BlockParameters
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped Topology

namespace Erdos676

noncomputable def discreteCutoff (L : ℕ) : ℝ := (1 / 2 : ℝ) ^ L

theorem discreteCutoff_pos (L : ℕ) : 0 < discreteCutoff L := by
  unfold discreteCutoff
  positivity

theorem discreteCutoff_tendsto : Tendsto discreteCutoff atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem discreteCutoff_degree_tendsto :
    Tendsto (fun L : ℕ => discreteCutoff L * (8 * L + 8 : ℕ)) atTop (nhds (0 : ℝ)) := by
  have hlinear := tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h := (hlinear.const_mul 8).add (discreteCutoff_tendsto.const_mul 8)
  convert h using 1
  · ext L
    simp only [discreteCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · norm_num

theorem truncation_loss_discrete (C : ℝ) (L : ℕ) :
    2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) =
      (2 * Real.exp (4 * C)) * (discreteCutoff L) ^ 2 := by
  unfold discreteCutoff
  rw [← pow_mul, Nat.mul_comm L 2, one_div_pow]
  ring

theorem exists_discrete_cutoff_parameters {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ L : ℕ, 1 ≤ L ∧ discreteCutoff L < 1 / 4 ∧
      discreteCutoff L * (8 * L + 8 : ℕ) ≤ 1 / 2 ∧
      C * (discreteCutoff L) ^ 2 < (c / 8) * discreteCutoff L := by
  have hsmall : ∀ᶠ L in atTop, discreteCutoff L < min (1 / 4) (c / (8 * C)) :=
    (tendsto_order.mp discreteCutoff_tendsto).2 _ (lt_min (by norm_num) (by positivity))
  have hdegree : ∀ᶠ L in atTop, discreteCutoff L * (8 * L + 8 : ℕ) < (1 / 2 : ℝ) :=
    (tendsto_order.mp discreteCutoff_degree_tendsto).2 _ (by norm_num)
  obtain ⟨L, hL, hs, hd⟩ := ((eventually_ge_atTop 1).and (hsmall.and hdegree)).exists
  refine ⟨L, hL, lt_of_lt_of_le hs (min_le_left _ _), hd.le, ?_⟩
  have hratio := lt_of_lt_of_le hs (min_le_right _ _)
  have hprod := (lt_div_iff₀ (by positivity : 0 < 8 * C)).mp hratio
  have hscaled := mul_lt_mul_of_pos_right hprod (discreteCutoff_pos L)
  nlinarith

end Erdos676
