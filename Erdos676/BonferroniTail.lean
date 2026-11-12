import Erdos676.BonferroniModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace Erdos676

theorem scaled_elementary_sum_le {P : Type*} [DecidableEq P]
    (s : Finset P) (g : P → ℝ) (k : ℕ) (hg : ∀ p ∈ s, 0 ≤ g p) :
    (2 : ℝ) ^ k * (∑ d ∈ s.powersetCard k, ∏ p ∈ d, g p) ≤
      ∏ p ∈ s, (1 + 2 * g p) := by
  calc
    _ = ∑ d ∈ s.powersetCard k, ∏ p ∈ d, (2 * g p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hd).2]
    _ ≤ ∑ d ∈ s.powerset, ∏ p ∈ d, (2 * g p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hd).1
      · intro d hd _
        exact Finset.prod_nonneg (fun p hp => mul_nonneg (by norm_num)
          (hg p (Finset.mem_powerset.mp hd hp)))
    _ = ∏ p ∈ s, (1 + 2 * g p) := by
      simpa only [Finset.prod_const_one, mul_one, add_comm] using
        (Finset.prod_add (fun p => 2 * g p) (fun _ => (1 : ℝ)) s).symm

theorem elementary_sum_geometric_bound {P : Type*} [DecidableEq P]
    (s : Finset P) (g : P → ℝ) (k : ℕ) (C : ℝ)
    (hg : ∀ p ∈ s, 0 ≤ g p) (hC : (∑ p ∈ s, g p) ≤ C) :
    (∑ d ∈ s.powersetCard k, ∏ p ∈ d, g p) ≤ Real.exp (2 * C) / (2 : ℝ) ^ k := by
  have hprod : (∏ p ∈ s, (1 + 2 * g p)) ≤ Real.exp (2 * C) := by
    calc
      _ ≤ ∏ p ∈ s, Real.exp (2 * g p) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact add_nonneg (by norm_num) (mul_nonneg (by norm_num) (hg p hp))
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (2 * g p)
      _ = Real.exp (∑ p ∈ s, 2 * g p) := (Real.exp_sum _ _).symm
      _ = Real.exp (2 * ∑ p ∈ s, g p) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (2 * C) := Real.exp_le_exp.mpr (by linarith)
  have h := (scaled_elementary_sum_le s g k hg).trans hprod
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mpr
  simpa only [mul_comm] using h

theorem exp_neg_two_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : -2 * x ≤ Real.log (1 - x) := by linarith
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr he

theorem survival_product_lower {P : Type*} (s : Finset P) (g : P → ℝ) (C : ℝ)
    (hg0 : ∀ p ∈ s, 0 ≤ g p) (hg1 : ∀ p ∈ s, g p ≤ 1 / 2)
    (hC : (∑ p ∈ s, g p) ≤ C) :
    Real.exp (-2 * C) ≤ ∏ p ∈ s, (1 - g p) := by
  calc
    _ ≤ Real.exp (-2 * ∑ p ∈ s, g p) := Real.exp_le_exp.mpr (by linarith)
    _ = ∏ p ∈ s, Real.exp (-2 * g p) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le)
      (fun p hp => exp_neg_two_le_one_sub (hg0 p hp) (hg1 p hp))

end Erdos676
