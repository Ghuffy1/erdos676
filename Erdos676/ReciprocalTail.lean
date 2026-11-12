import Erdos676.SingularFactors
import Mathlib.Analysis.PSeries

open scoped BigOperators

namespace Erdos676

theorem shifted_reciprocal_square_le (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ^ 2 ≤ 4 * ((p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hp0)).mpr
  nlinarith

theorem shifted_reciprocal_square_tail (s : Finset ℕ) (m n : ℕ)
    (hm : 1 ≤ m) (hn : m ≤ n) (hs : s ⊆ Finset.Ioc m n) :
    (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤ (4 : ℝ) / (m : ℝ) := by
  have hsum : (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤
      4 * ∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact shifted_reciprocal_square_le p (by have := (Finset.mem_Ioc.mp (hs hp)).1; omega)
  have hsub : (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹) ≤ ∑ p ∈ Finset.Ioc m n, ((p : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) hn
  have hinv : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hupper : (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by linarith
  simpa only [div_eq_mul_inv] using hsum.trans (mul_le_mul_of_nonneg_left hupper (by norm_num))

end Erdos676
