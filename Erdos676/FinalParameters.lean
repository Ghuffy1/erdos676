import Erdos676.FirstMomentAsymptotic
import Erdos676.DyadicRetention

namespace Erdos676

theorem first_moment_loss_dyadic (C : ℝ) (L : ℕ) :
    2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) =
      (2 * Real.exp (4 * C)) * (discreteCutoff L) ^ 2 := by
  rw [discreteCutoff_sq]
  simp only [pow_mul, div_pow, one_pow]
  norm_num
  ring

theorem final_parameter_choice {d : ℝ} (hd : 0 < d) (C : ℝ) :
    ∃ L : ℕ, 3 ≤ L ∧ discreteCutoff L ≤ 1 / 200 ∧
      discreteCutoff L * (8 * L + 8 : ℕ) ≤ 1 / 2 ∧
      16 * (2 * Real.exp (4 * C) + 40000) * (discreteCutoff L) ^ 2 < d * dyadicRetention ^ L := by
  exact exists_dyadic_retention_margin hd (by positivity)

end Erdos676
