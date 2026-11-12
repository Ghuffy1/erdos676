import Erdos676.MertensRatios
import Erdos676.SurvivalLower

open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem exists_survival_ratio_log_bound :
    ∃ T : ℝ, 1 < T ∧ ∀ y z : ℝ, T ≤ y → T ≤ z →
      survivalProduct y / survivalProduct z ≤
        Real.exp 2 * (Real.log z / Real.log y) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hlo : ∀ᶠ y in atTop, (-1 : ℝ) < Mertens.E₃ y :=
    (tendsto_order.mp hE).1 _ (by norm_num)
  have hhi : ∀ᶠ y in atTop, Mertens.E₃ y < (1 : ℝ) :=
    (tendsto_order.mp hE).2 _ (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlo.and hhi)
  refine ⟨max 2 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro y z hy hz
  have hy1 : 1 < y := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hy)
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hz)
  have hyE := hT y ((le_max_right _ _).trans hy)
  have hzE := hT z ((le_max_right _ _).trans hz)
  rw [survival_ratio_formula hy1 hz1]
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (Real.log_pos hz1).le (Real.log_pos hy1).le)
  exact Real.exp_le_exp.mpr (by linarith)

theorem exists_singularMajorant_log_bound :
    ∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ y : ℝ, T ≤ y →
      singularMajorant (primesUpToReal y) ≤ C * Real.log y := by
  obtain ⟨c, hc, hevent⟩ := exists_eventual_survival_lower
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨c⁻¹, max 2 T, inv_pos.mpr hc,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro y hy
  have hy1 : 1 < y := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hy)
  have hV := hT y ((le_max_right _ _).trans hy)
  have hproduct := (div_le_iff₀ (Real.log_pos hy1)).mp hV
  rw [singularMajorant_primes]
  apply (inv_le_iff_one_le_mul₀ (survivalProduct_pos y)).mpr
  have hscaled := mul_le_mul_of_nonneg_left hproduct (inv_nonneg.mpr hc.le)
  simpa only [inv_mul_cancel₀ hc.ne', mul_comm, mul_left_comm, mul_assoc] using hscaled

end Erdos676
