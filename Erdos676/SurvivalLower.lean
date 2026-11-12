import Erdos676.MertensInputs
import Erdos676.PowerCutoffs

open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem exists_eventual_survival_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c / Real.log x ≤ survivalProduct x := by
  let c := Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-1)
  have hlimit : Tendsto Mertens.E₃ atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hevent : ∀ᶠ x : ℝ in atTop, (-1 : ℝ) < Mertens.E₃ x :=
    (tendsto_order.mp hlimit).1 _ (by norm_num)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [hevent, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [survivalProduct_formula hx1]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx1).le
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.le) (Real.exp_pos _).le

theorem eventually_power_error_absorbed {α β C η : ℝ}
    (hα : 0 < α) (hβ : β < 1) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, C * x ^ β ≤ η * x * survivalProduct (x ^ α) := by
  obtain ⟨c, hc, hsurvival⟩ := exists_eventual_survival_lower
  have hlog := eventually_log_le_power (by linarith : 0 < 1 - β)
    (div_pos (mul_pos hη hc) (mul_pos hC hα))
  have hsurvival' := (tendsto_rpow_atTop hα).eventually hsurvival
  filter_upwards [hlog, hsurvival', eventually_gt_atTop (1 : ℝ)] with x hxlog hxV hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hden : 0 < α * Real.log x := mul_pos hα (Real.log_pos hx1)
  rw [Real.log_rpow hx0 α] at hxV
  have hpower : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx0, show β + (1 - β) = 1 by ring, Real.rpow_one]
  have hcancel : (C * α) * (η * c / (C * α)) = η * c := by
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hxlog
    (by positivity : 0 ≤ C * α * x ^ β)
  have hrhs : (C * α * x ^ β) * (η * c / (C * α) * x ^ (1 - β)) = η * c * x := by
    calc
      _ = ((C * α) * (η * c / (C * α))) * (x ^ β * x ^ (1 - β)) := by ring
      _ = _ := by rw [hcancel, hpower]
  rw [hrhs] at hscaled
  have hfirst : C * x ^ β ≤ η * c * x / (α * Real.log x) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hscaled]
  calc
    _ ≤ η * c * x / (α * Real.log x) := hfirst
    _ = (η * x) * (c / (α * Real.log x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hxV (mul_nonneg hη.le hx0.le)

end Erdos676
