import Erdos676.Gluing

namespace Erdos676

/-- Quantitative first and second moment bounds imply the strict gap needed for gluing. -/
theorem moment_gap_from_bounds {A Q K N V d e : ℝ}
    (hN : 0 < N) (hV : 0 < V) (hQ : 0 ≤ Q)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (he1 : e < 1)
    (hsmall : 3 * e < d)
    (hfirst : (1 - e) * N * V ≤ A)
    (hsecond : Q ≤ (1 + e) * N * V ^ 2)
    (hcomplement : K ≤ (1 - d) * N) :
    0 < A ∧ K * Q < A ^ 2 := by
  have hpositive : 0 < (1 - e) * N * V :=
    mul_pos (mul_pos (sub_pos.mpr he1) hN) hV
  have hA : 0 < A := lt_of_lt_of_le hpositive hfirst
  refine ⟨hA, ?_⟩
  have hcompare := scalar_moment_gap hd he hsmall
  have hscale : 0 < N ^ 2 * V ^ 2 := mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hV)
  have hscaled := mul_lt_mul_of_pos_right hcompare hscale
  calc
    K * Q ≤ ((1 - d) * N) * ((1 + e) * N * V ^ 2) :=
      mul_le_mul hcomplement hsecond hQ (mul_nonneg (sub_nonneg.mpr hd1) hN.le)
    _ < ((1 - e) * N * V) ^ 2 := by nlinarith [hscaled]
    _ ≤ A ^ 2 := by nlinarith

/-- A fixed positive cutoff can always separate a linear gain from quadratic losses. -/
theorem exists_linear_quadratic_margin {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ α : ℝ, 0 < α ∧ c * α ≤ 1 ∧ 0 ≤ C * α ^ 2 ∧ C * α ^ 2 < 1 ∧
      3 * (C * α ^ 2) < c * α := by
  let α := min (1 / (2 * c)) (c / (6 * C))
  have hα : 0 < α := lt_min (div_pos (by norm_num) (by positivity))
    (div_pos hc (by positivity))
  have hleft : α * (2 * c) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * c)).mp (min_le_left _ _)
  have hright : α * (6 * C) ≤ c :=
    (le_div_iff₀ (by positivity : 0 < 6 * C)).mp (min_le_right _ _)
  have hpos : 0 < 3 * C * α := by positivity
  have hfirst : 3 * C * α < c := by nlinarith
  have hgap : 3 * (C * α ^ 2) < c * α := by
    have := mul_lt_mul_of_pos_right hfirst hα
    nlinarith
  refine ⟨α, hα, ?_, mul_nonneg hC.le (sq_nonneg α), ?_, hgap⟩ <;> nlinarith

end Erdos676
