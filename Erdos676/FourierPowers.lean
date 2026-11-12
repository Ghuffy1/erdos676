import Erdos676.PrimeBandSize
import Erdos676.GrowingDyadic

open Filter
open scoped Topology

namespace Erdos676

noncomputable def fourierThreshold (η ε x : ℝ) : ℝ := x ^ ε / (powerFloor η x : ℝ)

theorem fourier_first_term_bound {x H β ε η : ℝ} (hx : 0 < x)
    (hH : x ^ η / 2 ≤ H) :
    1024 * (4 * x) * x ^ β * (x ^ ε / H) ≤ 8192 * x ^ (1 + β + ε - η) := by
  have hp : 0 < x ^ η / 2 := by positivity
  have hden := div_le_div_of_nonneg_left
    (show 0 ≤ 4096 * x * x ^ β * x ^ ε by positivity) hp hH
  have hproduct : x * x ^ β * x ^ ε = x ^ (1 + β + ε) := by
    rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
  calc
    _ = (4096 * x * x ^ β * x ^ ε) / H := by ring
    _ ≤ (4096 * x * x ^ β * x ^ ε) / (x ^ η / 2) := hden
    _ = 8192 * (x * x ^ β * x ^ ε / x ^ η) := by ring
    _ = _ := by rw [hproduct, ← Real.rpow_sub hx]

theorem fourier_tail_term_identity {x H β ε : ℝ} (hx : 0 < x) (hH : H ≠ 0) (J : ℕ) :
    2 * (4 * x) * (x ^ β) ^ 4 * (1 / (H * (x ^ ε / H))) ^ (2 * J) =
      8 * x ^ (1 + 4 * β - ε * (2 * J : ℕ)) := by
  have hcancel : H * (x ^ ε / H) = x ^ ε := by field_simp
  have hp : (1 / x ^ ε) ^ (2 * J) = x ^ (-ε * (2 * J : ℕ)) := by
    calc
      _ = (x ^ (-ε)) ^ (2 * J) := by rw [Real.rpow_neg hx.le, one_div]
      _ = (x ^ (-ε)) ^ ((2 * J : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = _ := (Real.rpow_mul hx.le _ _).symm
  have hfour : (x ^ β) ^ 4 = x ^ (4 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    norm_num
    ring
  rw [hcancel, hp, hfour]
  have hproduct : x * x ^ (4 * β) * x ^ (-ε * (2 * J : ℕ)) =
      x ^ (1 + 4 * β - ε * (2 * J : ℕ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
    congr 1
    ring
  calc
    _ = 8 * (x * x ^ (4 * β) * x ^ (-ε * (2 * J : ℕ))) := by ring
    _ = _ := by rw [hproduct]

theorem fourier_error_bound {x H β ε η : ℝ} (hx : 1 ≤ x)
    (hH : x ^ η / 2 ≤ H) (hrelation : η = β + 2 * ε)
    (J : ℕ) (hJ : 4 * β + ε ≤ ε * (2 * J : ℕ)) :
    1024 * (4 * x) * x ^ β * (x ^ ε / H) +
      2 * (4 * x) * (x ^ β) ^ 4 * (1 / (H * (x ^ ε / H))) ^ (2 * J) ≤
        8200 * x ^ (1 - ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity : 0 < x ^ η / 2) hH
  have hfirst := fourier_first_term_bound hx0 hH (β := β) (ε := ε)
  have hexponent : 1 + β + ε - η = 1 - ε := by linarith
  rw [hexponent] at hfirst
  rw [fourier_tail_term_identity hx0 hH0.ne' J]
  have hpower := Real.rpow_le_rpow_of_exponent_le hx
    (show 1 + 4 * β - ε * (2 * J : ℕ) ≤ 1 - ε by linarith)
  linarith

end Erdos676
