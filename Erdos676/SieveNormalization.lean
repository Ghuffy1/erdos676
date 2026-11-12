import Erdos676.PrimeLogMoments

open scoped BigOperators

namespace Erdos676

theorem reciprocal_bound_of_relative_loss {G V e : ℝ}
    (hG : 0 < G) (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hbound : 1 - e ≤ G * V) :
    1 / G ≤ (1 + 2 * e) * V := by
  apply (div_le_iff₀ hG).mpr
  have hprod := mul_le_mul_of_nonneg_left hbound (by linarith : 0 ≤ 1 + 2 * e)
  have hs : 0 ≤ e * (1 - 2 * e) := mul_nonneg he (by linarith)
  nlinarith

/-- Turning a square-moment tail bound into the relative inverse estimate used by the sieve. -/
theorem inverse_normalizer_bound {G V R L : ℝ}
    (hG : 0 < G) (hR : 0 < R)
    (hsmall : 20 * L ^ 2 ≤ R ^ 2 / 2)
    (htail : (1 - G * V) * R ^ 2 ≤ 20 * L ^ 2) :
    1 / G ≤ (1 + 40 * (L / R) ^ 2) * V := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hratio : 20 * (L / R) ^ 2 = (20 * L ^ 2) / R ^ 2 := by ring
  have he0 : 0 ≤ 20 * (L / R) ^ 2 := by positivity
  have hehalf : 20 * (L / R) ^ 2 ≤ 1 / 2 := by
    rw [hratio]
    exact (div_le_iff₀ hR2).mpr (by linarith)
  have hbound : 1 - 20 * (L / R) ^ 2 ≤ G * V := by
    have hdiv := (le_div_iff₀ hR2).mpr htail
    rw [← hratio] at hdiv
    linarith
  have h := reciprocal_bound_of_relative_loss hG he0 hehalf hbound
  convert h using 1
  ring

end Erdos676
