import Erdos676.ResidueFrequency
import Erdos676.PairCharacterKernel

namespace Erdos676

noncomputable def realCharacter (θ : ℝ) : AddChar ℤ ℂ where
  toFun n := Complex.exp (Complex.I * ((2 * Real.pi * θ * (n : ℝ) : ℝ) : ℂ))
  map_zero_eq_one' := by simp
  map_add_eq_mul' n k := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem realCharacter_norm (θ : ℝ) (n : ℤ) : ‖realCharacter θ n‖ = 1 := by
  simp [realCharacter, Complex.norm_exp, Complex.mul_re]

theorem realCharacter_one (θ : ℝ) :
    realCharacter θ 1 = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
  simp [realCharacter]

theorem realCharacter_gap (θ : ℝ) (hθ : |θ| ≤ 1 / 2) :
    4 * |θ| ≤ ‖realCharacter θ 1 - 1‖ := by
  have harg : |Real.pi * θ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hθ Real.pi_pos.le
      _ = _ := by ring
  have hsin := Real.mul_abs_le_abs_sin harg
  have hcancel : 2 / Real.pi * |Real.pi * θ| = 2 * |θ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hcancel] at hsin
  rw [realCharacter_one, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  rw [show 2 * Real.pi * θ / 2 = Real.pi * θ by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem realCharacter_difference (θ φ : ℝ) (n : ℤ) :
    star (realCharacter θ n) * realCharacter φ n = realCharacter (φ - θ) n := by
  have hinv := Complex.inv_eq_conj (realCharacter_norm θ n)
  rw [starRingEnd_apply] at hinv
  rw [← hinv, mul_comm, ← div_eq_mul_inv]
  change Complex.exp _ / Complex.exp _ = Complex.exp _
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem residueCharacter_eq_realCharacter {m : ℕ} [NeZero m] (k : ZMod m) :
    residueCharacter k = realCharacter (residueFrequency k) := by
  apply AddChar.ext
  intro n
  have hleft : residueCharacter k n = (residueCharacter k 1) ^ n := by
    simpa using (residueCharacter k).map_zsmul_eq_zpow n (1 : ℤ)
  have hright : realCharacter (residueFrequency k) n = (realCharacter (residueFrequency k) 1) ^ n := by
    simpa using (realCharacter (residueFrequency k)).map_zsmul_eq_zpow n (1 : ℤ)
  rw [hleft, hright, residueCharacter_one, realCharacter_one, stdAddChar_frequency]

end Erdos676
