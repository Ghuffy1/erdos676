import Erdos676.BoxSmoothing
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Erdos676

noncomputable def residueFrequency {m : ℕ} [NeZero m] (k : ZMod m) : ℝ :=
  (k.valMinAbs : ℝ) / (m : ℝ)

noncomputable def residueCharacter {m : ℕ} [NeZero m] (k : ZMod m) : AddChar ℤ ℂ where
  toFun n := ZMod.stdAddChar (k * (n : ZMod m))
  map_zero_eq_one' := by simp [AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by rw [Int.cast_add, mul_add, AddChar.map_add_eq_mul]

theorem residueCharacter_norm {m : ℕ} [NeZero m] (k : ZMod m) (n : ℤ) :
    ‖residueCharacter k n‖ = 1 := norm_stdAddChar _

theorem residueCharacter_one {m : ℕ} [NeZero m] (k : ZMod m) :
    residueCharacter k 1 = ZMod.stdAddChar k := by simp [residueCharacter]

theorem abs_residueFrequency_le_half {m : ℕ} [NeZero m] (k : ZMod m) :
    |residueFrequency k| ≤ 1 / 2 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hlo : -(m : ℝ) < (k.valMinAbs : ℝ) * 2 := by exact_mod_cast k.valMinAbs_mem_Ioc.1
  have hhi : (k.valMinAbs : ℝ) * 2 ≤ m := by exact_mod_cast k.valMinAbs_mem_Ioc.2
  unfold residueFrequency
  rw [abs_div, abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  exact (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem residueFrequency_ne_zero {m : ℕ} [NeZero m] {k : ZMod m} (hk : k ≠ 0) :
    residueFrequency k ≠ 0 := by
  apply div_ne_zero
  · exact Int.cast_ne_zero.mpr (fun h => hk ((ZMod.valMinAbs_eq_zero k).mp h))
  · exact Nat.cast_ne_zero.mpr (NeZero.ne m)

theorem stdAddChar_frequency {m : ℕ} [NeZero m] (k : ZMod m) :
    ZMod.stdAddChar k = Complex.exp (Complex.I * ((2 * Real.pi * residueFrequency k : ℝ) : ℂ)) := by
  calc
    _ = ZMod.stdAddChar (k.valMinAbs : ZMod m) := congrArg ZMod.stdAddChar k.coe_valMinAbs.symm
    _ = Complex.exp (2 * Real.pi * Complex.I * k.valMinAbs / m) := ZMod.stdAddChar_coe _
    _ = _ := by congr 1; unfold residueFrequency; push_cast; ring

theorem stdAddChar_sub_one_lower {m : ℕ} [NeZero m] (k : ZMod m) :
    4 * |residueFrequency k| ≤ ‖ZMod.stdAddChar k - 1‖ := by
  have hfreq := abs_residueFrequency_le_half k
  have harg : |Real.pi * residueFrequency k| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hfreq Real.pi_pos.le
      _ = _ := by ring
  have hsin := Real.mul_abs_le_abs_sin harg
  have hcancel : 2 / Real.pi * |Real.pi * residueFrequency k| = 2 * |residueFrequency k| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hcancel] at hsin
  rw [stdAddChar_frequency, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have harg' : 2 * Real.pi * residueFrequency k / 2 = Real.pi * residueFrequency k := by ring
  rw [harg', abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem residue_boxMultiplier_decay {m : ℕ} [NeZero m] (k : ZMod m) (hk : k ≠ 0)
    (H : ℕ) (hH : 0 < H) :
    ‖boxMultiplier H (residueCharacter k)‖ ≤ 1 / ((H : ℝ) * |residueFrequency k|) := by
  have hk1 : ZMod.stdAddChar k ≠ 1 := by
    intro h
    apply hk
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using h
  have hc1 : residueCharacter k 1 ≠ 1 := by rwa [residueCharacter_one]
  have h := norm_boxMultiplier_decay H hH (residueCharacter k) (residueCharacter_norm k) hc1
  rw [residueCharacter_one] at h
  have hf : 0 < |residueFrequency k| := abs_pos.mpr (residueFrequency_ne_zero hk)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hnorm : 0 < ‖ZMod.stdAddChar k - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hk1)
  have hgap := stdAddChar_sub_one_lower k
  apply h.trans
  apply (div_le_div_iff₀ (mul_pos hHreal hnorm) (mul_pos hHreal hf)).mpr
  nlinarith

end Erdos676
