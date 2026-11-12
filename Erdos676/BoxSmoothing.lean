import Erdos676.ResidueFourier
import Mathlib.Algebra.Field.GeomSum

open scoped BigOperators

namespace Erdos676

noncomputable def boxMean (H : ℕ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  (∑ h ∈ Finset.range H, f (n + h)) / (H : ℂ)

noncomputable def boxMultiplier (H : ℕ) (χ : AddChar ℤ ℂ) : ℂ :=
  (∑ h ∈ Finset.range H, χ h) / (H : ℂ)

noncomputable def boxSmooth (H : ℕ) : ℕ → (ℤ → ℂ) → (ℤ → ℂ)
  | 0, f => f
  | J + 1, f => boxMean H (boxSmooth H J f)

theorem boxMean_add (H : ℕ) (f g : ℤ → ℂ) (n : ℤ) :
    boxMean H (fun k => f k + g k) n = boxMean H f n + boxMean H g n := by
  simp only [boxMean, Finset.sum_add_distrib, add_div]

theorem boxMean_const_mul (H : ℕ) (c : ℂ) (f : ℤ → ℂ) (n : ℤ) :
    boxMean H (fun k => c * f k) n = c * boxMean H f n := by
  simp only [boxMean, ← Finset.mul_sum]
  ring

theorem boxMean_character (H : ℕ) (χ : AddChar ℤ ℂ) (n : ℤ) :
    boxMean H χ n = boxMultiplier H χ * χ n := by
  simp only [boxMean, boxMultiplier, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  ring

theorem boxSmooth_character (H J : ℕ) (χ : AddChar ℤ ℂ) (n : ℤ) :
    boxSmooth H J χ n = (boxMultiplier H χ) ^ J * χ n := by
  induction J generalizing n with
  | zero => simp only [boxSmooth, pow_zero, one_mul]
  | succ J ih =>
      change boxMean H (boxSmooth H J χ) n = _
      have hfun : boxSmooth H J χ = fun k => (boxMultiplier H χ) ^ J * χ k := funext ih
      rw [hfun, boxMean_const_mul, boxMean_character, pow_succ]
      ring

theorem norm_boxMultiplier_le_one (H : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) : ‖boxMultiplier H χ‖ ≤ 1 := by
  unfold boxMultiplier
  rw [norm_div, Complex.norm_natCast]
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_one hHreal).mpr
  calc
    _ ≤ ∑ h ∈ Finset.range H, ‖χ h‖ := norm_sum_le _ _
    _ = _ := by simp only [hχ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem norm_boxMultiplier_decay (H : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) :
    ‖boxMultiplier H χ‖ ≤ 2 / ((H : ℝ) * ‖χ 1 - 1‖) := by
  have hpow (h : ℕ) : χ (h : ℤ) = (χ 1) ^ h := by
    simpa only [nsmul_eq_mul, mul_one] using χ.map_nsmul_eq_pow h (1 : ℤ)
  have hgeom : (∑ h ∈ Finset.range H, χ (h : ℤ)) = ((χ 1) ^ H - 1) / (χ 1 - 1) := by
    simp_rw [hpow]
    exact geom_sum_eq hχ1 H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hdiff : 0 < ‖χ 1 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hχ1)
  have hnum : ‖(χ 1) ^ H - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(χ 1) ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hχ, norm_one, one_pow]; norm_num
  unfold boxMultiplier
  rw [hgeom, norm_div, norm_div, Complex.norm_natCast, div_div]
  simpa only [mul_comm] using div_le_div_of_nonneg_right hnum (mul_pos hdiff hHreal).le

theorem norm_boxSmooth_character_le (H J : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (n : ℤ) : ‖boxSmooth H J χ n‖ ≤ 1 := by
  rw [boxSmooth_character, norm_mul, norm_pow, hχ, mul_one]
  exact pow_le_one₀ (norm_nonneg _) (norm_boxMultiplier_le_one H hH χ hχ)

theorem norm_boxSmooth_character_decay (H J : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) (n : ℤ) :
    ‖boxSmooth H J χ n‖ ≤ (2 / ((H : ℝ) * ‖χ 1 - 1‖)) ^ J := by
  rw [boxSmooth_character, norm_mul, norm_pow, hχ, mul_one]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_boxMultiplier_decay H hH χ hχ hχ1) J

end Erdos676
