import Erdos676.LocalFactors
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

namespace Erdos676

noncomputable def normalizedFactor (p a : ℝ) : ℝ := 1 + (a - 1) / (p - 1) ^ 2

theorem normalizedFactor_formula (p a : ℝ) (hp : 2 ≤ p) :
    normalizedFactor p a = (1 - 2 / p + a / p ^ 2) / (1 - 1 / p) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hi : 1 - 1 / p ≠ 0 := by
    intro h
    have := (div_eq_one_iff_eq hp0).mp (by linarith : 1 / p = 1)
    linarith
  unfold normalizedFactor
  field_simp [hp0, hp1, hi]
  <;> ring

theorem normalizedFactor_nonneg {p a : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) :
    0 ≤ normalizedFactor p a := by
  have hden : 0 < (p - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hp1 : p - 1 ≠ 0 := by linarith
  have hnum : 0 ≤ (p - 1) ^ 2 + a - 1 := by nlinarith
  have hid : normalizedFactor p a = ((p - 1) ^ 2 + a - 1) / (p - 1) ^ 2 := by
    unfold normalizedFactor
    field_simp [hp1]
    <;> ring
  rw [hid]
  exact div_nonneg hnum hden.le

theorem normalizedFactor_le {p a : ℝ} (hp : 2 ≤ p) (ha : a ≤ p) :
    normalizedFactor p a ≤ p / (p - 1) := by
  have hden : 0 < (p - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hp1 : p - 1 ≠ 0 := by linarith
  have hid : normalizedFactor p a = ((p - 1) ^ 2 + a - 1) / (p - 1) ^ 2 := by
    unfold normalizedFactor
    field_simp [hp1]
    <;> ring
  rw [hid]
  calc
    _ ≤ (p * (p - 1)) / (p - 1) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith
    _ = p / (p - 1) := by field_simp [hp1]

/-- Any complete period with average overlap one has normalized mean one. -/
theorem sum_normalizedFactor {ι : Type*} (S : Finset ι) (p : ℝ) (a : ι → ℝ)
    (ha : ∑ i ∈ S, a i = S.card) :
    ∑ i ∈ S, normalizedFactor p (a i) = S.card := by
  simp only [normalizedFactor, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [ha]
  simp

end Erdos676
