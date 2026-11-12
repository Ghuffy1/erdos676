import Erdos676.LocalResidues
import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators

namespace Erdos676

noncomputable def residueIndicator {m : ℕ} (A : Finset (ZMod m)) (x : ZMod m) : ℂ :=
  if x ∈ A then 1 else 0

noncomputable def residueFourier {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (k : ZMod m) : ℂ :=
  ZMod.dft (residueIndicator A) k / (m : ℂ)

theorem norm_stdAddChar {m : ℕ} [NeZero m] (x : ZMod m) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem residue_dft_sum {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (k : ZMod m) :
    ZMod.dft (residueIndicator A) k = ∑ x ∈ A, ZMod.stdAddChar (-(x * k)) := by
  classical
  rw [ZMod.dft_apply]
  simp only [residueIndicator, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem residueFourier_zero {m : ℕ} [NeZero m] (A : Finset (ZMod m)) :
    residueFourier A 0 = (A.card : ℂ) / (m : ℂ) := by
  unfold residueFourier
  rw [residue_dft_sum]
  simp

theorem residueFourier_norm_le {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (k : ZMod m) :
    ‖residueFourier A k‖ ≤ (A.card : ℝ) / (m : ℝ) := by
  unfold residueFourier
  rw [norm_div, Complex.norm_natCast, residue_dft_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  calc
    _ ≤ ∑ x ∈ A, ‖ZMod.stdAddChar (-(x * k))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_stdAddChar, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem residueFourier_inversion {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (n : ZMod m) :
    residueIndicator A n =
      ∑ k : ZMod m, residueFourier A k * ZMod.stdAddChar (k * n) := by
  have h := congrArg (fun f : ZMod m → ℂ => f n) (ZMod.dft.symm_apply_apply (residueIndicator A))
  rw [ZMod.invDFT_apply] at h
  rw [← h]
  simp only [residueFourier, smul_eq_mul, Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem smallResidues_fourier_zero (p : ℕ) (hp : 1 ≤ p) :
    letI : NeZero p := ⟨by omega⟩
    residueFourier (smallResidues p) 0 = 1 / (p : ℂ) := by
  letI : NeZero p := ⟨by omega⟩
  rw [residueFourier_zero, smallResidues_card p hp, Nat.cast_pow]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem smallResidues_fourier_norm_le (p : ℕ) (hp : 1 ≤ p) :
    letI : NeZero p := ⟨by omega⟩
    ∀ k : ZMod (p ^ 2), ‖residueFourier (smallResidues p) k‖ ≤ 1 / (p : ℝ) := by
  letI : NeZero p := ⟨by omega⟩
  intro k
  have h := residueFourier_norm_le (smallResidues p) k
  rw [smallResidues_card p hp, Nat.cast_pow] at h
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : (p : ℝ) / (p : ℝ) ^ 2 = 1 / p := by field_simp
  rwa [heq] at h

end Erdos676
