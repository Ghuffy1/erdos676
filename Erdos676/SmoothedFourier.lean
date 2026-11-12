import Erdos676.ResidueFrequency

open scoped BigOperators

namespace Erdos676

theorem boxMean_sum {P : Type*} (H : ℕ) (s : Finset P) (f : P → ℤ → ℂ) (n : ℤ) :
    boxMean H (fun k => ∑ p ∈ s, f p k) n = ∑ p ∈ s, boxMean H (f p) n := by
  simp only [boxMean, Finset.sum_div]
  rw [Finset.sum_comm]

theorem boxSmooth_const_mul (H J : ℕ) (c : ℂ) (f : ℤ → ℂ) (n : ℤ) :
    boxSmooth H J (fun k => c * f k) n = c * boxSmooth H J f n := by
  induction J generalizing n with
  | zero => rfl
  | succ J ih =>
      change boxMean H (boxSmooth H J (fun k => c * f k)) n = _
      rw [show boxSmooth H J (fun k => c * f k) = (fun k => c * boxSmooth H J f k) from funext ih]
      exact boxMean_const_mul H c _ n

theorem boxSmooth_sum {P : Type*} (H J : ℕ) (s : Finset P) (f : P → ℤ → ℂ) (n : ℤ) :
    boxSmooth H J (fun k => ∑ p ∈ s, f p k) n = ∑ p ∈ s, boxSmooth H J (f p) n := by
  induction J generalizing n with
  | zero => rfl
  | succ J ih =>
      change boxMean H (boxSmooth H J (fun k => ∑ p ∈ s, f p k)) n = _
      rw [show boxSmooth H J (fun k => ∑ p ∈ s, f p k) =
        (fun k => ∑ p ∈ s, boxSmooth H J (f p) k) from funext ih]
      exact boxMean_sum H s _ n

noncomputable def residueFourierPart {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) (n : ℤ) : ℂ :=
  ∑ k ∈ s, residueFourier A k * residueCharacter k n

theorem residueIndicator_fourier {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (n : ℤ) :
    residueIndicator A (n : ZMod m) = residueFourierPart A Finset.univ n :=
  residueFourier_inversion A (n : ZMod m)

theorem smoothed_residueFourierPart {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) (H J : ℕ) (n : ℤ) :
    boxSmooth H J (residueFourierPart A s) n =
      ∑ k ∈ s, residueFourier A k * (boxMultiplier H (residueCharacter k)) ^ J * residueCharacter k n := by
  unfold residueFourierPart
  rw [boxSmooth_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [boxSmooth_const_mul, boxSmooth_character]
  ring

theorem residueFourier_mass_le {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) : (∑ k ∈ s, ‖residueFourier A k‖) ≤ A.card := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hc : (s.card : ℝ) ≤ m := by
    exact_mod_cast (show s.card ≤ m by simpa only [ZMod.card] using Finset.card_le_univ s)
  calc
    _ ≤ ∑ k ∈ s, (A.card : ℝ) / m := Finset.sum_le_sum (fun k hk => residueFourier_norm_le A k)
    _ = (s.card : ℝ) * ((A.card : ℝ) / m) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * ((A.card : ℝ) / m) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg _) hm.le)
    _ = _ := by field_simp

theorem smoothed_fourier_tail_bound {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) (H J : ℕ) (hH : 0 < H) (D : ℝ) (hD : 0 < D)
    (hs : ∀ k ∈ s, k ≠ 0 ∧ D ≤ |residueFrequency k|) (n : ℤ) :
    ‖boxSmooth H J (residueFourierPart A s) n‖ ≤
      A.card * (1 / ((H : ℝ) * D)) ^ J := by
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hdecay (k : ZMod m) (hk : k ∈ s) :
      ‖boxMultiplier H (residueCharacter k)‖ ^ J ≤ (1 / ((H : ℝ) * D)) ^ J := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (residue_boxMultiplier_decay k (hs k hk).1 H hH).trans
      (one_div_le_one_div_of_le (mul_pos hHreal hD)
        (mul_le_mul_of_nonneg_left (hs k hk).2 hHreal.le))
  rw [smoothed_residueFourierPart]
  calc
    _ ≤ ∑ k ∈ s, ‖residueFourier A k * (boxMultiplier H (residueCharacter k)) ^ J * residueCharacter k n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖residueFourier A k‖ * (1 / ((H : ℝ) * D)) ^ J := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, norm_mul, norm_pow, residueCharacter_norm, mul_one]
      exact mul_le_mul_of_nonneg_left (hdecay k hk) (norm_nonneg _)
    _ = (∑ k ∈ s, ‖residueFourier A k‖) * (1 / ((H : ℝ) * D)) ^ J := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (residueFourier_mass_le A s) (by positivity)

end Erdos676
