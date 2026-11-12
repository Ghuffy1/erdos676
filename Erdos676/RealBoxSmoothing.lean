import Erdos676.BoxPaths

open scoped BigOperators

namespace Erdos676

noncomputable def realBoxSmooth (H J : ℕ) (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  (∑ p : Fin J → Fin H, f (n + boxPathShift p)) / (H : ℝ) ^ J

theorem coe_realBoxSmooth (H J : ℕ) (f : ℤ → ℝ) (n : ℤ) :
    (realBoxSmooth H J f n : ℂ) = boxSmooth H J (fun k => (f k : ℂ)) n := by
  rw [boxSmooth_path_formula]
  simp only [realBoxSmooth, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem realBoxSmooth_const (H J : ℕ) (hH : 0 < H) (c : ℝ) (n : ℤ) :
    realBoxSmooth H J (fun _ => c) n = c := by
  have h := boxSmooth_const H J hH (c : ℂ) n
  rw [← coe_realBoxSmooth] at h
  exact_mod_cast h

theorem realBoxSmooth_nonneg (H J : ℕ) (f : ℤ → ℝ) (hf : ∀ k, 0 ≤ f k) (n : ℤ) :
    0 ≤ realBoxSmooth H J f n := by
  exact div_nonneg (Finset.sum_nonneg (fun p hp => hf _)) (pow_nonneg (Nat.cast_nonneg H) J)

theorem realBoxSmooth_le_of_local (H J : ℕ) (hH : 0 < H) (f : ℤ → ℝ) (n : ℤ) (c : ℝ)
    (hf : ∀ k : ℤ, n ≤ k → k ≤ n + (J : ℤ) * H → f k ≤ c) :
    realBoxSmooth H J f n ≤ c := by
  have hsum : (∑ p : Fin J → Fin H, f (n + boxPathShift p)) ≤
      ∑ _p : Fin J → Fin H, c := by
    apply Finset.sum_le_sum
    intro p hp
    exact hf _ (by linarith [boxPathShift_nonneg p]) (by linarith [boxPathShift_le p])
  have h := div_le_div_of_nonneg_right hsum (pow_nonneg (Nat.cast_nonneg H) J)
  exact h.trans_eq (realBoxSmooth_const H J hH c n)

theorem realBoxSmooth_ge_of_local (H J : ℕ) (hH : 0 < H) (f : ℤ → ℝ) (n : ℤ) (c : ℝ)
    (hf : ∀ k : ℤ, n ≤ k → k ≤ n + (J : ℤ) * H → c ≤ f k) :
    c ≤ realBoxSmooth H J f n := by
  have hsum : (∑ _p : Fin J → Fin H, c) ≤ ∑ p : Fin J → Fin H, f (n + boxPathShift p) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hf _ (by linarith [boxPathShift_nonneg p]) (by linarith [boxPathShift_le p])
  have h := div_le_div_of_nonneg_right hsum (pow_nonneg (Nat.cast_nonneg H) J)
  exact (realBoxSmooth_const H J hH c n).symm.trans_le h

end Erdos676
