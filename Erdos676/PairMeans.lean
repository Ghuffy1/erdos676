import Erdos676.ResidueAverages

open scoped BigOperators

namespace Erdos676

noncomputable def pairMean (H : ℕ) (f : ℤ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H, f ((i : ℤ) - j)) / (H : ℝ) ^ 2

theorem pairMean_mono (H : ℕ) {f g : ℤ → ℝ} (hfg : ∀ k, f k ≤ g k) :
    pairMean H f ≤ pairMean H g := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hfg _))

theorem pairMean_nonneg (H : ℕ) {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    0 ≤ pairMean H f := by
  apply div_nonneg _ (sq_nonneg _)
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hf _))

theorem pairMean_const (H : ℕ) (hH : 0 < H) (c : ℝ) :
    pairMean H (fun _ => c) = c := by
  have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH)
  simp only [pairMean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem pairMean_add (H : ℕ) (f g : ℤ → ℝ) :
    pairMean H (fun k => f k + g k) = pairMean H f + pairMean H g := by
  simp only [pairMean, Finset.sum_add_distrib, add_div]

theorem pairMean_mul_const (H : ℕ) (c : ℝ) (f : ℤ → ℝ) :
    pairMean H (fun k => c * f k) = c * pairMean H f := by
  simp only [pairMean, ← Finset.mul_sum]
  ring

theorem pairMean_sum {P : Type*} (H : ℕ) (s : Finset P) (f : P → ℤ → ℝ) :
    pairMean H (fun k => ∑ p ∈ s, f p k) = ∑ p ∈ s, pairMean H (f p) := by
  unfold pairMean
  simp_rw [Finset.sum_comm (s := Finset.range H) (t := s)]
  rw [Finset.sum_div]

end Erdos676
