import Erdos676.SamplingGram
import Erdos676.KernelEnvelope
import Erdos676.SeparatedKernel

open scoped BigOperators

namespace Erdos676

theorem pair_sample_sum {R : Type*} [AddCommMonoid R] (L : ℕ) (F : ℤ → R) :
    (∑ t : Fin L × Fin L, F ((t.1.val : ℤ) - t.2.val)) =
      ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, F ((a : ℤ) - b) := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ a : Fin L, ∑ b ∈ Finset.range L, F ((a.val : ℤ) - b) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Finset.sum_range (fun b => F ((a.val : ℤ) - b))).symm
    _ = _ := (Finset.sum_range (fun a => ∑ b ∈ Finset.range L, F ((a : ℤ) - b))).symm

theorem separated_pair_sampling_bound {P : Type*} (s : Finset P) (θ : P → ℝ)
    (c : P → ℂ) (L : ℕ) (hL : 0 < L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (L : ℝ) * |θ i - θ j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2) :
    (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      ‖∑ i ∈ s, c i * realCharacter (θ i) ((a : ℤ) - b)‖ ^ 2) ≤
        64 * (L : ℝ) ^ 2 * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let f (i : P) (t : Fin L × Fin L) := realCharacter (θ i) ((t.1.val : ℤ) - t.2.val)
  have hpair (i j : P) : (∑ t : Fin L × Fin L, star (f i t) * f j t) =
      ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        realCharacter (θ j - θ i) ((a : ℤ) - b) := by
    simp only [f, realCharacter_difference]
    exact pair_sample_sum L _
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hrow : ∀ i ∈ s, (∑ j ∈ s, ‖∑ t : Fin L × Fin L, star (f i t) * f j t‖) ≤
      64 * (L : ℝ) ^ 2 := by
    intro i hi
    have hsum := separated_square_kernel_sum s θ L (θ i) hLreal hsep
    have hbound : (∑ j ∈ s, ‖∑ t : Fin L × Fin L, star (f i t) * f j t‖) ≤
        4 * (L : ℝ) ^ 2 * ∑ j ∈ s, ((1 + L * |θ j - θ i|) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [hpair]
      simpa only [div_eq_mul_inv] using real_pair_kernel_bound L hL (θ j - θ i) (hdiam j hj i hi)
    have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * (L : ℝ) ^ 2 by positivity)
    nlinarith
  have h := sampling_gram_bound s f c (64 * (L : ℝ) ^ 2) hrow
  have htotal := pair_sample_sum L (fun n => ‖∑ i ∈ s, c i * realCharacter (θ i) n‖ ^ 2)
  change (∑ t : Fin L × Fin L, ‖∑ i ∈ s, c i * realCharacter (θ i) ((t.1.val : ℤ) - t.2.val)‖ ^ 2) ≤ _ at h
  rwa [htotal] at h

end Erdos676
