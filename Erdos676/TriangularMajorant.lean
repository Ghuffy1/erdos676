import Erdos676.SeparatedSampling

open scoped BigOperators

namespace Erdos676

theorem interval_sum_le_pair_sum (N : ℕ) (F : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (N : ℝ) * (∑ n ∈ Finset.range N, F n) ≤
      ∑ a ∈ Finset.range (2 * N), ∑ b ∈ Finset.range (2 * N), F ((a : ℤ) - b) := by
  classical
  let small := (Finset.range N).product (Finset.range N)
  let large := (Finset.range (2 * N)).product (Finset.range (2 * N))
  let embed (t : ℕ × ℕ) : ℕ × ℕ := (t.1 + t.2, t.2)
  have hinj : Function.Injective embed := by
    intro a b h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    dsimp [embed] at hfst hsnd
    apply Prod.ext <;> omega
  have hsub : small.image embed ⊆ large := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp hu
    have h1 := Finset.mem_range.mp hu1
    have h2 := Finset.mem_range.mp hu2
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [embed]; omega),
      Finset.mem_range.mpr (by dsimp [embed]; omega)⟩
  calc
    _ = ∑ t ∈ small, F (t.1 : ℤ) := by
      dsimp [small]
      rw [Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ = ∑ t ∈ small, F (((embed t).1 : ℤ) - (embed t).2) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [embed, Nat.cast_add, add_sub_cancel_right]
    _ = ∑ t ∈ small.image embed, F ((t.1 : ℤ) - t.2) :=
      by
        symm
        exact Finset.sum_image (fun a ha b hb h => hinj h)
    _ ≤ ∑ t ∈ large, F ((t.1 : ℤ) - t.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => hF _)
    _ = _ := by dsimp [large]; rw [Finset.sum_product]

theorem separated_interval_sampling_bound {P : Type*} (s : Finset P) (θ : P → ℝ)
    (c : P → ℂ) (N : ℕ) (hN : 0 < N)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (2 * N : ℕ) * |θ i - θ j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2) :
    (∑ n ∈ Finset.range N, ‖∑ i ∈ s, c i * realCharacter (θ i) n‖ ^ 2) ≤
      256 * N * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hpair := separated_pair_sampling_bound s θ c (2 * N) (by omega) hsep hdiam
  have hmajor := interval_sum_le_pair_sum N
    (fun n => ‖∑ i ∈ s, c i * realCharacter (θ i) n‖ ^ 2) (fun n => sq_nonneg _)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound := hmajor.trans hpair
  push_cast at hbound
  nlinarith

theorem separated_translated_sampling_bound {P : Type*} (s : Finset P) (θ : P → ℝ)
    (c : P → ℂ) (S : ℤ) (N : ℕ) (hN : 0 < N)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (2 * N : ℕ) * |θ i - θ j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2) :
    (∑ n ∈ Finset.range N, ‖∑ i ∈ s, c i * realCharacter (θ i) (S + n)‖ ^ 2) ≤
      256 * N * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have h := separated_interval_sampling_bound s θ (fun i => c i * realCharacter (θ i) S) N hN hsep hdiam
  have hfun (n : ℕ) : (∑ i ∈ s, c i * realCharacter (θ i) (S + n)) =
      ∑ i ∈ s, (c i * realCharacter (θ i) S) * realCharacter (θ i) n := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [AddChar.map_add_eq_mul]
    ring
  simpa only [hfun, norm_mul, realCharacter_norm, mul_one] using h

end Erdos676
