import Erdos676.SmallCorrelations
import Erdos676.AveragedFirstMoment

open scoped BigOperators

namespace Erdos676

theorem smallAverage_square_sum_eq_pairs (z H S N : ℕ) :
    (∑ n ∈ Finset.range N, (smallAverage z H (S + n)) ^ 2) =
      (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, smallPairCount z S N i j) / (H : ℝ) ^ 2 := by
  classical
  simp only [smallAverage, div_pow, ← Finset.sum_div]
  congr 1
  have h := weighted_square_expansion (Finset.range H) (Finset.range N) (fun _ => (1 : ℝ))
    (fun i n => if SmallAvoidance z (S + n + i) then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
  simp only [one_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold smallPairCount
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hi' : SmallAvoidance z (S + n + i) <;>
    by_cases hj' : SmallAvoidance z (S + n + j) <;> simp [hi', hj']

theorem smallAverage_dyadic_square_sum_eq_pairs (z H X : ℕ) :
    (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage z H n) ^ 2) =
      (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, smallPairCount z (X + 1) X i j) / (H : ℝ) ^ 2 := by
  rw [sum_dyadic_interval_eq_range]
  exact smallAverage_square_sum_eq_pairs z H (X + 1) X

theorem smallAverage_second_upper (z H S N : ℕ) (hH : 0 < H)
    (V : ℕ → ℕ → ℝ) (B E : ℝ)
    (hpairs : ∀ i < H, ∀ j < H, smallPairCount z S N i j ≤ B * V i j + E) :
    (∑ n ∈ Finset.range N, (smallAverage z H (S + n)) ^ 2) ≤
      B * ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, V i j) / (H : ℝ) ^ 2) + E := by
  have hsum : (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, smallPairCount z S N i j) ≤
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, (B * V i j + E) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hpairs i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  rw [smallAverage_square_sum_eq_pairs]
  calc
    _ ≤ (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, (B * V i j + E)) / (H : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have hHne : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH)
      field_simp

end Erdos676
