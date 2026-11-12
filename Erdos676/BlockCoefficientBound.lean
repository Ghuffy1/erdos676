import Erdos676.BonferroniExpansion
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators

namespace Erdos676

theorem sum_powers_le_add_pow (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), n ^ i) ≤ (1 + n) ^ k := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), n ^ i * k.choose i := by
      apply Finset.sum_le_sum
      intro i hi
      have hpos := Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      simpa using Nat.mul_le_mul_left (n ^ i) hpos
    _ = (n + 1) ^ k := by rw [add_pow]; simp
    _ = (1 + n) ^ k := by rw [Nat.add_comm n 1]

theorem bounded_elementary_sum {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (B k : ℕ) (ha : ∀ p ∈ s, a p ≤ B) :
    (∑ d ∈ s.powersetCard k, ∏ p ∈ d, a p) ≤ s.card.choose k * B ^ k := by
  calc
    _ ≤ ∑ _d ∈ s.powersetCard k, B ^ k := by
      apply Finset.sum_le_sum
      intro d hd
      have hprod : (∏ p ∈ d, a p) ≤ ∏ _p ∈ d, B :=
        Finset.prod_le_prod (fun p hp => ha p ((Finset.mem_powersetCard.mp hd).1 hp))
      simpa only [Finset.prod_const, (Finset.mem_powersetCard.mp hd).2] using hprod
    _ = s.card.choose k * B ^ k := by simp

theorem truncated_block_weight_bound {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (B k : ℕ) (ha : ∀ p ∈ s, a p ≤ B) :
    (∑ d ∈ bonferroniSupport s k, ∏ p ∈ d, a p) ≤ (1 + s.card * B) ^ k := by
  have hsum := truncated_card_sum s k (fun _ => (1 : ℕ)) (fun d => ∏ p ∈ d, a p)
  simp only [one_mul] at hsum
  rw [← hsum]
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), s.card.choose i * B ^ i :=
      Finset.sum_le_sum (fun i _ => bounded_elementary_sum s a B i ha)
    _ ≤ ∑ i ∈ Finset.range (k + 1), (s.card * B) ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := Nat.mul_le_mul_right (B ^ i) (Nat.choose_le_pow s.card i)
      simpa only [mul_pow] using h
    _ ≤ _ := sum_powers_le_add_pow (s.card * B) k

theorem block_weight_power_bound {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (B k : ℕ) (hB : 1 ≤ B)
    (ha : ∀ p ∈ s, a p ≤ B) (hcard : s.card + 1 ≤ B) :
    (∑ d ∈ bonferroniSupport s k, ∏ p ∈ d, a p) ≤ B ^ (2 * k) := by
  have hbase : 1 + s.card * B ≤ B ^ 2 := by nlinarith
  calc
    _ ≤ (1 + s.card * B) ^ k := truncated_block_weight_bound s a B k ha
    _ ≤ (B ^ 2) ^ k := Nat.pow_le_pow_left hbase k
    _ = B ^ (2 * k) := (pow_mul B 2 k).symm

theorem bounded_block_card {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (hinj : Set.InjOn a s) (B : ℕ) (hB : 1 ≤ B)
    (hmin : ∀ p ∈ s, 2 ≤ a p) (hmax : ∀ p ∈ s, a p ≤ B) : s.card + 1 ≤ B := by
  have hsubset : s.image a ⊆ Finset.Icc 2 B := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨hmin p hp, hmax p hp⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_iff.mpr hinj, Nat.card_Icc] at hcard
  omega

theorem bounded_block_coefficient_sum {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (hinj : Set.InjOn a s) (B k : ℕ) (hB : 1 ≤ B)
    (hmin : ∀ p ∈ s, 2 ≤ a p) (hmax : ∀ p ∈ s, a p ≤ B) :
    (∑ d ∈ bonferroniSupport s k, ∏ p ∈ d, a p) ≤ B ^ (2 * k) :=
  block_weight_power_bound s a B k hB hmax (bounded_block_card s a hinj B hB hmin hmax)

end Erdos676
