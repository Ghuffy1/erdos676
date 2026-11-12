import Erdos676.AvoidanceBoundaryCards
import Erdos676.IntervalSums
import Erdos676.PrimeBandSize
import Mathlib.Analysis.PSeries

open scoped BigOperators

namespace Erdos676

theorem family_reciprocal_square_tail {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (m : ℕ) (hm : 0 < m)
    (hlo : ∀ p, m < a p) : (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by
  let s := Finset.univ.image a
  let N := max m (s.sup id)
  have hsub : s ⊆ Finset.Ioc m N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr ⟨hlo p, (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hsum : (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) = ∑ n ∈ s, ((n : ℝ) ^ 2)⁻¹ := by
    symm
    apply Finset.sum_image
    intro p hp q hq h
    exact hinj h
  rw [hsum]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn hnot => by positivity : ∀ n, n ∈ Finset.Ioc m N → n ∉ s → 0 ≤ ((n : ℝ) ^ 2)⁻¹)
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (Nat.ne_of_gt hm) (le_max_left m (s.sup id))
  have hN0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  linarith

theorem avoidance_boundary_card_bound {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (m : ℕ) (hm : 0 < m) (hlo : ∀ p, m < a p) (z : ℝ) (hz : 0 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (S : ℤ) (N R : ℕ) :
    ((avoidanceBoundarySet a S (S + N - 1) R).card : ℝ) ≤
      2 * R * ((N : ℝ) / m + z) := by
  classical
  have hcount := family_boundary_interval_upper a hprime R N S
  have htail := family_reciprocal_square_tail a hinj m hm hlo
  have hcard := prime_family_card_le a hinj hprime z hz hle
  have hinner := add_le_add (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N)) hcard
  have hscaled := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * (R : ℝ) by positivity)
  have hsum : ((avoidanceBoundarySet a S (S + N - 1) R).card : ℝ) =
      ∑ n ∈ Finset.range N, if ∃ p : P,
        (S + (n : ℤ) : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R then 1 else 0 := by
    unfold avoidanceBoundarySet
    rw [card_filter_real, sum_int_interval]
    simp only [Int.cast_add]
  rw [hsum]
  have h := hcount.trans hscaled
  simpa only [div_eq_mul_inv] using h

end Erdos676
