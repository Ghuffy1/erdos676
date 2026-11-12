import Erdos676.SingularRangeIncrement

open scoped BigOperators

namespace Erdos676

theorem singularExcessAt_mean (q H : ℕ) (hq : q.Prime) (hH : 0 < H) :
    pairMean H (singularExcessAt q) ≤ 4 * (((q : ℝ) ^ 2)⁻¹ + 1 / (H : ℝ)) := by
  change pairMean H (fun k => singularExcessAt q k) ≤ _
  simpa only [singularProductOn, Finset.prod_empty, Nat.cast_one, one_mul] using
    singular_excess_mean_bound ∅ (by simp) q hq (by simp) H hH

theorem singular_excess_mean_coarse (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (q H : ℕ) (hq : q.Prime) (hH : 0 < H) :
    pairMean H (fun k => singularProductOn s k * singularExcessAt q k) ≤
      4 * singularMajorant s * (((q : ℝ) ^ 2)⁻¹ + 1 / (H : ℝ)) := by
  have hpoint (k : ℤ) : singularProductOn s k * singularExcessAt q k ≤
      singularMajorant s * singularExcessAt q k :=
    mul_le_mul_of_nonneg_right (singularProductOn_le_majorant s hs k) (le_max_right _ _)
  have h := pairMean_mono H hpoint
  rw [pairMean_mul_const] at h
  have hbound := mul_le_mul_of_nonneg_left (singularExcessAt_mean q H hq hH)
    (singularMajorant_nonneg s hs)
  nlinarith

theorem singular_range_mean_bound_coarse (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (H m n : ℕ) (hH : 0 < H) (hm : 1 ≤ m) (hn : m ≤ n)
    (htail : t ⊆ Finset.Ioc m n) :
    pairMean H (singularProductOn (s ∪ t)) ≤ pairMean H (singularProductOn s) +
      4 * singularMajorant s * singularMajorant t *
        ((m : ℝ)⁻¹ + t.card / (H : ℝ)) := by
  have hinc := singular_range_mean_increment s t hst hs ht H
  have hsum : (∑ p ∈ t, pairMean H (fun k => singularProductOn s k * singularExcessAt p k)) ≤
      4 * singularMajorant s * ((m : ℝ)⁻¹ + t.card / (H : ℝ)) := by
    have heach := Finset.sum_le_sum (fun p hp => singular_excess_mean_coarse s hs p H (ht p hp) hH)
    have htail' : (∑ p ∈ t, ((p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg htail
        (fun p _ _ => by positivity : ∀ p, p ∈ Finset.Ioc m n → p ∉ t → 0 ≤ ((p : ℝ) ^ 2)⁻¹)
      have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) hn
      have hn0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
      linarith
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at heach
    have hfactor : 0 ≤ 4 * singularMajorant s := mul_nonneg (by norm_num) (singularMajorant_nonneg s hs)
    have hscaled := mul_le_mul_of_nonneg_left htail' hfactor
    simp only [div_eq_mul_inv, one_mul] at heach ⊢
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (singularMajorant_nonneg t ht)
  nlinarith

end Erdos676
