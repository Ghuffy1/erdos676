import Erdos676.SingularFiniteMeans
import Erdos676.ReciprocalTail

open scoped BigOperators

namespace Erdos676

theorem singularMajorant_nonneg (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 ≤ singularMajorant s := by
  apply Finset.prod_nonneg
  intro p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
  exact div_nonneg (by positivity) (by linarith)

theorem singularProductOn_le_majorant (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (k : ℤ) :
    singularProductOn s k ≤ singularMajorant s :=
  Finset.prod_le_prod₀ (fun p hp => localSingularFactor_nonneg p (hs p hp).two_le _)
    (fun p hp => localSingularFactor_le p (hs p hp).two_le _)

theorem singular_range_mean_increment (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime) (H : ℕ) :
    pairMean H (singularProductOn (s ∪ t)) ≤ pairMean H (singularProductOn s) +
      singularMajorant t * ∑ p ∈ t,
        pairMean H (fun k => singularProductOn s k * singularExcessAt p k) := by
  have hpoint (k : ℤ) : singularProductOn (s ∪ t) k ≤ singularProductOn s k +
      singularMajorant t * ∑ p ∈ t, singularProductOn s k * singularExcessAt p k := by
    have htail := singular_tail_increment_upper t (fun p hp => (ht p hp).two_le) k
    change singularProductOn t k ≤ 1 + singularMajorant t * ∑ p ∈ t, singularExcessAt p k at htail
    have h := mul_le_mul_of_nonneg_left htail (singularProductOn_nonneg s hs k)
    rw [singularProductOn_union s t hst]
    calc
      _ ≤ singularProductOn s k * (1 + singularMajorant t * ∑ p ∈ t, singularExcessAt p k) := h
      _ = _ := by
        simp only [Finset.mul_sum, mul_add, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have h := pairMean_mono H hpoint
  simpa only [pairMean_add, pairMean_mul_const, pairMean_sum] using h

theorem singular_excess_mean_bound (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (q : ℕ) (hq : q.Prime) (hqs : q ∉ s) (H : ℕ) (hH : 0 < H) :
    pairMean H (fun k => singularProductOn s k * singularExcessAt q k) ≤
      4 * (((q : ℝ) ^ 2)⁻¹ + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
  have h := singularProductOn_excess_mean s hs q hq hqs H hH
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hH0 : 0 < (H : ℝ) := by exact_mod_cast hH
  have hnonneg : 0 ≤ 1 + (q : ℝ) ^ 2 * (∏ p ∈ s, p ^ 2 : ℕ) / H := by positivity
  have hbound := mul_le_mul_of_nonneg_left (shifted_reciprocal_square_le q hq.two_le) hnonneg
  have heq : (1 + (q : ℝ) ^ 2 * (∏ p ∈ s, p ^ 2 : ℕ) / H) *
      (4 * ((q : ℝ) ^ 2)⁻¹) =
      4 * (((q : ℝ) ^ 2)⁻¹ + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
    field_simp
  rw [heq] at hbound
  apply h.trans
  simpa only [Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, one_mul] using hbound

theorem singular_range_mean_bound (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (H m n : ℕ) (hH : 0 < H) (hm : 1 ≤ m) (hn : m ≤ n)
    (htail : t ⊆ Finset.Ioc m n) :
    pairMean H (singularProductOn (s ∪ t)) ≤ pairMean H (singularProductOn s) +
      4 * singularMajorant t * ((m : ℝ)⁻¹ +
        t.card * (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
  have hinc := singular_range_mean_increment s t hst hs ht H
  have hsum : (∑ p ∈ t, pairMean H (fun k => singularProductOn s k * singularExcessAt p k)) ≤
      4 * ((m : ℝ)⁻¹ + t.card * (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
    have heach := Finset.sum_le_sum (fun p hp => singular_excess_mean_bound s hs p (ht p hp)
      (fun hps => (Finset.disjoint_left.mp hst hps) hp) H hH)
    have htail' : (∑ p ∈ t, ((p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg htail
        (fun p _ _ => by positivity : ∀ p, p ∈ Finset.Ioc m n → p ∉ t → 0 ≤ ((p : ℝ) ^ 2)⁻¹)
      have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) hn
      have hn0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
      linarith
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul] at heach
    simp only [div_eq_mul_inv] at heach ⊢
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (singularMajorant_nonneg t ht)
  nlinarith

end Erdos676
