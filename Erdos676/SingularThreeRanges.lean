import Erdos676.SingularCoarseRange

open scoped BigOperators

namespace Erdos676

theorem singularMajorant_union (s t : Finset ℕ) (hst : Disjoint s t) :
    singularMajorant (s ∪ t) = singularMajorant s * singularMajorant t :=
  Finset.prod_union hst

theorem singular_three_ranges_mean_bound (s t u : Finset ℕ)
    (hst : s ⊆ t) (htu : t ⊆ u) (hu : ∀ p ∈ u, p.Prime)
    (H m n r : ℕ) (hH : 0 < H) (hm : 1 ≤ m) (hmn : m ≤ n) (hnr : n ≤ r)
    (hfirst : t \ s ⊆ Finset.Ioc m n) (hsecond : u \ t ⊆ Finset.Ioc n r) :
    pairMean H (singularProductOn u) ≤
      1 + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ) +
      4 * singularMajorant (t \ s) *
        ((m : ℝ)⁻¹ + (t \ s).card * (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) +
      4 * singularMajorant u * ((n : ℝ)⁻¹ + (u \ t).card / (H : ℝ)) := by
  have ht : ∀ p ∈ t, p.Prime := fun p hp => hu p (htu hp)
  have hs : ∀ p ∈ s, p.Prime := fun p hp => ht p (hst hp)
  have hst' : Disjoint s (t \ s) := Finset.disjoint_left.mpr
    (fun p hp hdiff => (Finset.mem_sdiff.mp hdiff).2 hp)
  have htu' : Disjoint t (u \ t) := Finset.disjoint_left.mpr
    (fun p hp hdiff => (Finset.mem_sdiff.mp hdiff).2 hp)
  have hsplit1 : s ∪ (t \ s) = t := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hst]
  have hsplit2 : t ∪ (u \ t) = u := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset htu]
  have hlow := singularProductOn_mean s hs H hH
  have hmiddle := singular_range_mean_bound s (t \ s) hst' hs
    (fun p hp => ht p (Finset.mem_sdiff.mp hp).1) H m n hH hm hmn hfirst
  have hupper := singular_range_mean_bound_coarse t (u \ t) htu' ht
    (fun p hp => hu p (Finset.mem_sdiff.mp hp).1) H n r hH (hm.trans hmn) hnr hsecond
  rw [hsplit1] at hmiddle
  rw [hsplit2] at hupper
  have hprod := singularMajorant_union t (u \ t) htu'
  rw [hsplit2] at hprod
  rw [mul_assoc 4 (singularMajorant t), ← hprod] at hupper
  linarith

theorem singular_mean_extension (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ p ∈ t, p.Prime) (H : ℕ) :
    pairMean H (singularProductOn t) ≤ singularMajorant (t \ s) *
      pairMean H (singularProductOn s) := by
  have hs : ∀ p ∈ s, p.Prime := fun p hp => ht p (hst hp)
  have hdisj : Disjoint s (t \ s) := Finset.disjoint_left.mpr
    (fun p hp hdiff => (Finset.mem_sdiff.mp hdiff).2 hp)
  have hsplit : s ∪ (t \ s) = t := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hst]
  have hpoint (k : ℤ) : singularProductOn t k ≤
      singularMajorant (t \ s) * singularProductOn s k := by
    conv_lhs => rw [← hsplit, singularProductOn_union s (t \ s) hdisj]
    have h := mul_le_mul_of_nonneg_left
      (singularProductOn_le_majorant (t \ s) (fun p hp => ht p (Finset.mem_sdiff.mp hp).1) k)
      (singularProductOn_nonneg s hs k)
    simpa only [mul_comm] using h
  simpa only [pairMean_mul_const] using pairMean_mono H hpoint

end Erdos676
