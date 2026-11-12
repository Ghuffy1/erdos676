import Erdos676.PairMeans
import Erdos676.SingularAverages
import Erdos676.SingularTail

open scoped BigOperators

namespace Erdos676

noncomputable def singularProductOn (s : Finset ℕ) (k : ℤ) : ℝ :=
  ∏ p ∈ s, localSingularFactor p (k : ZMod (p ^ 2))

noncomputable def singularExcessAt (p : ℕ) (k : ℤ) : ℝ :=
  localSingularExcess p (k : ZMod (p ^ 2))

noncomputable def singularMajorant (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, (p : ℝ) / (p - 1)

theorem singularProductOn_nonneg (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (k : ℤ) :
    0 ≤ singularProductOn s k :=
  Finset.prod_nonneg (fun p hp => localSingularFactor_nonneg p (hs p hp).two_le _)

theorem singular_mixed_finset_mean (s u : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (H : ℕ) (hH : 0 < H) :
    pairMean H (fun k => ∏ p ∈ s, if p ∈ u then singularExcessAt p k
      else localSingularFactor p (k : ZMod (p ^ 2))) ≤
      (1 + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) *
        ∏ p ∈ s, if p ∈ u then 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  classical
  have h := singular_mixed_average_upper (fun p : s => (p : ℕ)) Subtype.val_injective
    (fun p => hs p p.property) (Finset.univ.filter (fun p : s => (p : ℕ) ∈ u)) H hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hvalue (i j : ℕ) :
      (∏ p : s, if (p : ℕ) ∈ u then
        localSingularExcess p ((i : ZMod ((p : ℕ) ^ 2)) - j)
      else localSingularFactor p ((i : ZMod ((p : ℕ) ^ 2)) - j)) =
      ∏ p ∈ s, if p ∈ u then localSingularExcess p ((i : ZMod (p ^ 2)) - j)
        else localSingularFactor p ((i : ZMod (p ^ 2)) - j) :=
    Finset.prod_coe_sort s (fun p => if p ∈ u then
      localSingularExcess p ((i : ZMod (p ^ 2)) - j)
      else localSingularFactor p ((i : ZMod (p ^ 2)) - j))
  have hmodulus := Finset.prod_coe_sort s (fun p => p ^ 2)
  have hmean := Finset.prod_coe_sort s (fun p => if p ∈ u then 1 / ((p : ℝ) - 1) ^ 2 else 1)
  simp_rw [hvalue] at h
  rw [hmodulus, hmean] at h
  simpa only [pairMean, singularExcessAt, Int.cast_sub, Int.cast_natCast] using h

theorem singularProductOn_mean (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (H : ℕ) (hH : 0 < H) :
    pairMean H (singularProductOn s) ≤ 1 + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ) := by
  change pairMean H (fun k => ∏ p ∈ s, localSingularFactor p (k : ZMod (p ^ 2))) ≤ _
  simpa only [Finset.notMem_empty, ite_false,
    Finset.prod_const_one, mul_one] using singular_mixed_finset_mean s ∅ hs H hH

theorem singularProductOn_excess_mean (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (q : ℕ) (hq : q.Prime) (hqs : q ∉ s) (H : ℕ) (hH : 0 < H) :
    pairMean H (fun k => singularProductOn s k * singularExcessAt q k) ≤
      (1 + ((q ^ 2 * ∏ p ∈ s, p ^ 2 : ℕ) : ℝ) / H) /
        ((q : ℝ) - 1) ^ 2 := by
  classical
  have hs' : ∀ p ∈ insert q s, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
    · exact hs p hp
  have h := singular_mixed_finset_mean (insert q s) {q} hs' H hH
  have hfun : (fun k : ℤ => ∏ p ∈ insert q s, if p ∈ ({q} : Finset ℕ)
      then singularExcessAt p k else localSingularFactor p (k : ZMod (p ^ 2))) =
      (fun k => singularProductOn s k * singularExcessAt q k) := by
    funext k
    rw [Finset.prod_insert hqs]
    simp only [Finset.mem_singleton, ite_true]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hpq : p ≠ q := fun heq => hqs (heq ▸ hp)
    simp only [hpq, ite_false]
  have hprod : (∏ p ∈ insert q s, if p ∈ ({q} : Finset ℕ)
      then 1 / ((p : ℝ) - 1) ^ 2 else 1) = 1 / ((q : ℝ) - 1) ^ 2 := by
    rw [Finset.prod_insert hqs]
    simp only [Finset.mem_singleton, ite_true]
    have heq : (∏ p ∈ s, if p = q then 1 / ((p : ℝ) - 1) ^ 2 else 1) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hpq : p ≠ q := fun heq => hqs (heq ▸ hp)
      simp only [hpq, ite_false]
    rw [heq, mul_one]
  rw [hfun, hprod, Finset.prod_insert hqs] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem singularProductOn_union (s t : Finset ℕ) (hst : Disjoint s t) (k : ℤ) :
    singularProductOn (s ∪ t) k = singularProductOn s k * singularProductOn t k :=
  Finset.prod_union hst

end Erdos676
