import Erdos676.BonferroniExpansion

open scoped BigOperators

namespace Erdos676

theorem disjoint_polynomial_transfer {J P N : Type*} [Fintype J] [DecidableEq J] [DecidableEq P]
    (I : Finset N) (T : J → Finset (Finset P)) (c : J → Finset P → ℝ)
    (E : P → N → Prop) (g a : P → ℝ) (M : ℝ)
    (hdisjoint : ∀ i j, i ≠ j → ∀ d ∈ T i, ∀ e ∈ T j, Disjoint d e)
    (hcount : ∀ b ∈ Fintype.piFinset T,
      |(∑ n ∈ I, eventProduct E (Finset.univ.biUnion b) n) -
        M * (∏ p ∈ Finset.univ.biUnion b, g p)| ≤ ∏ p ∈ Finset.univ.biUnion b, a p) :
    |(∑ n ∈ I, ∏ j : J, ∑ d ∈ T j, c j d * eventProduct E d n) -
      M * (∏ j : J, ∑ d ∈ T j, c j d * (∏ p ∈ d, g p))| ≤
      ∏ j : J, ∑ d ∈ T j, |c j d| * (∏ p ∈ d, a p) := by
  classical
  let U (b : J → Finset P) := Finset.univ.biUnion b
  let w (b : J → Finset P) := ∏ j : J, c j (b j)
  have hpair (b : J → Finset P) (hb : b ∈ Fintype.piFinset T) :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset J)) b := by
    intro i hi j hj hij
    exact hdisjoint i j hij (b i) (Fintype.mem_piFinset.mp hb i)
      (b j) (Fintype.mem_piFinset.mp hb j)
  have hactual (n : N) : (∏ j : J, ∑ d ∈ T j, c j d * eventProduct E d n) =
      ∑ b ∈ Fintype.piFinset T, w b * eventProduct E (U b) n := by
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.prod_mul_distrib]
    rw [eventProduct_biUnion]
  have hmodel : (∏ j : J, ∑ d ∈ T j, c j d * (∏ p ∈ d, g p)) =
      ∑ b ∈ Fintype.piFinset T, w b * (∏ p ∈ U b, g p) := by
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.prod_mul_distrib, Finset.prod_biUnion (hpair b hb)]
  have hexpand : (∑ n ∈ I, ∏ j : J, ∑ d ∈ T j, c j d * eventProduct E d n) =
      ∑ b ∈ Fintype.piFinset T, w b * (∑ n ∈ I, eventProduct E (U b) n) := by
    simp_rw [hactual]
    have h := weighted_sum_linearCombination (Fintype.piFinset T) I (fun _ => 1) w
      (fun b n => eventProduct E (U b) n)
    simpa only [one_mul] using h
  rw [hexpand, hmodel]
  have hdiff : (∑ b ∈ Fintype.piFinset T, w b * (∑ n ∈ I, eventProduct E (U b) n)) -
      M * (∑ b ∈ Fintype.piFinset T, w b * (∏ p ∈ U b, g p)) =
      ∑ b ∈ Fintype.piFinset T, w b *
        ((∑ n ∈ I, eventProduct E (U b) n) - M * (∏ p ∈ U b, g p)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hdiff]
  calc
    _ ≤ ∑ b ∈ Fintype.piFinset T, |w b *
        ((∑ n ∈ I, eventProduct E (U b) n) - M * (∏ p ∈ U b, g p))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Fintype.piFinset T, |w b| * (∏ p ∈ U b, a p) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcount b hb) (abs_nonneg _)
    _ = ∑ b ∈ Fintype.piFinset T, ∏ j : J, |c j (b j)| * (∏ p ∈ b j, a p) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [w, Finset.abs_prod]
      rw [Finset.prod_biUnion (hpair b hb), Finset.prod_mul_distrib]
    _ = _ := (Finset.prod_univ_sum T (fun j d => |c j d| * (∏ p ∈ d, a p))).symm

end Erdos676
