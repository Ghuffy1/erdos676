import Erdos676.ProductBrackets

open scoped BigOperators

namespace Erdos676

theorem bracketLoss_replacements {J : Type*} [DecidableEq J]
    (s : Finset J) (lower upper : J → ℝ) :
    bracketLoss s lower upper = ∑ j ∈ s,
      ((∏ i ∈ s, upper i) - ∏ i ∈ s, Function.update upper j (lower j) i) := by
  unfold bracketLoss
  apply Finset.sum_congr rfl
  intro j hj
  have hU := Finset.mul_prod_erase s upper hj
  have hL : (∏ i ∈ s, Function.update upper j (lower j) i) =
      lower j * ∏ i ∈ s.erase j, upper i := by
    simpa only [Finset.sdiff_singleton_eq_erase] using Finset.prod_update_of_mem hj upper (lower j)
  rw [hL, ← hU]
  ring

theorem scalar_bracket_transfer {J : Type*} (s : Finset J)
    (A a E : ℝ) (B b : J → ℝ) (hA : |A - a| ≤ E)
    (hB : ∀ j ∈ s, |B j - b j| ≤ E) :
    (a - ∑ j ∈ s, (a - b j)) - (2 * (s.card : ℝ) + 1) * E ≤
      A - ∑ j ∈ s, (A - B j) := by
  have hAlow := (abs_le.mp hA).1
  have hAup := (abs_le.mp hA).2
  have hsum : (∑ j ∈ s, (A - B j)) ≤ ∑ j ∈ s, ((a - b j) + 2 * E) := by
    apply Finset.sum_le_sum
    intro j hj
    have hBlow := (abs_le.mp (hB j hj)).1
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

theorem product_bracket_transfer {J N : Type*} [DecidableEq J]
    (s : Finset J) (I : Finset N) (upper lower : J → N → ℝ)
    (u l : J → ℝ) (M E : ℝ)
    (hU : |(∑ n ∈ I, ∏ j ∈ s, upper j n) - M * (∏ j ∈ s, u j)| ≤ E)
    (hL : ∀ j ∈ s,
      |(∑ n ∈ I, ∏ i ∈ s, Function.update (fun i => upper i n) j (lower j n) i) -
        M * (∏ i ∈ s, Function.update u j (l j) i)| ≤ E) :
    M * ((∏ j ∈ s, u j) - bracketLoss s l u) - (2 * (s.card : ℝ) + 1) * E ≤
      ∑ n ∈ I, ((∏ j ∈ s, upper j n) - bracketLoss s (fun j => lower j n) (fun j => upper j n)) := by
  have h := scalar_bracket_transfer s
    (∑ n ∈ I, ∏ j ∈ s, upper j n) (M * (∏ j ∈ s, u j)) E
    (fun j => ∑ n ∈ I, ∏ i ∈ s, Function.update (fun i => upper i n) j (lower j n) i)
    (fun j => M * (∏ i ∈ s, Function.update u j (l j) i)) hU hL
  have hmodel : M * ((∏ j ∈ s, u j) - bracketLoss s l u) =
      M * (∏ j ∈ s, u j) -
        ∑ j ∈ s, (M * (∏ i ∈ s, u i) - M * (∏ i ∈ s, Function.update u j (l j) i)) := by
    rw [bracketLoss_replacements]
    simp only [mul_sub, Finset.mul_sum]
  have hactual : (∑ n ∈ I, ((∏ j ∈ s, upper j n) -
      bracketLoss s (fun j => lower j n) (fun j => upper j n))) =
      (∑ n ∈ I, ∏ j ∈ s, upper j n) - ∑ j ∈ s,
        ((∑ n ∈ I, ∏ i ∈ s, upper i n) -
          ∑ n ∈ I, ∏ i ∈ s, Function.update (fun i => upper i n) j (lower j n) i) := by
    simp_rw [bracketLoss_replacements]
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  rw [hmodel, hactual]
  exact h

end Erdos676
