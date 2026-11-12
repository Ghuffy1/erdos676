import Erdos676.BonferroniBlockBounds
import Erdos676.BlockParameters

open scoped BigOperators

namespace Erdos676

theorem grouped_bonferroni_model_lower {P : Type*} [Fintype P] [DecidableEq P]
    (blocks : ℕ → Finset P) (g : P → ℝ) (L J : ℕ) (hL : 1 ≤ L) (C : ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1 / 2)
    (hC : ∀ j < J, (∑ p ∈ blocks j, g p) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) *
        (∏ j ∈ Finset.range J, ∏ p ∈ blocks j, (1 - g p)) ≤
      (∏ j ∈ Finset.range J, bonferroniModel (blocks j) (2 * (L + j)) g) -
        bracketLoss (Finset.range J)
          (fun j => bonferroniModel (blocks j) (2 * (L + j) - 1) g)
          (fun j => bonferroniModel (blocks j) (2 * (L + j)) g) := by
  let error (j : ℕ) := Real.exp (4 * C) / (2 : ℝ) ^ (2 * (L + j))
  have hV : ∀ j ∈ Finset.range J, 0 ≤ ∏ p ∈ blocks j, (1 - g p) := by
    intro j hj
    apply Finset.prod_nonneg
    intro p hp
    have := hg1 p
    linarith
  have hEven (j : ℕ) : Even (2 * (L + j)) := ⟨L + j, by omega⟩
  have hupper : ∀ j ∈ Finset.range J,
      (∏ p ∈ blocks j, (1 - g p)) ≤ bonferroniModel (blocks j) (2 * (L + j)) g := by
    intro j hj
    exact bonferroniModel_even_upper g (blocks j) _ (hEven j) hg0 (fun p => by have := hg1 p; linarith)
  have hgap : ∀ j ∈ Finset.range J,
      bonferroniModel (blocks j) (2 * (L + j)) g -
          bonferroniModel (blocks j) (2 * (L + j) - 1) g ≤
        error j * bonferroniModel (blocks j) (2 * (L + j)) g := by
    intro j hj
    have hsub : 2 * (L + j) - 1 + 1 = 2 * (L + j) := by omega
    have heven' : Even (2 * (L + j) - 1 + 1) := by rw [hsub]; exact hEven j
    have h := bonferroniModel_relative_gap g (blocks j) (2 * (L + j) - 1) heven' C hg0 hg1
      (hC j (Finset.mem_range.mp hj))
    simpa only [hsub, error] using h
  have hsum : (∑ j ∈ Finset.range J, error j) ≤
      2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) := block_error_sum C L J
  have hmain := product_bracket_relative_lower (Finset.range J)
    (fun j => ∏ p ∈ blocks j, (1 - g p))
    (fun j => bonferroniModel (blocks j) (2 * (L + j) - 1) g)
    (fun j => bonferroniModel (blocks j) (2 * (L + j)) g) error
    hV hupper hgap (hsum.trans hsmall)
  have hprod0 : 0 ≤ ∏ j ∈ Finset.range J, ∏ p ∈ blocks j, (1 - g p) := Finset.prod_nonneg hV
  have hcompare := mul_le_mul_of_nonneg_right (sub_le_sub_left hsum 1) hprod0
  exact hcompare.trans hmain

end Erdos676
