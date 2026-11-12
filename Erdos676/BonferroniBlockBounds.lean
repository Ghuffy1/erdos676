import Erdos676.BonferroniTail
import Erdos676.ProductBrackets

open scoped BigOperators

namespace Erdos676

theorem bonferroniModel_relative_gap {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) (hk : Even (k + 1)) (C : ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1 / 2)
    (hC : (∑ p ∈ s, g p) ≤ C) :
    bonferroniModel s (k + 1) g - bonferroniModel s k g ≤
      (Real.exp (4 * C) / (2 : ℝ) ^ (k + 1)) * bonferroniModel s (k + 1) g := by
  have hV := survival_product_lower s g C (fun p _ => hg0 p) (fun p _ => hg1 p) hC
  have hcoef : 0 ≤ Real.exp (4 * C) / (2 : ℝ) ^ (k + 1) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hV hcoef
  have hexp : Real.exp (4 * C) * Real.exp (-2 * C) = Real.exp (2 * C) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : (Real.exp (4 * C) / (2 : ℝ) ^ (k + 1)) * Real.exp (-2 * C) =
      Real.exp (2 * C) / (2 : ℝ) ^ (k + 1) := by
    rw [div_mul_eq_mul_div, hexp]
  rw [hid] at hscaled
  have hupper := bonferroniModel_even_upper g s (k + 1) hk hg0 (fun p => by have := hg1 p; linarith)
  calc
    _ = ∑ d ∈ s.powersetCard (k + 1), ∏ p ∈ d, g p := bonferroniModel_gap g s k hk
    _ ≤ Real.exp (2 * C) / (2 : ℝ) ^ (k + 1) :=
      elementary_sum_geometric_bound s g (k + 1) C (fun p _ => hg0 p) hC
    _ ≤ (Real.exp (4 * C) / (2 : ℝ) ^ (k + 1)) * (∏ p ∈ s, (1 - g p)) := hscaled
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper hcoef

theorem product_bracket_relative_lower {J : Type*} [DecidableEq J]
    (s : Finset J) (V lower upper error : J → ℝ)
    (hV : ∀ j ∈ s, 0 ≤ V j) (hupper : ∀ j ∈ s, V j ≤ upper j)
    (hgap : ∀ j ∈ s, upper j - lower j ≤ error j * upper j)
    (herror : (∑ j ∈ s, error j) ≤ 1) :
    (1 - ∑ j ∈ s, error j) * (∏ j ∈ s, V j) ≤
      (∏ j ∈ s, upper j) - bracketLoss s lower upper := by
  have hU : ∀ j ∈ s, 0 ≤ upper j := fun j hj => (hV j hj).trans (hupper j hj)
  have hprod : (∏ j ∈ s, V j) ≤ ∏ j ∈ s, upper j := Finset.prod_le_prod₀ hV hupper
  have hloss : bracketLoss s lower upper ≤ (∑ j ∈ s, error j) * (∏ j ∈ s, upper j) := by
    unfold bracketLoss
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hnonneg : 0 ≤ ∏ i ∈ s.erase j, upper i :=
      Finset.prod_nonneg (fun i hi => hU i (Finset.mem_of_mem_erase hi))
    calc
      _ ≤ (error j * upper j) * (∏ i ∈ s.erase j, upper i) :=
        mul_le_mul_of_nonneg_right (hgap j hj) hnonneg
      _ = error j * (∏ i ∈ s, upper i) := by
        rw [mul_assoc, Finset.mul_prod_erase s upper hj]
  have hscaled := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr herror)
  nlinarith

end Erdos676
