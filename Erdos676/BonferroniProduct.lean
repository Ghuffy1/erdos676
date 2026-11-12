import Erdos676.DisjointPolynomial

open scoped BigOperators

namespace Erdos676

theorem bonferroni_product_count_error {J P N : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq P]
    (I : Finset N) (blocks : J → Finset P) (k : J → ℕ)
    (E : P → N → Prop) (g a : P → ℝ) (M : ℝ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hcount : ∀ d : Finset P,
      |(∑ n ∈ I, eventProduct E d n) - M * (∏ p ∈ d, g p)| ≤ ∏ p ∈ d, a p) :
    |(∑ n ∈ I, ∏ j : J, bonferroniEvent (blocks j) (k j) E n) -
      M * (∏ j : J, bonferroniModel (blocks j) (k j) g)| ≤
      ∏ j : J, ∑ d ∈ bonferroniSupport (blocks j) (k j), ∏ p ∈ d, a p := by
  let T (j : J) := bonferroniSupport (blocks j) (k j)
  let c (_ : J) (d : Finset P) : ℝ := (-1) ^ d.card
  have hpair : ∀ i j, i ≠ j → ∀ d ∈ T i, ∀ e ∈ T j, Disjoint d e := by
    intro i j hij d hd e he
    have hd' : d ⊆ blocks i := Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
    have he' : e ⊆ blocks j := Finset.mem_powerset.mp (Finset.mem_filter.mp he).1
    exact (hdisjoint hij).mono hd' he'
  have h := disjoint_polynomial_transfer I T c E g a M hpair (fun b _ => hcount _)
  simpa only [bonferroniEvent_expansion, bonferroniModel_expansion, T, c,
    abs_pow, abs_neg, abs_one, one_pow, one_mul] using h

end Erdos676
