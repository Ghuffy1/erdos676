import Erdos676.BernoulliMoments

open scoped BigOperators

namespace Erdos676

theorem bernoulli_product_split {P : Type*} [DecidableEq P]
    (s t : Finset P) (a b : P → ℝ) (ht : t ⊆ s) :
    (∏ p ∈ s, if p ∈ t then a p else b p) =
      (∏ p ∈ t, a p) * ∏ p ∈ s \ t, b p := by
  let f (p : P) := if p ∈ t then a p else b p
  have hleft : (∏ p ∈ s \ t, f p) = ∏ p ∈ s \ t, b p := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [f, (Finset.mem_sdiff.mp hp).2]
  have hright : (∏ p ∈ t, f p) = ∏ p ∈ t, a p := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [f, hp]
  change (∏ p ∈ s, f p) = _
  rw [← Finset.prod_sdiff ht, hleft, hright]
  ring

theorem bernoulli_product_expectation {P : Type*} [DecidableEq P]
    (s : Finset P) (g a b : P → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g *
      (∏ p ∈ s, if p ∈ t then a p else b p)) =
      ∏ p ∈ s, (g p * a p + (1 - g p) * b p) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t ht
  rw [bernoulli_product_split s t a b (Finset.mem_powerset.mp ht)]
  simp only [bernoulliWeight, Finset.prod_mul_distrib]
  ring

noncomputable def bernoulliBasis {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r t : Finset P) : ℝ :=
  ∏ p : P, if p ∈ t then (if p ∈ r then 1 - 1 / g p else 1) else 1

theorem bernoulliBasis_empty {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r : Finset P) : bernoulliBasis g r ∅ = 1 := by
  simp [bernoulliBasis]

theorem bernoulliBasis_product_expectation {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r u : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g * bernoulliBasis g r t *
      bernoulliBasis g u t) =
      ∏ p : P, (g p * ((if p ∈ r then 1 - 1 / g p else 1) *
        (if p ∈ u then 1 - 1 / g p else 1)) + (1 - g p)) := by
  have hprod (t : Finset P) : bernoulliBasis g r t * bernoulliBasis g u t =
      ∏ p : P, if p ∈ t then ((if p ∈ r then 1 - 1 / g p else 1) *
        (if p ∈ u then 1 - 1 / g p else 1)) else 1 := by
    unfold bernoulliBasis
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p ∈ t <;> simp [hp]
  calc
    _ = ∑ t : Finset P, bernoulliWeight Finset.univ t g *
        (∏ p : P, if p ∈ t then ((if p ∈ r then 1 - 1 / g p else 1) *
          (if p ∈ u then 1 - 1 / g p else 1)) else 1) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← hprod]
      ring
    _ = _ := by
      simpa only [Finset.powerset_univ, mul_one] using
        bernoulli_product_expectation Finset.univ g
          (fun p => (if p ∈ r then 1 - 1 / g p else 1) *
            (if p ∈ u then 1 - 1 / g p else 1)) (fun _ => 1)

end Erdos676
