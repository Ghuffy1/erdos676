import Erdos676.BonferroniModel

open scoped BigOperators

namespace Erdos676

def bonferroniSupport {P : Type*} (s : Finset P) (k : ℕ) : Finset (Finset P) :=
  s.powerset.filter (fun d => d.card ≤ k)

theorem truncated_card_sum {P R : Type*} [Semiring R] (s : Finset P) (k : ℕ)
    (c : ℕ → R) (f : Finset P → R) :
    (∑ j ∈ Finset.range (k + 1), c j * (∑ d ∈ s.powersetCard j, f d)) =
      ∑ d ∈ bonferroniSupport s k, c d.card * f d := by
  classical
  simp only [Finset.powersetCard_eq_filter, Finset.sum_filter, Finset.mul_sum,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff,
    bonferroniSupport, Finset.sum_filter]

theorem bonferroniEvent_expansion {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) :
    bonferroniEvent s k E n =
      ∑ d ∈ bonferroniSupport s k, (-1 : ℝ) ^ d.card * eventProduct E d n :=
  truncated_card_sum s k (fun j => (-1 : ℝ) ^ j) (fun d => eventProduct E d n)

theorem bonferroniModel_expansion {P : Type*} (s : Finset P) (k : ℕ) (g : P → ℝ) :
    bonferroniModel s k g =
      ∑ d ∈ bonferroniSupport s k, (-1 : ℝ) ^ d.card * (∏ p ∈ d, g p) :=
  truncated_card_sum s k (fun j => (-1 : ℝ) ^ j) (fun d => ∏ p ∈ d, g p)

theorem eventProduct_biUnion {J P N : Type*} [DecidableEq J] [DecidableEq P]
    (s : Finset J) (d : J → Finset P) (E : P → N → Prop) (n : N) :
    eventProduct E (s.biUnion d) n = ∏ j ∈ s, eventProduct E (d j) n := by
  induction s using Finset.induction_on with
  | empty => simp [eventProduct]
  | @insert j s hj ih =>
      rw [Finset.biUnion_insert, eventProduct_union, Finset.prod_insert hj, ih]

end Erdos676
