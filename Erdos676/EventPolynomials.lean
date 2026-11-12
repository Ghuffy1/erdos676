import Erdos676.SelbergSquare
import Erdos676.SelbergMixture
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open scoped BigOperators

namespace Erdos676

noncomputable def eventBasis {P N : Type*} (g : P → ℝ) (r : Finset P)
    (E : P → N → Prop) (n : N) : ℝ := by
  classical
  exact ∏ p ∈ r, (1 - (if E p n then 1 else 0) / g p)

noncomputable def basisCoefficient {P : Type*} (g : P → ℝ) (d : Finset P) : ℝ :=
  ∏ p ∈ d, (-1 / g p)

theorem eventBasis_expansion {P N : Type*} [DecidableEq P]
    (g : P → ℝ) (r : Finset P) (E : P → N → Prop) (n : N) :
    eventBasis g r E n = ∑ d ∈ r.powerset, basisCoefficient g d * eventProduct E d n := by
  classical
  unfold eventBasis
  have hfactor (p : P) : 1 - (if E p n then 1 else 0) / g p =
      (-1 / g p) * (if E p n then 1 else 0) + 1 := by ring
  simp_rw [hfactor]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib]
  rw [Finset.prod_boole]
  rfl

theorem eventBasis_pattern {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r t : Finset P) :
    eventBasis g r (fun p u => p ∈ u) t = bernoulliBasis g r t := by
  classical
  have hext : bernoulliBasis g r t =
      ∏ p : P, if p ∈ r then (if p ∈ t then 1 - 1 / g p else 1) else 1 := by
    unfold bernoulliBasis
    apply Finset.prod_congr rfl
    intro p _
    by_cases hr : p ∈ r <;> by_cases ht : p ∈ t <;> simp [hr, ht]
  rw [hext, Finset.prod_ite_mem_eq]
  unfold eventBasis
  apply Finset.prod_congr rfl
  intro p _
  by_cases ht : p ∈ t <;> simp [ht]

theorem basisCoefficient_abs_sum {P : Type*} [DecidableEq P]
    (g : P → ℝ) (r : Finset P) :
    (∑ d ∈ r.powerset, |basisCoefficient g d|) = ∏ p ∈ r, (1 + |1 / g p|) := by
  have h := Finset.prod_add (fun p => |(-1 : ℝ) / g p|) (fun _ => (1 : ℝ)) r
  simpa only [basisCoefficient, Finset.abs_prod, Finset.prod_const_one, mul_one,
    abs_div, abs_neg, abs_one, add_comm] using h.symm

theorem basisCoefficient_abs_sum_le {P : Type*} [DecidableEq P]
    (g size : P → ℝ) (r : Finset P)
    (hsize : ∀ p ∈ r, 2 ≤ size p) (hrecip : ∀ p ∈ r, |1 / g p| ≤ size p) :
    (∑ d ∈ r.powerset, |basisCoefficient g d|) ≤ (∏ p ∈ r, size p) ^ 2 := by
  rw [basisCoefficient_abs_sum, ← Finset.prod_pow]
  apply Finset.prod_le_prod₀
  · intro p hp
    positivity
  · intro p hp
    have hs := hsize p hp
    have hg := hrecip p hp
    nlinarith

end Erdos676
