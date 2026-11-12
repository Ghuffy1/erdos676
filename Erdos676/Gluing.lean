import Erdos676.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators

namespace Erdos676

/-- The finite Cauchy–Schwarz step used to combine both sieve ranges. -/
theorem restricted_mass_lower_bound {ι : Type*} [DecidableEq ι]
    (I U : Finset ι) (f : ι → ℝ) (hUI : U ⊆ I)
    (hf : ∀ x ∈ I, 0 ≤ f x) :
    (∑ x ∈ I, f x) -
        Real.sqrt ((I \ U).card * ∑ x ∈ I, (f x) ^ 2) ≤
      ∑ x ∈ U, f x := by
  have hsplit : (∑ x ∈ I \ U, f x) + (∑ x ∈ U, f x) = ∑ x ∈ I, f x :=
    Finset.sum_sdiff hUI
  have hcs := sq_sum_le_card_mul_sum_sq (s := I \ U) (f := f)
  have hsquares : (∑ x ∈ I \ U, (f x) ^ 2) ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ => sq_nonneg (f x))
  have hcard : (0 : ℝ) ≤ (I \ U).card := Nat.cast_nonneg _
  have hnonneg : 0 ≤ ((I \ U).card : ℝ) * ∑ x ∈ I, (f x) ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg (fun x _ => sq_nonneg (f x)))
  have hbound : (∑ x ∈ I \ U, f x) ≤
      Real.sqrt ((I \ U).card * ∑ x ∈ I, (f x) ^ 2) := by
    apply (Real.le_sqrt (Finset.sum_nonneg (fun x hx => hf x (Finset.mem_sdiff.mp hx).1))
      hnonneg).mpr
    exact hcs.trans (mul_le_mul_of_nonneg_left hsquares hcard)
  linarith

/-- A finite weighted count is bounded by the support cardinality when every weight is at most one. -/
theorem mass_le_card {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀ x ∈ S, f x ≤ 1) : ∑ x ∈ S, f x ≤ S.card := by
  simpa using Finset.sum_le_sum h

/-- A strict second-moment gap forces positive mass on the designated subset. -/
theorem positive_restricted_mass_of_moment_gap {ι : Type*} [DecidableEq ι]
    (I U : Finset ι) (f : ι → ℝ) (hUI : U ⊆ I)
    (hf : ∀ x ∈ I, 0 ≤ f x)
    (hfirst : 0 < ∑ x ∈ I, f x)
    (hgap : ((I \ U).card : ℝ) * (∑ x ∈ I, (f x) ^ 2) <
      (∑ x ∈ I, f x) ^ 2) :
    0 < ∑ x ∈ U, f x := by
  have hsplit := Finset.sum_sdiff (f := f) hUI
  have hcs := sq_sum_le_card_mul_sum_sq (s := I \ U) (f := f)
  have hsq : (∑ x ∈ I \ U, (f x) ^ 2) ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ => sq_nonneg (f x))
  have hupper := hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
  have hnonneg : 0 ≤ ∑ x ∈ I \ U, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_sdiff.mp hx).1
  by_contra h
  have hu : (∑ x ∈ U, f x) ≤ 0 := le_of_not_gt h
  nlinarith

/-- Linear avoidance gains dominate quadratic moment losses. -/
theorem scalar_moment_gap {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hsmall : 3 * e < d) :
    (1 - d) * (1 + e) < (1 - e) ^ 2 := by
  have : 0 ≤ d * e := mul_nonneg hd he
  nlinarith [sq_nonneg e]

end Erdos676
