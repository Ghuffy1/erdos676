import Erdos676.Assembly
import Erdos676.Specification

open scoped BigOperators

namespace Erdos676

theorem quantitative_restricted_mass {ι : Type*} [DecidableEq ι]
    (I U : Finset ι) (f : ι → ℝ) (hUI : U ⊆ I) {N V d e : ℝ}
    (hN : 0 ≤ N) (hV : 0 ≤ V) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (he : 0 ≤ e) (heSmall : e ≤ d / 8)
    (hfirst : (1 - e) * N * V ≤ ∑ x ∈ I, f x)
    (hsecond : (∑ x ∈ I, (f x) ^ 2) ≤ (1 + e) * N * V ^ 2)
    (hcomplement : ((I \ U).card : ℝ) ≤ (1 - d) * N) :
    (d / 8) * N * V ≤ ∑ x ∈ U, f x := by
  have hsplit := Finset.sum_sdiff (f := f) hUI
  have hcs := sq_sum_le_card_mul_sum_sq (s := I \ U) (f := f)
  have hsquares : (∑ x ∈ I \ U, (f x) ^ 2) ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ => sq_nonneg (f x))
  have hQ0 : 0 ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg (f x)
  have hupper := hcs.trans (mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _))
  have hproduct := mul_le_mul hcomplement hsecond hQ0
    (mul_nonneg (sub_nonneg.mpr hd1) hN)
  have hcoef : (1 - d) * (1 + e) ≤ (1 - d / 4) ^ 2 := by
    nlinarith [mul_nonneg hd he, sq_nonneg d]
  have hscaled := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg N) (sq_nonneg V))
  have hcap0 : 0 ≤ (1 - d / 4) * N * V := by
    apply mul_nonneg _ hV
    apply mul_nonneg _ hN
    linarith
  have hcap : (∑ x ∈ I \ U, f x) ≤ (1 - d / 4) * N * V := by
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_right heSmall (mul_nonneg hN hV)
  nlinarith

/-- The quantitative finite endpoint for the actual prime-avoidance averages. -/
theorem quantitative_dyadic_count (X z H : ℕ) (U : Finset ℕ)
    (hH : 0 < H) (hU : U ⊆ Finset.Ioc X (2 * X)) {V d e : ℝ}
    (hV : 0 ≤ V) (hd : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (heSmall : e ≤ d / 8)
    (hfirst : (1 - e) * X * V ≤
      ∑ n ∈ Finset.Ioc X (2 * X), smallAverage z H n)
    (hsecond : (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage z H n) ^ 2) ≤
      (1 + e) * X * V ^ 2)
    (hcomplement : (((Finset.Ioc X (2 * X)) \ U).card : ℝ) ≤ (1 - d) * X)
    (hlarge : ∀ n ∈ U, ∀ j < H, LargeAvoidance z (n + j))
    (hshift : ∀ n ∈ U, ∀ j < H, X < n + j ∧ n + j ≤ 2 * X) :
    (d / 8) * X * V ≤ (dyadicExceptions X).card := by
  have hmass := quantitative_restricted_mass (Finset.Ioc X (2 * X)) U
    (smallAverage z H) hU
    (Nat.cast_nonneg X) hV hd hd1 he heSmall hfirst hsecond hcomplement
  have hcount := smallAverage_mass_le_exceptions U (dyadicExceptions X) z H hH hlarge (by
    intro n hn j hj hexc
    exact (mem_dyadicExceptions X (n + j)).mpr
      ⟨(hshift n hn j hj).1, (hshift n hn j hj).2, hexc⟩)
  exact hmass.trans hcount

end Erdos676
