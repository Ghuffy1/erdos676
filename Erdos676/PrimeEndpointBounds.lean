import Erdos676.PrimeBandSize
import Mathlib.NumberTheory.Chebyshev

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem prime_family_card_le_count {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hle : ∀ p, (a p : ℝ) ≤ z) :
    Fintype.card P ≤ Nat.primeCounting ⌊z⌋₊ := by
  have hsub : Finset.univ.image a ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hle p), hprime p⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Nat.primesLE_card_eq_primeCounting] using hcard

universe u

theorem prime_endpoint_sum_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (a : P → ℕ),
        Function.Injective a → (∀ p, (a p).Prime) →
        (∀ p, (a p : ℝ) ≤ 2 * X ^ (1 / 2 : ℝ)) →
        (∑ p : P, (a p : ℝ)) ≤ ε * X := by
  let C := Real.log 4 + 1
  have hC : 0 < C := by dsimp [C]; have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith
  have hz : Tendsto (fun X : ℝ => 2 * X ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_atTop (by norm_num)
  have hpi := hz.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  have hlog := (Real.tendsto_log_atTop.comp hz).eventually_ge_atTop (max 1 (4 * C / ε))
  filter_upwards [hpi, hlog, eventually_gt_atTop (0 : ℝ)] with X hπ hl hx
  intro P instF instD a hinj hprime hle
  let z := 2 * X ^ (1 / 2 : ℝ)
  change max 1 (4 * C / ε) ≤ Real.log z at hl
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlogpos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hl)
  have hratio : 4 * C / Real.log z ≤ ε := by
    apply (div_le_iff₀ hlogpos).mpr
    have h := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hl)
    nlinarith
  have hsum : (∑ p : P, (a p : ℝ)) ≤ (Nat.primeCounting ⌊z⌋₊ : ℝ) * z := by
    have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) => hle p)
    have hc : (Fintype.card P : ℝ) ≤ Nat.primeCounting ⌊z⌋₊ := by
      exact_mod_cast prime_family_card_le_count a hinj hprime z hle
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right hc hz0.le)
  have hsquare : z ^ 2 = 4 * X := by
    have hp : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    dsimp [z]
    rw [mul_pow, hp]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_right hπ hz0.le
  have heq : C * z / Real.log z * z = (4 * C / Real.log z) * X := by
    have h := hsquare
    field_simp
    nlinarith
  change (Nat.primeCounting ⌊z⌋₊ : ℝ) * z ≤ C * z / Real.log z * z at hscaled
  rw [heq] at hscaled
  exact hsum.trans (hscaled.trans (mul_le_mul_of_nonneg_right hratio hx.le))

end Erdos676
