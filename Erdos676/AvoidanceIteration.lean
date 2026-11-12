import Erdos676.ResidueBoundaryCounts

open scoped BigOperators

namespace Erdos676

theorem avoid_indicator_lower {P : Type*} [Fintype P] (B : P → Prop) [DecidablePred B] :
    1 - (∑ p : P, if B p then (1 : ℝ) else 0) ≤ if ∀ p, ¬B p then 1 else 0 := by
  classical
  have h := finite_union_indicator_le B
  by_cases hall : ∀ p, ¬B p
  · simp [hall]
  · have hex : ∃ p, B p := by simpa only [not_forall, not_not] using hall
    simp only [hall, hex, ite_true, ite_false] at h ⊢
    linarith

theorem avoid_filter_card_lower {I P : Type*} [Fintype P] (U : Finset I)
    (B : P → I → Prop) [∀ p, DecidablePred (B p)] :
    letI : DecidablePred (fun n => ∀ p, ¬B p n) := Classical.decPred _
    (U.card : ℝ) - (∑ n ∈ U, ∑ p : P, if B p n then (1 : ℝ) else 0) ≤
      (U.filter (fun n => ∀ p, ¬B p n)).card := by
  classical
  have h := Finset.sum_le_sum (fun n (_ : n ∈ U) => avoid_indicator_lower (fun p => B p n))
  have hcard : ((U.filter (fun n => ∀ p, ¬B p n)).card : ℝ) =
      ∑ n ∈ U, if ∀ p, ¬B p n then (1 : ℝ) else 0 := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert n U hn ih => by_cases hcond : ∀ p, ¬B p n <;> simp [hn, hcond, ih]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [← hcard] at h
  convert h using 1
  apply congrArg (fun s : Finset I => (s.card : ℝ))
  ext n
  simp

theorem avoidance_block_lower {I P : Type*} [Fintype P] (U : Finset I)
    (B : P → I → Prop) [∀ p, DecidablePred (B p)] (mass error : ℝ)
    (hcount : (∑ n ∈ U, ∑ p : P, if B p n then (1 : ℝ) else 0) ≤ mass * U.card + error) :
    letI : DecidablePred (fun n => ∀ p, ¬B p n) := Classical.decPred _
    (1 - mass) * U.card - error ≤ (U.filter (fun n => ∀ p, ¬B p n)).card := by
  have h := avoid_filter_card_lower U B
  nlinarith

theorem finite_affine_iteration_lower (y : ℕ → ℝ) (d e : ℝ) (N : ℕ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e)
    (hstep : ∀ n < N, d * y n - e ≤ y (n + 1)) :
    d ^ N * y 0 - N * e ≤ y N := by
  have haux : ∀ n ≤ N, d ^ n * y 0 - n * e ≤ y n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hprev := ih (by omega)
        have hrec := hstep n (by omega)
        have hscaled := mul_le_mul_of_nonneg_left hprev hd0
        have herror := mul_le_mul_of_nonneg_right hd1 (show 0 ≤ (n : ℝ) * e by positivity)
        rw [pow_succ]
        push_cast
        nlinarith
  exact haux N le_rfl

end Erdos676
