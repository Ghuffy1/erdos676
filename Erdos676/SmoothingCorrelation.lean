import Erdos676.SmoothingSandwich
import Erdos676.Gluing

open scoped BigOperators

namespace Erdos676

theorem sum_deviation_bound {I : Type*} (W : Finset I) (F : I → ℝ) (μ E : ℝ)
    (hE : ∑ n ∈ W, (F n - μ) ^ 2 ≤ E) :
    |(∑ n ∈ W, F n) - μ * W.card| ≤ Real.sqrt (W.card * E) := by
  have hE0 : 0 ≤ E := (Finset.sum_nonneg (fun n hn => sq_nonneg (F n - μ))).trans hE
  have hcs := sq_sum_le_card_mul_sum_sq (s := W) (f := fun n => F n - μ)
  have hscaled := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg W.card)
  have hsum : (∑ n ∈ W, (F n - μ)) = (∑ n ∈ W, F n) - μ * W.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum] at hcs
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hE0)).mpr
  simpa only [sq_abs] using hcs.trans hscaled

theorem correlation_from_smoothing_bounds (L U V : Finset ℤ) (G F : ℤ → ℝ) (μ E M B : ℝ)
    (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (hlower : (∑ n ∈ L, F n) ≤ ∑ n ∈ U, G n)
    (hupper : (∑ n ∈ U, G n) ≤ ∑ n ∈ V, F n)
    (hEL : ∑ n ∈ L, (F n - μ) ^ 2 ≤ E)
    (hEV : ∑ n ∈ V, (F n - μ) ^ 2 ≤ E)
    (hLM : (L.card : ℝ) ≤ M) (hVM : (V.card : ℝ) ≤ M)
    (hLU : (U.card : ℝ) ≤ L.card + B) (hUV : (V.card : ℝ) ≤ U.card + B) :
    |(∑ n ∈ U, G n) - μ * U.card| ≤ Real.sqrt (M * E) + μ * B := by
  have hdl := sum_deviation_bound L F μ E hEL
  have hdv := sum_deviation_bound V F μ E hEV
  have hrootL := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hLM hE)
  have hrootV := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hVM hE)
  have hcl := mul_le_mul_of_nonneg_left hLU hμ
  have hcv := mul_le_mul_of_nonneg_left hUV hμ
  obtain ⟨hdl1, hdl2⟩ := abs_le.mp hdl
  obtain ⟨hdv1, hdv2⟩ := abs_le.mp hdv
  apply abs_le.mpr
  constructor <;> nlinarith

end Erdos676
