import Erdos676.IntegerKernel

open scoped BigOperators

namespace Erdos676

theorem floor_abs_le_abs_add_one (x : ℝ) : |(⌊x⌋ : ℝ)| ≤ |x| + 1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  exact abs_le.mpr ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

theorem inverse_square_floor_kernel (x : ℝ) :
    ((1 + |x|) ^ 2)⁻¹ ≤ 4 * ((1 + |(⌊x⌋ : ℝ)|) ^ 2)⁻¹ := by
  have hx : 0 < 1 + |x| := by positivity
  have hm : 0 < 1 + |(⌊x⌋ : ℝ)| := by positivity
  have hle : 1 + |(⌊x⌋ : ℝ)| ≤ 2 * (1 + |x|) := by
    linarith [floor_abs_le_abs_add_one x, abs_nonneg x]
  have hsq := pow_le_pow_left₀ hm.le hle 2
  simp only [← one_div, mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hx) (sq_pos_of_pos hm)).mpr
  nlinarith

theorem separated_floor_injective {P : Type*} (s : Finset P) (θ : P → ℝ) (L base : ℝ)
    (hL : 0 < L) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ L * |θ i - θ j|) :
    Set.InjOn (fun i => (⌊L * (θ i - base)⌋ : ℤ)) (s : Set P) := by
  intro i hi j hj heq
  change (⌊L * (θ i - base)⌋ : ℤ) = ⌊L * (θ j - base)⌋ at heq
  by_contra hij
  have hsep' := hsep i hi j hj hij
  have hlowi := Int.floor_le (L * (θ i - base))
  have hlowj := Int.floor_le (L * (θ j - base))
  have hupi := Int.lt_floor_add_one (L * (θ i - base))
  have hupj := Int.lt_floor_add_one (L * (θ j - base))
  rw [heq] at hlowi hupi
  have habs : |L * (θ i - θ j)| < 1 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  rw [abs_mul, abs_of_pos hL] at habs
  linarith

theorem separated_square_kernel_sum {P : Type*} (s : Finset P) (θ : P → ℝ) (L base : ℝ)
    (hL : 0 < L) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ L * |θ i - θ j|) :
    (∑ i ∈ s, ((1 + L * |θ i - base|) ^ 2)⁻¹) ≤ 16 := by
  have hinj := separated_floor_injective s θ L base hL hsep
  have hsum := indexed_integer_kernel_sum s (fun i => (⌊L * (θ i - base)⌋ : ℤ)) hinj
  have hpoint (i : P) : ((1 + L * |θ i - base|) ^ 2)⁻¹ ≤
      4 * ((1 + |((⌊L * (θ i - base)⌋ : ℤ) : ℝ)|) ^ 2)⁻¹ := by
    have h := inverse_square_floor_kernel (L * (θ i - base))
    simpa only [abs_mul, abs_of_pos hL] using h
  have hbound := Finset.sum_le_sum (fun i (_ : i ∈ s) => hpoint i)
  rw [← Finset.mul_sum] at hbound
  linarith

end Erdos676
