import Erdos676.SingularThreeRanges
import Erdos676.PrimeIntervals
import Erdos676.PrimeSquarePeriod

open scoped BigOperators

namespace Erdos676

theorem singular_cutoff_mean_bound (y₀ y₁ y₂ : ℝ) (H : ℕ)
    (h01 : y₀ ≤ y₁) (h12 : y₁ ≤ y₂) (hfloor : 1 ≤ ⌊y₀⌋₊) (hH : 0 < H) :
    pairMean H (singularFactorProduct y₂) ≤
      1 + (primeSquarePeriod y₀ : ℝ) / H +
      4 * singularMajorant (primesUpToReal y₁ \ primesUpToReal y₀) *
        ((⌊y₀⌋₊ : ℝ)⁻¹ + ⌊y₁⌋₊ * (primeSquarePeriod y₀ : ℝ) / H) +
      4 * singularMajorant (primesUpToReal y₂) *
        ((⌊y₁⌋₊ : ℝ)⁻¹ + (⌊y₂⌋₊ : ℝ) / H) := by
  have hprime (y : ℝ) : ∀ p ∈ primesUpToReal y, p.Prime :=
    fun p hp => ((mem_primesUpToReal y p).mp hp).1
  have h := singular_three_ranges_mean_bound (primesUpToReal y₀) (primesUpToReal y₁)
    (primesUpToReal y₂) (primesUpToReal_subset h01) (primesUpToReal_subset h12)
    (hprime y₂) H ⌊y₀⌋₊ ⌊y₁⌋₊ ⌊y₂⌋₊ hH hfloor (Nat.floor_mono h01) (Nat.floor_mono h12)
    prime_band_subset_Ioc prime_band_subset_Ioc
  have hc1 : ((primesUpToReal y₁ \ primesUpToReal y₀).card : ℝ) ≤ ⌊y₁⌋₊ :=
    by exact_mod_cast (prime_band_card_le (x := y₀) (y := y₁))
  have hc2 : ((primesUpToReal y₂ \ primesUpToReal y₁).card : ℝ) ≤ ⌊y₂⌋₊ :=
    by exact_mod_cast (prime_band_card_le (x := y₁) (y := y₂))
  have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
  have hterm1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg (primeSquarePeriod y₀))) hH0
  have hterm2 := div_le_div_of_nonneg_right hc2 hH0
  have hmajor1 : 0 ≤ singularMajorant (primesUpToReal y₁ \ primesUpToReal y₀) :=
    singularMajorant_nonneg _ (fun p hp => hprime y₁ p (Finset.mem_sdiff.mp hp).1)
  have hmajor2 := singularMajorant_nonneg _ (hprime y₂)
  have hscaled1 := mul_le_mul_of_nonneg_left hterm1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmajor1)
  have hscaled2 := mul_le_mul_of_nonneg_left hterm2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmajor2)
  change pairMean H (singularProductOn (primesUpToReal y₂)) ≤ _
  change pairMean H (singularProductOn (primesUpToReal y₂)) ≤
    1 + (primeSquarePeriod y₀ : ℝ) / H + _ + _ at h
  have hM : (∏ p ∈ primesUpToReal y₀, p ^ 2) = primeSquarePeriod y₀ := rfl
  rw [hM] at h
  nlinarith

end Erdos676
