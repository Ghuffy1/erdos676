import Erdos676.MertensInputs
import Erdos676.BernoulliMoments

open scoped BigOperators

namespace Erdos676

theorem prime_log_reciprocal_upper {z : ℝ} (hz : 1 ≤ z) :
    (∑ p ∈ primesUpToReal z, Real.log p / p) ≤ Real.log z + (Real.log 4 + 4) := by
  have h := (abs_le.mp (Mertens.sum_log_prime_div_eq_log hz)).2
  change (∑ p ∈ primesUpToReal z, Real.log p / p) - Real.log z ≤ Real.log 4 + 4 at h
  linarith

theorem prime_log_moments {z : ℝ} (hz : 2 ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ primesUpToReal z, 0 ≤ g p)
    (hg : ∀ p ∈ primesUpToReal z, g p ≤ 2 / p) :
    (∑ p ∈ primesUpToReal z, g p * Real.log p) ≤ 4 * Real.log z ∧
      (∑ p ∈ primesUpToReal z, g p * (Real.log p) ^ 2) ≤ 4 * (Real.log z) ^ 2 := by
  have hL : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hfirst : (∑ p ∈ primesUpToReal z, g p * Real.log p) ≤ 4 * Real.log z := by
    calc
      _ ≤ ∑ p ∈ primesUpToReal z, (2 / p) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (hg p hp) (Real.log_natCast_nonneg p)
      _ = 2 * (∑ p ∈ primesUpToReal z, Real.log p / p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (Real.log z + (Real.log 4 + 4)) := by
        exact mul_le_mul_of_nonneg_left (prime_log_reciprocal_upper (by linarith)) (by norm_num)
      _ ≤ 4 * Real.log z := by linarith
  refine ⟨hfirst, ?_⟩
  calc
    _ ≤ ∑ p ∈ primesUpToReal z, Real.log z * (g p * Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpz : (p : ℝ) ≤ z := by
        have hp' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
        exact (Nat.cast_le.mpr hp').trans (Nat.floor_le (by linarith))
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Finset.mem_filter.mp hp).2.pos
      have hlog := Real.log_le_log hp0 hpz
      have hnonneg := mul_nonneg (hg0 p hp) (Real.log_natCast_nonneg p)
      have h := mul_le_mul_of_nonneg_right hlog hnonneg
      nlinarith
    _ = Real.log z * (∑ p ∈ primesUpToReal z, g p * Real.log p) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log z * (4 * Real.log z) := mul_le_mul_of_nonneg_left hfirst hL
    _ = 4 * (Real.log z) ^ 2 := by ring

theorem bernoulli_prime_log_second_moment {z : ℝ} (hz : 2 ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ primesUpToReal z, 0 ≤ g p)
    (hg : ∀ p ∈ primesUpToReal z, g p ≤ 2 / p) :
    (∑ t ∈ (primesUpToReal z).powerset, bernoulliWeight (primesUpToReal z) t g *
      (∑ p ∈ t, Real.log p) ^ 2) ≤ 20 * (Real.log z) ^ 2 := by
  have h := prime_log_moments hz hlarge g hg0 hg
  have hfirst0 : 0 ≤ ∑ p ∈ primesUpToReal z, g p * Real.log p :=
    Finset.sum_nonneg fun p hp => mul_nonneg (hg0 p hp) (Real.log_natCast_nonneg p)
  have hsq : (∑ p ∈ primesUpToReal z, g p * Real.log p) ^ 2 ≤
      (4 * Real.log z) ^ 2 := by nlinarith [h.1]
  have hbound := bernoulli_second_moment_le (primesUpToReal z) g (fun p => Real.log p)
  nlinarith [h.2]

theorem prime_sieve_normalizer_tail {z R : ℝ} (hz : 2 ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (hR : 0 ≤ R) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ primesUpToReal z, 0 ≤ g p)
    (hg : ∀ p ∈ primesUpToReal z, g p ≤ 2 / p)
    (hg1 : ∀ p ∈ primesUpToReal z, g p < 1) :
    (1 - (∑ t ∈ (primesUpToReal z).powerset with (∑ p ∈ (t : Finset ℕ), Real.log p) ≤ R,
        ∏ p ∈ t, g p / (1 - g p)) * (∏ p ∈ primesUpToReal z, (1 - g p))) * R ^ 2 ≤
      20 * (Real.log z) ^ 2 := by
  classical
  rw [truncated_sieve_normalization (primesUpToReal z) g _
    (fun p hp => ne_of_lt (hg1 p hp))]
  exact (bernoulli_truncation_bound (primesUpToReal z) g
    (fun t => ∑ p ∈ t, Real.log p) R hR hg0 (fun p hp => (hg1 p hp).le)).trans
      (bernoulli_prime_log_second_moment hz hlarge g hg0 hg)

end Erdos676
