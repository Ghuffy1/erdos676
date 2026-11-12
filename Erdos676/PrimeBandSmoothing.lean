import Erdos676.PrimeBandEnergy
import Erdos676.FrequencyDecomposition

open scoped BigOperators

namespace Erdos676

noncomputable def primeBandSignal {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (n : ℤ) : ℂ :=
  ∑ p : P, residueIndicator (smallResidues (a p)) (n : ZMod ((a p) ^ 2))

noncomputable def retainedPrimeBand {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (H J : ℕ) (D : ℝ) (n : ℤ) : ℂ :=
  ∑ p : P, boxSmooth H J
    (residueFourierPart (smallResidues (a p)) (retainedFrequencies ((a p) ^ 2) D)) n

noncomputable def discardedPrimeBand {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (H J : ℕ) (D : ℝ) (n : ℤ) : ℂ :=
  ∑ p : P, boxSmooth H J
    (residueFourierPart (smallResidues (a p)) (discardedFrequencies ((a p) ^ 2) D)) n

theorem smoothed_prime_band_split {P : Type*} [Fintype P] (a : P → ℕ) [∀ p, NeZero (a p)]
    (hprime : ∀ p, (a p).Prime) (H J : ℕ) (hH : 0 < H) (D : ℝ) (n : ℤ) :
    boxSmooth H J (primeBandSignal a) n - (∑ p : P, 1 / (a p : ℂ)) =
      retainedPrimeBand a H J D n + discardedPrimeBand a H J D n := by
  unfold primeBandSignal
  rw [boxSmooth_sum]
  have hterm (p : P) := smoothed_indicator_decomposition (smallResidues (a p)) D H J hH n
  simp only [smallResidues_fourier_zero (a _) (hprime _).one_lt.le] at hterm
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun p hp => hterm p)
  simp only [Finset.sum_add_distrib] at hsum
  unfold retainedPrimeBand discardedPrimeBand
  rw [hsum]
  ring

theorem discardedPrimeBand_bound {P : Type*} [Fintype P] (a : P → ℕ) [∀ p, NeZero (a p)]
    (hprime : ∀ p, (a p).Prime) (H J : ℕ) (hH : 0 < H) (D : ℝ) (hD : 0 < D) (n : ℤ) :
    ‖discardedPrimeBand a H J D n‖ ≤ (∑ p : P, (a p : ℝ)) * (1 / ((H : ℝ) * D)) ^ J := by
  unfold discardedPrimeBand
  calc
    _ ≤ ∑ p : P, ‖boxSmooth H J
        (residueFourierPart (smallResidues (a p)) (discardedFrequencies ((a p) ^ 2) D)) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p : P, (a p : ℝ) * (1 / ((H : ℝ) * D)) ^ J := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [smallResidues_card (a p) (hprime p).one_lt.le] using
        smoothed_discarded_bound (smallResidues (a p)) D hD H J hH n
    _ = _ := by rw [Finset.sum_mul]

theorem smoothed_prime_band_energy {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (D : ℝ) (hD : 0 < D) (hsmall : ∀ p, D * a p < 1)
    (H J N : ℕ) (hH : 0 < H) (hN : 0 < N) (S : ℤ)
    (hsize : ∀ p q, (a p : ℝ) ^ 2 * (a q : ℝ) ^ 2 ≤ 2 * N) :
    (∑ n ∈ Finset.range N,
      ‖boxSmooth H J (primeBandSignal a) (S + n) - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2) ≤
      1024 * N * Fintype.card P * D +
        2 * N * (∑ p : P, (a p : ℝ)) ^ 2 * (1 / ((H : ℝ) * D)) ^ (2 * J) := by
  have hret := retained_prime_band_energy a hprime hinj D hD.le hsmall H J N hH hN S hsize
  have hret' : (∑ n ∈ Finset.range N, ‖retainedPrimeBand a H J D (S + n)‖ ^ 2) ≤
      512 * N * Fintype.card P * D := by
    simpa only [retainedPrimeBand, smoothed_residueFourierPart] using hret
  have hpoint (n : ℕ) :
      ‖boxSmooth H J (primeBandSignal a) (S + n) - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2 ≤
      2 * ‖retainedPrimeBand a H J D (S + n)‖ ^ 2 +
        2 * ((∑ p : P, (a p : ℝ)) * (1 / ((H : ℝ) * D)) ^ J) ^ 2 := by
    rw [smoothed_prime_band_split a hprime H J hH D]
    have htriangle := norm_add_le (retainedPrimeBand a H J D (S + n)) (discardedPrimeBand a H J D (S + n))
    have htail := discardedPrimeBand_bound a hprime H J hH D hD (S + n)
    have hn1 := norm_nonneg (retainedPrimeBand a H J D (S + n))
    have hn2 := norm_nonneg (discardedPrimeBand a H J D (S + n))
    have hn3 := norm_nonneg (retainedPrimeBand a H J D (S + n) + discardedPrimeBand a H J D (S + n))
    have hb : 0 ≤ (∑ p : P, (a p : ℝ)) * (1 / ((H : ℝ) * D)) ^ J := by positivity
    nlinarith [sq_nonneg (‖retainedPrimeBand a H J D (S + n)‖ - ‖discardedPrimeBand a H J D (S + n)‖)]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hpoint n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hpow : ((1 / ((H : ℝ) * D)) ^ J) ^ 2 = (1 / ((H : ℝ) * D)) ^ (2 * J) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [mul_pow, hpow] at hsum
  nlinarith

end Erdos676
