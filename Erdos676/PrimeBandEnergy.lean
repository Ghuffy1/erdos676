import Erdos676.PrimeSampling
import Erdos676.FrequencyCount
import Erdos676.SmoothedFourier

open scoped BigOperators

namespace Erdos676

theorem retained_prime_band_energy {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime)
    (hinj : Function.Injective a) (D : ℝ) (hD : 0 ≤ D)
    (hsmall : ∀ p, D * a p < 1) (H J N : ℕ) (hH : 0 < H) (hN : 0 < N) (S : ℤ)
    (hsize : ∀ p q, (a p : ℝ) ^ 2 * (a q : ℝ) ^ 2 ≤ 2 * N) :
    (∑ n ∈ Finset.range N, ‖∑ p : P, ∑ k ∈ retainedFrequencies ((a p) ^ 2) D,
      residueFourier (smallResidues (a p)) k * (boxMultiplier H (residueCharacter k)) ^ J *
        residueCharacter k (S + n)‖ ^ 2) ≤ 512 * N * Fintype.card P * D := by
  classical
  let Q := Σ p : P, retainedFrequencies ((a p) ^ 2) D
  let prime (q : Q) := a q.1
  let label (q : Q) := q.2.val.valMinAbs
  let coeff (q : Q) := residueFourier (smallResidues (a q.1)) q.2.val *
    (boxMultiplier H (residueCharacter q.2.val)) ^ J
  have hpQ (q : Q) : (prime q).Prime := hprime q.1
  have hnQ (q : Q) : label q ≠ 0 := by
    intro h
    have hk := (Finset.mem_filter.mp q.2.property).2.1
    exact hk ((ZMod.valMinAbs_eq_zero q.2.val).mp h)
  have hsQ (q : Q) : (label q).natAbs < prime q := by
    have hp0 : (0 : ℝ) < a q.1 := by exact_mod_cast (hprime q.1).pos
    have hfreq := (Finset.mem_filter.mp q.2.property).2.2
    unfold residueFrequency at hfreq
    rw [abs_div, Nat.cast_pow, abs_of_pos (sq_pos_of_pos hp0)] at hfreq
    have habs := (div_le_iff₀ (sq_pos_of_pos hp0)).mp hfreq
    have hcut := mul_lt_mul_of_pos_left (hsmall q.1) hp0
    have hreal : |(label q : ℝ)| < (prime q : ℝ) := by
      dsimp [label, prime]
      nlinarith
    have hreal' : ((label q).natAbs : ℝ) < (prime q : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal
    exact_mod_cast hreal'
  have hinjQ : ∀ i j : Q, prime i = prime j → label i = label j → i = j := by
    rintro ⟨p, k⟩ ⟨q, l⟩ hpq hkl
    have hpq' : p = q := hinj hpq
    subst q
    have hfreq : k.val = l.val := ZMod.valMinAbs_inj.mp hkl
    have hkl' : k = l := Subtype.ext hfreq
    subst l
    rfl
  have henergy := prime_frequency_sampling_bound (Finset.univ : Finset Q) prime label coeff S N hN
    (fun q _ => hpQ q) (fun q _ => hnQ q) (fun q _ => hsQ q)
    (fun i _ j _ => hinjQ i j) (fun i _ j _ => hsize i.1 j.1)
  have hmass : (∑ q : Q, ‖coeff q‖ ^ 2) ≤ (Fintype.card P : ℝ) * (2 * D) := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ p : P, ∑ k : retainedFrequencies ((a p) ^ 2) D,
          ‖residueFourier (smallResidues (a p)) k.val‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro k hk
        have hm := norm_boxMultiplier_le_one H hH (residueCharacter k.val) (residueCharacter_norm k.val)
        have hpow := pow_le_one₀ (norm_nonneg _) hm (n := J)
        have hmul := mul_le_mul_of_nonneg_left hpow (norm_nonneg (residueFourier (smallResidues (a p)) k.val))
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [coeff, norm_mul, norm_pow, mul_one] using hmul
      _ ≤ ∑ p : P, (2 * D) := by
        apply Finset.sum_le_sum
        intro p hp
        have heq := Finset.sum_coe_sort (retainedFrequencies ((a p) ^ 2) D)
          (fun k => ‖residueFourier (smallResidues (a p)) k‖ ^ 2)
        rw [heq]
        exact retained_prime_fourier_mass (a p) (hprime p).one_lt.le D hD
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hseries (n : ℕ) : (∑ q : Q, coeff q * realCharacter ((label q : ℝ) / (prime q : ℝ) ^ 2) (S + n)) =
      ∑ p : P, ∑ k ∈ retainedFrequencies ((a p) ^ 2) D,
        residueFourier (smallResidues (a p)) k * (boxMultiplier H (residueCharacter k)) ^ J *
          residueCharacter k (S + n) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    have heq := Finset.sum_coe_sort (retainedFrequencies ((a p) ^ 2) D)
      (fun k => residueFourier (smallResidues (a p)) k * (boxMultiplier H (residueCharacter k)) ^ J *
        residueCharacter k (S + n))
    rw [← heq]
    apply Finset.sum_congr rfl
    intro k hk
    have hfreq : (label ⟨p, k⟩ : ℝ) / (prime ⟨p, k⟩ : ℝ) ^ 2 = residueFrequency k.val := by
      simp only [label, prime, residueFrequency, Nat.cast_pow]
    rw [hfreq, ← residueCharacter_eq_realCharacter]
  simp only [hseries] at henergy
  have hscaled := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 256 * (N : ℝ) by positivity)
  nlinarith

end Erdos676
