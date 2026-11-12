import Erdos676.PrimeBandSmoothing
import Erdos676.PowerCutoffs

open scoped BigOperators

namespace Erdos676

theorem prime_family_card_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hz : 0 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z) :
    (Fintype.card P : ℝ) ≤ z := by
  have hsub : Finset.univ.image a ⊆ Finset.Ioc 0 ⌊z⌋₊ := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_Ioc.mpr ⟨(hprime p).pos, Nat.le_floor (hle p)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show (Fintype.card P : ℝ) ≤ ⌊z⌋₊ by exact_mod_cast hcard).trans (Nat.floor_le hz)

theorem prime_family_sum_le_square {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hz : 0 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z) :
    (∑ p : P, (a p : ℝ)) ≤ z ^ 2 := by
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) => hle p)
  have hcard := mul_le_mul_of_nonneg_right (prime_family_card_le a hinj hprime z hz hle) hz
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

theorem smoothed_prime_band_energy_size {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (z D : ℝ) (hz : 0 ≤ z) (hD : 0 < D) (hle : ∀ p, (a p : ℝ) ≤ z)
    (hcut : D * z < 1) (H J N : ℕ) (hH : 0 < H) (hN : 0 < N) (S : ℤ)
    (hsize : z ^ 4 ≤ 2 * N) :
    (∑ n ∈ Finset.range N,
      ‖boxSmooth H J (primeBandSignal a) (S + n) - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2) ≤
      1024 * N * z * D + 2 * N * z ^ 4 * (1 / ((H : ℝ) * D)) ^ (2 * J) := by
  have hsmall (p : P) : D * a p < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle p) hD.le) hcut
  have hpair (p q : P) : (a p : ℝ) ^ 2 * (a q : ℝ) ^ 2 ≤ 2 * N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (a p)) (hle p) 2
    have hq := pow_le_pow_left₀ (Nat.cast_nonneg (a q)) (hle q) 2
    have h := mul_le_mul hp hq (sq_nonneg _) (sq_nonneg z)
    nlinarith
  have h := smoothed_prime_band_energy a hprime hinj D hD hsmall H J N hH hN S hpair
  have hcard := prime_family_card_le a hinj hprime z hz hle
  have hsum := prime_family_sum_le_square a hinj hprime z hz hle
  have hsum0 : 0 ≤ ∑ p : P, (a p : ℝ) := Finset.sum_nonneg (fun p hp => Nat.cast_nonneg _)
  have hsum2 := pow_le_pow_left₀ hsum0 hsum 2
  have hterm1 := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 1024 * (N : ℝ) * D by positivity)
  have hterm2 := mul_le_mul_of_nonneg_left hsum2
    (show 0 ≤ 2 * (N : ℝ) * (1 / ((H : ℝ) * D)) ^ (2 * J) by positivity)
  nlinarith

end Erdos676
