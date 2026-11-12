import Erdos676.ResidueFrequency
import Mathlib.Data.Int.Interval

open scoped BigOperators

namespace Erdos676

noncomputable def retainedFrequencies (m : ℕ) [NeZero m] (D : ℝ) : Finset (ZMod m) :=
  Finset.univ.filter (fun k => k ≠ 0 ∧ |residueFrequency k| ≤ D)

theorem retained_frequency_abs_bound {m : ℕ} [NeZero m] {D : ℝ} (hD : 0 ≤ D)
    {k : ZMod m} (hk : k ∈ retainedFrequencies m D) : k.valMinAbs.natAbs ≤ ⌊(m : ℝ) * D⌋₊ := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hfreq := (Finset.mem_filter.mp hk).2.2
  unfold residueFrequency at hfreq
  rw [abs_div, abs_of_pos hm] at hfreq
  have hmul := (div_le_iff₀ hm).mp hfreq
  apply Nat.le_floor
  have habs : (k.valMinAbs.natAbs : ℝ) = |(k.valMinAbs : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  nlinarith

theorem retainedFrequencies_card_le (m : ℕ) [NeZero m] (D : ℝ) (hD : 0 ≤ D) :
    (retainedFrequencies m D).card ≤ 2 * ⌊(m : ℝ) * D⌋₊ := by
  classical
  let M := ⌊(m : ℝ) * D⌋₊
  let target : Finset ℤ := (Finset.Icc (-(M : ℤ)) M).erase 0
  have hsub : (retainedFrequencies m D).image ZMod.valMinAbs ⊆ target := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have habs := retained_frequency_abs_bound hD hk
    have habs' : |k.valMinAbs| ≤ (M : ℤ) := by
      simpa only [Int.natCast_natAbs] using (show (k.valMinAbs.natAbs : ℤ) ≤ M by exact_mod_cast habs)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_Icc.mpr (abs_le.mp habs')⟩
    exact fun h => (Finset.mem_filter.mp hk).2.1 ((ZMod.valMinAbs_eq_zero k).mp h)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ ZMod.injective_valMinAbs] at hcard
  have htarget : target.card = 2 * M := by
    have hzero : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) M := by simp
    rw [show target = (Finset.Icc (-(M : ℤ)) M).erase 0 from rfl,
      Finset.card_erase_of_mem hzero, Int.card_Icc]
    omega
  rwa [htarget] at hcard

theorem retainedFrequencies_card_real_le (m : ℕ) [NeZero m] (D : ℝ) (hD : 0 ≤ D) :
    ((retainedFrequencies m D).card : ℝ) ≤ 2 * m * D := by
  have hcard : ((retainedFrequencies m D).card : ℝ) ≤ 2 * (⌊(m : ℝ) * D⌋₊ : ℝ) :=
    by exact_mod_cast retainedFrequencies_card_le m D hD
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) hD)
  nlinarith

theorem retained_prime_fourier_mass (p : ℕ) (hp : 1 ≤ p) (D : ℝ) (hD : 0 ≤ D) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k ∈ retainedFrequencies (p ^ 2) D, ‖residueFourier (smallResidues p) k‖ ^ 2) ≤ 2 * D := by
  letI : NeZero p := ⟨by omega⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hbound : (∑ k ∈ retainedFrequencies (p ^ 2) D, ‖residueFourier (smallResidues p) k‖ ^ 2) ≤
      ((retainedFrequencies (p ^ 2) D).card : ℝ) * (1 / (p : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ k ∈ retainedFrequencies (p ^ 2) D, (1 / (p : ℝ)) ^ 2 :=
        Finset.sum_le_sum (fun k hk => pow_le_pow_left₀ (norm_nonneg _) (smallResidues_fourier_norm_le p hp k) 2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hcount := retainedFrequencies_card_real_le (p ^ 2) D hD
  rw [Nat.cast_pow] at hcount
  have hscaled := mul_le_mul_of_nonneg_right hcount (sq_nonneg (1 / (p : ℝ)))
  have heq : (2 * (p : ℝ) ^ 2 * D) * (1 / (p : ℝ)) ^ 2 = 2 * D := by field_simp
  exact hbound.trans (by rwa [heq] at hscaled)

end Erdos676
