import Erdos676.ResidueFrequency
import Mathlib.Data.Nat.Prime.Int

namespace Erdos676

theorem prime_frequency_cross_ne (p q : ℕ) (a b : ℤ)
    (hp : p.Prime) (hq : q.Prime) (ha : a ≠ 0) (habound : a.natAbs < p)
    (hpair : ¬(p = q ∧ a = b)) : a * (q : ℤ) ^ 2 ≠ b * (p : ℤ) ^ 2 := by
  intro heq
  by_cases hpq : p = q
  · subst q
    have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne_zero)
    exact hpair ⟨rfl, mul_right_cancel₀ hp0 heq⟩
  · have hdiv : (p : ℤ) ∣ a * (q : ℤ) ^ 2 := by
      rw [heq]
      refine ⟨b * p, ?_⟩
      ring
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdiv with hpa | hpqdiv
    · have ha0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hpa
        (by simpa only [Int.natAbs_natCast] using habound)
      exact ha ha0
    · have hpqdiv' : (p : ℤ) ∣ (q : ℤ) := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpqdiv
      have hpqN : p ∣ q := Int.natCast_dvd_natCast.mp hpqdiv'
      rcases (Nat.dvd_prime hq).mp hpqN with hp1 | hpq'
      · exact hp.ne_one hp1
      · exact hpq hpq'

theorem integer_fraction_separation (p q : ℕ) (a b : ℤ)
    (hp : 0 < p) (hq : 0 < q)
    (hcross : a * (q : ℤ) ^ 2 ≠ b * (p : ℤ) ^ 2) :
    1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) ≤
      |(a : ℝ) / (p : ℝ) ^ 2 - (b : ℝ) / (q : ℝ) ^ 2| := by
  let d : ℤ := a * (q : ℤ) ^ 2 - b * (p : ℤ) ^ 2
  have hd : d ≠ 0 := sub_ne_zero.mpr hcross
  have hnat : 1 ≤ d.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd)
  have habsInt : (1 : ℤ) ≤ |d| := by
    simpa only [Int.natCast_natAbs] using (show (1 : ℤ) ≤ d.natAbs by exact_mod_cast hnat)
  have habs : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast habsInt
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hden : 0 < (p : ℝ) ^ 2 * (q : ℝ) ^ 2 := mul_pos (sq_pos_of_ne_zero hp0) (sq_pos_of_ne_zero hq0)
  have hid : (a : ℝ) / (p : ℝ) ^ 2 - (b : ℝ) / (q : ℝ) ^ 2 =
      (d : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
    dsimp [d]
    push_cast
    field_simp
    <;> ring
  rw [hid, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right habs hden.le

theorem prime_frequency_separation (p q : ℕ) (a b : ℤ)
    (hp : p.Prime) (hq : q.Prime) (ha : a ≠ 0) (habound : a.natAbs < p)
    (hpair : ¬(p = q ∧ a = b)) :
    1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) ≤
      |(a : ℝ) / (p : ℝ) ^ 2 - (b : ℝ) / (q : ℝ) ^ 2| :=
  integer_fraction_separation p q a b hp.pos hq.pos
    (prime_frequency_cross_ne p q a b hp hq ha habound hpair)

theorem prime_frequency_abs_le_quarter (p : ℕ) (a : ℤ) (hp : 2 ≤ p) (ha : a.natAbs < p) :
    |(a : ℝ) / (p : ℝ) ^ 2| ≤ 1 / 4 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hboundInt : |a| ≤ (p : ℤ) - 1 := by
    have h := (show (a.natAbs : ℤ) < p by exact_mod_cast ha)
    rw [Int.natCast_natAbs] at h
    omega
  have hbound : |(a : ℝ)| ≤ (p : ℝ) - 1 := by exact_mod_cast hboundInt
  have hpos : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
  rw [abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

end Erdos676
