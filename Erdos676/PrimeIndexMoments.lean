import Erdos676.PrimeLogMoments

open scoped BigOperators

namespace Erdos676

theorem prime_index_log_sum_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {z : ℝ} (hz : 1 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z) :
    (∑ p : P, Real.log (a p) / a p) ≤ Real.log z + (Real.log 4 + 4) := by
  have hsub : Finset.univ.image a ⊆ primesUpToReal z := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(hprime p).pos, Nat.le_floor (hle p)⟩, hprime p⟩
  calc
    _ = ∑ q ∈ Finset.univ.image a, Real.log q / q := by
      symm
      rw [Finset.sum_image]
      intro p hp q hq h
      exact hinj h
    _ ≤ ∑ q ∈ primesUpToReal z, Real.log q / q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => div_nonneg (Real.log_natCast_nonneg q) (Nat.cast_nonneg q))
    _ ≤ _ := prime_log_reciprocal_upper hz

theorem prime_index_log_moments {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {z : ℝ} (hz : 2 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (g : P → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg : ∀ p, g p ≤ 2 / a p) :
    (∑ p : P, g p * Real.log (a p)) ^ 2 +
      (∑ p : P, g p * (Real.log (a p)) ^ 2) ≤ 20 * (Real.log z) ^ 2 := by
  have hL : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hfirst : (∑ p : P, g p * Real.log (a p)) ≤ 4 * Real.log z := by
    calc
      _ ≤ ∑ p : P, (2 / a p) * Real.log (a p) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hg p)
          (Real.log_natCast_nonneg (a p)))
      _ = 2 * (∑ p : P, Real.log (a p) / a p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (Real.log z + (Real.log 4 + 4)) :=
        mul_le_mul_of_nonneg_left (prime_index_log_sum_le a hinj hprime (by linarith) hle) (by norm_num)
      _ ≤ 4 * Real.log z := by linarith
  have hfirst0 : 0 ≤ ∑ p : P, g p * Real.log (a p) :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (hg0 p) (Real.log_natCast_nonneg (a p)))
  have hsecond : (∑ p : P, g p * (Real.log (a p)) ^ 2) ≤ 4 * (Real.log z) ^ 2 := by
    calc
      _ ≤ ∑ p : P, Real.log z * (g p * Real.log (a p)) := by
        apply Finset.sum_le_sum
        intro p _
        have hlog := Real.log_le_log (by exact_mod_cast (hprime p).pos) (hle p)
        have hnonneg := mul_nonneg (hg0 p) (Real.log_natCast_nonneg (a p))
        have h := mul_le_mul_of_nonneg_right hlog hnonneg
        nlinarith
      _ = Real.log z * (∑ p : P, g p * Real.log (a p)) := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.log z * (4 * Real.log z) := mul_le_mul_of_nonneg_left hfirst hL
      _ = 4 * (Real.log z) ^ 2 := by ring
  have hsq : (∑ p : P, g p * Real.log (a p)) ^ 2 ≤ (4 * Real.log z) ^ 2 := by
    nlinarith
  nlinarith

end Erdos676
