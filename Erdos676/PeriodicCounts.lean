import Erdos676.Basic
import Mathlib.Data.Nat.Periodic

namespace Erdos676

theorem periodic_count_mul (p : ℕ → Prop) [DecidablePred p] (m k : ℕ)
    (hp : Function.Periodic p m) :
    Nat.count p (k * m) = k * Nat.count p m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.count_add, ih]
      have hshift : (fun j => p (k * m + j)) = p := by
        funext j
        simpa [Nat.add_comm] using (hp.nat_mul k) j
      simp [hshift, Nat.add_mul]

theorem periodic_count_decomposition (p : ℕ → Prop) [DecidablePred p] (m N : ℕ)
    (hp : Function.Periodic p m) :
    Nat.count p N = (N / m) * Nat.count p m + Nat.count p (N % m) := by
  conv_lhs => rw [← Nat.div_add_mod N m]
  rw [Nat.count_add, Nat.mul_comm m (N / m), periodic_count_mul p m (N / m) hp]
  have hshift : (fun j => p (N / m * m + j)) = p := by
    funext j
    simpa [Nat.add_comm] using (hp.nat_mul (N / m)) j
  simp [hshift]

theorem periodic_count_bounds (p : ℕ → Prop) [DecidablePred p] (m N : ℕ)
    (hm : 0 < m) (hp : Function.Periodic p m) :
    (N / m) * Nat.count p m ≤ Nat.count p N ∧
      Nat.count p N ≤ (N / m + 1) * Nat.count p m := by
  have hr : Nat.count p (N % m) ≤ Nat.count p m :=
    Nat.count_monotone p (Nat.mod_lt N hm).le
  rw [periodic_count_decomposition p m N hp]
  constructor <;> nlinarith

/-- The prefix discrepancy is bounded by one period's accepted count, after clearing m. -/
theorem periodic_count_scaled_error (p : ℕ → Prop) [DecidablePred p] (m N : ℕ)
    (hm : 0 < m) (hp : Function.Periodic p m) :
    |(m : ℤ) * Nat.count p N - (N : ℤ) * Nat.count p m| ≤
      (m : ℤ) * Nat.count p m := by
  have hrem : (N % m : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.mod_lt N hm).le
  have hcount : (Nat.count p (N % m) : ℤ) ≤ Nat.count p m := by
    exact_mod_cast Nat.count_monotone p (Nat.mod_lt N hm).le
  have hm0 : (0 : ℤ) ≤ m := by omega
  have hrho : (0 : ℤ) ≤ Nat.count p m := by omega
  have hc0 : (0 : ℤ) ≤ Nat.count p (N % m) := by omega
  have hr0 : (0 : ℤ) ≤ N % m := by omega
  have hprod1 := mul_le_mul_of_nonneg_left hcount hm0
  have hprod2 := mul_le_mul_of_nonneg_right hrem hrho
  have hprod3 := mul_nonneg hm0 hc0
  have hprod4 := mul_nonneg hr0 hrho
  have hN : (N : ℤ) = (N / m : ℤ) * m + (N % m : ℤ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod N m).symm)
  have hNmul := congrArg (fun t : ℤ => t * (Nat.count p m : ℤ)) hN
  rw [periodic_count_decomposition p m N hp]
  push_cast
  apply abs_le.mpr
  constructor <;> nlinarith

theorem periodic_count_shift_period (p : ℕ → Prop) [DecidablePred p] (m S : ℕ)
    (hp : Function.Periodic p m) :
    Nat.count (fun j => p (S + j)) m = Nat.count p m := by
  have hshift : (fun j => p (m + j)) = p := by
    funext j
    simpa [Nat.add_comm] using hp j
  have h := congrArg (Nat.count p) (Nat.add_comm S m)
  simp only [Nat.count_add, hshift] at h
  omega

theorem periodic_interval_count_scaled_error (p : ℕ → Prop) [DecidablePred p]
    (m S N : ℕ) (hm : 0 < m) (hp : Function.Periodic p m) :
    |(m : ℤ) * Nat.count (fun j => p (S + j)) N - (N : ℤ) * Nat.count p m| ≤
      (m : ℤ) * Nat.count p m := by
  have hsp : Function.Periodic (fun j => p (S + j)) m := by
    intro j
    simpa [Nat.add_assoc] using hp (S + j)
  simpa only [periodic_count_shift_period p m S hp] using
    periodic_count_scaled_error (fun j => p (S + j)) m N hm hsp

end Erdos676
