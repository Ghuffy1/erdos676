import Erdos676.Gluing
import Mathlib.Data.Nat.Periodic

open scoped BigOperators

namespace Erdos676

theorem periodic_sum_mul (f : ℕ → ℝ) (m k : ℕ) (hf : Function.Periodic f m) :
    (∑ i ∈ Finset.range (k * m), f i) = k * ∑ i ∈ Finset.range m, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : (fun j => f (k * m + j)) = f := by
        funext j
        simpa [Nat.add_comm] using (hf.nat_mul k) j
      simp only [hshift, Nat.cast_add, Nat.cast_one]
      ring

theorem periodic_sum_decomposition (f : ℕ → ℝ) (m N : ℕ)
    (hf : Function.Periodic f m) :
    (∑ i ∈ Finset.range N, f i) =
      (N / m : ℕ) * (∑ i ∈ Finset.range m, f i) + ∑ i ∈ Finset.range (N % m), f i := by
  conv_lhs => rw [← Nat.div_add_mod N m]
  rw [Nat.mul_comm m (N / m), Finset.sum_range_add, periodic_sum_mul f m (N / m) hf]
  have hshift : (fun j => f (N / m * m + j)) = f := by
    funext j
    simpa [Nat.add_comm] using (hf.nat_mul (N / m)) j
  simp only [hshift]

theorem periodic_sum_error (f : ℕ → ℝ) (m N : ℕ) (hm : 0 < m)
    (hf : Function.Periodic f m) (hf0 : ∀ i, 0 ≤ f i) :
    |(∑ i ∈ Finset.range N, f i) -
        (N : ℝ) / m * (∑ i ∈ Finset.range m, f i)| ≤
      ∑ i ∈ Finset.range m, f i := by
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range m, f i := Finset.sum_nonneg (fun i _ => hf0 i)
  have hrem0 : 0 ≤ ∑ i ∈ Finset.range (N % m), f i :=
    Finset.sum_nonneg (fun i _ => hf0 i)
  have hrem : (∑ i ∈ Finset.range (N % m), f i) ≤ ∑ i ∈ Finset.range m, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.mod_lt N hm).le) (fun i _ _ => hf0 i)
  have hmod0 : (0 : ℝ) ≤ N % m := Nat.cast_nonneg _
  have hmod : (N % m : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt N hm).le
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (N : ℝ) = (N / m : ℕ) * m + (N % m : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod N m).symm)
  have hratio : (N : ℝ) / m = (N / m : ℕ) + (N % m : ℝ) / m := by
    apply (div_eq_iff (ne_of_gt hmreal)).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hmreal)]
    exact hN
  have hfract0 : 0 ≤ (N % m : ℝ) / m := div_nonneg hmod0 hmreal.le
  have hfract1 : (N % m : ℝ) / m ≤ 1 := (div_le_one hmreal).mpr hmod
  have hfracsum0 := mul_nonneg hfract0 hsum0
  have hfracsum1 := mul_le_mul_of_nonneg_right hfract1 hsum0
  rw [periodic_sum_decomposition f m N hf, hratio, abs_le]
  constructor <;> nlinarith

theorem periodic_sum_shift_period (f : ℕ → ℝ) (m S : ℕ)
    (hf : Function.Periodic f m) :
    (∑ i ∈ Finset.range m, f (S + i)) = ∑ i ∈ Finset.range m, f i := by
  have hshift : (fun i => f (m + i)) = f := by
    funext i
    simpa [Nat.add_comm] using hf i
  have h := congrArg (fun n => ∑ i ∈ Finset.range n, f i) (Nat.add_comm S m)
  simp only [Finset.sum_range_add, hshift] at h
  linarith

/-- Averaging an arbitrary family of translates of a nonnegative periodic mean-one function. -/
theorem periodic_double_average_upper (f : ℕ → ℝ) (m H : ℕ) (shift : ℕ → ℕ)
    (hm : 0 < m) (hH : 0 < H) (hf : Function.Periodic f m)
    (hf0 : ∀ i, 0 ≤ f i) (hmean : (∑ i ∈ Finset.range m, f i) = m) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H, f (shift j + i)) / (H : ℝ) ^ 2 ≤
      1 + (m : ℝ) / H := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hinner (j : ℕ) : (∑ i ∈ Finset.range H, f (shift j + i)) ≤ (H : ℝ) + m := by
    have hp : Function.Periodic (fun i => f (shift j + i)) m := by
      intro i
      simpa only [Nat.add_assoc] using hf (shift j + i)
    have h := (abs_le.mp (periodic_sum_error (fun i => f (shift j + i)) m H hm hp
      (fun i => hf0 _))).2
    rw [periodic_sum_shift_period f m (shift j) hf, hmean] at h
    rw [div_mul_cancel₀ _ (ne_of_gt hmreal)] at h
    linarith
  have htotal : (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H, f (shift j + i)) ≤
      (H : ℝ) * ((H : ℝ) + m) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.range H) => hinner j)
  apply (div_le_iff₀ (sq_pos_of_pos hHreal)).mpr
  have hid : (1 + (m : ℝ) / H) * (H : ℝ) ^ 2 = (H : ℝ) * ((H : ℝ) + m) := by
    field_simp
  rwa [hid]

end Erdos676
