import Erdos676.BoxSmoothing
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace Erdos676

def boxPathShift {H J : ℕ} (p : Fin J → Fin H) : ℤ := ∑ j : Fin J, (p j : ℤ)

theorem boxPathShift_nonneg {H J : ℕ} (p : Fin J → Fin H) : 0 ≤ boxPathShift p :=
  Finset.sum_nonneg (fun j hj => Int.natCast_nonneg _)

theorem boxPathShift_le {H J : ℕ} (p : Fin J → Fin H) :
    boxPathShift p ≤ (J : ℤ) * H := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin J))) =>
    (show (p j : ℤ) ≤ H by exact_mod_cast (p j).isLt.le))
  simpa only [boxPathShift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem boxPathShift_cons {H J : ℕ} (a : Fin H) (p : Fin J → Fin H) :
    boxPathShift (Fin.cons a p) = (a : ℤ) + boxPathShift p := by
  simp only [boxPathShift, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem box_path_sum_succ (H J : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    (∑ p : Fin (J + 1) → Fin H, f (n + boxPathShift p)) =
      ∑ a : Fin H, ∑ p : Fin J → Fin H, f ((n + a) + boxPathShift p) := by
  have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (J + 1) => Fin H))
    (fun p => f (n + boxPathShift p))
  rw [Fintype.sum_prod_type] at h
  symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p hp
  change f ((n + a) + boxPathShift p) = f (n + boxPathShift (Fin.cons a p))
  rw [boxPathShift_cons, add_assoc]

theorem boxSmooth_path_formula (H J : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    boxSmooth H J f n =
      (∑ p : Fin J → Fin H, f (n + boxPathShift p)) / (H : ℂ) ^ J := by
  induction J generalizing n with
  | zero => simp [boxSmooth, boxPathShift]
  | succ J ih =>
      change (∑ a ∈ Finset.range H, boxSmooth H J f (n + a)) / (H : ℂ) = _
      simp_rw [ih]
      rw [← Finset.sum_div, div_div, pow_succ, box_path_sum_succ, Finset.sum_range]

theorem boxSmooth_const (H J : ℕ) (hH : 0 < H) (c : ℂ) (n : ℤ) :
    boxSmooth H J (fun _ => c) n = c := by
  have hH0 : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hH)
  induction J generalizing n with
  | zero => rfl
  | succ J ih =>
      change (∑ a ∈ Finset.range H, boxSmooth H J (fun _ => c) (n + a)) / (H : ℂ) = c
      simp only [ih, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

end Erdos676
