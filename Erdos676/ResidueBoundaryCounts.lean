import Erdos676.ResidueMargins
import Erdos676.ResidueAverages

open scoped BigOperators

namespace Erdos676

theorem modular_interval_upper (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (S : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, if (S + (n : ℤ) : ZMod m) ∈ A then (1 : ℝ) else 0) ≤
      ((N : ℝ) / m + 1) * A.card := by
  classical
  let F (r : ZMod m) : ℝ := if (S : ZMod m) + r ∈ A then 1 else 0
  have hperm := Equiv.sum_comp (Equiv.addLeft (S : ZMod m))
    (fun r : ZMod m => if r ∈ A then (1 : ℝ) else 0)
  change (∑ r : ZMod m, F r) = (∑ r : ZMod m, if r ∈ A then (1 : ℝ) else 0) at hperm
  have hsum : (∑ n ∈ Finset.range m, F (n : ZMod m)) = (A.card : ℝ) := by
    rw [sum_range_zmod m F, hperm]
    simp
  have hperiod : Function.Periodic (fun n : ℕ => F (n : ZMod m)) m := by
    intro n
    simp
  have hnonneg : ∀ n : ℕ, 0 ≤ F (n : ZMod m) := by intro n; dsimp [F]; split_ifs <;> norm_num
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hmean : (∑ n ∈ Finset.range m, F (n : ZMod m)) ≤ (m : ℝ) * (A.card / (m : ℝ)) := by
    rw [hsum]
    field_simp
    rfl
  have h := periodic_sum_upper_mean (fun n : ℕ => F (n : ZMod m)) m N (A.card / (m : ℝ))
    (Nat.pos_of_ne_zero (NeZero.ne m)) hperiod hnonneg hmean
  have hid : ((N : ℝ) + m) * (A.card / (m : ℝ)) = ((N : ℝ) / m + 1) * A.card := by
    field_simp
    <;> ring
  rw [hid] at h
  simpa only [F, Int.cast_add, Int.cast_natCast] using h

theorem prime_boundary_interval_upper (p R N : ℕ) (hp : p.Prime) (S : ℤ) :
    (∑ n ∈ Finset.range N, if (S + (n : ℤ) : ZMod (p ^ 2)) ∈ boundaryResidues (p ^ 2) p R
      then (1 : ℝ) else 0) ≤ 2 * R * ((N : ℝ) / (p : ℝ) ^ 2 + 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := modular_interval_upper (p ^ 2) (boundaryResidues (p ^ 2) p R) S N
  have hcard : ((boundaryResidues (p ^ 2) p R).card : ℝ) ≤ 2 * R := by
    exact_mod_cast boundaryResidues_card_le (p ^ 2) p R (by nlinarith [hp.two_le])
  have hmul := mul_le_mul_of_nonneg_left hcard
    (show 0 ≤ (N : ℝ) / (p : ℝ) ^ 2 + 1 by positivity)
  rw [Nat.cast_pow] at h
  nlinarith

theorem finite_union_indicator_le {P : Type*} [Fintype P] (B : P → Prop) [DecidablePred B] :
    (if ∃ p, B p then (1 : ℝ) else 0) ≤ ∑ p : P, if B p then 1 else 0 := by
  classical
  by_cases h : ∃ p, B p
  · obtain ⟨p, hp⟩ := h
    have hex : ∃ p, B p := ⟨p, hp⟩
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun p => if B p then (1 : ℝ) else 0)
      (fun p hp => by split_ifs <;> norm_num) (Finset.mem_univ p)
    simpa only [hp, ite_true, hex] using hsingle
  · simp only [h, ite_false]
    exact Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)

theorem family_boundary_interval_upper {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (R N : ℕ) (S : ℤ) :
    (∑ n ∈ Finset.range N, if ∃ p : P,
      (S + (n : ℤ) : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R
      then (1 : ℝ) else 0) ≤
      2 * R * ((N : ℝ) * (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) + Fintype.card P) := by
  classical
  have hpoint := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) =>
    finite_union_indicator_le (fun p : P =>
      (S + (n : ℤ) : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R))
  rw [Finset.sum_comm] at hpoint
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
    prime_boundary_interval_upper (a p) R N (hprime p) S)
  have hid : (∑ p : P, 2 * R * ((N : ℝ) / (a p : ℝ) ^ 2 + 1)) =
      2 * R * ((N : ℝ) * (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) + Fintype.card P) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, div_eq_mul_inv,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hid] at hsum
  exact hpoint.trans hsum

end Erdos676
