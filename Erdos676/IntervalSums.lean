import Erdos676.ResidueBoundaryCounts
import Mathlib.Data.Int.Interval

open scoped BigOperators

namespace Erdos676

theorem card_filter_real {I : Type*} (s : Finset I) (P : I → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ n ∈ s, if P n then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hPa : P a <;> simp [ha, hPa, ih]

theorem int_interval_image (S : ℤ) (N : ℕ) :
    (Finset.range N).image (fun n : ℕ => S + (n : ℤ)) = Finset.Icc S (S + N - 1) := by
  ext m
  constructor
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn' := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hnat : (((m - S).toNat : ℕ) : ℤ) = m - S := Int.toNat_of_nonneg (by omega)
    exact Finset.mem_image.mpr ⟨(m - S).toNat, Finset.mem_range.mpr (by omega), by omega⟩

theorem sum_int_interval {T : Type*} [AddCommMonoid T] (S : ℤ) (N : ℕ) (f : ℤ → T) :
    (∑ n ∈ Finset.Icc S (S + N - 1), f n) = ∑ n ∈ Finset.range N, f (S + n) := by
  rw [← int_interval_image S N]
  apply Finset.sum_image
  intro a ha b hb h
  exact_mod_cast (add_left_cancel h)

theorem int_enlarged_interval_card (S : ℤ) (N R : ℕ) :
    (Finset.Icc (S - R) (S + N - 1)).card = N + R := by
  rw [Int.card_Icc]
  omega

end Erdos676
