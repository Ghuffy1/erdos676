import Erdos676.ReciprocalTail

open scoped BigOperators

namespace Erdos676

theorem nat_shifted_square_kernel_sum (s : Finset ℕ) :
    (∑ n ∈ s, ((1 + (n : ℝ)) ^ 2)⁻¹) ≤ 2 := by
  classical
  let N := s.sup id + 2
  have hsub : s.image Nat.succ ⊆ Finset.Ioo 0 N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hle : k ≤ s.sup id := Finset.le_sup (f := id) hk
    exact Finset.mem_Ioo.mpr ⟨by omega, by dsimp [N]; omega⟩
  have hsum : (∑ n ∈ s, ((1 + (n : ℝ)) ^ 2)⁻¹) =
      ∑ n ∈ s.image Nat.succ, ((n : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [Nat.cast_succ, add_comm]
    · intro a ha b hb hab
      exact Nat.succ_injective hab
  rw [hsum]
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => by positivity : ∀ n, n ∈ Finset.Ioo 0 N → n ∉ s.image Nat.succ → 0 ≤ ((n : ℝ) ^ 2)⁻¹)
  have htail := sum_Ioo_inv_sq_le (α := ℝ) 0 N
  norm_num only [Nat.cast_zero, zero_add, div_one] at htail
  exact hbound.trans htail

theorem signed_square_kernel_sum (s : Finset ℤ)
    (hs : (∀ n ∈ s, 0 ≤ n) ∨ (∀ n ∈ s, n ≤ 0)) :
    (∑ n ∈ s, ((1 + |(n : ℝ)|) ^ 2)⁻¹) ≤ 2 := by
  classical
  have hinj : Set.InjOn Int.natAbs (s : Set ℤ) := by
    intro a ha b hb heq
    rcases Int.natAbs_eq_natAbs_iff.mp heq with h | h
    · exact h
    · rcases hs with hs | hs <;> have ha' := hs a ha <;> have hb' := hs b hb <;> omega
  have hsum : (∑ n ∈ s, ((1 + |(n : ℝ)|) ^ 2)⁻¹) =
      ∑ n ∈ s.image Int.natAbs, ((1 + (n : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hsum]
  exact nat_shifted_square_kernel_sum _

theorem integer_square_kernel_sum (s : Finset ℤ) :
    (∑ n ∈ s, ((1 + |(n : ℝ)|) ^ 2)⁻¹) ≤ 4 := by
  classical
  have hpos := signed_square_kernel_sum (s.filter (fun n => 0 ≤ n))
    (Or.inl (fun n hn => (Finset.mem_filter.mp hn).2))
  have hneg := signed_square_kernel_sum (s.filter (fun n => ¬0 ≤ n))
    (Or.inr (fun n hn => (le_of_not_ge (Finset.mem_filter.mp hn).2)))
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun n : ℤ => 0 ≤ n)
    (fun n => ((1 + |(n : ℝ)|) ^ 2)⁻¹)
  linarith

theorem indexed_integer_kernel_sum {P : Type*} (s : Finset P) (g : P → ℤ)
    (hinj : Set.InjOn g (s : Set P)) :
    (∑ i ∈ s, ((1 + |(g i : ℝ)|) ^ 2)⁻¹) ≤ 4 := by
  classical
  have heq : (∑ n ∈ s.image g, ((1 + |(n : ℝ)|) ^ 2)⁻¹) =
      ∑ i ∈ s, ((1 + |(g i : ℝ)|) ^ 2)⁻¹ := Finset.sum_image hinj
  rw [← heq]
  exact integer_square_kernel_sum _

end Erdos676
