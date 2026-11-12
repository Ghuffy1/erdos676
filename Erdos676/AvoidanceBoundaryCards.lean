import Erdos676.AvoidanceMargins
import Erdos676.ResidueBoundaryCounts

namespace Erdos676

noncomputable def avoidanceBoundarySet {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc A B).filter (fun n => ∃ p,
    (n : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R)

theorem lower_avoidance_difference_bound {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    (originalAvoidSet a A B \ lowerAvoidSet a A B R).card ≤
      R + (avoidanceBoundarySet a A B R).card := by
  classical
  have hsub : originalAvoidSet a A B \ lowerAvoidSet a A B R ⊆
      Finset.Icc (B - R + 1) B ∪ avoidanceBoundarySet a A B R := by
    intro n hn
    obtain ⟨hnU, hnL⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hnU
    by_cases hcut : n ≤ B - R
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hnI, ?_⟩
      by_contra hnone
      push_neg at hnone
      apply hnL
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, hcut⟩, ?_⟩
      intro p hp
      apply hnone p
      exact Finset.mem_sdiff.mpr ⟨hp, fun hc => hnA p (contracted_subset_initial _ _ _ hc)⟩
    · apply Finset.mem_union_left
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hnI).2⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hlayer : (Finset.Icc (B - R + 1) B).card = R := by rw [Int.card_Icc]; omega
  rwa [hlayer] at hcard

theorem upper_avoidance_difference_bound {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    (upperAvoidSet a A B R \ originalAvoidSet a A B).card ≤
      R + (avoidanceBoundarySet a A B R).card := by
  classical
  have hsub : upperAvoidSet a A B R \ originalAvoidSet a A B ⊆
      Finset.Icc (A - R) (A - 1) ∪ avoidanceBoundarySet a A B R := by
    intro n hn
    obtain ⟨hnV, hnU⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hnV
    by_cases hcut : A ≤ n
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hcut, (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
      by_contra hnone
      push_neg at hnone
      apply hnU
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hcut, (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
      intro p hp
      exact hnone p (Finset.mem_sdiff.mpr ⟨initial_subset_expanded _ _ _ hp, hnA p⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, by omega⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hlayer : (Finset.Icc (A - R) (A - 1)).card = R := by rw [Int.card_Icc]; omega
  rwa [hlayer] at hcard

theorem avoidance_card_bounds {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    (originalAvoidSet a A B).card ≤ (lowerAvoidSet a A B R).card + R + (avoidanceBoundarySet a A B R).card ∧
    (upperAvoidSet a A B R).card ≤ (originalAvoidSet a A B).card + R + (avoidanceBoundarySet a A B R).card := by
  have hlo := lower_avoidance_difference_bound a A B R
  have hhi := upper_avoidance_difference_bound a A B R
  have hsplitL := Finset.card_sdiff_add_card_eq_card (lowerAvoidSet_subset a A B R)
  have hsplitV := Finset.card_sdiff_add_card_eq_card (originalAvoidSet_subset a A B R)
  omega

end Erdos676
