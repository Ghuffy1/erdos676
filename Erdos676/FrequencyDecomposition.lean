import Erdos676.FrequencyCount
import Erdos676.SmoothedFourier

open scoped BigOperators

namespace Erdos676

noncomputable def discardedFrequencies (m : ℕ) [NeZero m] (D : ℝ) : Finset (ZMod m) :=
  Finset.univ \ insert 0 (retainedFrequencies m D)

theorem zero_not_mem_retained (m : ℕ) [NeZero m] (D : ℝ) :
    (0 : ZMod m) ∉ retainedFrequencies m D := by
  simp [retainedFrequencies]

theorem discarded_frequency_lower {m : ℕ} [NeZero m] {D : ℝ}
    {k : ZMod m} (hk : k ∈ discardedFrequencies m D) :
    k ≠ 0 ∧ D < |residueFrequency k| := by
  have hnot := (Finset.mem_sdiff.mp hk).2
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    exact hnot (Finset.mem_insert_self 0 _)
  refine ⟨hk0, lt_of_not_ge ?_⟩
  intro hle
  apply hnot
  exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, hle⟩)

theorem frequency_sum_decomposition {m : ℕ} [NeZero m] (D : ℝ) (F : ZMod m → ℂ) :
    (∑ k : ZMod m, F k) = F 0 + (∑ k ∈ retainedFrequencies m D, F k) +
      ∑ k ∈ discardedFrequencies m D, F k := by
  classical
  have h := Finset.sum_sdiff (Finset.subset_univ (insert 0 (retainedFrequencies m D))) (f := F)
  rw [Finset.sum_insert (zero_not_mem_retained m D)] at h
  change (∑ k ∈ discardedFrequencies m D, F k) + (F 0 + ∑ k ∈ retainedFrequencies m D, F k) = _ at h
  rw [← h]
  ring

theorem residueCharacter_zero {m : ℕ} [NeZero m] (n : ℤ) :
    residueCharacter (0 : ZMod m) n = 1 := by simp [residueCharacter, AddChar.map_zero_eq_one]

theorem boxMultiplier_zero {m : ℕ} [NeZero m] (H : ℕ) (hH : 0 < H) :
    boxMultiplier H (residueCharacter (0 : ZMod m)) = 1 := by
  have hH0 : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hH)
  simp [boxMultiplier, residueCharacter_zero, hH0]

theorem smoothed_indicator_decomposition {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (D : ℝ) (H J : ℕ) (hH : 0 < H) (n : ℤ) :
    boxSmooth H J (fun k : ℤ => residueIndicator A (k : ZMod m)) n = residueFourier A 0 +
      boxSmooth H J (residueFourierPart A (retainedFrequencies m D)) n +
      boxSmooth H J (residueFourierPart A (discardedFrequencies m D)) n := by
  have hfun : (fun k : ℤ => residueIndicator A (k : ZMod m)) = residueFourierPart A Finset.univ :=
    funext (residueIndicator_fourier A)
  rw [hfun, smoothed_residueFourierPart, smoothed_residueFourierPart, smoothed_residueFourierPart,
    frequency_sum_decomposition D]
  simp only [boxMultiplier_zero H hH, one_pow, residueCharacter_zero, mul_one]

theorem smoothed_discarded_bound {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (D : ℝ) (hD : 0 < D) (H J : ℕ) (hH : 0 < H) (n : ℤ) :
    ‖boxSmooth H J (residueFourierPart A (discardedFrequencies m D)) n‖ ≤
      A.card * (1 / ((H : ℝ) * D)) ^ J :=
  smoothed_fourier_tail_bound A _ H J hH D hD
    (fun k hk => ⟨(discarded_frequency_lower hk).1, (discarded_frequency_lower hk).2.le⟩) n

end Erdos676
