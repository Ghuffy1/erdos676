import Erdos676.ResidueMargins
import Erdos676.SmoothingSandwich

open scoped BigOperators

namespace Erdos676

noncomputable def originalAvoidSet {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc A B).filter (fun n => ∀ p, (n : ZMod ((a p) ^ 2)) ∉ initialResidues ((a p) ^ 2) (a p))

noncomputable def lowerAvoidSet {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc A (B - R)).filter
    (fun n => ∀ p, (n : ZMod ((a p) ^ 2)) ∉ expandedResidues ((a p) ^ 2) (a p) R)

noncomputable def upperAvoidSet {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (A - R) B).filter
    (fun n => ∀ p, (n : ZMod ((a p) ^ 2)) ∉ contractedResidues ((a p) ^ 2) (a p) R)

theorem lowerAvoidSet_subset {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    lowerAvoidSet a A B R ⊆ originalAvoidSet a A B := by
  classical
  intro n hn
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, by have := (Finset.mem_Icc.mp hnI).2; omega⟩, ?_⟩
  intro p hp
  exact hnA p (initial_subset_expanded _ _ _ hp)

theorem originalAvoidSet_subset {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    originalAvoidSet a A B ⊆ upperAvoidSet a A B R := by
  classical
  intro n hn
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnI).1; omega, (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
  intro p hp
  exact hnA p (contracted_subset_initial _ _ _ hp)

theorem lowerAvoidSet_shift {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ)
    (t : ℤ) (ht0 : 0 ≤ t) (htR : t ≤ R) (n : ℤ) (hn : n ∈ lowerAvoidSet a A B R) :
    n + t ∈ originalAvoidSet a A B := by
  classical
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  have htNat : t.toNat ≤ R := by exact_mod_cast (show (t.toNat : ℤ) ≤ R by rwa [htcast])
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnI).1; omega,
    by have := (Finset.mem_Icc.mp hnI).2; omega⟩, ?_⟩
  intro p hp
  have htmod : (t.toNat : ZMod ((a p) ^ 2)) = (t : ZMod ((a p) ^ 2)) := by
    rw [← Int.cast_natCast, htcast]
  have hp' : (n : ZMod ((a p) ^ 2)) + t.toNat ∈ initialResidues ((a p) ^ 2) (a p) := by
    simpa only [Int.cast_add, htmod] using hp
  exact hnA p (initial_shift_expanded _ _ _ _ htNat _ hp')

theorem upperAvoidSet_shift {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ)
    (t : ℤ) (ht0 : 0 ≤ t) (htR : t ≤ R) (n : ℤ) (hn : n ∈ originalAvoidSet a A B) :
    n - t ∈ upperAvoidSet a A B R := by
  classical
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  have htNat : t.toNat ≤ R := by exact_mod_cast (show (t.toNat : ℤ) ≤ R by rwa [htcast])
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnI).1; omega,
    by have := (Finset.mem_Icc.mp hnI).2; omega⟩, ?_⟩
  intro p hp
  have htmod : (t.toNat : ZMod ((a p) ^ 2)) = (t : ZMod ((a p) ^ 2)) := by
    rw [← Int.cast_natCast, htcast]
  have hbad := contracted_shift_initial _ _ _ _ htNat (Int.cast (n - t) : ZMod ((a p) ^ 2)) hp
  apply hnA p
  simpa only [htmod, ← Int.cast_add, sub_add_cancel] using hbad

theorem avoidance_smoothing_sandwich {P : Type*} [Fintype P] (a : P → ℕ)
    (A B : ℤ) (H J : ℕ) (hH : 0 < H) (G : ℤ → ℝ) (hG : ∀ n, 0 ≤ G n) :
    (∑ n ∈ lowerAvoidSet a A B (J * H), realBoxSmooth H J G n) ≤
      (∑ n ∈ originalAvoidSet a A B, G n) ∧
    (∑ n ∈ originalAvoidSet a A B, G n) ≤
      ∑ n ∈ upperAvoidSet a A B (J * H), realBoxSmooth H J G n := by
  apply smoothing_sandwich _ _ _ G H J hH hG
  · intro t ht0 htR n hn
    exact lowerAvoidSet_shift a A B (J * H) t ht0 (by exact_mod_cast htR) n hn
  · intro t ht0 htR n hn
    exact upperAvoidSet_shift a A B (J * H) t ht0 (by exact_mod_cast htR) n hn

end Erdos676
