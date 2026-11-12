import Erdos676.SmoothingCorrelation
import Erdos676.BoundaryCountBound

open scoped BigOperators

namespace Erdos676

theorem avoidance_correlation_bound {P : Type*} [Fintype P] (a : P → ℕ)
    (A B : ℤ) (H J : ℕ) (hH : 0 < H) (G : ℤ → ℝ) (hG : ∀ n, 0 ≤ G n)
    (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (henergy : ∑ n ∈ Finset.Icc (A - (J * H : ℕ)) B,
      (realBoxSmooth H J G n - μ) ^ 2 ≤ E) :
    |(∑ n ∈ originalAvoidSet a A B, G n) - μ * (originalAvoidSet a A B).card| ≤
      Real.sqrt ((Finset.Icc (A - (J * H : ℕ)) B).card * E) +
        μ * ((J * H : ℕ) + (avoidanceBoundarySet a A B (J * H)).card) := by
  let R := J * H
  let W := Finset.Icc (A - (R : ℤ)) B
  have hVW : upperAvoidSet a A B R ⊆ W := Finset.filter_subset _ _
  have hLW : lowerAvoidSet a A B R ⊆ W :=
    (lowerAvoidSet_subset a A B R).trans ((originalAvoidSet_subset a A B R).trans hVW)
  have henergyL : ∑ n ∈ lowerAvoidSet a A B R, (realBoxSmooth H J G n - μ) ^ 2 ≤ E :=
    (Finset.sum_le_sum_of_subset_of_nonneg hLW (fun n hn hnot => sq_nonneg _)).trans henergy
  have henergyV : ∑ n ∈ upperAvoidSet a A B R, (realBoxSmooth H J G n - μ) ^ 2 ≤ E :=
    (Finset.sum_le_sum_of_subset_of_nonneg hVW (fun n hn hnot => sq_nonneg _)).trans henergy
  have hLM : ((lowerAvoidSet a A B R).card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hLW
  have hVM : ((upperAvoidSet a A B R).card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hVW
  have hcards := avoidance_card_bounds a A B R
  have hLU : ((originalAvoidSet a A B).card : ℝ) ≤ (lowerAvoidSet a A B R).card +
      ((R : ℝ) + (avoidanceBoundarySet a A B R).card) := by
    exact_mod_cast (by simpa only [Nat.add_assoc] using hcards.1)
  have hUV : ((upperAvoidSet a A B R).card : ℝ) ≤ (originalAvoidSet a A B).card +
      ((R : ℝ) + (avoidanceBoundarySet a A B R).card) := by
    exact_mod_cast (by simpa only [Nat.add_assoc] using hcards.2)
  have hsand := avoidance_smoothing_sandwich a A B H J hH G hG
  exact correlation_from_smoothing_bounds _ _ _ G (realBoxSmooth H J G) μ E W.card
    ((R : ℝ) + (avoidanceBoundarySet a A B R).card) hμ hE hsand.1 hsand.2 henergyL henergyV hLM hVM hLU hUV

theorem avoidance_correlation_explicit {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (m : ℕ) (hm : 0 < m) (hlo : ∀ p, m < a p) (z : ℝ) (hz : 0 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z)
    (S : ℤ) (N H J : ℕ) (hH : 0 < H) (G : ℤ → ℝ) (hG : ∀ n, 0 ≤ G n)
    (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (henergy : ∑ n ∈ Finset.Icc (S - (J * H : ℕ)) (S + N - 1),
      (realBoxSmooth H J G n - μ) ^ 2 ≤ E) :
    |(∑ n ∈ originalAvoidSet a S (S + N - 1), G n) - μ * (originalAvoidSet a S (S + N - 1)).card| ≤
      Real.sqrt (((N : ℝ) + J * H) * E) + μ * ((J * H : ℕ) + 2 * (J * H : ℕ) * ((N : ℝ) / m + z)) := by
  have h := avoidance_correlation_bound a S (S + N - 1) H J hH G hG μ E hμ hE henergy
  have hb := avoidance_boundary_card_bound a hprime hinj m hm hlo z hz hle S N (J * H)
  rw [int_enlarged_interval_card, Nat.cast_add, Nat.cast_mul] at h
  have hscaled := mul_le_mul_of_nonneg_left hb hμ
  simp only [Nat.cast_mul] at hscaled ⊢
  nlinarith

end Erdos676
