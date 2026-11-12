import Erdos676.RealBoxSmoothing

open scoped BigOperators

namespace Erdos676

theorem shifted_sum_lower (L U : Finset ℤ) (G : ℤ → ℝ) (t : ℤ)
    (hG : ∀ n, 0 ≤ G n) (hLU : ∀ n ∈ L, n + t ∈ U) :
    (∑ n ∈ L, G (n + t)) ≤ ∑ n ∈ U, G n := by
  classical
  have hsub : L.image (fun n => n + t) ⊆ U := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact hLU n hn
  have heq : (∑ m ∈ L.image (fun n => n + t), G m) = ∑ n ∈ L, G (n + t) :=
    Finset.sum_image (fun a ha b hb h => add_right_cancel h)
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => hG n)

theorem shifted_sum_upper (U V : Finset ℤ) (G : ℤ → ℝ) (t : ℤ)
    (hG : ∀ n, 0 ≤ G n) (hUV : ∀ n ∈ U, n - t ∈ V) :
    (∑ n ∈ U, G n) ≤ ∑ n ∈ V, G (n + t) := by
  have h := shifted_sum_lower U V (fun n => G (n + t)) (-t)
    (fun n => hG _) (by simpa only [sub_eq_add_neg] using hUV)
  simpa only [add_assoc, neg_add_cancel, add_zero] using h

theorem smoothing_sandwich (L U V : Finset ℤ) (G : ℤ → ℝ) (H J : ℕ) (hH : 0 < H)
    (hG : ∀ n, 0 ≤ G n)
    (hLU : ∀ t : ℤ, 0 ≤ t → t ≤ (J : ℤ) * H → ∀ n ∈ L, n + t ∈ U)
    (hUV : ∀ t : ℤ, 0 ≤ t → t ≤ (J : ℤ) * H → ∀ n ∈ U, n - t ∈ V) :
    (∑ n ∈ L, realBoxSmooth H J G n) ≤ (∑ n ∈ U, G n) ∧
      (∑ n ∈ U, G n) ≤ ∑ n ∈ V, realBoxSmooth H J G n := by
  have hlower (p : Fin J → Fin H) := shifted_sum_lower L U G (boxPathShift p) hG
    (hLU _ (boxPathShift_nonneg p) (boxPathShift_le p))
  have hupper (p : Fin J → Fin H) := shifted_sum_upper U V G (boxPathShift p) hG
    (hUV _ (boxPathShift_nonneg p) (boxPathShift_le p))
  have hconst : (∑ _p : Fin J → Fin H, ∑ n ∈ U, G n) / (H : ℝ) ^ J = ∑ n ∈ U, G n :=
    realBoxSmooth_const H J hH _ 0
  have hlo := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.univ) (fun (p : Fin J → Fin H) hp => hlower p))
    (pow_nonneg (Nat.cast_nonneg H) J)
  have hhi := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.univ) (fun (p : Fin J → Fin H) hp => hupper p))
    (pow_nonneg (Nat.cast_nonneg H) J)
  rw [hconst] at hlo hhi
  have heq (W : Finset ℤ) : (∑ n ∈ W, realBoxSmooth H J G n) =
      (∑ p : Fin J → Fin H, ∑ n ∈ W, G (n + boxPathShift p)) / (H : ℝ) ^ J := by
    unfold realBoxSmooth
    rw [← Finset.sum_div, Finset.sum_comm]
  constructor
  · rw [heq]
    exact hlo
  · rw [heq]
    exact hhi

end Erdos676
