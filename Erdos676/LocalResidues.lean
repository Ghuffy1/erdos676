import Erdos676.LocalFactors
import Erdos676.PrimeResidues
import Erdos676.NormalizedFactors
import Mathlib.Data.Finset.Preimage

open scoped BigOperators

namespace Erdos676

section AddGroup

variable {G : Type*} [AddGroup G] [DecidableEq G]

noncomputable def translatedBack (A : Finset G) (k : G) : Finset G :=
  A.preimage (fun x => x + k) (fun _ _ _ _ h => add_right_cancel h)

omit [DecidableEq G] in
theorem mem_translatedBack (A : Finset G) (k x : G) :
    x ∈ translatedBack A k ↔ x + k ∈ A := Finset.mem_preimage

omit [DecidableEq G] in
set_option backward.isDefEq.respectTransparency false in
theorem translatedBack_card (A : Finset G) (k : G) :
    (translatedBack A k).card = A.card := by
  classical
  unfold translatedBack
  rw [Finset.card_preimage]
  congr 1
  apply Finset.filter_true_of_mem
  intro x _
  exact (Equiv.addRight k).surjective x

theorem overlap_eq_card_inter (A : Finset G) (k : G) :
    overlap A k = (A ∩ translatedBack A k).card := by
  have hset : A ∩ translatedBack A k = A.filter (fun x => x + k ∈ A) := by
    ext x
    simp [mem_translatedBack]
  rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem two_position_card (A : Finset G) (k : G) :
    (A ∪ translatedBack A k).card + overlap A k = 2 * A.card := by
  rw [overlap_eq_card_inter, Finset.card_union_add_card_inter, translatedBack_card]
  omega

end AddGroup

noncomputable def twoPositionResidues (p : ℕ) (k : ZMod (p ^ 2)) :
    Finset (ZMod (p ^ 2)) := smallResidues p ∪ translatedBack (smallResidues p) k

theorem mem_twoPositionResidues (p : ℕ) (hp : 1 ≤ p) (k n : ℕ) :
    (n : ZMod (p ^ 2)) ∈ twoPositionResidues p (k : ZMod (p ^ 2)) ↔
      n % p ^ 2 < p ∨ (n + k) % p ^ 2 < p := by
  simp only [twoPositionResidues, Finset.mem_union, mem_translatedBack,
    mem_smallResidues p n hp, ← Nat.cast_add, mem_smallResidues p (n + k) hp]

theorem twoPositionResidues_card (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    (twoPositionResidues p k).card + overlap (smallResidues p) k = 2 * p := by
  rw [twoPositionResidues, two_position_card, smallResidues_card p hp]

noncomputable def twoPositionDensity (p : ℕ) (k : ZMod (p ^ 2)) : ℝ :=
  (twoPositionResidues p k).card / (p : ℝ) ^ 2

theorem twoPositionDensity_formula (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    twoPositionDensity p k = 2 / p - (overlap (smallResidues p) k : ℝ) / (p : ℝ) ^ 2 := by
  have hcard := twoPositionResidues_card p hp k
  have hc : ((twoPositionResidues p k).card : ℝ) + overlap (smallResidues p) k = 2 * p := by
    exact_mod_cast hcard
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  unfold twoPositionDensity
  field_simp
  nlinarith

theorem twoPositionDensity_bounds (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    0 ≤ twoPositionDensity p k ∧ twoPositionDensity p k ≤ 2 / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  constructor
  · unfold twoPositionDensity
    positivity
  · rw [twoPositionDensity_formula p hp k]
    have h : (0 : ℝ) ≤ overlap (smallResidues p) k := Nat.cast_nonneg _
    have := div_nonneg h (sq_nonneg (p : ℝ))
    linarith

theorem twoPositionDensity_le_one (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    twoPositionDensity p k ≤ 1 := by
  let : NeZero p := ⟨by omega⟩
  have hc : (twoPositionResidues p k).card ≤ p ^ 2 := by
    simpa only [Finset.card_univ, ZMod.card] using
      Finset.card_le_card (Finset.subset_univ (twoPositionResidues p k))
  have hcr : ((twoPositionResidues p k).card : ℝ) ≤ (p : ℝ) ^ 2 := by
    exact_mod_cast hc
  exact (div_le_one (sq_pos_of_pos (by exact_mod_cast (by omega : 0 < p)))).mpr hcr

theorem normalized_overlap_sum (p : ℕ) [NeZero p] (hp : 1 ≤ p) :
    (∑ k : ZMod (p ^ 2), normalizedFactor p (overlap (smallResidues p) k)) =
      (p : ℝ) ^ 2 := by
  have ho : (∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ)) = (p : ℝ) ^ 2 := by
    exact_mod_cast (by simpa only [smallResidues_card p hp] using sum_overlap (smallResidues p))
  have hmean : (∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ)) =
      (Finset.univ : Finset (ZMod (p ^ 2))).card := by
    simpa only [Finset.card_univ, ZMod.card, Nat.cast_pow] using ho
  simpa only [Finset.card_univ, ZMod.card, Nat.cast_pow] using
    sum_normalizedFactor (Finset.univ : Finset (ZMod (p ^ 2))) p
      (fun k => (overlap (smallResidues p) k : ℝ)) hmean

end Erdos676
