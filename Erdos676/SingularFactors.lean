import Erdos676.SmallCorrelations

open scoped BigOperators

namespace Erdos676

noncomputable def localSingularFactor (p : ℕ) (k : ZMod (p ^ 2)) : ℝ :=
  normalizedFactor p (overlap (smallResidues p) k)

noncomputable def localSingularExcess (p : ℕ) (k : ZMod (p ^ 2)) : ℝ :=
  max (localSingularFactor p k - 1) 0

noncomputable def singularFactorProduct (z : ℝ) (k : ℤ) : ℝ :=
  ∏ p ∈ primesUpToReal z, localSingularFactor p (k : ZMod (p ^ 2))

theorem localSingularFactor_nonneg (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    0 ≤ localSingularFactor p k :=
  normalizedFactor_nonneg (by exact_mod_cast hp) (Nat.cast_nonneg _)

theorem localSingularFactor_le (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    localSingularFactor p k ≤ (p : ℝ) / (p - 1) := by
  apply normalizedFactor_le (by exact_mod_cast hp)
  have h := overlap_le_card (smallResidues p) k
  rw [smallResidues_card p (by omega)] at h
  exact_mod_cast h

theorem localSingularExcess_le_overlap (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    localSingularExcess p k ≤ (overlap (smallResidues p) k : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  unfold localSingularExcess localSingularFactor normalizedFactor
  apply max_le
  · have h := div_le_div_of_nonneg_right
      (by linarith : (overlap (smallResidues p) k : ℝ) - 1 ≤ overlap (smallResidues p) k) hden.le
    linarith
  · exact div_nonneg (Nat.cast_nonneg _) hden.le

theorem one_add_localSingularExcess_le (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    1 + localSingularExcess p k ≤ (p : ℝ) / (p - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hone : (1 : ℝ) ≤ (p : ℝ) / (p - 1) := (le_div_iff₀ hp1).mpr (by linarith)
  have hfactor := localSingularFactor_le p hp k
  unfold localSingularExcess
  rw [add_max]
  apply max_le <;> linarith

theorem localSingularFactor_identity (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    1 - twoPositionDensity p k = (1 - (1 : ℝ) / p) ^ 2 * localSingularFactor p k := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [twoPositionDensity_formula p (by omega)]
  unfold localSingularFactor normalizedFactor
  field_simp
  ring

theorem pairSurvivalProduct_factorization (z : ℝ) (k : ℤ) :
    pairSurvivalProduct z k = (survivalProduct z) ^ 2 * singularFactorProduct z k := by
  unfold pairSurvivalProduct survivalProduct singularFactorProduct
  calc
    _ = ∏ p ∈ primesUpToReal z, (1 - (1 : ℝ) / p) ^ 2 * localSingularFactor p (k : ZMod (p ^ 2)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact localSingularFactor_identity p (Finset.mem_filter.mp hp).2.two_le _
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow]

theorem localSingularExcess_sum_le (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    (∑ k : ZMod (p ^ 2), localSingularExcess p k) ≤ (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 := by
  calc
    _ ≤ ∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ) / ((p : ℝ) - 1) ^ 2 :=
      Finset.sum_le_sum (fun k _ => localSingularExcess_le_overlap p hp k)
    _ = _ := by
      rw [← Finset.sum_div]
      have hsum : (∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ)) = (p : ℝ) ^ 2 := by
        exact_mod_cast (by simpa only [smallResidues_card p (by omega)] using sum_overlap (smallResidues p))
      rw [hsum]

end Erdos676
