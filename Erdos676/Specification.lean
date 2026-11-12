import Erdos676.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos676

/-- The quantitative conclusion of the source proof, at integral dyadic cutoffs. -/
def QuantitativeDisproof : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
    c * X / Real.log X ≤ (dyadicExceptions X).card

theorem quantitativeDisproof_implies_disproof (h : QuantitativeDisproof) :
    ¬ EventualRepresentation := by
  obtain ⟨c, hc, hcount⟩ := h
  apply not_eventual_iff_unbounded.mpr
  apply unbounded_of_eventually_dyadic_nonempty
  filter_upwards [hcount, Filter.eventually_ge_atTop 2] with X hX hX2
  have hXreal : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hpositive : 0 < c * X / Real.log X :=
    div_pos (mul_pos hc (lt_trans zero_lt_one hXreal)) (Real.log_pos hXreal)
  have hcard : 0 < (dyadicExceptions X).card := by
    exact_mod_cast lt_of_lt_of_le hpositive hX
  exact Finset.card_pos.mp hcard

end Erdos676
