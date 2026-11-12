import Erdos676.Avoidance
import Erdos676.Gluing

open scoped BigOperators

namespace Erdos676

/-- The concrete finite data that the analytic part must construct at each large X. -/
structure SieveData (X : ℕ) where
  cutoff : ℕ
  window : ℕ
  centers : Finset ℕ
  window_pos : 0 < window
  centers_subset : centers ⊆ Finset.Ioc X (2 * X)
  first_pos : 0 < ∑ n ∈ Finset.Ioc X (2 * X), smallAverage cutoff window n
  moment_gap :
    (((Finset.Ioc X (2 * X)) \ centers).card : ℝ) *
        (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage cutoff window n) ^ 2) <
      (∑ n ∈ Finset.Ioc X (2 * X), smallAverage cutoff window n) ^ 2
  large_avoidance :
    ∀ n ∈ centers, ∀ j < window, LargeAvoidance cutoff (n + j)
  shifts_stay_in_interval :
    ∀ n ∈ centers, ∀ j < window, X < n + j ∧ n + j ≤ 2 * X

/-- The finite part of the argument produces an actual exception from the sieve data. -/
theorem SieveData.exception_exists {X : ℕ} (D : SieveData X) :
    (dyadicExceptions X).Nonempty := by
  have hpositive : 0 < ∑ n ∈ D.centers, smallAverage D.cutoff D.window n :=
    positive_restricted_mass_of_moment_gap (Finset.Ioc X (2 * X)) D.centers
      (smallAverage D.cutoff D.window) D.centers_subset
      (fun n _ => smallAverage_nonneg _ _ n) D.first_pos D.moment_gap
  have hcard := smallAverage_mass_le_exceptions D.centers (dyadicExceptions X)
    D.cutoff D.window D.window_pos D.large_avoidance (by
      intro n hn j hj he
      exact (mem_dyadicExceptions X (n + j)).mpr
        ⟨(D.shifts_stay_in_interval n hn j hj).1,
          (D.shifts_stay_in_interval n hn j hj).2, he⟩)
  have : 0 < (dyadicExceptions X).card := by
    exact_mod_cast (lt_of_lt_of_le hpositive hcard)
  exact Finset.card_pos.mp this

/-- Discharging the eventual analytic construction proves the exact original disproof. -/
theorem disproof_of_eventual_sieve_data
    (h : ∀ᶠ X : ℕ in Filter.atTop, Nonempty (SieveData X)) :
    ¬ EventualRepresentation := by
  apply not_eventual_iff_unbounded.mpr
  apply unbounded_of_eventually_dyadic_nonempty
  filter_upwards [h] with X hX
  obtain ⟨D⟩ := hX
  exact D.exception_exists

end Erdos676
