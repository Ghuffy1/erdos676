import Erdos676.FullDisproof

open Filter

namespace Erdos676

theorem erdos676_negative :
    ¬ (∀ᶠ n : ℕ in atTop, ∃ a p b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b) :=
  full_disproof

theorem erdos676_infinite_exceptions :
    Set.Infinite {n : ℕ | ¬ ∃ a p b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b} :=
  unbounded_iff_infinite.mp full_unbounded_exceptions

end Erdos676
