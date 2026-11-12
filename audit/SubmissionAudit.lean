import Erdos676

open Filter

namespace JSP000549

/-- The catalog question, independently restated using the original arithmetic conditions. -/
def OriginalQuestion : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ a p b : ℕ,
    p.Prime ∧ 1 ≤ a ∧ 0 ≤ b ∧ b < p ∧ n = a * p ^ 2 + b

/-- The additional `0 ≤ b` is automatic because the remainder is a natural number. -/
theorem question_equivalent : OriginalQuestion ↔ Erdos676.EventualRepresentation := by
  simp only [OriginalQuestion, Erdos676.EventualRepresentation, Erdos676.Representable,
    Nat.zero_le, true_and]

theorem original_question_negative : ¬ OriginalQuestion := by
  intro h
  exact Erdos676.full_disproof (question_equivalent.mp h)

theorem arbitrarily_large_exceptions :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ ∃ a p b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b :=
  Erdos676.full_unbounded_exceptions

end JSP000549

#check @Erdos676.erdos676_negative
#check @Erdos676.erdos676_infinite_exceptions
#check @Erdos676.full_quantitative_disproof
#check @JSP000549.original_question_negative
#check @JSP000549.arbitrarily_large_exceptions
#print JSP000549.OriginalQuestion
#print Erdos676.Representable
#print Erdos676.EventualRepresentation
#print Erdos676.QuantitativeDisproof
#print axioms Erdos676.erdos676_negative
#print axioms Erdos676.erdos676_infinite_exceptions
#print axioms Erdos676.full_quantitative_disproof
#print axioms JSP000549.question_equivalent
#print axioms JSP000549.original_question_negative
#print axioms JSP000549.arbitrarily_large_exceptions
