import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
Classical inputs supplied by the pinned PrimeNumberTheoremAnd development.
Its exact source and commit are recorded in source_audit/vendor_manifest.json.
-/

open scoped BigOperators
open Filter Asymptotics

namespace Erdos676

noncomputable def primesUpToReal (x : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime

noncomputable def primeReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ primesUpToReal x, (1 : ℝ) / p

noncomputable def survivalProduct (x : ℝ) : ℝ :=
  ∏ p ∈ primesUpToReal x, (1 - (1 : ℝ) / p)

theorem prime_reciprocal_error :
    ∃ B C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum x - Real.log (Real.log x) - B| ≤ C / Real.log x := by
  refine ⟨Mertens.M, Real.log 4 + 6 + Mertens.E₁, ?_, ?_⟩
  · have hE := Mertens.E₁.nonneg
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx
    simpa only [primeReciprocalSum, primesUpToReal, Mertens.E₂p, one_div]
      using Mertens.E₂p.abs_le hx

theorem survivalProduct_asymptotic :
    survivalProduct ~[atTop]
      (fun x : ℝ => Real.exp (-Real.eulerMascheroniConstant) / Real.log x) := by
  exact Mertens.E₃.bound''

theorem survivalProduct_pos (x : ℝ) : 0 < survivalProduct x := by
  unfold survivalProduct
  apply Finset.prod_pos
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact sub_pos.mpr ((div_lt_one hp0).mpr hp1)

theorem survivalProduct_formula {x : ℝ} (hx : 1 < x) :
    survivalProduct x = Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Mertens.E₃ x) / Real.log x := by
  exact Mertens.prod_one_minus_div_prime_eq hx

end Erdos676
