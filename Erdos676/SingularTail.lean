import Erdos676.SingularFactors
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open scoped BigOperators

namespace Erdos676

theorem product_increment_upper {P : Type*} [LinearOrder P]
    (s : Finset P) (v c : P → ℝ)
    (hv : ∀ p ∈ s, 0 ≤ v p) (hc : ∀ p ∈ s, 1 + v p ≤ c p) :
    (∏ p ∈ s, (1 + v p)) ≤ 1 + (∏ p ∈ s, c p) * ∑ p ∈ s, v p := by
  rw [Finset.prod_one_add_ordered, Finset.mul_sum]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro p hp
  have hprefix : (∏ q ∈ s with q < p, (1 + v q)) ≤ ∏ q ∈ s, c q := by
    calc
      _ ≤ ∏ q ∈ s with q < p, c q :=
        Finset.prod_le_prod₀
          (fun q hq => by linarith [hv q (Finset.mem_filter.mp hq).1])
          (fun q hq => hc q (Finset.mem_filter.mp hq).1)
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le₀
        (Finset.filter_subset _ _) (fun q hq => by
          linarith [hv q (Finset.mem_filter.mp hq).1, hc q (Finset.mem_filter.mp hq).1])
        (fun q hq _ => by linarith [hv q hq, hc q hq])
  calc
    _ ≤ v p * (∏ q ∈ s, c q) := mul_le_mul_of_nonneg_left hprefix (hv p hp)
    _ = _ := mul_comm _ _

theorem singular_tail_increment_upper (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p)
    (k : ℤ) :
    (∏ p ∈ s, localSingularFactor p (k : ZMod (p ^ 2))) ≤
      1 + (∏ p ∈ s, (p : ℝ) / (p - 1)) *
        ∑ p ∈ s, localSingularExcess p (k : ZMod (p ^ 2)) := by
  calc
    _ ≤ ∏ p ∈ s, (1 + localSingularExcess p (k : ZMod (p ^ 2))) :=
      Finset.prod_le_prod₀ (fun p hp => localSingularFactor_nonneg p (hs p hp) _)
        (fun p _ => by
          have h := le_max_left (localSingularFactor p (k : ZMod (p ^ 2)) - 1) 0
          change _ ≤ 1 + max _ _
          linarith)
    _ ≤ _ := product_increment_upper s _ _
      (fun _ _ => le_max_right _ _)
      (fun p hp => one_add_localSingularExcess_le p (hs p hp) _)

end Erdos676
