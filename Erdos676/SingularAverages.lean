import Erdos676.SingularFactors
import Erdos676.ResidueAverages

open scoped BigOperators

namespace Erdos676

theorem localSingularFactor_sum (p : ℕ) [NeZero p] (hp : 1 ≤ p) :
    (∑ k : ZMod (p ^ 2), localSingularFactor p k) = (p : ℝ) ^ 2 :=
  normalized_overlap_sum p hp

theorem singular_mixed_average_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (s : Finset P) (H : ℕ) (hH : 0 < H) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      ∏ p : P, if p ∈ s then
        localSingularExcess (a p) ((i : ZMod ((a p) ^ 2)) - j)
      else localSingularFactor (a p) ((i : ZMod ((a p) ^ 2)) - j)) / (H : ℝ) ^ 2 ≤
      (1 + (∏ p : P, (a p) ^ 2 : ℕ) / (H : ℝ)) *
        (∏ p : P, if p ∈ s then 1 / ((a p : ℝ) - 1) ^ 2 else 1) := by
  classical
  letI (p : P) : NeZero (a p) := ⟨(hprime p).ne_zero⟩
  letI : NeZero (∏ p : P, (a p) ^ 2) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero 2 (hprime p).ne_zero)⟩
  have hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun heq => hpq (hinj heq))).pow 2 2
  apply crt_pair_average_upper (fun p => (a p) ^ 2) hc
    (fun p k => if p ∈ s then localSingularExcess (a p) k else localSingularFactor (a p) k)
    (fun p => if p ∈ s then 1 / ((a p : ℝ) - 1) ^ 2 else 1) _ _ H hH
  · intro p k
    split_ifs
    · exact le_max_right _ _
    · exact localSingularFactor_nonneg _ (hprime p).two_le _
  · intro p
    by_cases hp : p ∈ s
    · simp only [hp, if_true, Nat.cast_pow]
      simpa only [div_eq_mul_inv, one_mul] using
        localSingularExcess_sum_le (a p) (hprime p).two_le
    · simp only [hp, if_false, mul_one, Nat.cast_pow]
      exact (localSingularFactor_sum (a p) (hprime p).one_lt.le).le

theorem singular_product_average_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (H : ℕ) (hH : 0 < H) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      ∏ p : P, localSingularFactor (a p) ((i : ZMod ((a p) ^ 2)) - j)) /
        (H : ℝ) ^ 2 ≤ 1 + (∏ p : P, (a p) ^ 2 : ℕ) / (H : ℝ) := by
  simpa only [Finset.notMem_empty, if_false, Finset.prod_const_one, mul_one] using
    singular_mixed_average_upper a hinj hprime ∅ H hH

end Erdos676
