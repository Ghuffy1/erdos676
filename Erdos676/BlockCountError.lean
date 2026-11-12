import Erdos676.BonferroniProduct
import Erdos676.OneShiftCounts
import Erdos676.BlockCoefficientBound

open scoped BigOperators

namespace Erdos676

theorem bounded_block_product_count_error {J P : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (blocks : J → Finset P) (k B : J → ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hB : ∀ j, 1 ≤ B j) (hmax : ∀ j, ∀ p ∈ blocks j, a p ≤ B j)
    (S N : ℕ) :
    |(∑ n ∈ Finset.range N, ∏ j : J, bonferroniEvent (blocks j) (k j)
        (residueEvent a (fun p => smallResidues (a p)) S) n) -
      (N : ℝ) * (∏ j : J, bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p))| ≤
      ∏ j : J, (B j : ℝ) ^ (2 * k j) := by
  have h := bonferroni_product_count_error (Finset.range N) blocks k
    (residueEvent a (fun p => smallResidues (a p)) S)
    (fun p => (1 : ℝ) / a p) (fun p => (a p : ℝ)) N hdisjoint
    (fun d => one_shift_prime_count_error a hinj hprime d S N)
  apply h.trans
  apply Finset.prod_le_prod₀
  · intro j hj
    exact Finset.sum_nonneg (fun d hd => Finset.prod_nonneg (fun p hp => Nat.cast_nonneg (a p)))
  · intro j hj
    have hNat := bounded_block_coefficient_sum (blocks j) a hinj.injOn (B j) (k j) (hB j)
      (fun p hp => (hprime p).two_le) (hmax j)
    exact_mod_cast hNat

end Erdos676
