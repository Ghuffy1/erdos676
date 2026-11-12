import Erdos676.PrimeBlockLower
import Erdos676.DyadicErrorBudget

open scoped BigOperators

namespace Erdos676

theorem dyadic_first_moment_lower {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hz : 1 ≤ z) (hmax : ∀ p, (a p : ℝ) ≤ z)
    (J L : ℕ) (hL : 1 ≤ L) (hcover : dyadicCutoff z J < 2)
    (C : ℝ)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1)
    (S N : ℕ) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N *
        (∏ p : P, (1 - (1 : ℝ) / a p)) -
      (2 * (J : ℝ) + 1) * z ^ (8 * L + 8) ≤
      ∑ n ∈ Finset.range N, eventProduct
        (fun p n => ¬ residueEvent a (fun p => smallResidues (a p)) S p n) Finset.univ n := by
  let blocks (j : Fin J) := dyadicPrimeBlock a z j.val
  let B (j : Fin J) := ⌊dyadicCutoff z j.val⌋₊
  have hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)) := by
    intro i j hij
    exact dyadicPrimeBlocks_disjoint a hz (fun h => hij (Fin.ext h))
  have hB (j : Fin J) : 1 ≤ B j := floor_dyadicCutoff_pos hz j.val
  have hbound (j : Fin J) (p : P) (hp : p ∈ blocks j) : a p ≤ B j :=
    Nat.le_floor ((mem_dyadicPrimeBlock a z j.val p).mp hp).2
  have hmass (j : Fin J) : (∑ p ∈ blocks j, (1 : ℝ) / a p) ≤ C :=
    dyadicPrimeBlock_mass_le a hinj hprime hz C hC j.val
  have h := prime_block_first_moment_lower a hinj hprime J L hL blocks B
    hdisjoint hB hbound C hmass hsmall S N
  have hcover' : Finset.univ.biUnion blocks = Finset.univ :=
    dyadicPrimeBlocks_cover a hprime z hmax J hcover
  rw [hcover'] at h
  have herror : (∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val))) ≤ z ^ (8 * L + 8) :=
    dyadic_error_product_le hz L J
  have hscaled := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ 2 * (J : ℝ) + 1)
  calc
    _ ≤ (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N *
        (∏ p : P, (1 - (1 : ℝ) / a p)) -
      (2 * (J : ℝ) + 1) * (∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val))) :=
      sub_le_sub_left hscaled _
    _ ≤ _ := h

end Erdos676
