import Erdos676.BlockCountError
import Erdos676.BracketTransfer

open scoped BigOperators

namespace Erdos676

theorem grouped_first_moment_lower {J P : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (blocks : J → Finset P) (k B : J → ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hB : ∀ j, 1 ≤ B j) (hmax : ∀ j, ∀ p ∈ blocks j, a p ≤ B j)
    (hk : ∀ j, Even (k j)) (hkpos : ∀ j, 1 ≤ k j) (S N : ℕ) :
    (N : ℝ) * ((∏ j : J, bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p)) -
        bracketLoss Finset.univ
          (fun j => bonferroniModel (blocks j) (k j - 1) (fun p => (1 : ℝ) / a p))
          (fun j => bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p))) -
      (2 * (Fintype.card J : ℝ) + 1) * (∏ j : J, (B j : ℝ) ^ (2 * k j)) ≤
      ∑ n ∈ Finset.range N, eventProduct
        (fun p n => ¬ residueEvent a (fun p => smallResidues (a p)) S p n)
        (Finset.univ.biUnion blocks) n := by
  let ev := residueEvent a (fun p => smallResidues (a p)) S
  let upper (j : J) (n : ℕ) := bonferroniEvent (blocks j) (k j) ev n
  let lower (j : J) (n : ℕ) := bonferroniEvent (blocks j) (k j - 1) ev n
  let u (j : J) := bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p)
  let l (j : J) := bonferroniModel (blocks j) (k j - 1) (fun p => (1 : ℝ) / a p)
  let error : ℝ := ∏ j : J, (B j : ℝ) ^ (2 * k j)
  have hU : |(∑ n ∈ Finset.range N, ∏ j : J, upper j n) - N * (∏ j : J, u j)| ≤ error :=
    bounded_block_product_count_error a hinj hprime blocks k B hdisjoint hB hmax S N
  have hL : ∀ j : J, j ∈ (Finset.univ : Finset J) →
      |(∑ n ∈ Finset.range N, ∏ i : J, Function.update (fun i => upper i n) j (lower j n) i) -
        N * (∏ i : J, Function.update u j (l j) i)| ≤ error := by
    intro j hj
    let k' := Function.update k j (k j - 1)
    have hsmall (i : J) : k' i ≤ k i := by
      by_cases hi : i = j <;> simp [k', hi]
    have herror : (∏ i : J, (B i : ℝ) ^ (2 * k' i)) ≤ error := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact pow_nonneg (Nat.cast_nonneg _) _
      · intro i hi
        exact pow_le_pow_right₀ (by exact_mod_cast hB i) (Nat.mul_le_mul_left 2 (hsmall i))
    have h := (bounded_block_product_count_error a hinj hprime blocks k' B hdisjoint hB hmax S N).trans herror
    have hactual (i : J) (n : ℕ) : bonferroniEvent (blocks i) (k' i) ev n =
        Function.update (fun i => upper i n) j (lower j n) i := by
      by_cases hi : i = j <;> simp [k', upper, lower, hi]
    have hmodel (i : J) : bonferroniModel (blocks i) (k' i) (fun p => (1 : ℝ) / a p) =
        Function.update u j (l j) i := by
      by_cases hi : i = j <;> simp [k', u, l, hi]
    change |(∑ n ∈ Finset.range N, ∏ i : J, bonferroniEvent (blocks i) (k' i) ev n) -
      (N : ℝ) * (∏ i : J, bonferroniModel (blocks i) (k' i) (fun p => (1 : ℝ) / a p))| ≤ error at h
    simpa only [hactual, hmodel] using h
  have htransfer := product_bracket_transfer (Finset.univ : Finset J) (Finset.range N)
    upper lower u l (N : ℝ) error hU hL
  have hodd (j : J) : Odd (k j - 1) := by
    obtain ⟨m, hm⟩ := hk j
    refine ⟨m - 1, ?_⟩
    have := hkpos j
    omega
  have hpointwise (n : ℕ) : (∏ j : J, upper j n) -
      bracketLoss Finset.univ (fun j => lower j n) (fun j => upper j n) ≤
        eventProduct (fun p n => ¬ ev p n) (Finset.univ.biUnion blocks) n := by
    have h := product_lower_bound (Finset.univ : Finset J)
      (fun j => eventProduct (fun p n => ¬ ev p n) (blocks j) n)
      (fun j => lower j n) (fun j => upper j n) (by
        intro j hj
        unfold eventProduct
        split_ifs <;> norm_num)
      (fun j hj => bonferroniEvent_odd_lower (blocks j) (k j - 1) ev n (hodd j))
      (fun j hj => bonferroniEvent_even_upper (blocks j) (k j) ev n (hk j))
    rwa [← eventProduct_biUnion] at h
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hpointwise n)
  simpa only [Finset.card_univ] using htransfer.trans hsum

end Erdos676
