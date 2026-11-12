import Erdos676.GroupedFirstMoment
import Erdos676.BonferroniBlockBounds
import Erdos676.BlockParameters

open scoped BigOperators

namespace Erdos676

theorem prime_block_first_moment_lower {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (J L : ℕ) (hL : 1 ≤ L) (blocks : Fin J → Finset P) (B : Fin J → ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hB : ∀ j, 1 ≤ B j) (hmax : ∀ j, ∀ p ∈ blocks j, a p ≤ B j)
    (C : ℝ) (hC : ∀ j, (∑ p ∈ blocks j, (1 : ℝ) / a p) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) (S N : ℕ) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N *
        (∏ p ∈ Finset.univ.biUnion blocks, (1 - (1 : ℝ) / a p)) -
      (2 * (J : ℝ) + 1) * (∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val))) ≤
      ∑ n ∈ Finset.range N, eventProduct
        (fun p n => ¬ residueEvent a (fun p => smallResidues (a p)) S p n)
        (Finset.univ.biUnion blocks) n := by
  let g (p : P) : ℝ := 1 / a p
  let k (j : Fin J) := 2 * (L + j.val)
  let error (j : Fin J) : ℝ := Real.exp (4 * C) / (2 : ℝ) ^ k j
  let u (j : Fin J) := bonferroniModel (blocks j) (k j) g
  let l (j : Fin J) := bonferroniModel (blocks j) (k j - 1) g
  let V (j : Fin J) := ∏ p ∈ blocks j, (1 - g p)
  have hg0 (p : P) : 0 ≤ g p := by dsimp [g]; positivity
  have hg1 (p : P) : g p ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < a p := by exact_mod_cast (hprime p).pos
    have hp2 : (2 : ℝ) ≤ a p := by exact_mod_cast (hprime p).two_le
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hk (j : Fin J) : Even (k j) := ⟨L + j.val, by dsimp [k]; omega⟩
  have hkpos (j : Fin J) : 1 ≤ k j := by dsimp [k]; omega
  have hV : ∀ j ∈ (Finset.univ : Finset (Fin J)), 0 ≤ V j := by
    intro j hj
    apply Finset.prod_nonneg
    intro p hp
    have := hg1 p
    linarith
  have hupper : ∀ j ∈ (Finset.univ : Finset (Fin J)), V j ≤ u j := by
    intro j hj
    exact bonferroniModel_even_upper g (blocks j) (k j) (hk j) hg0 (fun p => by have := hg1 p; linarith)
  have hgap : ∀ j ∈ (Finset.univ : Finset (Fin J)), u j - l j ≤ error j * u j := by
    intro j hj
    have hsub : k j - 1 + 1 = k j := Nat.sub_add_cancel (hkpos j)
    have heven : Even (k j - 1 + 1) := by rw [hsub]; exact hk j
    have h := bonferroniModel_relative_gap g (blocks j) (k j - 1) heven C hg0 hg1 (hC j)
    simpa only [hsub, u, l, error] using h
  have hsum : (∑ j : Fin J, error j) ≤ 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) := by
    have h := block_error_sum C L J
    simpa only [Finset.sum_range, error, k] using h
  have hmodel := product_bracket_relative_lower (Finset.univ : Finset (Fin J))
    V l u error hV hupper hgap (hsum.trans hsmall)
  have hVprod : 0 ≤ ∏ j : Fin J, V j := Finset.prod_nonneg hV
  have hcompare := mul_le_mul_of_nonneg_right (sub_le_sub_left hsum 1) hVprod
  have hmodel' := hcompare.trans hmodel
  have hscaled := mul_le_mul_of_nonneg_left hmodel' (Nat.cast_nonneg N)
  have hactual := grouped_first_moment_lower a hinj hprime blocks k B hdisjoint hB hmax hk hkpos S N
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J))) blocks :=
    fun i hi j hj hij => hdisjoint hij
  have hVeq : (∏ p ∈ Finset.univ.biUnion blocks, (1 - g p)) = ∏ j : Fin J, V j :=
    Finset.prod_biUnion hpair
  have hpower : (∏ j : Fin J, (B j : ℝ) ^ (2 * k j)) =
      ∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val)) := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp [k]
    congr 1
    omega
  change (N : ℝ) * ((∏ j : Fin J, u j) - bracketLoss Finset.univ l u) -
    (2 * (Fintype.card (Fin J) : ℝ) + 1) * (∏ j : Fin J, (B j : ℝ) ^ (2 * k j)) ≤ _ at hactual
  rw [Fintype.card_fin, hpower] at hactual
  change (1 - _) * (N : ℝ) * (∏ p ∈ Finset.univ.biUnion blocks, (1 - g p)) - _ ≤ _
  rw [hVeq]
  nlinarith

end Erdos676
