import Erdos676.PolynomialError

open scoped BigOperators

namespace Erdos676

noncomputable def eventMixture {P N : Type*}
    (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop) (n : N) : ℝ :=
  ∑ r ∈ T, (selbergQ g r / selbergNormalizer T g) * eventBasis g r E n

theorem selberg_coefficient_sum {P : Type*} (T : Finset (Finset P)) (g : P → ℝ)
    (hG : selbergNormalizer T g ≠ 0) :
    (∑ r ∈ T, selbergQ g r / selbergNormalizer T g) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hG

theorem eventMixture_of_avoids {P N : Type*}
    (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop) (n : N)
    (hG : selbergNormalizer T g ≠ 0) (hn : ∀ p, ¬ E p n) : eventMixture T g E n = 1 := by
  have hb (r : Finset P) : eventBasis g r E n = 1 := by
    simp [eventBasis, hn]
  simp only [eventMixture, hb, mul_one]
  exact selberg_coefficient_sum T g hG

theorem selberg_model_quadratic {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ)
    (hg0 : ∀ p, g p ≠ 0) (hg1 : ∀ p, g p ≠ 1) (hG : selbergNormalizer T g ≠ 0) :
    (∑ r ∈ T, ∑ u ∈ T, (selbergQ g r / selbergNormalizer T g) *
      (selbergQ g u / selbergNormalizer T g) *
        (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)) = 1 / selbergNormalizer T g := by
  have h := weighted_square_expansion T Finset.univ
    (fun t => bernoulliWeight Finset.univ t g) (bernoulliBasis g)
    (fun r => selbergQ g r / selbergNormalizer T g)
  simp_rw [bernoulliBasis_orthogonal g hg0] at h
  exact h.symm.trans (selbergMixture_second_moment T g hg0 hg1 hG)

theorem eventMixture_second_moment_upper {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop)
    (hEmpty : ∅ ∈ T) (hg0 : ∀ p, 0 < g p) (hg1 : ∀ p, g p < 1) (M D : ℝ)
    (happrox : ∀ r ∈ T, ∀ u ∈ T,
      |(∑ n ∈ I, eventBasis g r E n * eventBasis g u E n) -
        M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)| ≤ D) :
    (∑ n ∈ I, (eventMixture T g E n) ^ 2) ≤ M / selbergNormalizer T g + D := by
  have hG : 0 < selbergNormalizer T g := selbergNormalizer_pos T g hEmpty
    (fun p => (hg0 p).le) (fun p => (hg1 p).le)
  let c (r : Finset P) := selbergQ g r / selbergNormalizer T g
  have hc (r : Finset P) : 0 ≤ c r :=
    div_nonneg (selbergQ_nonneg g r (fun p => (hg0 p).le) (fun p => (hg1 p).le)) hG.le
  have hcsum : (∑ r ∈ T, |c r|) = 1 := by
    simp_rw [abs_of_nonneg (hc _)]
    exact selberg_coefficient_sum T g (ne_of_gt hG)
  have herror := double_sum_error_bound T T c c
    (fun r u => ∑ n ∈ I, eventBasis g r E n * eventBasis g u E n)
    (fun r u => M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)) D happrox
  rw [hcsum, one_mul, one_mul] at herror
  have hmodel : (∑ r ∈ T, ∑ u ∈ T, c r * c u *
      (M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0))) =
        M / selbergNormalizer T g := by
    calc
      _ = M * (∑ r ∈ T, ∑ u ∈ T, c r * c u *
          (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        rw [selberg_model_quadratic T g (fun p => ne_of_gt (hg0 p))
          (fun p => ne_of_lt (hg1 p)) (ne_of_gt hG)]
        ring
  rw [hmodel] at herror
  have hactual := weighted_square_expansion T I (fun _ => 1)
    (fun r n => eventBasis g r E n) c
  simp only [one_mul] at hactual
  change (∑ n ∈ I, (∑ r ∈ T, c r * eventBasis g r E n) ^ 2) ≤ _
  rw [hactual]
  linarith [(abs_le.mp herror).2]

theorem selberg_avoidance_upper_from_inner {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop)
    (hEmpty : ∅ ∈ T) (hg0 : ∀ p, 0 < g p) (hg1 : ∀ p, g p < 1) (M D : ℝ)
    (happrox : ∀ r ∈ T, ∀ u ∈ T,
      |(∑ n ∈ I, eventBasis g r E n * eventBasis g u E n) -
        M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)| ≤ D) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) Finset.univ n) ≤
      M / selbergNormalizer T g + D := by
  classical
  have hG := selbergNormalizer_pos T g hEmpty (fun p => (hg0 p).le) (fun p => (hg1 p).le)
  calc
    _ ≤ ∑ n ∈ I, (eventMixture T g E n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      unfold eventProduct
      split_ifs with hn
      · have hn' : ∀ p, ¬ E p n := fun p => hn p (Finset.mem_univ p)
        rw [eventMixture_of_avoids T g E n (ne_of_gt hG) hn']
        norm_num
      · exact sq_nonneg _
    _ ≤ _ := eventMixture_second_moment_upper I T g E hEmpty hg0 hg1 M D happrox

theorem selberg_avoidance_upper_from_counts {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop)
    (hEmpty : ∅ ∈ T) (hg0 : ∀ p, 0 < g p) (hg1 : ∀ p, g p < 1)
    (M K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcoefficient : ∀ r ∈ T, (∑ d ∈ r.powerset, |basisCoefficient g d|) ≤ L)
    (hcounts : ∀ r ∈ T, ∀ u ∈ T, ∀ d ∈ r.powerset, ∀ e ∈ u.powerset,
      |(∑ n ∈ I, eventProduct E (d ∪ e) n) - M * (∏ p ∈ d ∪ e, g p)| ≤ K) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) Finset.univ n) ≤
      M / selbergNormalizer T g + L ^ 2 * K := by
  apply selberg_avoidance_upper_from_inner I T g E hEmpty hg0 hg1 M (L ^ 2 * K)
  intro r hr u hu
  have h := eventBasis_inner_error I g (fun p => ne_of_gt (hg0 p)) r u E M K
    (hcounts r hr u hu)
  have hprod := mul_le_mul (hcoefficient r hr) (hcoefficient u hu)
    (Finset.sum_nonneg (fun d _ => abs_nonneg (basisCoefficient g d))) hL
  have hscaled := mul_le_mul_of_nonneg_right hprod hK
  exact h.trans (by simpa only [pow_two] using hscaled)

end Erdos676
