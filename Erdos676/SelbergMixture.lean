import Erdos676.BernoulliOrthogonality

open scoped BigOperators

namespace Erdos676

noncomputable def selbergQ {P : Type*} (g : P → ℝ) (r : Finset P) : ℝ :=
  ∏ p ∈ r, g p / (1 - g p)

noncomputable def selbergNormalizer {P : Type*}
    (T : Finset (Finset P)) (g : P → ℝ) : ℝ := ∑ r ∈ T, selbergQ g r

noncomputable def selbergMixture {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ) (t : Finset P) : ℝ :=
  ∑ r ∈ T, (selbergQ g r / selbergNormalizer T g) * bernoulliBasis g r t

theorem selbergQ_nonneg {P : Type*} (g : P → ℝ) (r : Finset P)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) : 0 ≤ selbergQ g r := by
  exact Finset.prod_nonneg (fun p _ => div_nonneg (hg0 p) (sub_nonneg.mpr (hg1 p)))

theorem selbergNormalizer_pos {P : Type*} [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ) (hEmpty : ∅ ∈ T)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    0 < selbergNormalizer T g := by
  have h := Finset.single_le_sum (fun r (_ : r ∈ T) => selbergQ_nonneg g r hg0 hg1) hEmpty
  have hone : (1 : ℝ) ≤ selbergNormalizer T g := by
    simpa only [selbergQ, Finset.prod_empty, selbergNormalizer] using h
  linarith

theorem selbergQ_mul_norm {P : Type*} (g : P → ℝ)
    (hg0 : ∀ p, g p ≠ 0) (hg1 : ∀ p, g p ≠ 1) (r : Finset P) :
    selbergQ g r * (∏ p ∈ r, (1 - g p) / g p) = 1 := by
  unfold selbergQ
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p _
  field_simp [hg0 p, sub_ne_zero.mpr (Ne.symm (hg1 p))]

theorem selbergMixture_empty {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ) (hG : selbergNormalizer T g ≠ 0) :
    selbergMixture T g ∅ = 1 := by
  simp only [selbergMixture, bernoulliBasis_empty, mul_one, ← Finset.sum_div]
  exact div_self hG

theorem selbergMixture_second_moment {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ)
    (hg0 : ∀ p, g p ≠ 0) (hg1 : ∀ p, g p ≠ 1)
    (hG : selbergNormalizer T g ≠ 0) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g * (selbergMixture T g t) ^ 2) =
      1 / selbergNormalizer T g := by
  unfold selbergMixture
  rw [weighted_orthogonal_square T Finset.univ
    (fun t => bernoulliWeight Finset.univ t g) (bernoulliBasis g)
    (fun r => selbergQ g r / selbergNormalizer T g)
    (fun r => ∏ p ∈ r, (1 - g p) / g p)
    (fun r _ u _ => bernoulliBasis_orthogonal g hg0 r u)]
  calc
    _ = ∑ r ∈ T, selbergQ g r / (selbergNormalizer T g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      have hnorm := selbergQ_mul_norm g hg0 hg1 r
      field_simp
      nlinarith [congrArg (fun x => selbergQ g r * x) hnorm]
    _ = 1 / selbergNormalizer T g := by
      rw [← Finset.sum_div]
      change selbergNormalizer T g / (selbergNormalizer T g) ^ 2 = _
      field_simp

end Erdos676
