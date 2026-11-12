import Erdos676.MomentBounds

open scoped BigOperators

namespace Erdos676

noncomputable def bracketLoss {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (lower upper : ι → ℝ) : ℝ :=
  ∑ j ∈ s, (upper j - lower j) * ∏ i ∈ s.erase j, upper i

theorem bracketLoss_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (j : ι) (hj : j ∉ s) (lower upper : ι → ℝ) :
    bracketLoss (insert j s) lower upper =
      (upper j - lower j) * (∏ i ∈ s, upper i) + upper j * bracketLoss s lower upper := by
  unfold bracketLoss
  rw [Finset.sum_insert hj, Finset.erase_insert hj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hji : j ≠ i := by
    intro h
    subst i
    exact hj hi
  rw [Finset.erase_insert_of_ne hji, Finset.prod_insert]
  · ring
  · exact fun h => hj (Finset.mem_of_mem_erase h)

/-- The grouped Bonferroni lower bound allows the lower brackets to be negative. -/
theorem product_lower_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (actual lower upper : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ actual i)
    (hl : ∀ i ∈ s, lower i ≤ actual i)
    (hu : ∀ i ∈ s, actual i ≤ upper i) :
    (∏ i ∈ s, upper i) - bracketLoss s lower upper ≤ ∏ i ∈ s, actual i := by
  induction s using Finset.induction_on with
  | empty => simp [bracketLoss]
  | @insert j s hj ih =>
      have haS : ∀ i ∈ s, 0 ≤ actual i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hlS : ∀ i ∈ s, lower i ≤ actual i := fun i hi => hl i (Finset.mem_insert_of_mem hi)
      have huS : ∀ i ∈ s, actual i ≤ upper i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have haj := ha j (Finset.mem_insert_self j s)
      have hlj := hl j (Finset.mem_insert_self j s)
      have huj := hu j (Finset.mem_insert_self j s)
      have hup : ∀ i ∈ s, 0 ≤ upper i := fun i hi => (haS i hi).trans (huS i hi)
      have hp : 0 ≤ ∏ i ∈ s, upper i := Finset.prod_nonneg hup
      have hL : 0 ≤ bracketLoss s lower upper := by
        unfold bracketLoss
        apply Finset.sum_nonneg
        intro i hi
        exact mul_nonneg (sub_nonneg.mpr ((hlS i hi).trans (huS i hi)))
          (Finset.prod_nonneg fun k hk => hup k (Finset.mem_of_mem_erase hk))
      have hscaled := mul_le_mul_of_nonneg_left (ih haS hlS huS) haj
      have hterm1 := mul_nonneg (sub_nonneg.mpr hlj) hp
      have hterm2 := mul_nonneg (sub_nonneg.mpr huj) hL
      rw [Finset.prod_insert hj, Finset.prod_insert hj, bracketLoss_insert s j hj]
      nlinarith

end Erdos676
