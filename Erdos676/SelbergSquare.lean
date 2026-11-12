import Erdos676.BernoulliMoments

open scoped BigOperators

namespace Erdos676

noncomputable def eventProduct {P N : Type*} (E : P → N → Prop)
    (t : Finset P) (n : N) : ℝ := by
  classical
  exact if ∀ p ∈ t, E p n then 1 else 0

theorem eventProduct_union {P N : Type*} [DecidableEq P]
    (E : P → N → Prop) (t u : Finset P) (n : N) :
    eventProduct E (t ∪ u) n = eventProduct E t n * eventProduct E u n := by
  classical
  simp only [eventProduct, Finset.forall_mem_union]
  split_ifs <;> simp_all

noncomputable def sieveSquareRoot {P N : Type*}
    (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop) (n : N) : ℝ :=
  ∑ t ∈ T, weights t * eventProduct E t n

theorem sieveSquareRoot_of_avoids {P N : Type*} [DecidableEq P]
    (s : Finset P) (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1)
    (n : N) (hn : ∀ p ∈ s, ¬ E p n) :
    sieveSquareRoot T weights E n = 1 := by
  classical
  unfold sieveSquareRoot
  rw [Finset.sum_eq_single ∅]
  · simp [eventProduct, hweights]
  · intro t ht htne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr htne
    have hfalse : ¬ ∀ q ∈ t, E q n := fun h => hn p (hT t ht hp) (h p hp)
    simp [eventProduct, hfalse]
  · exact fun h => (h hEmpty).elim

theorem avoidance_le_sieveSquare {P N : Type*} [DecidableEq P]
    (s : Finset P) (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1) (n : N) :
    eventProduct (fun p n => ¬ E p n) s n ≤ (sieveSquareRoot T weights E n) ^ 2 := by
  classical
  unfold eventProduct
  split_ifs with hn
  · rw [sieveSquareRoot_of_avoids s T weights E hT hEmpty hweights n hn]
    norm_num
  · exact sq_nonneg _

theorem sieveSquare_expansion {P N : Type*} [DecidableEq P]
    (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop) (n : N) :
    (sieveSquareRoot T weights E n) ^ 2 =
      ∑ t ∈ T, ∑ u ∈ T, weights t * weights u * eventProduct E (t ∪ u) n := by
  unfold sieveSquareRoot
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [eventProduct_union]
  ring

theorem avoidance_sum_le_sieveSquare {P N : Type*} [DecidableEq P]
    (I : Finset N) (s : Finset P) (T : Finset (Finset P))
    (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) s n) ≤
      ∑ t ∈ T, ∑ u ∈ T, weights t * weights u * (∑ n ∈ I, eventProduct E (t ∪ u) n) := by
  classical
  calc
    _ ≤ ∑ n ∈ I, (sieveSquareRoot T weights E n) ^ 2 :=
      Finset.sum_le_sum fun n _ => avoidance_le_sieveSquare s T weights E hT hEmpty hweights n
    _ = _ := by
      simp_rw [sieveSquare_expansion]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      exact (Finset.mul_sum _ _ _).symm

theorem selberg_square_upper_bound {P N : Type*} [DecidableEq P]
    (I : Finset N) (s : Finset P) (T : Finset (Finset P))
    (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1)
    (mass : ℝ) (density : Finset P → ℝ) (error : Finset P → Finset P → ℝ)
    (happrox : ∀ t ∈ T, ∀ u ∈ T,
      |(∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)| ≤ error t u) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) s n) ≤
      mass * (∑ t ∈ T, ∑ u ∈ T, weights t * weights u * density (t ∪ u)) +
        ∑ t ∈ T, ∑ u ∈ T, |weights t * weights u| * error t u := by
  classical
  have hterm (t : Finset P) (ht : t ∈ T) (u : Finset P) (hu : u ∈ T) :
      weights t * weights u * (∑ n ∈ I, eventProduct E (t ∪ u) n) ≤
        mass * (weights t * weights u * density (t ∪ u)) +
          |weights t * weights u| * error t u := by
    have hscaled := mul_le_mul_of_nonneg_left (happrox t ht u hu)
      (abs_nonneg (weights t * weights u))
    have habs : weights t * weights u *
        ((∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)) ≤
        |weights t * weights u| *
          |(∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)| := by
      simpa only [abs_mul] using le_abs_self (weights t * weights u *
        ((∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)))
    nlinarith
  calc
    _ ≤ ∑ t ∈ T, ∑ u ∈ T,
        weights t * weights u * (∑ n ∈ I, eventProduct E (t ∪ u) n) :=
      avoidance_sum_le_sieveSquare I s T weights E hT hEmpty hweights
    _ ≤ ∑ t ∈ T, ∑ u ∈ T,
        (mass * (weights t * weights u * density (t ∪ u)) +
          |weights t * weights u| * error t u) := by
      exact Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun u hu => hterm t ht u hu
    _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end Erdos676
