import Erdos676.Bonferroni
import Erdos676.SelbergSquare

open scoped BigOperators

namespace Erdos676

theorem event_choose_count {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) :
    (∑ d ∈ s.powersetCard k, eventProduct E d n) =
      ((@Finset.filter P (fun p => E p n) (Classical.decPred _) s).card.choose k : ℝ) := by
  classical
  have hset : (s.filter (fun p => E p n)).powersetCard k =
      (s.powersetCard k).filter (fun d => ∀ p ∈ d, E p n) := by
    ext d
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hk⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hd hp)).1, hk⟩,
        fun p hp => (Finset.mem_filter.mp (hd hp)).2⟩
    · rintro ⟨⟨hd, hk⟩, he⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hd hp, he p hp⟩, hk⟩
  simp only [eventProduct, Finset.sum_boole]
  rw [← hset, Finset.card_powersetCard]

noncomputable def bonferroniEvent {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j *
    (∑ d ∈ s.powersetCard j, eventProduct E d n)

theorem bonferroniEvent_eq_alternatingChoose {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) :
    bonferroniEvent s k E n =
      (alternatingChoose ((@Finset.filter P (fun p => E p n) (Classical.decPred _) s).card) k : ℝ) := by
  classical
  simp only [bonferroniEvent, event_choose_count, alternatingChoose]
  push_cast
  rfl

theorem eventAvoidance_eq_zero_count {P N : Type*} [DecidableEq P]
    (s : Finset P) (E : P → N → Prop) (n : N) :
    eventProduct (fun p n => ¬ E p n) s n =
      if (@Finset.filter P (fun p => E p n) (Classical.decPred _) s).card = 0 then (1 : ℝ) else 0 := by
  classical
  have hz : (s.filter (fun p => E p n)).card = 0 ↔ ∀ p ∈ s, ¬ E p n := by
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  unfold eventProduct
  congr 1
  exact propext hz.symm

theorem bonferroniEvent_even_upper {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) (hk : Even k) :
    eventProduct (fun p n => ¬ E p n) s n ≤ bonferroniEvent s k E n := by
  classical
  rw [eventAvoidance_eq_zero_count, bonferroniEvent_eq_alternatingChoose]
  exact_mod_cast alternatingChoose_even_upper ((s.filter (fun p => E p n)).card) k hk

theorem bonferroniEvent_odd_lower {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) (hk : Odd k) :
    bonferroniEvent s k E n ≤ eventProduct (fun p n => ¬ E p n) s n := by
  classical
  rw [eventAvoidance_eq_zero_count, bonferroniEvent_eq_alternatingChoose]
  exact_mod_cast alternatingChoose_odd_lower ((s.filter (fun p => E p n)).card) k hk

theorem bonferroniEvent_gap {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) (hk : Even (k + 1)) :
    bonferroniEvent s (k + 1) E n - bonferroniEvent s k E n =
      ∑ d ∈ s.powersetCard (k + 1), eventProduct E d n := by
  classical
  simp only [bonferroniEvent_eq_alternatingChoose, event_choose_count]
  exact_mod_cast alternatingChoose_successor_gap ((s.filter (fun p => E p n)).card) k hk

end Erdos676
