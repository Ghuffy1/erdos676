import Erdos676.HighPrimeAveraging
import Erdos676.AvoidanceIteration

open scoped BigOperators
open Filter
open scoped Topology

namespace Erdos676

noncomputable def primeAvoidSet (s : Finset ℕ) (A B : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc A B).filter (fun n => ∀ p ∈ s,
    (n : ZMod (p ^ 2)) ∉ initialResidues (p ^ 2) p)

noncomputable def primeWitnessCount (s : Finset ℕ) (n : ℤ) : ℝ := by
  classical
  exact ∑ p ∈ s, if (n : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then 1 else 0

noncomputable def primeMass (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1 / (p : ℝ)

theorem primeAvoidSet_subtype (s : Finset ℕ) (A B : ℤ) :
    originalAvoidSet (fun p : s => (p : ℕ)) A B = primeAvoidSet s A B := by
  classical
  ext n
  simp [originalAvoidSet, primeAvoidSet]

theorem primeBandCount_subtype (s : Finset ℕ) (n : ℤ) :
    primeBandCount (fun p : s => (p : ℕ)) n = primeWitnessCount s n := by
  classical
  unfold primeBandCount primeWitnessCount
  have h := Finset.sum_coe_sort s (fun p : ℕ =>
    if (n : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then (1 : ℝ) else 0)
  exact h

theorem primeMass_subtype (s : Finset ℕ) :
    (∑ p : s, (1 : ℝ) / (p : ℕ)) = primeMass s := by
  exact Finset.sum_coe_sort s (fun p : ℕ => 1 / (p : ℝ))

theorem primeAvoidSet_mono {s t : Finset ℕ} (hst : s ⊆ t) (A B : ℤ) :
    primeAvoidSet t A B ⊆ primeAvoidSet s A B := by
  classical
  intro n hn
  obtain ⟨hnI, hnP⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnI, fun p hp => hnP p (hst hp)⟩

theorem primeAvoidSet_union (s t : Finset ℕ) (A B : ℤ) :
    primeAvoidSet (s ∪ t) A B = (primeAvoidSet s A B).filter
      (fun n => ∀ p ∈ t, (n : ZMod (p ^ 2)) ∉ initialResidues (p ^ 2) p) := by
  classical
  ext n
  simp only [primeAvoidSet, Finset.mem_filter, Finset.mem_union]
  aesop

theorem prime_avoidance_step (s t : Finset ℕ) (A B : ℤ) (mass error : ℝ)
    (hcount : (∑ n ∈ primeAvoidSet s A B, primeWitnessCount t n) ≤
      mass * (primeAvoidSet s A B).card + error) :
    (1 - mass) * (primeAvoidSet s A B).card - error ≤ (primeAvoidSet (s ∪ t) A B).card := by
  classical
  have hsum : (∑ n ∈ primeAvoidSet s A B, ∑ p : t,
      if (n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p then (1 : ℝ) else 0) ≤
      mass * (primeAvoidSet s A B).card + error := by
    have heq (n : ℤ) : (∑ p : t,
        if (n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p then (1 : ℝ) else 0) =
        primeWitnessCount t n :=
      Finset.sum_coe_sort t (fun p : ℕ =>
        if (n : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then (1 : ℝ) else 0)
    simpa only [heq] using hcount
  have h := avoidance_block_lower (primeAvoidSet s A B)
    (fun (p : t) n => (n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p) mass error hsum
  have hset : (primeAvoidSet s A B).filter
      (fun n => ∀ p : t, ¬(n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p) =
      primeAvoidSet (s ∪ t) A B := by
    ext n
    simp only [primeAvoidSet, Finset.mem_filter, Finset.mem_union]
    aesop
  convert h using 1
  apply congrArg (fun z : Finset ℤ => (z.card : ℝ))
  ext n
  simp only [primeAvoidSet, Finset.mem_filter, Finset.mem_union]
  aesop

theorem prime_set_high_averaging {a b η c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 4) (hbη : b < η) (hηc : η < c) (hc : c ≤ 1 / 2) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      ∀ s t : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ t, p.Prime) →
        (∀ p ∈ s, (X : ℝ) ^ c ≤ p) → (∀ p ∈ s, (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) →
        (∀ p ∈ t, (X : ℝ) ^ a ≤ p) → (∀ p ∈ t, (p : ℝ) ≤ (X : ℝ) ^ b) →
        |(∑ n ∈ primeAvoidSet s ((X : ℤ) + 1) (2 * X), primeWitnessCount t n) -
          primeMass t * (primeAvoidSet s ((X : ℤ) + 1) (2 * X)).card| ≤ K * (X : ℝ) ^ (1 - δ) := by
  obtain ⟨K, δ, hK, hδ, h⟩ := high_prime_averaging ha hab hb hbη hηc hc
  refine ⟨K, δ, hK, hδ, ?_⟩
  filter_upwards [h] with X hX
  intro s t hs ht hslo hshi htlo hthi
  letI (p : s) : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  letI (p : t) : NeZero (p : ℕ) := ⟨(ht p p.property).ne_zero⟩
  have hbound := hX t (fun p : t => (p : ℕ)) (fun p => ht p p.property) Subtype.val_injective
    (fun p => htlo p p.property) (fun p => hthi p p.property)
    s (fun p : s => (p : ℕ)) (fun p => hs p p.property) Subtype.val_injective
    (fun p => hslo p p.property) (fun p => hshi p p.property)
  simpa only [primeAvoidSet_subtype, primeBandCount_subtype, primeMass_subtype] using hbound

end Erdos676
