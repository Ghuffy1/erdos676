import Erdos676.CRTCounts

open scoped BigOperators

namespace Erdos676

def smallResidues (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  (Finset.range p).image (fun r : ℕ => (r : ZMod (p ^ 2)))

theorem smallResidues_card (p : ℕ) (hp : 1 ≤ p) : (smallResidues p).card = p := by
  have hsq : p ≤ p ^ 2 := by nlinarith
  unfold smallResidues
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < p ^ 2 := lt_of_lt_of_le (Finset.mem_range.mp ha) hsq
  have hb' : b < p ^ 2 := lt_of_lt_of_le (Finset.mem_range.mp hb) hsq
  have hval := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hval

theorem mem_smallResidues (p n : ℕ) (hp : 1 ≤ p) :
    (n : ZMod (p ^ 2)) ∈ smallResidues p ↔ n % p ^ 2 < p := by
  have hsq : p ≤ p ^ 2 := by nlinarith
  constructor
  · intro hn
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hn
    have hr' : r < p ^ 2 := lt_of_lt_of_le (Finset.mem_range.mp hr) hsq
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt hr', ZMod.val_natCast] at hv
    exact hv ▸ Finset.mem_range.mp hr
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨n % p ^ 2, Finset.mem_range.mpr hn, ?_⟩
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod _ _)

theorem prime_square_condition_count_period (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    @Nat.count (fun n => ∀ p ∈ s, n % p ^ 2 < p) (Classical.decPred _)
      ((∏ p ∈ s, p) ^ 2) = ∏ p ∈ s, p := by
  classical
  let m (p : s) := (p.val) ^ 2
  let A (p : s) := smallResidues p.val
  have hm : ∀ p : s, 0 < m p := fun p => pow_pos (hs p p.property).pos _
  have hc : Pairwise (fun p q : s => (m p).Coprime (m q)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hs p p.property) (hs q q.property)).mpr
      (Subtype.coe_ne_coe.mpr hpq)).pow 2 2
  have hpredicate : residueCondition m A = (fun n => ∀ p ∈ s, n % p ^ 2 < p) := by
    funext n
    apply propext
    constructor
    · intro hn p hp
      exact (mem_smallResidues p n (hs p hp).one_lt.le).mp (hn ⟨p, hp⟩)
    · intro hn p
      exact (mem_smallResidues p n (hs p p.property).one_lt.le).mpr (hn p p.property)
  have h := residueCondition_count_period m A hm hc
  rw [hpredicate] at h
  have hcard : ∀ p : s, (A p).card = p.val := fun p =>
    smallResidues_card p (hs p p.property).one_lt.le
  simp only [hcard, m, Finset.prod_pow] at h
  have hprod : (∏ p : s, (p : ℕ)) = ∏ p ∈ s, p :=
    Finset.prod_coe_sort s (fun p : ℕ => p)
  rwa [hprod] at h

theorem prime_square_condition_periodic (s : Finset ℕ) :
    Function.Periodic (fun n => ∀ p ∈ s, n % p ^ 2 < p) ((∏ p ∈ s, p) ^ 2) := by
  intro n
  apply propext
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have hd : p ^ 2 ∣ (∏ q ∈ s, q) ^ 2 :=
    pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp) 2
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod]

/-- The error numerator for an arbitrary interval is at most m cubed,
where m is the product of the selected primes and the common period is m squared. -/
theorem prime_square_interval_scaled_error (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (S N : ℕ) :
    |(((∏ p ∈ s, p) ^ 2 : ℕ) : ℤ) *
        @Nat.count (fun j => ∀ p ∈ s, (S + j) % p ^ 2 < p) (Classical.decPred _) N -
      (N : ℤ) * (∏ p ∈ s, p : ℕ)| ≤
      (((∏ p ∈ s, p) ^ 2 : ℕ) : ℤ) * (∏ p ∈ s, p : ℕ) := by
  classical
  have hm : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have h := periodic_interval_count_scaled_error
    (fun n => ∀ p ∈ s, n % p ^ 2 < p) ((∏ p ∈ s, p) ^ 2) S N
    (pow_pos hm _) (prime_square_condition_periodic s)
  have hcount : Nat.count (fun n => ∀ p ∈ s, n % p ^ 2 < p)
      ((∏ p ∈ s, p) ^ 2) = ∏ p ∈ s, p := by
    convert prime_square_condition_count_period s hs using 1
    exact congrArg (fun D : DecidablePred _ => @Nat.count _ D _)
      (Subsingleton.elim _ _)
  rw [hcount] at h
  convert h using 1
  congr 2
  congr 2
  exact congrArg (fun D : DecidablePred _ => @Nat.count _ D _)
    (Subsingleton.elim _ _)

end Erdos676
