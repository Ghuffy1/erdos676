import Erdos676.LocalResidues

namespace Erdos676

def initialResidues (m p : ℕ) : Finset (ZMod m) :=
  (Finset.range p).image (fun k : ℕ => (k : ZMod m))

def expandedResidues (m p R : ℕ) : Finset (ZMod m) :=
  (Finset.range (p + R)).image (fun k : ℕ => (k : ZMod m) - R)

def contractedResidues (m p R : ℕ) : Finset (ZMod m) := initialResidues m (p - R)

def boundaryResidues (m p R : ℕ) : Finset (ZMod m) :=
  expandedResidues m p R \ contractedResidues m p R

theorem contracted_subset_initial (m p R : ℕ) : contractedResidues m p R ⊆ initialResidues m p := by
  apply Finset.image_subset_image
  exact Finset.range_mono (Nat.sub_le p R)

theorem initial_subset_expanded (m p R : ℕ) : initialResidues m p ⊆ expandedResidues m p R := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨k + R, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), ?_⟩
  simp only [Nat.cast_add, add_sub_cancel_right]

theorem contracted_shift_initial (m p R h : ℕ) (hh : h ≤ R) (n : ZMod m)
    (hn : n ∈ contractedResidues m p R) : n + h ∈ initialResidues m p := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨k + h, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), ?_⟩
  rw [Nat.cast_add, heq]

theorem initial_shift_expanded (m p R h : ℕ) (hh : h ≤ R) (n : ZMod m)
    (hn : n + h ∈ initialResidues m p) : n ∈ expandedResidues m p R := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨k + (R - h),
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), ?_⟩
  rw [Nat.cast_add, Nat.cast_sub hh, heq]
  ring

theorem initialResidues_card (m p : ℕ) (hp : p ≤ m) : (initialResidues m p).card = p := by
  unfold initialResidues
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < m := (Finset.mem_range.mp ha).trans_le hp
  have hb' : b < m := (Finset.mem_range.mp hb).trans_le hp
  have hval := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hval

theorem boundaryResidues_card_le (m p R : ℕ) (hp : p ≤ m) :
    (boundaryResidues m p R).card ≤ 2 * R := by
  have hsub := (contracted_subset_initial m p R).trans (initial_subset_expanded m p R)
  have hcon : (contractedResidues m p R).card = p - R := initialResidues_card m (p - R)
    ((Nat.sub_le p R).trans hp)
  have hexp : (expandedResidues m p R).card ≤ p + R := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range (p + R))
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  change (boundaryResidues m p R).card + (contractedResidues m p R).card =
    (expandedResidues m p R).card at hcard
  omega

theorem outside_boundary_shift (m p R h : ℕ) (hh : h ≤ R) (n : ZMod m)
    (hn : n ∉ boundaryResidues m p R) :
    n + h ∈ initialResidues m p ↔ n ∈ initialResidues m p := by
  have hcon (he : n ∈ expandedResidues m p R) : n ∈ contractedResidues m p R := by
    by_contra hc
    exact hn (Finset.mem_sdiff.mpr ⟨he, hc⟩)
  constructor
  · intro hmem
    exact contracted_subset_initial m p R (hcon (initial_shift_expanded m p R h hh n hmem))
  · intro hmem
    exact contracted_shift_initial m p R h hh n (hcon (initial_subset_expanded m p R hmem))

theorem initial_prime_square (p : ℕ) : initialResidues (p ^ 2) p = smallResidues p := rfl

end Erdos676
