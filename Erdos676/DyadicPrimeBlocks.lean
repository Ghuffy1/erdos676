import Erdos676.PrimeBlocks

open scoped BigOperators

namespace Erdos676

noncomputable def dyadicCutoff (z : ℝ) : ℕ → ℝ
  | 0 => z
  | j + 1 => dyadicCutoff z j ^ (1 / 2 : ℝ)

theorem one_le_dyadicCutoff {z : ℝ} (hz : 1 ≤ z) (j : ℕ) : 1 ≤ dyadicCutoff z j := by
  induction j with
  | zero => exact hz
  | succ j ih => exact Real.one_le_rpow ih (by norm_num)

theorem dyadicCutoff_antitone {z : ℝ} (hz : 1 ≤ z) : Antitone (dyadicCutoff z) := by
  apply antitone_nat_of_succ_le
  intro j
  exact Real.rpow_le_self_of_one_le (one_le_dyadicCutoff hz j) (by norm_num)

theorem log_dyadicCutoff {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    Real.log (dyadicCutoff z j) = (1 / 2 : ℝ) ^ j * Real.log z := by
  induction j with
  | zero => simp [dyadicCutoff]
  | succ j ih =>
      have hp : 0 < dyadicCutoff z j := lt_of_lt_of_le zero_lt_one (one_le_dyadicCutoff hz j)
      rw [dyadicCutoff, Real.log_rpow hp, ih, pow_succ]
      ring

theorem exists_cutoff_interval (cutoff : ℕ → ℝ) (J : ℕ) (x : ℝ)
    (hfirst : x ≤ cutoff 0) (hlast : cutoff J < x) :
    ∃ j < J, cutoff (j + 1) < x ∧ x ≤ cutoff j := by
  induction J generalizing x with
  | zero => linarith
  | succ J ih =>
      by_cases hj : cutoff J < x
      · obtain ⟨j, hjJ, hlow, hupp⟩ := ih x hfirst hj
        exact ⟨j, Nat.lt_trans hjJ (Nat.lt_succ_self J), hlow, hupp⟩
      · exact ⟨J, Nat.lt_succ_self J, hlast, le_of_not_gt hj⟩

noncomputable def dyadicPrimeBlock {P : Type*} [Fintype P]
    (a : P → ℕ) (z : ℝ) (j : ℕ) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => dyadicCutoff z (j + 1) < (a p : ℝ) ∧ (a p : ℝ) ≤ dyadicCutoff z j)

theorem mem_dyadicPrimeBlock {P : Type*} [Fintype P]
    (a : P → ℕ) (z : ℝ) (j : ℕ) (p : P) :
    p ∈ dyadicPrimeBlock a z j ↔
      dyadicCutoff z (j + 1) < (a p : ℝ) ∧ (a p : ℝ) ≤ dyadicCutoff z j := by
  classical
  simp [dyadicPrimeBlock]

theorem dyadicPrimeBlocks_disjoint {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) {z : ℝ} (hz : 1 ≤ z) :
    Pairwise (fun i j => Disjoint (dyadicPrimeBlock a z i) (dyadicPrimeBlock a z j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_dyadicPrimeBlock a z i p).mp hpi
  have hj := (mem_dyadicPrimeBlock a z j p).mp hpj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcut := dyadicCutoff_antitone hz (Nat.succ_le_of_lt hlt)
    linarith
  · have hcut := dyadicCutoff_antitone hz (Nat.succ_le_of_lt hgt)
    linarith

theorem dyadicPrimeBlocks_cover {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hprime : ∀ p, (a p).Prime) (z : ℝ) (hmax : ∀ p, (a p : ℝ) ≤ z)
    (J : ℕ) (hlast : dyadicCutoff z J < 2) :
    Finset.univ.biUnion (fun j : Fin J => dyadicPrimeBlock a z j.val) = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro p
  have hp2 : (2 : ℝ) ≤ a p := by exact_mod_cast (hprime p).two_le
  obtain ⟨j, hj, hlow, hupp⟩ := exists_cutoff_interval (dyadicCutoff z) J (a p)
    (hmax p) (hlast.trans_le hp2)
  exact Finset.mem_biUnion.mpr
    ⟨⟨j, hj⟩, Finset.mem_univ _, (mem_dyadicPrimeBlock a z j p).mpr ⟨hlow, hupp⟩⟩

theorem dyadicPrimeBlock_mass_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {z : ℝ} (hz : 1 ≤ z) (C : ℝ)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (j : ℕ) : (∑ p ∈ dyadicPrimeBlock a z j, (1 : ℝ) / a p) ≤ C := by
  let block := dyadicPrimeBlock a z j
  have hlow (p : block) : dyadicCutoff z (j + 1) < (a p : ℝ) :=
    ((mem_dyadicPrimeBlock a z j p).mp p.property).1
  have hupp (p : block) : (a p : ℝ) ≤ dyadicCutoff z j :=
    ((mem_dyadicPrimeBlock a z j p).mp p.property).2
  have h := prime_interval_mass_le (fun p : block => a p)
    (fun p q hpq => Subtype.ext (hinj hpq)) (fun p => hprime p)
    (dyadicCutoff_antitone hz (Nat.le_succ j)) hlow hupp
  have hbound := h.trans (hC (dyadicCutoff z j))
  have hsum : (∑ p : block, (1 : ℝ) / a p) = ∑ p ∈ block, (1 : ℝ) / a p :=
    Finset.sum_coe_sort block (fun p => (1 : ℝ) / a p)
  rw [hsum] at hbound
  exact hbound

end Erdos676
