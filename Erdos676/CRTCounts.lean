import Erdos676.PeriodicCounts
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace Erdos676

def residueCondition {ι : Type*} (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i)))
    (n : ℕ) : Prop := ∀ i, (n : ZMod (m i)) ∈ A i

theorem residueCondition_periodic {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i))) :
    Function.Periodic (residueCondition m A) (∏ i, m i) := by
  intro n
  unfold residueCondition
  apply propext
  apply forall_congr'
  intro i
  have hz : ((∏ j, m j : ℕ) : ZMod (m i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  simp only [Nat.cast_add, hz, add_zero]

/-- CRT makes the number of simultaneously allowed residues exactly multiplicative. -/
theorem residueCondition_count_period {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i)))
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => (m i).Coprime (m j))) :
    @Nat.count (residueCondition m A) (Classical.decPred _) (∏ i, m i) =
      ∏ i, (A i).card := by
  classical
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  let : NeZero M := ⟨ne_of_gt hM⟩
  let : Fintype {n : ℕ // n < M ∧ residueCondition m A n} :=
    Fintype.ofFinset ((Finset.range M).filter (residueCondition m A)) (by
      intro n
      simp only [Finset.mem_filter, Finset.mem_range]
      rfl)
  let f (r : ZMod M) (i : ι) : ZMod (m i) :=
    ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r
  let e₁ : {n : ℕ // n < M ∧ residueCondition m A n} ≃
      {r : ZMod M // ∀ i, f r i ∈ A i} := {
    toFun := fun n => ⟨n.val, by
      intro i
      change ZMod.castHom _ _ (n.val : ZMod M) ∈ A i
      rw [map_natCast]
      exact n.property.2 i⟩
    invFun := fun r => ⟨r.val.val, ZMod.val_lt r.val, by
      have hcast : (r.val.val : ZMod M) = r.val := ZMod.natCast_zmod_val r.val
      have hh : ∀ i, f (r.val.val : ZMod M) i ∈ A i := by
        rw [hcast]
        exact r.property
      intro i
      have hh' := hh i
      change ZMod.castHom _ _ (r.val.val : ZMod M) ∈ A i at hh'
      rwa [map_natCast] at hh'⟩
    left_inv := fun n => Subtype.ext (ZMod.val_natCast_of_lt n.property.1)
    right_inv := fun r => Subtype.ext (ZMod.natCast_zmod_val r.val)
  }
  let e₂ : {r : ZMod M // ∀ i, f r i ∈ A i} ≃
      {r : ∀ i, ZMod (m i) // ∀ i, r i ∈ A i} :=
    (ZMod.prodEquivPi m hc).toEquiv.subtypeEquiv (by
      intro r
      change (∀ i, f r i ∈ A i) ↔ ∀ i, ZMod.prodEquivPi m hc r i ∈ A i
      simp only [ZMod.prodEquivPi_apply]
      rfl)
  rw [Nat.count_eq_card_fintype]
  calc
    _ = Fintype.card (∀ i, {r : ZMod (m i) // r ∈ A i}) :=
      Fintype.card_congr ((e₁.trans e₂).trans Equiv.subtypePiEquivPi)
    _ = ∏ i, (A i).card := by simp

theorem residueCondition_interval_error {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i)))
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (S N : ℕ) :
    |(@Nat.count (fun j => residueCondition m A (S + j)) (Classical.decPred _) N : ℝ) -
      (N : ℝ) / (∏ i, m i : ℕ) * (∏ i, (A i).card : ℕ)| ≤
      (∏ i, (A i).card : ℕ) := by
  classical
  let M := ∏ i, m i
  let ρ := ∏ i, (A i).card
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  have hi := periodic_interval_count_scaled_error (residueCondition m A) M S N hM
    (residueCondition_periodic m A)
  rw [residueCondition_count_period m A hm hc] at hi
  have hr : |(M : ℝ) * Nat.count (fun j => residueCondition m A (S + j)) N -
      (N : ℝ) * ρ| ≤ (M : ℝ) * ρ := by exact_mod_cast hi
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : (M : ℝ) * ((N : ℝ) / M * ρ) = (N : ℝ) * ρ := by
    field_simp
  rw [abs_le] at hr ⊢
  constructor <;> nlinarith

end Erdos676
