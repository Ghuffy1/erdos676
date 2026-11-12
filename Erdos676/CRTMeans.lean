import Erdos676.LocalResidues
import Erdos676.PeriodicSums
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Erdos676

theorem sum_range_zmod (m : ℕ) [NeZero m] (f : ZMod m → ℝ) :
    (∑ n ∈ Finset.range m, f (n : ZMod m)) = ∑ r : ZMod m, f r := by
  have he (i : Fin m) : ZMod.finEquiv m i = (i.val : ZMod m) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt i.isLt]
    cases m with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ m => rfl
  rw [Finset.sum_range]
  have h := Equiv.sum_comp (ZMod.finEquiv m).toEquiv f
  change (∑ i : Fin m, f (ZMod.finEquiv m i)) = _ at h
  simpa only [he] using h

theorem crt_sum_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ r : ZMod (∏ i, m i), ∏ i,
      f i (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r)) =
      ∏ i, ∑ r : ZMod (m i), f i r := by
  calc
    _ = ∑ r : ∀ i, ZMod (m i), ∏ i, f i (r i) := by
      have h := Equiv.sum_comp (ZMod.prodEquivPi m hc).toEquiv (fun r => ∏ i, f i (r i))
      change (∑ r : ZMod (∏ i, m i), ∏ i, f i (ZMod.prodEquivPi m hc r i)) = _ at h
      simpa only [ZMod.prodEquivPi_apply] using h
    _ = _ := (Fintype.prod_sum f).symm

theorem crt_product_mean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ)
    (hf : ∀ i, (∑ r : ZMod (m i), f i r) = m i) :
    (∑ r : ZMod (∏ i, m i), ∏ i,
      f i (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r)) =
      (∏ i, m i : ℕ) := by
  rw [crt_sum_product m hc f]
  simp only [hf, Nat.cast_prod]

theorem crt_natural_sum_mean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ)
    (hf : ∀ i, (∑ r : ZMod (m i), f i r) = m i) :
    (∑ n ∈ Finset.range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) =
      (∏ i, m i : ℕ) := by
  have h := sum_range_zmod (∏ i, m i)
    (fun r => ∏ i, f i (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r))
  simp only [map_natCast] at h
  rw [h]
  exact crt_product_mean_one m hc f hf

theorem crt_product_periodic {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (f : ∀ i, ZMod (m i) → ℝ) :
    Function.Periodic (fun n : ℕ => ∏ i, f i (n : ZMod (m i))) (∏ i, m i) := by
  intro n
  apply Finset.prod_congr rfl
  intro i _
  have hz : ((∏ j, m j : ℕ) : ZMod (m i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  rw [Nat.cast_add, hz, add_zero]

theorem crt_double_average_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ)
    (hf : ∀ i, (∑ r : ZMod (m i), f i r) = m i)
    (hf0 : ∀ i r, 0 ≤ f i r) (H : ℕ) (hH : 0 < H) (shift : ℕ → ℕ) :
    (∑ j ∈ Finset.range H, ∑ n ∈ Finset.range H,
      ∏ i, f i ((shift j + n : ℕ) : ZMod (m i))) / (H : ℝ) ^ 2 ≤
      1 + (∏ i, m i : ℕ) / (H : ℝ) := by
  exact periodic_double_average_upper (fun n => ∏ i, f i (n : ZMod (m i)))
    (∏ i, m i) H shift (Nat.pos_of_ne_zero (NeZero.ne _)) hH
    (crt_product_periodic m f) (fun _ => Finset.prod_nonneg (fun i _ => hf0 i _))
    (crt_natural_sum_mean_one m hc f hf)

end Erdos676
