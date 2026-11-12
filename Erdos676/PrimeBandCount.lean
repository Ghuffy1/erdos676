import Erdos676.GrowingFourier
import Erdos676.RealBoxSmoothing

open scoped BigOperators

namespace Erdos676

noncomputable def primeBandCount {P : Type*} [Fintype P] (a : P → ℕ) (n : ℤ) : ℝ := by
  classical
  exact ∑ p : P, if (n : ZMod ((a p) ^ 2)) ∈ smallResidues (a p) then 1 else 0

theorem primeBandCount_nonneg {P : Type*} [Fintype P] (a : P → ℕ) (n : ℤ) :
    0 ≤ primeBandCount a n := by
  classical
  unfold primeBandCount
  exact Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)

theorem coe_primeBandCount {P : Type*} [Fintype P] (a : P → ℕ) [∀ p, NeZero (a p)] (n : ℤ) :
    (primeBandCount a n : ℂ) = primeBandSignal a n := by
  classical
  unfold primeBandCount primeBandSignal
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with h <;> simp [residueIndicator, h]

theorem primeBandCount_energy_identity {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (H J : ℕ) (n : ℤ) :
    (realBoxSmooth H J (primeBandCount a) n - (∑ p : P, 1 / (a p : ℝ))) ^ 2 =
      ‖boxSmooth H J (primeBandSignal a) n - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2 := by
  have hfun : (fun k => (primeBandCount a k : ℂ)) = primeBandSignal a := funext (coe_primeBandCount a)
  have hcoe : ((realBoxSmooth H J (primeBandCount a) n - (∑ p : P, 1 / (a p : ℝ)) : ℝ) : ℂ) =
      boxSmooth H J (primeBandSignal a) n - (∑ p : P, 1 / (a p : ℂ)) := by
    rw [Complex.ofReal_sub, coe_realBoxSmooth, hfun]
    simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [← hcoe, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Erdos676
