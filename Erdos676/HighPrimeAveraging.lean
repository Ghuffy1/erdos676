import Erdos676.BoundaryPowers
import Erdos676.PrimeReciprocalBounds
import Erdos676.PrimeBandCount

open Filter
open scoped BigOperators Topology

namespace Erdos676

universe u v

theorem high_prime_averaging {a b η c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 4) (hbη : b < η) (hηc : η < c) (hc : c ≤ 1 / 2) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (p : P → ℕ) [∀ i, NeZero (p i)],
        (∀ i, (p i).Prime) → Function.Injective p → (∀ i, (X : ℝ) ^ a ≤ p i) →
        (∀ i, (p i : ℝ) ≤ (X : ℝ) ^ b) →
      ∀ (Q : Type v) [Fintype Q] [DecidableEq Q] (q : Q → ℕ) [∀ i, NeZero (q i)],
        (∀ i, (q i).Prime) → Function.Injective q → (∀ i, (X : ℝ) ^ c ≤ q i) →
        (∀ i, (q i : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) →
        |(∑ n ∈ originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ)), primeBandCount p n) -
          (∑ i : P, 1 / (p i : ℝ)) * (originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ))).card| ≤
            K * (X : ℝ) ^ (1 - δ) := by
  let ε := (η - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hb0 : 0 < b := ha.trans_le hab
  have hη0 : 0 < η := hb0.trans hbη
  have hc0 : 0 < c := hη0.trans hηc
  have hrelation : η = b + 2 * ε := by dsimp [ε]; ring
  obtain ⟨J, henergy⟩ := growing_prime_band_energy hb0 hb hε hrelation
  obtain ⟨C, hC, hreciprocal⟩ := exists_prime_band_reciprocal_bound ha hab
  let δ := min (ε / 2) (c - η)
  let K := 200 + 13 * J * C
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, δ, hK, hδ, ?_⟩
  filter_upwards [henergy,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreciprocal,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (growing_fourier_cutoffs hε hη0 hrelation),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_box_radius_le (by linarith : η < 1) J),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually ((tendsto_rpow_atTop hc0).eventually_ge_atTop 4)]
    with X henergyX hrecX hcutX hradius hcX
  intro P instP instDP p instNP hp hinjp hlop hhip Q instQ instDQ q instNQ hq hinjq hloq hhiq
  obtain ⟨hx, hH, hhalf, hD, hsmall⟩ := hcutX
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans_le hx
  have hXnat : 0 < X := by exact_mod_cast hx0
  let H := powerFloor η X
  let R := J * H
  let m := ⌊(X : ℝ) ^ c / 2⌋₊
  let μ := ∑ i : P, 1 / (p i : ℝ)
  let E := 8200 * (X : ℝ) ^ (1 - ε)
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun i hi => by positivity)
  have hμC : μ ≤ C := hrecX P p hinjp hp hlop hhip
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hRreal : (R : ℝ) ≤ X := by simpa only [R, H, Nat.cast_mul] using hradius
  have hRnat : R ≤ X := by exact_mod_cast hRreal
  have hm1 : 1 ≤ m := Nat.le_floor (by norm_num only [Nat.cast_one]; linarith)
  have hm : 0 < m := by omega
  have hmlow : (m : ℝ) ≤ (X : ℝ) ^ c / 2 := Nat.floor_le (by positivity)
  have hmq (i : Q) : m < q i := by
    have hi := hloq i
    have hpow : 0 < (X : ℝ) ^ c := Real.rpow_pos_of_pos hx0 c
    exact_mod_cast (show (m : ℝ) < (q i : ℝ) by linarith)
  have henergy0 := henergyX P p hp hinjp hhip 0
  have hframe : Finset.Icc ((X : ℤ) + 1 - R) (2 * (X : ℤ)) ⊆
      Finset.Icc 0 ((4 * X : ℕ) - 1 : ℤ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have henergyAll : (∑ n ∈ Finset.Icc 0 ((4 * X : ℕ) - 1 : ℤ),
      (realBoxSmooth H J (primeBandCount p) n - μ) ^ 2) ≤ E := by
    rw [show ((4 * X : ℕ) - 1 : ℤ) = (0 : ℤ) + (4 * X : ℕ) - 1 by omega,
      sum_int_interval]
    dsimp only [μ]
    simp_rw [primeBandCount_energy_identity]
    simpa only [zero_add] using henergy0
  have henergyFrame := (Finset.sum_le_sum_of_subset_of_nonneg hframe
    (fun n hn hnot => sq_nonneg (realBoxSmooth H J (primeBandCount p) n - μ))).trans henergyAll
  have hend : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  have hcorr := avoidance_correlation_explicit q hq hinjq m hm hmq
    (2 * (X : ℝ) ^ (1 / 2 : ℝ)) (by positivity) hhiq ((X : ℤ) + 1) X H J hH
    (primeBandCount p) (primeBandCount_nonneg p) μ E hμ hE (by simpa only [hend] using henergyFrame)
  rw [hend] at hcorr
  have hsqrt := correlation_sqrt_power_bound hx0 hRreal (ε := ε)
  have hRupper : (R : ℝ) ≤ J * (X : ℝ) ^ η :=
    by simpa only [R, H, powerFloor, Nat.cast_mul] using
      (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hx0.le η)) (Nat.cast_nonneg J))
  have hboundary := boundary_error_power_bound hx hc hcX (Nat.cast_nonneg R) J hRupper
  have hboundary0 : 0 ≤ (R : ℝ) + 2 * R * ((X : ℝ) / m + 2 * (X : ℝ) ^ (1 / 2 : ℝ)) := by positivity
  have hμbound := mul_le_mul_of_nonneg_left hboundary hμ
  have hCbound := mul_le_mul_of_nonneg_right hμC (show 0 ≤ 13 * J * (X : ℝ) ^ (1 + η - c) by positivity)
  have hpow1 := Real.rpow_le_rpow_of_exponent_le hx (show 1 - ε / 2 ≤ 1 - δ by dsimp [δ]; have := min_le_left (ε / 2) (c - η); linarith)
  have hpow2 := Real.rpow_le_rpow_of_exponent_le hx (show 1 + η - c ≤ 1 - δ by dsimp [δ]; have := min_le_right (ε / 2) (c - η); linarith)
  have hp1 := mul_le_mul_of_nonneg_left hpow1 (by norm_num : (0 : ℝ) ≤ 200)
  have hp2 := mul_le_mul_of_nonneg_left hpow2 (show 0 ≤ 13 * J * C by positivity)
  change |(∑ n ∈ originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ)), primeBandCount p n) -
    μ * (originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ))).card| ≤ K * (X : ℝ) ^ (1 - δ)
  dsimp only [E] at hcorr
  dsimp only [R, H, m] at hsqrt hμbound
  simp only [Nat.cast_mul] at hcorr hsqrt hμbound
  dsimp only [K]
  nlinarith

end Erdos676
