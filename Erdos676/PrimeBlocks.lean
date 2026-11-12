import Erdos676.PrimeBands

open scoped BigOperators Topology
open Filter

namespace Erdos676

theorem mem_primesUpToReal (x : ℝ) (p : ℕ) :
    p ∈ primesUpToReal x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  constructor
  · intro hp
    obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
    refine ⟨hprime, ?_⟩
    exact (Nat.le_floor_iff' hprime.ne_zero).mp (Finset.mem_Ioc.mp hinterval).2
  · rintro ⟨hprime, hx⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hprime.pos, Nat.le_floor hx⟩, hprime⟩

theorem primesUpToReal_subset {x y : ℝ} (hxy : x ≤ y) : primesUpToReal x ⊆ primesUpToReal y := by
  intro p hp
  obtain ⟨hprime, hpx⟩ := (mem_primesUpToReal x p).mp hp
  exact (mem_primesUpToReal y p).mpr ⟨hprime, hpx.trans hxy⟩

theorem primeReciprocalSum_nonneg (x : ℝ) : 0 ≤ primeReciprocalSum x :=
  Finset.sum_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))

theorem primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro x y hxy
  exact Finset.sum_le_sum_of_subset_of_nonneg (primesUpToReal_subset hxy)
    (fun p _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))

theorem exists_half_power_prime_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C := by
  have hlimit := prime_power_band_limit (1 / 2 : ℝ) 1 (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hlimit
  let limit := Real.log 1 - Real.log (1 / 2 : ℝ)
  have hevent : ∀ᶠ x : ℝ in atTop,
      primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) < limit + 1 :=
    (tendsto_order.mp hlimit).2 _ (by dsimp [limit]; linarith)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hevent
  let T := max 2 X₀
  let C := 1 + |primeReciprocalSum T| + |limit|
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x
  by_cases hTx : T ≤ x
  · have h := hX₀ x ((le_max_right 2 X₀).trans hTx)
    have hlim := le_abs_self limit
    have hmass := abs_nonneg (primeReciprocalSum T)
    dsimp [C]
    linarith
  · have hxT : x ≤ T := (lt_of_not_ge hTx).le
    have hmono := primeReciprocalSum_mono hxT
    have hnonneg := primeReciprocalSum_nonneg (x ^ (1 / 2 : ℝ))
    have habs := le_abs_self (primeReciprocalSum T)
    have hlim := abs_nonneg limit
    dsimp [C]
    linarith

theorem prime_interval_mass_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {x y : ℝ} (hyx : y ≤ x) (hmin : ∀ p, y < (a p : ℝ)) (hmax : ∀ p, (a p : ℝ) ≤ x) :
    (∑ p : P, (1 : ℝ) / a p) ≤ primeReciprocalSum x - primeReciprocalSum y := by
  have himage : Finset.univ.image a ⊆ primesUpToReal x \ primesUpToReal y := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_primesUpToReal x (a p)).mpr ⟨hprime p, hmax p⟩, ?_⟩
    intro hbad
    have hle := ((mem_primesUpToReal y (a p)).mp hbad).2
    exact (not_le_of_gt (hmin p)) hle
  have hsum : (∑ p : P, (1 : ℝ) / a p) =
      ∑ q ∈ Finset.univ.image a, (1 : ℝ) / q := by
    symm
    rw [Finset.sum_image]
    intro p hp q hq h
    exact hinj h
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg himage
    (fun p _ _ => div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg p))
  have hsplit : (∑ p ∈ primesUpToReal x \ primesUpToReal y, (1 : ℝ) / p) +
      primeReciprocalSum y = primeReciprocalSum x :=
    Finset.sum_sdiff (primesUpToReal_subset hyx)
  rw [hsum]
  linarith

end Erdos676
