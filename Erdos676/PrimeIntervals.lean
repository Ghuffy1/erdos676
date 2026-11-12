import Erdos676.PrimeBlocks

open scoped BigOperators

namespace Erdos676

theorem prime_band_subset_Ioc {x y : ℝ} :
    primesUpToReal y \ primesUpToReal x ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
  intro p hp
  obtain ⟨hpy, hpx⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hprime, hpy⟩ := (mem_primesUpToReal y p).mp hpy
  have hpx' : x < (p : ℝ) := by
    by_contra h
    exact hpx ((mem_primesUpToReal x p).mpr ⟨hprime, le_of_not_gt h⟩)
  have hlower : ⌊x⌋₊ < p := Nat.lt_of_not_ge (fun h =>
    (not_le_of_gt hpx') ((Nat.le_floor_iff' hprime.ne_zero).mp h))
  exact Finset.mem_Ioc.mpr ⟨hlower, Nat.le_floor hpy⟩

theorem prime_band_card_le {x y : ℝ} :
    (primesUpToReal y \ primesUpToReal x).card ≤ ⌊y⌋₊ := by
  have h := Finset.card_le_card (prime_band_subset_Ioc (x := x) (y := y))
  rw [Nat.card_Ioc] at h
  omega

end Erdos676
