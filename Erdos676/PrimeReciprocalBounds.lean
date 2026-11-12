import Erdos676.PrimeBlocks

open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem prime_family_reciprocal_band_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (y z : ℝ) (hyz : y ≤ z) (hlo : ∀ p, y < a p) (hhi : ∀ p, (a p : ℝ) ≤ z) :
    (∑ p : P, 1 / (a p : ℝ)) ≤ primeReciprocalSum z - primeReciprocalSum y := by
  have hsub : Finset.univ.image a ⊆ primesUpToReal z \ primesUpToReal y := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_primesUpToReal z (a p)).mpr ⟨hprime p, hhi p⟩, ?_⟩
    intro hmem
    exact (not_le_of_gt (hlo p)) ((mem_primesUpToReal y (a p)).mp hmem).2
  have himage : (∑ p : P, 1 / (a p : ℝ)) = ∑ q ∈ Finset.univ.image a, 1 / (q : ℝ) := by
    symm
    apply Finset.sum_image
    intro p hp q hq h
    exact hinj h
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p hp hnot => by positivity : ∀ p, p ∈ primesUpToReal z \ primesUpToReal y →
      p ∉ Finset.univ.image a → 0 ≤ 1 / (p : ℝ))
  have hsplit := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) (primesUpToReal_subset hyz)
  rw [himage]
  change (∑ q ∈ primesUpToReal z \ primesUpToReal y, 1 / (q : ℝ)) + primeReciprocalSum y =
    primeReciprocalSum z at hsplit
  linarith

universe u

theorem exists_prime_band_reciprocal_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (p : P → ℕ),
        Function.Injective p → (∀ i, (p i).Prime) → (∀ i, X ^ a ≤ (p i : ℝ)) →
        (∀ i, (p i : ℝ) ≤ X ^ b) → (∑ i : P, 1 / (p i : ℝ)) ≤ C := by
  let limit := Real.log b - Real.log (a / 2)
  have hb : 0 < b := ha.trans_le hab
  have hlimit := prime_power_band_limit (a / 2) b (by positivity) hb
  have hnear : ∀ᶠ X : ℝ in atTop, primeReciprocalSum (X ^ b) - primeReciprocalSum (X ^ (a / 2)) < limit + 1 :=
    (tendsto_order.mp hlimit).2 _ (by dsimp [limit]; linarith)
  refine ⟨|limit| + 2, by positivity, ?_⟩
  filter_upwards [hnear, eventually_gt_atTop (1 : ℝ)] with X hX hx
  intro P instF instD p hinj hprime hlo hhi
  have hstrict : X ^ (a / 2) < X ^ a := Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)
  have horder : X ^ (a / 2) ≤ X ^ b := hstrict.le.trans (Real.rpow_le_rpow_of_exponent_le hx.le hab)
  have h := prime_family_reciprocal_band_le p hinj hprime _ _ horder
    (fun i => hstrict.trans_le (hlo i)) hhi
  linarith [le_abs_self limit]

end Erdos676
