import Erdos676.ComplexGram
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Erdos676

theorem sampling_gram_bound {P T : Type*} [Fintype T]
    (s : Finset P) (f : P → T → ℂ) (c : P → ℂ) (C : ℝ)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, ‖∑ t : T, star (f i t) * f j t‖) ≤ C) :
    (∑ t : T, ‖∑ i ∈ s, c i * f i t‖ ^ 2) ≤ C * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let v (i : P) : EuclideanSpace ℂ T := WithLp.toLp 2 (f i)
  have hinner (i j : P) : ⟪v i, v j⟫_ℂ = ∑ t : T, star (f i t) * f j t := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro t ht
    change f j t * star (f i t) = star (f i t) * f j t
    exact mul_comm _ _
  have h := complex_gram_row_bound s v c C (by simpa only [hinner] using hrow)
  rw [EuclideanSpace.norm_sq_eq] at h
  have heval (t : T) : (∑ i ∈ s, c i • v i) t = ∑ i ∈ s, c i * f i t := by
    have hmap := map_sum (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : T => ℂ) 2 t)
      (fun i => c i • v i) s
    simpa only [PiLp.projₗ_apply, PiLp.smul_apply, v, PiLp.toLp_apply, smul_eq_mul] using hmap
  simpa only [heval] using h

end Erdos676
