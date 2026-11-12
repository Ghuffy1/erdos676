import Erdos676.SingularFiniteMeans
import Erdos676.PrimeBlocks

open Filter Asymptotics
open scoped Topology BigOperators

namespace Erdos676

theorem singularMajorant_primes (y : ℝ) :
    singularMajorant (primesUpToReal y) = (survivalProduct y)⁻¹ := by
  unfold singularMajorant survivalProduct
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast ((mem_primesUpToReal y p).mp hp).1.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem singularMajorant_band {y z : ℝ} (hyz : y ≤ z) :
    singularMajorant (primesUpToReal z \ primesUpToReal y) =
      survivalProduct y / survivalProduct z := by
  have h := Finset.prod_sdiff (f := fun p : ℕ => (p : ℝ) / (p - 1))
    (primesUpToReal_subset hyz)
  change singularMajorant (primesUpToReal z \ primesUpToReal y) *
    singularMajorant (primesUpToReal y) = singularMajorant (primesUpToReal z) at h
  rw [singularMajorant_primes, singularMajorant_primes] at h
  have hy := (survivalProduct_pos y).ne'
  have hz := (survivalProduct_pos z).ne'
  field_simp at h ⊢
  nlinarith

theorem survival_ratio_formula {y z : ℝ} (hy : 1 < y) (hz : 1 < z) :
    survivalProduct y / survivalProduct z =
      Real.exp (Mertens.E₃ y - Mertens.E₃ z) * (Real.log z / Real.log y) := by
  rw [survivalProduct_formula hy, survivalProduct_formula hz, Real.exp_sub]
  have hylog := (Real.log_pos hy).ne'
  have hzlog := (Real.log_pos hz).ne'
  have he := Real.exp_ne_zero (-Real.eulerMascheroniConstant)
  have hez := Real.exp_ne_zero (Mertens.E₃ z)
  field_simp

theorem survival_ratio_limit {f g : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop)
    (hlog : Tendsto (fun x => Real.log (g x) / Real.log (f x)) atTop (nhds L)) :
    Tendsto (fun x => survivalProduct (f x) / survivalProduct (g x)) atTop (nhds L) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hexp : Tendsto (fun x => Real.exp (Mertens.E₃ (f x) - Mertens.E₃ (g x)))
      atTop (nhds (1 : ℝ)) := by
    simpa only [sub_self, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp ((hE.comp hf).sub (hE.comp hg))
  have hprod := hexp.mul hlog
  simp only [one_mul] at hprod
  apply Filter.Tendsto.congr' _ hprod
  filter_upwards [hf.eventually (eventually_gt_atTop (1 : ℝ)),
    hg.eventually (eventually_gt_atTop (1 : ℝ))] with x hfx hgx
  exact (survival_ratio_formula hfx hgx).symm

end Erdos676
