import Erdos676.MertensInputs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem primeReciprocalSum_eq (x : ℝ) :
    primeReciprocalSum x = Real.log (Real.log x) + Mertens.M + Mertens.E₂p x := by
  exact Mertens.sum_prime_div_eq x

/-- Reciprocal prime mass between two fixed positive powers of X. -/
theorem prime_power_band_limit (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun X : ℝ => primeReciprocalSum (X ^ b) - primeReciprocalSum (X ^ a))
      atTop (nhds (Real.log b - Real.log a)) := by
  have herror : Tendsto Mertens.E₂p atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have hea := herror.comp (tendsto_rpow_atTop ha)
  have heb := herror.comp (tendsto_rpow_atTop hb)
  have hlimit : Tendsto
      (fun X : ℝ => Real.log b - Real.log a + (Mertens.E₂p (X ^ b) - Mertens.E₂p (X ^ a)))
      atTop (nhds (Real.log b - Real.log a)) := by
    simpa using tendsto_const_nhds.add (heb.sub hea)
  refine Filter.Tendsto.congr' ?_ hlimit
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [primeReciprocalSum_eq, primeReciprocalSum_eq,
    Real.log_rpow hX0 b, Real.log_rpow hX0 a,
    Real.log_mul (ne_of_gt hb) (ne_of_gt hlog),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hlog)]
  ring

end Erdos676
