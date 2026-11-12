import Erdos676.CRTMeans

open scoped BigOperators

namespace Erdos676

theorem periodic_sum_upper_mean (f : ℕ → ℝ) (m H : ℕ) (μ : ℝ)
    (hm : 0 < m) (hf : Function.Periodic f m) (hf0 : ∀ i, 0 ≤ f i)
    (hmean : (∑ i ∈ Finset.range m, f i) ≤ (m : ℝ) * μ) :
    (∑ i ∈ Finset.range H, f i) ≤ ((H : ℝ) + m) * μ := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (abs_le.mp (periodic_sum_error f m H hm hf hf0)).2
  have hfactor : 0 ≤ (H : ℝ) / m + 1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmean hfactor
  have hid : ((H : ℝ) / m + 1) * ((m : ℝ) * μ) = ((H : ℝ) + m) * μ := by
    field_simp
  rw [hid] at hscaled
  nlinarith

theorem zmod_double_average_upper (m H : ℕ) [NeZero m]
    (f : ZMod m → ℝ) (μ : ℝ) (hH : 0 < H) (hf0 : ∀ r, 0 ≤ f r)
    (hmean : (∑ r : ZMod m, f r) ≤ (m : ℝ) * μ) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      f ((i : ZMod m) - (j : ZMod m))) / (H : ℝ) ^ 2 ≤
        (1 + (m : ℝ) / H) * μ := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne _)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hinner (j : ℕ) : (∑ i ∈ Finset.range H, f ((i : ZMod m) - (j : ZMod m))) ≤
      ((H : ℝ) + m) * μ := by
    have hp : Function.Periodic (fun i : ℕ => f ((i : ZMod m) - (j : ZMod m))) m := by
      intro i
      simp
    have hsum : (∑ i ∈ Finset.range m, f ((i : ZMod m) - (j : ZMod m))) = ∑ r : ZMod m, f r := by
      rw [sum_range_zmod m (fun r => f (r - (j : ZMod m)))]
      have h := Equiv.sum_comp (Equiv.addRight (-(j : ZMod m))) f
      change (∑ r : ZMod m, f (r + -(j : ZMod m))) = _ at h
      simpa only [sub_eq_add_neg] using h
    apply periodic_sum_upper_mean _ m H μ hm hp (fun i => hf0 _)
    rwa [hsum]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range H) => hinner j)
  have hsum' : (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      f ((i : ZMod m) - (j : ZMod m))) ≤ (H : ℝ) * (((H : ℝ) + m) * μ) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply (div_le_iff₀ (sq_pos_of_pos hHreal)).mpr
  have hid : ((1 + (m : ℝ) / H) * μ) * (H : ℝ) ^ 2 =
      (H : ℝ) * (((H : ℝ) + m) * μ) := by
    field_simp
  rwa [hid]

theorem crt_pair_average_upper {J : Type*} [Fintype J] [DecidableEq J]
    (m : J → ℕ) [∀ j, NeZero (m j)] [NeZero (∏ j, m j)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ j, ZMod (m j) → ℝ) (μ : J → ℝ)
    (hf0 : ∀ j r, 0 ≤ f j r)
    (hmean : ∀ j, (∑ r : ZMod (m j), f j r) ≤ (m j : ℝ) * μ j)
    (H : ℕ) (hH : 0 < H) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      ∏ t : J, f t ((i : ZMod (m t)) - (j : ZMod (m t)))) / (H : ℝ) ^ 2 ≤
        (1 + (∏ t, m t : ℕ) / (H : ℝ)) * (∏ t : J, μ t) := by
  let F (r : ZMod (∏ t, m t)) :=
    ∏ t : J, f t (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ t)) _ r)
  have hF0 : ∀ r, 0 ≤ F r := fun r => Finset.prod_nonneg (fun t _ => hf0 t _)
  have hFmean : (∑ r : ZMod (∏ t, m t), F r) ≤ (∏ t, m t : ℕ) * (∏ t : J, μ t) := by
    rw [crt_sum_product m hc f]
    calc
      _ ≤ ∏ t : J, (m t : ℝ) * μ t :=
        Finset.prod_le_prod₀ (fun t _ => Finset.sum_nonneg (fun r _ => hf0 t r)) (fun t _ => hmean t)
      _ = _ := by rw [Finset.prod_mul_distrib, Nat.cast_prod]
  have h := zmod_double_average_upper (∏ t, m t) H F (∏ t : J, μ t) hH hF0 hFmean
  simpa only [F, map_sub, map_natCast] using h

end Erdos676
