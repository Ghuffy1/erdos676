/-
The modular equivalence proof follows the public Formal Conjectures development,
Copyright 2026 The Formal Conjectures Authors, Apache License 2.0.
Source commit e754a78c74a3f2bbc38e4f2063b5f6eed51bde39.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice
import Lean.Elab.Tactic.Omega

/-!
The exact prime-only Erdős 676 statement and its negation.
All arguments in this file include the positive multiplier and the zero remainder.
-/

namespace Erdos676

def Representable (n : ℕ) : Prop :=
  ∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b

def Exceptional (n : ℕ) : Prop := ¬ Representable n

def EventualRepresentation : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, Representable n

def UnboundedExceptions : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Exceptional n

theorem representable_iff_mod (n : ℕ) :
    Representable n ↔ ∃ p : ℕ, p.Prime ∧ p ^ 2 ≤ n ∧ n % p ^ 2 < p := by
  constructor
  · rintro ⟨a, p, b, hp, ha, hb, rfl⟩
    refine ⟨p, hp, ?_, ?_⟩
    · nlinarith
    · have hb' : b < p ^ 2 := by
        have := hp.two_le
        nlinarith
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb'] using hb
  · rintro ⟨p, hp, hn, hr⟩
    refine ⟨n / p ^ 2, p, n % p ^ 2, hp, ?_, hr, ?_⟩
    · exact Nat.div_pos hn (pow_pos hp.pos _)
    · simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n (p ^ 2)).symm

theorem exceptional_iff_mod (n : ℕ) :
    Exceptional n ↔ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ≤ n % p ^ 2 := by
  simp only [Exceptional, representable_iff_mod, not_exists, not_and, not_lt]

theorem not_eventual_iff_unbounded :
    ¬ EventualRepresentation ↔ UnboundedExceptions := by
  simp only [EventualRepresentation, Filter.eventually_atTop, UnboundedExceptions,
    Exceptional, not_exists, not_forall, exists_prop]

theorem unbounded_iff_infinite :
    UnboundedExceptions ↔ Set.Infinite {n : ℕ | Exceptional n} := by
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n, hn, he⟩ := h (m + 1)
    exact ⟨n, he, by omega⟩
  · intro h N
    obtain ⟨n, hn, hnN⟩ := h.exists_gt N
    exact ⟨n, le_of_lt hnN, hn⟩

noncomputable def dyadicExceptions (X : ℕ) : Finset ℕ :=
  @Finset.filter ℕ Exceptional (Classical.decPred Exceptional) (Finset.Ioc X (2 * X))

theorem mem_dyadicExceptions (X n : ℕ) :
    n ∈ dyadicExceptions X ↔ X < n ∧ n ≤ 2 * X ∧ Exceptional n := by
  simp [dyadicExceptions, and_assoc]

theorem unbounded_of_eventually_dyadic_nonempty
    (h : ∀ᶠ X : ℕ in Filter.atTop, (dyadicExceptions X).Nonempty) :
    UnboundedExceptions := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h
  intro N
  obtain ⟨n, hn⟩ := hX₀ (max X₀ N) (le_max_left _ _)
  obtain ⟨hl, _, he⟩ := (mem_dyadicExceptions _ _).mp hn
  exact ⟨n, le_trans (le_max_right _ _) hl.le, he⟩

end Erdos676
