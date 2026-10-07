/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences

/-!
# Subsequence Dichotomy

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

noncomputable section

namespace CIV

/-- Step 1 of the proof of `prop:aniso:small`: every real sequence `a` admits a strictly
increasing subsequence `a ∘ φ` along which either the values stay bounded above, or the
values tend to `+∞`. Applied to the ratio `r_n / λ_n`, this splits the analysis of
`prop:aniso:small` into the case where the ratio stays bounded and the case where it
escapes to infinity along a subsequence. -/
theorem exists_subseq_bounded_or_tendsto_atTop (a : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ A : ℝ, ∀ n, a (φ n) ≤ A) ∨ Filter.Tendsto (fun n => a (φ n)) Filter.atTop
        Filter.atTop) := by
  by_cases hb : ∃ A : ℝ, ∀ n, a n ≤ A
  · exact ⟨id, strictMono_id, Or.inl hb⟩
  · have h_unbdd : ∀ A : ℝ, ∃ n : ℕ, A < a n := by
      intro A
      by_contra h
      push Not at h
      exact hb ⟨A, h⟩
    -- A strengthened unboundedness statement: for every bound `A` and every index `N`,
    -- some index beyond `N` has value beyond `A`. Proved by induction on `N`, never using
    -- a maximum over a finite set (only the binary `max` of two reals).
    have h_strong : ∀ (N : ℕ) (A : ℝ), ∃ n : ℕ, N < n ∧ A < a n := by
      intro N
      induction N with
      | zero =>
        intro A
        obtain ⟨n, hn⟩ := h_unbdd (max A (a 0))
        have hA : A < a n := lt_of_le_of_lt (le_max_left A (a 0)) hn
        have ha0 : a 0 < a n := lt_of_le_of_lt (le_max_right A (a 0)) hn
        have hn0 : n ≠ 0 := by
          intro h0
          rw [h0] at ha0
          exact lt_irrefl (a 0) ha0
        refine ⟨n, ?_, hA⟩
        omega
      | succ N ih =>
        intro A
        obtain ⟨n, hgtN, hn⟩ := ih (max A (a (N + 1)))
        have hA : A < a n := lt_of_le_of_lt (le_max_left A (a (N + 1))) hn
        have haN1 : a (N + 1) < a n := lt_of_le_of_lt (le_max_right A (a (N + 1))) hn
        have hne : n ≠ N + 1 := by
          intro h_eq
          rw [h_eq] at haN1
          exact lt_irrefl (a (N + 1)) haN1
        refine ⟨n, ?_, hA⟩
        omega
    -- Build the subsequence by recursion: `φ (k + 1)` is chosen simultaneously beyond
    -- `φ k` and with value beyond both `a (φ k)` and `k + 1`.
    obtain ⟨φ, hφ0, hφsucc⟩ :
        ∃ φ : ℕ → ℕ, φ 0 = Classical.choose (h_strong 0 0) ∧
          ∀ k, φ (k + 1) = Classical.choose (h_strong (φ k) (max (a (φ k)) ((k : ℝ) + 1))) :=
      ⟨fun n => Nat.rec (Classical.choose (h_strong 0 0))
          (fun k ih => Classical.choose (h_strong ih (max (a ih) ((k : ℝ) + 1)))) n,
        rfl, fun _ => rfl⟩
    have hφ_lt : ∀ k, φ k < φ (k + 1) := by
      intro k
      rw [hφsucc k]
      exact (Classical.choose_spec (h_strong (φ k) (max (a (φ k)) ((k : ℝ) + 1)))).1
    have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ hφ_lt
    have hφ_val : ∀ k : ℕ, (k : ℝ) < a (φ k) := by
      intro k
      match k with
      | 0 =>
        rw [hφ0]
        exact_mod_cast (Classical.choose_spec (h_strong 0 0)).2
      | m + 1 =>
        rw [hφsucc m]
        have hspec := (Classical.choose_spec (h_strong (φ m) (max (a (φ m)) ((m : ℝ) + 1)))).2
        have hlt : (m : ℝ) + 1 <
            a (Classical.choose (h_strong (φ m) (max (a (φ m)) ((m : ℝ) + 1)))) :=
          lt_of_le_of_lt (le_max_right (a (φ m)) ((m : ℝ) + 1)) hspec
        exact_mod_cast hlt
    refine ⟨φ, hφ_mono, Or.inr ?_⟩
    exact Filter.tendsto_atTop_mono (fun k => (hφ_val k).le) tendsto_natCast_atTop_atTop

/-- Step 1 continued, the bounded branch: a nonnegative sequence bounded above by some `A`
admits a strictly increasing subsequence converging to a limit `L ≥ 0`. Applied to the ratio
`r_n / λ_n` in the bounded branch of `exists_subseq_bounded_or_tendsto_atTop`, this produces
the finite limit ratio used in `prop:aniso:small`. -/
theorem exists_subseq_tendsto_of_bddAbove (a : ℕ → ℝ) (h0 : ∀ n, 0 ≤ a n) (hA : ∃ A, ∀ n, a n ≤ A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ℝ, 0 ≤ L ∧
      Filter.Tendsto (fun n => a (φ n)) Filter.atTop (nhds L) := by
  obtain ⟨A, hA⟩ := hA
  have h_mem : ∀ n, a n ∈ Set.Icc (0 : ℝ) A := fun n => ⟨h0 n, hA n⟩
  obtain ⟨L, hL_mem, φ, hφ_mono, hφ_tendsto⟩ := isCompact_Icc.tendsto_subseq h_mem
  exact ⟨φ, hφ_mono, L, hL_mem.1, hφ_tendsto⟩

end CIV
