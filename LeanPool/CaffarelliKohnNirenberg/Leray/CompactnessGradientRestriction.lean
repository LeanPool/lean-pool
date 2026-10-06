/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientFiber
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Compactness Gradient Restriction

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace CKN.Leray

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Pairing with a test extended by zero identifies the full-space and
restricted L² Hilbert pairings. -/
theorem inner_indicator_eq_restricted_inner
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (S : Set α) (hS : MeasurableSet S)
    (f : α → E) (hf : MemLp f 2 μ)
    (w : Lp E 2 (μ.restrict S)) :
    inner ℝ (hf.toLp f)
      (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp w)).toLp
        (S.indicator (fun x => w x))) =
      inner ℝ ((hf.restrict S).toLp f) w := by
  let ψ : α → E := S.indicator (fun x => w x)
  let hψ : MemLp ψ 2 μ :=
    (memLp_indicator_iff_restrict hS).mpr (Lp.memLp w)
  let ψLp : Lp E 2 μ := hψ.toLp ψ
  have hleft : inner ℝ (hf.toLp f) ψLp =
      ∫ x in S, inner ℝ (f x) (w x) ∂μ := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℝ ((hf.toLp f) x) (ψLp x) ∂μ) =
          ∫ x, S.indicator (fun y => inner ℝ (f y) (w y)) x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp, hψ.coeFn_toLp] with x hfx hψx
        rw [hfx, hψx]
        by_cases hx : x ∈ S <;> simp [ψ, Set.indicator, hx]
      _ = _ := integral_indicator hS
  have hright : inner ℝ ((hf.restrict S).toLp f) w =
      ∫ x in S, inner ℝ (f x) (w x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hf.restrict S).coeFn_toLp] with x hfx
    rw [hfx]
  simpa only [ψ, hψ, ψLp] using hleft.trans hright.symm

/-- Weak L² convergence passes from a measure to its restriction to a
measurable set. -/
theorem weak_l2_restrict_of_weak_l2
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (S : Set α) (hS : MeasurableSet S)
    (f : ℕ → α → E) (g : Lp E 2 μ)
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hweak : ∀ v, Tendsto
      (fun k => inner ℝ ((hf k).toLp (f k)) v) atTop
      (nhds (inner ℝ g v))) :
    ∀ w : Lp E 2 (μ.restrict S), Tendsto
      (fun k => inner ℝ (((hf k).restrict S).toLp (f k)) w) atTop
      (nhds (inner ℝ (((Lp.memLp g).restrict S).toLp
        (fun x => g x)) w)) := by
  intro w
  let ψ : α → E := S.indicator (fun x => w x)
  let hψ : MemLp ψ 2 μ :=
    (memLp_indicator_iff_restrict hS).mpr (Lp.memLp w)
  let ψLp : Lp E 2 μ := hψ.toLp ψ
  have h := hweak ψLp
  have hn (k : ℕ) :
      inner ℝ ((hf k).toLp (f k)) ψLp =
        inner ℝ (((hf k).restrict S).toLp (f k)) w :=
    inner_indicator_eq_restricted_inner S hS (f k) (hf k) w
  have hg : inner ℝ g ψLp =
      inner ℝ (((Lp.memLp g).restrict S).toLp (fun x => g x)) w := by
    simpa only [Lp.toLp_coeFn g (Lp.memLp g)] using
      inner_indicator_eq_restricted_inner S hS
        (fun x => g x) (Lp.memLp g) w
  simpa only [hn, hg] using h

/-- Weak `L²` convergence is unchanged when two measures are equal. -/
theorem weak_l2_of_measure_eq
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure α} (hμ : μ = ν)
    (f : ℕ → α → E) (g : α → E)
    (hfμ : ∀ k, MemLp (f k) 2 μ) (hgμ : MemLp g 2 μ)
    (hfν : ∀ k, MemLp (f k) 2 ν) (hgν : MemLp g 2 ν)
    (hweak : ∀ w : Lp E 2 μ,
      Tendsto (fun k => inner ℝ ((hfμ k).toLp (f k)) w) atTop
        (nhds (inner ℝ (hgμ.toLp g) w))) :
    ∀ w : Lp E 2 ν,
      Tendsto (fun k => inner ℝ ((hfν k).toLp (f k)) w) atTop
        (nhds (inner ℝ (hgν.toLp g) w)) := by
  subst ν
  exact hweak

end CKN.Leray
