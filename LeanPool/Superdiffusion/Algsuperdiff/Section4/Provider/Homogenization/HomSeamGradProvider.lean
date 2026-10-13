/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomProviderBAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomProviderBSeamClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfBundle
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradSpine

/-!
# HomSeamGradProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The conditional provider, re-threaded: gradient binder, tail binder, `Creg` hoist

## What this file supplies

The §4.5 energy supply has four obstructions.  Three of them are ours;
this file gives them:

* **(α)** the display's classical-gradient binder is threaded all the way
  to the top, where the frozen ROOT's OWN binder re-supplies it — the
  provider introduced it as `_hgrad` and discarded it;
* **(β)** the a.e. finiteness of the minimal scale becomes an explicit binder of
  the supply and is DISCHARGED here from the Theorem-C tail
  (`ae_ne_top_of_regTail`);
* **(γ)** the Theorem-C constant `Creg` is hoisted above the `K_abs` pin, so
  `C_en⁰` — which is linear in `Creg` — may legally depend on it.

The source-facing hypothesis count is UNCHANGED: the threaded binder is the
frozen root's own, and the tail binder is discharged, not assumed.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The minimal-scale tail kills the value `⊤` -/

/-- **THE `X`-TAIL BINDER, DISCHARGED.**

`HomProviderBAssembly.exists_regularity_minimalScale` supplies, at every
admissible model, the Theorem-C tail bound

```text
  ∀ N, P[N ≤ X] ≤ C_st exp(-(1-α)²(N - C_st)/(C_st γ)).
```

Since `1 - α = s/2 > 0` and `C_st γ > 0` the right-hand side is a geometric
sequence with ratio `exp(-(1-α)²/(C_st γ)) < 1`, so it tends to `0` and the
event `{X = ⊤}`, which sits inside every `{N ≤ X}`, is null.  This is the
binder the per-`ω` energy slot needs: off it the enlarged `Y` degenerates to
`⊤` and the printed factor carries no information. -/
theorem ae_ne_top_of_regTail {d : ℕ} (M : ABKModel d) {Cst : ℝ} (hCst : 1 ≤ Cst)
    (hs : 0 < homS M) {X : Cutoff.CutoffSample d → ℕ∞}
    (htail : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
        ENNReal.ofReal (Cst *
          Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
            (Cst * M.gamma)))) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤ := by
  have hCst0 : (0 : ℝ) < Cst := lt_of_lt_of_le zero_lt_one hCst
  have hgpos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsplit : (1 : ℝ) - homAlpha M = homS M / 2 := by rw [homAlpha]; ring
  have ha : (0 : ℝ) < (1 - homAlpha M) ^ (2 : ℕ) := by
    rw [hsplit]; exact pow_pos (by linarith only [hs]) 2
  have hb : (0 : ℝ) < Cst * M.gamma := mul_pos hCst0 hgpos
  set a : ℝ := (1 - homAlpha M) ^ (2 : ℕ) with hadef
  set b : ℝ := Cst * M.gamma with hbdef
  set r : ℝ := Real.exp (-(a / b)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have hab : (0 : ℝ) < a / b := div_pos ha hb
    have hlt := Real.exp_lt_exp.mpr (show -(a / b) < (0 : ℝ) by linarith only [hab])
    rwa [Real.exp_zero] at hlt
  have hpow : ∀ N : ℕ, r ^ N = Real.exp (-(a / b) * (N : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, hrdef, ← Real.exp_add]
        congr 1
        push_cast
        ring
  have hrw : ∀ N : ℕ, Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b) =
      Cst * Real.exp (a * Cst / b) * r ^ N := by
    intro N
    have hstep : Cst * Real.exp (a * Cst / b) * r ^ N =
        Cst * (Real.exp (a * Cst / b) * Real.exp (-(a / b) * (N : ℝ))) := by
      rw [hpow N]; ring
    rw [hstep, ← Real.exp_add]
    have harg : a * Cst / b + -(a / b) * (N : ℝ) = -(a * ((N : ℝ) - Cst)) / b := by
      field_simp
      ring
    rw [harg]
  have hlim : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => Cst * Real.exp (a * Cst / b) * r ^ N)
        Filter.atTop (nhds (Cst * Real.exp (a * Cst / b) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _
    rw [mul_zero] at h0
    have hreal : Filter.Tendsto
        (fun N : ℕ => Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) Filter.atTop
        (nhds 0) := h0.congr fun N => (hrw N).symm
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa using! hcomp
  rw [MeasureTheory.ae_iff]
  have hsub : ∀ N : ℕ,
      {omega : Cutoff.CutoffSample d | ¬ X omega ≠ ⊤} ⊆
        {omega : Cutoff.CutoffSample d | (N : ℕ∞) ≤ X omega} := by
    intro N omega homega
    have htop : X omega = ⊤ := not_not.mp homega
    simp only [Set.mem_ofPred_eq, htop, le_top]
  have hle : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | ¬ X omega ≠ ⊤} ≤
        ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) :=
    fun N => le_trans (measure_mono (hsub N)) (htail N)
  exact le_antisymm (ge_of_tendsto' hlim hle) zero_le

end

end Algsuperdiff.Section4.Provider.Homogenization
