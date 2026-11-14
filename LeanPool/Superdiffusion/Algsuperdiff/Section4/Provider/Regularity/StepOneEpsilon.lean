/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GoodEventCaps
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepOneParameters

/-!
# StepOneEpsilon

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 1: the annular-admissibility bullet and `ε_j(z)`

## The target

ABK26 `t.regularity` Step 1, (the first bullet's second half) (the definition
of `ε_j(z)` and its cap):

```
ε_j(z) := 𝓔_{s/8,∞,2}(z + □_j; a_L - (κ_L-κ_j)_{z+□_j}, σ̂_j) · 1_{𝒢(j,z; ⅛s, ⅛ s δ^{1/2})} ,
ε_j(z) ≤ C_{ann} s δ^{1/2} ≤ ½ s^{3/2} C_{edos}^{-1} 3^{-k/4} .
```

## The re-verification (binding)

The printed first bullet asks for `γ|log γ|² ≤ s c⋆² (⅛ s δ^{1/2})`; the frozen
producer is at the strengthened hypothesis `γ|log γ|² ≤ t^{3/2} c⋆² ε` with `t` the index
at which it is applied.  Step 1 applies it at `t = s/8` (that is the index
inside `𝒢(j,z; ⅛s, …)` and inside `ε_j(z)`) and at `ε = ⅛ s δ^{1/2}`, so the
honest requirement is

```
γ |log γ|²  ≤  (s/8)^{3/2} · c⋆² · (⅛ s δ^{1/2}) .
```

That requirement is carried here as a hypothesis of the cap, not discharged: it
is NOT a consequence of `γ ≤ γ₀` alone, because `δ` degenerates as `α → 1`, and
the lower bound on `δ` is the caller's own `α`-range hypothesis `α ≤ 1 - C(d,c⋆)
γ^{1/2}` (the S Step-1 bullet).

## Contents

* `stepOneEpsJ` — the definition of `ε_j(z)`, in the carriers the frozen
  producers use (`fluxCorrectedErrorObservableSup` at the `z`-translated sample,
  gated by `goodEventAt`, `ℝ≥0∞`-valued).
* `stepOneSEighth_mem_Icc` — the annular `s`-window at `γ ≤ 1/256`.
* `ae_stepOneEpsJ_le` — **the `ε_j(z)` cap**: `ε_j(z) ≤ C_ann · (⅛ s δ^{1/2})`
  almost surely, for every scale `j` and every centre `z`.

## Deviations from the printed text

1. **The `∞` slot.**  `ε_j(z)` is formed here with
   `Support.fluxCorrectedErrorObservableSup`, the supremum over the truncation
   levels `L ≥ j` of the flux-corrected `(∞,2)` representative — the object the
   frozen `p.minimal.scale.separation.sec4` and `p.mathcalE.annular.decomp`
   clauses both carry.  It dominates the printed per-`L` representative
   (`Support.le_fluxCorrectedErrorObservableSup`), so the cap proved here is
   stronger than the printed one at every fixed `L`.
2. **The centre.**  The frozen annular clause (ii) is stated at the centre `0`
   and the untranslated sample; the transport to `(z, z`-translated sample`)`
   is the proved law-preserving translation, not a new assumption.
3. **The cap's `ε` slot.**  The printed chain writes `ε_j(z) ≤ C_ann s δ^{1/2}`;
   the producer delivers `C_ann ε` at `ε = ⅛ s δ^{1/2}`, which is smaller.

## References

* ABK26, `t.regularity` Step 1.
* ABK26, `e.mathcalE.annular.decomp.good.event`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The annular window at the Step-1 index `s/8` -/

/-- The Step-1 index `s/8 = 1/32` lies in the annular producer's `s`-window `[8γ,
1/4]` as soon as `γ ≤ 1/256`. -/
theorem stepOneSEighth_mem_Icc {gamma : ℝ} (hgamma : gamma ≤ 1 / 256) :
    stepOneSEighth ∈ Set.Icc (8 * gamma) (1 / 4 : ℝ) := by
  rw [stepOneSEighth_eq]
  exact ⟨by linarith only [hgamma], by norm_num⟩

/-! ## 2. `ε_j(z)` -/

/-- **`ε_j(z)`**: the flux-corrected homogenization-error observable at the cube `z
+ □_j` and index `s/8`, restricted to the good event `𝒢(j, z; ⅛ s, ⅛ s
δ^{1/2})`.

The two ingredients are the frozen `d.good.event.for.lambda` carrier
`goodEventAt` and the `d.mathcal.E` carrier `fluxCorrectedErrorObservableSup`,
in exactly the pairing the frozen `p.minimal.scale.separation.sec4` clause uses
(event at the centre `z`, observable at the `z`-translated sample). -/
noncomputable def stepOneEpsJ (M : ABKModel d) (j : ℤ) (z : Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  Set.indicator
    (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) j z
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (stepOneEp delta))
    (fun omega' =>
      Support.fluxCorrectedErrorObservableSup M j ⟨stepOneSEighth, stepOneSEighth_pos⟩
        (Cutoff.translateCutoffSample z omega'))
    omega

/-- **The `ε_j(z)` cap (first inequality)**: almost surely, at every scale `j`
and every centre `z`,

```
ε_j(z) ≤ C_ann · (⅛ s δ^{1/2}) ,
```

The three hypotheses are that anchor's own premises at the Step-1 slot: the
standing regime `γ ≤ C_ann⁻¹ c⋆¹⁰`, the `s`-window (through `γ ≤ 1/256`), the
`ε`-range (through `δ ∈ (0,1/2]`) and the strengthened smallness. -/
theorem ae_stepOneEpsJ_le (d : ℕ) :
    ∃ Cann : ℝ, 0 < Cann ∧
      ∀ M : ABKModel d, M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ 1 / 256 →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ (j : ℤ) (z : Vec d),
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                stepOneEpsJ M j z delta omega ≤
                  ENNReal.ofReal (Cann * stepOneEp delta) := by
  obtain ⟨Cann, hCannpos, hcap⟩ :=
    ExcessDecay.ae_errorObservableSup_le_of_mem_goodEventAt d
  refine ⟨Cann, hCannpos, ?_⟩
  intro M hregime hgamma delta hdelta hsmall j z
  have hslot := hcap M hregime ⟨stepOneSEighth, stepOneSEighth_pos⟩
    (stepOneSEighth_mem_Icc hgamma) (stepOneEp delta) (stepOneEp_mem_Ioc hdelta)
    hsmall j z
  filter_upwards [hslot] with omega homega
  rw [stepOneEpsJ]
  by_cases hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) j z ⟨stepOneSEighth, stepOneSEighth_pos⟩
      (stepOneEp delta)
  · rw [Set.indicator_of_mem hmem]
    exact homega hmem
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

end Algsuperdiff.Section4.Provider.Regularity
