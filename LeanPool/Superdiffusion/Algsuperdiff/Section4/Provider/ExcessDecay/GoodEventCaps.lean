/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.AnnularDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.LambdaCaps
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api

/-!
# GoodEventCaps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The good-event caps: `𝓔·1_𝒢 ≤ C` and `max{σ⁻¹Λ, σλ⁻¹}·1_𝒢 ≤ C`

This module assembles the good-event caps of ABK26 — the displays
`e.good.set.giveth.v2` and `e.bound.Lambdas.by.Es.v2` — from the frozen
annular anchor `Algsuperdiff.Frozen.Section4.annular_decomposition` (clause
(ii)) and the `Λ`/`λ` algebra of `LambdaCaps.lean`.

## The extraction, and the term analysis it replaces

That analysis is *not* redone here: the frozen theorem's **clause (ii)**
already packages all four groups into the single bound `≤ C ε` under exactly
that hypothesis, so this module consumes the conclusion, never the proof.

## Parameter plumbing (verified below, not assumed)

The harmonic anchor's slot is `(s/8, ε = 1/2)` with `s ∈ [64γ, 1]`; the
annular anchor demands `s/8 ∈ [8γ, 1/4]` and `ε ∈ (0, 1/2]`.

* `s ≥ 64γ ⟹ s/8 ≥ 8γ`, and `s ≤ 1 ⟹ s/8 ≤ 1/8 ≤ 1/4` — both discharged by
  `annularSlot_mem_Icc`, so the whole `s`-range of the harmonic statement is
  admissible.
* `ε = 1/2 ∈ (0, 1/2]` — the right endpoint, discharged by `half_mem_Ioc`.
* The harmonic anchor's second hoisted hypothesis is *literally* the annular
  clause-(ii) hypothesis at this slot.  That identity is machine-certified,
  not asserted: `ae_boundLambdasByEs_harmonicSlot` binds the hypothesis in
  the harmonic statement's own syntax and discharges the generic lemma's
  requirement by `exact`, with no rewriting.  Likewise the first hoisted
  hypothesis `γ ≤ C⁻¹ c⋆¹⁰` is the annular standing regime verbatim.

The constant `C` produced below **is** the annular anchor's own constant;
a consumer that must satisfy both anchors' regime hypotheses at one constant
takes a maximum, which is the standard §4 pattern.

## Main results

* `annularSlot_mem_Icc`, `half_mem_Ioc` — the parameter plumbing.
* `ae_errorObservableSup_le_of_mem_goodEventAt` — clause (ii) read at the
  translated centre `z`: the `[0,∞]`-valued `sup_{L ≥ m}` observable is
  `≤ C ε` on the event `𝒢(m, z; t, ε)`.
* `ae_errorRepresentative_le_of_mem_goodEventAt` — **the caps step**
  (`e.good.set.giveth.v2`'s payoff): the real-valued per-`L`
  `𝓔_{t,∞,2}(z+□_m; a_L − (κ_L−κ_m)_{z+□_m}, σ_m)` is `≤ C ε` on the event.
* `ae_boundLambdasByEs` — **`e.bound.Lambdas.by.Es.v2`**:
  `max{σ_m⁻¹Λ_{t,2}, σ_mλ_{t,2}⁻¹} ≤ 2d((Cε)² + 1)` on the event.
* `ae_errorRepresentative_le_harmonicSlot`,
  `ae_boundLambdasByEs_harmonicSlot` — the two headline results at the
  harmonic statement's own slot `(s/8, ε = 1/2)` and its own binders.

## Deviations from print, recorded

1. **The index/cube of the cap.**  The printed `e.bound.Lambdas.by.Es.v2` is
   stated at the *child* cube `x+□_{n+1}` and index `s/4`; the caps proved here
   are at the *parent* cube `z+□_{n+2}` and index `s/8`, which is where the
   annular anchor delivers and where no index change is needed.  **They are NOT
   assumed here**; no declaration below takes them as a hypothesis.
   Consequently the printed display's first two inequalities are out of scope
   for this module, and the good-event caps they carry remain open.
3. **The comparator.**  See `LambdaCaps.lean`: the printed display mixes
   `σ_n⁻¹Λ` with `σ_{n+1}λ⁻¹` whereas the cited lemma uses a single `σ₀`;
   we follow the lemma at `σ₀ = σ_m`.

## References

* ABK26, `e.good.set.giveth.v2` and `e.bound.Lambdas.by.Es.v2`.
* ABK26, `e.mathcalE.annular.decomp.good.event`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Parameter plumbing -/

theorem annularSlot_mem_Icc (gamma s : ℝ) (h : s ∈ Set.Icc (64 * gamma) 1) :
    s / 8 ∈ Set.Icc (8 * gamma) (1 / 4 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := h
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- **The ruled `ε` slot is the right endpoint of the annular `ε`-range.** -/
theorem half_mem_Ioc : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) :=
  ⟨by norm_num, le_refl _⟩

/-! ## 2. Clause (ii) at a translated centre -/

/-- **Annular clause (ii), read at the centre `z`.**

The frozen theorem states clause (ii) at the origin centre `0` and at the
untranslated sample.  Composing with the law-preserving
`Cutoff.translateCutoffSample z` (proved:
`GoodEvents.measurePreserving_translateCutoffSample`, valid for every real `z`)
and using the preimage shape of the frozen `goodEventAt` turns it into the
statement at the centre `z` and the `z`-translated sample — the convention
resolution A4 fixes, and the one the harmonic statement's right-hand side uses. -/
theorem ae_errorObservableSup_le_of_mem_goodEventAt (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ t : {t : ℝ // 0 < t}, (t : ℝ) ∈ Set.Icc (8 * M.gamma) (1 / 4 : ℝ) →
          ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (t : ℝ) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep →
              ∀ (m : ℤ) (z : Vec d),
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Support.cgEllipLowerConstant d) m z t ep →
                    Support.fluxCorrectedErrorObservableSup M m t
                        (Cutoff.translateCutoffSample z omega) ≤
                      ENNReal.ofReal (C * ep) := by
  obtain ⟨C, hCpos, hC⟩ := Algsuperdiff.Frozen.Section4.annular_decomposition d
  refine ⟨C, hCpos, ?_⟩
  intro M hregime t ht ep hep hsmall m z
  have hbase := hC M hregime (t : ℝ) ht t.2 m
  have htrans := (GoodEvents.measurePreserving_translateCutoffSample M
    z).quasiMeasurePreserving.ae hbase
  filter_upwards [htrans] with omega homega
  intro hmem
  have hcap := homega.2 ep hep hsmall
  have hmem0 : Cutoff.translateCutoffSample z omega ∈
      Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) m
        (0 : Vec d) t ep := by
    rw [GoodEvents.goodEventAt_zero]
    exact hmem
  rw [Set.indicator_of_mem hmem0] at hcap
  exact hcap

/-! ## 3. The caps step -/

/-- **The caps step: `𝓔 · 1_𝒢 ≤ C ε`, real-valued and per-`L`.**

This is the payoff of `e.good.set.giveth.v2` that the harmonic statement's
right-hand side actually reads: the flux-corrected `(∞,2)` representative
`𝓔_{t,∞,2}(z+□_m; a_L − (κ_L−κ_m)_{z+□_m}, σ_m)` at the `z`-translated
sample, for every `L ≥ m`.

Only the *third* inequality of the printed display (the `≤ C`) is proved
here; the first two are out of scope, see deviation 1 in the module
docstring. -/
theorem ae_errorRepresentative_le_of_mem_goodEventAt (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ t : {t : ℝ // 0 < t}, (t : ℝ) ∈ Set.Icc (8 * M.gamma) (1 / 4 : ℝ) →
          ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (t : ℝ) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep →
              ∀ (m : ℤ) (z : Vec d),
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Support.cgEllipLowerConstant d) m z t ep →
                    ∀ L : ℤ, m ≤ L →
                      Support.fluxCorrectedErrorRepresentative M L m t
                          (Cutoff.translateCutoffSample z omega) ≤ C * ep := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorObservableSup_le_of_mem_goodEventAt d
  refine ⟨C, hCpos, ?_⟩
  intro M hregime t ht ep hep hsmall m z
  have hprod : 0 ≤ C * ep := mul_nonneg hCpos.le hep.1.le
  filter_upwards [hC M hregime t ht ep hep hsmall m z] with omega homega
  intro hmem L hL
  have hsup := homega hmem
  have hle : ENNReal.ofReal
      (Support.fluxCorrectedErrorRepresentative M L m t
        (Cutoff.translateCutoffSample z omega)) ≤ ENNReal.ofReal (C * ep) :=
    le_trans (Support.le_fluxCorrectedErrorObservableSup M m t
      (Cutoff.translateCutoffSample z omega) hL) hsup
  exact (ENNReal.ofReal_le_ofReal_iff hprod).1 hle

/-! ## 4. `e.bound.Lambdas.by.Es.v2` -/

/-- **`e.bound.Lambdas.by.Es.v2` at the annular slot.**

The good-event cap on the coarse-grained ellipticity ratios of the
flux-corrected field:

```
max{ σ_m⁻¹ Λ_{t,2}(z+□_m; a_L − (κ_L−κ_m)_{z+□_m}) ,
     σ_m   λ_{t,2}⁻¹(z+□_m; a_L − (κ_L−κ_m)_{z+□_m}) } · 1_𝒢  ≤  2d((Cε)² + 1) .
```

The right-hand side is a constant `C(d)`, which is what the coarse-grained
Caccioppoli step `e.energy.bound.interior` consumes; see deviations 1, 3, 4
in the module docstring for the three ways this differs from the printed
display. -/
theorem ae_boundLambdasByEs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ t : {t : ℝ // 0 < t}, (t : ℝ) ∈ Set.Icc (8 * M.gamma) (1 / 4 : ℝ) →
          ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (t : ℝ) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep →
              ∀ (m : ℤ) (z : Vec d),
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Support.cgEllipLowerConstant d) m z t ep →
                    ∀ L : ℤ, m ≤ L →
                      fluxCorrectedEllipticityRatioMax M L m (t : ℝ)
                          (Cutoff.translateCutoffSample z omega) ≤
                        2 * (d : ℝ) * ((C * ep) ^ 2 + 1) := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  refine ⟨C, hCpos, ?_⟩
  intro M hregime t ht ep hep hsmall m z
  have halg := (GoodEvents.measurePreserving_translateCutoffSample M
    z).quasiMeasurePreserving.ae (ae_fluxCorrectedEllipticityRatioMax_le M m t)
  filter_upwards [hC M hregime t ht ep hep hsmall m z, halg] with omega hcap hratio
  intro hmem L hL
  refine le_trans (hratio L hL) (two_mul_dim_mul_sq_add_one_le_of_le ?_ (hcap hmem L hL))
  exact Support.fluxCorrectedErrorRepresentative_nonneg M L m t
    (Cutoff.translateCutoffSample z omega)

/-! ## 5. The harmonic statement's own slot -/

/-- **The caps step at the harmonic statement's slot `(s/8, ε = 1/2)`.**

Every hypothesis below is transcribed from
`Algsuperdiff/Frozen/Section4/HarmonicApproximation.lean` in that file's own
syntax; the annular window and `ε`-range requirements are *derived*, and the
smallness hypothesis is handed to the generic lemma by `exact`, which
machine-certifies that the harmonic anchor's second hoisted hypothesis is
literally annular clause (ii)'s hypothesis at this slot. -/
theorem ae_errorRepresentative_le_harmonicSlot (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L →
                Support.fluxCorrectedErrorRepresentative M L (n + 2)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) ≤ C * (1 / 2) := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs n z
  exact hC M hregime ⟨s / 8, by linarith only [hs]⟩
    (annularSlot_mem_Icc M.gamma s hsrange) (1 / 2) half_mem_Ioc hsmall (n + 2) z

end

end Algsuperdiff.Section4.Provider.ExcessDecay
