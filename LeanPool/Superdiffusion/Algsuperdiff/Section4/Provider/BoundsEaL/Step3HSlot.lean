/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ResponseTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.UglyPre

/-!
# Step3HSlot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 3: the sensitivity estimate at the recentered `h`-slot, at scale `j`

## The target

Step 3 of the proof of `l.bounds.mathcal.E.aL` applies

> the sensitivity estimate `e.J.sensitivity.no.conditions` of Lemma
> `l.J.sensitivity.no.conditions` in the cube `□_j` with `μ := σ_m σ_{j-2}^{-1}`,
> `σ₀ := σ_{j-2}` and `h := k_L − k_{j-2} − (k_L − k_m)_{□_m}`

to the single `J`-moment produced by Steps 1--2, "as in `e.ugly.estimate.for.J.pre`
in Step 2 of the proof of Proposition `p.mathcalE.annular.decomp`".

That template is **already proved** in this repository, for §4.1, at the SAME
witness family and with the SAME recentered `h`-slot:

* `Annular.exists_responseJ_ugly_pre` (`Provider/Annular/UglyPre.lean`) — the
  Section 2.4 anchor `Frozen.Section24.responseJ_sensitivity_unconditional`
  instantiated at `μ = σ_m σ_{n-2}^{-1}`, `σ₀ = σ_{n-2}`, with the caller's
  unit-cube coefficient `a` and unit-cube skew perturbation `h`, and with the
  anchor's `t`-slot at the caller's `s`;
* `Annular.responseJ_fluxCorrectedConst_lattice_eq_perturbCoeffOn`
  (`Provider/Annular/ResponseTransport.lean`) — the translation/dilation identity
  that reads `J(z + □_n; a_L − (k_L − k_m)_{□_m})` as the unit-cube perturbed
  object the anchor consumes, with the **recentering constant folded into the
  unit-cube perturbation** `centeredShellUnitCube`.

## What the export gives, and why that shape

The conclusion bounds

```
J(3^j v + □_j , σ_m^{-1/2} e , σ_m^{1/2} e; a_L − (k_L − k_m)_{□_m})
```

by a right-hand side **not containing `e`**.  That is exactly the hypothesis
shape `hfld` of the proved primal/adjoint split
`Annular.normalizedBlockResponseMax_isotropicComparator_le` (`e.bfJ.general`,
constant `1`), which is the step that connects this display to the *block*
response maximum appearing in `d.mathcal.E` — i.e. to the inner object of the
Step-1 endpoint of `Step1ScaleSum.lean`.

## Deviations from the printed display, all inherited

* **The gapped gauge.**  The printed exponents of `e.apply.sensitivity.J.aL`
  are `2s/(1-2γ)` and `2γ/(1-2γ)`; the display below carries `2s/(1-4γ)` and
  `4γ/(1-4γ)`, and its `λ`-slots read `unitCubeLambda (2γ)`.  A warning about
  direction: antitonicity of `λ⁻¹` in the gauge means the conclusion can never
  be read back at gauge `γ`.
* **The unit-cube gauges.**  The right side is written in the anchor's
  unit-cube gauges (`h.gradientW1Infinity`, `h.valueL2`, `unitCubeLambda`,
  `unitCubeHomogenizationError`), not in the printed scale-normalized ones
  (`3^{2j} ‖∇(k_L − k_{j-2})‖_{W^{1,∞}(□_j)}`, `‖·‖_{L²(□_j)}`,
  `λ_{γ,2}^{-1}(□_j; a_{j-2})`, `𝓔_{s,2,2}(□_j; a_{j-2}, σ_{j-2})`).  The
  manuscript performs that replacement silently; §4.1 records it as a named
  divergence and leaves it at the instantiation site, and so does this module.
  Supplying the identification is Step 4's business (its bullets (B4)--(B6) are
  stated in exactly those normalized gauges).
* **`s ≤ 1/4`.**  The cited lemma needs both exponent slots in `(0, 1/4]`.  This
  is free at §4.5, whose own `s`-range is `[C² √γ, 1/4]` with the closed right
  endpoint; `γ ≤ 1/8` is likewise free from `γ ≤ C^{-10}`.

## Main result

* `exists_responseJ_step3_recentered` — the Step-3 field-leg display at the
  lattice cube `3^j v + □_j`, for every `j` with `j - 2 ≤ L`, every recentering
  index `m`, and every unit `e`, with an `e`-free right-hand side.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 3 and `e.apply.sensitivity.J.aL`);
  `l.J.sensitivity.no.conditions`; `e.ugly.estimate.for.J.pre`;
  `e.bfJ.general`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-- **Step 3, field leg.**  The Section 2.4 sensitivity anchor, instantiated at §4.5's
own witness

```
μ := σ_m σ_{j-2}^{-1} ,   σ₀ := σ_{j-2} ,   h := k_L − k_{j-2} − (k_L − k_m)_{□_m} ,
```

read at the lattice cube `3^j v + □_j` through the proved response transport.
The right-hand side does not mention `e`, so it is directly usable as the
primal half of `Annular.normalizedBlockResponseMax_isotropicComparator_le`.

The three summands are the printed ones of `e.apply.sensitivity.J.aL`, in the
anchor's unit-cube gauges and at the gapped gauge `s = 2γ`; see the
module docstring for the complete deviation list. -/
theorem exists_responseJ_step3_recentered (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m j L : ℤ) (hle : j - 2 ≤ L) (v : Fin d → ℤ)
        (omega : Cutoff.CutoffSample d) (s : ℝ) (e : Vec d),
        0 < s → s ≤ 1 / 4 → M.gamma ≤ 1 / 8 → vecNorm e = 1 →
        responseJ (cubeDomain (⟨j, v⟩ : TriadicCube d))
            ((subConstCutoffTriadicCoeffFamily M L
              (Support.fluxIncrementAverage M L m (originCube d m) omega)
              (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
              omega).coeffOn (⟨j, v⟩ : TriadicCube d))
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤
          C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (j - 2) : ℝ)) *
              Real.rpow (1 +
                  (centeredShellUnitCube M (⟨j, v⟩ : TriadicCube d) hle omega
                    (Support.fluxIncrementAverage M L m (originCube d m) omega)
                    (matTranspose_fluxIncrementAverage M L m (originCube d m)
                      omega)).gradientW1Infinity *
                    (unitCubeLambda (2 * M.gamma) (.finite 2)
                      (unitRescaledCutoffCoeff M (⟨j, v⟩ : TriadicCube d) (j - 2)
                        omega))⁻¹)
                (2 * s / (1 - 4 * M.gamma)) *
              unitCubeHomogenizationError s (.finite 2) (.finite 2)
                (unitRescaledCutoffCoeff M (⟨j, v⟩ : TriadicCube d) (j - 2) omega)
                (Observable.isotropicComparatorMatrix
                  (Annealed.sigmaBar M (j - 2))) ^ 2 +
            C * ((Annealed.sigmaBar M m : ℝ)⁻¹ *
                (Annealed.sigmaBar M (j - 2) : ℝ) ^ 2) *
              (unitCubeLambda (2 * M.gamma) (.finite 2)
                (unitRescaledCutoffCoeff M (⟨j, v⟩ : TriadicCube d) (j - 2) omega))⁻¹ *
              Real.rpow (1 +
                  (centeredShellUnitCube M (⟨j, v⟩ : TriadicCube d) hle omega
                    (Support.fluxIncrementAverage M L m (originCube d m) omega)
                    (matTranspose_fluxIncrementAverage M L m (originCube d m)
                      omega)).gradientW1Infinity *
                    (unitCubeLambda (2 * M.gamma) (.finite 2)
                      (unitRescaledCutoffCoeff M (⟨j, v⟩ : TriadicCube d) (j - 2)
                        omega))⁻¹)
                (4 * M.gamma / (1 - 4 * M.gamma)) *
              ((Annealed.sigmaBar M (j - 2) : ℝ)⁻¹ ^ 2 *
                  (centeredShellUnitCube M (⟨j, v⟩ : TriadicCube d) hle omega
                    (Support.fluxIncrementAverage M L m (originCube d m) omega)
                    (matTranspose_fluxIncrementAverage M L m (originCube d m)
                      omega)).valueL2 ^ 2 +
                ((Annealed.sigmaBar M m : ℝ) *
                  (Annealed.sigmaBar M (j - 2) : ℝ)⁻¹ - 1) ^ 2) +
            C * (((Annealed.sigmaBar M m : ℝ)⁻¹ +
                  (unitCubeLambda (2 * M.gamma) (.finite 2)
                    (unitRescaledCutoffCoeff M (⟨j, v⟩ : TriadicCube d) (j - 2)
                      omega))⁻¹) *
                (centeredShellUnitCube M (⟨j, v⟩ : TriadicCube d) hle omega
                  (Support.fluxIncrementAverage M L m (originCube d m) omega)
                  (matTranspose_fluxIncrementAverage M L m (originCube d m)
                    omega)).gradientW1Infinity) ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hpre⟩ := exists_responseJ_ugly_pre d dimension
  refine ⟨C, hC, ?_⟩
  intro M m j L hle v omega s e hs0 hs1 hgam he
  rw [responseJ_fluxCorrectedConst_lattice_eq_perturbCoeffOn M j v hle m
    (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
    (Observable.sqrtLoad (Annealed.sigmaBar M m) e) omega]
  exact hpre M m j (unitRescaledCutoffCoeff M (⟨j, v⟩ : TriadicCube d) (j - 2) omega)
    (centeredShellUnitCube M (⟨j, v⟩ : TriadicCube d) hle omega
      (Support.fluxIncrementAverage M L m (originCube d m) omega)
      (matTranspose_fluxIncrementAverage M L m (originCube d m) omega))
    s e hs0 hs1 hgam he

end

end Algsuperdiff.Section4.Provider.BoundsEaL
