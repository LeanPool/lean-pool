/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorPrefactor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlotTransportChildCube

/-!
# CaccioppoliInteriorEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.energy.bound.interior` at the parent slot

This module assembles ABK26's interior coarse-grained Caccioppoli energy
estimate (`e.energy.bound.interior`) at the **parent** slot of the frozen §4.3
anchor, in the translated frame of resolution A4:

```text
  ⨍_{□_{n+2} ∩ (w+□_n)} ∇u · ã_{L,n+2} ∇u  ·  1_𝒢
      ≤  C(d) ( σ_{n+2} 3^{-2(n+2)} ‖u - (u)_{□_{n+2}}‖²_{L²(□_{n+2})}
                + s^{-8} σ_{n+2}^{-1} [g]²_{B^s(□_{n+2})} ) ,
```

almost surely on the harmonic anchor's own good event
`𝒢(n+2, z; s/8, 1/2)`, for every `L ≥ n+2`, every window centre `w`, and every
forced `H¹(□_{n+2})` solution of `-∇·ã_{L,n+2}∇u = ∇·g`.

## What each input supplies

* the **energy inequality**: CoarseGraining's `coarseCaccioppoliRHSTheory`,
  specialized to the interior regime and mean-subtracted in
  `CaccioppoliInteriorDatum.lean`;
* the **geometry**: `CaccioppoliInteriorGeometry.lean` (the corollary that
  identifies the Caccioppoli core with the translated child cube `w + □_n`).

## What this module does NOT do (disclosed frontier)

The forced equation on the parent cube, at the flux-corrected family and at the
translated sample, is an **input**.  Producing it from the frozen theorem's
Dirichlet problem on `□_m` still needs, and this module does not contain:

1. the restriction of the `□_m` equation to the parent window (the interior
   gate `(z+□_{n+2}) ⊆ □_m` — proved in `CaccioppoliInteriorGeometry.lean` —
   plus `H¹₀` extension by zero, which CoarseGraining has for arbitrary open
   supersets);
3. the A4 **translation transport** of `H¹`, of the coefficient field and of the
   Besov seminorm from the geometric window `z + □_{n+2}` to the origin cube.

Likewise the passage from this estimate to the frozen theorem's own display
needs the `ν^{1/2}‖∇u‖_{L²} ↔ ⨍ ∇u·ã∇u` identification and a
Gagliardo-versus-Besov comparison (the anchor writes `normalizedGagliardo`,
CoarseGraining's Caccioppoli carries the block-average Besov seminorm).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The display object -/

/-- **The right-hand side of `e.energy.bound.interior`, squared, at the parent
window.**  The mean-subtracted parent `L²` square plus the forcing seminorm
square, at the honest envelope `s^{-8}`. -/
def interiorEnergyRHS (M : ABKModel d) (n : ℤ) (s : ℝ)
    (u : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 2) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y -
          volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) +
    Real.rpow s (-8 : ℝ) * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g ^ 2

/-- The same display at the **printed** envelope `s^{-11}` (the square of the
printed `s^{-11/2}`). -/
def interiorEnergyRHSPrinted (M : ABKModel d) (n : ℤ) (s : ℝ)
    (u : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 2) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y -
          volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) +
    Real.rpow s (-11 : ℝ) * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g ^ 2

/-- **The honest envelope is stronger than the printed one** on the anchor's
`s`-range: `s^{-8} ≤ s^{-11}` for `0 < s ≤ 1`. -/
theorem interiorEnergyRHS_le_printed (M : ABKModel d) (n : ℤ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    (u : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (g : Vec d → Vec d)
    (hg : ForceBesovRegularity (originCube d (n + 2)) s g) :
    interiorEnergyRHS M n s u g ≤ interiorEnergyRHSPrinted M n s u g := by
  have hpow : Real.rpow s (-8 : ℝ) ≤ Real.rpow s (-11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hBnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ s g
      hg.partialSeminorms_bddAbove
  have hsig : 0 ≤ (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (n + 2)).2.le
  have hstep : Real.rpow s (-8 : ℝ) *
        ((Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
          scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d (n + 2)) s g ^ 2) ≤
      Real.rpow s (-11 : ℝ) *
        ((Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
          scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d (n + 2)) s g ^ 2) :=
    mul_le_mul_of_nonneg_right hpow (mul_nonneg hsig (pow_nonneg hBnn 2))
  rw [interiorEnergyRHS, interiorEnergyRHSPrinted]
  linarith only [hstep]

/-! ## 2. The arithmetic stitch -/

/-- The purely arithmetic step folding the prefactor bound, the two `q = 1`
ellipticity caps, the forcing-factor bound and the Besov exponent comparison into
one constant.  Abstract in every quantity, so no analytic content hides here. -/
private theorem stitch_arith {LHS P Pb lam Sc L2 F Finv B Bs K sig E : ℝ}
    (hmain : LHS ≤ P * (lam * Sc * L2 + F * Finv * B ^ 2))
    (hpre : P ≤ Pb) (hPnn : 0 ≤ P)
    (hlam : lam ≤ K * sig) (hlamnn : 0 ≤ lam)
    (hFinv : Finv ≤ K * sig⁻¹) (hFinvnn : 0 ≤ Finv)
    (hF : F ≤ 131072 * E) (hFnn : 0 ≤ F)
    (hB : B ≤ Bs) (hBnn : 0 ≤ B)
    (hSc : 0 ≤ Sc) (hL2 : 0 ≤ L2) (hEnn : 0 ≤ E) (hKnn : 0 ≤ K)
    (hsignn : 0 ≤ sig) (hsiginv : 0 ≤ sig⁻¹) :
    LHS ≤ Pb * (131072 * K) * (sig * Sc * L2 + E * sig⁻¹ * Bs ^ 2) := by
  have hEb : (0 : ℝ) ≤ 131072 * E := by linarith only [hEnn]
  have hbr1 : lam * Sc * L2 ≤ 131072 * K * (sig * Sc * L2) := by
    have h1 : lam * (Sc * L2) ≤ K * sig * (Sc * L2) :=
      mul_le_mul_of_nonneg_right hlam (mul_nonneg hSc hL2)
    have h2 : (0 : ℝ) ≤ K * (sig * (Sc * L2)) :=
      mul_nonneg hKnn (mul_nonneg hsignn (mul_nonneg hSc hL2))
    linarith only [h1, h2]
  have hbr2 : F * Finv * B ^ 2 ≤ 131072 * K * (E * sig⁻¹ * Bs ^ 2) := by
    have hBsq : B ^ 2 ≤ Bs ^ 2 := pow_le_pow_left₀ hBnn hB 2
    have hstep1 : F * Finv ≤ 131072 * E * (K * sig⁻¹) :=
      mul_le_mul hF hFinv hFinvnn hEb
    have hstep2 : F * Finv * B ^ 2 ≤ 131072 * E * (K * sig⁻¹) * Bs ^ 2 :=
      mul_le_mul hstep1 hBsq (pow_nonneg hBnn 2)
        (mul_nonneg hEb (mul_nonneg hKnn hsiginv))
    linarith only [hstep2]
  have hbr : lam * Sc * L2 + F * Finv * B ^ 2 ≤
      131072 * K * (sig * Sc * L2 + E * sig⁻¹ * Bs ^ 2) := by
    linarith only [hbr1, hbr2]
  have hbrnn : (0 : ℝ) ≤ lam * Sc * L2 + F * Finv * B ^ 2 :=
    add_nonneg (mul_nonneg (mul_nonneg hlamnn hSc) hL2)
      (mul_nonneg (mul_nonneg hFnn hFinvnn) (pow_nonneg hBnn 2))
  calc LHS ≤ P * (lam * Sc * L2 + F * Finv * B ^ 2) := hmain
    _ ≤ Pb * (131072 * K * (sig * Sc * L2 + E * sig⁻¹ * Bs ^ 2)) :=
        mul_le_mul hpre hbr hbrnn (le_trans hPnn hpre)
    _ = Pb * (131072 * K) * (sig * Sc * L2 + E * sig⁻¹ * Bs ^ 2) := by ring

/-! ## 3. The energy estimate on the good event -/

/-- **`e.energy.bound.interior` at the parent slot, in the translated frame.**

Almost surely on the harmonic anchor's good event `𝒢(n+2, z; s/8, 1/2)`, for
every `L ≥ n+2`, every window centre `w` whose Dirichlet patch `w + □_{n+1}`
sits inside `□_{n+2}` (the interior regime), and every `H¹(□_{n+2})` solution of
`-∇·ã_{L,n+2}∇u = ∇·g` with `g ∈ H^s(□_{n+2})`,

```text
  ⨍_{□_{n+2} ∩ (w+□_n)} ∇u · ã_{L,n+2} ∇u ≤ Cout · interiorEnergyRHS M n s u g .
```

The two constants are separate: `C` is the annular anchor's regime constant,
`Cout` the output constant. -/
theorem ae_interiorCaccioppoliEnergy_harmonicSlot (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L → ∀ (w : Vec d) (g : Vec d → Vec d)
                (u : H1Function
                  (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d))),
                openCubeAtScale w (n + 1) ⊆ openCubeSet (originCube d (n + 2)) →
                ForceBesovRegularity (originCube d (n + 2)) s g →
                IsForcedEquation (originCube d (n + 2))
                    (Support.fluxCorrectedCoeffFamily M L (n + 2)
                      (originCube d (n + 2))
                      (Cutoff.translateCutoffSample z omega)) u g →
                  localizedCoeffEnergyValue
                      (caccioppoliCoreSet (originCube d (n + 2)) w)
                      ((Support.fluxCorrectedCoeffFamily M L (n + 2)
                        (originCube d (n + 2))
                        (Cutoff.translateCutoffSample z omega)).coeffOn
                        (originCube d (n + 2))) u ≤
                    Cout * interiorEnergyRHS M n s u g := by
  obtain ⟨C1, hC1pos, hcacc⟩ := exists_interiorCaccioppoliEnergy_subConst d
  obtain ⟨C, hCpos, hcaps⟩ := ae_boundLambdasByEs_parent_index_le_harmonicSlot d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hKpos : (0 : ℝ) < 2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) := by
    have h1 : (0 : ℝ) < (C * (1 / 2)) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  refine ⟨C, (2 * max 1 C1) ^ (4 : ℕ) * 4 *
    ((2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1)) ^ (2 : ℕ)) ^ (2 : ℕ) *
    (131072 * (2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1))), hCpos, ?_, ?_⟩
  · have hC1m : (0 : ℝ) < 2 * max 1 C1 := by
      have : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
      linarith only [this]
    positivity
  intro M s hsrange hregime hsmall hs n z
  filter_upwards [hcaps M s hsrange hregime hsmall hs n z] with omega hcap
  intro hmem L hL w g u hpatch hgreg hu
  -- abbreviations
  have hs1 : s ≤ 1 := hsrange.2
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) :=
    (Annealed.sigmaBar M (n + 2)).2
  have hscale : (originCube d (n + 2)).scale - 1 = n + 1 := by
    show n + 2 - 1 = n + 1
    ring
  have hpatch' : openCubeAtScale w ((originCube d (n + 2)).scale - 1) ⊆
      openCubeSet (originCube d (n + 2)) := by
    rw [hscale]
    exact hpatch
  have hgreg' : ForceBesovRegularity (originCube d (n + 2)) (2 * (s / 4)) g :=
    CubeVectorBesovHRegularity.of_exponent_le hgreg (by linarith only [hs])
  -- the two `q = 2` caps, read off the proved ratio maximum
  have hcapU : (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      Ch02.LambdaSq (originCube d (n + 2)) (1 / 4 / 2) (.finite 2)
        (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
          (Cutoff.translateCutoffSample z omega)) ≤
      2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) := by
    have h := hcap hmem L hL (1 / 4 / 2) (by linarith only [hs1])
    rw [fluxCorrectedEllipticityRatioMax_def] at h
    exact le_trans (le_max_left _ _) h
  have hcapL : (Annealed.sigmaBar M (n + 2) : ℝ) *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4 / 2) (.finite 2)
        (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
          (Cutoff.translateCutoffSample z omega)))⁻¹ ≤
      2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) := by
    have h := hcap hmem L hL (s / 4 / 2) (by linarith only [])
    rw [fluxCorrectedEllipticityRatioMax_def] at h
    exact le_trans (le_max_right _ _) h
  -- the `q = 1` ingredients
  have hLam := LambdaS_le_of_ratio_cap (originCube d (n + 2))
    (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega))
    (u := 1 / 4) (by norm_num) hsig hcapU
  have hlamInv := lambdaS_inv_le_of_ratio_cap (originCube d (n + 2))
    (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega))
    (u := s / 4) (by linarith only [hs]) hsig hcapL
  have hlam : Ch02.lambdaS (originCube d (n + 2)) (s / 4)
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega)) ≤
      2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 2) : ℝ) :=
    le_trans (lambdaS_le_LambdaS (originCube d (n + 2)) _ (by norm_num)
      (by linarith only [hs])) hLam
  have hTheta : Ch02.ThetaRatio (originCube d (n + 2)) (1 / 4) (s / 4)
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega)) ≤
      (2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1)) ^ (2 : ℕ) := by
    have h := thetaRatio_le_of_caps (originCube d (n + 2)) _
      (by norm_num : (0 : ℝ) < 1 / 4) (by linarith only [hs] : (0 : ℝ) < s / 4)
      hLam hlamInv
    have heq : 2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) *
          (Annealed.sigmaBar M (n + 2) : ℝ) *
          (2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) *
            (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹) =
        (2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1)) ^ (2 : ℕ) := by
      field_simp
    rw [heq] at h
    exact h
  -- the Caccioppoli inequality at the chosen parameters
  have hmain := hcacc (Q := originCube d (n + 2))
    (a := Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega))
    (s := 1 / 4) (t := s / 4) (x := w) (g := g) u
    (volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) hu
    (by norm_num) (by norm_num) (by linarith only [hs]) (by linarith only [hs1])
    (by linarith only [hs1]) hpatch' hgreg'
  -- the prefactor
  have hpre := caccioppoliWithRHSPrefactor_quarter_le (Q := originCube d (n + 2))
    (a := Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega))
    (C := C1) (s := s) hC1pos hs hs1 hTheta
  -- the remaining ingredients of the stitch
  have hlamnn : 0 ≤ Ch02.lambdaS (originCube d (n + 2)) (s / 4)
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega)) := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg _ _ (by linarith only [hs]) (by norm_num)
  have hFinv : Real.rpow (Ch02.lambdaS (originCube d (n + 2)) (s / 4)
        (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
          (Cutoff.translateCutoffSample z omega))) (-1 : ℝ) ≤
      2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    exact hlamInv
  have hPnn : 0 ≤ caccioppoliWithRHSPrefactor C1 (originCube d (n + 2))
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega)) (1 / 4) (s / 4) :=
    caccioppoliWithRHSPrefactor_nonneg hC1pos.le (by norm_num)
      (by linarith only [hs]) (by linarith only [hs1])
  have hFnn : (0 : ℝ) ≤ Real.rpow (s / 4) (-8 : ℝ) / (1 - 2 * (s / 4)) :=
    div_nonneg (Real.rpow_nonneg (by linarith only [hs]) _) (by linarith only [hs1])
  have hBnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) (2 * (s / 4)) g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ _ g
      hgreg'.partialSeminorms_bddAbove
  have hB : scaleNormalizedPositiveBesovVectorSeminormTwo
        (originCube d (n + 2)) (2 * (s / 4)) g ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove
      (originCube d (n + 2)) g (by linarith only [hs])
      hgreg.partialSeminorms_bddAbove
  rw [interiorEnergyRHS]
  exact stitch_arith hmain hpre hPnn hlam hlamnn hFinv
    (Real.rpow_nonneg hlamnn _) (forcing_factor_quarter_le hs hs1) hFnn hB hBnn
    (Real.rpow_nonneg (by norm_num) _)
    (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _))
    (Real.rpow_nonneg hs.le _) hKpos.le hsig.le (inv_nonneg.mpr hsig.le)

/-! ## 4. The frozen theorem's own geometry, at the printed envelope -/

/-- **`e.energy.bound.interior` read at the frozen theorem's geometry binder.**

Under the anchor's own binder `(x+□_n) ⊆ (z+□_{n+1}) ∩ □_m`, the Caccioppoli core
of the translated frame *is* the translated child cube `(x-z) + □_n`, and the
Dirichlet patch inclusion is automatic.  The right-hand side is stated at the
**printed** envelope `s^{-11}` (the square of `s^{-11/2}`), which the honest
`s^{-8}` dominates on the anchor's `s`-range:

```text
  ⨍_{(x-z)+□_n} ∇u · ã_{L,n+2} ∇u  ·  1_𝒢
      ≤ C(d) ( σ_{n+2} 3^{-2(n+2)} ‖u - (u)_{□_{n+2}}‖²_{L²(□_{n+2})}
               + s^{-11} σ_{n+2}^{-1} [g]²_{B^s(□_{n+2})} ) .
```

The frontier-empty gate of the anchor's second conjunct is *not* consumed here:
it is what the caller needs in order to restrict the `□_m` equation to the parent
(see `CaccioppoliInteriorGeometry.lean` and the module docstring). -/
theorem ae_interiorCaccioppoliEnergy_originCube (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (m n : ℤ) (x z : Vec d),
          (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L → ∀ (g : Vec d → Vec d)
                (u : H1Function
                  (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d))),
                ForceBesovRegularity (originCube d (n + 2)) s g →
                IsForcedEquation (originCube d (n + 2))
                    (Support.fluxCorrectedCoeffFamily M L (n + 2)
                      (originCube d (n + 2))
                      (Cutoff.translateCutoffSample z omega)) u g →
                  localizedCoeffEnergyValue
                      ((fun y => (x - z) + y) '' openCubeSet (originCube d n))
                      ((Support.fluxCorrectedCoeffFamily M L (n + 2)
                        (originCube d (n + 2))
                        (Cutoff.translateCutoffSample z omega)).coeffOn
                        (originCube d (n + 2))) u ≤
                    Cout * interiorEnergyRHSPrinted M n s u g := by
  obtain ⟨C, Cout, hCpos, hCoutpos, hmain⟩ :=
    ae_interiorCaccioppoliEnergy_harmonicSlot d
  refine ⟨C, Cout, hCpos, hCoutpos, ?_⟩
  intro M s hsrange hregime hsmall hs m n x z hsub
  filter_upwards [hmain M s hsrange hregime hsmall hs n z] with omega hbound
  intro hmem L hL g u hgreg hu
  have hs1 : s ≤ 1 := hsrange.2
  have hpatch : openCubeAtScale (x - z) (n + 1) ⊆
      openCubeSet (originCube d (n + 2)) :=
    openCubeAtScale_patch_subset_of_anchorGeometry hsub
  have hstep := hbound hmem L hL (x - z) g u hpatch hgreg hu
  rw [← caccioppoliCoreSet_eq_image_add_of_anchorGeometry hsub]
  refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ hCoutpos.le)
  exact interiorEnergyRHS_le_printed M n hs hs1 u g hgreg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
