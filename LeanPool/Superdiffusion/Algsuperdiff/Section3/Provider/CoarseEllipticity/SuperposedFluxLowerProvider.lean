/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxRateParameters
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLocalPayoffAE

/-!
# SuperposedFluxLowerProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Sharp superposed-flux provider for the lower coarse-ellipticity leg

The earlier local-payoff interface factors `3^(2 * beta * k₀)` into a common
constant.  That factor is harmless only in the collar term, where it remains
paired with the rare factor `exp (-kp / 36)`; putting it into the deterministic
term loses the dimension-only profile as `gamma` tends to zero.  This file
keeps the collar factor in the rare slot and builds the lower provider from
that sharp split.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Filter MeasureTheory Topology
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

/-! ## The sharp local split -/

/-- The deterministic part of the shifted pure-flux constant.  Only the
`(2 gamma + eps) * k₀` shift belongs here. -/
def superposedFluxSharpConst (M : ABKModel d) (n i : ℤ)
    (eps beta : ℝ) (k₀ kp : ℕ) : ℝ :=
  superposedFluxCoordinateConst M n i eps beta kp *
    (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))

/-- The collar shift retained beside the rare factor. -/
def superposedFluxSharpRare (beta : ℝ) (k₀ kp : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) * superposedFluxRare kp

theorem superposedFluxSharpConst_pos (hd : 2 ≤ d) (M : ABKModel d)
    (n i : ℤ) (eps beta : ℝ) (k₀ kp : ℕ) :
    0 < superposedFluxSharpConst M n i eps beta k₀ kp := by
  unfold superposedFluxSharpConst
  exact mul_pos
    (by
      have hlocal := superposedFluxLocalConst_pos hd M n i eps beta 0 kp
      simpa [superposedFluxLocalConst] using hlocal)
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem superposedFluxSharpRare_pos (beta : ℝ) (k₀ kp : ℕ) :
    0 < superposedFluxSharpRare beta k₀ kp := by
  unfold superposedFluxSharpRare superposedFluxRare
  positivity

/-- The pure-flux conclusion with the collar shift left in its rare slot. -/
theorem sum_superposedConclusionPayload_flux_basis_le_sharpStep3Payload
    (hd : 2 ≤ d) (M : ABKModel d) (n i L : ℤ) (E : ℝ)
    {b eps beta : ℝ} (heps : 0 < eps)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (t : ℝ) (k₀ kp : ℕ) (omega : CutoffSample d) :
    (∑ j : Fin d,
        superposedConclusionPayload M n i L E b eps t beta k₀ kp omega
          0 (basisVec j)) ≤
      superposedFluxSharpConst M n i eps beta k₀ kp *
        ((3 : ℝ) ^
            (superposedFluxLocalExponent M b eps beta *
              (hsep M n E b omega : ℝ)) *
          (1 + (3 : ℝ) ^ (2 * b * (hsep M n E b omega : ℝ)) *
            superposedFluxSharpRare beta k₀ kp)) := by
  rw [sum_superposedConclusionPayload_flux_basis_eq]
  have hK : 0 ≤ superposedFluxCoordinateConst M n i eps beta kp :=
    superposedFluxCoordinateConst_nonneg hd M n i eps beta kp
  have hh : 0 ≤ (hsep M n E b omega : ℝ) := Nat.cast_nonneg _
  have hbeta_b : b ≤ beta := by
    linarith [M.shellPrefix.gamma_pos]
  have hgamdom :
      (2 * M.gamma + eps) * (hsep M n E b omega : ℝ) ≤
        superposedFluxLocalExponent M b eps beta *
          (hsep M n E b omega : ℝ) := by
    unfold superposedFluxLocalExponent
    nlinarith [mul_nonneg (sub_nonneg.mpr hbeta_b) hh]
  have hfirst :
      (3 : ℝ) ^ ((2 * M.gamma + eps) *
          (hsep M n E b omega : ℝ)) ≤
        (3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
          (hsep M n E b omega : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hgamdom
  rw [Nat.cast_add,
    show (2 * M.gamma + eps) *
        ((hsep M n E b omega : ℝ) + (k₀ : ℝ)) =
      (2 * M.gamma + eps) * (hsep M n E b omega : ℝ) +
        (2 * M.gamma + eps) * (k₀ : ℝ) by ring,
    show 2 * beta * ((hsep M n E b omega : ℝ) + (k₀ : ℝ)) =
      2 * beta * (hsep M n E b omega : ℝ) +
        2 * beta * (k₀ : ℝ) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  unfold superposedFluxSharpConst superposedFluxSharpRare
  have hrare : 0 ≤ superposedFluxRare kp :=
    (by unfold superposedFluxRare; positivity)
  have hpowerEq :
      (3 : ℝ) ^ ((2 * M.gamma + eps) * (hsep M n E b omega : ℝ)) *
          (3 : ℝ) ^ (2 * beta * (hsep M n E b omega : ℝ)) =
        (3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
            (hsep M n E b omega : ℝ)) *
          (3 : ℝ) ^ (2 * b * (hsep M n E b omega : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    unfold superposedFluxLocalExponent
    ring
  calc
    superposedFluxCoordinateConst M n i eps beta kp *
          (((3 : ℝ) ^ ((2 * M.gamma + eps) *
                (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) *
            (1 +
              (3 : ℝ) ^ (2 * beta * (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
                superposedFluxRare kp)) =
        superposedFluxCoordinateConst M n i eps beta kp *
            ((3 : ℝ) ^ ((2 * M.gamma + eps) *
                (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) +
          superposedFluxCoordinateConst M n i eps beta kp *
            ((3 : ℝ) ^ ((2 * M.gamma + eps) *
                (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) *
            ((3 : ℝ) ^ (2 * beta * (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
              superposedFluxRare kp) := by ring
    _ ≤ superposedFluxCoordinateConst M n i eps beta kp *
            ((3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
                (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) +
          superposedFluxCoordinateConst M n i eps beta kp *
            ((3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
                (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) *
            ((3 : ℝ) ^ (2 * b * (hsep M n E b omega : ℝ)) *
              (3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
              superposedFluxRare kp) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfirst
            (Real.rpow_nonneg (by norm_num) _)) hK
      · have hrandom :
            superposedFluxCoordinateConst M n i eps beta kp *
                ((3 : ℝ) ^ ((2 * M.gamma + eps) *
                    (hsep M n E b omega : ℝ)) *
                  (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) *
                ((3 : ℝ) ^ (2 * beta * (hsep M n E b omega : ℝ)) *
                  (3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
                  superposedFluxRare kp) =
              superposedFluxCoordinateConst M n i eps beta kp *
                ((3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
                    (hsep M n E b omega : ℝ)) *
                  (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ))) *
                ((3 : ℝ) ^ (2 * b * (hsep M n E b omega : ℝ)) *
                  (3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
                  superposedFluxRare kp) := by
          calc
            _ = superposedFluxCoordinateConst M n i eps beta kp *
                  (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ)) *
                  ((3 : ℝ) ^ ((2 * M.gamma + eps) *
                      (hsep M n E b omega : ℝ)) *
                    (3 : ℝ) ^ (2 * beta * (hsep M n E b omega : ℝ))) *
                  ((3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
                    superposedFluxRare kp) := by ring
            _ = superposedFluxCoordinateConst M n i eps beta kp *
                  (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ)) *
                  ((3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
                      (hsep M n E b omega : ℝ)) *
                    (3 : ℝ) ^ (2 * b * (hsep M n E b omega : ℝ))) *
                  ((3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
                    superposedFluxRare kp) := by rw [hpowerEq]
            _ = _ := by ring
        exact hrandom.le
    _ = superposedFluxCoordinateConst M n i eps beta kp *
          (3 : ℝ) ^ ((2 * M.gamma + eps) * (k₀ : ℝ)) *
        ((3 : ℝ) ^ (superposedFluxLocalExponent M b eps beta *
            (hsep M n E b omega : ℝ)) *
          (1 + (3 : ℝ) ^ (2 * b * (hsep M n E b omega : ℝ)) *
            ((3 : ℝ) ^ (2 * beta * (k₀ : ℝ)) *
              superposedFluxRare kp))) := by
      ring

/-- Conditional one-cube payoff with the sharp deterministic and rare slots. -/
theorem slstar_local_perCube_of_sharpSuperposedFluxConclusion_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 3 ≤ k₀)
    {eps : ℝ} (heps : 0 < eps) {t : ℝ} (ht0 : 0 ≤ t) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (hsepSet M R.scale (E : ℝ) b
        (translateCutoffSample (triadicCubeShift R) omega)).Nonempty →
      ∀ (L : ℤ), m - 1 ≤ L →
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀
              (translateCutoffSample (triadicCubeShift R) omega)) n,
          cubeSupBound Q Q.scale L
              (translateCutoffSample (triadicCubeShift R) omega).1 ≤
            whitneyWaveLayerScale M R.scale
              (whitneyScale M R.scale (E : ℝ) b k₀
                (translateCutoffSample (triadicCubeShift R) omega)) n L * t) →
        cutoffSigmaStarInvBlockFamily M L
            (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
          2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
            bfaLocalLane M R (E : ℝ) b
              (superposedFluxLocalExponent M b eps beta)
              (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
              (superposedFluxSharpRare beta k₀ kp) omega := by
  have hgam : 0 ≤ superposedFluxLocalExponent M b eps beta := by
    unfold superposedFluxLocalExponent
    have hbeta_b : b ≤ beta := by linarith [M.shellPrefix.gamma_pos]
    linarith [M.shellPrefix.gamma_pos]
  have hCpre : 0 ≤
      superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp :=
    (superposedFluxSharpConst_pos hd M _ _ eps beta k₀ kp).le
  filter_upwards
      [descendantInverseBlock_le_superposedFluxBasis_ae
        hd M hR hS hb0 hb hk₀ heps ht0 hbeta0 hbeta9 hbetab hgammaWin hcap]
    with omega hbase hne L hL henv
  have hsum := hbase hne L hL henv
  have hcompress :=
    sum_superposedConclusionPayload_flux_basis_le_sharpStep3Payload
      hd M R.scale (m - 1) L (E : ℝ) heps hbetab t k₀ kp
        (translateCutoffSample (triadicCubeShift R) omega)
  have hsplit := step3Payload_le_two_mul_add_bfaLane M R.scale
    (E := (E : ℝ)) (b := b)
    (gam := superposedFluxLocalExponent M b eps beta)
    (Cpre := superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
    (eps := superposedFluxSharpRare beta k₀ kp) hgam hCpre
    (translateCutoffSample (triadicCubeShift R) omega)
  have hsplitLocal :
      superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp *
          ((3 : ℝ) ^
              (superposedFluxLocalExponent M b eps beta *
                (hsep M R.scale (E : ℝ) b
                  (translateCutoffSample (triadicCubeShift R) omega) : ℝ)) *
            (1 + (3 : ℝ) ^
                (2 * b * (hsep M R.scale (E : ℝ) b
                  (translateCutoffSample (triadicCubeShift R) omega) : ℝ)) *
              superposedFluxSharpRare beta k₀ kp)) ≤
        2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
          bfaLocalLane M R (E : ℝ) b
            (superposedFluxLocalExponent M b eps beta)
            (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
            (superposedFluxSharpRare beta k₀ kp) omega := by
    simpa [bfaLocalLane] using hsplit
  exact hsum.trans (hcompress.trans hsplitLocal)

/-! ## Removal of the translated wave and separation gates -/

private theorem slstar_local_perCube_allL_of_sharpEnvelope_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 3 ≤ k₀)
    {eps : ℝ} (heps : 0 < eps) {t : ℝ} (ht : 1 ≤ t) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ((hsepSet M R.scale (E : ℝ) b
          (translateCutoffSample (triadicCubeShift R) omega)).Nonempty ∧
        randomHsepAllLWaveEnvelope M R.scale (E : ℝ) b k₀ (m - 1) t
          (translateCutoffSample (triadicCubeShift R) omega)) →
      ∀ (L : ℤ), m - 1 ≤ L →
        cutoffSigmaStarInvBlockFamily M L
            (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
          2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
            bfaLocalLane M R (E : ℝ) b
              (superposedFluxLocalExponent M b eps beta)
              (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
              (superposedFluxSharpRare beta k₀ kp) omega := by
  have hrAe : ∀ r : ℕ, ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (hsepSet M R.scale (E : ℝ) b
          (translateCutoffSample (triadicCubeShift R) omega)).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
          (whitneyScale M R.scale (E : ℝ) b k₀
            (translateCutoffSample (triadicCubeShift R) omega)) n,
        cubeSupBound Q Q.scale (m - 1 + (r : ℤ))
            (translateCutoffSample (triadicCubeShift R) omega).1 ≤
          whitneyWaveLayerScale M R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀
              (translateCutoffSample (triadicCubeShift R) omega)) n
                (m - 1 + (r : ℤ)) * allLWaveAmplitude t r) →
      cutoffSigmaStarInvBlockFamily M (m - 1 + (r : ℤ))
          (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
        2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
          bfaLocalLane M R (E : ℝ) b
            (superposedFluxLocalExponent M b eps beta)
            (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
            (superposedFluxSharpRare beta k₀ kp) omega := by
    intro r
    have hamp0 : 0 ≤ allLWaveAmplitude t r := by
      unfold allLWaveAmplitude
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    have hbase := slstar_local_perCube_of_sharpSuperposedFluxConclusion_ae
      hd M hR hS hb0 hb hk₀ heps hamp0 hbeta0 hbeta9 hbetab hgammaWin hcap
    filter_upwards [hbase] with omega homega hne henv
    exact homega hne (m - 1 + (r : ℤ)) (by omega) henv
  have hall := MeasureTheory.ae_all_iff.mpr hrAe
  filter_upwards [hall] with omega homega hgood L hL
  let r : ℕ := (L - (m - 1)).toNat
  have hdiff : (0 : ℤ) ≤ L - (m - 1) := sub_nonneg.mpr hL
  have hrCast : ((r : ℕ) : ℤ) = L - (m - 1) := Int.toNat_of_nonneg hdiff
  have hLr : m - 1 + (r : ℤ) = L := by omega
  have hpay := homega r hgood.1 (hgood.2 r)
  rwa [hLr] at hpay

/-- The sharp one-cube payoff holds almost surely for every cutoff index. -/
theorem slstar_local_perCube_allL_ae_sharp_of_gates
    (hd : 2 ≤ d) (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma b : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ (E : ℝ))
    (hE4 : 4 ≤ (E : ℝ)) (hunit : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : (E : ℝ)⁻¹ ^ 2 ≤ Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ (E : ℝ))
    (hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {eps : ℝ} (heps : 0 < eps) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (L : ℤ), m - 1 ≤ L →
        cutoffSigmaStarInvBlockFamily M L
            (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
          2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
            bfaLocalLane M R (E : ℝ) b
              (superposedFluxLocalExponent M b eps beta)
              (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
              (superposedFluxSharpRare beta k₀ kp) omega := by
  let μ := (cutoffSampleLaw M).toMeasure
  let Target : CutoffSample d → Prop := fun omega =>
    ∀ (L : ℤ), m - 1 ≤ L →
      cutoffSigmaStarInvBlockFamily M L
          (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
        2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
          bfaLocalLane M R (E : ℝ) b
            (superposedFluxLocalExponent M b eps beta)
            (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
            (superposedFluxSharpRare beta k₀ kp) omega
  have hscale : R.scale = m - 1 - (k : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hlocal : R.scale - 1 ≤ m - 1 := by rw [hscale]; omega
  have hSlocal := inductionState_restrict hlocal hS
  have hsepCenterReal : μ.real {omega : CutoffSample d |
      ¬ (hsepSet M R.scale (E : ℝ) b omega).Nonempty} = 0 := by
    simpa only [μ] using
      (measureReal_hsepSet_not_nonempty_of_gates M hd E.property hSlocal
        hsigma0 hsigma hb0 hb hEexp hE4 hunit hgamma20 hinvSq hEb hgamma)
  have hsepCenter : ∀ᵐ omega ∂μ,
      (hsepSet M R.scale (E : ℝ) b omega).Nonempty := by
    rw [ae_iff]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hsepCenterReal
  have hsepTranslate : ∀ᵐ omega ∂μ,
      (hsepSet M R.scale (E : ℝ) b
        (translateCutoffSample (triadicCubeShift R) omega)).Nonempty := by
    refine MeasureTheory.ae_of_ae_map
      (p := fun omega => (hsepSet M R.scale (E : ℝ) b omega).Nonempty)
      (measurable_translateCutoffSample (triadicCubeShift R)).aemeasurable ?_
    rw [map_translateCutoffSample_cutoffSampleLaw]
    exact hsepCenter
  have hbadBound : ∀ j : ℕ,
      μ.real {omega : CutoffSample d | ¬ Target omega} ≤
        randomHsepAllLWavePrice sigma b
          (allLPriceLimitDepth j) (allLPriceLimitAmplitude j) := by
    intro j
    have hH : 1 ≤ allLPriceLimitDepth j := by unfold allLPriceLimitDepth; omega
    have ht : 1 ≤ allLPriceLimitAmplitude j := by
      rw [allLPriceLimitAmplitude, Real.one_le_sqrt]
      norm_num
    let Wave : CutoffSample d → Prop := fun omega =>
      randomHsepAllLWaveEnvelope M R.scale (E : ℝ) b k₀ (m - 1)
        (allLPriceLimitAmplitude j)
        (translateCutoffSample (triadicCubeShift R) omega)
    have hpay := slstar_local_perCube_allL_of_sharpEnvelope_ae
      hd M hR hS hb0 hb hk₀ heps ht hbeta0 hbeta9 hbetab hgammaWin hcap
    have himp : ∀ᵐ omega ∂μ, Wave omega → Target omega := by
      filter_upwards [hsepTranslate, hpay] with omega hsep hlocalPay hwave
      exact hlocalPay ⟨hsep, hwave⟩
    let Nae : Set (CutoffSample d) := {omega | ¬ (Wave omega → Target omega)}
    have hNaeMeasure : μ Nae = 0 := by simpa only [Nae] using ae_iff.mp himp
    have hNaeReal : μ.real Nae = 0 := by
      rw [measureReal_def, hNaeMeasure, ENNReal.toReal_zero]
    have hsub : {omega : CutoffSample d | ¬ Target omega} ⊆
        {omega : CutoffSample d | ¬ Wave omega} ∪ Nae := by
      intro omega htarget
      by_cases hwave : Wave omega
      · exact Or.inr (fun himpTarget => htarget (himpTarget hwave))
      · exact Or.inl hwave
    have hmono := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
    have hunion := measureReal_union_le (μ := μ)
      {omega : CutoffSample d | ¬ Wave omega} Nae
    have hwaveBad : μ.real {omega : CutoffSample d | ¬ Wave omega} ≤
        randomHsepAllLWavePrice sigma b
          (allLPriceLimitDepth j) (allLPriceLimitAmplitude j) := by
      simpa only [μ, Wave] using
        (measureReal_not_randomHsepAllLWaveEnvelope_translate_le hd M
          E.property hSlocal hsigma0 hsigma hb0 hb hEexp hE4 hunit hgamma20
          hinvSq hEb hgamma k₀ (by omega) hH ht (triadicCubeShift R))
    linarith
  have hprice := tendsto_randomHsepAllLWavePrice_limitSequence hsigma hb0
  have hbadNonpos : μ.real {omega : CutoffSample d | ¬ Target omega} ≤ 0 :=
    ge_of_tendsto hprice (Filter.Eventually.of_forall hbadBound)
  have hbadZero : μ.real {omega : CutoffSample d | ¬ Target omega} = 0 :=
    le_antisymm hbadNonpos measureReal_nonneg
  have htargetAe : ∀ᵐ omega ∂μ, Target omega := by
    rw [ae_iff]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hbadZero
  simpa only [μ, Target] using htargetAe

/-! ## Finite descendant-grid lift -/

/-- The sharp payoff simultaneously over the finite descendant grid. -/
theorem slstar_descendantGrid_allL_ae_sharp_of_gates
    (hd : 2 ≤ d) (M : ABKModel d) {m : ℤ} (k : ℕ)
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma b : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ (E : ℝ))
    (hE4 : 4 ≤ (E : ℝ)) (hunit : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : (E : ℝ)⁻¹ ^ 2 ≤ Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ (E : ℝ))
    (hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {eps : ℝ} (heps : 0 < eps) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
        ∀ (L : ℤ), m - 1 ≤ L →
          cutoffSigmaStarInvBlockFamily M L
              (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
            2 * superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
                eps beta k₀ kp +
              bfaLocalGridSup M m k (E : ℝ) b
                (superposedFluxLocalExponent M b eps beta)
                (superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
                  eps beta k₀ kp)
                (superposedFluxSharpRare beta k₀ kp) omega := by
  have hperCube : ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
      ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        ∀ (L : ℤ), m - 1 ≤ L →
          cutoffSigmaStarInvBlockFamily M L
              (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
            2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
              bfaLocalLane M R (E : ℝ) b
                (superposedFluxLocalExponent M b eps beta)
                (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
                (superposedFluxSharpRare beta k₀ kp) omega := by
    intro R hR
    exact slstar_local_perCube_allL_ae_sharp_of_gates hd M hR hS hsigma0 hsigma
      hb0 hb hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hk₀ heps hbeta0
      hbeta9 hbetab hgammaWin hcap
  have hall : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
        ∀ (L : ℤ), m - 1 ≤ L →
          cutoffSigmaStarInvBlockFamily M L
              (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
            2 * superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp +
              bfaLocalLane M R (E : ℝ) b
                (superposedFluxLocalExponent M b eps beta)
                (superposedFluxSharpConst M R.scale (m - 1) eps beta k₀ kp)
                (superposedFluxSharpRare beta k₀ kp) omega := by
    rw [Filter.eventually_all_finset]
    exact hperCube
  filter_upwards [hall] with omega homega
  intro R hR L hL
  have hscale : R.scale = m - 1 - (k : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hpay := homega R hR L hL
  rw [hscale] at hpay
  refine hpay.trans (add_le_add le_rfl ?_)
  refine (le_abs_self _).trans ?_
  unfold bfaLocalGridSup
  exact le_blockGridSup
    (X := fun R => bfaLocalLane M R (E : ℝ) b
      (superposedFluxLocalExponent M b eps beta)
      (superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
        eps beta k₀ kp)
      (superposedFluxSharpRare beta k₀ kp)) hR omega

/-- The sharp grid payoff paired with its direct Orlicz certificate. -/
theorem slstar_descendantGrid_allL_ae_and_isBigOWith_sharp_of_gates
    (hd : 2 ≤ d) (M : ABKModel d) {m : ℤ} (k : ℕ)
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma b : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ (E : ℝ))
    (hE4 : 4 ≤ (E : ℝ)) (hunit : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : (E : ℝ)⁻¹ ^ 2 ≤ Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ (E : ℝ))
    (hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {eps : ℝ} (heps : 0 < eps) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ)))
    (hlocalb : superposedFluxLocalExponent M b eps beta ≤ b) :
    (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
        ∀ (L : ℤ), m - 1 ≤ L →
          cutoffSigmaStarInvBlockFamily M L
              (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
            2 * superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
                eps beta k₀ kp +
              bfaLocalGridSup M m k (E : ℝ) b
                (superposedFluxLocalExponent M b eps beta)
                (superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
                  eps beta k₀ kp)
                (superposedFluxSharpRare beta k₀ kp) omega) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma (bfaTau sigma (superposedFluxLocalExponent M b eps beta) b))
        (bfaLocalGridSup M m k (E : ℝ) b
          (superposedFluxLocalExponent M b eps beta)
          (superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
            eps beta k₀ kp)
          (superposedFluxSharpRare beta k₀ kp))
        (gridBlockAmp d
          (bfaTau sigma (superposedFluxLocalExponent M b eps beta) b)
          (bfaLaneScale sigma b (superposedFluxLocalExponent M b eps beta)
            (superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
              eps beta k₀ kp)
            (superposedFluxSharpRare beta k₀ kp)) k) := by
  refine ⟨slstar_descendantGrid_allL_ae_sharp_of_gates hd M k hS hsigma0 hsigma
    hb0 hb hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hk₀ heps hbeta0 hbeta9
    hbetab hgammaWin hcap, ?_⟩
  have hlocal0 : 0 < superposedFluxLocalExponent M b eps beta := by
    unfold superposedFluxLocalExponent
    have hbeta_b : b ≤ beta := by linarith [M.shellPrefix.gamma_pos]
    linarith [M.shellPrefix.gamma_pos]
  exact isBigOWith_gammaSigma_bfaLocalGridSup_of_gates M k hd E.property hS
    hsigma0 hsigma hb0 hb hEexp hE4 hunit hgamma20 hinvSq hEb hgamma
    hlocal0 hlocalb
    (superposedFluxSharpConst_pos hd M _ _ eps beta k₀ kp)
    (superposedFluxSharpRare_pos beta k₀ kp)

/-! ## Dimension-only deterministic profile -/

/-- The pure-flux value of the `Ktot` prefactor, before its scale power. -/
def superposedFluxKBase (d : ℕ) : ℝ :=
  960 * simplexCrudeConst d (1 / 4)

/-- The pure-flux `Ktot` constant is the dimension-only base times its scale
power. -/
theorem ktotConst_flux_basis_eq (M : ABKModel d) (n i : ℤ)
    (j : Fin d) :
    ktotConst M n i 3 0 (0 : Vec d) (basisVec j) =
      superposedFluxKBase d * (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (n : ℝ))) := by
  rw [ktotConst, vecNormSq_basisVec]
  simp only [vecNormSq, vecDot_zero_left, mul_zero, mul_one]
  unfold superposedFluxKBase
  ring

/-- A dimension-only envelope for the sharp deterministic constant. -/
def superposedFluxSharpDetConst (d : ℕ) : ℝ :=
  (d : ℝ) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
    (superposedFluxKBase d * (6 * (d : ℝ)) +
      8 * (superposedDivConst d) ^ 2 * superposedFluxKBase d *
        Real.sqrt (6 * (d : ℝ))) *
    (3 : ℝ) ^ (2 * siteRateBase d + 2)

theorem superposedFluxSharpDetConst_pos (hd : 2 ≤ d) :
    0 < superposedFluxSharpDetConst d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hI : 0 < (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
    exact inv_pos.mpr (sub_pos.mpr three_rpow_neg_quarter_lt_one)
  have hK : 0 < superposedFluxKBase d := by
    unfold superposedFluxKBase
    refine mul_pos (by norm_num) ?_
    rw [simplexCrudeConst]
    have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hpow := Real.rpow_lt_one_of_one_lt_of_neg
        (show (1 : ℝ) < 3 by norm_num) (show (-(1 / 2 : ℝ)) < 0 by norm_num)
      linarith
    norm_num
    positivity
  unfold superposedFluxSharpDetConst
  positivity

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
