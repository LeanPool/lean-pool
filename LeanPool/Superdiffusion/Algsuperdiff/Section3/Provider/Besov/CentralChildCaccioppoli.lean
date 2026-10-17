/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Existence
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliDilationTransport
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliScalarEnvelopes
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.CoeffFamily
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-!
# CentralChildCaccioppoli

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Coarse-grained Caccioppoli energy on the ordinary central child

The Chapter 3 public interior Caccioppoli endpoint of the homogenization
development controls the *centered* patch at scale `Q.scale - 2`, namely
`caccioppoliCoreSet Q (cubeCenter Q) = \cu_m \cap (x_Q + \cu_{m-2})`.  The
Section 3.5 argument of ABK26 instead uses the ordinary central child at scale
`Q.scale - 1`.  This module supplies that endpoint, for an arbitrary Chapter 2
cube solution and at every integer scale, and then specializes it to the
canonical maximizer of a cube.

The deterministic content is already available upstream: the raw scale-zero
Caccioppoli bridge estimates the *localized one-third interior profile* of the
energy density, and the ordinary central child sits inside the concentric
closed one-third subcube.  Comparing normalizations costs exactly the parent to
child volume ratio `3^d`.

The right-hand side is the upstream `interiorCaccioppoliRHS`, i.e. the
`caccioppoliPrefactor` — which already carries the explicit `3^{-2m}` weight
and the coarse-grained `ThetaRatio`/`LambdaS` factors — multiplied by the
parent-cube oscillation `L^2` square.  No microscopic diffusivity enters.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open scoped Pointwise

noncomputable section

/-! ## Geometry of the ordinary central child -/

private theorem cubeScaleFactor_centralChild {d : ℕ} (Q : TriadicCube d) :
    cubeScaleFactor (CubeCalderonZygmund.centralChild Q) = cubeScaleFactor Q / 3 := by
  simpa [CubeCalderonZygmund.centralChild] using
    cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))

/-- The ordinary central child of `Q` sits inside `Q`. -/
theorem openCubeSet_centralChild_subset {d : ℕ} (Q : TriadicCube d) :
    openCubeSet (CubeCalderonZygmund.centralChild Q) ⊆ openCubeSet Q :=
  openCubeSet_subset_of_mem_childCubes (CubeCalderonZygmund.centralChild_mem_childCubes Q)

/-- The ordinary central child is contained in the closed concentric one-third
subcube, which is the localization radius occurring in the upstream raw
centered Caccioppoli bridge. -/
theorem openCubeSet_centralChild_subset_scaledClosedCubeSet_one_third
    {d : ℕ} (Q : TriadicCube d) :
    openCubeSet (CubeCalderonZygmund.centralChild Q) ⊆
      scaledClosedCubeSet Q (1 / 3 : ℝ) := by
  intro x hx i
  have hxi := hx i
  have hchild :
      cubeScaleFactor (CubeCalderonZygmund.centralChild Q) = cubeScaleFactor Q / 3 :=
    cubeScaleFactor_centralChild Q
  have hindex :
      (((CubeCalderonZygmund.centralChild Q).index i : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) := by
    simp [CubeCalderonZygmund.centralChild]
  rw [hchild, hindex] at hxi
  rw [abs_le]
  constructor <;> simp only [cubeCenter, cubeRadius] <;> linarith [hxi.1, hxi.2]

/-- Dilation commutes with taking the ordinary central child. -/
theorem centralChild_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    CubeCalderonZygmund.centralChild (Ch02.dilateCube k Q) =
      Ch02.dilateCube k (CubeCalderonZygmund.centralChild Q) := by
  apply congrArg₂ TriadicCube.mk
  · simp only [CubeCalderonZygmund.centralChild, Ch02.dilateCube]
    omega
  · rfl

private theorem cubeVolume_mul_inv_centralChild {d : ℕ} (Q : TriadicCube d) :
    (cubeVolume (CubeCalderonZygmund.centralChild Q))⁻¹ * cubeVolume Q = (3 : ℝ) ^ d := by
  have hscale :
      cubeScaleFactor (CubeCalderonZygmund.centralChild Q) = cubeScaleFactor Q / 3 :=
    cubeScaleFactor_centralChild Q
  have hQne : cubeScaleFactor Q ≠ 0 := by
    simpa [cubeScaleFactor] using
      (zpow_ne_zero Q.scale (show (3 : ℝ) ≠ 0 by norm_num))
  rw [cubeVolume_eq_scaleFactor_pow, cubeVolume_eq_scaleFactor_pow, hscale, div_pow]
  field_simp

/-! ## The central-child energy -/

/-- The parent-coefficient energy of a cube solution on the ordinary central child,
normalized by the child volume.  This is the quantity written
`\fint_{\cu_{m-1}} \nabla v \cdot \s \nabla v`. -/
noncomputable def centralChildCaccioppoliEnergy {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (u : CubeSolution Q a) : ℝ :=
  localizedCoeffEnergyValue (openCubeSet (CubeCalderonZygmund.centralChild Q))
    (a.coeffOn Q) u.toH1

private theorem centralChildCaccioppoliEnergy_eq_normalizedSetAverage_pointwise
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d} (u : CubeSolution Q a) :
    centralChildCaccioppoliEnergy Q a u =
      normalizedSetAverage (openCubeSet (CubeCalderonZygmund.centralChild Q))
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic y) := by
  have hAopen :
      (a.coeffOn Q).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet Q)] pointwiseCoeffFor Q a := by
    simpa [pointwiseCoeffFor, Ch02.cubeDomain] using
      (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
        (Ch02.cubeDomain Q) (a.coeffOn Q)).symm
  have hAchild :
      (a.coeffOn Q).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (CubeCalderonZygmund.centralChild Q))]
          pointwiseCoeffFor Q a :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (openCubeSet_centralChild_subset Q) hAopen
  unfold centralChildCaccioppoliEnergy localizedCoeffEnergyValue normalizedSetAverage
    volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    hAchild.mono fun y hy => by
      simp [scalarVariationEnergyIntegrand, hy, CubeSolution.toPointwiseAHarmonic]

private theorem setIntegral_centralChild_le_cubeVolume_mul_localizedProfile
    {d : ℕ} (Q : TriadicCube d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    ∫ y in openCubeSet (CubeCalderonZygmund.centralChild Q), energy y
        ∂MeasureTheory.volume ≤
      cubeVolume Q * coarseCaccioppoliLocalizedEnergyProfile Q (1 / 3 : ℝ) energy := by
  set inner : Set (Vec d) := scaledClosedCubeSet Q (1 / 3 : ℝ) with hinner
  have hloc_int :
      MeasureTheory.IntegrableOn (inner.indicator energy) (cubeSet Q)
        MeasureTheory.volume :=
    integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet
      Q (1 / 3 : ℝ) henergy_int
  have hloc_nonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] inner.indicator energy := by
    change ∀ᵐ y ∂MeasureTheory.volume.restrict (cubeSet Q), 0 ≤ inner.indicator energy y
    rw [MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)]
    refine Filter.Eventually.of_forall fun y hyQ => ?_
    by_cases hyinner : y ∈ inner
    · simpa [Set.indicator_of_mem hyinner] using henergy_nonneg y hyQ
    · simp [Set.indicator_of_notMem hyinner]
  have hchild_sub_cube :
      openCubeSet (CubeCalderonZygmund.centralChild Q) ⊆ cubeSet Q :=
    (openCubeSet_centralChild_subset Q).trans (openCubeSet_subset_cubeSet Q)
  have hmono :
      ∫ y in openCubeSet (CubeCalderonZygmund.centralChild Q),
          inner.indicator energy y ∂MeasureTheory.volume ≤
        ∫ y in cubeSet Q, inner.indicator energy y ∂MeasureTheory.volume :=
    MeasureTheory.setIntegral_mono_set hloc_int hloc_nonneg
      (Filter.Eventually.of_forall hchild_sub_cube)
  have hchild_eq :
      ∫ y in openCubeSet (CubeCalderonZygmund.centralChild Q), energy y
          ∂MeasureTheory.volume =
        ∫ y in openCubeSet (CubeCalderonZygmund.centralChild Q),
          inner.indicator energy y ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (CubeCalderonZygmund.centralChild Q)) fun y hy => ?_
    have hyinner : y ∈ inner :=
      openCubeSet_centralChild_subset_scaledClosedCubeSet_one_third Q hy
    rw [Set.indicator_of_mem hyinner]
  have hprofile_eq :
      ∫ y in cubeSet Q, inner.indicator energy y ∂MeasureTheory.volume =
        cubeVolume Q * coarseCaccioppoliLocalizedEnergyProfile Q (1 / 3 : ℝ) energy := by
    have hvol_ne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
    unfold coarseCaccioppoliLocalizedEnergyProfile cubeAverage
    rw [← hinner]
    field_simp
  rw [hchild_eq]
  exact hmono.trans_eq hprofile_eq

/-- The ordinary central-child energy is bounded by `3^d` times the raw
localized one-third energy profile of the same solution.  The factor is exactly
the ratio of the parent and child volumes. -/
theorem centralChildCaccioppoliEnergy_le_three_pow_mul_localizedProfile
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) :
    centralChildCaccioppoliEnergy Q a u ≤
      (3 : ℝ) ^ d *
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) (1 / 3 : ℝ) := by
  let A : CoeffField d := pointwiseCoeffFor Q a
  let uPw : AHarmonicFunction A (openCubeSet Q) := u.toPointwiseAHarmonic
  let energy : Vec d → ℝ := fun y => scalarVariationEnergyIntegrand A uPw y
  have hctrl :
      CoarseCaccioppoliFluxEnergyControls Q A (1 : ℝ)
        (fun y => matVecMul (A y) (uPw.toCubeSet.toH1.grad y))
        (fun y => scalarVariationEnergyIntegrand A uPw.toCubeSet y) :=
    CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
      (Q := Q) (a := A) (s := (1 : ℝ)) (by norm_num)
      (pointwiseCoeffFor_isEllipticFieldOn_cubeSet Q a) uPw.toCubeSet
  have henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y := by
    intro y hy
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.1 y hy
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := by
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.2.1
  have hintegral :=
    setIntegral_centralChild_le_cubeVolume_mul_localizedProfile Q henergy_nonneg henergy_int
  have hchildVolume :
      (MeasureTheory.volume (openCubeSet (CubeCalderonZygmund.centralChild Q))).toReal =
        cubeVolume (CubeCalderonZygmund.centralChild Q) :=
    volume_openCubeSet_toReal (CubeCalderonZygmund.centralChild Q)
  rw [centralChildCaccioppoliEnergy_eq_normalizedSetAverage_pointwise u]
  unfold normalizedSetAverage
  change
    (MeasureTheory.volume (openCubeSet (CubeCalderonZygmund.centralChild Q))).toReal⁻¹ *
        ∫ y in openCubeSet (CubeCalderonZygmund.centralChild Q), energy y
          ∂MeasureTheory.volume ≤ _
  rw [hchildVolume]
  calc
    (cubeVolume (CubeCalderonZygmund.centralChild Q))⁻¹ *
        ∫ y in openCubeSet (CubeCalderonZygmund.centralChild Q), energy y
          ∂MeasureTheory.volume ≤
        (cubeVolume (CubeCalderonZygmund.centralChild Q))⁻¹ *
          (cubeVolume Q * coarseCaccioppoliLocalizedEnergyProfile Q (1 / 3 : ℝ) energy) :=
      mul_le_mul_of_nonneg_left hintegral
        (inv_nonneg.mpr (cubeVolume_nonneg (CubeCalderonZygmund.centralChild Q)))
    _ =
        ((cubeVolume (CubeCalderonZygmund.centralChild Q))⁻¹ * cubeVolume Q) *
          coarseCaccioppoliLocalizedEnergyProfile Q (1 / 3 : ℝ) energy := by ring
    _ =
        (3 : ℝ) ^ d *
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q energy (1 / 3 : ℝ) := by
      rw [cubeVolume_mul_inv_centralChild Q]
      rfl

/-! ## The central-child Caccioppoli endpoint -/

/-- Scale-zero central-child Caccioppoli endpoint.  The constant is
dimension-only; it is the upstream scale-zero scalar envelope multiplied by
`d^2`, and the only new geometric factor relative to the upstream centered core
estimate is the parent-to-child volume ratio. -/
theorem centralChildCaccioppoli_scale_zero (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} (u : CubeSolution Q a),
        0 < s → 0 < t → s + t < 1 → Q.scale = 0 →
          centralChildCaccioppoliEnergy Q a u ≤ interiorCaccioppoliRHS C Q a s t u := by
  obtain ⟨Cenv, hCenv, _, hinteriorEnv⟩ :=
    (coarseCaccioppoliScaleZeroScalarEnvelope d).exists_constant
  set D : ℝ := (d : ℝ) ^ (2 : ℕ) with hD
  have hd_nat : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_nat
  have hD_pos : 0 < D := by
    rw [hD]
    exact pow_pos (lt_of_lt_of_le zero_lt_one hd_one) 2
  refine ⟨D * Cenv, mul_pos hD_pos hCenv, ?_⟩
  intro Q a s t u hs ht hst hQscale
  set CsolQ : ℝ := fullVectorPoincareCubeConstant Q with hCsolQ
  set CalphaQ : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s CsolQ with hCalphaQ
  set CcrossQ : ℝ := coarseCaccioppoliBufferedCrossBudget Q s CsolQ with hCcrossQ
  set CnoteQ : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q (pointwiseCoeffFor Q a) s t ((Fintype.card (Fin d) : ℝ) * CalphaQ)
      ((Fintype.card (Fin d) : ℝ) * CcrossQ) with hCnoteQ
  have hdet_full :=
    interior_centered_deterministic_note_from_public_oscillation_standardExplicitBudgetSplit
      (Q := Q) (a := a) u hs ht hst
  have hdet :
      0 ≤ CnoteQ ∧
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q
            (fun y =>
              scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                u.toPointwiseAHarmonic y) (1 / 3 : ℝ) ≤
          coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
            (interiorCaccioppoliParentOscillationL2Sq Q a u) := by
    simpa [hCsolQ, hCalphaQ, hCcrossQ, hCnoteQ] using hdet_full
  obtain ⟨hCnote, hdet_bound⟩ := hdet
  have hgeom :=
    centralChildCaccioppoliEnergy_le_three_pow_mul_localizedProfile (Q := Q) (a := a) u
  have hthree_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  have hconvert :
      coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
          (interiorCaccioppoliParentOscillationL2Sq Q a u) ≤
        interiorCaccioppoliRHS (D * CnoteQ) Q a s t u := by
    rw [hD]
    exact
      deterministic_interiorNoteRhs_pointwiseCoeffFor_le_publicRHS_dim_sq_mul_of_scale_zero
        (Q := Q) (a := a) u (s := s) (t := t) (C := CnoteQ) hs ht hst hCnote hQscale
  have hbound :
      centralChildCaccioppoliEnergy Q a u ≤
        (3 : ℝ) ^ d * interiorCaccioppoliRHS (D * CnoteQ) Q a s t u :=
    hgeom.trans
      ((mul_le_mul_of_nonneg_left hdet_bound hthree_nonneg).trans
        (mul_le_mul_of_nonneg_left hconvert hthree_nonneg))
  have hnote_le :
      CnoteQ ≤
        caccioppoliStandardExplicitNoteBoundSplit s t
          ((Fintype.card (Fin d) : ℝ) * coarseCaccioppoliBufferedAlphaBudgetUnit d s)
          ((Fintype.card (Fin d) : ℝ) * coarseCaccioppoliBufferedCrossBudgetUnit d s) := by
    have halpha : CalphaQ = coarseCaccioppoliBufferedAlphaBudgetUnit d s := by
      simpa [hCalphaQ, hCsolQ] using
        coarseCaccioppoliBufferedAlphaBudget_eq_unit_of_scale_eq_zero (Q := Q) s hQscale
    have hcross : CcrossQ = coarseCaccioppoliBufferedCrossBudgetUnit d s := by
      simpa [hCcrossQ, hCsolQ] using
        coarseCaccioppoliBufferedCrossBudget_eq_unit_of_scale_eq_zero (Q := Q) s hQscale
    simpa [hCnoteQ, halpha, hcross] using
      interior_centered_standardExplicitNoteConstantSplit_le_unitExplicitBound_of_scale_zero
        Q a hs ht hst hQscale
  have hnote_to_env : (3 : ℝ) ^ d * CnoteQ ≤ Cenv := by
    have hthree_le_eighteen : (3 : ℝ) ^ d ≤ (18 : ℝ) ^ d :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) d
    calc
      (3 : ℝ) ^ d * CnoteQ ≤ (18 : ℝ) ^ d * CnoteQ :=
        mul_le_mul_of_nonneg_right hthree_le_eighteen hCnote
      _ ≤
          (18 : ℝ) ^ d *
            caccioppoliStandardExplicitNoteBoundSplit s t
              ((Fintype.card (Fin d) : ℝ) * coarseCaccioppoliBufferedAlphaBudgetUnit d s)
              ((Fintype.card (Fin d) : ℝ) * coarseCaccioppoliBufferedCrossBudgetUnit d s) :=
        mul_le_mul_of_nonneg_left hnote_le (by positivity)
      _ = interiorCaccioppoliScaleZeroExplicitConstant d s t := rfl
      _ ≤ Cenv := hinteriorEnv hs ht hst
  have hconstant : (3 : ℝ) ^ d * (D * CnoteQ) ≤ D * Cenv := by
    calc
      (3 : ℝ) ^ d * (D * CnoteQ) = D * ((3 : ℝ) ^ d * CnoteQ) := by ring
      _ ≤ D * Cenv := mul_le_mul_of_nonneg_left hnote_to_env hD_pos.le
  exact
    hbound.trans
      (interiorCaccioppoliRHS_mul_const_le_of_mul_constant_le (Q := Q) (a := a) u
        (M := (3 : ℝ) ^ d) (C₁ := D * CnoteQ) (C₂ := D * Cenv)
        (one_le_pow₀ (by norm_num)) (mul_nonneg hD_pos.le hCnote) hconstant hs ht hst)

/-- **Central-child coarse-grained Caccioppoli estimate at every integer
scale.**  For a Chapter 2 cube solution on `\cu_m`, the coefficient energy on
the ordinary central child `\cu_{m-1}` is bounded by the public Caccioppoli
right-hand side of the parent, i.e. by the `caccioppoliPrefactor` — which
carries the explicit `3^{-2m}` weight — times the parent-cube oscillation `L^2`
square.  The constant is dimension-only.

Dilation preserves the parent-coefficient central-child energy exactly and
preserves the right-hand side after the `3^{-2m}` factor is combined with the
squared solution-amplitude normalization. -/
theorem centralChildCaccioppoli_transport (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} (u : CubeSolution Q a),
        0 < s → 0 < t → s + t < 1 →
          centralChildCaccioppoliEnergy Q a u ≤ interiorCaccioppoliRHS C Q a s t u := by
  obtain ⟨C, hC, hscaleZero⟩ := centralChildCaccioppoli_scale_zero d
  refine ⟨C, hC, ?_⟩
  intro Q a s t u hs ht hst
  set k : ℤ := -Q.scale with hk
  set r : ℝ := Ch02.triadicDilationFactor k with hr
  set b : CoeffFamily d := Ch02.TriadicCoeffFamily.dilate k a with hb
  have hFam : Ch02.TriadicCoeffFamily.IsDilation k a b :=
    Ch02.TriadicCoeffFamily.isDilation_dilate k a
  have hCoeff :
      Ch02.CoeffOn.IsCubeDilation k (a.coeffOn Q) (b.coeffOn (Ch02.dilateCube k Q)) :=
    hFam Q
  set vPack := Ch02.Solution.dilate hCoeff u with hvPack
  set vSol : CubeSolution (Ch02.dilateCube k Q) b := vPack.toSolution with hvSol
  have hscale : (Ch02.dilateCube k Q).scale = 0 := by simp [hk]
  have hzero :
      centralChildCaccioppoliEnergy (Ch02.dilateCube k Q) b vSol ≤
        interiorCaccioppoliRHS C (Ch02.dilateCube k Q) b s t vSol :=
    hscaleZero vSol hs ht hst hscale
  have henergy_dilate :=
    localizedCoeffEnergyValue_dilate_eq hCoeff vPack.isDilation
      (V := openCubeSet (CubeCalderonZygmund.centralChild Q))
      (openCubeSet_centralChild_subset Q)
  have hcentral_open :
      openCubeSet (CubeCalderonZygmund.centralChild (Ch02.dilateCube k Q)) =
        r • openCubeSet (CubeCalderonZygmund.centralChild Q) := by
    rw [centralChild_dilateCube]
    simpa [hr] using Ch02.openCubeSet_dilateCube k (CubeCalderonZygmund.centralChild Q)
  have henergy_eq :
      centralChildCaccioppoliEnergy (Ch02.dilateCube k Q) b vSol =
        centralChildCaccioppoliEnergy Q a u := by
    unfold centralChildCaccioppoliEnergy
    rw [hcentral_open]
    simpa [hvSol, hr] using henergy_dilate
  have hosc :=
    interiorCaccioppoliParentOscillationL2Sq_dilate_eq (A := a) (B := b) (Q := Q)
      vPack.isDilation
  have hpref :=
    caccioppoliPrefactor_dilate_neg_scale (Ch02.multiscaleDilationTheory d) (Q := Q)
      (a := a) (b := b) (C := C) (s := s) (t := t) (by simpa [hk, hb] using hFam)
  have hsq : r ^ (2 : ℕ) = Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) := by
    simpa [hr, hk] using triadicDilationFactor_neg_scale_sq Q
  have hrhs :
      interiorCaccioppoliRHS C (Ch02.dilateCube k Q) b s t vSol =
        interiorCaccioppoliRHS C Q a s t u := by
    unfold interiorCaccioppoliRHS
    rw [hosc, hsq, hpref]
    ring
  calc
    centralChildCaccioppoliEnergy Q a u =
        centralChildCaccioppoliEnergy (Ch02.dilateCube k Q) b vSol := henergy_eq.symm
    _ ≤ interiorCaccioppoliRHS C (Ch02.dilateCube k Q) b s t vSol := hzero
    _ = interiorCaccioppoliRHS C Q a s t u := hrhs

/-! ## The canonical maximizer of a cube -/

/-- The canonical maximizer of the cube `Q` for the pair `(p, q)`, read as a
Chapter 2 cube solution of the coefficient family of `a`.  This is the function
written `v = v(\cdot, \cu_m, p, q)` in Section 3.5. -/
noncomputable def canonicalCubeMaximizerSolution {d : ℕ} (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) :
    CubeSolution Q (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) :=
  (Ch02.canonicalMaximizer
      (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
      p q).toSolution

/-- **The Section 3.5 form of the Caccioppoli step.**  For the canonical
maximizer `v` of the cube `\cu_m` and an a.e. locally uniformly elliptic
coefficient field, the coefficient energy of `v` on the ordinary central child
`\cu_{m-1}` is bounded by the public Caccioppoli right-hand side of `\cu_m`,
whose prefactor carries the explicit weight `3^{-2m}` and whose remaining factor
is the parent-cube oscillation `L^2` square of `v`.  The constant is
dimension-only. -/
theorem centralChildCaccioppoli_canonicalMaximizer (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
        (Q : TriadicCube d) (p q : Vec d) {s t : ℝ},
        0 < s → 0 < t → s + t < 1 →
          centralChildCaccioppoliEnergy Q
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
              (canonicalCubeMaximizerSolution a ha Q p q) ≤
            interiorCaccioppoliRHS C Q
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) s t
              (canonicalCubeMaximizerSolution a ha Q p q) := by
  obtain ⟨C, hC, hbound⟩ := centralChildCaccioppoli_transport d
  refine ⟨C, hC, ?_⟩
  intro a ha Q p q s t hs ht hst
  exact hbound (canonicalCubeMaximizerSolution a ha Q p q) hs ht hst

end

end Algsuperdiff.Section3.Provider.Besov
