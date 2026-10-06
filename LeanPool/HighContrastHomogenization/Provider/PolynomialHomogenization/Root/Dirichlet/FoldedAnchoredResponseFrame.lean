/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.AmplitudeRate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.AnchoredProduct
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.GaugeMaxPowerFluxFrameAbsorption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredResidualFrameRate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FoldedAnchoredResponseFrame

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The folded-scale anchored residual frame provider

The formulaic anchored provider produces a physical flux frame at the
certificate's own homogenization length, with a frame constant that still
carries the homogenized matrix: through the filling coefficient, which is a
truncation of a multiple of the absolute gauge scale, and through the frame
exponent, which carries the certificate's activation length and hence the
witness eccentricity.

This module assembles a **parallel** provider at the folded length.  The
original provider is consumed as a black box — it is neither re-proved nor
edited — and only two things are re-derived from its exported package: the
amplitude rate (`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.AmplitudeRate`)
and the arithmetic of the frame exponent
(`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.FrameExponentFold`).
The result exports a frame constant
built from the dimension, the printed orders, the rate, the flux constant, the
outer sandwich radius, the normalization radius and the certificate's own
amplitude alone, at the folded length
`x * eccentricityFoldFactor abar pEcc` with the law-free exponent
`pEcc = printRowOrder g * max (responseWindowOrder g) kappaRate /
   (2 * kappaRate ^ 2)`.

No hypothesis outside the original provider's binder surface and the frozen
normalization data is introduced.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Set

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The cross-grid coefficient at a general microscopic parameter -/

/-- **The cross-grid matrix is a scalar.**  The affine grid at the microscopic
parameter `lambda` and the exact normalized root differ by the scalar
`lambda * alpha`, with `alpha` the absolute gauge scale of the homogenized
matrix.  No comparison matrix survives. -/
theorem crossGrid_gauge_eq [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {lambda : ℝ}
    (hlambda : 0 < lambda) :
    (epsilonAffineGrid lambda abar)⁻¹ * Selection.normalizedRoot (symmPart abar) =
      (lambda * Real.sqrt (specBound ((symmPart abar)⁻¹))) • (1 : Mat d) := by
  have hq : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  rw [epsilonAffineGrid, Selection.normalizedRoot_eq,
    inv_smul_of_isUnit (inv_ne_zero hlambda.ne') hq, inv_inv,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hq, smul_smul]

/-! ## The law-free split of the filling coefficient -/

/-- The law-free truncation constant of the observation filling on the residual
window. -/
@[expose]
def gaugeSplitFillingConstant (d : ℕ) : ℝ :=
  max 1 (6 * (d : ℝ) * Real.sqrt d * (3 * ‖(1 : Mat d)‖))

theorem one_le_gaugeSplitFillingConstant (d : ℕ) :
    (1 : ℝ) ≤ gaugeSplitFillingConstant d :=
  le_max_left _ _

/-- **The filling coefficient splits into a law-free constant and a truncated
gauge scale.**  The cross-grid matrix is `lambda * alpha` times the identity, so
the whole law dependence of the filling coefficient is the truncation at one of
the absolute gauge scale. -/
theorem observationFillingCoefficient_le_gaugeSplit [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {lambda : ℝ}
    (hlambda0 : 0 < lambda) (hlambda3 : lambda ≤ 3) :
    observationFillingCoefficient d lambda abar ≤
      gaugeSplitFillingConstant d *
        max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹))) := by
  have halpha0 : (0 : ℝ) ≤ Real.sqrt (specBound ((symmPart abar)⁻¹)) :=
    Real.sqrt_nonneg _
  have hnorm : ‖(epsilonAffineGrid lambda abar)⁻¹ *
      Selection.normalizedRoot (symmPart abar)‖ =
      lambda * Real.sqrt (specBound ((symmPart abar)⁻¹)) * ‖(1 : Mat d)‖ := by
    rw [crossGrid_gauge_eq hS hlambda0, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hlambda0.le halpha0)]
  have hdim0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
  have hinner : lambda * Real.sqrt (specBound ((symmPart abar)⁻¹)) *
      ‖(1 : Mat d)‖ ≤
      3 * ‖(1 : Mat d)‖ * Real.sqrt (specBound ((symmPart abar)⁻¹)) := by
    have h1 : lambda * ‖(1 : Mat d)‖ ≤ 3 * ‖(1 : Mat d)‖ :=
      mul_le_mul_of_nonneg_right hlambda3 (norm_nonneg _)
    calc lambda * Real.sqrt (specBound ((symmPart abar)⁻¹)) * ‖(1 : Mat d)‖
        = lambda * ‖(1 : Mat d)‖ *
          Real.sqrt (specBound ((symmPart abar)⁻¹)) := by ring
      _ ≤ 3 * ‖(1 : Mat d)‖ *
          Real.sqrt (specBound ((symmPart abar)⁻¹)) :=
        mul_le_mul_of_nonneg_right h1 halpha0
  have hstep : 6 * (d : ℝ) * Real.sqrt d *
      (lambda * Real.sqrt (specBound ((symmPart abar)⁻¹)) * ‖(1 : Mat d)‖) ≤
      6 * (d : ℝ) * Real.sqrt d * (3 * ‖(1 : Mat d)‖) *
        Real.sqrt (specBound ((symmPart abar)⁻¹)) := by
    calc 6 * (d : ℝ) * Real.sqrt d *
        (lambda * Real.sqrt (specBound ((symmPart abar)⁻¹)) * ‖(1 : Mat d)‖)
        ≤ 6 * (d : ℝ) * Real.sqrt d *
          (3 * ‖(1 : Mat d)‖ *
            Real.sqrt (specBound ((symmPart abar)⁻¹))) :=
          mul_le_mul_of_nonneg_left hinner hdim0
      _ = 6 * (d : ℝ) * Real.sqrt d * (3 * ‖(1 : Mat d)‖) *
            Real.sqrt (specBound ((symmPart abar)⁻¹)) := by ring
  calc observationFillingCoefficient d lambda abar
      = max 1 (6 * (d : ℝ) * Real.sqrt d *
        (lambda * Real.sqrt (specBound ((symmPart abar)⁻¹)) *
          ‖(1 : Mat d)‖)) := by
        rw [observationFillingCoefficient, hnorm]
    _ ≤ max 1 (6 * (d : ℝ) * Real.sqrt d * (3 * ‖(1 : Mat d)‖) *
          Real.sqrt (specBound ((symmPart abar)⁻¹))) :=
        max_le_max (le_refl (1 : ℝ)) hstep
    _ ≤ gaugeSplitFillingConstant d *
          max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹))) :=
        max_one_mul_le_mul_max_one halpha0

/-- The law-free filling constant of the folded provider, at the response
order. -/
@[expose]
def foldedResponseFillingConstant (d : ℕ) (g : ℝ) : ℝ :=
  Real.sqrt (gaugeSplitFillingConstant d *
    (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹)

theorem foldedResponseFillingConstant_nonneg (d : ℕ) (g : ℝ) :
    0 ≤ foldedResponseFillingConstant d g :=
  Real.sqrt_nonneg _

/-- **The response prefactor splits.**  The parent-anchored response prefactor
is below a law-free constant times the truncated square root of the absolute
gauge scale — exactly the truncated gauge power that the absorption of
`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.GaugeMaxPowerFluxFrameAbsorption`
consumes. -/
theorem sqrt_observationFilling_le_gaugeSplit [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {lambda g : ℝ}
    (hlambda0 : 0 < lambda) (hlambda3 : lambda ≤ 3)
    (hbHalf : responseWindowOrder g ≤ 1 / 2) :
    Real.sqrt (observationFillingCoefficient d lambda abar *
        (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹) ≤
      foldedResponseFillingConstant d g *
        max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ (1 / 2 : ℝ)) := by
  have hdisc0 : (0 : ℝ) ≤
      (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹ :=
    inv_nonneg.mpr
      (Book.Ch02.book_geometricDiscount_nonneg
        (mul_nonneg (by linarith only [hbHalf]) (by norm_num)))
  have hKdisc0 : (0 : ℝ) ≤ gaugeSplitFillingConstant d *
      (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹ :=
    mul_nonneg (le_trans zero_le_one (one_le_gaugeSplitFillingConstant d))
      hdisc0
  have hfill := observationFillingCoefficient_le_gaugeSplit hS hlambda0 hlambda3
  have hstep : observationFillingCoefficient d lambda abar *
      (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹ ≤
      (gaugeSplitFillingConstant d *
          (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹) *
        max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹))) := by
    calc observationFillingCoefficient d lambda abar *
        (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹
        ≤ (gaugeSplitFillingConstant d *
            max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)))) *
          (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹ :=
          mul_le_mul_of_nonneg_right hfill hdisc0
      _ = (gaugeSplitFillingConstant d *
            (Book.Ch02.geometricDiscount
              (1 - 2 * responseWindowOrder g) 1)⁻¹) *
          max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹))) := by ring
  refine (Real.sqrt_le_sqrt hstep).trans ?_
  rw [Real.sqrt_mul hKdisc0, foldedResponseFillingConstant]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hmono : Monotone Real.sqrt := fun _ _ hab => Real.sqrt_le_sqrt hab
  rw [hmono.map_max, Real.sqrt_one, Real.sqrt_eq_rpow]

/-! ## The folded provider -/

/-- The law-free exponent of the eccentricity fold that the provider exports. -/
@[expose]
def foldedFrameEccentricityExponent (g kappaRate : ℝ) : ℝ :=
  Certificate.printRowOrder g * max (responseWindowOrder g) kappaRate /
    (2 * kappaRate * kappaRate)

/-- The law-free response constant of the folded provider. -/
@[expose]
def foldedAnchoredResponseConstant (d : ℕ) (g kappaRate delta J : ℝ) : ℝ :=
  foldedResponseFillingConstant d g * Real.sqrt delta *
    frameFoldConstant d g kappaRate J

theorem frameFoldConstant_nonneg (d : ℕ) (g kappaRate J : ℝ) :
    0 ≤ frameFoldConstant d g kappaRate J := by
  have h1 : (1 : ℝ) ≤ max 1 (foldPrefactorBase d g kappaRate) := le_max_left _ _
  have hbase : (0 : ℝ) ≤ 3 * max 1 (foldPrefactorBase d g kappaRate) := by
    linarith only [h1]
  rw [frameFoldConstant, activationFoldConstant]
  exact mul_nonneg (Real.rpow_nonneg hbase _)
    (le_trans zero_le_one (le_max_left _ _))

theorem foldedAnchoredResponseConstant_nonneg (d : ℕ) (g kappaRate delta J : ℝ) :
    0 ≤ foldedAnchoredResponseConstant d g kappaRate delta J := by
  rw [foldedAnchoredResponseConstant]
  exact mul_nonneg
    (mul_nonneg (foldedResponseFillingConstant_nonneg d g) (Real.sqrt_nonneg _))
    (frameFoldConstant_nonneg d g kappaRate J)

/-- **The folded-scale anchored residual frame provider.**  A parallel provider:
the formulaic anchored provider is consumed as a black box and its frame
constant is replaced by a law-free one, at the homogenization length folded by
the eccentricity factor at the law-free exponent
`printRowOrder g * max (responseWindowOrder g) kappaRate / (2 * kappaRate ^ 2)`.

Every hypothesis is one of the original provider's own binders together with the
frozen normalization data (`hcnorm`, `hInner`, `hSandwich`), which the Dirichlet
conjunct supplies at its witness. -/
theorem RowRetainingPrintOrderGoodScale.exists_foldedAnchoredResidualFrameResponseRate
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x epsilon : ℝ}
    (h : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) (hscale : x ≤ epsilon⁻¹)
    {U : Set (Vec d)} {rho Rad r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) (hRad : 0 < Rad)
    (hGauge : U ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹})
    (hresponseOrder : responseWindowOrder g < r)
    (hrateOrder : kappaRate ≤ r)
    (hCflux : 0 ≤ Cflux)
    (aObs : system.CellIndex → Book.Ch03.CoeffFamily d)
    (hObs : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
      fun y ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun z ↦ scaledCoeff epsilon a z - skewPart abar)
        (y + ruledObservationCenter system i))
    {Uphys : Set (Vec d)} {cnorm : ℝ} (hcnorm : 0 < cnorm)
    (hInner : ellipsoid abar cnorm ⊆ Uphys)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ Uphys) rho Rad) :
    ∃ (J : ℕ) (responseBound : system.CellIndex → ℝ),
      2 * Rad ≤ (3 : ℝ) ^ (J : ℤ) ∧
      (3 : ℝ) ^ (J : ℤ) ≤ 1 + 3 * (2 * Rad) ∧
      (∀ i,
        Book.Ch02.HomogenizationErrorOnCube
            (ruledObservationCube system i) (responseWindowOrder g)
            .infinity (.finite 2) (aObs i)
              (identityConstantCoeffMatrix d).matrix ≤ responseBound i) ∧
      PhysicalFluxEpsilonFrameBound system (responseWindowOrder g) r Cflux
        responseBound epsilon
        (x * eccentricityFoldFactor abar
          (foldedFrameEccentricityExponent g kappaRate))
        kappaRate
        (Real.rpow (3 : ℝ) (-responseWindowOrder g) *
          Real.rpow (2 * Rad) (r - responseWindowOrder g) * Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor (responseWindowOrder g) r *
          (foldedAnchoredResponseConstant d g kappaRate h.delta ((J : ℕ) : ℝ) *
            max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)))) := by
  obtain ⟨N, G, J, lambda, deltaScaled, _aScaled, _aRef, L, M, responseBound,
      _Kframe, hlambda, hlambdaRange, _haScaled, hdeltaScaled, _hG, hGupper,
      hLeq, _hLupper, hJ, hJupper, hMeq, _hKframe, _haRef, _hTail, _hLM, _hKM,
      hresponseFormula, hHomError, _hFrame⟩ :=
    h.exists_formulaicAnchoredResidualFrameResponseRate hS hg hkappa hx hepsilon
      hscale system hU hRad hGauge hresponseOrder hrateOrder hCflux aObs hObs
  have hrw3 : ∀ e : ℝ, Real.rpow (3 : ℝ) e = (3 : ℝ) ^ e := fun _ => rfl
  -- the printed orders
  have hg0 : (0 : ℝ) ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hb0 : 0 < responseWindowOrder g := by
    rw [responseWindowOrder]; linarith only [hg0]
  have hbHalf : responseWindowOrder g ≤ 1 / 2 := by
    rw [responseWindowOrder]; linarith only [hg1]
  have hrho : (0 : ℝ) ≤ Certificate.printRowOrder g := by
    rw [Certificate.printRowOrder]; linarith only [hg0]
  -- the geometric gap and the positivity of the absorption prefactor
  have hgeom := one_sub_rpow_neg_gap_pos_responseWindow hg1
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqrtd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hP : 0 < Certificate.shiftedTailAbsorptionPrefactor d
      (responseWindowOrder g) (Certificate.printRowOrder g) G := by
    rw [Certificate.shiftedTailAbsorptionPrefactor]
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hd0) hsqrtd)
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (one_div_pos.mpr hgeom))
  -- the frame exponent folds
  have hGupperR : (3 : ℝ) ^ ((G : ℕ) : ℝ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) := by
    rw [Real.rpow_natCast]
    rwa [zpow_natCast] at hGupper
  have hfold := rpow_three_frameExponent_le_fold (abar := abar) (g := g)
    (kappaRate := kappaRate) (G := G) (L := L) (J := J) (M := M)
    hkappa hrho hgeom hP hLeq hGupperR hMeq
  have hfoldDef : (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
        kappaRate * ((L : ℕ) : ℝ)) ≤
      frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
        (eccentricityFoldFactor abar
          (foldedFrameEccentricityExponent g kappaRate)) ^ kappaRate := by
    rw [foldedFrameEccentricityExponent]
    exact hfold
  -- the microscopic parameter and the amplitude rate
  have hlambda0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambdaRange.1
  have hAmp := sqrt_deltaScaled_le_physicalFrameRate h hkappa hepsilon hlambda
    hlambdaRange hdeltaScaled
  have hfillLe := sqrt_observationFilling_le_gaugeSplit (d := d) hS (g := g)
    hlambda0 hlambdaRange.2 hbHalf
  -- the folded length
  have hF1 : (1 : ℝ) ≤ eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate) :=
    one_le_eccentricityFoldFactor abar _
  have hF0 : (0 : ℝ) ≤ eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate) :=
    le_trans zero_le_one hF1
  have hEX0 : (0 : ℝ) ≤ epsilon * x :=
    mul_nonneg hepsilon.le (le_trans zero_le_one hx)
  have hXfold0 : (0 : ℝ) ≤ epsilon * (x * eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate)) :=
    mul_nonneg hepsilon.le
      (mul_nonneg (le_trans zero_le_one hx) hF0)
  have hsplitRate : (epsilon * (x * eccentricityFoldFactor abar
        (foldedFrameEccentricityExponent g kappaRate))) ^ kappaRate =
      (epsilon * x) ^ kappaRate *
        (eccentricityFoldFactor abar
          (foldedFrameEccentricityExponent g kappaRate)) ^ kappaRate := by
    rw [← mul_assoc, Real.mul_rpow hEX0 hF0]
  have hRHS1 : (0 : ℝ) ≤ foldedResponseFillingConstant d g *
      max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ (1 / 2 : ℝ)) :=
    mul_nonneg (foldedResponseFillingConstant_nonneg d g)
      (le_trans zero_le_one (le_max_left _ _))
  have hRHS2 : (0 : ℝ) ≤ (foldedResponseFillingConstant d g *
        max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ (1 / 2 : ℝ))) *
      (Real.sqrt h.delta * (epsilon * x) ^ kappaRate) :=
    mul_nonneg hRHS1
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hEX0 _))
  -- the cell-anchored rate at the folded length
  have hrate : ∀ i, 0 ≤ responseBound i ∧
      printCellScaleFactor (ruledObservationCube system i)
            (responseWindowOrder g) * responseBound i ≤
        foldedAnchoredResponseConstant d g kappaRate h.delta ((J : ℕ) : ℝ) *
          max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^ (1 / 2 : ℝ)) *
          (epsilon * (x * eccentricityFoldFactor abar
            (foldedFrameEccentricityExponent g kappaRate))) ^ kappaRate := by
    intro i
    refine ⟨?_, ?_⟩
    · rw [hresponseFormula i]
      simp only [hrw3]
      positivity
    · have hprod := printCellScaleFactor_mul_responseBound_eq (d := d) system
        (s := responseWindowOrder g) (deltaScaled := deltaScaled)
        (Cresponse := Real.sqrt (observationFillingCoefficient d lambda abar *
          (Book.Ch02.geometricDiscount
            (1 - 2 * responseWindowOrder g) 1)⁻¹))
        (kappaRate := kappaRate) (M := M) (L := L) responseBound
        hresponseFormula i
      rw [hprod]
      simp only [hrw3]
      have hstep1 : Real.sqrt (observationFillingCoefficient d lambda abar *
            (Book.Ch02.geometricDiscount
              (1 - 2 * responseWindowOrder g) 1)⁻¹) *
          Real.sqrt deltaScaled ≤
          (foldedResponseFillingConstant d g *
              max 1 (Real.sqrt (specBound ((symmPart abar)⁻¹)) ^
                (1 / 2 : ℝ))) *
            (Real.sqrt h.delta * (epsilon * x) ^ kappaRate) :=
        mul_le_mul hfillLe hAmp (Real.sqrt_nonneg _) hRHS1
      have hstep2 := mul_le_mul hstep1 hfoldDef
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) hRHS2
      refine hstep2.trans (le_of_eq ?_)
      rw [hsplitRate, foldedAnchoredResponseConstant]
      ring
  refine ⟨J, responseBound, hJ, hJupper, hHomError, ?_⟩
  exact physicalFluxEpsilonFrameBound_of_gaugeMaxPowerRate (Uphys := Uphys)
    system hS responseBound hU.1 hRad.le hb0 hresponseOrder hCflux hcnorm
    (foldedAnchoredResponseConstant_nonneg d g kappaRate h.delta ((J : ℕ) : ℝ))
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)) hXfold0 hInner hSandwich hrate

end

end RowSupply
end HighContrast
end HCPolySupport
