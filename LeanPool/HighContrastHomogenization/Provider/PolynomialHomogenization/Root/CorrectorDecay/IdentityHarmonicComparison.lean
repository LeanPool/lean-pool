/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationHarmonicComparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicReplacement
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedAnalyticGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedHarmonicReplacement
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.BlockExcessHomogenizationError
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.Energy
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.Response
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.RHSCorrections
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.QTwo

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityHarmonicComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# Common-scale rounded harmonic comparison
The physical rounded response row is first identified exactly with the
canonical response row of the rounded coefficient and rounded constant
matrix.  The finite `q = 2` recurrence then feeds the already selected
common-scale dual comparison without changing the printed order or scale
normalization.
-/
namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator
noncomputable section
private theorem cubeBesovNegativeVectorSeminormTwo_le_responseError
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch03.CoeffFamily d) (a0 : Mat d) (s : ℝ) (hs : 0 < s)
    (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : IntegrableOn energy (cubeSet Q) volume)
    (hresp : CubeAverageFluxResponseControl Q
      (Book.Ch03.publicCoeffField Q a) a0 defect energy) :
    cubeBesovNegativeVectorSeminormTwo Q s defect ≤
      Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.sqrt ((4 : ℝ) * matNorm a0) *
          Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 *
            Real.sqrt (cubeAverage Q energy) := by
  let coeff : ℕ → ℝ := fun n ↦
    Book.Ch02.geometricWeight s 2 n *
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        Q (Q.scale - (n : ℤ)) a a0
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hdisc_nonneg : 0 ≤ Book.Ch02.geometricDiscount s 2 :=
    (Book.Ch02.book_geometricDiscount_pos hs2).le
  have hconst_nonneg : 0 ≤ (4 : ℝ) * matNorm a0 :=
    mul_nonneg (by norm_num) (matNorm_nonneg a0)
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hhom_nonneg : 0 ≤
      Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    apply Real.rpow_nonneg
    refine tsum_nonneg ?_
    intro n
    refine mul_nonneg ?_ ?_
    · simpa only [Book.Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg n (by nlinarith only [hs.le])
    · exact Real.rpow_nonneg
        (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
          (sub_le_self _ (Nat.cast_nonneg n)) a a0) _
  have hsum : Summable coeff := by
    simpa only [coeff] using
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 hs
  have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ coeff n := by
    intro n
    dsimp only [coeff]
    exact mul_nonneg
      (by simpa only [Book.Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg n (by nlinarith only [hs.le]))
      (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (sub_le_self _ (Nat.cast_nonneg n)) a a0)
  let B : ℝ :=
    Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
      Real.sqrt ((4 : ℝ) * matNorm a0) *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 *
          Real.sqrt (cubeAverage Q energy)
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hdisc_nonneg _)
          (Real.sqrt_nonneg _)) hhom_nonneg)
      (Real.sqrt_nonneg _)
  change cubeBesovNegativeVectorSeminormTwo Q s defect ≤ B
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s defect ?_
  intro N
  have hdepth : ∀ j ∈ Finset.range (N + 1),
      cubeBesovNegativeVectorDepthAverage Q defect j ≤
        ((4 : ℝ) * matNorm a0 *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            Q (Q.scale - (j : ℤ)) a a0) * cubeAverage Q energy := by
    intro j _hj
    have havg := cubeBesovNegativeVectorDepthAverage_le_fluxResponseEnergy
      (Book.Ch03.publicCoeffField Q a) a0 defect energy
        henergy_nonneg henergy_int hresp j
    rw [Book.Ch03.maxDescendantNormalizedBlockResponseAtScale_publicCoeffField_eq_ch02
      a Q (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) a0] at havg
    exact havg
  have hpartial_sq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N defect) ^ 2 ≤
        (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            Finset.sum (Finset.range (N + 1)) coeff * cubeAverage Q energy := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N defect) ^ 2 ≤
          ∑ j ∈ Finset.range (N + 1),
            (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              (((4 : ℝ) * matNorm a0 *
                Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
                  Q (Q.scale - (j : ℤ)) a a0) * cubeAverage Q energy) :=
        sq_cubeBesovNegativeVectorPartialSeminormTwo_le_of_depthAverage_le
          Q s N defect hdepth
      _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            Finset.sum (Finset.range (N + 1)) coeff * cubeAverage Q energy := by
        calc
          ∑ j ∈ Finset.range (N + 1),
              (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                (((4 : ℝ) * matNorm a0 *
                  Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
                    Q (Q.scale - (j : ℤ)) a a0) * cubeAverage Q energy) =
            ∑ j ∈ Finset.range (N + 1),
              (Book.Ch02.geometricDiscount s 2)⁻¹ *
                ((4 : ℝ) * matNorm a0) * coeff j * cubeAverage Q energy := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hweight :
                (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
                  (Book.Ch02.geometricDiscount s 2)⁻¹ *
                    Book.Ch02.geometricWeight s 2 j := by
              calc
                (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
                    Real.rpow (3 : ℝ) ((-s * (j : ℝ)) * 2) := by
                  simpa [Real.rpow_natCast] using
                    (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                      (-s * (j : ℝ)) (2 : ℝ)).symm
                _ = Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by ring_nf
                _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
                    Book.Ch02.geometricWeight s 2 j :=
                  by simpa only [Book.Ch02.geometricDiscount_eq_old,
                      Book.Ch02.geometricWeight_eq_old] using
                    rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two
                      hs j
            rw [hweight]
            dsimp only [coeff]
            ring
          _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
              ((4 : ℝ) * matNorm a0) *
                Finset.sum (Finset.range (N + 1)) coeff * cubeAverage Q energy := by
            rw [Finset.mul_sum, Finset.sum_mul]
  have hfinite : Finset.sum (Finset.range (N + 1)) coeff ≤ ∑' n, coeff n :=
    hsum.sum_le_tsum _ (fun n _hn ↦ hcoeff_nonneg n)
  have hpartial_sq' :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N defect) ^ 2 ≤
        (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            (∑' n, coeff n) * cubeAverage Q energy := by
    exact hpartial_sq.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfinite
        (mul_nonneg (inv_nonneg.mpr hdisc_nonneg) hconst_nonneg))
      henergy_avg_nonneg)
  have hhom_sq :
      (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 =
        ∑' n, coeff n := by
    simpa only [coeff] using
      Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0
  have hB_sq : B ^ 2 =
      (Book.Ch02.geometricDiscount s 2)⁻¹ *
        ((4 : ℝ) * matNorm a0) *
          (∑' n, coeff n) * cubeAverage Q energy := by
    dsimp only [B]
    calc
      (Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
          Real.sqrt ((4 : ℝ) * matNorm a0) *
            Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 *
              Real.sqrt (cubeAverage Q energy)) ^ 2 =
        (Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 *
          (Real.sqrt ((4 : ℝ) * matNorm a0)) ^ 2 *
            (Book.Ch02.HomogenizationErrorOnCube Q s .infinity
              (.finite 2) a a0) ^ 2 *
                (Real.sqrt (cubeAverage Q energy)) ^ 2 := by ring
      _ = (Book.Ch02.geometricDiscount s 2)⁻¹ *
          ((4 : ℝ) * matNorm a0) *
            (∑' n, coeff n) * cubeAverage Q energy := by
        rw [sq_rpow_neg_half_eq_inv_of_nonneg hdisc_nonneg,
          Real.sq_sqrt hconst_nonneg, Real.sq_sqrt henergy_avg_nonneg,
          hhom_sq]
  rw [← hB_sq] at hpartial_sq'
  have habs := sq_le_sq.mp hpartial_sq'
  simpa only [abs_of_nonneg
      (cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N defect),
    abs_of_nonneg hB_nonneg] using habs
private theorem cubeLpNorm_originCube_pred_le_card_mul_printOrder
    {d : ℕ} (m : ℤ) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))) :
    cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f ≤
      ((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f := by
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d m) 1 FiniteLpExponent.two f
  rw [centralDescendant_originCube_eq_originCube_sub] at hraw
  have htop :
      ENNReal.ofReal ((3 ^ d : ℕ) : ℝ) *
          MeasureTheory.eLpNorm f 2
            (normalizedCubeMeasure (originCube d m)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hraw' :
      MeasureTheory.eLpNorm f 2
          (normalizedCubeMeasure (originCube d (m - 1))) ≤
        ENNReal.ofReal ((3 ^ d : ℕ) : ℝ) *
          MeasureTheory.eLpNorm f 2
            (normalizedCubeMeasure (originCube d m)) := by
    simpa using hraw
  have hreal := ENNReal.toReal_mono htop hraw'
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal
private theorem cubeLpNorm_eq_of_ae_eq_on_parent_cube
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {f g : Vec d → ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hfg : f =ᵐ[volumeMeasureOn (cubeSet Q)] g) :
    cubeLpNorm R (2 : ℝ≥0∞) f = cubeLpNorm R (2 : ℝ≥0∞) g := by
  have hvol : f =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] g := by
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (cubeSet_subset_of_mem_descendantsAtDepth hR)
      (by simpa only [volumeMeasureOn] using! hfg)
  have hnorm : f =ᵐ[normalizedCubeMeasure R] g := by
    simpa only [normalizedCubeMeasure, cubeMeasure] using!
      MeasureTheory.Measure.ae_smul_measure hvol
        (ENNReal.ofReal ((cubeVolume R)⁻¹))
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae hnorm]
private theorem
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d} (s : ℝ)
    (hFG : F =ᵐ[volumeMeasureOn (cubeSet Q)] G) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact Book.Ch03.cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet
    s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (hFG.fun_comp fun z ↦ z i)

private theorem identity_flux_defect_dual_le_response_error
    {d : ℕ} [NeZero d] {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo
        (originCube d m) (printCertificateOrder g)
        (fluxDefect (Book.Ch03.publicCoeffField (originCube d m) a) (1 : Mat d) u.grad) ≤
      ((d : ℝ) * Real.rpow 3 ((d : ℝ) + printCertificateOrder g) *
        (Real.rpow (Book.Ch02.geometricDiscount (printCertificateOrder g) 2)
          (-1 / 2 : ℝ) * Real.sqrt ((4 : ℝ) * matNorm (1 : Mat d)))) *
        scalarIdentityWeakError a (printCertificateOrder g) m *
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a u := by
  let s : ℝ := printCertificateOrder g
  let Q := originCube d m
  let a0 := identityConstantCoeffMatrix d
  let E := scalarIdentityWeakError a s m
  let A := Book.Ch03.h1EnergyNormOnCube Q a u
  let F := fluxDefect (Book.Ch03.publicCoeffField Q a) (1 : Mat d) u.grad
  let Kr : ℝ := Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
    Real.sqrt ((4 : ℝ) * matNorm (1 : Mat d))
  let Kd : ℝ := (d : ℝ) * Real.rpow 3 ((d : ℝ) + s)
  let B : ℝ := Kd * Kr
  have hs : 0 < s := (printOrder_margins hg).1
  have hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a
  have huWeak :=
    Book.Ch03.isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (isForcedEquation_zero_of_isWeakSolutionOn u hu)
  let uh : AHarmonicFunction (Book.Ch03.publicCoeffField Q a) (cubeSet Q) :=
    { toH1 := Book.Ch03.publicH1ToCubeSet u
      isHarmonic := ⟨(Book.Ch03.publicH1ToCubeSet u).isPotentialOn, by
        simpa [Book.Ch03.publicH1ToCubeSet_grad] using
          huWeak.residual_solenoidal hEll MeasureTheory.MemLp.zero⟩ }
  let energy := scalarVariationEnergyIntegrand
    (Book.Ch03.publicCoeffField Q a) uh
  let := isFiniteMeasureVolumeMeasureOnCubeSet Q
  have henergy0 : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    exact scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      (cubeSet Q) _ hEll uh
  have henergyInt : IntegrableOn energy (cubeSet Q) volume := by
    exact ResponseLinearIntegrabilityData.energy
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) uh
  have hresp : CubeAverageFluxResponseControl Q
      (Book.Ch03.publicCoeffField Q a) (1 : Mat d) F energy := by
    simpa [F, energy, uh, fluxDefect, Book.Ch03.publicH1ToCubeSet_grad] using!
      cubeAverageFluxResponseControl_of_aHarmonicFunction Q
        (Book.Ch03.publicCoeffField Q a) (1 : Mat d) hEll
        (identityConstantCoeffMatrix d).elliptic
        (identityConstantCoeffMatrix d).isSymm uh
  have hrec := cubeBesovNegativeVectorSeminormTwo_le_responseError
    Q a (1 : Mat d) s hs F energy henergy0 henergyInt hresp
  have henergyFun : energy = coefficientEnergyDensity
      (Book.Ch03.publicCoeffField Q a) u.grad := by
    funext x
    change vecDot ((Book.Ch03.publicH1ToCubeSet u).grad x)
        (matVecMul (symmPart (Book.Ch03.publicCoeffField Q a x))
          ((Book.Ch03.publicH1ToCubeSet u).grad x)) = _
    rw [Book.Ch03.publicH1ToCubeSet_grad]
    rfl
  have henergyEq : Real.sqrt (cubeAverage Q energy) = A := by
    dsimp only [A]
    rw [Book.Ch03.h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField]
    rw [henergyFun]
  rw [henergyEq] at hrec
  have hconcrete : cubeBesovNegativeVectorSeminormTwo Q s F ≤ Kr * E * A := by
    simpa only [Kr, E, scalarIdentityWeakError] using hrec
  have hFmem : MemVectorL2 (cubeSet Q) F := by
    simpa only [Q, F, a0, identityConstantCoeffMatrix_matrix] using
      Book.Ch03.publicH1_fluxDefect_memVectorL2_descendant_cubeSet
        (Q := Q) (R := Q) (a := a) (a0 := a0) (j := 0) u (by simp)
  have hKd : 0 ≤ Kd := by
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hFdual : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
      B * E * A := by
    have hraw :=
      Book.Ch03.normalizedDualNegativeBesovNormTwo_le_constant_mul_negativeBesovSeminormTwo
        Q s F hs hFmem
    rw [Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo,
      Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight] at hraw
    calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
          Kd * cubeBesovNegativeVectorSeminormTwo Q s F := by
            simpa only [Kd] using! hraw
      _ ≤ Kd * (Kr * E * A) := mul_le_mul_of_nonneg_left hconcrete hKd
      _ = B * E * A := by dsimp only [B]; ring
  exact hFdual

/-- In the exact gauge frame the printed finite response recurrence closes
directly against the identity dual regularity theorem.  No rounded reference,
generation, or tolerance occurs in the statement. -/
theorem exists_identityHarmonicComparisonConstant
    (d : ℕ) [NeZero d] (g Cdual : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hdual : PrintOrderIdentityCubeDualRegularityWithConstant d g Cdual) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ)
        (u : H1Function
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
        (hu : IsWeakSolutionOn
          (a.coeffOn (originCube d m)).toCoeffField
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad),
        let W := identityHarmonicReplacementDatum a m u hu
        let E := scalarIdentityWeakError a (printCertificateOrder g) m
        let A := Book.Ch03.h1EnergyNormOnCube (originCube d m) a u
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d m) (printCertificateOrder g)
            (fun x ↦ u.grad x - W.v.grad x) ≤ C * E * A ∧
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d m) (printCertificateOrder g)
            (Book.Ch03.homogenizationComparisonFluxField
              (originCube d m) a (identityConstantCoeffMatrix d) u W.v) ≤
          C * E * A ∧
        cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
            cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
              (fun x ↦ u.toFun x - W.v.toFun x) ≤ C * E * A := by
  let s : ℝ := printCertificateOrder g
  let Kr : ℝ :=
    Real.rpow (Book.Ch02.geometricDiscount s 2) (-1 / 2 : ℝ) *
      Real.sqrt ((4 : ℝ) * matNorm (1 : Mat d))
  let Kd : ℝ := (d : ℝ) * Real.rpow 3 ((d : ℝ) + s)
  let Kg : ℝ := besovExponentLossGap (2 * s) s
  let Kp : ℝ :=
    ((((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
        2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      Real.sqrt ((1 - Real.rpow 3 (-2 * ((1 / 2 : ℝ) - s)))⁻¹))
  let Kc : ℝ := ((3 ^ d : ℕ) : ℝ)
  let B : ℝ := Kd * Kr
  let Cg : ℝ := Cdual * B
  let Cf : ℝ := Cdual * B
  let Cl : ℝ := Kc * Kp * Kg * Cg
  let C : ℝ := max 0 (max Cg (max Cf Cl))
  have hs : 0 < s := by
    simpa only [s] using (printOrder_margins hg).1
  have hCdual : 0 ≤ Cdual := hdual.1
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a m u hu
  let Q := originCube d m
  let a0 := identityConstantCoeffMatrix d
  let W := identityHarmonicReplacementDatum a m u hu
  let E := scalarIdentityWeakError a s m
  let A := Book.Ch03.h1EnergyNormOnCube Q a u
  let F := fluxDefect (Book.Ch03.publicCoeffField Q a) (1 : Mat d) u.grad
  let wdiff : Vec d → Vec d := fun x ↦ u.grad x - W.v.grad x
  have hFdual : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
      B * E * A :=
    identity_flux_defect_dual_le_response_error hg a m u hu
  have hFmem : MemVectorL2 (cubeSet Q) F := by
    simpa only [Q, F, a0, identityConstantCoeffMatrix_matrix] using
      Book.Ch03.publicH1_fluxDefect_memVectorL2_descendant_cubeSet
        (Q := Q) (R := Q) (a := a) (a0 := a0) (j := 0) u (by simp)
  have hWu : W.u = u := by
    simpa only [W] using identityHarmonicReplacementDatum_u a m u hu
  have hpair := W.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
  rw [hWu] at hpair
  have hpot : IsPotentialZeroTraceOn (cubeSet Q) wdiff := by
    simpa only [wdiff, W, Book.Ch03.publicH1ToCubeSet_grad] using hpair.2
  have hsol : IsSolenoidalOn (cubeSet Q) (fun x ↦ wdiff x + F x) := by
    simpa only [wdiff, F, W, identityConstantCoeffMatrix_matrix,
      HCPolySupport.matVecMul_one, Book.Ch03.publicH1ToCubeSet_grad] using
      hpair.comparisonPair_solenoidal
  obtain ⟨hgrad, hflux⟩ := hdual.2 Q hFmem hpot hsol
  have hgrad0 : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff ≤
      Cg * E * A := by
    calc
      _ ≤ Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F := by
        simpa only [s] using hgrad
      _ ≤ Cdual * (B * E * A) := mul_le_mul_of_nonneg_left hFdual hCdual
      _ = Cg * E * A := by dsimp only [Cg]; ring
  have hfluxAE : Book.Ch03.homogenizationComparisonFluxField Q a a0 u W.v
      =ᵐ[volumeMeasureOn (cubeSet Q)] fun x ↦ wdiff x + F x := by
    have hbase :=
      Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
        (Q := Q) (a := a) (a0 := a0) u W.v
    filter_upwards [hbase] with x hx
    rw [hx]
    dsimp only [a0]
    rw [identityConstantCoeffMatrix_matrix]
    dsimp only [wdiff, F]
    unfold fluxComparison fluxDefect
    simp only [HCPolySupport.matVecMul_one]
    abel
  have hflux0 : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u W.v) ≤
      Cf * E * A := by
    rw [cubeScaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
      s hfluxAE]
    calc
      _ ≤ Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F := by
        simpa only [s] using hflux
      _ ≤ Cdual * (B * E * A) := mul_le_mul_of_nonneg_left hFdual hCdual
      _ = Cf * E * A := by dsimp only [Cf]; ring
  obtain ⟨w, hw⟩ := W.zeroTraceDifference
  rw [hWu] at hw
  let wCube := Book.Ch03.publicH10ToCubeSet w
  have hwCube : w.toH1Function.toFun =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x ↦ u.toFun x - W.v.toFun x := by
    simpa [Q, volumeMeasureOn, Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hw
  have hgradCube : wCube.toH1Function.grad =ᵐ[volumeMeasureOn (cubeSet Q)] wdiff := by
    have hgrad := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (Book.Ch02.cubeDomain Q).isOpen
      (u := w.toH1Function) (v := u - W.v) (by
        simpa only [H1Function.sub_toFun] using hw)
    have hgrad' : w.toH1Function.grad =ᵐ[
        volume.restrict (Book.Ch02.cubeDomain Q : Set (Vec d))] wdiff := by
      simpa only [H1Function.sub_grad, wdiff] using hgrad
    simpa only [wCube, Q, Book.Ch03.publicH10ToCubeSet_toH1Function_grad,
      volumeMeasureOn, Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgrad'
  have hdualGrad : cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
      wCube.toH1Function.grad =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff :=
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
      s hgradCube
  have hgap : 0 ≤ Kg :=
    besovExponentLossGap_nonneg hs (by nlinarith only [hs])
  have hneg := (concreteNegativeFromDualExponentLoss_geometric d).2 Q
    wCube.toH1Function.grad (s := 2 * s) (t := s) hs
    (by nlinarith only [hs]) (by
      have hsHalf : s < 1 / 2 := by
        simpa only [s] using (printOrder_margins hg).2.1
      linarith only [hsHalf])
    wCube.toH1Function.grad_memVectorL2
  have hKp : 0 ≤ Kp := by
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
          (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
          (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg d))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)))
      (Real.sqrt_nonneg _)
  have hpoincare :=
    Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
      Q wCube hs (by simpa only [s] using (printOrder_margins hg).2.1)
  have hparent : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ w.toH1Function.toFun x) ≤
      Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff := by
    calc
      _ ≤ Kp * cubeBesovNegativeVectorSeminormTwo Q (2 * s)
          wCube.toH1Function.grad := by
            simpa only [Kp, wCube,
              Book.Ch03.publicH10ToCubeSet_toH1Function_toFun] using hpoincare
      _ ≤ Kp * (1 * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
          wCube.toH1Function.grad) := mul_le_mul_of_nonneg_left hneg hKp
      _ = Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s wdiff := by
        rw [hdualGrad]
        ring
  have hchild : cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
      (fun x ↦ u.toFun x - W.v.toFun x) ≤
      Kc * cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ w.toH1Function.toFun x) := by
    have hdesc : originCube d (m - 1) ∈ descendantsAtDepth Q 1 := by
      simpa only [Q, centralDescendant_originCube_eq_originCube_sub] using!
        CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth Q 1
    rw [← cubeLpNorm_eq_of_ae_eq_on_parent_cube hdesc hwCube]
    simpa only [Kc, Q] using cubeLpNorm_originCube_pred_le_card_mul_printOrder m
      (fun x ↦ w.toH1Function.toFun x)
      (by simpa only [wCube,
          Book.Ch03.publicH10ToCubeSet_toH1Function_toFun,
          H10Function.toOpenCubeSet_toH1Function_toFun] using
        wCube.toOpenCubeSet.toH1Function.memL2_normalizedCubeMeasure)
  have hl20 : cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
        (fun x ↦ u.toFun x - W.v.toFun x) ≤ Cl * E * A := by
    calc
      _ ≤ cubeBesovScaleWeight (1 : ℝ) Q *
          (Kc * cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ w.toH1Function.toFun x)) :=
        mul_le_mul_of_nonneg_left hchild (cubeBesovScaleWeight_nonneg 1 Q)
      _ = Kc * (cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ w.toH1Function.toFun x)) := by ring
      _ ≤ Kc * (Kp * Kg * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q s wdiff) := mul_le_mul_of_nonneg_left hparent (by positivity)
      _ ≤ Kc * (Kp * Kg * (Cg * E * A)) := by gcongr
      _ = Cl * E * A := by dsimp only [Cl]; ring
  have hEA : 0 ≤ E * A := mul_nonneg
    (scalarIdentityWeakError_nonneg a s m)
    (by dsimp [A, Book.Ch03.h1EnergyNormOnCube]; exact Real.sqrt_nonneg _)
  have hCgC : Cg ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCfC : Cf ≤ C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hClC : Cl ≤ C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact hgrad0.trans (by
      rw [mul_assoc Cg, mul_assoc C]
      exact mul_le_mul_of_nonneg_right hCgC hEA)
  · exact hflux0.trans (by
      rw [mul_assoc Cf, mul_assoc C]
      exact mul_le_mul_of_nonneg_right hCfC hEA)
  · exact hl20.trans (by
      rw [mul_assoc Cl, mul_assoc C]
      exact mul_le_mul_of_nonneg_right hClC hEA)

end
end HighContrast
end HCPolySupport
