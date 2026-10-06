/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff
public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure
public import LeanPool.HighContrastHomogenization.Support.PDE.Harmonic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.LocalizedZeroTrace
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# Coarse-graining support: Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.WeakTesting

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

noncomputable section

open scoped ENNReal

private theorem scalarCutoffGradientProductSquareIntegrability
    {d : ℕ} (Q : TriadicCube d) (function : H1Function (openCubeSet Q))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) :
    MemVectorL2 (openCubeSet Q) (fun x => function x • scalarCutoffGradientField η x) := by
  simpa [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul, mul_comm] using
    (MeasureTheory.MemLp.of_eval fun i : Fin d => by
      have hgradη_compact :
          HasCompactSupport (fun x => scalarCutoffGradientField η x i) := by
        simpa [scalarCutoffGradientField] using
          hη_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
      rcases
          memH1_mul_of_contDiff_hasCompactSupport
            (contDiff_scalarCutoffGradientField_component hη i) hgradη_compact
            function.memH1 with
        ⟨v, hv_toFun⟩
      simpa [hv_toFun, mul_comm] using v.memL2)

private theorem harmonicFluxZeroTraceTesting
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (test : H1Function (openCubeSet Q)) (htest : MemH10 (openCubeSet Q) test.toFun) :
    ∫ x in openCubeSet Q,
      vecDot (matVecMul (a x) (w.toH1.grad x)) (test.grad x) ∂MeasureTheory.volume = 0 := by
  let U : Set (Vec d) := openCubeSet Q
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [U, volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  rcases htest with ⟨φ, hφ_toFun⟩
  have hflux_mem : MemVectorL2 U (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
  have hcoord_ae :
      ∀ i : Fin d,
        (fun x => φ.toH1Function.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
          (fun x => test.grad x i) := by
    intro i
    have hφ_loc :
        MeasureTheory.LocallyIntegrableOn (fun x => φ.toH1Function.grad x i)
          U MeasureTheory.volume :=
      MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((φ.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    have htest_loc :
        MeasureTheory.LocallyIntegrableOn (fun x => test.grad x i)
          U MeasureTheory.volume :=
      MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((test.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    have hφ_weak :
        HasWeakPartialDerivOn U i test.toFun
          (fun x => φ.toH1Function.grad x i) := by
      simpa [hφ_toFun] using φ.toH1Function.hasWeakGradient i
    have htest_weak :
        HasWeakPartialDerivOn U i test.toFun (fun x => test.grad x i) :=
      test.hasWeakGradient i
    exact
      HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
        hφ_loc htest_loc hφ_weak htest_weak
  have hcoord_int_test :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x => (matVecMul (a x) (w.toH1.grad x)) i * test.grad x i)
          (MeasureTheory.volume.restrict U) := by
    intro i
    exact
      (memScalarL2_coord_of_memVectorL2 hflux_mem i).integrable_mul
        (test.gradMemL2 i)
  have hcoord_int_φ :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x => (matVecMul (a x) (w.toH1.grad x)) i * φ.toH1Function.grad x i)
          (MeasureTheory.volume.restrict U) := by
    intro i
    exact
      (memScalarL2_coord_of_memVectorL2 hflux_mem i).integrable_mul
        (φ.toH1Function.gradMemL2 i)
  calc
    ∫ x in U,
        vecDot (matVecMul (a x) (w.toH1.grad x)) (test.grad x) ∂MeasureTheory.volume
        =
      ∑ i, ∫ x in U,
        (matVecMul (a x) (w.toH1.grad x)) i * test.grad x i ∂MeasureTheory.volume := by
          rw [show
            (fun x => vecDot (matVecMul (a x) (w.toH1.grad x)) (test.grad x)) =
              fun x => ∑ i, (matVecMul (a x) (w.toH1.grad x)) i * test.grad x i by
                funext x
                simp [vecDot]]
          rw [MeasureTheory.integral_finsetSum]
          intro i hi
          exact hcoord_int_test i
    _ = ∑ i, ∫ x in U,
          (matVecMul (a x) (w.toH1.grad x)) i * φ.toH1Function.grad x i
            ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcoord_ae i] with x hx
          simp [hx]
    _ = ∫ x in U,
          vecDot (matVecMul (a x) (w.toH1.grad x)) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
          symm
          rw [show
            (fun x => vecDot (matVecMul (a x) (w.toH1.grad x)) (φ.toH1Function.grad x)) =
              fun x => ∑ i, (matVecMul (a x) (w.toH1.grad x)) i * φ.toH1Function.grad x i by
                funext x
                simp [vecDot]]
          rw [MeasureTheory.integral_finsetSum]
          intro i hi
          exact hcoord_int_φ i
    _ = 0 := w.isHarmonic.2 φ

/-- The harmonic flux tested against `u ∇η` is integrable on the closed cube.

The weak-testing identity below already proves this internally on the open
cube; this lemma exposes the integrability input needed by descendant
summation. -/
theorem integrableOn_vecDot_harmonicFlux_harmonicFunction_scalarCutoffGradientField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) :
    MeasureTheory.IntegrableOn
      (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x))
      (cubeSet Q) MeasureTheory.volume := by
  let U : Set (Vec d) := openCubeSet Q
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [U, volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hflux_mem :
      MemVectorL2 U (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
  have hpair_vec_mem :
      MemVectorL2 U (fun x => w.toH1 x • scalarCutoffGradientField η x) := by
    exact scalarCutoffGradientProductSquareIntegrability Q w.toH1 hη hη_compact
  have hpair_int :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x))
        U := by
    exact integrableOn_vecDot_of_memVectorL2 hflux_mem hpair_vec_mem
  simpa [U, MeasureTheory.IntegrableOn, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hpair_int

theorem
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_memH10
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η)
    (hw_memH10 : MemH10 (openCubeSet Q) (fun x => η x * w.toH1 x)) :
    ∫ x in openCubeSet Q, η x * scalarVariationEnergyIntegrand a w x ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q,
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume := by
  let U : Set (Vec d) := openCubeSet Q
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [U, volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let wη : H1Function U := w.toH1.mulContDiffHasCompactSupport hη hη_compact
  have hflux_mem :
      MemVectorL2 U (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
  have hprod_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x)) U := by
    exact integrableOn_vecDot_of_memVectorL2 hflux_mem wη.grad_memVectorL2
  have hpair_vec_mem :
      MemVectorL2 U (fun x => w.toH1 x • scalarCutoffGradientField η x) := by
    exact scalarCutoffGradientProductSquareIntegrability Q w.toH1 hη hη_compact
  have hpair_int :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x))
        U := by
    exact integrableOn_vecDot_of_memVectorL2 hflux_mem hpair_vec_mem
  have hsol_wη :
      ∫ x in U,
        vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x) ∂MeasureTheory.volume = 0 := by
    exact harmonicFluxZeroTraceTesting Q a w hEll wη
      (by simpa [wη, H1Function.mulContDiffHasCompactSupport_toFun] using hw_memH10)
  have hprod_split :
      (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x)) =
      (fun x =>
        η x * scalarVariationEnergyIntegrand a w x +
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x)) := by
    funext x
    have henergy :
        vecDot (matVecMul (a x) (w.toH1.grad x)) (w.toH1.grad x) =
          scalarVariationEnergyIntegrand a w x := by
      rw [vecDot_comm, ← vecDot_matVecMul_symmPart (a x) (w.toH1.grad x)]
      rfl
    have hwη_grad :
        wη.grad x = η x • w.toH1.grad x + w.toH1 x • scalarCutoffGradientField η x := by
      ext i
      simp [wη, H1Function.mulContDiffHasCompactSupport_grad, scalarCutoffGradientField,
        Pi.smul_apply, smul_eq_mul]
    calc
      vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x)
          = vecDot (matVecMul (a x) (w.toH1.grad x))
              (η x • w.toH1.grad x + w.toH1 x • scalarCutoffGradientField η x) := by
                rw [hwη_grad]
      _ = vecDot (matVecMul (a x) (w.toH1.grad x)) (η x • w.toH1.grad x) +
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) := by
                rw [vecDot_add_right]
      _ = η x * vecDot (matVecMul (a x) (w.toH1.grad x)) (w.toH1.grad x) +
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) := by
                rw [vecDot_smul_right]
      _ = η x * scalarVariationEnergyIntegrand a w x +
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) := by
                rw [henergy]
  have hweighted_eq :
      (fun x => η x * scalarVariationEnergyIntegrand a w x) =
        (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x) -
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x)) := by
    funext x
    have hx := congrFun hprod_split x
    linarith
  have hweighted_int :
      MeasureTheory.IntegrableOn
        (fun x => η x * scalarVariationEnergyIntegrand a w x) U := by
    have hdiff_int :
        MeasureTheory.IntegrableOn
          (fun x =>
            vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x) -
              vecDot (matVecMul (a x) (w.toH1.grad x))
                (w.toH1 x • scalarCutoffGradientField η x))
          U := by
      simpa [MeasureTheory.IntegrableOn] using! hprod_int.integrable.sub hpair_int.integrable
    simpa [hweighted_eq] using hdiff_int
  have hsum_zero :
      ∫ x in U,
        (η x * scalarVariationEnergyIntegrand a w x +
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x)) ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U,
          (η x * scalarVariationEnergyIntegrand a w x +
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x)) ∂MeasureTheory.volume
          =
        ∫ x in U,
          vecDot (matVecMul (a x) (w.toH1.grad x)) (wη.grad x) ∂MeasureTheory.volume := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => (congrFun hprod_split x).symm
      _ = 0 := hsol_wη
  have hsum_zero' :
      ∫ x in U, η x * scalarVariationEnergyIntegrand a w x ∂MeasureTheory.volume +
        ∫ x in U,
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U, η x * scalarVariationEnergyIntegrand a w x ∂MeasureTheory.volume +
          ∫ x in U,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume
          =
        ∫ x in U,
          (η x * scalarVariationEnergyIntegrand a w x +
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x)) ∂MeasureTheory.volume := by
              symm
              rw [MeasureTheory.integral_add hweighted_int hpair_int]
      _ = 0 := hsum_zero
  linarith

theorem
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ openCubeSet Q) :
    ∫ x in openCubeSet Q, η x * scalarVariationEnergyIntegrand a w x ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q,
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume := by
  exact
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_memH10
      Q a w hEll hη hη_compact
      (memH10_mul_of_contDiff_hasCompactSupport
        (isOpenBoundedConvexDomain_openCubeSet Q) hη hη_compact hη_sub w.toH1.memH1)

theorem
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_aHarmonicFunction
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V w.toH1.toFun)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in openCubeSet Q, η x * scalarVariationEnergyIntegrand a w x ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q,
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume := by
  exact
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_memH10
      Q a w hEll hη hη_compact
      (localizedZeroTraceFunctionOn_memH10_mul hzero hη hη_compact hη_sub)

theorem
    cubeAverage_scalarVariationEnergy_eq_neg_fluxCutoffPairing
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ openCubeSet Q) :
    cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x) =
      -cubeAverage Q (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x)) := by
  have hset :=
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing
      Q a w hEll hη hη_compact hη_sub
  calc
    cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x)
        = (cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, η x * scalarVariationEnergyIntegrand a w x
              ∂MeasureTheory.volume := by
              rfl
    _ = (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q, η x * scalarVariationEnergyIntegrand a w x
            ∂MeasureTheory.volume := by
            rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = (cubeVolume Q)⁻¹ *
          (-∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume) := by
            rw [hset]
    _ = -((cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume) := by
            ring
    _ = -((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume) := by
            rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = -cubeAverage Q (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x)) := by
          rfl

theorem
    cubeAverage_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_aHarmonicFunction
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V w.toH1.toFun)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x) =
      -cubeAverage Q (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x)) := by
  have hset :=
    setIntegral_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_aHarmonicFunction
      Q a w hEll hzero hη hη_compact hη_sub
  calc
    cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x)
        = (cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, η x * scalarVariationEnergyIntegrand a w x
              ∂MeasureTheory.volume := by
              rfl
    _ = (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q, η x * scalarVariationEnergyIntegrand a w x
            ∂MeasureTheory.volume := by
            rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = (cubeVolume Q)⁻¹ *
          (-∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume) := by
            rw [hset]
    _ = -((cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume) := by
            ring
    _ = -((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q,
            vecDot (matVecMul (a x) (w.toH1.grad x))
              (w.toH1 x • scalarCutoffGradientField η x) ∂MeasureTheory.volume) := by
            rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = -cubeAverage Q (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x)) := by
          rfl

theorem
    le_abs_cubeAverage_vectorDot_flux_scalarCutoffGradientField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam F : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ openCubeSet Q)
    (hlower :
      F ≤ cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x)) :
    F ≤
      |cubeAverage Q (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x))| := by
  have havg :=
    cubeAverage_scalarVariationEnergy_eq_neg_fluxCutoffPairing
      Q a w hEll hη hη_compact hη_sub
  calc
    F ≤ cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x) := hlower
    _ = -cubeAverage Q (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x)) := havg
    _ ≤ |cubeAverage Q (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x))| := by
          exact neg_le_abs _

theorem
    le_abs_cubeAverage_vectorDot_flux_scalarCutoffGradientField_of_aHarmonicFunction
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam F : ℝ}
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V w.toH1.toFun)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V)
    (hlower :
      F ≤ cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x)) :
    F ≤
      |cubeAverage Q (fun x =>
        vecDot (matVecMul (a x) (w.toH1.grad x))
          (w.toH1 x • scalarCutoffGradientField η x))| := by
  have havg :=
    cubeAverage_scalarVariationEnergy_eq_neg_fluxCutoffPairing_of_aHarmonicFunction
      Q a w hEll hzero hη hη_compact hη_sub
  calc
    F ≤ cubeAverage Q (fun x => η x * scalarVariationEnergyIntegrand a w x) := hlower
    _ = -cubeAverage Q (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x)) := havg
    _ ≤ |cubeAverage Q (fun x =>
          vecDot (matVecMul (a x) (w.toH1.grad x))
            (w.toH1 x • scalarCutoffGradientField η x))| := by
          exact neg_le_abs _

end

end HCPolySupport
