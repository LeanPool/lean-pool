/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorTelescope
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorDifference
public import LeanPool.HighContrastHomogenization.Provider.Regularity.MultiscaleEllipticityExponentGap
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoli
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.EnergySplit
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSuccessorLocalEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local energy of successive finite affine solutions

This module applies coarse Caccioppoli on a centered parent cube.  Its honest
core is the centered cube two scales below.  The parent value oscillation is
controlled by the two adjacent finite-corrector slope errors, while the local
good-pair condition bounds the Caccioppoli ellipticity factors.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem triadic_cube_ext {d : ℕ} {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) (hindex : Q.index = R.index) : Q = R := by
  cases Q
  cases R
  cases hscale
  cases hindex
  rfl

private theorem centralDescendant_originCube_two {d : ℕ} (m : ℤ) :
    CubeCalderonZygmund.centralDescendant (originCube d m) 2 =
      originCube d (m - 2) := by
  apply triadic_cube_ext
  · simp [CubeCalderonZygmund.centralDescendant,
      CubeCalderonZygmund.centralChild, originCube]
    omega
  · funext i
    simp [CubeCalderonZygmund.centralDescendant,
      CubeCalderonZygmund.centralChild, originCube]

private theorem originCube_sub_two_mem_descendantsAtDepth {d : ℕ} (m : ℤ) :
    originCube d (m - 2) ∈ descendantsAtDepth (originCube d m) 2 := by
  rw [← centralDescendant_originCube_two (d := d) m]
  exact CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth
    (originCube d m) 2

/-- The successive finite affine difference, restricted to the centered cube
two scales below its harmonic parent. -/
@[expose]
noncomputable def finiteAffineSuccessorDifferenceInnerRestriction
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (e : Vec d) :
    Book.Ch03.CubeSolution (originCube d (m - 2)) a := by
  let Q : TriadicCube d := originCube d m
  let R : TriadicCube d := originCube d (m - 2)
  have hR : R ∈ descendantsAtDepth Q 2 := by
    simpa only [Q, R] using originCube_sub_two_mem_descendantsAtDepth (d := d) m
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  let uQ : Book.Ch03.CubeSolution Q a :=
    finiteAffineSuccessorDifference a m e
  have hfluxQ :
      MemVectorL2 (openCubeSet Q)
        (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (uQ.toH1.grad x)) :=
    Book.Ch02.Solution.flux_memVectorL2 uQ
  have hfluxR :
      MemVectorL2 (openCubeSet R)
        (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x) (uQ.toH1.grad x)) := by
    have hmono := Measure.restrict_mono_set volume hsub
    simpa only [MemVectorL2, volumeMeasureOn] using hfluxQ.mono_measure hmono
  let uR :
      Book.Ch02.Solution (Book.Ch02.cubeDomain R)
        ((a.coeffOn Q).restrictToSubcube hsub) :=
    uQ.restrictOfMemVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hfluxR
  have hCoeff :
      Book.Ch02.CoeffOn.AEEq ((a.coeffOn Q).restrictToSubcube hsub)
        (a.coeffOn R) := by
    exact (a.restrictsTo_of_subset hsub).symm
  exact Book.Ch02.Solution.ofAEEq hCoeff uR

/-- The inner restriction preserves the successive difference's gradient
representative. -/
@[simp] theorem finiteAffineSuccessorDifferenceInnerRestriction_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorDifferenceInnerRestriction a m e).toH1.grad =
      (finiteAffineSuccessorDifference a m e).toH1.grad := by
  rfl

/-- On a centered cube, the coarse Caccioppoli core is exactly the centered
cube two scales below. -/
theorem caccioppoliCoreSet_originCube_eq_openCubeSet_sub_two
    {d : ℕ} (m : ℤ) :
    Book.Ch03.caccioppoliCoreSet (originCube d m)
        (cubeCenter (originCube d m)) =
      openCubeSet (originCube d (m - 2)) := by
  have hcenter : cubeCenter (originCube d m) = (0 : Vec d) := by
    funext i
    simp [cubeCenter, originCube]
  have hsub : openCubeSet (originCube d (m - 2)) ⊆
      openCubeSet (originCube d m) :=
    openCubeSet_subset_of_mem_descendantsAtDepth
      (originCube_sub_two_mem_descendantsAtDepth (d := d) m)
  change openCubeSet (originCube d m) ∩
      Book.Ch03.openCubeAtScale (cubeCenter (originCube d m)) (m - 2) =
    openCubeSet (originCube d (m - 2))
  rw [hcenter, Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube]
  exact Set.inter_eq_right.mpr hsub

/-- The actual inner-cube energy norm of the restricted difference is the
square root of the parent Caccioppoli core energy. -/
theorem finiteAffineSuccessorDifferenceInner_energy_eq_coreEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (e : Vec d) :
    Book.Ch03.h1EnergyNormOnCube (originCube d (m - 2)) a
        (finiteAffineSuccessorDifferenceInnerRestriction a m e).toH1 =
      Real.sqrt
        (Book.Ch03.interiorCaccioppoliCoreEnergy (originCube d m) a
          (cubeCenter (originCube d m))
          (finiteAffineSuccessorDifference a m e)) := by
  let Q : TriadicCube d := originCube d m
  let R : TriadicCube d := originCube d (m - 2)
  have hR : R ∈ descendantsAtDepth Q 2 := by
    simpa only [Q, R] using originCube_sub_two_mem_descendantsAtDepth (d := d) m
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hcoeff :
      (a.coeffOn R).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet R)] (a.coeffOn Q).toCoeffField :=
    a.restrictsTo_of_subset hsub
  have henergy :
      Book.Ch03.localizedCoeffEnergyValue (openCubeSet R) (a.coeffOn R)
          (finiteAffineSuccessorDifferenceInnerRestriction a m e).toH1 =
        Book.Ch03.localizedCoeffEnergyValue (openCubeSet R) (a.coeffOn Q)
          (finiteAffineSuccessorDifference a m e).toH1 := by
    rw [Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity,
      Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity]
    apply Book.Ch03.volumeAverage_eq_of_ae_eq
    filter_upwards [hcoeff] with x hx
    simp only [coefficientEnergyDensity,
      finiteAffineSuccessorDifferenceInnerRestriction_grad, hx]
  unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.interiorCaccioppoliCoreEnergy
  rw [caccioppoliCoreSet_originCube_eq_openCubeSet_sub_two]
  exact congrArg Real.sqrt henergy

private theorem ScalarIdentityGoodTailOnInterval.weakError_pair_le_one
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s : ℝ} {m : ℤ}
    (h : ScalarIdentityGoodTailOnInterval a s 1 m (m + 1)) :
    scalarIdentityWeakError a s m ≤ 1 ∧
      scalarIdentityWeakError a s (m + 1) ≤ 1 := by
  have hm : m ∈ Finset.Icc m (m + 1) := by simp
  have hm1 : m + 1 ∈ Finset.Icc m (m + 1) := by simp
  constructor
  · exact (Finset.single_le_sum
      (fun k _ ↦ scalarIdentityWeakError_nonneg a s k) hm).trans h
  · exact (Finset.single_le_sum
      (fun k _ ↦ scalarIdentityWeakError_nonneg a s k) hm1).trans h

private theorem cubeLpNorm_two_cubeFluctuation_le_two_mul
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have hconst : MemLp (fun _ : Vec d ↦ -cubeAverage Q f)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_const (-cubeAverage Q f)
  have hadd := cubeLpNorm_add_le Q (2 : ℝ≥0∞) f
    (fun _ : Vec d ↦ -cubeAverage Q f) hf hconst (by norm_num)
  have havg : |cubeAverage Q f| ≤ cubeLpNorm Q (2 : ℝ≥0∞) f := by
    simpa only [Real.norm_eq_abs] using norm_cubeAverage_le_cubeLpNorm_two Q f hf
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) f +
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun _ : Vec d ↦ -cubeAverage Q f) := by
      simpa [cubeFluctuation, sub_eq_add_neg] using! hadd
    _ = cubeLpNorm Q (2 : ℝ≥0∞) f + |cubeAverage Q f| := by
      rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
        (c := -cubeAverage Q f) (by norm_num)]
      simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) f +
        cubeLpNorm Q (2 : ℝ≥0∞) f := add_le_add_right havg _
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by ring

private theorem cubeLpNorm_originCube_child_le_descendantCount_mul
    {d : ℕ} (m : ℤ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (m + 1)))) :
    cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f ≤
      ((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d (m + 1)) (2 : ℝ≥0∞) f := by
  have hchild :
      CubeCalderonZygmund.centralDescendant (originCube d (m + 1)) 1 =
        originCube d m := by
    apply triadic_cube_ext
    · simp [CubeCalderonZygmund.centralDescendant,
        CubeCalderonZygmund.centralChild, originCube]
    · funext i
      simp [CubeCalderonZygmund.centralDescendant,
        CubeCalderonZygmund.centralChild, originCube]
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d (m + 1)) 1 (FiniteLpExponent.two) f
  rw [hchild] at hraw
  have htop :
      ENNReal.ofReal (((3 ^ d) ^ 1 : ℕ) : ℝ) *
          eLpNorm f 2 (normalizedCubeMeasure (originCube d (m + 1))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal

private theorem cubeBesovScaleWeight_one_originCube_succ
    {d : ℕ} (m : ℤ) :
    cubeBesovScaleWeight 1 (originCube d m) =
      3 * cubeBesovScaleWeight 1 (originCube d (m + 1)) := by
  unfold cubeBesovScaleWeight
  rw [Real.rpow_neg_one, Real.rpow_neg_one]
  change ((3 : ℝ) ^ m)⁻¹ = 3 * ((3 : ℝ) ^ (m + 1))⁻¹
  rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  field_simp

private theorem finiteAffineSuccessorDifference_toFun_eq_correction_sub
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorDifference a m e).toH1.toFun =
      fun x ↦ (finiteAffineCorrection a (m + 1) e).toH1Function.toFun x -
        (finiteAffineCorrection a m e).toH1Function.toFun x := by
  funext x
  rw [congrFun (finiteAffineSuccessorDifference_toFun a m e) x]
  simp only [finiteAffineCubeSolution, finiteAffineSolution_toH1,
    H1Function.add_toFun, finiteAffineBoundaryH1_toFun]
  ring

private theorem exists_finiteAffineSuccessorDifferenceParentL2EstimateConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d),
        cubeBesovScaleWeight 1 (originCube d m) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (finiteAffineSuccessorDifference a m e).toH1.toFun ≤
          C * (scalarIdentityCorrectedWeakError a s m +
            scalarIdentityCorrectedWeakError a s (m + 1)) * euclideanNorm e := by
  rcases exists_finiteAffineSolutionL2SlopeErrorEstimateConstant_at_error_order
      d s hs hs_lt with ⟨C₀, hC₀, hC₀bound⟩
  let D : ℝ := ((3 ^ d : ℕ) : ℝ)
  let C : ℝ := (1 + 3 * D) * C₀
  have hD_nonneg : 0 ≤ D := by positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by positivity) hC₀
  refine ⟨C, hC, ?_⟩
  intro a m e
  let f₁ : Vec d → ℝ :=
    fun x ↦ (finiteAffineCorrection a (m + 1) e).toH1Function.toFun x
  let f₀ : Vec d → ℝ :=
    fun x ↦ (finiteAffineCorrection a m e).toH1Function.toFun x
  let W : ℝ := cubeBesovScaleWeight 1 (originCube d m)
  let W₁ : ℝ := cubeBesovScaleWeight 1 (originCube d (m + 1))
  let L₁ : ℝ := cubeLpNorm (originCube d (m + 1)) (2 : ℝ≥0∞) f₁
  let L₁r : ℝ := cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f₁
  let L₀ : ℝ := cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f₀
  let E₁ : ℝ := scalarIdentityCorrectedWeakError a s (m + 1)
  let E₀ : ℝ := scalarIdentityCorrectedWeakError a s m
  let N : ℝ := euclideanNorm e
  have hf₁ : MemLp f₁ (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (m + 1))) := by
    exact (finiteAffineCorrection a (m + 1) e).toH1Function.memL2_normalizedCubeMeasure
  have hf₁r : MemLp f₁ (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    have hmem := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d (m + 1)) 1 hf₁
    have hchild :
        CubeCalderonZygmund.centralChild (originCube d (m + 1)) =
          originCube d m := by
      apply triadic_cube_ext
      · simp [CubeCalderonZygmund.centralChild, originCube]
      · funext i
        simp [CubeCalderonZygmund.centralChild, originCube]
    change MemLp f₁ (2 : ℝ≥0∞)
      (normalizedCubeMeasure
        (CubeCalderonZygmund.centralChild (originCube d (m + 1)))) at hmem
    simpa only [hchild] using hmem
  have hf₀ : MemLp f₀ (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) :=
    (finiteAffineCorrection a m e).toH1Function.memL2_normalizedCubeMeasure
  have htri :
      cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
          (finiteAffineSuccessorDifference a m e).toH1.toFun ≤ L₁r + L₀ := by
    have hadd := cubeLpNorm_add_le (originCube d m) (2 : ℝ≥0∞)
      f₁ (fun x ↦ -f₀ x) hf₁r hf₀.neg (by norm_num)
    have hneg :
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x ↦ -f₀ x) = L₀ := by
      dsimp [L₀]
      unfold cubeLpNorm
      change
        (MeasureTheory.eLpNorm (-f₀) 2
          (normalizedCubeMeasure (originCube d m))).toReal =
        (MeasureTheory.eLpNorm f₀ 2
          (normalizedCubeMeasure (originCube d m))).toReal
      rw [MeasureTheory.eLpNorm_neg]
    rw [hneg] at hadd
    rw [finiteAffineSuccessorDifference_toFun_eq_correction_sub]
    simpa [f₁, f₀, L₁r, sub_eq_add_neg] using hadd
  have hrestrict : L₁r ≤ D * L₁ := by
    simpa [D, L₁r, L₁, f₁] using
      cubeLpNorm_originCube_child_le_descendantCount_mul m f₁ hf₁
  have hW : W = 3 * W₁ := by
    simpa [W, W₁] using cubeBesovScaleWeight_one_originCube_succ (d := d) m
  have hinner : W * L₀ ≤ C₀ * E₀ * N := by
    simpa [W, L₀, E₀, N, f₀, scalarIdentityCorrectedWeakError, mul_assoc] using
      hC₀bound a m e
  have houter : W₁ * L₁ ≤ C₀ * E₁ * N := by
    simpa [W₁, L₁, E₁, N, f₁, scalarIdentityCorrectedWeakError, mul_assoc] using
      hC₀bound a (m + 1) e
  have hW_nonneg : 0 ≤ W := cubeBesovScaleWeight_nonneg 1 _
  have hE₀_nonneg : 0 ≤ E₀ := scalarIdentityCorrectedWeakError_nonneg _ _ _
  have hE₁_nonneg : 0 ≤ E₁ := scalarIdentityCorrectedWeakError_nonneg _ _ _
  have hN_nonneg : 0 ≤ N := euclideanNorm_nonneg e
  calc
    W * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
        (finiteAffineSuccessorDifference a m e).toH1.toFun ≤
        W * (L₁r + L₀) := mul_le_mul_of_nonneg_left htri hW_nonneg
    _ = W * L₁r + W * L₀ := by ring
    _ ≤ W * (D * L₁) + C₀ * E₀ * N := by
      exact add_le_add (mul_le_mul_of_nonneg_left hrestrict hW_nonneg) hinner
    _ = (3 * D) * (W₁ * L₁) + C₀ * E₀ * N := by rw [hW]; ring
    _ ≤ (3 * D) * (C₀ * E₁ * N) + C₀ * E₀ * N := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left houter
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hD_nonneg))
        (le_refl (C₀ * E₀ * N))
    _ ≤ (1 + 3 * D) * C₀ * (E₀ + E₁) * N := by
      calc
        (3 * D) * (C₀ * E₁ * N) + C₀ * E₀ * N =
            (C₀ * N) * ((3 * D) * E₁ + E₀) := by ring
        _ ≤ (C₀ * N) * ((1 + 3 * D) * (E₀ + E₁)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀.le hN_nonneg)
          calc
            (3 * D) * E₁ + E₀ ≤
                (3 * D) * E₁ + E₀ + (E₁ + (3 * D) * E₀) :=
              le_add_of_nonneg_right
                (add_nonneg hE₁_nonneg
                  (mul_nonneg (mul_nonneg (by norm_num) hD_nonneg) hE₀_nonneg))
            _ = (1 + 3 * D) * (E₀ + E₁) := by ring
        _ = (1 + 3 * D) * C₀ * (E₀ + E₁) * N := by ring
    _ = C * (scalarIdentityCorrectedWeakError a s m +
        scalarIdentityCorrectedWeakError a s (m + 1)) * euclideanNorm e := by
      rfl

private theorem scalarIdentityGoodPair_ellipticity_bounds
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) {m : ℤ}
    (hgood : ScalarIdentityGoodTailOnInterval a s 1 m (m + 1)) :
    Book.Ch02.LambdaS (originCube d m) r a ≤
        exponentGapFactor s r * (4 * (d : ℝ)) ∧
      (Book.Ch02.lambdaS (originCube d m) r a)⁻¹ ≤
        exponentGapFactor s r * (4 * (d : ℝ)) := by
  let E : ℝ := scalarIdentityWeakError a s m
  have hE_nonneg : 0 ≤ E := scalarIdentityWeakError_nonneg a s m
  have hE_le : E ≤ 1 := hgood.weakError_pair_le_one.1
  have hE_sq : E ^ 2 + 1 ≤ 2 := by
    nlinarith only [hE_nonneg, hE_le]
  have hdim_nonneg : 0 ≤ 2 * (d : ℝ) := by positivity
  have hupperRaw :=
    Book.Ch02.inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      (originCube d m) a hs (by norm_num : (0 : ℝ) < 1)
  have hlowerRaw :=
    Book.Ch02.sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
      (originCube d m) a hs (by norm_num : (0 : ℝ) < 1)
  have hupperTwo :
      Book.Ch02.LambdaSq (originCube d m) s (.finite 2) a ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hupperRaw
  have hlowerTwo :
      (Book.Ch02.lambdaSq (originCube d m) s (.finite 2) a)⁻¹ ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hlowerRaw
  have hgap_nonneg : 0 ≤ exponentGapFactor s r :=
    (exponentGapFactor_pos hs hsr).le
  constructor
  · calc
      Book.Ch02.LambdaS (originCube d m) r a ≤
          exponentGapFactor s r *
            Book.Ch02.LambdaSq (originCube d m) s (.finite 2) a := by
        simpa only [exponentGapFactor] using
          LambdaS_le_exponentGap_mul_LambdaSq_finite_two
            (originCube d m) a hs hsr
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * (E ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hupperTwo hgap_nonneg
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE_sq hdim_nonneg) hgap_nonneg
      _ = exponentGapFactor s r * (4 * (d : ℝ)) := by ring
  · calc
      (Book.Ch02.lambdaS (originCube d m) r a)⁻¹ ≤
          exponentGapFactor s r *
            (Book.Ch02.lambdaSq (originCube d m) s (.finite 2) a)⁻¹ := by
        simpa only [exponentGapFactor] using
          lambdaS_inv_le_exponentGap_mul_lambdaSq_finite_two_inv
            (originCube d m) a hs hsr
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * (E ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hlowerTwo hgap_nonneg
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE_sq hdim_nonneg) hgap_nonneg
      _ = exponentGapFactor s r * (4 * (d : ℝ)) := by ring

private theorem caccioppoliPrefactor_goodPair_le
    {d : ℕ} [NeZero d] {C₀ s r : ℝ}
    (hC₀ : 0 < C₀) (hs : 0 < s) (hsr : s < r) (hr_lt : r < 1 / 2)
    {a : Book.Ch02.TriadicCoeffFamily d} {m : ℤ}
    (hgood : ScalarIdentityGoodTailOnInterval a s 1 m (m + 1)) :
    let D : ℝ := exponentGapFactor s r * (4 * (d : ℝ))
    let α : ℝ := r / (1 - 2 * r)
    let K : ℝ :=
      Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
        Real.rpow r (-(2 * r / (1 - 2 * r))) *
        Real.rpow (D * D) α * D
    Book.Ch03.caccioppoliPrefactor C₀ (originCube d m) a r r ≤
      K * (cubeBesovScaleWeight 1 (originCube d m)) ^ 2 := by
  dsimp
  let D : ℝ := exponentGapFactor s r * (4 * (d : ℝ))
  let α : ℝ := r / (1 - 2 * r)
  have hr : 0 < r := hs.trans hsr
  have hden : 0 < 1 - 2 * r := by
    linarith only [hr_lt]
  have hD : 0 < D := by
    dsimp [D]
    have hd : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (exponentGapFactor_pos hs hsr) (mul_pos (by norm_num) hd)
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hr.le hden.le
  obtain ⟨hLambda, hlambda⟩ := scalarIdentityGoodPair_ellipticity_bounds
    (d := d) hs hsr hgood
  have hLambda_nonneg :
      0 ≤ Book.Ch02.LambdaS (originCube d m) r a := by
    unfold Book.Ch02.LambdaS
    exact Book.Ch02.LambdaSq_finite_nonneg _ _ hr (by norm_num)
  have hlambda_inv_nonneg :
      0 ≤ (Book.Ch02.lambdaS (originCube d m) r a)⁻¹ := by
    exact inv_nonneg.mpr (by
      unfold Book.Ch02.lambdaS
      exact Book.Ch02.lambdaSq_finite_nonneg _ _ hr (by norm_num))
  have hTheta_nonneg :
      0 ≤ Book.Ch02.ThetaRatio (originCube d m) r r a := by
    unfold Book.Ch02.ThetaRatio
    exact div_nonneg hLambda_nonneg (by
      unfold Book.Ch02.lambdaS
      exact Book.Ch02.lambdaSq_finite_nonneg _ _ hr (by norm_num))
  have hTheta :
      Book.Ch02.ThetaRatio (originCube d m) r r a ≤ D * D := by
    unfold Book.Ch02.ThetaRatio
    rw [div_eq_mul_inv]
    exact mul_le_mul hLambda hlambda hlambda_inv_nonneg hD.le
  have hThetaPow := Real.rpow_le_rpow hTheta_nonneg hTheta hα
  have hfront_nonneg :
      0 ≤ Real.rpow (C₀ / (1 - 2 * r))
          (2 + 4 * r / (1 - 2 * r)) *
        Real.rpow r (-(2 * r / (1 - 2 * r))) := by
    exact mul_nonneg
      (Real.rpow_nonneg (div_nonneg hC₀.le hden.le) _)
      (Real.rpow_nonneg hr.le _)
  have hscale_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-2 * (((originCube d m).scale : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hscale :
      Real.rpow (3 : ℝ) (-2 * (((originCube d m).scale : ℤ) : ℝ)) =
        (cubeBesovScaleWeight 1 (originCube d m)) ^ 2 := by
    calc
      Real.rpow (3 : ℝ) (-2 * (((originCube d m).scale : ℤ) : ℝ)) =
          cubeBesovScaleWeight 2 (originCube d m) := by
        simpa using Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight
          (originCube d m) (2 : ℝ)
      _ = cubeBesovScaleWeight 1 (originCube d m) *
          cubeBesovScaleWeight 1 (originCube d m) := by
        rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        norm_num
      _ = (cubeBesovScaleWeight 1 (originCube d m)) ^ 2 := by ring
  have hscale_m :
      Real.rpow (3 : ℝ) (-2 * (m : ℝ)) =
        (cubeBesovScaleWeight 1 (originCube d m)) ^ 2 := by
    simpa using! hscale
  have hscale_m_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-2 * (m : ℝ)) := by
    simpa using! hscale_nonneg
  unfold Book.Ch03.caccioppoliPrefactor
  rw [show 1 - r - r = 1 - 2 * r by ring]
  change
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (Book.Ch02.ThetaRatio (originCube d m) r r a) α *
          Book.Ch02.LambdaS (originCube d m) r a *
          Real.rpow (3 : ℝ) (-2 * (m : ℝ)) ≤
      (Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (D * D) α * D) *
        (cubeBesovScaleWeight 1 (originCube d m)) ^ 2
  rw [← hscale_m]
  calc
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
            Real.rpow r (-(2 * r / (1 - 2 * r))) *
            Real.rpow (Book.Ch02.ThetaRatio (originCube d m) r r a) α *
            Book.Ch02.LambdaS (originCube d m) r a *
            Real.rpow (3 : ℝ) (-2 * (m : ℝ)) ≤
        Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
            Real.rpow r (-(2 * r / (1 - 2 * r))) *
            Real.rpow (D * D) α *
            Book.Ch02.LambdaS (originCube d m) r a *
            Real.rpow (3 : ℝ) (-2 * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hThetaPow hfront_nonneg)
          hLambda_nonneg)
        hscale_m_nonneg
    _ ≤ Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (D * D) α * D *
          Real.rpow (3 : ℝ) (-2 * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLambda
          (mul_nonneg hfront_nonneg
            (Real.rpow_nonneg (mul_nonneg hD.le hD.le) _)))
        hscale_m_nonneg

/-- There is a dimension-and-order constant controlling the actual weighted
energy of the successive finite affine difference on `Q_(m-2)`.  The only
coefficient premise is the two-scale unit good-tail bound. -/
theorem exists_finiteAffineSuccessorDifferenceLocalEnergyEstimateConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d),
        ScalarIdentityGoodTailOnInterval a s 1 m (m + 1) →
          Book.Ch03.h1EnergyNormOnCube (originCube d (m - 2)) a
              (finiteAffineSuccessorDifferenceInnerRestriction a m e).toH1 ≤
            C * (scalarIdentityCorrectedWeakError a s m +
              scalarIdentityCorrectedWeakError a s (m + 1)) * euclideanNorm e := by
  rcases exists_finiteAffineSuccessorDifferenceParentL2EstimateConstant
      d s hs hs_lt with ⟨C₁, hC₁, hparent⟩
  rcases (Book.Ch03.coarseCaccioppoliTheory d).exists_constant with
    ⟨C₀, hC₀, _hboundary, hinterior⟩
  let r : ℝ := (s + 1 / 2) / 2
  have hsr : s < r := by
    dsimp only [r]
    linarith only [hs_lt]
  have hr : 0 < r := hs.trans hsr
  have hr_lt : r < 1 / 2 := by
    dsimp only [r]
    linarith only [hs_lt]
  let D : ℝ := exponentGapFactor s r * (4 * (d : ℝ))
  let α : ℝ := r / (1 - 2 * r)
  let K : ℝ :=
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
      Real.rpow r (-(2 * r / (1 - 2 * r))) *
      Real.rpow (D * D) α * D
  let C : ℝ := 2 * Real.sqrt K * C₁
  have hden : 0 < 1 - 2 * r := by
    linarith only [hr_lt]
  have hD : 0 < D := by
    dsimp [D]
    have hd : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (exponentGapFactor_pos hs hsr) (mul_pos (by norm_num) hd)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos
      (mul_pos
        (mul_pos
          (Real.rpow_pos_of_pos (div_pos hC₀ hden) _)
          (Real.rpow_pos_of_pos hr _))
        (Real.rpow_pos_of_pos (mul_pos hD hD) _))
      hD
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hK)) hC₁
  refine ⟨C, hC, ?_⟩
  intro a m e hgood
  let Q : TriadicCube d := originCube d m
  let u : Book.Ch03.CubeSolution Q a := finiteAffineSuccessorDifference a m e
  let W : ℝ := cubeBesovScaleWeight 1 Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.toH1.toFun
  let E : ℝ := scalarIdentityCorrectedWeakError a s m +
    scalarIdentityCorrectedWeakError a s (m + 1)
  let N : ℝ := euclideanNorm e
  have hW_nonneg : 0 ≤ W := cubeBesovScaleWeight_nonneg 1 Q
  have hL_nonneg : 0 ≤ L := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  have hE_nonneg : 0 ≤ E := add_nonneg
    (scalarIdentityCorrectedWeakError_nonneg a s m)
    (scalarIdentityCorrectedWeakError_nonneg a s (m + 1))
  have hN_nonneg : 0 ≤ N := euclideanNorm_nonneg e
  have hpref : Book.Ch03.caccioppoliPrefactor C₀ Q a r r ≤
      K * W ^ 2 := by
    simpa [Q, W, D, α, K] using
      caccioppoliPrefactor_goodPair_le hC₀ hs hsr hr_lt hgood
  have huMem : MemLp u.toH1.toFun (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := u.toH1.memL2_normalizedCubeMeasure
  have hfluctuation :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun) ≤
        2 * L := by
    simpa [L] using cubeLpNorm_two_cubeFluctuation_le_two_mul Q u.toH1.toFun huMem
  have hoscEq :
      Book.Ch03.interiorCaccioppoliParentOscillationL2Sq Q a u =
        (cubeLpNorm Q (2 : ℝ≥0∞)
          (cubeFluctuation Q u.toH1.toFun)) ^ 2 := by
    unfold Book.Ch03.interiorCaccioppoliParentOscillationL2Sq
    simpa [cubeFluctuation, Book.Ch01.Legacy.normalizedAverage] using!
      Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q
        (cubeFluctuation Q u.toH1.toFun) (huMem.sub (memLp_const _))
  have hosc :
      Book.Ch03.interiorCaccioppoliParentOscillationL2Sq Q a u ≤
        4 * L ^ 2 := by
    rw [hoscEq]
    have hfluctuation_nonneg := cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (cubeFluctuation Q u.toH1.toFun)
    nlinarith only [hfluctuation, hfluctuation_nonneg]
  have hcore := hinterior u hr hr (by linarith only [hr_lt] : r + r < 1)
  have hcoreBound :
      Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
        4 * K * (W * L) ^ 2 := by
    calc
      Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
          Book.Ch03.interiorCaccioppoliRHS C₀ Q a r r u := hcore
      _ = Book.Ch03.caccioppoliPrefactor C₀ Q a r r *
          Book.Ch03.interiorCaccioppoliParentOscillationL2Sq Q a u := rfl
      _ ≤ (K * W ^ 2) * (4 * L ^ 2) :=
        mul_le_mul hpref hosc
          (Book.Ch03.normalizedL2SqOnSet_nonneg (openCubeSet Q)
            (cubeFluctuation Q u.toH1.toFun) (measurableSet_openCubeSet Q))
          (mul_nonneg hK.le (sq_nonneg W))
      _ = 4 * K * (W * L) ^ 2 := by ring
  have hWL : W * L ≤ C₁ * E * N := by
    simpa [Q, u, W, L, E, N] using hparent a m e
  have hright_nonneg : 0 ≤ 2 * Real.sqrt K * (W * L) := by positivity
  have hroot :
      Real.sqrt
          (Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u) ≤
        2 * Real.sqrt K * (W * L) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨hright_nonneg, ?_⟩
    calc
      Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
          4 * K * (W * L) ^ 2 := hcoreBound
      _ = (2 * Real.sqrt K * (W * L)) ^ 2 := by
        calc
          4 * K * (W * L) ^ 2 =
              4 * (Real.sqrt K) ^ 2 * (W * L) ^ 2 := by
            rw [Real.sq_sqrt hK.le]
          _ = (2 * Real.sqrt K * (W * L)) ^ 2 := by ring
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d (m - 2)) a
        (finiteAffineSuccessorDifferenceInnerRestriction a m e).toH1 =
        Real.sqrt
          (Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u) := by
      simpa [Q, u] using
        finiteAffineSuccessorDifferenceInner_energy_eq_coreEnergy a m e
    _ ≤ 2 * Real.sqrt K * (W * L) := hroot
    _ ≤ 2 * Real.sqrt K * (C₁ * E * N) := by
      exact mul_le_mul_of_nonneg_left hWL (by positivity)
    _ = C * (scalarIdentityCorrectedWeakError a s m +
        scalarIdentityCorrectedWeakError a s (m + 1)) * euclideanNorm e := by
      dsimp [C, E, N]
      ring

end

end HighContrast
end HCPolySupport
