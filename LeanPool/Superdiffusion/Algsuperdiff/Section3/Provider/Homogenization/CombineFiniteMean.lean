/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Block.CompletedSquares
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.RealStationaryTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdasUpper
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.RelativeComparatorProbe
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.PartitionAverageMoments.Rosenthal
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.QuadraticStability.CauchySchwarz
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.FiniteBasis
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.NormalizedResponseEllipticity
public import LeanPool.Superdiffusion.Support.HighContrast.Variance.Projection

/-!
# CombineFiniteMean

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Corrected finite-corridor mean estimate

This module bounds comparator-centered starred coarse quadratics under the
same-cutoff relative-normalized law. It combines the relative-origin error
comparison with real-stationary descendant averaging.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch02
open _root_.HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
open _root_.HCPolySupport.IndependentSums
open scoped MatrixOrder

noncomputable section

noncomputable def starredComparatorQuadraticRaw
    {d : ℕ} (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d)
    (U : Set (Vec d)) (a : CoeffField d) : ℝ :=
  fullBlockQuadratic
    (CFC.sqrt B *
      (toFullBlockMat (blockReflect (coarseBlockMatrix U a)) -
        toFullBlockMat (blockReflect C)) *
      CFC.sqrt B) q

noncomputable def starredComparatorQuadratic
    {d : ℕ} (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d)
    (U : Set (Vec d)) (a : RegCoeffField d) : ℝ :=
  starredComparatorQuadraticRaw B C q U a.toFun

noncomputable def twoTermSecondFourthBudget (A D : ℝ) : ℝ :=
  2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
    8 *
      ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))

private theorem starredComparatorQuadraticRaw_translation_covariant
    {d : ℕ} (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d) :
    ∀ (U : Set (Vec d)) (z : Vec d) (a : CoeffField d),
      starredComparatorQuadraticRaw B C q (translateSet z U) a =
        starredComparatorQuadraticRaw B C q U (translateCoeffField z a) := by
  intro U z a
  simp only [starredComparatorQuadraticRaw]
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]

private theorem aemeasurable_starredComparatorQuadratic_cubeSet
    {d : ℕ} {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : Book.Ch04.RestrictionLawCarrier P)
    (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d)
    (R : TriadicCube d) :
    AEMeasurable (starredComparatorQuadratic B C q (cubeSet R)) P := by
  let g : FullBlockMat d → ℝ := fun A =>
    fullBlockQuadratic
      (CFC.sqrt B *
        (A.submatrix Sum.swap Sum.swap - toFullBlockMat (blockReflect C)) *
        CFC.sqrt B) q
  have hg : Measurable g := by
    have hcont : Continuous g := by
      dsimp only [g]
      unfold fullBlockQuadratic
      fun_prop
    exact hcont.measurable
  have hA : AEMeasurable
      (fun a : RegCoeffField d =>
        toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun)) P :=
    hP.aemeasurable_coarseFullBlockMatrix_cubeSet R
  refine (hg.comp_aemeasurable hA).congr ?_
  filter_upwards with a
  simp only [Function.comp_apply, starredComparatorQuadratic,
    starredComparatorQuadraticRaw, g, toFullBlockMat_blockReflect]

private theorem exists_localRep_starredComparatorQuadratic_cubeSet
    {d : ℕ} {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : Book.Ch04.RestrictionLawCarrier P)
    (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d)
    (R : TriadicCube d) :
    ∃ Y : RegCoeffField d → ℝ,
      Book.Ch04.IsRestrictionLocalRandomVariable
          (cubeSet R) (measurableSet_cubeSet R) Y ∧
        starredComparatorQuadratic B C q (cubeSet R) =ᵐ[P] Y := by
  let g : FullBlockMat d → ℝ := fun A =>
    fullBlockQuadratic
      (CFC.sqrt B *
        (A.submatrix Sum.swap Sum.swap - toFullBlockMat (blockReflect C)) *
        CFC.sqrt B) q
  have hg : Measurable g := by
    have hcont : Continuous g := by
      dsimp only [g]
      unfold fullBlockQuadratic
      fun_prop
    exact hcont.measurable
  obtain ⟨Ymat, hYmatLocal, hYmat⟩ :=
    Book.Ch04.exists_isRestrictionLocalRandomVariable_ae_eq_coarseFullBlockMatrix_cubeSet
      hP R
  refine ⟨fun a => g (Ymat a), hYmatLocal.comp_measurable hg, ?_⟩
  filter_upwards [hYmat] with a ha
  simp only [starredComparatorQuadratic, starredComparatorQuadraticRaw, g,
    toFullBlockMat_blockReflect]
  rw [ha]

private theorem centeredComparatorQuadratic_integral_bound :
    ∀ {d : ℕ} {P : Ch04.RestrictionCoeffLaw d},
      Annealed.IsStationaryRealR P →
        ∀ (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d) {child parent : ℤ},
          IsProbabilityMeasure P →
            let Q : TriadicCube d := originCube d parent;
            let D : Finset (TriadicCube d) := descendantsAtScale Q child;
            let X : Set (Vec d) → RegCoeffField d → ℝ := starredComparatorQuadratic B C q;
            let mu0 : ℝ := ∫ (a : RegCoeffField d), X (cubeSet (originCube d child)) a ∂P;
            let Z : TriadicCube d → RegCoeffField d → ℝ := fun (R : TriadicCube d) (a : RegCoeffField d) =>
              X (cubeSet R) a - mu0;
            Integrable (X (cubeSet (originCube d child))) P →
              (∀ R ∈ D, R.scale = child) →
                (∀ R ∈ D, Z R = fun (a : RegCoeffField d) => Z (originCube d child) (translateReg (triadicCubeShift R) a)) →
                  ∀ R ∈ D, ∫ (a : RegCoeffField d), Z R a ∂P = (0 : ℝ) := by
  intro d P hstat B C q child _ _ _ _ X mu0 Z hX0Int hScale hComp R hR
  have hXInt : Integrable (X (cubeSet R)) P := by
    have hcompInt :=
      (show MeasurePreserving (translateReg (triadicCubeShift R)) P P from
        ⟨measurable_translateReg (triadicCubeShift R), hstat (triadicCubeShift
          R)⟩).integrable_comp_of_integrable
        hX0Int
    refine hcompInt.congr ?_
    filter_upwards with a
    have h := congrFun (hComp R hR) a
    dsimp only [Z] at h
    exact sub_left_injective h.symm
  have hmean : ∫ a, X (cubeSet R) a ∂P = mu0 := by
    have hgeom : cubeSet R =
        translateSet (triadicCubeShift R) (cubeSet (originCube d child)) := by
      calc
        cubeSet R = translateSet (triadicCubeShift R)
            (cubeSet (originCube d R.scale)) :=
          cubeSet_eq_translateSet_originCube_of_triadicCube R
        _ = translateSet (triadicCubeShift R)
            (cubeSet (originCube d child)) := by rw [hScale R hR]
    rw [hgeom]
    simpa only [X, starredComparatorQuadratic, mu0] using
      Provider.Annealed.integral_comp_toFun_translation_transfer_real
        hstat hX0Int.aestronglyMeasurable
        (starredComparatorQuadraticRaw_translation_covariant B C q)
        (triadicCubeShift R)
  simp only [Z]
  rw [integral_sub hXInt (integrable_const mu0), hmean, integral_const]
  simp

private theorem starredComparatorQuadratic_centeredDescendantSum_root_le
    {d : ℕ} {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : Book.Ch04.RestrictionLawCarrier P)
    (hstat : Provider.Annealed.IsStationaryRealR P)
    (hdep : Book.Ch04.RestrictionUnitRangeDependentLaw P)
    (B : FullBlockMat d) (C : BlockMat d) (q : FullBlockVec d)
    {child parent : ℤ} (hchildParent : child ≤ parent) {K : ℝ}
    (hK : 0 ≤ K)
    (hOriginInt : Integrable
      (fun a =>
        |Book.Ch04.restrictionCenteredOriginObservable P child
          (starredComparatorQuadratic B C q) a| ^ (2 : ℕ)) P)
    (hOriginRoot :
      (∫ a,
        |Book.Ch04.restrictionCenteredOriginObservable P child
          (starredComparatorQuadratic B C q) a| ^ (2 : ℕ) ∂P) ^
          (1 / (2 : ℝ)) ≤ K) :
    Integrable
        (fun a =>
          |∑ R ∈ descendantsAtScale (originCube d parent) child,
            (starredComparatorQuadratic B C q (cubeSet R) a -
              ∫ b, starredComparatorQuadratic B C q
                (cubeSet (originCube d child)) b ∂P)| ^ (2 : ℕ)) P ∧
      (∫ a,
        |∑ R ∈ descendantsAtScale (originCube d parent) child,
          (starredComparatorQuadratic B C q (cubeSet R) a -
            ∫ b, starredComparatorQuadratic B C q
              (cubeSet (originCube d child)) b ∂P)| ^ (2 : ℕ) ∂P) ^
          (1 / (2 : ℝ)) ≤
        Book.Ch04.rosenthalDescendantsAtScaleLpConst d child 2 *
            ((descendantsAtScale (originCube d parent) child).card : ℝ) ^
              (1 / (2 : ℝ)) * K +
          Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d child 2 *
            Real.sqrt
              ((descendantsAtScale (originCube d parent) child).card : ℝ) * K := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d parent
  let D : Finset (TriadicCube d) := descendantsAtScale Q child
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    starredComparatorQuadratic B C q
  let mu0 : ℝ := ∫ a, X (cubeSet (originCube d child)) a ∂P
  let Z : TriadicCube d → RegCoeffField d → ℝ :=
    fun R a => X (cubeSet R) a - mu0
  have hX0Meas : AEMeasurable (X (cubeSet (originCube d child))) P := by
    simpa only [X] using
      aemeasurable_starredComparatorQuadratic_cubeSet
        hP B C q (originCube d child)
  have hZ0Meas : AEMeasurable (Z (originCube d child)) P := by
    simpa only [Z, X, mu0] using! hX0Meas.sub aemeasurable_const
  have hZ0Int : Integrable
      (fun a => |Z (originCube d child) a| ^ (2 : ℕ)) P := by
    simpa only [Z, X, mu0, Book.Ch04.restrictionCenteredOriginObservable]
      using hOriginInt
  have hZ0Mem : MemLp (Z (originCube d child)) (2 : ENNReal) P := by
    rw [memLp_two_iff_integrable_sq hZ0Meas.aestronglyMeasurable]
    refine hZ0Int.congr ?_
    filter_upwards with a
    rw [sq_abs]
  have hZ0L1 : Integrable (Z (originCube d child)) P :=
    hZ0Mem.integrable (by norm_num)
  have hX0Int : Integrable (X (cubeSet (originCube d child))) P := by
    have heq : X (cubeSet (originCube d child)) =
        fun a => Z (originCube d child) a + mu0 := by
      funext a
      simp [Z, mu0]
    rw [heq]
    exact hZ0L1.add (integrable_const mu0)
  have hScale : ∀ R ∈ D, R.scale = child := by
    intro R hR
    exact Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube
      hchildParent (by simpa only [D, Q] using hR)
  have hComp : ∀ R ∈ D,
      Z R = fun a => Z (originCube d child) (translateReg (triadicCubeShift R) a) := by
    intro R hR
    funext a
    have hgeom : cubeSet R =
        translateSet (triadicCubeShift R) (cubeSet (originCube d child)) := by
      calc
        cubeSet R = translateSet (triadicCubeShift R)
            (cubeSet (originCube d R.scale)) :=
          cubeSet_eq_translateSet_originCube_of_triadicCube R
        _ = translateSet (triadicCubeShift R)
            (cubeSet (originCube d child)) := by rw [hScale R hR]
    dsimp only [Z, X]
    rw [hgeom]
    exact congrArg (fun t : ℝ => t - mu0)
      (starredComparatorQuadraticRaw_translation_covariant
        B C q (cubeSet (originCube d child)) (triadicCubeShift R) a.toFun)
  have hZMeas : ∀ R ∈ D, AEMeasurable (Z R) P := by
    intro R hR
    simpa only [Z, X] using!
      (aemeasurable_starredComparatorQuadratic_cubeSet hP B C q R).sub
        aemeasurable_const
  have hZInt : ∀ R ∈ D,
      Integrable (fun a => |Z R a| ^ (2 : ℕ)) P := by
    intro R hR
    have hcompInt :=
      (show MeasurePreserving (translateReg (triadicCubeShift R)) P P from
        ⟨measurable_translateReg (triadicCubeShift R), hstat (triadicCubeShift
          R)⟩).integrable_comp_of_integrable
        hZ0Int
    refine hcompInt.congr ?_
    filter_upwards with a
    simp only [Function.comp_apply, hComp R hR]
  have hZMean := @centeredComparatorQuadratic_integral_bound (d) (P) (hstat) (B) (C) (q) (child)
    (parent) (this) (hX0Int) (hScale) (hComp)
  have hZRoot : ∀ R ∈ D,
      (∫ a, |Z R a| ^ (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤ K := by
    intro R hR
    have hIntegral : ∫ a, |Z R a| ^ (2 : ℕ) ∂P =
        ∫ a, |Z (originCube d child) a| ^ (2 : ℕ) ∂P := by
      calc
        ∫ a, |Z R a| ^ (2 : ℕ) ∂P =
            ∫ a, |Z (originCube d child)
              (translateReg (triadicCubeShift R) a)| ^ (2 : ℕ) ∂P := by
          apply integral_congr_ae
          filter_upwards with a
          rw [congrFun (hComp R hR) a]
        _ = ∫ a, |Z (originCube d child) a| ^ (2 : ℕ) ∂P :=
          integral_comp_eq_of_map_eq
            (measurable_translateReg (triadicCubeShift R))
            (hstat (triadicCubeShift R)) _
            hZ0Int.aestronglyMeasurable
    rw [hIntegral]
    simpa only [Z, X, mu0, Book.Ch04.restrictionCenteredOriginObservable]
      using hOriginRoot
  let Y : TriadicCube d → RegCoeffField d → ℝ := fun R =>
    Classical.choose
      (exists_localRep_starredComparatorQuadratic_cubeSet hP B C q R)
  let Zlocal : TriadicCube d → RegCoeffField d → ℝ :=
    fun R a => Y R a - mu0
  have hZEq : ∀ R, Z R =ᵐ[P] Zlocal R := by
    intro R
    have hYeq :=
      (Classical.choose_spec
        (exists_localRep_starredComparatorQuadratic_cubeSet hP B C q R)).2
    filter_upwards [hYeq] with a ha
    simp only [Z, X, Zlocal, Y, ha]
  have hZlocalLocal : ∀ R ∈ D,
      Book.Ch04.IsRestrictionLocalRandomVariable
        (cubeSet R) (measurableSet_cubeSet R) (Zlocal R) := by
    intro R hR
    have hYLocal :=
      (Classical.choose_spec
        (exists_localRep_starredComparatorQuadratic_cubeSet hP B C q R)).1
    simpa only [Zlocal, Y] using hYLocal.sub measurable_const
  have hZlocalMeas : ∀ R ∈ D, AEMeasurable (Zlocal R) P := by
    intro R hR
    exact (hP.aemeasurable_of_isLocalRandomVariable (hZlocalLocal R hR))
  have hZlocalInt : ∀ R ∈ D,
      Integrable (fun a => |Zlocal R a| ^ (2 : ℕ)) P := by
    intro R hR
    refine (hZInt R hR).congr ?_
    filter_upwards [hZEq R] with a ha
    rw [ha]
  have hZlocalMean : ∀ R ∈ D, ∫ a, Zlocal R a ∂P = 0 := by
    intro R hR
    rw [← hZMean R hR]
    exact integral_congr_ae (hZEq R).symm
  have hZlocalRoot : ∀ R ∈ D,
      (∫ a, |Zlocal R a| ^ (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤ K := by
    intro R hR
    have hIntegral :
        ∫ a, |Zlocal R a| ^ (2 : ℕ) ∂P =
          ∫ a, |Z R a| ^ (2 : ℕ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hZEq R] with a ha
      rw [ha]
    rw [hIntegral]
    exact hZRoot R hR
  have hRosenthal :=
    Book.Ch04.integral_abs_finiteSum_pow_rpow_inv_le_rosenthal_uniform_descendants
      (Q := Q) (k := child) (P := P) (p := 2) (K := K)
      hdep (by norm_num) hK Zlocal
      (by intro R hR; exact hZlocalLocal R (by simpa only [D] using hR))
      (by intro R hR; exact hZlocalMeas R (by simpa only [D] using hR))
      (by intro R hR; exact hZlocalInt R (by simpa only [D] using hR))
      (by intro R hR; exact hZlocalMean R (by simpa only [D] using hR))
      (by intro R hR; exact hZlocalRoot R (by simpa only [D] using hR))
  have hSumEq : ∀ᵐ a ∂P,
      ∑ R ∈ D, Z R a = ∑ R ∈ D, Zlocal R a := by
    have hall : ∀ᵐ a ∂P, ∀ R ∈ D, Z R a = Zlocal R a := by
      rw [Filter.eventually_all_finset]
      intro R hR
      exact hZEq R
    filter_upwards [hall] with a ha
    exact Finset.sum_congr rfl fun R hR => ha R hR
  have hIntegralEq :
      ∫ a, |∑ R ∈ D, Z R a| ^ (2 : ℕ) ∂P =
        ∫ a, |∑ R ∈ D, Zlocal R a| ^ (2 : ℕ) ∂P := by
    apply integral_congr_ae
    filter_upwards [hSumEq] with a ha
    rw [ha]
  have hLocalSumMem : MemLp (fun a => ∑ R ∈ D, Zlocal R a)
      (2 : ENNReal) P := by
    apply memLp_finsetSum D
    intro R hR
    rw [memLp_two_iff_integrable_sq (hZlocalMeas R hR).aestronglyMeasurable]
    refine (hZlocalInt R hR).congr ?_
    filter_upwards with a
    rw [sq_abs]
  have hLocalSumInt : Integrable
      (fun a => |∑ R ∈ D, Zlocal R a| ^ (2 : ℕ)) P := by
    refine hLocalSumMem.integrable_sq.congr ?_
    filter_upwards with a
    rw [sq_abs]
  have hRawSumInt : Integrable
      (fun a => |∑ R ∈ D, Z R a| ^ (2 : ℕ)) P := by
    refine hLocalSumInt.congr ?_
    filter_upwards [hSumEq] with a ha
    rw [ha]
  refine ⟨?_, ?_⟩
  · simpa only [D, Q, Z, X, mu0] using hRawSumInt
  · rw [show (∫ a,
        |∑ R ∈ descendantsAtScale (originCube d parent) child,
          (starredComparatorQuadratic B C q (cubeSet R) a -
            ∫ b, starredComparatorQuadratic B C q
              (cubeSet (originCube d child)) b ∂P)| ^ (2 : ℕ) ∂P) =
          ∫ a, |∑ R ∈ D, Z R a| ^ (2 : ℕ) ∂P by
        simp only [D, Q, Z, X, mu0], hIntegralEq]
    simpa only [Q, D] using! hRosenthal

private theorem combineFiniteMean_momentBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) (L : ℤ) {s A D : ℝ} (hs : (0 : ℝ) < s),
      let mu : Measure (Cutoff.CutoffSample d) := (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d));
      let X0 : Cutoff.CutoffSample d → ℝ := Observable.cutoffHomogenizationError M L ⟨s, hs⟩;
      ∀ (Y Z : Cutoff.CutoffSample d → ℝ) (_ : (0 : ℝ) < A) (_ : (0 : ℝ) < D)
        (_ : Measurable (Observable.cutoffHomogenizationError M L ⟨s, hs⟩)) (_ : Measurable Z)
        (_ : ∀ (ω : Cutoff.CutoffSample d), Observable.cutoffHomogenizationError M L ⟨s, hs⟩ ω ≤ Y ω + Z ω)
        (_ : IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma (2 : ℝ)) Y A)
        (_ : IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma (1 / 2 : ℝ)) Z D),
        let Y0 : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => max (0 : ℝ) (Y omega);
        let Z0 : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => max (0 : ℝ) (Z omega);
        ∀ (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Y0 omega)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Z0 omega) (_ : AEMeasurable Y0 mu),
          Integrable (fun (omega : Cutoff.CutoffSample d) => Y0 omega ^ (4 : ℕ)) mu ∧
            Integrable (fun (omega : Cutoff.CutoffSample d) => Z0 omega ^ (4 : ℕ)) mu ∧
              ∫ (omega : Cutoff.CutoffSample d), Y0 omega ^ (4 : ℕ) ∂mu ≤
                  (gammaMomentConst (2 : ℝ) * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℕ) ∧
                ∫ (omega : Cutoff.CutoffSample d), Z0 omega ^ (4 : ℕ) ∂mu ≤
                    (gammaMomentConst (1 / 2 : ℝ) * (4 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (4 : ℕ) ∧
                  (∀ (omega : Cutoff.CutoffSample d),
                      X0 omega ^ (4 : ℕ) ≤ (8 : ℝ) * (Y0 omega ^ (4 : ℕ) + Z0 omega ^ (4 : ℕ))) ∧
                    Integrable (fun (omega : Cutoff.CutoffSample d) => X0 omega ^ (2 : ℕ)) mu ∧
                      Integrable (fun (omega : Cutoff.CutoffSample d) => X0 omega ^ (4 : ℕ)) mu ∧
                        ∫ (omega : Cutoff.CutoffSample d), X0 omega ^ (2 : ℕ) ∂mu ≤
                          (2 : ℝ) *
                            ((gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ) +
                              (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ)) := by
  intro _ M L s A D hs mu X0 Y _ hA hD hXmeas hZmeas hdom hYtail hZtail Y0 Z0 hY0nonneg hZ0nonneg hY0meas
  have hZ0meas : AEMeasurable Z0 mu :=
    (measurable_const.max hZmeas).aemeasurable
  have hY0tail : IsBigOWith mu (gammaSigma 2) Y0 A := by
    simpa only [Y0] using Tail.isBigOWith_max_zero hA hYtail
  have hZ0tail : IsBigOWith mu (gammaSigma (1 / 2)) Z0 D := by
    simpa only [Z0] using Tail.isBigOWith_max_zero hD hZtail
  have hY2Int : Integrable (fun omega => Y0 omega ^ (2 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 2)
      (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hZ2Int : Integrable (fun omega => Z0 omega ^ (2 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 2)
      (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hY4Int : Integrable (fun omega => Y0 omega ^ (4 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 4)
      (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hZ4Int : Integrable (fun omega => Z0 omega ^ (4 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 4)
      (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hY2 : ∫ omega, Y0 omega ^ (2 : ℕ) ∂mu ≤
      (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) := by
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 2)
        (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail)
  have hZ2 : ∫ omega, Z0 omega ^ (2 : ℕ) ∂mu ≤
      (gammaMomentConst (1 / 2) *
        (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ) := by
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 2)
        (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail)
  have hY4 : ∫ omega, Y0 omega ^ (4 : ℕ) ∂mu ≤
      (gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) := by
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 4)
        (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail)
  have hZ4 : ∫ omega, Z0 omega ^ (4 : ℕ) ∂mu ≤
      (gammaMomentConst (1 / 2) *
        (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ) := by
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 4)
        (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail)
  have hX0nonneg : ∀ omega, 0 ≤ X0 omega := fun omega => by
    simpa only [X0] using Observable.cutoffHomogenizationError_nonneg M L ⟨s, hs⟩ omega
  have hX0dom : ∀ omega, X0 omega ≤ Y0 omega + Z0 omega := by
    intro omega
    exact (hdom omega).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
  have hX2Point : ∀ omega, X0 omega ^ (2 : ℕ) ≤
      2 * (Y0 omega ^ (2 : ℕ) + Z0 omega ^ (2 : ℕ)) := by
    intro omega
    have hp := pow_le_pow_left₀ (hX0nonneg omega) (hX0dom omega) 2
    nlinarith [sq_nonneg (Y0 omega - Z0 omega)]
  have hX4Point : ∀ omega, X0 omega ^ (4 : ℕ) ≤
      8 * (Y0 omega ^ (4 : ℕ) + Z0 omega ^ (4 : ℕ)) := by
    intro omega
    have hp := pow_le_pow_left₀ (hX0nonneg omega) (hX0dom omega) 4
    have hadd := add_pow_le (hY0nonneg omega) (hZ0nonneg omega) 4
    norm_num at hadd ⊢
    exact hp.trans hadd
  have hX2Int : Integrable (fun omega => X0 omega ^ (2 : ℕ)) mu := by
    refine Integrable.mono'
      ((hY2Int.add hZ2Int).const_mul 2)
      ((hXmeas.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hX2Point omega
  have hX4Int : Integrable (fun omega => X0 omega ^ (4 : ℕ)) mu := by
    refine Integrable.mono'
      ((hY4Int.add hZ4Int).const_mul 8)
      ((hXmeas.pow_const 4).aestronglyMeasurable) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX0nonneg omega) 4)]
    exact hX4Point omega
  have hX2 : ∫ omega, X0 omega ^ (2 : ℕ) ∂mu ≤
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) := by
    calc
      _ ≤ ∫ omega, 2 * (Y0 omega ^ (2 : ℕ) + Z0 omega ^ (2 : ℕ)) ∂mu :=
        integral_mono hX2Int ((hY2Int.add hZ2Int).const_mul 2) hX2Point
      _ = 2 * ((∫ omega, Y0 omega ^ (2 : ℕ) ∂mu) +
          ∫ omega, Z0 omega ^ (2 : ℕ) ∂mu) := by
        rw [integral_const_mul, integral_add hY2Int hZ2Int]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hY2 hZ2) (by norm_num)
  exact ⟨hY4Int, hZ4Int, hY4, hZ4, hX4Point, hX2Int, hX4Int, hX2⟩

private theorem relativeOrigin_centeredStarredComparatorQuadratic_sq_integrable_and_le
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ)
    {s A D : ℝ} (hs : 0 < s)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨s, hs⟩) A D)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let X : Set (Vec d) → RegCoeffField d → ℝ :=
      starredComparatorQuadratic B C0 q
    Integrable (fun a =>
        (X (cubeSet (originCube d (-c))) a) ^ (2 : ℕ))
        (Cutoff.relativeNormalizedCutoffLaw M L) ∧
      (∫ a, (X (cubeSet (originCube d (-c))) a) ^ (2 : ℕ)
          ∂(Cutoff.relativeNormalizedCutoffLaw M L)) ≤
        6 * (dotProduct q q) ^ (2 : ℕ) * twoTermSecondFourthBudget A D ∧
      Integrable
        (fun a => |Book.Ch04.restrictionCenteredOriginObservable
          (Cutoff.relativeNormalizedCutoffLaw M L) (-c) X a| ^ (2 : ℕ))
        (Cutoff.relativeNormalizedCutoffLaw M L) ∧
      ∫ a, |Book.Ch04.restrictionCenteredOriginObservable
          (Cutoff.relativeNormalizedCutoffLaw M L) (-c) X a| ^ (2 : ℕ)
          ∂(Cutoff.relativeNormalizedCutoffLaw M L) ≤
        6 * (dotProduct q q) ^ (2 : ℕ) * twoTermSecondFourthBudget A D := by
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let X0 : Cutoff.CutoffSample d → ℝ :=
    Observable.cutoffHomogenizationError M L ⟨s, hs⟩
  obtain ⟨Y, Z, _hPsiY, _hPsiZ, hA, hD, hXmeas, hYmeas, hZmeas,
      hdom, hYtail, hZtail⟩ := hLower
  let Y0 : Cutoff.CutoffSample d → ℝ := fun omega => max 0 (Y omega)
  let Z0 : Cutoff.CutoffSample d → ℝ := fun omega => max 0 (Z omega)
  have hY0nonneg : ∀ omega, 0 ≤ Y0 omega := fun omega => le_max_left _ _
  have hZ0nonneg : ∀ omega, 0 ≤ Z0 omega := fun omega => le_max_left _ _
  have hY0meas : AEMeasurable Y0 mu :=
    (measurable_const.max hYmeas).aemeasurable
  obtain ⟨hY4Int, hZ4Int, hY4, hZ4, hX4Point, hX2Int, hX4Int, hX2⟩ :=
    @combineFiniteMean_momentBounds1 (d) (M) (L) (s) (A) (D) (hs) (Y) (Z) (hA) (hD) (hXmeas)
      (hZmeas) (hdom) (hYtail) (hZtail) (hY0nonneg) (hZ0nonneg) (hY0meas)
  have hX4 : ∫ omega, X0 omega ^ (4 : ℕ) ∂mu ≤
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ)) := by
    calc
      _ ≤ ∫ omega, 8 * (Y0 omega ^ (4 : ℕ) + Z0 omega ^ (4 : ℕ)) ∂mu :=
        integral_mono hX4Int ((hY4Int.add hZ4Int).const_mul 8) hX4Point
      _ = 8 * ((∫ omega, Y0 omega ^ (4 : ℕ) ∂mu) +
          ∫ omega, Z0 omega ^ (4 : ℕ) ∂mu) := by
        rw [integral_const_mul, integral_add hY4Int hZ4Int]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hY4 hZ4) (by norm_num)
  have hErrInt : Integrable
      (fun omega => 6 * (dotProduct q q) ^ (2 : ℕ) *
        (X0 omega ^ (2 : ℕ) + X0 omega ^ (4 : ℕ))) mu :=
    (hX2Int.add hX4Int).const_mul (6 * (dotProduct q q) ^ (2 : ℕ))
  have hErrBound :
      ∫ omega, 6 * (dotProduct q q) ^ (2 : ℕ) *
          (X0 omega ^ (2 : ℕ) + X0 omega ^ (4 : ℕ)) ∂mu ≤
        6 * (dotProduct q q) ^ (2 : ℕ) * twoTermSecondFourthBudget A D := by
    rw [integral_const_mul, integral_add hX2Int hX4Int]
    exact mul_le_mul_of_nonneg_left (add_le_add hX2 hX4)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let R : TriadicCube d := originCube d (-c)
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    starredComparatorQuadratic B C0 q
  let Xrel : RegCoeffField d → ℝ := X (cubeSet R)
  let relmu := Cutoff.relativeNormalizedCutoffLaw M L
  have hXrelMeas : AEMeasurable Xrel relmu := by
    simpa only [Xrel, X, R] using
      aemeasurable_starredComparatorQuadratic_cubeSet
        (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L) B C0 q R
  have hXrelSqMeas : AEMeasurable (fun a => Xrel a ^ (2 : ℕ)) relmu :=
    hXrelMeas.pow_const 2
  have hrelLaw : relmu = Measure.map (dilateReg (-h))
      (Cutoff.coefficientCutoffLaw M L) := by
    simpa only [relmu, h] using Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg M L
  have hXrelSqMeasMap : AEMeasurable (fun a => Xrel a ^ (2 : ℕ))
      (Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L)) := by
    simpa only [← hrelLaw] using hXrelSqMeas
  have hcoeffMeas := hXrelSqMeasMap.comp_quasiMeasurePreserving
    ((measurable_dilateReg (d := d) (-h)).quasiMeasurePreserving
      (Cutoff.coefficientCutoffLaw M L))
  have hsampleMeas := hcoeffMeas.comp_quasiMeasurePreserving
    ((Cutoff.measurable_coefficientCutoff M.nu L).quasiMeasurePreserving mu)
  have hraw := Observable.cutoffHomogenizationErrorRaw_ae_eq_representative
    M L L hs sigma
  have hsampleDom : ∀ᵐ omega ∂mu,
      |Xrel (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ^ (2 : ℕ)| ≤
        6 * (dotProduct q q) ^ (2 : ℕ) *
          (X0 omega ^ (2 : ℕ) + X0 omega ^ (4 : ℕ)) := by
    filter_upwards [hraw] with omega hrawOmega
    have hpoint := fullBlockQuadratic_starredFluctuation_relativeOrigin_sq_le_error
      M L hs omega q
    have hX0eq : X0 omega =
        Observable.cutoffHomogenizationErrorRepresentative M L L hs sigma omega := by
      rfl
    dsimp only [c, h, sigma, a0, B, C0, R, X, Xrel] at hpoint ⊢
    rw [hrawOmega] at hpoint
    rw [← hX0eq] at hpoint
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hpoint
  have hXrelSqInt : Integrable (fun a => Xrel a ^ (2 : ℕ)) relmu := by
    rw [hrelLaw] at hXrelSqMeas ⊢
    refine (integrable_map_measure hXrelSqMeas.aestronglyMeasurable
      (measurable_dilateReg (d := d) (-h)).aemeasurable).mpr ?_
    rw [Cutoff.coefficientCutoffLaw_eq_map] at hcoeffMeas ⊢
    refine (integrable_map_measure hcoeffMeas.aestronglyMeasurable
      (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable).mpr ?_
    exact Integrable.mono' hErrInt hsampleMeas.aestronglyMeasurable hsampleDom
  have hXrelBound : ∫ a, Xrel a ^ (2 : ℕ) ∂relmu ≤
      6 * (dotProduct q q) ^ (2 : ℕ) * twoTermSecondFourthBudget A D := by
    rw [hrelLaw] at hXrelSqMeas ⊢
    rw [MeasureTheory.integral_map
      (measurable_dilateReg (d := d) (-h)).aemeasurable
      hXrelSqMeas.aestronglyMeasurable]
    rw [Cutoff.coefficientCutoffLaw_eq_map] at hcoeffMeas ⊢
    change (∫ a, (((fun y => Xrel y ^ (2 : ℕ)) ∘ dilateReg (-h)) a)
        ∂Measure.map (Cutoff.coefficientCutoff M.nu L) mu) ≤
      6 * (dotProduct q q) ^ (2 : ℕ) * twoTermSecondFourthBudget A D
    rw [MeasureTheory.integral_map
      (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable
      hcoeffMeas.aestronglyMeasurable]
    have hsampleInt : Integrable
        (fun omega => Xrel (dilateReg (-h)
          (Cutoff.coefficientCutoff M.nu L omega)) ^ (2 : ℕ)) mu :=
      Integrable.mono' hErrInt hsampleMeas.aestronglyMeasurable hsampleDom
    have hsampleLe :
        (fun omega => Xrel (dilateReg (-h)
          (Cutoff.coefficientCutoff M.nu L omega)) ^ (2 : ℕ)) ≤ᵐ[mu]
        fun omega => 6 * (dotProduct q q) ^ (2 : ℕ) *
          (X0 omega ^ (2 : ℕ) + X0 omega ^ (4 : ℕ)) := by
      filter_upwards [hsampleDom] with omega homega
      exact (le_abs_self _).trans homega
    exact (integral_mono_ae hsampleInt hErrInt hsampleLe).trans hErrBound
  have hXrelMem : MemLp Xrel (2 : ENNReal) relmu := by
    rw [memLp_two_iff_integrable_sq hXrelMeas.aestronglyMeasurable]
    exact hXrelSqInt
  let Xcenter := Book.Ch04.restrictionCenteredOriginObservable relmu (-c) X
  have hCenterInt : Integrable (fun a => |Xcenter a| ^ (2 : ℕ)) relmu := by
    have hmem := hXrelMem.sub (memLp_const (∫ b, Xrel b ∂relmu))
    have hint := hmem.integrable_sq
    refine hint.congr ?_
    filter_upwards with a
    rw [sq_abs]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [c, sigma, a0, B, C0, X, Xrel, R, relmu] using hXrelSqInt
  · simpa only [c, sigma, a0, B, C0, X, Xrel, R, relmu] using hXrelBound
  · simpa only [c, sigma, a0, B, C0, X, Xcenter] using hCenterInt
  · have hvar : ProbabilityTheory.variance Xrel relmu ≤
        ∫ a, (Xrel a - 0) ^ (2 : ℕ) ∂relmu :=
      variance_le_integral_sub_const hXrelMem 0
    have hcenterVar : ∫ a, |Xcenter a| ^ (2 : ℕ) ∂relmu =
        ProbabilityTheory.variance Xrel relmu := by
      rw [ProbabilityTheory.variance_eq_integral hXrelMeas]
      apply integral_congr_ae
      filter_upwards with a
      simp only [Xcenter, Book.Ch04.restrictionCenteredOriginObservable, Xrel, X, R,
        sq_abs]
    have hcenterBound : ∫ a, |Xcenter a| ^ (2 : ℕ) ∂relmu ≤
        6 * (dotProduct q q) ^ (2 : ℕ) * twoTermSecondFourthBudget A D := by
      rw [hcenterVar]
      exact hvar.trans (by simpa using hXrelBound)
    simpa only [c, sigma, a0, B, C0, X, Xcenter] using hcenterBound

/-- Raw relative-origin and centered descendant second-moment bounds used by
the quantitative finite-corridor consumer. -/
theorem relativeStarredComparator_origin_and_descendant_moment_bounds
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    {s A D : ℝ} (hs : 0 < s)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨s, hs⟩) A D)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let X : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
      fullBlockQuadratic (starredFluctuationMatrix B C0 U a) q
    let parent : ℤ := n - L - c
    let N : ℝ :=
      ((descendantsAtScale (originCube d parent) (-c)).card : ℝ)
    let budget : ℝ :=
      2 *
          ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
        8 *
          ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
    let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
    let K : ℝ := Real.sqrt probeBudget
    Integrable (fun a =>
        (X (cubeSet (originCube d (-c))) a) ^ (2 : ℕ)) P ∧
      (∫ a, (X (cubeSet (originCube d (-c))) a) ^ (2 : ℕ) ∂P) ≤
        probeBudget ∧
      Integrable
        (fun a =>
          |Book.Ch04.restrictionCenteredDescendantAverage P (-c) parent X a| ^
            (2 : ℕ)) P ∧
      (∫ a,
        |Book.Ch04.restrictionCenteredDescendantAverage P (-c) parent X a| ^
          (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤
        N⁻¹ *
          (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
              N ^ (1 / (2 : ℝ)) * K +
            Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
              Real.sqrt N * K) := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    starredComparatorQuadratic B C0 q
  let parent : ℤ := n - L - c
  let N : ℝ := ((descendantsAtScale (originCube d parent) (-c)).card : ℝ)
  let budget : ℝ := twoTermSecondFourthBudget A D
  let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
  let K : ℝ := Real.sqrt probeBudget
  have hchildParent : -c ≤ parent := by
    simp only [c, parent]
    omega
  have hOrigin :=
    relativeOrigin_centeredStarredComparatorQuadratic_sq_integrable_and_le
      M L hs hLower q
  have hBudgetNonneg : 0 ≤ probeBudget := by
    dsimp only [probeBudget, budget]
    unfold twoTermSecondFourthBudget
    positivity
  have hOriginRoot :
      (∫ a,
        |Book.Ch04.restrictionCenteredOriginObservable P (-c) X a| ^
          (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤ K := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by
      simpa only [P, c, sigma, a0, B, C0, X] using hOrigin.2.2.2)
  have hsum :=
    starredComparatorQuadratic_centeredDescendantSum_root_le
      (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L)
      (Cutoff.relativeNormalizedCutoffLaw_stationary_real M L)
      (Cutoff.relativeNormalizedCutoffLaw_unitRangeDependent M L)
      B C0 q hchildParent (Real.sqrt_nonneg _) (by
        simpa only [P, c, sigma, a0, B, C0, X] using hOrigin.2.2.1) hOriginRoot
  let S : RegCoeffField d → ℝ := fun a =>
    ∑ R ∈ descendantsAtScale (originCube d parent) (-c),
      (X (cubeSet R) a - ∫ b, X (cubeSet (originCube d (-c))) b ∂P)
  have hNPos : 0 < N := by
    dsimp only [N]
    exact_mod_cast
      (descendantsAtScale_nonempty (originCube d parent) hchildParent).card_pos
  have hNInvNonneg : 0 ≤ N⁻¹ := (inv_pos.mpr hNPos).le
  have hsumInt : Integrable (fun a => |S a| ^ (2 : ℕ)) P := by
    simpa only [S, P, c, sigma, a0, B, C0, X] using hsum.1
  have havgEq : Book.Ch04.restrictionCenteredDescendantAverage P (-c) parent X =
      fun a => N⁻¹ * S a := by
    funext a
    rfl
  have havgInt : Integrable
      (fun a =>
        |Book.Ch04.restrictionCenteredDescendantAverage P (-c) parent X a| ^
          (2 : ℕ)) P := by
    have hscaled := hsumInt.const_mul (N⁻¹ ^ (2 : ℕ))
    refine hscaled.congr ?_
    filter_upwards with a
    rw [havgEq]
    simp only [abs_mul, abs_of_nonneg hNInvNonneg]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [P, c, sigma, a0, B, C0, X] using! hOrigin.1
  · simpa only [P, c, sigma, a0, B, C0, X] using! hOrigin.2.1
  · simpa only [P, c, sigma, a0, B, C0, X] using! havgInt
  · have hintegral :
        ∫ a,
          |Book.Ch04.restrictionCenteredDescendantAverage P (-c) parent X a| ^
            (2 : ℕ) ∂P =
          N⁻¹ ^ (2 : ℕ) * ∫ a, |S a| ^ (2 : ℕ) ∂P := by
      rw [havgEq]
      simp_rw [abs_mul, abs_of_nonneg hNInvNonneg]
      simp_rw [mul_pow]
      rw [integral_const_mul]
    change
      (∫ a,
          |Book.Ch04.restrictionCenteredDescendantAverage P (-c) parent X a| ^
            (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤
        N⁻¹ *
          (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
                N ^ (1 / (2 : ℝ)) * K +
            Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
                Real.sqrt N * K)
    rw [hintegral, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (sq_nonneg N⁻¹), Real.sqrt_sq hNInvNonneg]
    have hsumRoot : Real.sqrt (∫ a, |S a| ^ (2 : ℕ) ∂P) ≤
        Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
            N ^ (1 / (2 : ℝ)) * K +
          Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
            Real.sqrt N * K := by
      rw [Real.sqrt_eq_rpow]
      simpa only [S, P, c, sigma, a0, B, C0, X, N, K] using hsum.2
    exact mul_le_mul_of_nonneg_left
      hsumRoot hNInvNonneg

end

end Algsuperdiff.Section3.Provider.Homogenization
