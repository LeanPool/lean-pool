/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.SubdivisionDefect

/-!
# High-contrast homogenization: Provider.Response.AffineResponseDifferenceEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Difference energy for a common coefficient representative

When every descendant cube carries the same coefficient representative as its
parent, the parent canonical response solution restricts to every descendant.
The one-cube second-variation identity then sums exactly to the response
partition defect.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02
open Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

private theorem exists_restrictedCanonicalResponseSolution_of_commonCoeff
    (F : Book.Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (p r : Vec d)
    (hcoeff : (F.coeffOn R).toCoeffField =
      (F.coeffOn Q).toCoeffField) :
    ∃ w : Book.Ch02.Solution (Book.Ch02.cubeDomain R) (F.coeffOn R),
      w.toH1.grad =
        canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p r := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  let uParent : AHarmonicFunction (F.coeffOn R).toCoeffField (openCubeSet Q) :=
    castAHarmonicCoeff hcoeff.symm
      (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p r)
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hgradL2 : MemVectorL2 (openCubeSet R) uParent.toH1.grad := by
    simpa using
      (uParent.toH1.restrict (isOpen_openCubeSet R) hsub).grad_memVectorL2
  have hEll : IsAEEllipticFieldOn (F.coeffOn R).lam (F.coeffOn R).Lam
      (openCubeSet R) (F.coeffOn R).toCoeffField := by
    simpa [Book.Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (F.coeffOn R))
  have hflux : MemVectorL2 (openCubeSet R)
      (fun x ↦ matVecMul ((F.coeffOn R).toCoeffField x)
        (uParent.toH1.grad x)) :=
    hEll.memVectorL2_matVecMul hgradL2
  refine ⟨uParent.restrictOfMemVectorL2
    (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hflux, ?_⟩
  change uParent.toH1.grad =
    canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p r
  calc
    uParent.toH1.grad =
        (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p r).toH1.grad := by
      exact castAHarmonicCoeff_grad hcoeff.symm
        (canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p r)
    _ = canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p r := rfl

/-- For a family with one exact coefficient representative on a parent and all
of its descendants, the averaged gradient-difference half-energy is exactly
the child-minus-parent response defect. -/
theorem descendantsAverage_additivityDiffHalfEnergy_eq_responseJPartitionDefect_of_commonCoeff
    (F : Book.Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (j : ℕ) (p r : Vec d)
    (hcommon : ∀ R ∈ descendantsAtDepth Q j,
      (F.coeffOn R).toCoeffField = (F.coeffOn Q).toCoeffField) :
    descendantsAverage Q j (fun R ↦
        cubeAverage R
          (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p r)) =
      responseJPartitionDefectOnFamilyAtDepth F Q j p r := by
  classical
  let Z : Finset (TriadicCube d) := descendantsAtDepth Q j
  let U : Book.Ch02.Domain d := Book.Ch02.cubeDomain Q
  let V : TriadicCube d → Book.Ch02.Domain d := fun R ↦ Book.Ch02.cubeDomain R
  let a : Book.Ch02.CoeffOn U := F.coeffOn Q
  let b : ∀ R, Book.Ch02.CoeffOn (V R) := fun R ↦ F.coeffOn R
  let v : Book.Ch02.Solution U a := canonicalResponseSolution U a p r
  let z : ∀ R, Book.Ch02.Solution (V R) (b R) := fun R ↦
    if hR : R ∈ Z then
      Classical.choose
        (exists_restrictedCanonicalResponseSolution_of_commonCoeff
          F Q (by simpa [Z] using hR) p r
          (hcommon R (by simpa [Z] using hR)))
    else
      canonicalResponseSolution (V R) (b R) p r
  have hz : ∀ R ∈ Z, (z R).toH1.grad = v.toH1.grad := by
    intro R hR
    have hspec := Classical.choose_spec
      (exists_restrictedCanonicalResponseSolution_of_commonCoeff
        F Q (by simpa [Z] using hR) p r
        (hcommon R (by simpa [Z] using hR)))
    rw [show z R = Classical.choose
      (exists_restrictedCanonicalResponseSolution_of_commonCoeff
        F Q (by simpa [Z] using hR) p r
        (hcommon R (by simpa [Z] using hR))) by simp [z, hR]]
    exact hspec
  have hsub : ∀ R ∈ Z, (V R).carrier ⊆ U.carrier := by
    intro R hR
    simpa [U, V, Book.Ch02.cubeDomain_coe] using
      (openCubeSet_subset_of_mem_descendantsAtDepth
        (by simpa [Z] using hR))
  have hdisj : (↑Z : Set (TriadicCube d)).PairwiseDisjoint
      fun R ↦ (V R).carrier := by
    simpa [Z, V, Book.Ch02.cubeDomain_coe] using
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j)
  have hcover : U.carrier \ ⋃ R ∈ (↑Z : Set (TriadicCube d)), (V R).carrier ⊆
      ⋃ R ∈ (↑Z : Set (TriadicCube d)), cubeBoundary R := by
    intro x hx
    have hxQ : x ∈ cubeSet Q :=
      openCubeSet_subset_cubeSet Q (by simpa [U, Book.Ch02.cubeDomain_coe] using hx.1)
    have hxUnion : x ∈ ⋃ R ∈ (↑Z : Set (TriadicCube d)), cubeSet R := by
      rw [← show cubeSet Q = ⋃ R ∈ (↑Z : Set (TriadicCube d)), cubeSet R by
        simpa [Z] using cubeSet_eq_iUnion_descendantsAtDepth Q j]
      exact hxQ
    rcases Set.mem_iUnion.mp hxUnion with ⟨R, hxR⟩
    rcases Set.mem_iUnion.mp hxR with ⟨hR, hxR⟩
    refine Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxR, ?_⟩⟩
    intro hxOpen
    apply hx.2
    exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, by
      simpa [V, Book.Ch02.cubeDomain_coe] using hxOpen⟩⟩
  have hboundaries :
      volume (⋃ R ∈ (↑Z : Set (TriadicCube d)), cubeBoundary R) = 0 :=
    (measure_biUnion_null_iff Z.countable_toSet).2
      (fun R _hR ↦ volume_cubeBoundary_eq_zero R)
  have hnull : volume
      (U.carrier \ ⋃ R ∈ (↑Z : Set (TriadicCube d)), (V R).carrier) = 0 :=
    measure_mono_null hcover hboundaries
  have hweight : ∀ R ∈ Z,
      (volume (V R).carrier).toReal / (volume U.carrier).toReal =
        ((Z.card : ℝ))⁻¹ := by
    intro R hR
    have hvol := cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth
      (Q := Q) (by simpa [Z] using hR)
    change cubeVolume Q = (Z.card : ℝ) * cubeVolume R at hvol
    have hcard : (Z.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr
        (by simpa [Z] using descendantsAtDepth_nonempty Q j)
    have hvolR : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
    simp only [U, V, Book.Ch02.cubeDomain_coe, volume_openCubeSet_toReal]
    rw [hvol]
    field_simp
  have henergy : ∀ R ∈ Z,
      Book.Ch02.secondVariationEnergyValue (V R) (b R)
          (canonicalResponseSolution (V R) (b R) p r) (z R) =
        cubeAverage R
          (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p r) := by
    intro R hR
    have hgrad := Classical.choose_spec
      (exists_restrictedCanonicalResponseSolution_of_commonCoeff
        F Q (by simpa [Z] using hR) p r
        (hcommon R (by simpa [Z] using hR)))
    have hzR : z R = Classical.choose
        (exists_restrictedCanonicalResponseSolution_of_commonCoeff
          F Q (by simpa [Z] using hR) p r
          (hcommon R (by simpa [Z] using hR))) := by
      simp [z, hR]
    have hdiff :=
      cubeAverage_additivityEnergyDensity_eq_responseJ_sub_responseValue
        F Q R p r (z R) (by simpa [hzR] using hgrad)
    have hsecond := Book.Ch02.secondVariation_eq_of_isResponseMaximizer
      (canonicalResponseSolution_isMaximizer (V R) (b R) p r) (z R)
    exact hsecond.symm.trans hdiff.symm
  have hweighted := sum_weight_responseJ_sub_responseJ_eq_sum_weight_secondVariation
    (Z := Z) (U := U) (V := V) (a := a) (b := b)
    (fun R hR ↦ by simpa [a, b] using hcommon R (by simpa [Z] using hR))
    hsub hdisj hnull (v := v)
    (canonicalResponseSolution_isMaximizer U a p r) hz
  have haverage :
      ((Z.card : ℝ))⁻¹ * ∑ R ∈ Z,
          Book.Ch02.responseJ (V R) (b R) p r -
        Book.Ch02.responseJ U a p r =
      ((Z.card : ℝ))⁻¹ * ∑ R ∈ Z,
        Book.Ch02.secondVariationEnergyValue (V R) (b R)
          (canonicalResponseSolution (V R) (b R) p r) (z R) := by
    calc
      ((Z.card : ℝ))⁻¹ * ∑ R ∈ Z,
            Book.Ch02.responseJ (V R) (b R) p r -
          Book.Ch02.responseJ U a p r =
          (∑ R ∈ Z, (volume (V R).carrier).toReal /
              (volume U.carrier).toReal *
                Book.Ch02.responseJ (V R) (b R) p r) -
            Book.Ch02.responseJ U a p r := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun R hR ↦ by rw [hweight R hR]
      _ = ∑ R ∈ Z, (volume (V R).carrier).toReal /
            (volume U.carrier).toReal *
              Book.Ch02.secondVariationEnergyValue (V R) (b R)
                (canonicalResponseSolution (V R) (b R) p r) (z R) := hweighted
      _ = ((Z.card : ℝ))⁻¹ * ∑ R ∈ Z,
            Book.Ch02.secondVariationEnergyValue (V R) (b R)
              (canonicalResponseSolution (V R) (b R) p r) (z R) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun R hR ↦ by rw [hweight R hR]
  calc
    descendantsAverage Q j (fun R ↦ cubeAverage R
        (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p r)) =
        ((Z.card : ℝ))⁻¹ * ∑ R ∈ Z,
          Book.Ch02.secondVariationEnergyValue (V R) (b R)
            (canonicalResponseSolution (V R) (b R) p r) (z R) := by
      unfold descendantsAverage
      simp only [Z]
      congr 1
      exact Finset.sum_congr rfl fun R hR ↦ (henergy R (by simpa [Z] using hR)).symm
    _ = ((Z.card : ℝ))⁻¹ * ∑ R ∈ Z,
          Book.Ch02.responseJ (V R) (b R) p r -
        Book.Ch02.responseJ U a p r := haverage.symm
    _ = responseJPartitionDefectOnFamilyAtDepth F Q j p r := by
      rfl

end

end HCPolySupport.HighContrast.Response
