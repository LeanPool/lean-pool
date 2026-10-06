/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CommonResidualObservationParent

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FixedParentObservationResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Observation response at a fixed common parent

The bounded-domain parent is selected once for the whole Whitney family.
The usual descendant filling and boundary convolution can then be evaluated
at this fixed parent, retaining the upper generation needed by the physical
frame estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem triadicCube_eq_translateCube_index_origin_fixed
    (Q : TriadicCube d) : translateCube Q.index (originCube d Q.scale) = Q := by
  cases Q
  simp [translateCube, originCube]

private theorem epsilonAffineTarget_descendant_subset_fixed
    [NeZero d] {epsilon : ℝ} (abar : Mat d) (center : Vec d)
    {K k : ℤ} {R : TriadicCube d}
    (hk : k ≤ K) (hR : R ∈ descendantsAtScale (originCube d K) k) :
    adaptedCellTranslate (epsilonAffineGrid epsilon abar) k
        (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
          adaptedCellCenter (epsilonAffineGrid epsilon abar) k R.index) ⊆
      adaptedCellTranslate (epsilonAffineGrid epsilon abar) K
        (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
          adaptedCellCenter (epsilonAffineGrid epsilon abar) K 0) := by
  let p := epsilonAffineGrid epsilon abar
  let z := epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center
  have hscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
  have hRrepr : translateCube R.index (originCube d k) = R := by
    rw [← hscale]
    exact triadicCube_eq_translateCube_index_origin_fixed R
  have hopen : openCubeSet R ⊆ openCubeSet (originCube d K) :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  have hstandard : standardCell d k R.index ⊆ standardCell d K 0 := by
    have hadaptedOne : adaptedCellAt (1 : Mat d) k R.index ⊆
        adaptedCellAt (1 : Mat d) K 0 := by
      rw [adaptedCellAt_one_eq_openCubeSet_translateCube,
        adaptedCellAt_one_eq_openCubeSet_translateCube]
      rw [hRrepr]
      simpa only [translateCube, originCube, Pi.zero_apply, add_zero] using! hopen
    rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellAt_eq_image] at hadaptedOne
    have hone : matVecMul (1 : Mat d) = id := funext fun x ↦ matVecMul_one x
    rw [hone, Set.image_id, Set.image_id] at hadaptedOne
    exact hadaptedOne
  have hadapted : adaptedCellAt p k R.index ⊆ adaptedCellAt p K 0 := by
    simpa only [Recurrence.adaptedCellAt_eq_image] using Set.image_mono hstandard
  rw [← translateSet_adaptedCellAt_eq_translate,
    ← translateSet_adaptedCellAt_eq_translate]
  unfold translateSet
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, hadapted hy, rfl⟩

/-- A supplied enclosing parent controls every descendant response of one
centered observation cube. -/
theorem observationAllDepth_normalizedFixedParentMajorant
    [NeZero d] {s epsilon : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hepsilon : 0 < epsilon) (center : Vec d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (t : ℤ) (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (K M : ℤ) (hKM : K ≤ M) (aObs : Book.Ch03.CoeffFamily d)
    (hObs : (aObs.coeffOn (originCube d K)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d K))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center))
    (hEnclose : adaptedCellTranslate (epsilonAffineGrid epsilon abar) K
        (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
          adaptedCellCenter (epsilonAffineGrid epsilon abar) K 0) ⊆
      adaptedCell (Selection.normalizedRoot (symmPart abar)) M) :
    ∀ l : ℕ,
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d K) (K - (l : ℤ)) aObs (1 : Mat d) ≤
        ∑' u : ℕ,
          (if u = 0 then 1 else
            6 * (d : ℝ) * Real.sqrt d *
              ‖(epsilonAffineGrid epsilon abar)⁻¹ *
                Selection.normalizedRoot (symmPart abar)‖ *
              (3 : ℝ) ^ (-(u : ℤ))) *
            Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
              (originCube d M) (K - (l : ℤ) - (u : ℤ))
                aRef (1 : Mat d) := by
  intro l
  let p := epsilonAffineGrid epsilon abar
  let q := Selection.normalizedRoot (symmPart abar)
  let z := epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center
  let k : ℤ := K - (l : ℤ)
  have hp : p.PosDef := by
    simpa only [p] using epsilonAffineGrid_posDef hepsilon hS
  have hkK : k ≤ K := by dsimp only [k]; omega
  have hkM : k ≤ M := hkK.trans hKM
  apply Book.Ch02.finsetSupReal_le
    (descendantsAtScale (originCube d K) k)
    (descendantsAtScale_nonempty (originCube d K) hkK)
  intro R hR
  have hscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
  have hRrepr : translateCube R.index (originCube d k) = R := by
    rw [← hscale]
    exact triadicCube_eq_translateCube_index_origin_fixed R
  have hObsR := coeffOn_descendant_ae_eq_of_root_ae_eq
    aObs hkK hR hObs
  have htarget : adaptedCellTranslate p k
      (z + adaptedCellCenter p k R.index) ⊆ adaptedCell q M := by
    have hdesc := epsilonAffineTarget_descendant_subset_fixed
      (epsilon := epsilon) abar center hkK hR
    exact hdesc.trans (by simpa only [p, q, z] using hEnclose)
  have hpoint :=
    observationNormalizedBlockResponseMax_le_normalizedParentRow_of_enclosed
      hs hsHalf hepsilon center a abar hS t aRef haRef k M hkM R.index
        aObs (by rw [hRrepr]; exact hObsR)
        (by simpa only [p, q, z] using htarget)
  rw [hRrepr] at hpoint
  simpa only [k, sub_sub] using hpoint

/-- A fixed parent above the activation generation gives the same power-tail
response estimate as the cellwise construction, with its parent generation
now bounded by construction. -/
theorem observationHomogenizationError_le_referencePowerTail_fixedParent
    [NeZero d] {s epsilon amplitude kappa : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hepsilon : 0 < epsilon) (hAmplitude : 0 ≤ amplitude)
    (center : Vec d) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (N K M : ℤ) (hNM : N ≤ M) (hKM : K ≤ M)
    (hTail : ScalarIdentityPowerTail aRef s amplitude kappa ((3 : ℝ) ^ N))
    (aObs : Book.Ch03.CoeffFamily d)
    (hObs : (aObs.coeffOn (originCube d K)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d K))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center))
    (hEnclose : adaptedCellTranslate (epsilonAffineGrid epsilon abar) K
        (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
          adaptedCellCenter (epsilonAffineGrid epsilon abar) K 0) ⊆
      adaptedCell (Selection.normalizedRoot (symmPart abar)) M) :
    Summable (fun l : ℕ ↦ Book.Ch02.geometricWeight s 2 l *
      observationParentRowMajorant epsilon abar aRef M K l) ∧
    (∀ l : ℕ,
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d K) (K - (l : ℤ)) aObs (1 : Mat d) ≤
        observationParentRowMajorant epsilon abar aRef M K l) ∧
    Book.Ch02.HomogenizationErrorOnCube
        (originCube d K) s .infinity (.finite 2) aObs (1 : Mat d) ≤
      Real.sqrt
        (observationParentConvolutionFactor d s epsilon abar M K *
          (amplitude * (((3 : ℝ) ^ M) / ((3 : ℝ) ^ N)) ^ (-kappa)) ^ 2) := by
  have hrawMax := observationAllDepth_normalizedFixedParentMajorant
    hs hsHalf hepsilon center a abar hS t aRef haRef K M hKM aObs hObs hEnclose
  let G : ℕ := (M - K).toNat
  have hG : (G : ℤ) = M - K := Int.toNat_of_nonneg (sub_nonneg.mpr hKM)
  let A : ℕ → ℝ := fun n ↦
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
      (originCube d M) (M - (n : ℤ)) aRef (1 : Mat d)
  let C : ℝ := observationFillingCoefficient d epsilon abar
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
      (originCube d M) (by simp only [originCube]; omega) aRef (1 : Mat d)
  have hA : Summable (fun n : ℕ ↦ Book.Ch02.geometricWeight s 2 n * A n) := by
    simpa only [A, originCube] using
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        (originCube d M) aRef (1 : Mat d) hs
  have hC0 : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  obtain ⟨hinner, houter, hconvolution⟩ :=
    Transport.summable_boundaryConvolution_shift_and_tsum_le
      hs hsHalf hC0 G A hA0 hA
  have hindex : ∀ (l u : ℕ), M - ((G + (l + u) : ℕ) : ℤ) =
      K - (l : ℤ) - (u : ℤ) := by
    intro l u
    rw [Nat.cast_add, Nat.cast_add, hG]
    omega
  have hBdef : ∀ l : ℕ,
      observationParentRowMajorant epsilon abar aRef M K l =
        ∑' u : ℕ, (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u)) := by
    intro l
    unfold observationParentRowMajorant
    apply tsum_congr
    intro u
    rw [show C = observationFillingCoefficient d epsilon abar by rfl]
    dsimp only [A]
    rw [hindex l u]
  have hBsum : Summable (fun l : ℕ ↦ Book.Ch02.geometricWeight s 2 l *
      observationParentRowMajorant epsilon abar aRef M K l) := by
    exact houter.congr fun l ↦ by rw [hBdef l]
  have hrawCoefficient : ∀ u : ℕ,
      (if u = 0 then 1 else
        6 * (d : ℝ) * Real.sqrt d *
          ‖(epsilonAffineGrid epsilon abar)⁻¹ *
            Selection.normalizedRoot (symmPart abar)‖ * (3 : ℝ) ^ (-(u : ℤ))) ≤
        C * (3 : ℝ) ^ (-(u : ℤ)) := by
    intro u
    by_cases hu : u = 0
    · subst u
      simpa only [ite_eq_left, Int.ofNat_zero, neg_zero, zpow_zero, mul_one, C,
        observationFillingCoefficient] using
        le_max_left (1 : ℝ)
          (6 * (d : ℝ) * Real.sqrt d *
            ‖(epsilonAffineGrid epsilon abar)⁻¹ *
              Selection.normalizedRoot (symmPart abar)‖)
    · rw [ite_eq_right hu]
      exact mul_le_mul_of_nonneg_right
        (le_max_right (1 : ℝ)
          (6 * (d : ℝ) * Real.sqrt d *
            ‖(epsilonAffineGrid epsilon abar)⁻¹ *
              Selection.normalizedRoot (symmPart abar)‖))
        (zpow_nonneg (by norm_num) _)
  have hmax : ∀ l : ℕ,
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d K) (K - (l : ℤ)) aObs (1 : Mat d) ≤
        observationParentRowMajorant epsilon abar aRef M K l := by
    intro l
    let raw : ℕ → ℝ := fun u ↦
      (if u = 0 then 1 else
        6 * (d : ℝ) * Real.sqrt d *
          ‖(epsilonAffineGrid epsilon abar)⁻¹ *
            Selection.normalizedRoot (symmPart abar)‖ * (3 : ℝ) ^ (-(u : ℤ))) *
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d M) (K - (l : ℤ) - (u : ℤ)) aRef (1 : Mat d)
    let major : ℕ → ℝ := fun u ↦
      (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u))
    have hraw0 : ∀ u, 0 ≤ raw u := by
      intro u
      exact mul_nonneg (by split <;> positivity)
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
          (originCube d M) (by simp only [originCube]; omega) aRef (1 : Mat d))
    have hrawMajor : ∀ u, raw u ≤ major u := by
      intro u
      dsimp only [raw, major]
      rw [show Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d M) (K - (l : ℤ) - (u : ℤ)) aRef (1 : Mat d) =
        A (G + (l + u)) by dsimp only [A]; rw [hindex l u]]
      exact mul_le_mul_of_nonneg_right (hrawCoefficient u) (hA0 _)
    have hmajorSum : Summable major := by simpa only [major] using hinner l
    have hrawSum : Summable raw := Summable.of_nonneg_of_le hraw0 hrawMajor hmajorSum
    calc
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d K) (K - (l : ℤ)) aObs (1 : Mat d) ≤
        ∑' u : ℕ, raw u := by simpa only [raw] using hrawMax l
      _ ≤ ∑' u : ℕ, major u := hrawSum.tsum_le_tsum hrawMajor hmajorSum
      _ = observationParentRowMajorant epsilon abar aRef M K l := (hBdef l).symm
  have hparent : (∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n) =
      scalarIdentityWeakError aRef s M ^ 2 := by
    simpa only [A, originCube, scalarIdentityWeakError] using
      (Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum
        (originCube d M) hs aRef (1 : Mat d)).symm
  have htotal : (∑' l : ℕ, Book.Ch02.geometricWeight s 2 l *
      observationParentRowMajorant epsilon abar aRef M K l) ≤
      observationParentConvolutionFactor d s epsilon abar M K *
        scalarIdentityWeakError aRef s M ^ 2 := by
    calc
      (∑' l : ℕ, Book.Ch02.geometricWeight s 2 l *
          observationParentRowMajorant epsilon abar aRef M K l) =
        ∑' l : ℕ, Book.Ch02.geometricWeight s 2 l *
          ∑' u : ℕ, (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u)) := by
            apply tsum_congr
            intro l
            rw [hBdef l]
      _ ≤ (C * (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹) *
          Real.rpow (3 : ℝ) (2 * s * (G : ℝ)) *
            ∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n := hconvolution
      _ = observationParentConvolutionFactor d s epsilon abar M K *
          scalarIdentityWeakError aRef s M ^ 2 := by
        rw [hparent]
        simp only [observationParentConvolutionFactor, C, G]
  have hactive : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ M :=
    zpow_le_zpow_right₀ (by norm_num) hNM
  have hweak := hTail M hactive
  let target : ℝ := amplitude * (((3 : ℝ) ^ M) / ((3 : ℝ) ^ N)) ^ (-kappa)
  have htarget0 : 0 ≤ target :=
    mul_nonneg hAmplitude (Real.rpow_nonneg (by positivity) _)
  have hweakSq : scalarIdentityWeakError aRef s M ^ 2 ≤ target ^ 2 :=
    pow_le_pow_left₀ (scalarIdentityWeakError_nonneg aRef s M)
      (by simpa only [target] using hweak) 2
  have hfactor0 : 0 ≤ observationParentConvolutionFactor d s epsilon abar M K := by
    unfold observationParentConvolutionFactor
    exact mul_nonneg
      (mul_nonneg hC0 (inv_nonneg.mpr
        (Book.Ch02.book_geometricDiscount_nonneg (by
          exact mul_nonneg (by linarith only [hsHalf]) (by norm_num)))))
      (Real.rpow_nonneg (by norm_num) _)
  have herror := homogenizationErrorOnCube_infinity_two_le_sqrt_tsum_of_max_le
    (originCube d K) hs aObs (1 : Mat d)
      (observationParentRowMajorant epsilon abar aRef M K) hBsum hmax
  refine ⟨hBsum, hmax, herror.trans ?_⟩
  apply Real.sqrt_le_sqrt
  exact htotal.trans (mul_le_mul_of_nonneg_left hweakSq hfactor0)

end

end RowSupply
end HighContrast
end HCPolySupport
