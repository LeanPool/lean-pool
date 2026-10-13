/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEllipticitySlot
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueCap
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlotTransportChildCube

/-!
# InteriorEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The child-frame coarse-graining objects, capped at the anchor's own slot

With the re-based family and the re-cut slot of `InteriorEllipticitySlot`, both
coarse-graining objects the interior clause's right-hand side carries at the
child cube `□_n` — the `q = 1` error at depth `0` and the ellipticity factors
`λ_{s/6,2}`, `Λ_{s/6,2}` inside CoarseGraining's forcing bracket — are read at
the index `s/6`.

Two steps, both proved elsewhere and composed here:

* **the off-grid cap** (`InteriorGlueCap`, printed slot `(s/6, s/8)`): that
  functional is bounded by the anchor's own
  `fluxCorrectedErrorRepresentative M L (n+2) ⟨s/8⟩` at the translated sample;
* **the good event** (`GoodEventCaps`): the representative is bounded by `C/2`.

The result is the pair of caps the interior assembly consumes: the energy leg's
`𝓔` factor **retained** at the anchor's printed index (it is a factor of the
anchor's own first summand), and the forcing bracket collapsed to a constant.

## Why the slot sits at `s/6`

At `r = s/3` the child's index is `s/6 > s/8` and the proved cap applies
verbatim.  See `InteriorEllipticitySlot`.

## References

* ABK26, `e.mathcalE.stability.applied`; `e.bound.Lambdas.by.Es.v2`;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 0. The comparator, in the two spellings -/

/-- The anchor's isotropic comparator matrix is CoarseGraining's scalar matrix. -/
private theorem isotropicComparator_eq_scalarMatrix (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) := rfl

/-! ## 1. The frame bridge at the re-based family -/

/-- **The child-frame error object is the off-grid error at `w = x − z`.**

Exact; no constant.  The family hypothesis of `InteriorGlueFrame` is the frame
identity. -/
theorem homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid [NeZero d]
    (M : ABKModel d) (L k n : ℤ) (x z : Vec d) (omega : Cutoff.CutoffSample d)
    {t : ℝ} (ht : 0 < t) (a0 : Mat d) :
    Ch02.HomogenizationErrorOnCube (originCube d n) t .infinity (.finite 2)
        (parentRebasedFamily M L k x z omega) a0 =
      offGridErrorFunctional (x - z) (originCube d n) t
        (Support.fluxCorrectedRegField M L k (originCube d k)
          (Cutoff.translateCutoffSample z omega)).toFun a0 :=
  (offGridErrorFunctional_eq_homogenizationErrorOnCube_translate (x - z) (originCube d n)
    ht (parentRebasedFamily M L k x z omega) _
    (parentRebasedFamily_coeffOn_eq_translateCoeffField M L k x z omega) a0).symm

/-! ## 2. The `q = 2` error at the child cube, capped at the anchor's index -/

/-- **The child-frame `𝓔_{s/6,∞,2}`, against the anchor's own representative.**

On one probability-one event, for every off-lattice centre `x` and every ambient
scale `m` the anchor's geometry binder relates. -/
theorem ae_homogenizationErrorOnCube_rebased_le_representative [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        Ch02.HomogenizationErrorOnCube (originCube d n) (s / 6) .infinity (.finite 2)
            (parentRebasedFamily M L (n + 2) x z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (2 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 2)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_offGridChildError_le_representative_harmonicSlot M L n z hs hs1]
    with omega hall
  intro x m hgeom
  have hbase := hall x m hgeom
  rwa [homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid M L (n + 2) n x z omega
    (by linarith only [hs] : (0 : ℝ) < s / 6)
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2)))]

/-! ## 3. The energy leg's `𝓔` factor, at the printed index -/

/-- **The `q = 1` error at depth `0` of the re-cut slot, at the anchor's own
representative.**

`𝓔_{s/3,∞,1}(□_n; ã_x, σ) ≤ √C(d) · 3^{s/4} · 𝓔_{s/8,∞,2}(□_{n+2}; ã_z, σ)`,
the right-hand factor being the anchor's printed
`fluxCorrectedErrorRepresentative M L (n+2) ⟨s/8⟩`.  This is the factor the
frozen statement's **first** interior summand carries; it is not capped here. -/
theorem ae_coarseGrainingErrorAtDepth_rebased_le_representative [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
            (parentRebasedFamily M L (n + 2) x z omega)
            (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) 0 ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (2 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 2)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_homogenizationErrorOnCube_rebased_le_representative M L n z hs hs1]
    with omega hall
  intro x m hgeom
  have hdepth := coarseGrainingHomogenizationErrorAtDepth_le (originCube d n)
    (parentRebasedFamily M L (n + 2) x z omega)
    (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (r := s / 3) (t := s / 6) 0
    (by linarith only [hs]) (by linarith only [hs])
  have hone : Real.rpow (3 : ℝ) (s / 6 * ((0 : ℕ) : ℝ)) = 1 := by
    norm_num
  rw [hone, one_mul] at hdepth
  have hmat : (scalarComparator (d := d) (Annealed.sigmaBar M (n + 2)).2).matrix =
      isotropicComparatorMatrix (d := d) (Annealed.sigmaBar M (n + 2)) := by
    rw [scalarComparator_matrix, isotropicComparator_eq_scalarMatrix]
  rw [hmat] at hdepth
  exact hdepth.trans (hall x m hgeom)

/-! ## 4. The ellipticity ratio at the child frame -/

/-- **`e.bound.Lambdas.by.Es.v2` at the child cube, in the child's own frame.**

The coarse-grained ellipticity factors of the re-based family at the slot index
`s/6`, against the anchor's own representative. -/
theorem ae_ellipticityRatio_rebased_le_representative [NeZero d] (M : ABKModel d)
    (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        max (((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ *
              Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2)
                (parentRebasedFamily M L (n + 2) x z omega))
            ((Annealed.sigmaBar M (n + 2) : ℝ) *
              (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2)
                (parentRebasedFamily M L (n + 2) x z omega))⁻¹) ≤
          2 * (d : ℝ) *
            ((Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                ((3 : ℝ) ^ (2 * (s / 8)) *
                  fluxCorrectedErrorRepresentative M L (n + 2)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega))) ^ 2 + 1) := by
  filter_upwards [ae_homogenizationErrorOnCube_rebased_le_representative M L n z hs hs1]
    with omega hall
  intro x m hgeom
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d) (originCube d n)
    (parentRebasedFamily M L (n + 2) x z omega) hs6 (Annealed.sigmaBar M (n + 2)).2
  rw [← isotropicComparator_eq_scalarMatrix] at hratio
  have hnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d n) (s / 6) .infinity
      (.finite 2) (parentRebasedFamily M L (n + 2) x z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) hs6
  exact hratio.trans (two_mul_dim_mul_sq_add_one_le_of_le hnn (hall x m hgeom))

/-! ## 5. CoarseGraining's forcing bracket at the child frame -/

/-- Three `Real.rpow` normalizations, in the `Real.sqrt` spelling the bracket
arithmetic uses. -/
theorem rpow_half_eq_sqrt (x : ℝ) : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
  show x ^ (1 / 2 : ℝ) = _
  rw [← Real.sqrt_eq_rpow]

theorem rpow_neg_half_eq_sqrt_inv {x : ℝ} (hx : 0 < x) :
    Real.rpow x (-(1 / 2 : ℝ)) = Real.sqrt x⁻¹ := by
  show x ^ (-(1 / 2 : ℝ)) = _
  rw [Real.rpow_neg hx.le, ← Real.inv_rpow hx.le, ← Real.sqrt_eq_rpow]

theorem rpow_neg_one_eq_inv {x : ℝ} (hx : 0 < x) :
    Real.rpow x (-1 : ℝ) = x⁻¹ := by
  show x ^ (-1 : ℝ) = _
  rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_one]

/-- **The forcing bracket at the child frame, in terms of the anchor's own
representative.**

The comparator's scale `σ_{n+2}` cancels between the ellipticity factors and
the matrix norm, so the bound is `σ`-free: it depends only on `d`, on the
proved off-grid constant and on the anchor's `𝓔_{s/8}` representative.  On the
good event the representative is a constant, so the whole bracket is. -/
theorem ae_forceBracket_rebased_le [NeZero d] (M : ABKModel d) (L n : ℤ) (z : Vec d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        coarseGrainingForceBracket (originCube d n)
            (parentRebasedFamily M L (n + 2) x z omega)
            (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) ≤
          Real.sqrt (2 * (d : ℝ) *
                ((Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                    ((3 : ℝ) ^ (2 * (s / 8)) *
                      fluxCorrectedErrorRepresentative M L (n + 2)
                        ⟨s / 8, by linarith only [hs]⟩
                        (Cutoff.translateCutoffSample z omega))) ^ 2 + 1)) *
              (Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                ((3 : ℝ) ^ (2 * (s / 8)) *
                  fluxCorrectedErrorRepresentative M L (n + 2)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega))) +
            2 * (2 * (d : ℝ) *
                ((Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                    ((3 : ℝ) ^ (2 * (s / 8)) *
                      fluxCorrectedErrorRepresentative M L (n + 2)
                        ⟨s / 8, by linarith only [hs]⟩
                        (Cutoff.translateCutoffSample z omega))) ^ 2 + 1)) := by
  filter_upwards [ae_coarseGrainingErrorAtDepth_rebased_le_representative M L n z hs hs1,
    ae_ellipticityRatio_rebased_le_representative M L n z hs hs1] with omega herr hratio
  intro x m hgeom
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  set A : Ch03.CoeffFamily d := parentRebasedFamily M L (n + 2) x z omega with hAdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 2) : ℝ) with hsigdef
  have hsig : 0 < sig := (Annealed.sigmaBar M (n + 2)).2
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
      ((3 : ℝ) ^ (2 * (s / 8)) *
        fluxCorrectedErrorRepresentative M L (n + 2) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega)) with hEbdef
  set Kb : ℝ := 2 * (d : ℝ) * (Eb ^ 2 + 1) with hKbdef
  have hKb : 0 ≤ Kb := by
    rw [hKbdef]
    have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ Eb ^ 2 + 1 := by positivity
    exact mul_nonneg h1 h2
  have hlam : 0 < Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A :=
    Ch02.lambdaSq_finite_pos (originCube d n) A hs6 (by norm_num)
  have hLam : 0 < Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A :=
    Ch02.LambdaSq_finite_pos (originCube d n) A hs6 (by norm_num)
  have hrat := hratio x m hgeom
  have h1 : sig⁻¹ * Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A ≤ Kb :=
    le_trans (le_max_left _ _) hrat
  have h2 : sig * (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ ≤ Kb :=
    le_trans (le_max_right _ _) hrat
  have hErrDepth := herr x m hgeom
  have hErrDepthNn : 0 ≤ Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n) A
      (scalarComparator (d := d) hsig) (s / 3) 0 :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg (originCube d n) A _
      (by linarith only [hs]) 0
  have hprodInv : Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A *
      (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ ≤ Kb * Kb := by
    have heq : Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A *
        (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ =
        (sig⁻¹ * Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A) *
          (sig * (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹) := by
      field_simp
    rw [heq]
    exact mul_le_mul h1 h2 (mul_nonneg hsig.le (inv_pos.mpr hlam).le)
      (le_trans (mul_nonneg (inv_pos.mpr hsig).le hLam.le) h1)
  -- the second bracket summand
  have hT2 : Ch03.poincareUpperEllipticityFactor (originCube d n) A (s / 6) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor (originCube d n) A (s / 6) (.finite 2) ≤ Kb := by
    rw [Ch03.poincareUpperEllipticityFactor, Ch03.poincareLowerEllipticityFactor,
      rpow_half_eq_sqrt, rpow_neg_half_eq_sqrt_inv hlam,
      ← Real.sqrt_mul hLam.le]
    refine le_trans (Real.sqrt_le_sqrt hprodInv) ?_
    rw [show Kb * Kb = Kb ^ (2 : ℕ) by ring, Real.sqrt_sq hKb]
  -- the third bracket summand
  have hT3 : Ch03.constantCoeffMatrixNorm (scalarComparator (d := d) hsig) *
      Real.rpow (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A) (-1 : ℝ) ≤ Kb := by
    rw [constantCoeffMatrixNorm_scalarComparator hsig, rpow_neg_one_eq_inv hlam]
    exact h2
  -- the first bracket summand
  have hT1 : Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsig) *
      Ch03.poincareLowerEllipticityFactor (originCube d n) A (s / 6) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n) A
        (scalarComparator (d := d) hsig) (s / 3) 0 ≤
      Real.sqrt Kb * Eb := by
    have hhalf : Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsig) *
        Ch03.poincareLowerEllipticityFactor (originCube d n) A (s / 6) (.finite 2) ≤
        Real.sqrt Kb := by
      rw [constantCoeffMatrixNormHalf_scalarComparator hsig,
        Ch03.poincareLowerEllipticityFactor, rpow_half_eq_sqrt,
        rpow_neg_half_eq_sqrt_inv hlam, ← Real.sqrt_mul hsig.le]
      exact Real.sqrt_le_sqrt h2
    exact mul_le_mul hhalf hErrDepth hErrDepthNn (Real.sqrt_nonneg _)
  rw [coarseGrainingForceBracket, show s / 3 / 2 = s / 6 by ring]
  linarith only [hT1, hT2, hT3]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
