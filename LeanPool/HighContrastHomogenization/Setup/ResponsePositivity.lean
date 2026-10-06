/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Support.HighContrast.EntryScale.BadMaximal.P1

/-!
# High-contrast homogenization: Setup.ResponsePositivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positive definiteness of the coarse response on the coefficient space

Every field of the coefficient space is uniformly elliptic almost everywhere on
every bounded set, so on each triadic cube it agrees almost everywhere with a
measurable everywhere uniformly elliptic field, and the deterministic
coarse-graining theory gives positive definiteness of the coarse response of that
field.  Since the coarse response only sees the almost everywhere class of the
field on the cube, this is the sample-side half of the well-formedness that
`e.Theta.m` presupposes.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A pointwise uniformly elliptic measurable field is a regular coefficient
field: its entries are bounded by the upper ellipticity constant, hence locally
integrable. -/
@[expose]
def regCoeffFieldOfPointwiseElliptic {lam Lam : ℝ} (f : CoeffField d)
    (hfm : Measurable f) (hfp : ∀ x, IsEllipticMatrix lam Lam (f x)) :
    RegCoeffField d where
  toFun := f
  entry_measurable := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)
  entry_locInt := fun i j =>
    RegCoeffField.locallyIntegrable_of_bounded_measurable
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm))
      (fun x => abs_apply_le_of_isEllipticMatrix (hfp x) i j)

@[simp] theorem regCoeffFieldOfPointwiseElliptic_toFun {lam Lam : ℝ}
    (f : CoeffField d) (hfm : Measurable f)
    (hfp : ∀ x, IsEllipticMatrix lam Lam (f x)) :
    (regCoeffFieldOfPointwiseElliptic f hfm hfp).toFun = f := rfl

/-- Pointwise uniform ellipticity gives locally uniform almost everywhere
ellipticity, with the same constants on every triadic cube. -/
theorem aeLocallyUniformlyEllipticField_of_pointwise {lam Lam : ℝ} {f : CoeffField d}
    (hfm : Measurable f) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hfp : ∀ x, IsEllipticMatrix lam Lam (f x)) :
    Book.Ch04.AELocallyUniformlyEllipticField
      (regCoeffFieldOfPointwiseElliptic f hfm hfp) := by
  intro Q
  refine ⟨lam, Lam, hlam, hle, IsAEEllipticFieldOn.of_isEllipticFieldOn ?_⟩
  refine ⟨?_, fun x _ => hfp x⟩
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact Measurable.ite (measurableSet_openCubeSet Q)
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)) measurable_const

/-- A measurable scalar field bounded on every ball around the origin is locally
integrable: a compact set lies in such a ball. -/
theorem locallyIntegrable_of_ball_bounded_measurable {f : Vec d → ℝ}
    (hf : Measurable f)
    (hbd : ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ x ∈ Metric.ball (0 : Vec d) R, |f x| ≤ C) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR, hkR⟩ := exists_ball_of_isBounded hk.isBounded
  obtain ⟨C, hC⟩ := hbd R hR
  refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne
    hf.aestronglyMeasurable (M := C) ?_
  filter_upwards [ae_restrict_mem_of_subset hkR measurableSet_ball] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

/-- A measurable field uniformly elliptic at every point of every ball around
the origin, with that ball's own constants, is a regular coefficient field: its
entries are bounded on each ball by the upper ellipticity constant there, hence
locally integrable. -/
@[expose]
def regCoeffFieldOfBallPointwiseElliptic (f : CoeffField d) (hfm : Measurable f)
    (hfp : ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ x ∈ Metric.ball (0 : Vec d) R, IsEllipticMatrix lam Lam (f x)) :
    RegCoeffField d where
  toFun := f
  entry_measurable := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)
  entry_locInt := fun i j =>
    locallyIntegrable_of_ball_bounded_measurable
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm))
      fun R hR => by
        obtain ⟨_lam, Lam, _hlam, _hle, hell⟩ := hfp R hR
        exact ⟨Lam, fun x hx => abs_apply_le_of_isEllipticMatrix (hell x hx) i j⟩

@[simp] theorem regCoeffFieldOfBallPointwiseElliptic_toFun (f : CoeffField d)
    (hfm : Measurable f)
    (hfp : ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ x ∈ Metric.ball (0 : Vec d) R, IsEllipticMatrix lam Lam (f x)) :
    (regCoeffFieldOfBallPointwiseElliptic f hfm hfp).toFun = f := rfl

/-- Pointwise uniform ellipticity on every ball gives locally uniform almost
everywhere ellipticity: a triadic cube lies in a ball, whose constants serve
it. -/
theorem aeLocallyUniformlyEllipticField_of_ball_pointwise {f : CoeffField d}
    (hfm : Measurable f)
    (hfp : ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ x ∈ Metric.ball (0 : Vec d) R, IsEllipticMatrix lam Lam (f x)) :
    Book.Ch04.AELocallyUniformlyEllipticField
      (regCoeffFieldOfBallPointwiseElliptic f hfm hfp) := by
  intro Q
  obtain ⟨R, hR, hQR⟩ :=
    exists_ball_of_isBounded (isBoundedDomain_openCubeSet Q).isBounded
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hfp R hR
  refine ⟨lam, Lam, hlam, hle, IsAEEllipticFieldOn.of_isEllipticFieldOn ?_⟩
  refine ⟨?_, fun x hx => hell x (hQR hx)⟩
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact Measurable.ite (measurableSet_openCubeSet Q)
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)) measurable_const

/-- **The coarse response of a sample is positive definite** on every centered
triadic cube. -/
theorem blockPosDef_coarseBlock [NeZero d] (m : ℤ) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock (centeredCube d m) a) := by
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hfp, hfa⟩ :=
    exists_globally_elliptic_representative_ae_eq_on a.2
      (isBoundedDomain_openCubeSet (originCube d m)).isBounded
  have hposCube : Book.Ch02.BlockPosDef
      (coarseBlockMatrix (cubeSet (originCube d m)) f) := by
    have h :=
      HighContrast.EntryScale.coarseBlockMatrix_cubeSet_blockPosDef_of_uniformEllipticity
      (a := regCoeffFieldOfPointwiseElliptic f hfm hfp) (originCube d m)
      (aeLocallyUniformlyEllipticField_of_pointwise hfm hlam hle hfp)
    exact h
  have h1 : coarseBlock (centeredCube d m) a =
      coarseBlockMatrix (openCubeSet (originCube d m)) f :=
    coarseBlockMatrix_congr_of_ae_eq hfa
  have h2 : coarseBlockMatrix (cubeSet (originCube d m)) f =
      coarseBlockMatrix (openCubeSet (originCube d m)) f :=
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet m f
  rw [h1, ← h2]
  exact hposCube

/-- **The annealed block is positive definite** once the coarse response is
integrable over the law. -/
theorem blockPosDef_annealedBlock_centeredCube [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (m : ℤ)
    (hint : HasIntegrableCoarseBlock P (centeredCube d m)) :
    Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d m)) :=
  blockPosDef_annealedBlock hint (blockPosDef_coarseBlock m)

end

end HighContrast
end HCPolySupport
