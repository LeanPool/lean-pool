/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Law
public import LeanPool.Superdiffusion.Support.HighContrast.LocalEllipticity

/-!
# LawCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Chapter 4 law carrier of the genuine coefficient cutoff

For every public lower-tail sample, the literal cutoff coefficient has the
canonical compatible Chapter 2 coefficient family.  This gives locally a.e.
uniform ellipticity *everywhere on the source carrier*.  The Chapter 4
`RestrictionLawCarrier` then follows by transport through the actual measurable
pushforward law; no stationarity, range, isotropy, adjoint invariance, or
quantitative input is bundled here.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-- On every triadic cube, the literal cutoff coefficient has the exact a.e.
ellipticity data stored by its canonical Chapter 2 `CoeffOn` object. -/
theorem coefficientCutoff_aeeEllipticOn (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    Ch04.AEEllipticOn M.nu (coefficientCutoffCubeEllipticityUpper M m omega Q)
      (openCubeSet Q) (coefficientCutoff M.nu m omega) := by
  change IsAEEllipticFieldOn
    (coefficientCutoffCoeffOn M m omega Q).lam
    (coefficientCutoffCoeffOn M m omega Q).Lam
    ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d))
    (coefficientCutoffCoeffOn M m omega Q).toCoeffField
  exact ⟨(coefficientCutoffCoeffOn M m omega Q).measurableSet,
    (coefficientCutoffCoeffOn M m omega Q).aeStronglyMeasurable,
    (coefficientCutoffCoeffOn M m omega Q).aeElliptic⟩

/-- Every genuine cutoff realization belongs to the exact Chapter 4 local
a.e.-uniform-ellipticity carrier.  The witnesses are the source coefficient's
canonical cube-wise `CoeffOn` witnesses, including their realised upper bound. -/
theorem coefficientCutoff_aeLocallyUniformlyEllipticField (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) :
    Ch04.AELocallyUniformlyEllipticField (coefficientCutoff M.nu m omega) := by
  intro Q
  refine ⟨M.nu, coefficientCutoffCubeEllipticityUpper M m omega Q, M.nu_pos, ?_, ?_⟩
  · exact (coefficientCutoffCoeffOn M m omega Q).lam_le_Lam
  · exact coefficientCutoff_aeeEllipticOn M m omega Q

/-- The actual pushforward coefficient law is supported on the exact Chapter 4
locally a.e.-uniformly elliptic carrier. -/
theorem coefficientCutoffLaw_aeLocallyUniformlyElliptic (M : ABKModel d) (m : ℤ) :
    Ch04.AELocallyUniformlyEllipticLaw (coefficientCutoffLaw M m) := by
  rw [Ch04.AELocallyUniformlyEllipticLaw, coefficientCutoffLaw_eq_map,
    ae_map_iff (measurable_coefficientCutoff M.nu m).aemeasurable
      measurableSet_aeLocallyUniformlyEllipticField]
  exact Filter.Eventually.of_forall fun omega =>
    coefficientCutoff_aeLocallyUniformlyEllipticField M m omega

/-- The genuine cutoff law supplies exactly the two Chapter 4
`RestrictionLawCarrier`
fields: probability and local a.e.-uniform ellipticity support. -/
theorem coefficientCutoffLaw_lawCarrier (M : ABKModel d) (m : ℤ) :
    Ch04.RestrictionLawCarrier (coefficientCutoffLaw M m) :=
  Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    (coefficientCutoffLaw_aeLocallyUniformlyElliptic M m)

end

end Algsuperdiff.Section3.Cutoff
