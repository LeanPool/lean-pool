/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Law

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

/-- The exact Chapter 4 local-ellipticity support event is measurable.  This is the
countable quantitative-slice characterization of CoarseGraining's own
`AELocallyUniformlyEllipticField`, kept local so the cutoff construction does not depend
on the unrelated high-contrast development where the general lemma also occurs. -/
private theorem measurableSet_aeLocallyUniformlyEllipticField :
    MeasurableSet {a : RegCoeffField d | Ch04.AELocallyUniformlyEllipticField a} := by
  classical
  have hEq : {a : RegCoeffField d | Ch04.AELocallyUniformlyEllipticField a}
      = ⋂ Q : TriadicCube d, ⋃ k : ℕ,
          {a : RegCoeffField d |
            AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k, hk⟩ := ha Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
          (cubeSet Q) a.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

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
