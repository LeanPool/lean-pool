/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds.LawObservable
public import LeanPool.HighContrastHomogenization.Support.Probability.RandomFieldMeasurability

/-!
# Measurability of the local ellipticity event

Ported from scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
The countable quantitative-slice characterization is shared by the cutoff,
flux-corrected and corridor laws without importing the corridor construction.
-/

@[expose] public section

open HCPolySupport.Book.Ch04 (AELocallyUniformlyEllipticField)
open MeasureTheory

namespace HCPolySupport

variable {d : ℕ}

/-- The set of locally a.e.-uniformly elliptic carrier fields is genuinely
measurable: it equals the countable `⋂_Q ⋃_k` of the AEE quantitative-slice
sets (`AELocallyUniformlyEllipticField.exists_aeeQuantitativeEllipticSlice_cubeSet`
forward; the definition `AEEQuantitativeEllipticSlice = IsAEEllipticFieldOn (k+1)⁻¹ (k+1)`
plus `IsAEEllipticFieldOn.mono` to the open core backward), each slice set being
genuinely `LocalSigmaR`-measurable on the carrier
(`measurableSet_localSigmaR_aeeQuantitativeEllipticSlice`, Packet P4b) and
`LocalSigmaR ≤` the canonical carrier σ-algebra. -/
theorem measurableSet_aeLocallyUniformlyEllipticField :
    MeasurableSet {b : RegCoeffField d | AELocallyUniformlyEllipticField b} := by
  classical
  have hEq : {b : RegCoeffField d | AELocallyUniformlyEllipticField b}
      = ⋂ Q : TriadicCube d, ⋃ k : ℕ,
          {b : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k b.toFun} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hb Q
      exact hb.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro hb Q
      obtain ⟨k, hk⟩ := hb Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) (cubeSet Q) b.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (Book.Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

end HCPolySupport
