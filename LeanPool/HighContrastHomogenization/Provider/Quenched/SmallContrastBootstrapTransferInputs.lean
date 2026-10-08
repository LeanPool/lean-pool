/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapReverseAdapter
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.CorrectedTiltConsumer

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBootstrapTransferInputs

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrected-tilt transfer inputs

The corrected tilt transfer consumes, at the corrected halfway
scale `n = ⌊m/2⌋ + n₀` of the midpoint-scale identity, four inputs: the reverse Loewner
adapter, the unit cap on the absorbed size, the unit cap on the hatted defect,
and the decaying error clause.  The first, second and fourth are supplied here
from the reverse adapter with its generation-free law factor; the third is the
bootstrap smallness at tolerance one.

The only arithmetic in this file is the passage from the adapter's integer
scale difference `-(m − n)` to the natural-number difference the corrected
transfer writes, which needs `n ≤ m`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The adapter's triadic error factor written with the natural-number scale
difference of the corrected halfway transfer. -/
theorem three_rpow_neg_intCast_sub_eq {a b : ℕ} (hab : b ≤ a) :
    (3 : ℝ) ^ (-((((a : ℕ) : ℤ) : ℝ) - (((b : ℕ) : ℤ) : ℝ))) =
      Real.rpow (3 : ℝ) (-((a - b : ℕ) : ℝ)) := by
  have hexp : -((((a : ℕ) : ℤ) : ℝ) - (((b : ℕ) : ℤ) : ℝ)) =
      -((a - b : ℕ) : ℝ) := by
    rw [Nat.cast_sub hab]
    push_cast
    ring
  rw [hexp]
  rfl

/-- **The corrected-tilt transfer inputs.**  At the corrected halfway scale the
reverse Euclidean adapter supplies the Loewner comparison together with the
unit cap on the absorbed size and the decaying error clause, in the exact
shapes the corrected tilt transfer consumes.  The hatted unit
cap and the hatted tail are the two remaining inputs; the first is the
bootstrap smallness at tolerance one, the second is the recursion's decay. -/
theorem exists_corrected_tilt_transfer_inputs (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ mAl : Mat d, mAl.PosDef →
              ∀ G : ℕ, ‖roundedGrid l mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ G →
                ∀ n₀ mOut : ℕ,
                  0 < Prop42Scalar.correctedTiltScale n₀ mOut →
                  Prop42Scalar.correctedTiltScale n₀ mOut < mOut →
                  l ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) →
                  0 ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) +
                    (G : ℤ) - 1 - sK →
                  ∀ A : ℝ, CB * reverseAdapterFactor Cd g K E mAl G ≤ A →
                    A * Real.rpow (3 : ℝ)
                        (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                          ℕ) : ℝ)) ≤ 1 →
                    ∃ c : ℝ, 0 ≤ c ∧
                      BlockMatLoewnerLE
                        (blockSub (annealedBlock P (centeredCube d (mOut : ℤ)))
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)))
                        (blockScale c E) ∧
                      c * blockSize E
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)) ≤
                        1 ∧
                      (9 / 2 : ℝ) *
                          (c * blockSize E
                            (adaptedMean P (roundedGrid l mAl)
                              (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ))) ≤
                        (9 / 2 : ℝ) * A * Real.rpow (3 : ℝ)
                          (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                            ℕ) : ℝ)) := by
  classical
  obtain ⟨CB, hCB0, hCB⟩ := exists_reverse_adapter_error_bound d hd g hg
  refine ⟨CB, hCB0, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK0 hsK l hl mAl hmAl G hqnorm
    n₀ mOut hn0 hnm hln hDelta A hA hAcap
  have hnmZ : ((Prop42Scalar.correctedTiltScale n₀ mOut : ℕ) : ℤ) <
      ((mOut : ℕ) : ℤ) := by exact_mod_cast hnm
  have hn0Z : (0 : ℤ) < ((Prop42Scalar.correctedTiltScale n₀ mOut : ℕ) : ℤ) := by
    exact_mod_cast hn0
  obtain ⟨c, hc0, hsub, hbound⟩ := hCB P E Ψ K S hP hstat hunit hdag Cd hCd
    sK hsK0 hsK l hl mAl hmAl G hqnorm 0
    ((Prop42Scalar.correctedTiltScale n₀ mOut : ℕ) : ℤ) ((mOut : ℕ) : ℤ)
    le_rfl hn0Z hnmZ hln hDelta
  rw [three_rpow_neg_intCast_sub_eq hnm.le] at hbound
  have hrpow0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ)
      (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut : ℕ) : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hstep : CB * reverseAdapterFactor Cd g K E mAl G *
      Real.rpow (3 : ℝ)
        (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut : ℕ) : ℝ)) ≤
      A * Real.rpow (3 : ℝ)
        (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hA hrpow0
  refine ⟨c, hc0, hsub, ?_, ?_⟩
  · linarith only [hbound, hstep, hAcap]
  · linarith only [hbound, hstep]

end

end HCPolySupport.HighContrast.Quenched
