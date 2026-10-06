/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.SeminormRecurrence

/-!
# Coarse-graining support: Support.Deterministic.CoarsePoincareRHS.Constants

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

noncomputable section

/-- Coefficient prefactor in the local absorbed RHS error. -/
@[expose]
noncomputable def coarsePoincareRHSLocalCoeff {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) : ℝ :=
  (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹

/-- Intrinsic local energy piece in the absorbed RHS error. -/
@[expose]
noncomputable def coarsePoincareRHSIntrinsicLocalEnergyError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d) (s : ℝ) : ℝ :=
  2 * coarsePoincareRHSLocalCoeff Q a s * cubeAverage Q (coefficientEnergyDensity a u)

/-- Intrinsic local forcing multiplier in the absorbed RHS error.

The uniform ellipticity lower bound is intentionally absent: quantitative
dependence runs through `lambdaSq`, while `IsEllipticFieldOn` only supplies
well-posedness and nonnegativity hypotheses. -/
@[expose]
noncomputable def coarsePoincareRHSIntrinsicLocalForceMultiplier {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) : ℝ :=
  coarsePoincareRHSLocalCoeff Q a s *
    ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))

/-- Centered local forcing seminorm in the absorbed RHS error. -/
@[expose]
noncomputable def coarsePoincareRHSLocalCenteredForceSeminorm {d : ℕ}
    (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) : ℝ :=
  cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)

/-- The global positive-Besov forcing bound localized to descendants of depth `n`. -/
@[expose]
noncomputable def coarsePoincareRHSGlobalForceBound {d : ℕ}
    (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ) : ℝ :=
  ((Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2)⁻¹ *
    (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2

/-- Intrinsic local forcing piece in the absorbed RHS error. -/
@[expose]
noncomputable def coarsePoincareRHSIntrinsicLocalForceError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d) (s : ℝ) : ℝ :=
  (coarsePoincareRHSIntrinsicLocalForceMultiplier Q a s *
    coarsePoincareRHSLocalCenteredForceSeminorm Q g s) ^ 2

/-- Intrinsic local non-child error produced by the absorbed RHS one-cube recurrence. -/
@[expose]
noncomputable def coarsePoincareRHSIntrinsicAbsorbedLocalError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g u : Vec d → Vec d)
    (s η : ℝ) : ℝ :=
  let A : ℝ := coarsePoincareRHSIntrinsicLocalEnergyError Q a u s
  let K : ℝ := coarsePoincareRHSIntrinsicLocalForceMultiplier Q a s
  let G : ℝ := coarsePoincareRHSLocalCenteredForceSeminorm Q g s
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  A + η * U ^ 2 +
    η * ((1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2))) +
    2 * η⁻¹ * ((K * G) ^ 2)

/-- Parent half-scale coefficient used after localizing `lambda_{s,2}^{-1}`. -/
@[expose]
noncomputable def coarsePoincareRHSParentHalfCoeff {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) : ℝ :=
  (geometricDiscount s 2)⁻¹ *
    (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
      (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)

/-- Intrinsic parent half-scale forcing multiplier used after localizing `lambda_{s,2}^{-1}`. -/
@[expose]
noncomputable def coarsePoincareRHSIntrinsicParentHalfForceMultiplier {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) : ℝ :=
  coarsePoincareRHSParentHalfCoeff Q a s n *
    ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))

/-- Coefficient of the local energy average after expanding the absorbed error. -/
@[expose]
noncomputable def coarsePoincareRHSAbsorbedEnergyCoeff (η : ℝ) : ℝ :=
  1 + η * (1 - η)⁻¹

/-- Coefficient of the current `R_n` term after expanding the absorbed error. -/
@[expose]
noncomputable def coarsePoincareRHSAbsorbedRnCoeff (η : ℝ) : ℝ :=
  η + η ^ 2 * (1 - η)⁻¹

/-- Coefficient of the local forcing average after expanding the absorbed error. -/
@[expose]
noncomputable def coarsePoincareRHSAbsorbedForceCoeff (η : ℝ) : ℝ :=
  2 * η * (1 - η)⁻¹ * η⁻¹ + 2 * η⁻¹

/-- Absorption parameter that makes the scaled recurrence use the note-step
ratio exactly. -/
@[expose]
noncomputable def coarsePoincareRHSNoteEta (s : ℝ) : ℝ :=
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  (1 - r) / (2 - r)

/-- Exact energy envelope after inserting `coarsePoincareRHSNoteEta`. -/
@[expose]
noncomputable def coarsePoincareRHSNoteEnergyEnvelope (s : ℝ) : ℝ :=
  (1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s))⁻¹ *
    coarsePoincareRHSAbsorbedEnergyCoeff (coarsePoincareRHSNoteEta s)

/-- Exact forcing envelope after inserting `coarsePoincareRHSNoteEta`. -/
@[expose]
noncomputable def coarsePoincareRHSNoteForceEnvelope (s : ℝ) : ℝ :=
  (1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s))⁻¹ *
    coarsePoincareRHSAbsorbedForceCoeff (coarsePoincareRHSNoteEta s)

/-- The fixed one-step discount in the current natural-depth `R_n` recurrence. -/
@[expose]
noncomputable def coarsePoincareRHSDiscount (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (-2 * s)

/-- The one-step discount after the note-style scaling from `R_n` to `S_n`. -/
@[expose]
noncomputable def coarsePoincareRHSStepDiscount (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (-s)

/-- Abstract one-step coefficient after passing from `R_n` to the scaled `S_n`. -/
@[expose]
noncomputable def coarsePoincareRHSScaledStepCoeff (s θ : ℝ) : ℝ :=
  θ * Real.rpow (3 : ℝ) s

/-- The note-facing one-step coefficient `3^{-3s/2}` for the `R_n` recurrence. -/
@[expose]
noncomputable def coarsePoincareRHSNoteStepCoeff (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (-(3 * s / 2))

/-- Ratio governing the localized energy coefficient sums after inserting parent `q = 2` bounds. -/
@[expose]
noncomputable def coarsePoincareRHSFiniteSumRatio (s θ : ℝ) : ℝ :=
  coarsePoincareRHSScaledStepCoeff s θ

/-- Ratio governing the localized force coefficient sums after inserting parent `q = 2` bounds. -/
@[expose]
noncomputable def coarsePoincareRHSForceFiniteSumRatio (s θ : ℝ) : ℝ :=
  coarsePoincareRHSScaledStepCoeff s θ * Real.rpow (3 : ℝ) (-s)


end

end HCPolySupport
