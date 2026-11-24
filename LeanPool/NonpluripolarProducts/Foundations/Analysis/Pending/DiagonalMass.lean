/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedMass

/-!
# Diagonal non-pluripolar mass

This is the diagonal specialization of the actual global mixed
non-pluripolar measure.  It lives in `Pending` because the global construction
still imports explicit analytic holes, although the definitions and proof
independence below contain no new `sorry`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.DiagonalMass

open FirstPass FirstPass.PositiveClasses MixedMass GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The top non-pluripolar mass of one potential in one background. -/
def diagonalMass (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : ThetaPlurisubharmonic θ.val u) : ℝ≥0∞ :=
  globalMixedMass (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu)

/-- Positivity of the actual diagonal non-pluripolar mass. -/
def HasPositiveMass (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : ThetaPlurisubharmonic θ.val u) : Prop :=
  0 < diagonalMass θ u hu

/-- The actual diagonal non-pluripolar measure of a genuine global theta-psh
potential.  The
`LocallyNondegenerate` component of `IsThetaPshPotential` excludes the raw
locally-identically-minus-infinity inputs that are absent from the source's
`PSH(X, θ)` convention. -/
def diagonalPotentialMeasure (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) : Measure M :=
  globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu.1)

/-- The diagonal mass is the whole-space mass of the actual diagonal
non-pluripolar measure. -/
def diagonalPotentialMass (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) : ℝ≥0∞ :=
  diagonalPotentialMeasure θ u hu Set.univ

/-- Positive non-pluripolar top mass for a genuine theta-psh potential. -/
def HasPositivePotentialMass (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) : Prop :=
  0 < diagonalPotentialMass θ u hu

omit [BorelSpace M] in
/-- The mass is independent of the proof witnessing theta-plurisubharmonicity. -/
theorem diagonalMass_proof_independent {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu hv : ThetaPlurisubharmonic θ.val u) :
    diagonalMass θ u hu = diagonalMass θ u hv := by
  unfold diagonalMass globalMixedMass
  exact congrArg (fun μ : Measure M => μ Set.univ)
    (globalMixedMeasure_proof_independent (fun _ => hu) (fun _ => hv))

omit [BorelSpace M] in
theorem hasPositiveMass_proof_independent {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu hv : ThetaPlurisubharmonic θ.val u) :
    HasPositiveMass θ u hu ↔ HasPositiveMass θ u hv := by
  simp only [HasPositiveMass, diagonalMass_proof_independent hu hv]

omit [BorelSpace M] in
/-- The actual diagonal measure is independent of the proof witnessing the
theta-PSH property. -/
theorem diagonalPotentialMeasure_proof_independent
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu hv : IsThetaPshPotential θ.val u) :
    diagonalPotentialMeasure θ u hu = diagonalPotentialMeasure θ u hv :=
  globalMixedMeasure_proof_independent (fun _ => hu.1) (fun _ => hv.1)

omit [BorelSpace M] in
@[simp] theorem diagonalPotentialMeasure_univ
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    diagonalPotentialMeasure θ u hu Set.univ = diagonalPotentialMass θ u hu :=
  rfl

omit [BorelSpace M] in
theorem diagonalPotentialMass_proof_independent {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu hv : IsThetaPshPotential θ.val u) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ u hv := by
  exact congrArg (fun μ : Measure M => μ Set.univ)
    (diagonalPotentialMeasure_proof_independent hu hv)

omit [BorelSpace M] in
theorem hasPositivePotentialMass_proof_independent
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu hv : IsThetaPshPotential θ.val u) :
    HasPositivePotentialMass θ u hu ↔ HasPositivePotentialMass θ u hv := by
  simp only [HasPositivePotentialMass,
    diagonalPotentialMass_proof_independent hu hv]

end

end SGPT.Foundations.Analysis.Pending.DiagonalMass
