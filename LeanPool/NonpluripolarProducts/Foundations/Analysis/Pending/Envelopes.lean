/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

/-!
# Compatibility wrappers for analytic properties of the actual envelopes

These three statements are now exact wrappers around proofs in the checked
core. They concern the concrete supremum and regularization and do not define pseudoeffectivity
or assume an abstract envelope operator. Compactness, a nonempty manifold,
closedness, type (1,1), local potentials and nonempty theta-PSH potentials are
explicit in the signatures. `IsComplexManifold` includes Hausdorffness,
second-countability and holomorphic chart compatibility. Its model is the
concrete finite-dimensional Euclidean complex space with compatible real
scalars. No ambient measure is a parameter of these disc-based statements,
so no unmentioned Borel or Haar structure on the manifold is needed.

The proofs use locally bounded PSH supremum regularization, change of smooth
local potential, and normalization by a finite upper bound on a compact
manifold. Nothing here asserts non-pluripolar mass preservation.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

/-- The pointwise supremum V_theta is already a genuine
theta-PSH potential; in particular its regularization does not change it.
Existence of a potential replaces any undefined pseudoeffectivity assumption. -/
theorem thetaPshSupremum_isThetaPshPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2)
    (hlocal : HasSmoothLocalPotentials θ) (hne : ∃ u, IsThetaPshPotential θ u) :
    IsThetaPshPotential θ (thetaPshSupremum θ) := by
  exact FirstPass.thetaPshSupremum_isThetaPshPotential θ hlocal hne

/-- Canonical minimal singularities: every theta-PSH potential
is more singular than the actual pointwise supremum V_theta. -/
theorem thetaPshSupremum_minimalSingularities
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2)
    (u : M → EReal) (hu : IsThetaPshPotential θ u) :
    MoreSingularOn u (thetaPshSupremum θ) univ := by
  exact FirstPass.thetaPshSupremum_minimalSingularities
    θ u hu

/-- The singularity-type envelope of an actual theta-PSH
potential is again a theta-PSH potential. It need not have the same additive
singularity type as its reference potential. -/
theorem singularityEnvelope_isThetaPshPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal) (hφ : IsThetaPshPotential θ φ) :
    IsThetaPshPotential θ (singularityEnvelope θ φ) := by
  exact FirstPass.singularityEnvelope_isThetaPshPotential
    θ hlocal φ hφ

end SGPT.Foundations.Analysis.Pending
