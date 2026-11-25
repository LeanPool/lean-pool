/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials

/-!
# Compact upper bounds for theta-plurisubharmonic functions

An extended-real upper-semicontinuous function with values below `⊤` has a
finite real upper bound on a nonempty compact space. This applies to the
upper-semicontinuous representatives of theta-plurisubharmonic functions.
-/

@[expose] public section

open Set
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A `⊤`-free upper-semicontinuous extended-real function on a nonempty
compact space admits one global finite real upper bound. -/
theorem exists_real_upper_bound_of_upperSemicontinuous
    [CompactSpace X] [Nonempty X] {u : X → EReal}
    (hu : UpperSemicontinuous u) (htop : ∀ x, u x ≠ ⊤) :
    ∃ C : ℝ, ∀ x, u x ≤ (C : EReal) := by
  obtain ⟨y, _hy, hmax⟩ :=
    (hu.upperSemicontinuousOn univ).exists_isMaxOn univ_nonempty isCompact_univ
  obtain ⟨C, hC, _⟩ := EReal.exists_rat_btwn_of_lt
    (lt_top_iff_ne_top.mpr (htop y))
  exact ⟨C, fun x => (hmax (mem_univ x)).trans hC.le⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every raw theta-PSH function has a global finite real upper bound on a
nonempty compact complex manifold. -/
theorem ThetaPlurisubharmonic.exists_global_upper_bound
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) :
    ∃ C : ℝ, ∀ x, u x ≤ (C : EReal) :=
  exists_real_upper_bound_of_upperSemicontinuous
    hu.quasiPlurisubharmonic.upperSemicontinuous
    hu.quasiPlurisubharmonic.ne_top

/-- Potential-level wrapper for the compact global upper bound. -/
theorem IsThetaPshPotential.exists_global_upper_bound
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) :
    ∃ C : ℝ, ∀ x, u x ≤ (C : EReal) :=
  hu.1.exists_global_upper_bound

end

end SGPT.Foundations.Analysis.FirstPass
