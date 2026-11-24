/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ERealChordUSC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.Envelopes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FiniteTranslation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocallyUniformUpperBounds

/-!
# Compact upper bounds and normalized theta-PSH competitors

An extended-real upper-semicontinuous function which avoids `⊤` has a finite
real upper bound on a nonempty compact space.  Applying this to a theta-PSH
potential and subtracting the bound produces an actual normalized competitor.
The same translate is a singularity competitor for the original potential.

These statements retain values equal to `⊥`: normalization uses only finite
translation in `EReal`, and no `toReal` operation is applied pointwise.
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

/-- Subtracting a finite real constant preserves the theta-PSH potential
predicate, including local nondegeneracy at poles. -/
theorem IsThetaPshPotential.sub_const {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential θ u) (C : ℝ) :
    IsThetaPshPotential θ (fun x => u x - (C : EReal)) := by
  simpa only [sub_eq_add_neg, EReal.coe_neg] using hu.add_const (-C)

omit [TopologicalSpace M] in
/-- Subtracting an upper bound makes the translated function nonpositive. -/
theorem sub_const_nonpositive_of_le {u : M → EReal} {C : ℝ}
    (hC : ∀ x, u x ≤ (C : EReal)) :
    (fun x => u x - (C : EReal)) ≤ 0 := by
  intro x
  exact (EReal.sub_le_sub (hC x) le_rfl).trans EReal.sub_self_le_zero

/-- A compact theta-PSH potential has a finite translate which is an actual
normalized theta-PSH competitor. -/
theorem IsThetaPshPotential.exists_normalized_sub_const
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) :
    ∃ C : ℝ, (fun x => u x - (C : EReal)) ∈ thetaPshCompetitors θ := by
  obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
  exact ⟨C, hu.sub_const C, sub_const_nonpositive_of_le hC⟩

/-- Nonemptiness of the unnormalized potential class implies nonemptiness of
the normalized competitor class on a compact manifold. -/
theorem thetaPshCompetitors_nonempty
    [CompactSpace M] [Nonempty M] (θ : SmoothRealForm n M 2)
    (hne : ∃ u, IsThetaPshPotential θ u) :
    (thetaPshCompetitors θ).Nonempty := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨C, hC⟩ := hu.exists_normalized_sub_const
  exact ⟨fun x => u x - (C : EReal), hC⟩

/-- The normalized translate is also a singularity competitor for the
original potential, since finite translation preserves singularity type. -/
theorem IsThetaPshPotential.exists_normalized_singularityCompetitor
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) :
    ∃ C : ℝ, (fun x => u x - (C : EReal)) ∈ singularityCompetitors θ u := by
  obtain ⟨C, hnormalized⟩ := hu.exists_normalized_sub_const
  refine ⟨C, hnormalized, ?_⟩
  simpa only [sub_eq_add_neg, EReal.coe_neg] using
    (sameSingularityTypeOn_add_const u univ (-C)).1

/-- Every actual theta-PSH reference potential has a nonempty singularity
competitor class on a compact manifold. -/
theorem singularityCompetitors_nonempty
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) :
    (singularityCompetitors θ u).Nonempty := by
  obtain ⟨C, hC⟩ := hu.exists_normalized_singularityCompetitor
  exact ⟨fun x => u x - (C : EReal), hC⟩

/-- A family whose members are all nonpositive is locally uniformly bounded
above on every domain, with the common bound zero. -/
theorem locallyUniformlyBoundedAbove_of_nonpositive
    {F : Set (X → EReal)} {Ω : Set X}
    (hF : ∀ f ∈ F, f ≤ 0) : LocallyUniformlyBoundedAbove F Ω := by
  intro x hx
  exact ⟨univ, Filter.univ_mem, 0, fun f hf y _hy => hF f hf y⟩

/-- The normalized theta-PSH family has the common local upper bound zero. -/
theorem thetaPshCompetitors_locallyUniformlyBoundedAbove
    (θ : SmoothRealForm n M 2) (Ω : Set M) :
    LocallyUniformlyBoundedAbove (thetaPshCompetitors θ) Ω :=
  locallyUniformlyBoundedAbove_of_nonpositive fun _ hu => hu.2

/-- Every singularity-competitor family inherits the common local upper bound
zero from the normalized theta-PSH family. -/
theorem singularityCompetitors_locallyUniformlyBoundedAbove
    (θ : SmoothRealForm n M 2) (u : M → EReal) (Ω : Set M) :
    LocallyUniformlyBoundedAbove (singularityCompetitors θ u) Ω :=
  locallyUniformlyBoundedAbove_of_nonpositive fun _ hv => hv.1.2

end

end SGPT.Foundations.Analysis.FirstPass
