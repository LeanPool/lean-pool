/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Blowups with smooth centers, modifications and strict transforms

Source: Copy-4, `sec:prelim` (modifications), the paragraph before
`lem:relative-principalization` (sequences of blowups adapted to a
submanifold), `lem:exceptional-metric` and `lem:resolution`
(`transcendental-nakamaye-copy4-20260911`).

New definitions of this first pass (recorded in the blueprint,
`ana:geometric-setting`):

* `IsClosedSubmanifold C`: `C` is closed and locally biholomorphically a
  coordinate plane at each of its points (a smooth center; components may have
  different dimensions).  `IsClosedConnectedSubmanifold W k` fixes the dimension
  and adds connectedness.
* `exceptionalLocus f`: the points where the holomorphic differential of
  `f : Y → X` (equal dimensions) is not bijective.  For a proper bimeromorphic map
  of complex manifolds this is the smallest set off which `f` is biholomorphic
  onto its image (Zariski's main theorem makes the fibre through a point of
  invertible differential a single point).
* `strictTransform f A = closure (f⁻¹ A \ Exc f)`.
* `IsIsomorphismOver f S`: `f` maps `f⁻¹ S` bijectively onto `S` and is a local
  biholomorphism at each point of `f⁻¹ S`.
* `IsBlowupAlong C π`: `π` is the blowup of `X` along the nowhere dense closed
  submanifold `C`, defined by its universal property: `π` is holomorphic, `𝓘_C 𝒪_Y` is invertible,
  and every holomorphic `g : Z → X` from a complex manifold with `𝓘_C 𝒪_Z`
  invertible factors uniquely and holomorphically through `π`.  Test manifolds
  range over all dimensions in the universe of `Y`; since the blowup of a
  manifold along a smooth center is a manifold, this characterizes it up to
  unique isomorphism.  The center is required to be nowhere dense: the universal
  property alone would also accept the blowup along a whole connected component,
  which deletes that component (a map into it pulls `𝓘_C` back to the zero
  ideal, which is never invertible), and such a map is not a modification.
* `IsBlowupSequence n X Y f`: `f` is a finite composition of blowups with smooth
  centers (a modification in the manuscript's sense).
* `IsAdaptedBlowupSequence n X W Y f`: every center is contained in a proper
  analytic subset of the current strict transform of `W`, or is disjoint from it.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.FirstPass.BlowupSequences

noncomputable section

open HolomorphicIdealSheaves

section Basic

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

variable (n) in
/-- A closed complex submanifold: closed, and regular of some dimension at each
of its points. -/
def IsClosedSubmanifold (C : Set X) : Prop :=
  IsClosed C ∧ ∀ x ∈ C, ∃ k : ℕ, RegularAtDim (n := n) C x k

variable (n) in
/-- A closed connected complex submanifold of dimension `k`. -/
def IsClosedConnectedSubmanifold (W : Set X) (k : ℕ) : Prop :=
  IsClosed W ∧ IsConnected W ∧ ∀ x ∈ W, RegularAtDim (n := n) W x k

variable (n) in
/-- The exceptional locus: points where the holomorphic differential is not
bijective. -/
def exceptionalLocus (f : Y → X) : Set Y :=
  {y | ¬ Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f y)}

variable (n) in
/-- The strict transform `closure (f⁻¹ A \ Exc f)`. -/
def strictTransform (f : Y → X) (A : Set X) : Set Y :=
  closure (f ⁻¹' A \ exceptionalLocus n f)

variable (n) in
/-- `f` is an isomorphism over `S`. -/
def IsIsomorphismOver (f : Y → X) (S : Set X) : Prop :=
  BijOn f (f ⁻¹' S) S ∧ Disjoint (f ⁻¹' S) (exceptionalLocus n f)

variable (n) in
/-- The blowup of `X` along the nowhere dense closed submanifold `C`, by its universal
property. -/
def IsBlowupAlong (C : Set X) (π : Y → X) : Prop :=
  IsClosedSubmanifold n C ∧ interior C = ∅ ∧
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π ∧
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsInvertible ∧
    ∀ (m : ℕ) (Z : Type u) [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
      [IsComplexManifold m Z] (g : Z → X),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g →
      (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).IsInvertible →
        ∃! h : Z → Y, ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h ∧ π ∘ h = g

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
theorem IsBlowupAlong.contMDiff {C : Set X} {π : Y → X} (h : IsBlowupAlong n C π) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π :=
  h.2.2.1

end Basic

/-- A finite composition of blowups with smooth centers, starting from `X`. -/
inductive IsBlowupSequence (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] :
    (Y : Type u) → [TopologicalSpace Y] → [ChartedSpace (ComplexModel n) Y] →
      [IsComplexManifold n Y] → (Y → X) → Prop
  | refl : IsBlowupSequence n X X id
  | step {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
      [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
      [IsComplexManifold n Z] (f : Y → X) (C : Set Y) (g : Z → Y) :
      IsBlowupSequence n X Y f → IsBlowupAlong n C g → IsBlowupSequence n X Z (f ∘ g)

/-- A finite composition of blowups with smooth centers adapted to `W`: each
center lies in a proper analytic subset of the current strict transform of `W`,
or is disjoint from it. -/
inductive IsAdaptedBlowupSequence (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (W : Set X) :
    (Y : Type u) → [TopologicalSpace Y] → [ChartedSpace (ComplexModel n) Y] →
      [IsComplexManifold n Y] → (Y → X) → Prop
  | refl : IsAdaptedBlowupSequence n X W X id
  | step {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
      [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
      [IsComplexManifold n Z] (f : Y → X) (C : Set Y) (g : Z → Y) :
      IsAdaptedBlowupSequence n X W Y f → IsBlowupAlong n C g →
      ((∃ A : Set Y, IsComplexAnalyticSubset (n := n) A ∧
          A ⊆ strictTransform n f W ∧ A ≠ strictTransform n f W ∧ C ⊆ A) ∨
        Disjoint C (strictTransform n f W)) →
      IsAdaptedBlowupSequence n X W Z (f ∘ g)

section Lemmas

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- A blowup sequence is holomorphic. -/
theorem IsBlowupSequence.contMDiff {f : Y → X} (h : IsBlowupSequence n X Y f) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl => exact contMDiff_id
  | step f C g _ hg ih => exact ih.comp hg.contMDiff

/-- An adapted blowup sequence is a blowup sequence. -/
theorem IsAdaptedBlowupSequence.isBlowupSequence {W : Set X} {f : Y → X}
    (h : IsAdaptedBlowupSequence n X W Y f) : IsBlowupSequence n X Y f := by
  induction h with
  | refl => exact IsBlowupSequence.refl
  | step f C g _ hg _ ih => exact IsBlowupSequence.step f C g ih hg

/-- An adapted blowup sequence is holomorphic. -/
theorem IsAdaptedBlowupSequence.contMDiff {W : Set X} {f : Y → X}
    (h : IsAdaptedBlowupSequence n X W Y f) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f :=
  h.isBlowupSequence.contMDiff

end Lemmas

end

end SGPT.Foundations.Analysis.FirstPass.BlowupSequences
