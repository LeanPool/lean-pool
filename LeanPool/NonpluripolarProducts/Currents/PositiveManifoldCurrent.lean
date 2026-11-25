/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ChartDomains
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullback
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorProducts

/-!
# Positive currents on a complex manifold

A positive current is specified by positive coordinate expressions that agree under pullback
on overlaps. The compatibility condition uses biholomorphic transitions in the given atlas.
-/

@[expose] public section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### Coordinate changes -/

section Transition

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

theorem chartTransition_mem_contDiffGroupoid (e f : ComplexChart n M) :
    chartTransition e f ∈ contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n)) :=
  StructureGroupoid.compatible _ e.property f.property

/-- The coordinate change `f ∘ e⁻¹` is holomorphic on its overlap. -/
theorem contDiffOn_chartTransition (e f : ComplexChart n M) :
    ContDiffOn ℂ ∞ (chartTransition e f) (chartTransition e f).source :=
  contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_of_mem_contDiffGroupoid (chartTransition_mem_contDiffGroupoid e f))

/-- The inverse coordinate change is holomorphic on the overlap in `f`-coordinates. -/
theorem contDiffOn_chartTransition_symm (e f : ComplexChart n M) :
    ContDiffOn ℂ ∞ (chartTransition e f).symm (chartTransition e f).target := by
  have h := (contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n))).symm
    (chartTransition_mem_contDiffGroupoid e f)
  have h' := contMDiffOn_iff_contDiffOn.mp (contMDiffOn_of_mem_contDiffGroupoid h)
  simpa only [OpenPartialHomeomorph.symm_source] using h'

/-- **Atlas coordinate changes are biholomorphisms** between the two coordinate expressions of an
overlap (only the holomorphic atlas is used). -/
theorem chartTransition_isBiholomorphicPair (e f : ComplexChart n M) :
    IsBiholomorphicPair (overlapSource e f) (overlapTarget e f)
      (chartTransition e f) (chartTransition e f).symm where
  holo := contDiffOn_chartTransition e f
  holo_inv := contDiffOn_chartTransition_symm e f
  mapsTo := fun _ hx => (chartTransition e f).map_source hx
  mapsTo_inv := fun _ hy => (chartTransition e f).map_target hy
  left_inv := fun _ hx => (chartTransition e f).left_inv hx
  right_inv := fun _ hy => (chartTransition e f).right_inv hy

end Transition

/-! ### Positive currents on the manifold -/

section Currents

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

variable (n M) in
/-- **A positive current of bidimension `(q,q)` on `M`** (bidegree `(n-q, n-q)`), given by its
expressions in all atlas charts: positive currents on the coordinate domains which agree on every
overlap, the expression in `e` being the pull-back of the expression in `f` along the coordinate
change `f ∘ e⁻¹`. -/
structure PositiveCurrent (q : ℕ) where
  /-- The coordinate expression in the chart `e`. -/
  inChart : (e : ComplexChart n M) → LocalProductCurrent n (chartTarget e) q
  /-- Every coordinate expression is a positive current. -/
  isPositive : ∀ e, IsPositive (inChart e)
  /-- Compatibility on overlaps. -/
  compatible : ∀ e f : ComplexChart n M,
    restrict (overlapSource_le e f) (inChart e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (isPositive f) (overlapTarget_le e f))

namespace PositiveCurrent

variable {q : ℕ}

@[ext] theorem ext {S T : PositiveCurrent n M q} (h : ∀ e, S.inChart e = T.inChart e) :
    S = T := by
  cases S
  cases T
  congr
  funext e
  exact h e

/-- A current on `M` is closed when all its coordinate expressions are closed. -/
def IsClosed (T : PositiveCurrent n M q) : Prop :=
  ∀ e, IsClosedAny q (T.inChart e)

end PositiveCurrent

end Currents

end SGPT.NPP
