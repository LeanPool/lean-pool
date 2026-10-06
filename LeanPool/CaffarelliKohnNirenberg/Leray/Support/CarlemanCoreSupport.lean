/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreProduct
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Support of conjugated test functions

The exponential change of variables in `prop:carleman-gauss` of the
Escauriaza–Seregin–Šverák manuscript
preserves smooth compact support when the phase is smooth near that support.
-/

public section

open CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

local instance carlemanCoreSupportNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreSupportNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- Multiplication by a scalar exponential does not enlarge topological support. -/
theorem tsupport_exp_mul_subset (φ w : ParabolicPoint → ℝ) :
    tsupport (fun z => Real.exp (φ z) * w z) ⊆ tsupport w := by
  exact tsupport_mul_subset_right

/-- Exponential conjugation preserves compact support. -/
theorem hasCompactSupport_exp_mul (φ w : ParabolicPoint → ℝ)
    (hw : HasCompactSupport w) :
    HasCompactSupport (fun z => Real.exp (φ z) * w z) := by
  exact hw.mul_left

/-- Exponential conjugation is globally smooth when the phase is smooth on an
open neighborhood of the support; this is used by `eq:carleman-commutator` of
the Escauriaza–Seregin–Šverák manuscript. -/
theorem contDiff_exp_mul_of_tsupport
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwU : tsupport w ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => Real.exp (φ z) * w z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact ((hφ.contDiffAt (hU.mem_nhds hz)).exp.mul hw.contDiffAt)
  · have hzs : z ∉ tsupport w := fun h => hz (hwU h)
    have hnhds : (tsupport w)ᶜ ∈ 𝓝 z :=
      (isClosed_tsupport w).isOpen_compl.mem_nhds hzs
    have heq : (fun y => Real.exp (φ y) * w y) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hnhds] with y hy
      have hwy : w y = 0 := by
        by_contra hne
        exact hy (subset_tsupport w hne)
      simp only [hwy, mul_zero]
    exact (contDiffAt_const (𝕜 := ℝ) (c := (0 : ℝ))).congr_of_eventuallyEq heq

end CKN
