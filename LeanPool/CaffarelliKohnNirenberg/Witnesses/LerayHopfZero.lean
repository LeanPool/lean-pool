/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsGlobalLerayHopfSolution

/-!
# The zero datum has a global Leray–Hopf solution

The zero field with zero weak gradient satisfies the source-facing finite-time
and global Leray–Hopf predicates.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The zero datum belongs to the source space `J`. -/
theorem isInJ_zero : IsInJ (fun _ : Vec3 => 0) := by
  refine ⟨by simp, (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro k
    exact contDiff_const
  · intro k
    exact HasCompactSupport.intro isCompact_empty (by simp)
  · intro k x
    simp [CKN.spatialDeriv]
  · simp

/-- The zero fields satisfy the finite-time Leray–Hopf predicate. -/
theorem isLerayHopfSolution_zero (T : ℝ) (hT : 0 < T) :
    IsLerayHopfSolution T (fun _ : Vec3 => 0)
      (fun _ : ParabolicPoint => 0) (fun _ : ParabolicPoint => 0) := by
  refine ⟨hT, isInJ_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aestronglyMeasurable_const
  · exact aestronglyMeasurable_const
  · have hzero :
        essSup (fun _ : ℝ => (⊥ : ℝ≥0∞)) (volume.restrict (Ioo 0 T)) < ⊤ := by
      rw [essSup_const_bot]
      exact bot_lt_top
    simpa [CKN.Foundation.Parabolic.vec3EuclideanNorm, ENNReal.bot_eq_zero] using hzero
  · simp
  · filter_upwards [] with s
    intro i φ hφsmooth hφcompact hφsupport
    simp
  · filter_upwards [] with s
    intro ψ
    simp
  · intro w hw
    simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 T))
  · intro φ hφ hdiv
    simp
  · intro t₀ ht₀
    simp [CKN.spatialGradientSq]
  · simp [CKN.Foundation.Parabolic.vec3EuclideanNorm]

/-- The zero fields give a global Leray–Hopf solution for zero data. -/
theorem isGlobalLerayHopfSolution_zero :
    IsGlobalLerayHopfSolution (fun _ : Vec3 => 0)
      (fun _ : ParabolicPoint => 0) (fun _ : ParabolicPoint => 0) := by
  intro T hT
  exact isLerayHopfSolution_zero T hT

end CKN
