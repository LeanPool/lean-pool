/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Witnesses.LerayHopfZero
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsGlobalForcedLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallySquareIntegrableForce
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallyQIntegrableForce

/-!
# Zero data and zero force satisfy the forced predicates

The zero force is square integrable on every slab and locally `L^q` for every
exponent, and the zero fields form a forced Leray–Hopf solution with zero
datum and zero force.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The zero force is square integrable on every finite positive-time slab. -/
theorem isLocallySquareIntegrableForce_zero :
    IsLocallySquareIntegrableForce (fun _ : ParabolicPoint => (0 : Vec3)) := by
  intro T hT
  exact MemLp.zero

/-- The zero force is locally `L^q` on every CKN local box, for every `q`. -/
theorem isLocallyQIntegrableForce_zero (q : ℝ) :
    IsLocallyQIntegrableForce q (fun _ : ParabolicPoint => (0 : Vec3)) := by
  intro Ω' J hbox i
  exact MemLp.zero

/-- The zero fields form a finite-time forced Leray–Hopf solution with zero
datum and zero force. -/
theorem isForcedLerayHopfSolution_zero (T : ℝ) (hT : 0 < T) :
    IsForcedLerayHopfSolution T (fun _ : Vec3 => 0) (fun _ : ParabolicPoint => 0)
      (fun _ : ParabolicPoint => 0) (fun _ : ParabolicPoint => 0) := by
  refine ⟨hT, isInJ_zero, MemLp.zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    simp [CKN.spatialGradientSq, CKN.Foundation.Parabolic.vec3EuclideanNorm]
  · simp [CKN.Foundation.Parabolic.vec3EuclideanNorm]

/-- The zero fields form a global forced Leray–Hopf solution. -/
theorem isGlobalForcedLerayHopfSolution_zero :
    IsGlobalForcedLerayHopfSolution (fun _ : Vec3 => 0) (fun _ : ParabolicPoint => 0)
      (fun _ : ParabolicPoint => 0) (fun _ : ParabolicPoint => 0) := by
  intro T hT
  exact isForcedLerayHopfSolution_zero T hT

end CKN
