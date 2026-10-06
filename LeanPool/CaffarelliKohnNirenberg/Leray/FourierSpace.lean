/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier spaces for the regularized Leray construction

The spatial Fourier transform is taken on CKN's Euclidean L2Vec3 carrier.
The coordinate presentation Vec3 is related to this Hilbert space by a
volume-preserving equivalence.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Complex-valued velocity fields with the Euclidean norm on their three components. -/
abbrev ComplexVec3 := PiLp 2 (fun _ : Fin 3 => ℂ)

/-- Complex-valued tensor fields with the Frobenius norm on their components. -/
abbrev ComplexTensor3 := PiLp 2 (fun _ : Fin 3 => ComplexVec3)

/-- The coordinate-to-Hilbert-space identification preserves spatial volume. -/
theorem vec3ToL2Vec3_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
  PiLp.volume_preserving_toLp (Fin 3)

end CKN.Leray
