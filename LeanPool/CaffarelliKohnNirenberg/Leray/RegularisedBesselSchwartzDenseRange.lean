/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzCore

/-!
# Density of Schwartz representatives

The range inclusion of Schwartz lifts upgrades density from weighted
L² coordinates to genuine Schwartz fields.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Schwartz distributions are dense in every complete Bessel Hˢ space. -/
theorem regularisedBesselOfSchwartz_denseRange (s : ℝ) :
    DenseRange (regularisedBesselOfSchwartz s) := by
  intro v
  exact closure_mono (regularisedBesselSchwartzLift_range_subset s)
    ((regularisedBesselSchwartzLift_denseRange s) v)

end CKN.Leray

end
