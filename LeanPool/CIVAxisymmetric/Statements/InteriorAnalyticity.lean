/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.InteriorAnalyticity
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Statements.LocallyUniformlyAnalyticOn

/-!
# Interior Analyticity

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Theorem 2.1 (`thm:analytic:interior`, Kahane 1969): interior spatial analyticity. -/
theorem interiorAnalyticity (R t₁ t₂ : ℝ) (hR : 0 < R) (ht : t₁ < t₂)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo t₁ t₂)))
    (hf : LocallyUniformlyAnalyticOn f R t₁ t₂) :
    LocallyUniformlyAnalyticOn u R t₁ t₂ := by
  exact CIV.Main.interiorAnalyticity R t₁ t₂ hR ht u p f hsol hf

end CIV
