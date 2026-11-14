/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.JetAlgebra
public import LeanPool.PlanarMidpoint.GeodesicDefinitions
public import Mathlib.Tactic.Ring

/-! Exact transfers between opposite connection coefficients. -/

@[expose] public section
namespace PlanarMidpoint

/-- Negating the coefficient field and both derivatives preserves the Taylor-error norm. -/
theorem neg_coeff_taylor_remainder (C : E → Coeff) (p d : E) (c : Coeff)
    (J : E →L[ℝ] Coeff) (H : Hessian) :
    ‖(-C) (p + d) - (-c) - (-J) d - (1 / 2 : ℝ) • (-H) d d‖ =
      ‖C (p + d) - c - J d - (1 / 2 : ℝ) • H d d‖ := by
  simp only [Pi.neg_apply, neg_apply]
  rw [show - C (p + d) - (-c) - (-J d) - (1 / 2 : ℝ) • (-H d d) =
    -(C (p + d) - c - J d - (1 / 2 : ℝ) • H d d) by module]
  exact norm_neg _

theorem norm_neg_coeff_sub (C : E → Coeff) (p q : E) :
    ‖(-C) p - (-C) q‖ = ‖C p - C q‖ := by
  simp only [Pi.neg_apply, neg_sub_neg, norm_sub_rev]

/-- Negating the field exchanges the plus and minus geodesic equations. -/
theorem isGeodesicSegment_neg (C : E → Coeff) (γ v : ℝ → E) :
    IsGeodesicSegment C (-1) γ v ↔ IsGeodesicSegment (-C) 1 γ v := by
  have hk (c : Coeff) (u : E) : K (-c) u u = -K c u u := by
    apply vec_ext <;> simp [K] <;> ring
  simp only [IsGeodesicSegment, Pi.neg_apply, hk, neg_neg, one_smul,
    neg_one_smul]

/-- The shortness and endpoint requirements are unchanged by the sign transfer. -/
theorem isShortGeodesic_neg (C : E → Coeff) (p : E) (r : ℝ) (P Q : E) (γ v : ℝ → E) :
    IsShortGeodesic C (-1) p r P Q γ v ↔ IsShortGeodesic (-C) 1 p r P Q γ v := by
  simp only [IsShortGeodesic, isGeodesicSegment_neg]

end PlanarMidpoint
