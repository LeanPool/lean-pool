/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.ApproximationRemainder
public import LeanPool.PlanarMidpoint.LocalBounds
public import LeanPool.PlanarMidpoint.Negation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Complementary geodesic midpoints force the fourth-order obstruction

The proof compares actual short geodesics with explicit polynomial trajectories.
It needs no differentiability of a family of solutions with respect to endpoints.
-/

@[expose] public section

noncomputable section
namespace PlanarMidpoint
open Set Metric

/-- Complementarity for arbitrarily short actual geodesics annihilates the
first-order quartic obstruction. -/
theorem obstruction_of_short_complementary_pairs {Ω : Set E} {C : E → Coeff} {p : E}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hC : ContDiffOn ℝ 2 C Ω)
    (hpairs : ArbitrarilyShortComplementaryPairs C p) (h : E) :
    obstruction (C p) (fderiv ℝ C p) h = 0 := by
  let c := C p
  let J := fderiv ℝ C p
  let H : Hessian := fderiv ℝ (fderiv ℝ C) p
  let e := obstruction c J h
  change e = 0
  by_contra he
  have hne : 0 < ‖e‖ := norm_pos_iff.mpr he
  let κ := ‖e‖ / 1000
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨r, hr, M, hM, L, hL, _hsub, hbound, hLip, hsmall⟩ := local_coefficient_bounds hΩ hp hC
  have hTaylor : ∀ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ d : E, ‖d‖ < ρ →
      ‖C (p + d) - c - J d - (1 / 2 : ℝ) • H d d‖ ≤ η * ‖d‖ ^ 2 := by
    intro η hη
    obtain ⟨ρ, hρ, _hsub, herr⟩ := exists_second_order_spatial_remainder hΩ hp hC hη
    exact ⟨ρ, hρ, herr⟩
  have hTaylorMinus : ∀ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ d : E, ‖d‖ < ρ →
      ‖(-C) (p + d) - (-c) - (-J) d - (1 / 2 : ℝ) • (-H) d d‖ ≤ η * ‖d‖ ^ 2 := by
    intro η hη
    obtain ⟨ρ, hρ, herr⟩ := hTaylor η hη
    refine ⟨ρ, hρ, ?_⟩
    intro d hd
    rw [neg_coeff_taylor_remainder]
    exact herr d hd
  obtain ⟨δPlus, hδPlus, hPlus⟩ := exists_short_geodesic_approximation
    C p c J H h r M L hr hM hL hbound hLip hsmall hTaylor κ hκ
  obtain ⟨δMinus, hδMinus, hMinus⟩ := exists_short_geodesic_approximation
    (-C) p (-c) (-J) (-H) h r M L hr hM hL
    (fun x hx ↦ by simpa only [Pi.neg_apply, norm_neg] using hbound x hx)
    (fun x hx y hy ↦ by simpa only [norm_neg_coeff_sub] using hLip x hx y hy)
    hsmall hTaylorMinus κ hκ
  obtain ⟨δPair, hδPair, hPair⟩ := hpairs r hr
  obtain ⟨ε, hε, hεδ⟩ := exists_between
    (show 0 < min δPlus (min δMinus (δPair / (‖h‖ + 1))) by positivity)
  have hεPlus : ε < δPlus := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεMinus : ε < δMinus := lt_of_lt_of_le hεδ
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεEnd : ε < δPair / (‖h‖ + 1) := lt_of_lt_of_le hεδ
    ((min_le_right _ _).trans (min_le_right _ _))
  have hscalar : (ε / 2) * ‖h‖ < δPair := by
    have hh := (lt_div_iff₀ (show 0 < ‖h‖ + 1 by positivity)).mp hεEnd
    nlinarith [norm_nonneg h]
  have hP : p - (ε / 2) • h ∈ ball p δPair := by
    rw [mem_ball, dist_eq_norm]
    have hh : p - (ε / 2) • h - p = -((ε / 2) • h) := by module
    rw [hh, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hscalar
  have hQ : p + (ε / 2) • h ∈ ball p δPair := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hscalar
  obtain ⟨γPlus, vPlus, γMinus, vMinus, hγPlus, hγMinus, hcomp⟩ := hPair _ _ hP hQ
  have herrPlus := hPlus ε hε.le hεPlus γPlus vPlus hγPlus
  have herrMinus := hMinus ε hε.le hεMinus γMinus vMinus
    ((isShortGeodesic_neg C p r _ _ γMinus vMinus).mp hγMinus)
  let dPlus := approxDisplacement c J H h ε (1 / 2)
  let dMinus := approxDisplacement (-c) (-J) (-H) h ε (1 / 2)
  have hdefect : ‖dPlus + dMinus‖ ≤ 2 * κ * ε ^ 4 := by
    calc
      ‖dPlus + dMinus‖ = ‖(p + dPlus - γPlus (1 / 2)) + (p + dMinus - γMinus (1 / 2))‖ := by
        congr 1
        have hsum : p + p = γPlus (1 / 2) + γMinus (1 / 2) := by
          calc
            p + p = (p - (ε / 2) • h) + (p + (ε / 2) • h) := by module
            _ = _ := hcomp.symm
        calc
          dPlus + dMinus = (p + dPlus) + (p + dMinus) - (p + p) := by module
          _ = _ := by rw [hsum]; module
      _ ≤ ‖p + dPlus - γPlus (1 / 2)‖ + ‖p + dMinus - γMinus (1 / 2)‖ := norm_add_le _ _
      _ ≤ κ * ε ^ 4 + κ * ε ^ 4 := add_le_add
        (by simpa only [norm_sub_rev] using herrPlus)
        (by simpa only [norm_sub_rev] using herrMinus)
      _ = _ := by ring
  have hpoly : dPlus + dMinus = (ε ^ 4 / 192) • e :=
    approxDisplacement_add_opposite_midpoint c J H h ε
  rw [hpoly, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hdefect
  have hε4 : 0 < ε ^ 4 := pow_pos hε 4
  have hnorm : ‖e‖ / 192 ≤ 2 * κ := by
    apply le_of_mul_le_mul_right (a := ε ^ 4) _ hε4
    nlinarith
  dsimp [κ] at hnorm
  linarith

end PlanarMidpoint
