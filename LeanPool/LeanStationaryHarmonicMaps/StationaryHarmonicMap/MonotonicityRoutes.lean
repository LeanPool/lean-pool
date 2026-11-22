/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
module

public import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusPrimitive
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.BallIntegralAC
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.BoundaryFromRadial
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.MonotonicityFinal
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusFormulas
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Packaged monotonicity routes

This module contains the main packaged weak monotonicity routes up to the
thin-shell and primitive-cutoff interfaces.

These declarations are internal scaffolding for the proof architecture.  User
code should normally import `MainTheorem.lean` or `API.lean` instead of relying
on a particular route theorem in this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Final weak-map interface through primitive cutoffs only.  This theorem does
not assume that all radial vector fields are `C¹`; each one-dimensional
test function is realized by a primitive cutoff that is proved flat near the
origin as part of the construction. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_primitive_cutoffs
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_stationarity_of_W12Loc_via_primitives
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset
      henergy_radius hradial_radius hdefect_loc hcalc hprimitive_realize
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr =>
      weakTheta_increment_eq_weakMonotonicityRhs_of_boundary
        (n := n) (m := m) (Du := Du) (R0 := R0) (s := s) (r := r)
        hboundary (weakEnergyAbsolutelyContinuousOnRadii_of_oneDimensionalCalculus hcalc)
        hradial_radius hs hsr hr)

/-- Same primitive-cutoff route with the interval-integral/smooth-bump
realization supplied by the formalized construction. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_constructed_primitive_cutoffs
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_primitive_cutoffs
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    henergy_radius hradial_radius hdefect_loc hcalc
    (weakPrimitiveCutoffRealization R0)

/-- Final weak-map interface using the exact radial-vector-field regularity
input needed for stationarity tests. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_vectorFieldContDiff
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hX : RadialVectorFieldContDiffForCutoffs n R0)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hrad : WeakRadialScalarCutoffStationarityIdentity Du R0 :=
    weak_radial_scalar_cutoff_identity_from_stationarity_of_W12Loc_vectorFieldContDiff
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset hX
  have hcalc : WeakBallEnergyOneDimensionalCalculus Du R0 :=
    weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hthin hmap.1 hclosedBall_subset henergy_radius hradial_radius
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredients
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad henergy_radius hradial_radius hdefect_loc
      hcalc.2.1 hcalc.2.2 (weakPrimitiveCutoffRealization R0)
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr =>
      weakTheta_increment_eq_weakMonotonicityRhs_of_boundary
        (n := n) (m := m) (Du := Du) (R0 := R0) (s := s) (r := r)
        hboundary (weakEnergyAbsolutelyContinuousOnRadii_of_oneDimensionalCalculus hcalc)
        hradial_radius hs hsr hr)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
