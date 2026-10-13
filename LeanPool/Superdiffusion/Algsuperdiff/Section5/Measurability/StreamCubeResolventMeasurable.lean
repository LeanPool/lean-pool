/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.ContinuousRepresentativeMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.ShiftedCoefficientContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.StreamCoefficientMeasurable

@[expose] public section

/-!
# Measurability of stream cube resolvents

The stream coefficient on a compact cube is a measurable continuous-map-valued
random variable.  Continuous dependence of the shifted weak solution gives
measurability of its local integrals, and continuity of the analytic
representative then gives pointwise measurability.
-/

namespace Algsuperdiff.Section5.Measurability

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form
open HCPolySupport MeasureTheory
open MarkovProcess.Semigroup

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem wholeSpaceCube_subset_outerCube (m : ℕ) :
    wholeSpaceCube d m ⊆ cubeSetAt (0 : Vec d) (m + 1 : ℤ) := by
  intro x hx
  rw [mem_wholeSpaceCube_iff] at hx
  rw [mem_cubeSetAt_iff_forall_coord]
  intro i
  have hp : (3 : ℝ) ^ (m + 1 : ℤ) = 3 * (3 : ℝ) ^ m := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    ring
  rw [Pi.zero_apply, sub_zero, hp]
  have hmpos : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
  constructor <;> linarith only [(hx i).1, (hx i).2, hmpos]

omit [NeZero d] in
private theorem streamCoefficientRestrict_mem_ellipticCube
    (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℕ) :
    streamCoefficientRestrict M.nu (closedCubeAt (0 : Vec d) (m + 1 : ℤ)) omega ∈
      ellipticCube M.nu (0 : Vec d) (m + 1 : ℤ) := by
  intro z
  simpa only [streamCoefficientRestrict_apply] using
    symmPart_streamCoefficient M.nu omega (z : Vec d)

theorem measurable_analyticCubeResolvent_stream
    (M : ABKModel d) (mu : PositiveShift) (f : Vec d → ℝ)
    (hf : Measurable f) (D : ℝ) (hfD : ∀ x, |f x| ≤ D)
    (m : ℕ) (x : Vec d) :
    Measurable fun omega : FullSample d M.gamma =>
      (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
        mu f hf hfD m x := by
  let U : Set (Vec d) := wholeSpaceCube d m
  let n : ℤ := (m + 1 : ℕ)
  let hUdom := isOpenBoundedConvexDomain_wholeSpaceCube d m
  have hUmeas : MeasurableSet U := hUdom.isOpen.measurableSet
  have hUfin : volume U ≠ ⊤ := hUdom.volume_lt_top.ne
  have hUsub : U ⊆ cubeSetAt (0 : Vec d) n := wholeSpaceCube_subset_outerCube m
  let fU : ScalarL2 U := boundedMeasurableToScalarL2 hUdom
    (hf.comp measurable_subtype_coe) (fun y => hfD y)
  let coeff : FullSample d M.gamma → ellipticCube M.nu (0 : Vec d) n := fun omega =>
    ⟨streamCoefficientRestrict M.nu (closedCubeAt (0 : Vec d) n) omega,
      streamCoefficientRestrict_mem_ellipticCube M omega m⟩
  have hcoeff : Measurable coeff := Measurable.subtype_mk
    (measurable_streamCoefficientRestrict M.nu (closedCubeAt (0 : Vec d) n))
  by_cases hx : x ∈ U
  · apply measurable_eval_of_continuousOn_of_setIntegral hUdom.isOpen
      (fun omega => (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
        mu f hf hfD m) _ _ hx
    · intro omega
      exact (streamWholeSpaceAnalyticData M omega).continuousOn_analyticCubeResolvent
        mu hf hfD m
    · intro B hBU
      have hmeas :=
        (ShiftedCoefficientContinuity.continuous_shiftedFieldSetIntegral
          M.nu_pos mu.property hUmeas hUfin hUsub fU hBU).measurable.comp hcoeff
      have heq : (fun omega : FullSample d M.gamma =>
          ∫ y in B, (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
            mu f hf hfD m y ∂volume) =
          fun omega => ShiftedCoefficientContinuity.shiftedFieldSetIntegral
            M.nu_pos mu.property hUmeas hUsub fU B (coeff omega) := by
        funext omega
        have hcoeffEq : ∀ y ∈ U,
            streamCoefficient M.nu omega y =
              extendCoeff (0 : Vec d) n (coeff omega).1 y := by
          intro y hy
          have hyK : y ∈ closedCubeAt (0 : Vec d) n :=
            cubeSetAt_subset_closedCubeAt (0 : Vec d) n (hUsub hy)
          rw [extendCoeff_apply_of_mem _ hyK]
          rfl
        have hL2 :
            alphaShiftedResolvent (streamCoefficient M.nu omega) mu.property M.nu_pos
                ((streamWholeSpaceAnalyticData M omega).cubeEllipticity m) fU =
              ShiftedCoefficientContinuity.shiftedFieldResolvent M.nu_pos mu.property
                hUmeas hUsub fU (coeff omega) := by
          exact
            ShiftedCoefficientContinuity.alphaShiftedResolvent_eq_shiftedFieldResolvent_of_eqOn
              M.nu_pos mu.property hUmeas hUsub (coeff omega)
              ((streamWholeSpaceAnalyticData M omega).cubeEllipticity m)
              hcoeffEq fU
        have hae := (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent_ae
          mu hf hfD m
        change (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
            mu f hf hfD m =ᵐ[volumeMeasureOn U]
          alphaShiftedResolvent (streamCoefficient M.nu omega) mu.property M.nu_pos
            ((streamWholeSpaceAnalyticData M omega).cubeEllipticity m) fU at hae
        rw [hL2] at hae
        unfold ShiftedCoefficientContinuity.shiftedFieldSetIntegral
        exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hBU hae)
      rw [heq]
      exact hmeas
  · have hz : (fun omega : FullSample d M.gamma =>
        (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
          mu f hf hfD m x) = fun _ => 0 := by
      funext omega
      exact (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent_of_notMem
        mu hf hfD m hx
    rw [hz]
    exact measurable_const

end

end Algsuperdiff.Section5.Measurability
