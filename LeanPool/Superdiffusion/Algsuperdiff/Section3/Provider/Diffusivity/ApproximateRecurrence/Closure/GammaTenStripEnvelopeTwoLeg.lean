/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripEnvelopeConst

/-!
# GammaTenStripEnvelopeTwoLeg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# One Besov envelope for the **two scaled legs** of Step 2

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`, `e.Fz.def`.

## What this module does

`Closure.GammaTenCloserAssembly.ClosureBesovEnvelopeInput` --- and its interior
restatement `Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput` ---
asks for **one** sample family `Bg` dominating the Besov towers of **both** legs
of the gauged `bfF_z`, with `gridFourthMomentRoot Bg <= cgamma^{15}`.  By
`Closure.GammaTenEnvelopeInputGauge.cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential`
and `..._flux` those two towers are `|c_1|` and `|c_2|` times the towers of two
**raw** fields, the Dirichlet corrector gradient and the Neumann flux field, with

```
  c_1 = sqrt(sigma_0) . sqrt(shom_n)^{-1} ,   c_2 = sqrt(sigma_0)^{-1} . sqrt(shom_n) ,
```

both bounded by the gauge cap of `e.shom.h.bounds`.  This module produces that
single envelope from the two raw per-depth inputs, and closes the arithmetic:
each leg is enveloped at the budget `cgamma^{15} / (4 C_g)` by
`Closure.GammaTenStripEnvelopeConst.exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const`,
the two envelopes are added, and the elementary constant `8^{1/4} <= 2` of
`LocalizationOscillationGridMoment.gridFourthMomentRoot_le_add_of_le` still
leaves the sum below `cgamma^{15}`:

```
  8^{1/4} ( |c_1| + |c_2| ) cgamma^{15} / (4 C_g)  <=  2 . 2 C_g . cgamma^{15} / (4 C_g)
                                                   =  cgamma^{15} .
```

The single numerical premise `hthr : 200 (4 A C_g)^4 cgamma^4 <= 1` is what the
constants cost: `A` is the per-depth constant of the two raw inputs (`1` for the
Dirichlet leg, `2 d` for the flux leg after
`Closure.GammaTenDepthFluxOscillation`), `C_g` the gauge cap.  Both are
dimension-only, so `hthr` is a threshold on `cgamma` alone.

## What is proved

* `exists_besovEnvelope_two_legs_interiorMesoCubeGrid` --- the two-leg envelope,
  dominating `|c_1|` times the tower of the first field and `|c_2|` times the
  tower of the second, with grid fourth-moment root below `cgamma^{15}`.

## Binders

Those of the one-leg composite --- the scale bookkeeping, the boundary gate and
the three cellwise typing binders, now for each of the two fields --- together
with `1 <= A`, `1 <= C_g`, the scalar bounds `|c_1|, |c_2| <= C_g`, the two
per-depth inputs at the common constant `A`, and the single numerical threshold
`hthr`.  Nothing about the corrector, the coefficient field or the sample space
occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.Fz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-! ## The fourth power of an `L^4` family is integrable -/

/-- For a nonnegative family in `L^4`, the fourth power is integrable, in the
`rpow` spelling the grid functional uses.  Unconditional. -/
theorem integrable_rpow_four_of_memLp_four {mu : Measure Omega} {f : Omega → ℝ}
    (hf : MemLp f 4 mu) (hf0 : ∀ w, 0 ≤ f w) :
    Integrable (fun w => f w ^ (4 : ℝ)) mu := by
  have hbase := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have hfun : (fun w => ‖f w‖ ^ ((4 : ℝ≥0∞).toReal)) = fun w => f w ^ (4 : ℝ) := by
    funext w
    rw [Real.norm_of_nonneg (hf0 w)]
    norm_num
  rwa [hfun] at hbase

/-! ## The two-leg envelope -/

/-- **One envelope for the two scaled legs.**

From two per-depth grid fourth-moment roots at the *same* constant `A` and the
single numerical threshold `hthr`, a nonnegative sample family `B`, in `L^4` at
every cell of `interiorMesoCubeGrid d K n outer`, whose grid fourth-moment root
is below `cgamma^{15}` and which dominates, almost surely and at every depth
cutoff, `|c_1|` times the Besov tower of `U` **and** `|c_2|` times the Besov
tower of `V`.

on the scale bookkeeping, the boundary gate `hsmall`, the threshold `hthr`, the
two scalar caps, the six cellwise typing binders and the two per-depth inputs. -/
theorem exists_besovEnvelope_two_legs_interiorMesoCubeGrid
    (mu : Measure Omega) {K n outer : ℤ} {p g : ℕ}
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (hno : n ≤ outer)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2)
    (U V : Omega → Vec d → Vec d) {gamma A Cg c1 c2 : ℝ}
    (hgamma0 : 0 < gamma) (hA1 : 1 ≤ A) (hCg1 : 1 ≤ Cg)
    (hthr : 200 * (4 * A * Cg) ^ (4 : ℕ) * gamma ^ (4 : ℕ) ≤ 1)
    (hc1 : |c1| ≤ Cg) (hc2 : |c2| ≤ Cg)
    (hmeasU : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      Measurable fun w => meshOscillationCell (n - (i : ℤ)) (U w) R')
    (hintU : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      Integrable (fun w => meshOscillationCell (n - (i : ℤ)) (U w) R' ^ (4 : ℕ)) mu)
    (hmem2U : ∀ (w : Omega) (i : ℕ),
      ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      MemLp (U w) (2 : ℝ≥0∞) (normalizedCubeMeasure R'))
    (hmeasV : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      Measurable fun w => meshOscillationCell (n - (i : ℤ)) (V w) R')
    (hintV : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      Integrable (fun w => meshOscillationCell (n - (i : ℤ)) (V w) R' ^ (4 : ℕ)) mu)
    (hmem2V : ∀ (w : Omega) (i : ℕ),
      ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      MemLp (V w) (2 : ℝ≥0∞) (normalizedCubeMeasure R'))
    (hdepthU : ∀ i : ℕ,
      gridFourthMomentRoot mu (interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1))
          (fun R' w => meshOscillationCell (n - (i : ℤ)) (U w) R') ≤
        A * (gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))))
    (hdepthV : ∀ i : ℕ,
      gridFourthMomentRoot mu (interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1))
          (fun R' w => meshOscillationCell (n - (i : ℤ)) (V w) R') ≤
        A * (gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))) :
    ∃ B : TriadicCube d → Omega → ℝ,
      (∀ R w, 0 ≤ B R w) ∧
      (∀ R ∈ interiorMesoCubeGrid d K n outer, MemLp (B R) 4 mu) ∧
      gridFourthMomentRoot mu (interiorMesoCubeGrid d K n outer) B ≤ gamma ^ (15 : ℕ) ∧
      (∀ R ∈ interiorMesoCubeGrid d K n outer, ∀ᵐ w ∂mu, ∀ N : ℕ,
        |c1| * cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N (U w) ≤
            B R w ∧
          |c2| * cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
              (V w) ≤ B R w) := by
  classical
  have hCg0 : (0 : ℝ) < Cg := lt_of_lt_of_le zero_lt_one hCg1
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  set leg : ℝ := gamma ^ (15 : ℕ) / (4 * Cg) with hleg
  have hleg0 : (0 : ℝ) ≤ leg := by
    rw [hleg]
    have : (0 : ℝ) < 4 * Cg := by linarith
    positivity
  -- the budget premise of the one-leg composite, at the halved target
  have hbudget : 200 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ) ≤ leg ^ (4 : ℕ) := by
    have hden : (0 : ℝ) < (4 * Cg) ^ (4 : ℕ) := by positivity
    have hexp : leg ^ (4 : ℕ) = gamma ^ (60 : ℕ) / (4 * Cg) ^ (4 : ℕ) := by
      rw [hleg, div_pow]
      congr 1
      ring
    rw [hexp, le_div_iff₀ hden]
    have hsplit : 200 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ) * (4 * Cg) ^ (4 : ℕ) =
        gamma ^ (60 : ℕ) * (200 * (4 * A * Cg) ^ (4 : ℕ) * gamma ^ (4 : ℕ)) := by
      ring
    have h60 : (0 : ℝ) ≤ gamma ^ (60 : ℕ) := by positivity
    rw [hsplit]
    calc gamma ^ (60 : ℕ) * (200 * (4 * A * Cg) ^ (4 : ℕ) * gamma ^ (4 : ℕ))
        ≤ gamma ^ (60 : ℕ) * 1 := mul_le_mul_of_nonneg_left hthr h60
      _ = gamma ^ (60 : ℕ) := mul_one _
  -- the two one-leg envelopes
  obtain ⟨BU, hBU0, hBUmem, hBUroot, hBUdom⟩ :=
    exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const mu hK houter hgp
      hno hsmall U hleg0 hbudget hmeasU hintU hmem2U hdepthU
  obtain ⟨BV, hBV0, hBVmem, hBVroot, hBVdom⟩ :=
    exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const mu hK houter hgp
      hno hsmall V hleg0 hbudget hmeasV hintV hmem2V hdepthV
  refine ⟨fun R w => |c1| * BU R w + |c2| * BV R w, ?_, ?_, ?_, ?_⟩
  · intro R w
    have h1 : (0 : ℝ) ≤ |c1| * BU R w := mul_nonneg (abs_nonneg c1) (hBU0 R w)
    have h2 : (0 : ℝ) ≤ |c2| * BV R w := mul_nonneg (abs_nonneg c2) (hBV0 R w)
    linarith
  · intro R hR
    exact ((hBUmem R hR).const_mul |c1|).add ((hBVmem R hR).const_mul |c2|)
  · -- the grid root of the sum
    have hmomU : gridFourthMoment mu (interiorMesoCubeGrid d K n outer)
        (fun R w => |c1| * BU R w) ≤ (|c1| * leg) ^ (4 : ℕ) := by
      refine gridFourthMoment_le_pow_four_of_root_le mu _ _ ?_
      rw [gridFourthMomentRoot_const_mul' mu _ (abs_nonneg c1) BU]
      exact mul_le_mul_of_nonneg_left hBUroot (abs_nonneg c1)
    have hmomV : gridFourthMoment mu (interiorMesoCubeGrid d K n outer)
        (fun R w => |c2| * BV R w) ≤ (|c2| * leg) ^ (4 : ℕ) := by
      refine gridFourthMoment_le_pow_four_of_root_le mu _ _ ?_
      rw [gridFourthMomentRoot_const_mul' mu _ (abs_nonneg c2) BV]
      exact mul_le_mul_of_nonneg_left hBVroot (abs_nonneg c2)
    have hintBU : ∀ R ∈ interiorMesoCubeGrid d K n outer,
        Integrable (fun w => (|c1| * BU R w) ^ (4 : ℝ)) mu := by
      intro R hR
      have hbase := integrable_rpow_four_of_memLp_four (hBUmem R hR) (hBU0 R)
      have hfun : (fun w => (|c1| * BU R w) ^ (4 : ℝ)) =
          fun w => |c1| ^ (4 : ℕ) * (BU R w ^ (4 : ℝ)) := by
        funext w
        rw [rpow_four_eq_pow_four, rpow_four_eq_pow_four, mul_pow]
      rw [hfun]
      exact hbase.const_mul _
    have hintBV : ∀ R ∈ interiorMesoCubeGrid d K n outer,
        Integrable (fun w => (|c2| * BV R w) ^ (4 : ℝ)) mu := by
      intro R hR
      have hbase := integrable_rpow_four_of_memLp_four (hBVmem R hR) (hBV0 R)
      have hfun : (fun w => (|c2| * BV R w) ^ (4 : ℝ)) =
          fun w => |c2| ^ (4 : ℕ) * (BV R w ^ (4 : ℝ)) := by
        funext w
        rw [rpow_four_eq_pow_four, rpow_four_eq_pow_four, mul_pow]
      rw [hfun]
      exact hbase.const_mul _
    have hsum := gridFourthMomentRoot_le_add_of_le mu (interiorMesoCubeGrid d K n outer)
      (fun R w => |c1| * BU R w + |c2| * BV R w) (fun R w => |c1| * BU R w)
      (fun R w => |c2| * BV R w)
      (mul_nonneg (abs_nonneg c1) hleg0) (mul_nonneg (abs_nonneg c2) hleg0)
      (fun R _ w => by
        have h1 : (0 : ℝ) ≤ |c1| * BU R w := mul_nonneg (abs_nonneg c1) (hBU0 R w)
        have h2 : (0 : ℝ) ≤ |c2| * BV R w := mul_nonneg (abs_nonneg c2) (hBV0 R w)
        linarith)
      (fun _ _ _ => le_refl _) hintBU hintBV hmomU hmomV
    refine hsum.trans ?_
    have h8 : (8 : ℝ) ^ ((4 : ℝ)⁻¹) ≤ 2 := by
      have hmono : (8 : ℝ) ^ ((4 : ℝ)⁻¹) ≤ (16 : ℝ) ^ ((4 : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      have hval : (16 : ℝ) ^ ((4 : ℝ)⁻¹) = 2 := by
        have h16 : (16 : ℝ) = (2 : ℝ) ^ ((4 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; norm_num
        rw [h16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      linarith [hmono, hval.le, hval.ge]
    have hcsum : |c1| * leg + |c2| * leg ≤ gamma ^ (15 : ℕ) / 2 := by
      have hstep : |c1| * leg + |c2| * leg = (|c1| + |c2|) * leg := by ring
      have hcc : |c1| + |c2| ≤ 2 * Cg := by linarith
      have hmul : (|c1| + |c2|) * leg ≤ (2 * Cg) * leg :=
        mul_le_mul_of_nonneg_right hcc hleg0
      have hval : (2 * Cg) * leg = gamma ^ (15 : ℕ) / 2 := by
        rw [hleg]
        field_simp
        ring
      rw [hstep]
      linarith [hmul, hval.le, hval.ge]
    have hpos : (0 : ℝ) ≤ |c1| * leg + |c2| * leg := by
      have h1 : (0 : ℝ) ≤ |c1| * leg := mul_nonneg (abs_nonneg c1) hleg0
      have h2 : (0 : ℝ) ≤ |c2| * leg := mul_nonneg (abs_nonneg c2) hleg0
      linarith
    calc (8 : ℝ) ^ ((4 : ℝ)⁻¹) * (|c1| * leg + |c2| * leg)
        ≤ 2 * (|c1| * leg + |c2| * leg) := mul_le_mul_of_nonneg_right h8 hpos
      _ ≤ 2 * (gamma ^ (15 : ℕ) / 2) := by linarith [hcsum]
      _ = gamma ^ (15 : ℕ) := by ring
  · -- the two dominations
    intro R hR
    filter_upwards [hBUdom R hR, hBVdom R hR] with w hwU hwV
    intro N
    have h1 : (0 : ℝ) ≤ |c1| * BU R w := mul_nonneg (abs_nonneg c1) (hBU0 R w)
    have h2 : (0 : ℝ) ≤ |c2| * BV R w := mul_nonneg (abs_nonneg c2) (hBV0 R w)
    constructor
    · have hstep : |c1| *
          cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N (U w) ≤
          |c1| * BU R w := mul_le_mul_of_nonneg_left (hwU N) (abs_nonneg c1)
      linarith
    · have hstep : |c2| *
          cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N (V w) ≤
          |c2| * BV R w := mul_le_mul_of_nonneg_left (hwV N) (abs_nonneg c2)
      linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
