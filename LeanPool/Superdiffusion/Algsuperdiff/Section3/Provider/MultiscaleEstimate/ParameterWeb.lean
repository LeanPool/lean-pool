/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.HomogenizationInput
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.WaveSizesZeroth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# ParameterWeb

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the parameter web of `p.multiscale.estimate`

This module collects the *parameter-discharge* obligations accumulated across
the proved Section 3.6 modules and routes all of them
through a single arithmetic core: the two scalar binders of the multiscale
proposition's own hypothesis list,

```
(c⋆)⁻¹ ε^{-Cms} ≤ E                  (the window)
γ ≤ (E⁻¹)^{10}                       (the smallness)
```

## The arithmetic core, in one paragraph

On `ε ∈ (0,1/2]` one has `ε⁻¹ ≥ 2`, hence `ε^{-a} ≥ 2^a` for every `a ≥ 0`
(`two_rpow_le_rpow_neg`).  The proved `Provider.Disorder.cstar_le_three_halves`
gives `c⋆⁻¹ ≥ 2/3`, so the window binder yields the two floors

```
K * c⋆⁻¹ ≤ E        whenever K ≤ 2^{Cms}        (the RELATIVE gate)
K ≤ E               whenever (3/2) K ≤ 2^{Cms}  (the ABSOLUTE gate)
```

and in particular `10 ≤ E` as soon as `Cms ≥ 4`.  The smallness binder then
turns every `E`-floor into a `γ`-ceiling.  For the corridor one uses the
*logarithmic* form of the same window: `ε^{-Cms} = exp(Cms |log ε|)` and
`x + 1 ≤ exp x` give `Cms |log ε| ≤ (3/2) E`, so the integer cutoff
`h := waveCutoff (2 Chom) ε = ⌈2 Chom |log ε|⌉` obeys `h ≤ 3 Chom E / Cms + 1`,
which is `≤ 3E + 1` once the witness satisfies `Chom ≤ Cms`.

## The `10^9` and where it may appear (development decision D4)

What §3 and §5 prove is strictly stronger and numeral free — the `ε^2` form `γ
≤ Chom⁻¹ E^{-2} ε^2` (development decision D2, the form the proved
`homogenizationStep_spec` consumes) and the corridor `γ h ≤ 1`, both on a
**free** real `Chom` and on the sole witness constraints `4 ≤ Cms`, `Chom ≤
Cms`, `Chom ≤ 2^{Cms}`.

Those constraints are satisfiable for **every** real `Chom`: that is
`exists_parameterWeb_general` (§8), which binds `Chom` freely.  Consequently
`max (homogenizationStepConst d) 10^9` is a legitimate instantiation of that
theorem, at which this module's own `Chom`-free dischargers
(`gamma_mul_waveCutoff_le_one`, and `chom_le_pow_mul_sq_of_window` composed
with `gamma_le_gate_of_pow`) deliver BOTH enlarged obligations — the corridor
and the `ε^2` gate at the enlarged constant.  The numeral `10^9` therefore
occurs in no statement of this file: it is a *witness choice inside an
existential* and never a claim about `.choose`.

## `_root_` anchoring: prophylactic, measured

The three `open _root_.…` lines below are **not** load-bearing in this module.
The anchoring is kept because the enclosing namespace
`Algsuperdiff.Section3.Provider.MultiscaleEstimate` is a sibling of
`Algsuperdiff.Section3.Provider.Multiscale` (Section 3.3, 77 files, live name
collisions — development decision D5), so a future sibling declaration named
`Homogenization` or `MeasureTheory` would silently capture the open.  No claim
of present load-bearing is made.

## Sources

* ABK26, `p.multiscale.estimate` and its parameter conditions, the cutoff `h :=
  C|log ε|`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ}

/-! ## 1. The window floor

The frozen root binds `ε ∈ (0,1/2]` and `(c⋆)⁻¹ ε^{-Cms} ≤ E`.  Everything in
§2-§5 is read off those two lines together with `c⋆ ≤ 3/2`. -/

/-- `2^a ≤ 1` fails for `a < 0`; on `a ≥ 0` the base-2 power is at least one. -/
theorem one_le_two_rpow {a : ℝ} (ha : 0 ≤ a) : (1 : ℝ) ≤ (2 : ℝ) ^ a := by
  simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha

/-- **The window's exponential floor.**  On `ε ∈ (0,1/2]` the negative power
`ε^{-a}` dominates `2^a` for every `a ≥ 0`. -/
theorem two_rpow_le_rpow_neg {epsilon a : ℝ} (heps0 : 0 < epsilon)
    (heps : epsilon ≤ 1 / 2) (ha : 0 ≤ a) :
    (2 : ℝ) ^ a ≤ epsilon ^ (-a) := by
  have hinv : (2 : ℝ) ≤ epsilon⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) heps0]
    linarith
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) hinv ha
  rwa [Real.inv_rpow heps0.le, ← Real.rpow_neg heps0.le] at h

/-- **The shell constant's reciprocal floor.**  From the proved
`Provider.Disorder.cstar_le_three_halves`. -/
theorem two_thirds_le_cstar_inv (M : ABKModel d) :
    (2 / 3 : ℝ) ≤ (Disorder.cstar M)⁻¹ := by
  have hpos : 0 < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hupper : Disorder.cstar M ≤ 3 / 2 :=
    Provider.Disorder.cstar_le_three_halves M
  rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3 / 2) hpos).2 hupper

/-- **The model-free window floor.**  The frozen window binder, with `c⋆⁻¹`
replaced by its absolute lower bound `2/3`.  Every later statement of §2-§5
takes this as its hypothesis, so it is stated once and proved once. -/
theorem two_thirds_mul_le_of_window {cstarInv epsilon Cms E : ℝ}
    (hcs : (2 / 3 : ℝ) ≤ cstarInv) (hpow : 0 ≤ epsilon ^ (-Cms))
    (hwin : cstarInv * epsilon ^ (-Cms) ≤ E) :
    (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E :=
  le_trans (mul_le_mul_of_nonneg_right hcs hpow) hwin

/-- The model-level form of `two_thirds_mul_le_of_window`, at the frozen root's
own window binder. -/
theorem two_thirds_mul_le_of_window' (M : ABKModel d) {epsilon Cms E : ℝ}
    (heps0 : 0 < epsilon)
    (hwin : (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ E) :
    (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E :=
  two_thirds_mul_le_of_window (two_thirds_le_cstar_inv M)
    (Real.rpow_pos_of_pos heps0 _).le hwin

/-- The manuscript's `E ≥ 15` is *not* used anywhere in this module. -/
theorem ten_le_of_window {epsilon Cms E : ℝ} (heps0 : 0 < epsilon)
    (heps : epsilon ≤ 1 / 2) (hCms : 4 ≤ Cms)
    (hfloor : (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E) :
    (10 : ℝ) ≤ E := by
  have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ Cms := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hCms
    have h4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith [h4 ▸ h]
  have h2 : (2 : ℝ) ^ Cms ≤ epsilon ^ (-Cms) :=
    two_rpow_le_rpow_neg heps0 heps (by linarith)
  linarith

/-- **The logarithmic form of the window.**  `ε^{-Cms} = exp(Cms |log ε|)` and `x +
1 ≤ exp x` turn the window binder into a linear bound on `|log ε|`.  This is
the step the corridor budget of §5 runs on; the private
`badEventMultiscaleGates` performs it inline in
`Provider/BadEvents/BadEventMultiscaleConsumption.lean`, as `hExpScale` and
`hLinearExp` (header census, item 3). -/
theorem abs_log_le_of_window {epsilon Cms E : ℝ} (heps0 : 0 < epsilon)
    (heps : epsilon ≤ 1 / 2)
    (hfloor : (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E) :
    Cms * |Real.log epsilon| ≤ (3 / 2) * E := by
  have hlognp : Real.log epsilon ≤ 0 := Real.log_nonpos heps0.le (by linarith)
  have habs : |Real.log epsilon| = -Real.log epsilon := abs_of_nonpos hlognp
  have hexp : Real.exp (Cms * |Real.log epsilon|) = epsilon ^ (-Cms) := by
    rw [Real.rpow_def_of_pos heps0, habs]
    congr 1
    ring
  have hle : Cms * |Real.log epsilon| + 1 ≤ Real.exp (Cms * |Real.log epsilon|) :=
    Real.add_one_le_exp _
  rw [hexp] at hle
  linarith

/-! ## 2. The constant-`E` gates

(ii) (vi).  Both are instances of one of two shapes, and both are absorbed by
the root's own `c⋆⁻¹ ε^{-Cms}` witness at a witness-choice constraint on `Cms`. -/

/-- **The relative gate.**  A demand of the shape `K c⋆⁻¹ ≤ E` — the shape of
`p.homogenization.step`'s `15 c⋆⁻¹ ≤ E` and of `l.shom.continuity`'s
`Cshom c⋆⁻¹ ≤ E` — is discharged by the window as soon as the chosen witness
satisfies `K ≤ 2^{Cms}`.  No bound on `c⋆` is needed on this branch. -/
theorem relative_gate_le_of_window {cstarInv epsilon Cms E K : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) (hCms : 0 ≤ Cms)
    (hcs : 0 ≤ cstarInv) (hK : K ≤ (2 : ℝ) ^ Cms)
    (hwin : cstarInv * epsilon ^ (-Cms) ≤ E) :
    K * cstarInv ≤ E := by
  have h2 : (2 : ℝ) ^ Cms ≤ epsilon ^ (-Cms) :=
    two_rpow_le_rpow_neg heps0 heps hCms
  calc K * cstarInv ≤ epsilon ^ (-Cms) * cstarInv :=
        mul_le_mul_of_nonneg_right (hK.trans h2) hcs
    _ = cstarInv * epsilon ^ (-Cms) := by ring
    _ ≤ E := hwin

/-- **The absolute gate.**  A demand of the shape `K ≤ E` with `K` a constant of
the model-free part of the argument — the shape of the coarse-graining gate
`exp(Ccg/(1/7)) ≤ E` — is discharged by the window together with `c⋆ ≤ 3/2`, at
the witness-choice constraint `(3/2) K ≤ 2^{Cms}`. -/
theorem absolute_gate_le_of_window {epsilon Cms E K : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) (hCms : 0 ≤ Cms)
    (hK : (3 / 2 : ℝ) * K ≤ (2 : ℝ) ^ Cms)
    (hfloor : (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E) :
    K ≤ E := by
  have h2 : (2 : ℝ) ^ Cms ≤ epsilon ^ (-Cms) :=
    two_rpow_le_rpow_neg heps0 heps hCms
  linarith

/-- ** (vi): `15 c⋆⁻¹ ≤ E`.**

The honest route is `2^{Cms} ≥ 15`, i.e. `Cms ≥ 4`: the demand is *relative* to
`c⋆⁻¹`, exactly like the root's own window, so it needs no bound on `c⋆`
whatsoever.  That route proves a *different* statement (`10 ≤ E`, delivered
separately as `ten_le_of_window`) and does not by itself give `15 c⋆⁻¹ ≤ E`
when `c⋆` is small; the `2^{Cms} ≥ 15` route does, uniformly in the model, and
is the one taken. -/
theorem fifteen_mul_cstar_inv_le_of_window (M : ABKModel d) {epsilon Cms E : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) (hCms : 4 ≤ Cms)
    (hwin : (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ E) :
    15 * (Disorder.cstar M)⁻¹ ≤ E := by
  have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ Cms := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hCms
    have h4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith [h4 ▸ h]
  exact relative_gate_le_of_window heps0 heps (by linarith)
    (le_of_lt (inv_pos.2 (Provider.Orlicz.cstar_pos M))) (by linarith) hwin

/-- ** (ii), first gate: `exp(Ccg/(1/7)) ≤ E`.**

The coarse-graining gate of the frozen `coarse_ellipticity_bounds` at `σ =
1/7`, in the `max` spelling the proved `exists_crude_bound` consumes.  Its
second entry `c⋆⁻¹ ≤ E` is free from the window at `Cms ≥ 0`; the first is the
absolute gate at the witness-choice constraint `(3/2) exp(7 Ccg) ≤ 2^{Cms}`. -/
theorem coarseGrainingGate_le_of_window (M : ABKModel d) {epsilon Cms E Ccg : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) (hCms : 0 ≤ Cms)
    (hK : (3 / 2 : ℝ) * Real.exp (Ccg / (1 / 7)) ≤ (2 : ℝ) ^ Cms)
    (hwin : (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ E) :
    max (Real.exp (Ccg / (1 / 7))) (Disorder.cstar M)⁻¹ ≤ E := by
  refine max_le ?_ ?_
  · exact absolute_gate_le_of_window heps0 heps hCms hK
      (two_thirds_mul_le_of_window' M heps0 hwin)
  · have := relative_gate_le_of_window (K := 1) heps0 heps hCms
      (le_of_lt (inv_pos.2 (Provider.Orlicz.cstar_pos M)))
      (one_le_two_rpow hCms) hwin
    linarith

/-- ** (ii), second gate: `Cshom c⋆⁻¹ ≤ E`.**

The gauge-conversion gate of `l.shom.continuity`, at the witness-choice
constraint `Cshom ≤ 2^{Cms}`. -/
theorem shomGate_le_of_window (M : ABKModel d) {epsilon Cms E Cshom : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) (hCms : 0 ≤ Cms)
    (hK : Cshom ≤ (2 : ℝ) ^ Cms)
    (hwin : (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ E) :
    Cshom * (Disorder.cstar M)⁻¹ ≤ E :=
  relative_gate_le_of_window heps0 heps hCms
    (le_of_lt (inv_pos.2 (Provider.Orlicz.cstar_pos M))) hK hwin

/-! ## 3. The `γ`-ceilings

Every `E`-floor of §2 becomes a `γ`-ceiling through the root's own second
scalar binder `γ ≤ (E⁻¹)^{10}`. -/

/-- The arithmetic core of the `ε²` smallness gate: the window forces
`Chom ≤ E^8 ε^2` at the witness-choice constraints `4 ≤ Cms`,
`Chom ≤ 2^{Cms}`.

The margin is enormous and entirely explicit: `E^8 ε^2 ≥ (2/3)^8 2^{8Cms-2}`,
while the constraint only asks `Chom ≤ 2^{Cms}`, so the slack is the factor
`(2/3)^8 2^{7Cms-2} ≥ (256/6561)·2^{26} > 2.6·10^6` at `Cms = 4`. -/
theorem chom_le_pow_mul_sq_of_window {epsilon Cms E Chom : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) (hCms : 4 ≤ Cms)
    (hChom : Chom ≤ (2 : ℝ) ^ Cms)
    (hfloor : (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E) :
    Chom ≤ E ^ 8 * epsilon ^ 2 := by
  set P : ℝ := epsilon ^ (-Cms) with hPdef
  have hPpos : (0 : ℝ) < P := Real.rpow_pos_of_pos heps0 _
  have hEpos : (0 : ℝ) < E := by nlinarith
  have hP8 : P ^ 8 = epsilon ^ (-(8 * Cms)) := by
    rw [hPdef, ← Real.rpow_natCast (epsilon ^ (-Cms)) 8, ← Real.rpow_mul heps0.le]
    norm_num
    ring_nf
  have heps2 : epsilon ^ 2 = epsilon ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcomb : P ^ 8 * epsilon ^ 2 = epsilon ^ (-(8 * Cms - 2)) := by
    rw [hP8, heps2, ← Real.rpow_add heps0]
    ring_nf
  have hlow : (2 : ℝ) ^ (8 * Cms - 2) ≤ P ^ 8 * epsilon ^ 2 := by
    rw [hcomb]
    exact two_rpow_le_rpow_neg heps0 heps (by linarith)
  have hsplit : (2 : ℝ) ^ (8 * Cms - 2) = (2 : ℝ) ^ Cms * (2 : ℝ) ^ (7 * Cms - 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have h26 : (67108864 : ℝ) ≤ (2 : ℝ) ^ (7 * Cms - 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : (26 : ℝ) ≤ 7 * Cms - 2)
    have h26' : (2 : ℝ) ^ (26 : ℝ) = 67108864 := by
      rw [show (26 : ℝ) = ((26 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith [h26' ▸ h]
  have hCmspos : (0 : ℝ) < (2 : ℝ) ^ Cms := Real.rpow_pos_of_pos (by norm_num) _
  have hkey : (2 : ℝ) ^ Cms ≤
      (2 / 3 : ℝ) ^ 8 * ((2 : ℝ) ^ Cms * (2 : ℝ) ^ (7 * Cms - 2)) := by
    have h1 : (2 : ℝ) ^ Cms * 67108864 ≤ (2 : ℝ) ^ Cms * (2 : ℝ) ^ (7 * Cms - 2) :=
      mul_le_mul_of_nonneg_left h26 hCmspos.le
    nlinarith [hCmspos]
  have hE8 : ((2 / 3 : ℝ) * P) ^ 8 ≤ E ^ 8 :=
    pow_le_pow_left₀ (by positivity) hfloor 8
  have hexpand : ((2 / 3 : ℝ) * P) ^ 8 = (2 / 3 : ℝ) ^ 8 * P ^ 8 := by ring
  calc Chom ≤ (2 : ℝ) ^ Cms := hChom
    _ ≤ (2 / 3 : ℝ) ^ 8 * ((2 : ℝ) ^ Cms * (2 : ℝ) ^ (7 * Cms - 2)) := hkey
    _ = (2 / 3 : ℝ) ^ 8 * (2 : ℝ) ^ (8 * Cms - 2) := by rw [hsplit]
    _ ≤ (2 / 3 : ℝ) ^ 8 * (P ^ 8 * epsilon ^ 2) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = ((2 / 3 : ℝ) * P) ^ 8 * epsilon ^ 2 := by rw [hexpand]; ring
    _ ≤ E ^ 8 * epsilon ^ 2 := by
        have : (0 : ℝ) < epsilon ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_right hE8 this.le

/-- The `ε²` smallness gate in the consumer's spelling, over plain reals. -/
theorem gamma_le_gate_of_pow {epsilon E Chom gamma : ℝ}
    (hChom0 : 0 < Chom) (hEpos : 0 < E)
    (hgate : Chom ≤ E ^ 8 * epsilon ^ 2)
    (hgamma : gamma ≤ (E⁻¹) ^ 10) :
    gamma ≤ Chom⁻¹ * (E⁻¹) ^ 2 * epsilon ^ 2 := by
  have hEne : E ≠ 0 := ne_of_gt hEpos
  have hCne : Chom ≠ 0 := ne_of_gt hChom0
  have hstep : (E⁻¹) ^ 8 ≤ Chom⁻¹ * epsilon ^ 2 := by
    have hmul : (0 : ℝ) < E ^ 8 * Chom := by positivity
    refine le_of_mul_le_mul_right ?_ hmul
    have e1 : (E⁻¹) ^ 8 * (E ^ 8 * Chom) = Chom := by field_simp
    have e2 : Chom⁻¹ * epsilon ^ 2 * (E ^ 8 * Chom) = epsilon ^ 2 * E ^ 8 := by
      field_simp
    rw [e1, e2]
    linarith
  have h : (E⁻¹) ^ 2 * (E⁻¹) ^ 8 ≤ (E⁻¹) ^ 2 * (Chom⁻¹ * epsilon ^ 2) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  calc gamma ≤ (E⁻¹) ^ 10 := hgamma
    _ = (E⁻¹) ^ 2 * (E⁻¹) ^ 8 := by ring
    _ ≤ (E⁻¹) ^ 2 * (Chom⁻¹ * epsilon ^ 2) := h
    _ = Chom⁻¹ * (E⁻¹) ^ 2 * epsilon ^ 2 := by ring

/-! ## 5. The corridor cutoff `h := waveCutoff (2 Chom) ε`

: the manuscript sets `h := C|log ε|`, which is not an integer, and the
localization lemma needs `h ∈ ℕ`.  The proved integer cutoff is `waveCutoff C₀
ε = ⌈C₀ |log ε|⌉₊` (`WaveSizesZeroth.lean`); the development's instantiation
is `C₀ := 2 Chom`, the doubling being the `ε²`-route cost of development
decision D2. -/

/-- **`1 ≤ h` at the development's own cutoff.**  The one new binder of
`BadEventSummed.exists_badEventSup_isBigOWith_gammaOne`, whose printed window
had to exclude `h = 0`, is at the instantiation: `ε ≤ 1/2` makes `|log ε| > 0`,
so the ceiling is at least one. -/
theorem one_le_waveCutoff {C0 epsilon : ℝ} (hC0 : 0 < C0) (heps0 : 0 < epsilon)
    (heps : epsilon ≤ 1 / 2) :
    1 ≤ waveCutoff C0 epsilon := by
  have hlognp : Real.log epsilon < 0 := Real.log_neg heps0 (by linarith)
  have habs : (0 : ℝ) < |Real.log epsilon| := abs_pos.2 (ne_of_lt hlognp)
  exact Nat.one_le_ceil_iff.mpr (mul_pos hC0 habs)

/-- ** (v): the corridor budget.**  The integer cutoff is at least the printed real
one, so `h ≥ C₀ |log ε|` — at the development's `C₀ := 2 Chom` this is exactly
the corridor `h ≥ 2 Chom |log ε|` that the `ε²`-route endpoints of
`HomogenizationInput` require. -/
theorem le_waveCutoff (C0 epsilon : ℝ) :
    C0 * |Real.log epsilon| ≤ ((waveCutoff C0 epsilon : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- The ceiling overshoot, in the form the consumers' `H`-budget binder
`(h : ℝ) ≤ H |log ε| + 1` asks for: at `H := C₀` the binder is an equality of
shapes. -/
theorem waveCutoff_le_add_one {C0 epsilon : ℝ} (hC0 : 0 ≤ C0) :
    ((waveCutoff C0 epsilon : ℕ) : ℝ) ≤ C0 * |Real.log epsilon| + 1 :=
  (Nat.ceil_lt_add_one (mul_nonneg hC0 (abs_nonneg _))).le

/-- ** (i): `γ h ≤ 1`.**

The printed window of `l.localization.mathcalE` and the collapse hypothesis of
the proved `AggregationRemainder` both carry `γ h ≤ 1`; the aggregation record
booked its discharge to this module.  Route: the logarithmic window
(`abs_log_le_of_window`) bounds `|log ε|` by `(3/2) E / Cms`, the ceiling costs
one, and `Chom ≤ Cms` turns the result into `h ≤ 3E + 1`, which `γ ≤ E^{-10}`
crushes at `E ≥ 10` with nine orders of magnitude to spare.

The witness-choice constraint `Chom ≤ Cms` is the whole of what the corridor
costs; `exists_parameterWeb_general` meets it, at a `Chom`, hence also at the
enlarged `max Chom 10^9`. -/
theorem gamma_mul_waveCutoff_le_one {epsilon Cms E gamma Chom : ℝ}
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2)
    (hCms : 4 ≤ Cms) (hChom0 : 0 ≤ Chom) (hChomCms : Chom ≤ Cms)
    (hfloor : (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ E)
    (hgamma : gamma ≤ (E⁻¹) ^ 10) :
    gamma * ((waveCutoff (2 * Chom) epsilon : ℕ) : ℝ) ≤ 1 := by
  have hE : (10 : ℝ) ≤ E := ten_le_of_window heps0 heps hCms hfloor
  have hEpos : (0 : ℝ) < E := by linarith
  have hL0 : (0 : ℝ) ≤ |Real.log epsilon| := abs_nonneg _
  have hCmsL : Cms * |Real.log epsilon| ≤ (3 / 2) * E :=
    abs_log_le_of_window heps0 heps hfloor
  have hceil : ((waveCutoff (2 * Chom) epsilon : ℕ) : ℝ)
      ≤ 2 * Chom * |Real.log epsilon| + 1 :=
    waveCutoff_le_add_one (by linarith)
  have hkey : 2 * Chom * |Real.log epsilon| ≤ 3 * E := by
    have h1 : Chom * |Real.log epsilon| ≤ Cms * |Real.log epsilon| :=
      mul_le_mul_of_nonneg_right hChomCms hL0
    linarith
  have hh : ((waveCutoff (2 * Chom) epsilon : ℕ) : ℝ) ≤ 3 * E + 1 := by linarith
  have hh0 : (0 : ℝ) ≤ ((waveCutoff (2 * Chom) epsilon : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hinv : E⁻¹ ≤ 1 / 10 := by
    rw [inv_le_comm₀ hEpos (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) ≤ E⁻¹ := le_of_lt (inv_pos.mpr hEpos)
  have h9 : (E⁻¹) ^ 9 ≤ (1 / 10 : ℝ) ^ 9 := pow_le_pow_left₀ hinv0 hinv 9
  have h10 : (E⁻¹) ^ 10 ≤ (1 / 10 : ℝ) ^ 10 := pow_le_pow_left₀ hinv0 hinv 10
  have hEmul : E * (E⁻¹) ^ 10 = (E⁻¹) ^ 9 := by
    field_simp
  calc gamma * ((waveCutoff (2 * Chom) epsilon : ℕ) : ℝ)
      ≤ (E⁻¹) ^ 10 * (3 * E + 1) := mul_le_mul hgamma hh hh0 (by positivity)
    _ = 3 * (E * (E⁻¹) ^ 10) + (E⁻¹) ^ 10 := by ring
    _ = 3 * (E⁻¹) ^ 9 + (E⁻¹) ^ 10 := by rw [hEmul]
    _ ≤ 3 * (1 / 10 : ℝ) ^ 9 + (1 / 10 : ℝ) ^ 10 := by linarith
    _ ≤ 1 := by norm_num

/-- ** (vi): `3^{5h} ≤ ε^{-C}` with `C` explicit.**

The absorption at the integer cutoff, in the exact `rpow` spelling `(3: ℝ) ^ (5
* (h: ℝ))` that the proved bad-event amplitudes carry
(`BadEventIngredients.lean`, `BadEventSummed.lean`).  The output constant is

```
C(C₀) = 5 C₀ log 3 + 8 ,
```

explicit in the cutoff constant `C₀`, hence explicit in `Chom` at the
development's `C₀ := 2 Chom`.  The `+8` is the ceiling overshoot: `⌈x⌉ < x + 1`
leaves the factor `3^5 = 243`, which `ε ≤ 1/2` absorbs into `ε^{-8}` because
`2^8 = 256 ≥ 243`.  The proved private twin at exponent `8`
(`three_pow_eight_cutoff_le` in `WaveSizesZeroth.lean`) leaves its `6561`
standing in front instead. -/
theorem three_rpow_five_waveCutoff_le {C0 epsilon : ℝ} (hC0 : 0 ≤ C0)
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 1 / 2) :
    (3 : ℝ) ^ (5 * ((waveCutoff C0 epsilon : ℕ) : ℝ)) ≤
      epsilon ^ (-(5 * C0 * Real.log 3 + 8)) := by
  set L : ℝ := |Real.log epsilon| with hLdef
  have hlognp : Real.log epsilon ≤ 0 := Real.log_nonpos heps0.le (by linarith)
  have hL : L = -Real.log epsilon := abs_of_nonpos hlognp
  have hL0 : 0 ≤ L := abs_nonneg _
  have hceil : ((waveCutoff C0 epsilon : ℕ) : ℝ) ≤ C0 * L + 1 :=
    waveCutoff_le_add_one hC0
  have hmono : (3 : ℝ) ^ (5 * ((waveCutoff C0 epsilon : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ ((5 : ℝ) * (C0 * L + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsplit : (3 : ℝ) ^ ((5 : ℝ) * (C0 * L + 1)) =
      (3 : ℝ) ^ (5 : ℝ) * (3 : ℝ) ^ (5 * C0 * L) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have h35 : (3 : ℝ) ^ (5 : ℝ) = 243 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have heq : (3 : ℝ) ^ (5 * C0 * L) = epsilon ^ (-(5 * C0 * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos heps0, hL]
    congr 1
    ring
  have h8 : (243 : ℝ) ≤ epsilon ^ (-(8 : ℝ)) := by
    have h := two_rpow_le_rpow_neg heps0 heps (by norm_num : (0 : ℝ) ≤ 8)
    have h256 : (2 : ℝ) ^ (8 : ℝ) = 256 := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h256] at h
    linarith
  have hpos : (0 : ℝ) < epsilon ^ (-(5 * C0 * Real.log 3)) :=
    Real.rpow_pos_of_pos heps0 _
  calc (3 : ℝ) ^ (5 * ((waveCutoff C0 epsilon : ℕ) : ℝ))
      ≤ (3 : ℝ) ^ ((5 : ℝ) * (C0 * L + 1)) := hmono
    _ = 243 * epsilon ^ (-(5 * C0 * Real.log 3)) := by rw [hsplit, h35, heq]
    _ ≤ epsilon ^ (-(8 : ℝ)) * epsilon ^ (-(5 * C0 * Real.log 3)) :=
        mul_le_mul_of_nonneg_right h8 hpos.le
    _ = epsilon ^ (-(5 * C0 * Real.log 3 + 8)) := by
        rw [← Real.rpow_add heps0]
        ring_nf

/-- **The window binder transfers to any larger witness.**  If the window holds
at `Cms'` and `Cms ≤ Cms'`, it holds at `Cms`.  This is the direction the
enlargement needs: assuming the strong hypothesis at `max Cms 1`, one may still
apply the root at `Cms`. -/
theorem window_of_le {cstarInv epsilon Cms Cms' E : ℝ} (heps0 : 0 < epsilon)
    (heps1 : epsilon ≤ 1) (hcs : 0 ≤ cstarInv) (hle : Cms ≤ Cms')
    (hwin : cstarInv * epsilon ^ (-Cms') ≤ E) :
    cstarInv * epsilon ^ (-Cms) ≤ E := by
  have h : epsilon ^ (-Cms) ≤ epsilon ^ (-Cms') :=
    Real.rpow_le_rpow_of_exponent_ge heps0 heps1 (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_left h hcs) hwin

section Carrier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 7. The almost-everywhere to pointwise witness bridge
((iii))

`Probability.IsTwoTermBigOWithWitnesses` demands the domination `∀ ω, X ω ≤ Y ω
+ Z ω` **pointwise**, while every Section 3 identification of an observable
with an analytic quantity is only almost everywhere (the observables are
measurable representatives).

The proved witness upgrade `Provider.Tail.isTwoTermBigOWith_of_ae_le`
(`Provider/Tail/TailSqrt.lean`) delivers the **existential**
`IsTwoTermBigOWith` and forgets the modified witnesses.  The frozen multiscale
conclusion is not of that shape: its second conjunct is an `IsBigOWith` clause
on the *same* `Y` that the first conjunct names, so the upgrade must return
witnesses whose relation to the given ones is known.  The statement below
returns exactly that — the modified pair is almost everywhere equal to the
given pair — from which every tail of the original witnesses transfers by the
proved `Provider.Tail.isBigOWith_of_ae_eq`.  In particular the refinement
clause survives the modification with no extra hypothesis.

The construction is the proved one (modify on the measurable null set where the
inequality fails, sending the failure into the `Z`-slot); the two tail
transfers `Provider.Tail.isBigOWith_of_ae_eq`.  `IsFiniteMeasure` is NOT
required. -/

/-- **The witness upgrade with its witnesses named.**  See the
section docstring. -/
theorem exists_witnesses_ae_eq_of_ae_le
    {Ψ₁ Ψ₂ : ℝ → ℝ} {X Y Z : Ω → ℝ} {A₁ A₂ : ℝ}
    (hΨ₁ : Probability.IsAdmissibleTail Ψ₁)
    (hΨ₂ : Probability.IsAdmissibleTail Ψ₂)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ Y ω + Z ω)
    (hYt : IsBigOWith μ Ψ₁ Y A₁) (hZt : IsBigOWith μ Ψ₂ Z A₂) :
    ∃ Y' Z' : Ω → ℝ,
      Probability.IsTwoTermBigOWithWitnesses μ Ψ₁ Ψ₂ X Y' Z' A₁ A₂ ∧
        Y' =ᵐ[μ] Y ∧ Z' =ᵐ[μ] Z := by
  classical
  set N : Set Ω := {ω | Y ω + Z ω < X ω} with hN
  have hNmeas : MeasurableSet N := measurableSet_lt (hY.add hZ) hX
  have hNnull : μ N = 0 := by
    have h := ae_iff.1 hle
    simpa [hN, not_le] using h
  have hout : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hNnull
  have hYae : (fun ω => if ω ∈ N then (0 : ℝ) else Y ω) =ᵐ[μ] Y := by
    filter_upwards [hout] with ω hω
    simp [hω]
  have hZae : (fun ω => if ω ∈ N then X ω else Z ω) =ᵐ[μ] Z := by
    filter_upwards [hout] with ω hω
    simp [hω]
  refine ⟨fun ω => if ω ∈ N then 0 else Y ω, fun ω => if ω ∈ N then X ω else Z ω,
    ⟨hΨ₁, hΨ₂, hA₁, hA₂, hX, ?_, ?_, ?_, ?_, ?_⟩, hYae, hZae⟩
  · exact Measurable.ite hNmeas measurable_const hY
  · exact Measurable.ite hNmeas hX hZ
  · intro ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · simp only [hω, ite_false]
      exact not_lt.1 (by simpa [hN] using hω)
  · exact Provider.Tail.isBigOWith_of_ae_eq hYae.symm hYt
  · exact Provider.Tail.isBigOWith_of_ae_eq hZae.symm hZt

end Carrier

/-! ## 8. Feasibility of the witness choice

Every constraint the web places on `Cms` is a constraint on the *existential
witness of the conclusion*, chosen after the homogenization constant `Chom` is
in hand (development decision D4).

`exists_parameterWeb_general` is the theorem with `Chom` a free binder, which
is what makes the enlarged witness `max Chom 10^9`'s addendum a genuine
instantiation rather than a wish. -/

/-- `2 ^ (log K / log 2) = K` for `K > 0`; the base-2 logarithm written out, so
that §8's witness needs no `Real.logb` in its statement.

The proof below therefore the Mathlib lemma rather than re-deriving it, and
this statement is retained only as the `log/log` spelling in which the witness
of `exists_parameterWeb_general` is written.  Any future base-2 site must
consume `Real.rpow_logb` directly. -/
theorem two_rpow_log_div_log_two {K : ℝ} (hK : 0 < K) :
    (2 : ℝ) ^ (Real.log K / Real.log 2) = K := by
  rw [Real.log_div_log]
  exact Real.rpow_logb (by norm_num) (by norm_num) hK

/-- **The parameter web is feasible, at every `Chom`.**  For every real
homogenization constant `Chom`, every window exponent `Cwin` that a consumer
carries in its own existential, and every pair of development constants `Ccg`,
`Cshom`, there is a witness `Cms` meeting *all* constraints the dischargers of
§2-§6 impose at once:

* `4 ≤ Cms` — the `E ≥ 10` floor, the `15 ≤ 2^{Cms}` gate and the `ε²` gate;
* `Chom ≤ Cms` — the corridor budget `γ h ≤ 1`
  (`gamma_mul_waveCutoff_le_one`);
* `Cwin ≤ Cms` — the transfer of the root's window, through `window_of_le`, to
  a consumer that carries its OWN existential window constant.
* `Chom ≤ 2^{Cms}` — the `ε²` smallness gate;
* `(3/2) exp(Ccg/(1/7)) ≤ 2^{Cms}` — the coarse-graining gate;
* `Cshom ≤ 2^{Cms}` — the `l.shom.continuity` gauge gate;
* `15 ≤ 2^{Cms}` — the `15 c⋆⁻¹ ≤ E` of `p.homogenization.step` (
  `Frozen/Section3/HomogenizationStep.lean`).

The witness is explicit: the `max` of `4`, of `Chom`, of `Cwin`, of the
absorption exponent, and of the base-2 logarithm of the largest multiplicative
constant in play.  Only numerals already printed in the constraints occur. -/
theorem exists_parameterWeb_general (Chom Cwin Ccg Cshom : ℝ) :
    ∃ Cms : ℝ, 0 < Cms ∧ 1 ≤ Cms ∧ 4 ≤ Cms ∧
      Chom ≤ Cms ∧
      Cwin ≤ Cms ∧
      10 * Chom * Real.log 3 + 8 ≤ Cms ∧
      Chom ≤ (2 : ℝ) ^ Cms ∧
      (3 / 2 : ℝ) * Real.exp (Ccg / (1 / 7)) ≤ (2 : ℝ) ^ Cms ∧
      Cshom ≤ (2 : ℝ) ^ Cms ∧
      (15 : ℝ) ≤ (2 : ℝ) ^ Cms := by
  set K : ℝ := max 1 (max Chom
    (max ((3 / 2 : ℝ) * Real.exp (Ccg / (1 / 7))) (max Cshom 15))) with hKdef
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set Cms : ℝ := max 4 (max Chom (max Cwin
    (max (10 * Chom * Real.log 3 + 8) (Real.log K / Real.log 2)))) with hCmsdef
  have hfour : (4 : ℝ) ≤ Cms := le_max_left _ _
  have hChom : Chom ≤ Cms := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCwin : Cwin ≤ Cms :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have habs : 10 * Chom * Real.log 3 + 8 ≤ Cms :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hlog : Real.log K / Real.log 2 ≤ Cms :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hKle : K ≤ (2 : ℝ) ^ Cms := by
    have hmono : (2 : ℝ) ^ (Real.log K / Real.log 2) ≤ (2 : ℝ) ^ Cms :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
    rwa [two_rpow_log_div_log_two hKpos] at hmono
  refine ⟨Cms, by linarith, by linarith, hfour, hChom, hCwin, habs, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hKle
  · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right 1 _)) hKle
  · exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right 1 _)) hKle
  · exact le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right 1 _)) hKle

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
