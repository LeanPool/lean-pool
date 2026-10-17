/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGammaFold

/-!
# GammaTenEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The pathwise envelope of a monotone family with a uniform fourth moment

ABK26, Step 2 of `l.approximate.recurrence.formula`.

## The obstruction this module removes

`LocalizationFluctuationPerCube.perCube_localizationFluctuation_le` consumes the
Besov envelope of `bfF_z` in the **pathwise** form

```
  hpos1 hpos2 :  forall N, [ gauged bfF_z ]_{B^s_{2,2}, <= N}  <=  Bg
```

--- a single real `Bg`, valid at *every* depth cutoff, at the sample point where
the per-cube bound is being read.  The oscillation input of Step 2 is
**annealed** instead: the pathwise fold cannot be instantiated at the
recurrence's own data, and what is available is a depth fold in the mean,

```
  E[ [ u ]_{<= N}^4 ]  <=  4 (A 3^{-B})^4      (uniformly in N).
```

The two are reconciled here.  The finite-depth positive `q = 2` seminorms are
**monotone in the depth cutoff** (their square is a sum of nonnegative terms over
`range (N+1)`), so the fourth powers form a monotone family; monotone convergence
turns a bound on `E[u_N^4]` that is uniform in `N` into the *same* bound on the
fourth moment of the pointwise envelope, and in particular the envelope is finite
almost surely.  That envelope is the pathwise `Bg` the per-cube bound asks for,
and its fourth moment is the oscillation leg the annealed Hoelder fold consumes.

## What is proved

* `envelopeSup` --- the pointwise envelope: the supremum of the *fourth
  powers*, taken (so that it is total and measurable with no boundedness
  hypothesis) and read back in `ℝ` through the fourth root.  Taking the
  supremum after the fourth power avoids any commutation of `iSup` with `^ 4`.
* `envelopeSup_nonneg`, `le_envelopeSup_of_ne_top`, `pow_envelopeSup` --- the
  three elementary facts.
* `measurable_envelopeSup` --- measurability.

The device built on them is
`Closure.GammaTenEnvelopeInputGrid.exists_grid_pathwise_envelope_of_monotone`:
a monotone, measurable, nonnegative family whose fourth moments are bounded by
a single `C` uniformly in the depth cutoff admits a measurable pathwise
envelope `B` with

```
  (a.e. w)  forall N, u N w <= B w ,        0 <= B ,        E[B^4] <= C ,
```

run simultaneously at every cell of the mesh.  The almost-everywhere quantifier
is the exact strength the consumer needs: the per-cube bound is read inside a
Bochner integral, where `integral_mono_ae` applies.

## Binders

Nonnegativity of the family, and finiteness of the supremum of its fourth
powers wherever a member is to be dominated.  No smallness gate, no geometry,
nothing about the corrector or the coefficient field.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

section Envelope

variable {Omega : Type*}

/-- **The pointwise envelope of a family of nonnegative reals, made total.**

The supremum of the fourth powers is taken, so that it exists with no
boundedness hypothesis, and the fourth root is taken after reading it back in
`ℝ`. -/
def envelopeSup (u : ℕ → Omega → ℝ) (w : Omega) : ℝ :=
  ((⨆ N, ENNReal.ofReal (u N w ^ (4 : ℕ))).toReal) ^ ((4 : ℝ)⁻¹)

theorem envelopeSup_nonneg (u : ℕ → Omega → ℝ) (w : Omega) : 0 ≤ envelopeSup u w :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- The fourth power of the envelope is the supremum itself, read in `ℝ`. -/
theorem pow_envelopeSup (u : ℕ → Omega → ℝ) (w : Omega) :
    envelopeSup u w ^ (4 : ℕ) = (⨆ N, ENNReal.ofReal (u N w ^ (4 : ℕ))).toReal := by
  unfold envelopeSup
  rw [← Real.rpow_natCast (((⨆ N, ENNReal.ofReal (u N w ^ (4 : ℕ))).toReal) ^ ((4 : ℝ)⁻¹)) 4,
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

/-- Every member of the family is below the envelope, wherever the supremum is
finite. -/
theorem le_envelopeSup_of_ne_top {u : ℕ → Omega → ℝ} {w : Omega}
    (hw : (⨆ N, ENNReal.ofReal (u N w ^ (4 : ℕ))) ≠ ⊤) (hnn : ∀ N, 0 ≤ u N w) (N : ℕ) :
    u N w ≤ envelopeSup u w := by
  have hle : ENNReal.ofReal (u N w ^ (4 : ℕ)) ≤
      ⨆ M, ENNReal.ofReal (u M w ^ (4 : ℕ)) :=
    le_iSup (fun M => ENNReal.ofReal (u M w ^ (4 : ℕ))) N
  have hmono := ENNReal.toReal_mono hw hle
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ u N w ^ (4 : ℕ))] at hmono
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ u N w ^ (4 : ℕ)) hmono
    (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
  have hid : (u N w ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹) = u N w := by
    rw [← Real.rpow_natCast (u N w) 4, ← Real.rpow_mul (hnn N)]
    norm_num
  rwa [hid] at hroot

theorem measurable_envelopeSup [MeasurableSpace Omega] {u : ℕ → Omega → ℝ}
    (hu : ∀ N, Measurable (u N)) : Measurable (envelopeSup u) := by
  unfold envelopeSup
  exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)).measurable.comp
    (Measurable.iSup fun N =>
      ENNReal.measurable_ofReal.comp ((hu N).pow_const 4)).ennreal_toReal

variable [MeasurableSpace Omega]

end Envelope

section Besov

variable {Omega : Type*} [MeasurableSpace Omega]

end Besov

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
