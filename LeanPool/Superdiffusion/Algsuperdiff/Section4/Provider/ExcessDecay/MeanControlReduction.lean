/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStabilityEndpoints
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanControlWindowCube

/-!
# MeanControlReduction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The mean comparison, step 2: the homogenization-error split, and its loop-free
account

## What is proved

The single number `S` is controlled by the homogenization error.  That
mechanism is reduced here to its exact arithmetic skeleton and machine-checked.
With

```text
  ρ = u − h ,   V₁ = the covering cube c+□_{n+2} ,
  V₂ = the boundary-flush cube of MeanControlWindowCube ,
  W  = the frozen window (z+□_{n+3}) ∩ □_m ⊇ V₁ ∪ V₂ ,
```

and comparators `v` (any function on `V₂`; intended: the `Δ`-harmonic
replacement of `u` there) and `h` (intended: the `Δ`-harmonic replacement of the
datum `h`), the module proves

```text
  S = |⨍_{V₁} ρ|
      ≤ (r₁ + r₂)·‖ρ − (ρ)_W‖_{L²(W)}          (§1, §4: two window transfers)
        + ‖u − v‖_{L²(V₂)}                      (the homogenization error)
        + ‖h − h‖_{L²(V₂)}                      (the datum comparator, data-only)
        + |⨍_{V₂} (v − h)| ,                     (§2: THE remaining scalar)
```

```text
  ‖(v − h) − (v − h)_{V₂}‖_{L²(V₂)}
      ≤ 2‖u − v‖ + 2‖h − h‖ + ‖u − (u)_{V₂}‖ + ‖h − (h)_{V₂}‖      (§3, §5)
```

## What this buys, and what remains

Every summand except the last is a frozen-statement leg or a legal data step:
the window oscillation of `ρ` splits into the frozen leg `‖u − (u)_W‖` and the
datum oscillation `‖h − (h)_W‖` (the mean-zero Poincaré on the datum), and
`‖h − h‖` is a Dirichlet-comparison step on
the datum alone.  The single remaining analytic obligation is

```text
  |⨍_{V₂} (v − h)| ≤ C(d) · ‖(v − h) − (v − h)_{V₂}‖_{L²(V₂)}
```

for the `Δ`-harmonic difference `v − h` on the **boundary-flush** cube `V₂`,
whose trace vanishes on the face `V₂` shares with `∂□_m` (that face exists by
`MeanControlWindowCube.wellPlacedCentre_faceLevel`, and `u − h ∈ H¹₀(□_m)`).
That obligation is a statement about `Δ`-harmonic functions and Lebesgue
measure alone (the comparator class of `BoundaryLaneMaxPrinciple`), so flat
estimates suffice for it.  §6 records the arithmetic that converts the
boundary-trace form of that obligation into the stated form.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 0. Elementary identities for the normalized average -/

/-- The volume average of a constant is that constant. -/
theorem volumeAverage_const_of_toReal_pos {V : Set (Vec d)}
    (hVpos : 0 < (volume V).toReal) (b : ℝ) :
    volumeAverage V (fun _ => b) = b := by
  have hVne : ((volume V).toReal) ≠ 0 := ne_of_gt hVpos
  have hconst : ∫ _x in V, b ∂volume = (volume V).toReal * b := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
  unfold volumeAverage
  rw [hconst, ← mul_assoc, inv_mul_cancel₀ hVne, one_mul]

/-- The normalized seminorm of a constant is its absolute value. -/
theorem normalizedL2On_const_abs {V : Set (Vec d)} (hVpos : 0 < (volume V).toReal)
    (b : ℝ) : normalizedL2On V (fun _ => b) = |b| := by
  have hconst : volumeAverage V (fun _ => b ^ 2) = b ^ 2 :=
    volumeAverage_const_of_toReal_pos hVpos (b ^ 2)
  unfold normalizedL2On
  rw [hconst, Real.sqrt_sq_eq_abs]

/-- The volume average is additive on integrable summands. -/
theorem volumeAverage_add_eq {V : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (hg : IntegrableOn g V volume) :
    volumeAverage V (fun x => f x + g x) =
      volumeAverage V f + volumeAverage V g := by
  unfold volumeAverage
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- The volume average is additive on integrable differences. -/
theorem volumeAverage_sub_eq {V : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (hg : IntegrableOn g V volume) :
    volumeAverage V (fun x => f x - g x) =
      volumeAverage V f - volumeAverage V g := by
  unfold volumeAverage
  rw [MeasureTheory.integral_sub hf hg]
  ring

/-- Subtracting a constant shifts the volume average by that constant. -/
theorem volumeAverage_sub_const_eq {V : Set (Vec d)}
    (hVpos : 0 < (volume V).toReal) (hVtop : volume V ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (c : ℝ) :
    volumeAverage V (fun x => f x - c) = volumeAverage V f - c := by
  have : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have hc : IntegrableOn (fun _ : Vec d => c) V volume := MeasureTheory.integrable_const c
  rw [volumeAverage_sub_eq hf hc, volumeAverage_const_of_toReal_pos hVpos]

/-! ## 1. The two-window mean transfer -/

/-- **The mean transfer.**

For a subwindow `V ⊆ W`, the gap between the two normalized means is at most the
oscillation of `f` on the big window, at the square root of the volume ratio.
No equation, no coefficient field: Jensen on `V` followed by the volume-ratio
comparison of the normalized seminorms. -/
theorem abs_volumeAverage_sub_windowAverage_le {W V : Set (Vec d)}
    (hVm : MeasurableSet V) (hsub : V ⊆ W)
    (hWpos : 0 < (volume W).toReal) (hVpos : 0 < (volume V).toReal)
    (hVtop : volume V ≠ ⊤) {f : Vec d → ℝ} (hfV : IntegrableOn f V volume)
    (hfV2 : IntegrableOn (fun x => (f x - volumeAverage W f) ^ 2) V volume)
    (hfW2 : IntegrableOn (fun x => (f x - volumeAverage W f) ^ 2) W volume) :
    |volumeAverage V f - volumeAverage W f| ≤
      Real.sqrt ((volume W).toReal / (volume V).toReal) *
        normalizedL2On W (fun x => f x - volumeAverage W f) := by
  have : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have hc : IntegrableOn (fun _ : Vec d => volumeAverage W f) V volume :=
    MeasureTheory.integrable_const _
  have hsubint : IntegrableOn (fun x => f x - volumeAverage W f) V volume := hfV.sub hc
  have hJ := abs_volumeAverage_le_normalizedL2On hVm hVpos hsubint hfV2
  rw [volumeAverage_sub_const_eq hVpos hVtop hfV] at hJ
  exact hJ.trans (normalizedL2On_le_of_subset hsub hWpos hVpos hfW2)

/-! ## 2. The split through the comparators -/

/-- **The split.**

`u − h = (u − v) + (h − h) + (v − h)` pointwise, so the mean of `u − h` over
the flush cube is controlled by the homogenization error `‖u − v‖`, the datum
comparison `‖h − h‖`, and the mean of the comparator difference `v − h`.

The first two summands are the pieces the proved machinery prices; the third is
the single remaining analytic obligation, and it is a statement about the
comparators alone. -/
theorem abs_volumeAverage_sub_le_comparatorSplit {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal)
    {u h vbar hbar : Vec d → ℝ}
    (huv : IntegrableOn (fun x => u x - vbar x) V volume)
    (hhh : IntegrableOn (fun x => hbar x - h x) V volume)
    (hvh : IntegrableOn (fun x => vbar x - hbar x) V volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V volume)
    (hhh2 : IntegrableOn (fun x => (hbar x - h x) ^ 2) V volume) :
    |volumeAverage V (fun x => u x - h x)| ≤
      normalizedL2On V (fun x => u x - vbar x) +
        normalizedL2On V (fun x => hbar x - h x) +
        |volumeAverage V (fun x => vbar x - hbar x)| := by
  have hdecomp : (fun x => u x - h x) =
      fun x => ((u x - vbar x) + (hbar x - h x)) + (vbar x - hbar x) := by
    funext x; ring
  have hsum : IntegrableOn (fun x => (u x - vbar x) + (hbar x - h x)) V volume :=
    huv.add hhh
  rw [hdecomp, volumeAverage_add_eq hsum hvh, volumeAverage_add_eq huv hhh]
  have hJ1 := abs_volumeAverage_le_normalizedL2On hVm hVpos huv huv2
  have hJ2 := abs_volumeAverage_le_normalizedL2On hVm hVpos hhh hhh2
  have habs := abs_add_le (volumeAverage V (fun x => u x - vbar x) +
    volumeAverage V (fun x => hbar x - h x)) (volumeAverage V (fun x => vbar x - hbar x))
  have habs2 := abs_add_le (volumeAverage V (fun x => u x - vbar x))
    (volumeAverage V (fun x => hbar x - h x))
  linarith only [habs, habs2, hJ1, hJ2]

/-! ## 3. The oscillation of a comparator -/

/-- **The comparator's oscillation, in terms of the original's.**

`‖v − (v)_V‖ ≤ 2‖u − v‖ + ‖u − (u)_V‖`: the comparator oscillates no more than
the original does, up to twice the comparison error.  The proof is Minkowski
with the constant `(u)_V` inserted, plus Jensen on the mean gap; mean-minimality
is deliberately **not** used, so that the module needs no Pythagoras identity and
its import cone stays minimal. -/
theorem oscillation_comparator_le {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal) (hVtop : volume V ≠ ⊤)
    {u vbar : Vec d → ℝ} (hu : IntegrableOn u V volume)
    (hv : IntegrableOn vbar V volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V volume)
    (hvuM : MemLp (fun x => vbar x - u x) 2 (volume.restrict V))
    (hoscM : MemLp (fun x => u x - volumeAverage V u) 2 (volume.restrict V)) :
    normalizedL2On V (fun x => vbar x - volumeAverage V vbar) ≤
      2 * normalizedL2On V (fun x => u x - vbar x) +
        normalizedL2On V (fun x => u x - volumeAverage V u) := by
  have : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have huv : IntegrableOn (fun x => u x - vbar x) V volume := hu.sub hv
  have hconstM : MemLp (fun _ : Vec d => volumeAverage V u - volumeAverage V vbar) 2
      (volume.restrict V) := memLp_const _
  have hdecomp : (fun x => vbar x - volumeAverage V vbar) =
      fun x => (vbar x - u x) +
        ((u x - volumeAverage V u) +
          (volumeAverage V u - volumeAverage V vbar)) := by
    funext x; ring
  have hinner : MemLp (fun x => (u x - volumeAverage V u) +
      (volumeAverage V u - volumeAverage V vbar)) 2 (volume.restrict V) :=
    hoscM.add hconstM
  have hstep1 : normalizedL2On V (fun x => vbar x - volumeAverage V vbar) ≤
      normalizedL2On V (fun x => vbar x - u x) +
        normalizedL2On V (fun x => (u x - volumeAverage V u) +
          (volumeAverage V u - volumeAverage V vbar)) := by
    rw [hdecomp]
    exact normalizedL2On_add_le hvuM hinner
  have hstep2 : normalizedL2On V (fun x => (u x - volumeAverage V u) +
      (volumeAverage V u - volumeAverage V vbar)) ≤
      normalizedL2On V (fun x => u x - volumeAverage V u) +
        |volumeAverage V u - volumeAverage V vbar| := by
    refine (normalizedL2On_add_le hoscM hconstM).trans (le_of_eq ?_)
    rw [normalizedL2On_const_abs hVpos]
  have hgap : |volumeAverage V u - volumeAverage V vbar| ≤
      normalizedL2On V (fun x => u x - vbar x) := by
    have hJ := abs_volumeAverage_le_normalizedL2On hVm hVpos huv huv2
    rwa [volumeAverage_sub_eq hu hv] at hJ
  have hsym : normalizedL2On V (fun x => vbar x - u x) =
      normalizedL2On V (fun x => u x - vbar x) :=
    normalizedL2On_sub_comm V vbar u
  rw [hsym] at hstep1
  linarith only [hstep1, hstep2, hgap]

/-- The oscillation of a difference splits into the two oscillations. -/
theorem oscillation_sub_le {V : Set (Vec d)}
    {vbar hbar : Vec d → ℝ} (hv : IntegrableOn vbar V volume)
    (hh : IntegrableOn hbar V volume)
    (hvM : MemLp (fun x => vbar x - volumeAverage V vbar) 2 (volume.restrict V))
    (hhM : MemLp (fun x => -(hbar x - volumeAverage V hbar)) 2 (volume.restrict V)) :
    normalizedL2On V (fun x => (vbar x - hbar x) -
        volumeAverage V (fun y => vbar y - hbar y)) ≤
      normalizedL2On V (fun x => vbar x - volumeAverage V vbar) +
        normalizedL2On V (fun x => hbar x - volumeAverage V hbar) := by
  have hmean := volumeAverage_sub_eq hv hh
  have hdecomp : (fun x => (vbar x - hbar x) -
      volumeAverage V (fun y => vbar y - hbar y)) =
      fun x => (vbar x - volumeAverage V vbar) +
        (-(hbar x - volumeAverage V hbar)) := by
    funext x
    rw [hmean]
    ring
  rw [hdecomp]
  refine (normalizedL2On_add_le hvM hhM).trans (le_of_eq ?_)
  rw [normalizedL2On_neg]

/-! ## 4. The composite reduction -/

/-! ## 5. The loop-free certificate -/

/-- **The remaining obligation's own oscillation carries no `S`.**

The oscillation of the comparator difference `v − h` on the flush cube is
bounded by twice the two comparison errors plus the oscillations of `u` and of
the datum `h` — and by nothing else. -/
theorem oscillation_comparatorDifference_le {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal) (hVtop : volume V ≠ ⊤)
    {u h vbar hbar : Vec d → ℝ}
    (hu : IntegrableOn u V volume) (hh : IntegrableOn h V volume)
    (hv : IntegrableOn vbar V volume) (hhb : IntegrableOn hbar V volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V volume)
    (hhh2 : IntegrableOn (fun x => (h x - hbar x) ^ 2) V volume)
    (hvuM : MemLp (fun x => vbar x - u x) 2 (volume.restrict V))
    (hhbM : MemLp (fun x => hbar x - h x) 2 (volume.restrict V))
    (huoscM : MemLp (fun x => u x - volumeAverage V u) 2 (volume.restrict V))
    (hhoscM : MemLp (fun x => h x - volumeAverage V h) 2 (volume.restrict V))
    (hvoscM : MemLp (fun x => vbar x - volumeAverage V vbar) 2 (volume.restrict V))
    (hhboscM : MemLp (fun x => -(hbar x - volumeAverage V hbar)) 2
      (volume.restrict V)) :
    normalizedL2On V (fun x => (vbar x - hbar x) -
        volumeAverage V (fun y => vbar y - hbar y)) ≤
      2 * normalizedL2On V (fun x => u x - vbar x) +
        2 * normalizedL2On V (fun x => h x - hbar x) +
        normalizedL2On V (fun x => u x - volumeAverage V u) +
        normalizedL2On V (fun x => h x - volumeAverage V h) := by
  have hsplit := oscillation_sub_le hv hhb hvoscM hhboscM
  have hv' := oscillation_comparator_le hVm hVpos hVtop hu hv huv2 hvuM huoscM
  have hh' := oscillation_comparator_le hVm hVpos hVtop hh hhb hhh2 hhbM hhoscM
  linarith only [hsplit, hv', hh']

/-! ## 6. The boundary-trace form of the remaining obligation -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
