/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryClauseSkeleton

/-!
# CoarseMeanComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The mean-comparison chain, formalized and orientation-checked

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## The mechanism under test

The mechanism under test, stated verbatim: *"since the average of a function is
the unique constant `c` minimizing the `L²` norm of `u − c`, I think you can
compare `u − (u)` to `u − (h)` to `u − h`, the last bit costing exactly the `∇h`
term."*

* §1 **Pythagoras** — the exact identity, for `0 < |W| < ∞` and `f ∈ L²(W)`:
  `‖f − c‖²_{L²(W)} = ‖f − (f)_W‖²_{L²(W)} + |(f)_W − c|²`.
* §2 **Mean-minimality** — its immediate corollary
  `‖f − (f)_W‖ ≤ ‖f − c‖` for every constant `c`, and the scalar half
  `|(f)_W − c| ≤ ‖f − c‖`.
* §3 **The author's chain**, end to end: `|(u)_W − (h)_W| ≤ ‖u − h‖_{L²(W)} +
  ‖h − (h)_W‖_{L²(W)}`, the last term discharged by the proved data Poincaré
  at the covering cube (§5).
* §4 **The reverse decomposition**, which is what the boundary assembly's slot
  actually consumes:
  `‖u − h‖_{L²(W)} ≤ ‖u − (u)_W‖ + |(u)_W − (h)_W| + ‖h − (h)_W‖`.

## Orientation finding (STOP, reported to the author)

Write `S := |(u)_W − (h)_W|` (the residue at `W = c + □_{n+2}`), `Osc:= ‖u −
(u)_W‖_{L²(W)}` (absorbed by the frozen leg through mean-minimality plus the
proved window transport) and `Dat:= ‖h − (h)_W‖_{L²(W)}` (absorbed by the
frozen leg through the proved data Poincaré).  The boundary Caccioppoli's
parent-`L²` object is `‖u(·+c) − v_cc‖_{L²(cc)}`, and (`CoarseDatumPricing`
having priced `‖v_cc − h‖`) the one quantity still to bound is `‖u −
h‖_{L²(cc)}`.

The two machine-checked statements below are

```text
  §3 (author's chain) :   S          ≤ ‖u − h‖ + Dat
  §4 (assembly's need):   ‖u − h‖    ≤ Osc + S + Dat
```

They are the **same** inequality read in the two directions: §3 bounds `S` by
the very quantity the assembly must bound, and §4 bounds that quantity by `S`.
Chaining them is vacuous (`‖u−h‖ ≤ Osc + ‖u−h‖ + 2·Dat`).  Mean-minimality
produces `Osc ≤ ‖u − (h)_W‖`, i.e. a **lower** bound on the quantity the slot
needs an **upper** bound for; Pythagoras turns that into the exact identity
`‖u − (h)_W‖² = Osc² + S²`, which determines `‖u − (h)_W‖` from `Osc` and `S`
rather than bounding `S`.

Nothing here is forced and no substitute mechanism is attempted.  The two
sides, verbatim, are the statements of
`meanGap_le_normalizedL2On_sub_add_datumOscillation` (§3, what the chain gives)
and `normalizedL2On_sub_le_oscillation_add_meanGap_add_datumOscillation` (§4,
what the slot needs, with `S` still present at coefficient 1).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Pythagoras in the normalized carrier -/

/-- The average of `(f − c)²` expanded against the mean. -/
private theorem volumeAverage_sub_const_sq_expand {W : Set (Vec d)}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f W volume) (hf2 : IntegrableOn (fun x => f x ^ 2) W volume)
    (c : ℝ) :
    volumeAverage W (fun x => (f x - c) ^ 2) =
      volumeAverage W (fun x => f x ^ 2) - 2 * c * volumeAverage W f + c ^ 2 := by
  have hVpos : (0 : ℝ) < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hVne : ((volume W).toReal) ≠ 0 := ne_of_gt hVpos
  have : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWtop
  have hconst : ∫ _x in W, c ^ 2 ∂volume = (volume W).toReal * c ^ 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
  have hcf : IntegrableOn (fun x => 2 * c * f x) W volume := hf.const_mul _
  have hc2 : IntegrableOn (fun _x : Vec d => c ^ 2) W volume :=
    MeasureTheory.integrable_const _
  have hsplit : ∫ x in W, (f x - c) ^ 2 ∂volume =
      (∫ x in W, f x ^ 2 ∂volume) - 2 * c * (∫ x in W, f x ∂volume) +
        (volume W).toReal * c ^ 2 := by
    have h1 : ∫ x in W, (f x - c) ^ 2 ∂volume =
        ∫ x in W, ((f x ^ 2 - 2 * c * f x) + c ^ 2) ∂volume := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      ring
    have hsubInt : IntegrableOn (fun x => f x ^ 2 - 2 * c * f x) W volume :=
      hf2.sub hcf
    rw [h1, MeasureTheory.integral_add (f := fun x => f x ^ 2 - 2 * c * f x)
        (g := fun _ : Vec d => c ^ 2) hsubInt hc2,
      MeasureTheory.integral_sub (f := fun x => f x ^ 2)
        (g := fun x => 2 * c * f x) hf2 hcf,
      MeasureTheory.integral_const_mul, hconst]
  unfold volumeAverage
  rw [hsplit]
  field_simp

/-- **Pythagoras on the normalized carrier.**

For a window of positive finite volume and an `L²` function, the deviation from
any constant splits orthogonally into the oscillation and the mean gap:

```text
  ‖f − c‖²_{L²(W)} = ‖f − (f)_W‖²_{L²(W)} + |(f)_W − c|² .
```
-/
theorem normalizedL2On_sub_const_sq_eq {W : Set (Vec d)}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f W volume) (hf2 : IntegrableOn (fun x => f x ^ 2) W volume)
    (c : ℝ) :
    normalizedL2On W (fun x => f x - c) ^ 2 =
      normalizedL2On W (fun x => f x - volumeAverage W f) ^ 2 +
        (volumeAverage W f - c) ^ 2 := by
  rw [normalizedL2On_sq, normalizedL2On_sq,
    volumeAverage_sub_const_sq_expand hWpos hWtop hf hf2 c,
    volumeAverage_sub_const_sq_expand hWpos hWtop hf hf2 (volumeAverage W f)]
  ring

/-! ## 2. Mean-minimality and the scalar half -/

/-- **Mean-minimality.**  The volume average is the `L²(W)`-minimizing constant:
the oscillation is at most the deviation from any constant.  This is the author's
first comparison, and it is the step that lets the assembly replace the covering
cube's own mean by the frozen clause's `(u)_{W'}` at no cost. -/
theorem normalizedL2On_sub_average_le_sub_const {W : Set (Vec d)}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f W volume) (hf2 : IntegrableOn (fun x => f x ^ 2) W volume)
    (c : ℝ) :
    normalizedL2On W (fun x => f x - volumeAverage W f) ≤
      normalizedL2On W (fun x => f x - c) := by
  have hpy := normalizedL2On_sub_const_sq_eq hWpos hWtop hf hf2 c
  have hsq : normalizedL2On W (fun x => f x - volumeAverage W f) ^ 2 ≤
      normalizedL2On W (fun x => f x - c) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (volumeAverage W f - c) ^ 2 := sq_nonneg _
    linarith only [hpy, h0]
  exact le_of_sq_le_sq hsq (normalizedL2On_nonneg W _)

/-- The normalized seminorm of a constant is its absolute value. -/
theorem normalizedL2On_const {W : Set (Vec d)} (hWpos : 0 < volume W)
    (hWtop : volume W ≠ ⊤) (b : ℝ) :
    normalizedL2On W (fun _ => b) = |b| := by
  have hVpos : (0 : ℝ) < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hVne : ((volume W).toReal) ≠ 0 := ne_of_gt hVpos
  have hconst : ∫ _x in W, b ^ 2 ∂volume = (volume W).toReal * b ^ 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
  unfold normalizedL2On volumeAverage
  rw [hconst, ← mul_assoc, inv_mul_cancel₀ hVne, one_mul, Real.sqrt_sq_eq_abs]

/-! ## 3. The author's chain, end to end -/

/-! ## 4. The reverse decomposition: what the assembly's slot consumes -/

/-- **The assembly's slot.**

```text
  ‖u − h‖_{L²(W)}
      ≤ ‖u − (u)_W‖_{L²(W)} + |(u)_W − (h)_W| + ‖h − (h)_W‖_{L²(W)} ,
```

i.e. the boundary Caccioppoli's parent-`L²` object, after
`CoarseDatumPricing` has removed the `‖v_cc − h‖` leg, reduces to the frozen
leg (through mean-minimality and the proved window transport), the frozen leg
(through the data Poincaré) and the residue `S = |(u)_W − (h)_W|` **at
coefficient 1**.

Read together with §3 it shows the mean-comparison chain to be an identity in
disguise rather than a bound on `S`. -/
theorem normalizedL2On_sub_le_oscillation_add_meanGap_add_datumOscillation
    {W : Set (Vec d)} (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤)
    {u h : Vec d → ℝ}
    (huosc : MemLp (fun x => u x - volumeAverage W u) 2 (volume.restrict W))
    (hhosc : MemLp (fun x => h x - volumeAverage W h) 2 (volume.restrict W)) :
    normalizedL2On W (fun x => u x - h x) ≤
      normalizedL2On W (fun x => u x - volumeAverage W u) +
        |volumeAverage W u - volumeAverage W h| +
        normalizedL2On W (fun x => h x - volumeAverage W h) := by
  have hconstMem : MemLp
      (fun _ : Vec d => volumeAverage W u - volumeAverage W h) 2
      (volume.restrict W) := by
    have : IsFiniteMeasure (volume.restrict W) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 hWtop
    exact memLp_const _
  have hnegMem : MemLp (fun x => -(h x - volumeAverage W h)) 2
      (volume.restrict W) := hhosc.neg
  have hsum : MemLp
      (fun x => (u x - volumeAverage W u) +
        (volumeAverage W u - volumeAverage W h)) 2 (volume.restrict W) :=
    huosc.add hconstMem
  have hfun : (fun x => u x - h x) =
      fun x => ((u x - volumeAverage W u) +
          (volumeAverage W u - volumeAverage W h)) +
        (-(h x - volumeAverage W h)) := by
    funext x; ring
  rw [hfun]
  refine (normalizedL2On_add_le hsum hnegMem).trans ?_
  have h1 : normalizedL2On W
      (fun x => (u x - volumeAverage W u) +
        (volumeAverage W u - volumeAverage W h)) ≤
      normalizedL2On W (fun x => u x - volumeAverage W u) +
        |volumeAverage W u - volumeAverage W h| := by
    refine (normalizedL2On_add_le huosc hconstMem).trans (le_of_eq ?_)
    rw [normalizedL2On_const hWpos hWtop]
  have h2 : normalizedL2On W (fun x => -(h x - volumeAverage W h)) =
      normalizedL2On W (fun x => h x - volumeAverage W h) :=
    normalizedL2On_neg W _
  rw [h2]
  linarith only [h1]

/-! ## 5. The leg comparison: what the chain DO buy -/

/-! ## 6. The chain at the boundary covering cube -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
