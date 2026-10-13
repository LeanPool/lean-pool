/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStability

/-!
# QuasiMonotone

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Excess quasi-monotonicity (`hmono`) on the cube-sandwich family

`l.iteration.lemma` never displays the inequality

```
E_k ≤ κ · E_{k+1}
```

but it uses it twice: once in Step 2, where the shifted excess sum is
reabsorbed across its `h` end terms (`e.sum.excess.bound`, whose graph edge
records "the reabsorption crosses the `h` end-terms of the shifted sum using
the per-scale quasi-monotonicity `E_k ≤ κ E_{k+1}`, which is a consequence of
the definition together with the window sandwich"), and once implicitly inside
the printed reabsorption factor `3^{(d+2)h}`, which is `κ^h`.  It is the
`hmono` hypothesis of the proved iteration engine
(`IterationLemma.combinedBound`, `IterationLemma.iterationSlopeBound`).

This module proves it, from geometry alone, on the family the lemma actually assumes.

## The mechanism

The competitor set is the *same* set of affine functions for both windows, so the domain comparison
is competitor-by-competitor: for `W' ⊆ W` and every affine `ℓ`,

```
‖u − ℓ‖_{L²(W')} ≤ (|W|/|W'|)^{1/2} ‖u − ℓ‖_{L²(W)}     (Support.normalizedL2On_le_of_subset)
```

and the left-hand infimum is below every competitor
(`Support.affineExcessRaw_le_affineDistOn`), which gives
`affineExcessRaw W' u ≤ (|W|/|W'|)^{1/2} affineExcessRaw W u`.  Restoring the `|W|^{−1/d}`
normalizer of `Support.affineExcess` turns the exponent `1/2` into `1/d + 1/2`:

```
E(u, W') ≤ (|W|/|W'|)^{1/d + 1/2} E(u, W) .
```

## The constant actually obtained

On the sandwich `x + □_{k−2} ⊆ U_k ⊆ y + □_k` the one-scale ratio is
`|U_{k+1}|/|U_k| ≤ 3^{(k+1)d}/3^{(k−2)d} = 3^{3d}`, so the derived constant is
*exactly* the one already proved for slope stability,

```
κ = volumeRatioConstTriadic d = (3^{3d})^{1/d + 1/2} = 3^{3 + 3d/2} ,
```

with `1 ≤ κ` available as `one_le_volumeRatioConstTriadic` — so the engine's `hκ` slot is
discharged by the same object.  Nothing here is assumed: the ratio bound is
proved from the two inclusions.

The route above gives `3 + 3d/2` (the `3` is `3d · (1/d)`, the `3d/2` is `3d ·
(1/2)`; `1 + 3d/2` would need the ratio `3^d` for the first summand and
`3^{3d}` for the second, so it cannot come from one ratio).  Since `3 + 3d/2 ≤
d + 2` fails for **every** `d ≥ 1`, the printed `3^{(d+2)h}` is too small at
the derived `κ` in every dimension, not only for `d ≥ 3`.  This module does not
change any statement: `κ` is an explicit `def` here and the caveat is's to
adjust.

## References

* ABK26, `e.excess.def`; `e.sum.excess.bound`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec axisCube openCubeSet TriadicCube cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### `MemLp` transfer across the nesting

The iteration engine reads `u` on every window of the family, while a caller typically knows
`u ∈ L²` on the largest one.  Restriction is monotone in the set, so `MemLp` transfers downwards;
this is the whole content. -/

/-- **`MemLp` restricts to a subwindow.**  `Measure.restrict_mono` plus `MemLp.mono_measure`. -/
theorem memLp_restrict_of_subset {W W' : Set (Vec d)} {f : Vec d → ℝ} {p : ENNReal}
    (hsub : W' ⊆ W) (hf : MemLp f p (volume.restrict W)) :
    MemLp f p (volume.restrict W') :=
  hf.mono_measure (Measure.restrict_mono hsub le_rfl)

/-! ### Domain comparison for the excess -/

/-- **Domain comparison for the unnormalized excess.**  For `W' ⊆ W` of positive volume, with every
affine deviation of `u` square-integrable on `W`,

`min_ℓ ‖u − ℓ‖_{L²(W')} ≤ (|W|/|W'|)^{1/2} · min_ℓ ‖u − ℓ‖_{L²(W)}`.

Proved competitor-by-competitor: the seminorm comparison holds for each affine `ℓ`, and the
left-hand infimum is below every competitor. -/
theorem affineExcessRaw_le_of_subset {W W' : Set (Vec d)} {u : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W) :
    affineExcessRaw W' u
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineExcessRaw W u := by
  have hr : 0 < Real.sqrt ((volume W).toReal / (volume W').toReal) :=
    Real.sqrt_pos.2 (div_pos hW hW')
  rw [← div_le_iff₀' hr]
  refine le_csInf (affineDistSet_nonempty W u) ?_
  rintro y ⟨q, rfl⟩
  rw [div_le_iff₀ hr]
  have hcmp : affineDistOn W' u q.1 q.2
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineDistOn W u q.1 q.2 :=
    normalizedL2On_le_of_subset hsub hW hW' (hint q.1 q.2)
  calc affineExcessRaw W' u ≤ affineDistOn W' u q.1 q.2 :=
        affineExcessRaw_le_affineDistOn W' u q.1 q.2
    _ ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineDistOn W u q.1 q.2 := hcmp
    _ = affineDistOn W u q.1 q.2
          * Real.sqrt ((volume W).toReal / (volume W').toReal) := by ring

/-- The `rpow` bookkeeping of the normalizer restoration, over abstract positive reals: no numeric
tactic ever sees a `Real.rpow` atom. -/
private theorem rpow_ratio_identity {A B e : ℝ} (hA : 0 < A) (hB : 0 < B) :
    B ^ (-e) * Real.sqrt (A / B) = (A / B) ^ (e + 1 / 2) * A ^ (-e) := by
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  have hAe : A ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA e)
  have hBe : B ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hB e)
  have hhalf : (A / B) ^ ((1 : ℝ) / 2) = Real.sqrt (A / B) := (Real.sqrt_eq_rpow (A / B)).symm
  have hsplit : (A / B) ^ (e + 1 / 2) = A ^ e / B ^ e * Real.sqrt (A / B) := by
    rw [Real.rpow_add hAB, Real.div_rpow hA.le hB.le e, hhalf]
  rw [hsplit, Real.rpow_neg hA.le, Real.rpow_neg hB.le]
  field_simp

/-- **Domain comparison for the excess `E(u,W) = |W|^{−1/d} min_ℓ ‖u − ℓ‖_{L²(W)}`.**
For `W' ⊆ W` of positive volume,

`E(u, W') ≤ (|W|/|W'|)^{1/d + 1/2} · E(u, W)`,

the exponent splitting as `1/d` (restoring the two `|·|^{−1/d}` normalizers) plus `1/2` (the
seminorm volume ratio). -/
theorem affineExcess_le_of_subset {W W' : Set (Vec d)} {u : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W) :
    affineExcess W' u
      ≤ ((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * affineExcess W u := by
  have hraw := affineExcessRaw_le_of_subset hsub hW hW' hint
  have hBe : (0 : ℝ) ≤ ((volume W').toReal) ^ (-(d : ℝ)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hraw hBe
  have hid := rpow_ratio_identity (e := (d : ℝ)⁻¹) hW hW'
  calc affineExcess W' u
      = ((volume W').toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W' u := rfl
    _ ≤ ((volume W').toReal) ^ (-(d : ℝ)⁻¹)
          * (Real.sqrt ((volume W).toReal / (volume W').toReal) * affineExcessRaw W u) := hstep
    _ = (((volume W').toReal) ^ (-(d : ℝ)⁻¹)
          * Real.sqrt ((volume W).toReal / (volume W').toReal)) * affineExcessRaw W u := by ring
    _ = (((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
          * ((volume W).toReal) ^ (-(d : ℝ)⁻¹)) * affineExcessRaw W u := by rw [hid]
    _ = ((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * affineExcess W u := by
        rw [affineExcess]
        ring

/-! ### The `hmono` producer -/

/-- **Excess quasi-monotonicity on an abstract nested family**, in the exact shape
the proved iteration engine consumes as `hmono`
(`IterationLemma.combinedBound`, `IterationLemma.iterationSlopeBound`, at `E:=
fun k => affineExcess (U k) u`):

`∀ k, E k ≤ κ * E (k + 1)`.

`hratio` is the only quantitative input; the cube-sandwich instance below *proves* it. -/
theorem affineExcess_quasiMonotone_of_nested (U : ℤ → Set (Vec d)) (u : Vec d → ℝ) {κ : ℝ}
    (hnest : ∀ k : ℤ, U k ⊆ U (k + 1)) (hvol : ∀ k : ℤ, 0 < (volume (U k)).toReal)
    (hint : ∀ (k : ℤ) (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) (U k))
    (hratio : ∀ k : ℤ,
      ((volume (U (k + 1))).toReal / (volume (U k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) ≤ κ) :
    ∀ k : ℤ, affineExcess (U k) u ≤ κ * affineExcess (U (k + 1)) u := by
  intro k
  have hcmp := affineExcess_le_of_subset (hnest k) (hvol (k + 1)) (hvol k) (hint (k + 1))
  exact hcmp.trans
    (mul_le_mul_of_nonneg_right (hratio k) (affineExcess_nonneg (U (k + 1)) u))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
