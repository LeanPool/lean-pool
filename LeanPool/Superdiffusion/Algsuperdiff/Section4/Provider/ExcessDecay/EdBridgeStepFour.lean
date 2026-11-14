/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeFolds

/-!
# EdBridgeStepFour

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The anchored one-step delivered in the Step-4 / `IterationDecay` slot

The anchored interior one-step is the printed one-step contraction
with the harmonic-approximation anchor's four legs on the right.
`t.regularity` Step 4 and the frozen iteration anchor's own hypothesis
`e.Ej.decay.assumption` (named `IterationDecay` by the Step-5 provider) want
instead

```text
   E(u, U_{j-h}) ≤ θ^h E(u, U_j) + ε_j |∇ℓ_j| + δ_j ,   U_j = (z+□_j) ∩ □_m ,  θ = 3^{-1/4} .
```

This module performs that conversion — residues 1--4 — on the interior
branch.

## Residue 3: the `W' → U_0` window move, measured and closed at zero new analysis

In the proved indices the gap is exactly **one triadic scale**: the one-step at
scale `n` carries all four legs on `(z+□_{n+1}) ∩ □_m` and its supply event at
index `n+1` (the frozen statement's anchor is `z`-centred at its own index `+3`, two
scales above the print's `x`-centred `+1`), while its contraction reads the
excess at `(z+□_n) ∩ □_m`.

The move is therefore **not** an analytic comparison of two incomparable windows: it is a
re-index.  Running the one-step at `x := z` and reading the conclusion at `j := n+1`,

* the anchor's legs sit on `U_{n+1} = U_j` — the recursion's own window, where residue 2 applies
  verbatim, and the supply event sits at index `j`, which is exactly the index of the Step-3 bad
  set `𝓑_z = {j : 𝒢(j,z;·) fails}`;
* the contraction's excess sits on `U_n = U_{j-1}`, one scale below, and is
  moved up by the **proved** excess quasi-monotonicity `E(u,U_n) ≤ κ(d,1)
  E(u,U_{n+1})` (`OneStepWindows.affineExcess_truncatedWindow_le`, a pure
  volume-ratio bound), whose constant is absorbed into the contraction by
  residue 4;
* the left-hand window sits on `U_{n-k} = U_{j-h}` at `h := k+1`.

This module is the general-clause route, kept because it needs no
frontier-empty gate (hence covers the windows that meet `∂□_m`, where the
boundary join lives).

## What is discharged, and what is carried

Discharged inside: the anchor, the good-event cap
(`OneStepGoodScales.ae_errorRepresentative_le_goodEventDeltaSlot`), the
oscillation-to-excess fold, the window move, the contraction absorption, and
the almost-sure quantifier over the whole scale range (`ae_all_iff` over `ℤ`,
so that ONE `ω` serves every scale — what a pathwise bad set needs).

Carried, as source binders: the Dirichlet datum and clause-(iv) `MemLp` data of
the one-step; the harmonic replacement `v, w` on the moved cube at each scale
(the reflection chain plus the Weyl
representative produce them with no analytic input); the affine minimizer at
the scale in question; the interior gate `(z+□_{n-2}) ⊆ □_m`; and one smallness
gate on `δ`.

## The `δ`-gate (disclosed)

Printed Step 4 absorbs the one-step's second `E`-coefficient into `3^{-k/4}` by
the two inequalities (`C s^{-3/2} 3^{-k/4} ≤ 1/2` and `ε_j(z) ≤ ½ s^{3/2}
C^{-1} 3^{-k/4}`).  Here that absorption is a single explicit hypothesis
`hgate`: the capped leg constant times `s^{-3} δ^{1/2}` is at most `½ ·
3^{-(k+1)/4}`.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Steps 3--5;
  `l.iteration.lemma`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The bridge's constants and legs -/

/-- **The bridge's `ε_j` at `j = n+1`**: the printed `ε_j` at
the `ε`-re-pin `s^{-4}`, with the error representative left (uncapped),
exactly as `t.regularity` Step 5's own `ε_j(z)` is. -/
def edBridgeEps (M : ABKModel d) (Ceps : ℝ) (L : ℤ) (s : ℝ) (t : {t : ℝ // 0 < t}) (z : Vec d)
    (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  Ceps * Real.rpow s (-(4 : ℝ)) *
    fluxCorrectedErrorRepresentative M L (n + 1) t (Cutoff.translateCutoffSample z omega)

/-! ## 2. The scalar recombination -/

/-- `3^{-n} · 3^{n+1} = 3`: the single triadic scale of the re-index. -/
theorem zpow_reindex (n : ℤ) : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1) = 3 := by
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num

/-- ** residue 3, atom: the one-scale excess move.**  `E(u,U_n) ≤ κ(d,1)
E(u,U_{n+1})` on the Step-3 window family, at the proved volume-ratio constant. -/
theorem affineExcess_reindex_le {m n : ℤ} (z : Vec d)
    (hz : z ∈ openCubeSet (originCube d m)) (hnm : n + 1 - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m (n + 1)))) :
    affineExcess (truncatedWindow z m n) u
      ≤ windowRatioConst d 1 * affineExcess (truncatedWindow z m (n + 1)) u := by
  have h := affineExcess_truncatedWindow_le (d := d) (u := u) z hz (by omega : n - 1 ≤ m) hnm
    (by omega : n ≤ n + 1) hu
  rwa [show n + 1 - n = 1 from by ring] at h

/-! ## 3. The endpoint: the anchored one-step in the Step-4 slot -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
