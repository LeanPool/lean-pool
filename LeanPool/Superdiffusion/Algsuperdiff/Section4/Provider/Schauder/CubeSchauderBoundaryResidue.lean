/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderResidue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderBoundaryZeroTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflection
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderComposeBoundary

/-!
# CubeSchauderBoundaryResidue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the harmonic competitor on the **reflected** window

`CubeSchauderResidue.exists_harmonicCompetitor_residue` produces the harmonic
competitor of the forced equation on the *truncated* window `(x+□_n) ∩ □_m`.
The boundary branch's Lipschitz atom
(`CubeSchauderBoundaryTwin.exists_gradientLipschitz_boundary`) instead asks for a
competitor that is classically harmonic on the **partially reflected** window
`reflectedWindow x m (n-2)` — the odd double of the truncated window across
every met face of `∂□_m`.  This module produces it, for the **zero-datum** cube
problem, and prices its residue.

The chain, on the window `W = (x + □_{n-2}) ∩ □_m`:

1. *freezing at the window's own scale*
   (`CubeSchauderResidue.exists_frozenHarmonicReplacement_truncatedWindow`, at
   the base point `x` and the constant `c = G(x)`): a corrector `w ∈ H¹₀(W)`
   with `u - w` weakly harmonic on `W` and
   `Σᵢ ‖∂ᵢw‖_{L²(W)} ≤ d KG √(3^{n-2}|W|)`;
2. *the zero-trace slot* (`CubeSchauderBoundaryZeroTrace`): `u ∈ H¹₀(□_m)` and
   `w ∈ H¹₀(W)` give the face-only localized zero trace of `u - w` on `W`
   against `reflectedWindow x m (n-2)` — no extra hypothesis;
3. *the odd reflection*
   (`ExcessDecay.exists_h1_oddReflection_reflectedWindow`, any met
   configuration — interior, face, edge or corner): a weakly harmonic
   `H¹(reflectedWindow x m (n-2))` extension pinned to `u - w` on `W`;
4. *Weyl on the doubled window*
   (`ExcessDecay.Schauder.exists_classicalCompetitor_reflectedWindow`): a
   classically harmonic representative `V`, so that `u - V = w` almost
   everywhere on `W`;
5. *the Dirichlet Poincaré* (`CubeSchauderPoincare`, at the inscribing cube
   `x + □_{n-2}`), exactly as in the interior chain.

Because the freezing runs at the *replacement* scale `n-2` rather than at `n`,
the interior chain's window transfer `U_0 → U_2` is not needed and the residue
constant loses the `√((3⁴)^d)` volume-ratio factor: the boundary residue is
**smaller** than the interior one, at
`boundaryResidueConst d = C_Poincaré(d) · d` (the honest value carries a further
factor `1/27`, discarded here).

## What this module does *not* do

It supplies the **competitor** of the boundary one step, not the one step.  The
step that remains open is the fold of the competitor's excess on the doubled
window, `E(V, reflectedWindow x m (n-2))`, back into `E(u, (x+□_n) ∩ □_m)`: on
the interior branch that is one triangle inequality
(`affineExcess_sub_le_truncatedWindow`), but on the doubled window `u` is not
defined on the far side, and the affine competitor must be replaced by its odd
part before the far-side leg can be folded back.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`), the
  harmonic-approximation display `e.harmapprox.Sch.onealpha`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant -/

/-- The residue constant of the boundary branch: `C_Poincaré(d) · d`.  No
volume-ratio factor, because the freezing runs at the replacement scale. -/
def boundaryResidueConst (d : ℕ) : ℝ := schauderDirichletPoincareConst d * (d : ℝ)

theorem boundaryResidueConst_nonneg (d : ℕ) : 0 ≤ boundaryResidueConst d :=
  mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d)

/-! ## 2. The competitor and its residue -/

end

end Algsuperdiff.Section4.Provider.Schauder
