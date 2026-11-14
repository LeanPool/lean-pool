/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ConstantDatumCoreEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorComposed

/-!
# GeneralClauseInteriorComposed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The general clause at frontier-empty windows, composed at `s^{-7}`

The payoff of the constant-datum route: **one** almost-sure statement, entered
at the frozen theorem's own binders and concluded in the frozen theorem's own
carriers,

```text
  1_𝒢 ‖u − v‖_{L²(x+□_n)}
      ≤ C ( s^{-4} 𝓔_{s/8}(z+□_{n+2}; ã_{L,n+2}, σ_{n+2}) ‖u − (u)_W‖_{L²(W)}
          + s^{-7} σ_{n+2}^{-1} 3^{(1+s)n} [g]_{H^s(W)} ) ,
      W = (z + □_{n+2}) ∩ □_m ,
```

on the frontier-empty gate.  This is
`InteriorComposed.exists_interiorClause_honest` **with the force leg at the
frozen general clause's own printed exponent `s^{-7}`** in place of the proved
`s^{-19/2}`: the only change is the energy input,
the sharpened interior energy estimate (force envelope
`s^{-6}`) in place of `InteriorClause.ae_interiorCaccioppoliEnergy_anchorWindow`
(force envelope `s^{-11}`).  Everything else — the `x`-frame chain, the
coarse-graining slot, the flux prefactor, the good-event caps, the window move
— is the proved chain's, unchanged.

Exponent bookkeeping of the force leg: `√(s^{-6}) = s^{-3}` on the energy leg,
composed with the flux prefactor `s^{-4}`, gives `s^{-7}`; the coarse-graining
force term contributes `s^{-6}` and the interior correction `s^{-1/2}`, both
dominated by `s^{-7}` on `(0,1]`.  The bound is therefore **exactly** at the
frozen general clause's budget, with no `γ`-move anywhere.

## Deviations from the printed statement

* the coarse-graining slot index `r = s/3` (`InteriorEllipticitySlot`;).
* the `σ` index: the force leg carries `σ_{n+2}^{-1}`; the frozen statement
  carries `σ_n^{-1}`, and `SigmaBarIndex.exists_inv_sigmaBar_add_two_le`
  converts at the factor `4` inside the anchor's own regime.
* no `γ`-move is made anywhere.

## References

* ABK26, `l.harmonic.approximation.good.scales`;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The sharpened arithmetic helpers -/

/-- The two `s`-powers of the composition add: `s^{-4} · s^{-3} = s^{-7}`. -/
theorem rpow_s_four_mul_three {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(4 : ℝ)) * Real.rpow s (-(3 : ℝ)) = Real.rpow s (-(7 : ℝ)) := by
  change s ^ (-(4 : ℝ)) * s ^ (-(3 : ℝ)) = s ^ (-(7 : ℝ))
  rw [← Real.rpow_add hs]
  congr 1
  ring

/-- On `(0,1]` every `s`-power above `−7` is dominated by `s^{-7}`. -/
theorem rpow_le_rpow_neg_seven {s a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : -(7 : ℝ) ≤ a) : Real.rpow s a ≤ Real.rpow s (-(7 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 ha

end

end Algsuperdiff.Section4.Provider.ExcessDecay
