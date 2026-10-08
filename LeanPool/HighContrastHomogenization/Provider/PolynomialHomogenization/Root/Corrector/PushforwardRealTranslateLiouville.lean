/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardH1sLocTranslate
public import LeanPool.HighContrastHomogenization.Provider.Regularity.WeakSolutionTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardRealTranslateLiouville

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The residue, discharged: the Liouville class under a real translation

This module closes `RealTranslateLiouville d`, and with it clause (1) of the
stationary corrector family clause becomes unconditional.

The three conjuncts of `MemLiouvilleClass` are discharged by the three
transports proved here:

| conjunct | transport |
|---|---|
| `MemH1sLoc` | `memH1sLoc_realTranslate_subConst` |
| `IsWeakSolutionOn _ univ` | `IsWeakSolutionOn.translateCoeffField_univ` (available) |
| growth | `tendsto_growth_realTranslate_subConst` |

The coefficient identification `translateCoeffField t b = fun y ↦ b (y + t)` is
definitional, so the weak-solution conjunct needs no rewriting at all.

The `0 < theta` binder is necessary; see `PushforwardEngineInput`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The Liouville class transports along a translation by an arbitrary real
vector**, the coefficient field translating with the pair and an arbitrary
additive constant absorbed.

The statement is unconditional in `b`, `v`, `Dv`, `t` and `c`; the only
hypothesis is `0 < theta`, which is necessary — see `PushforwardEngineInput`. -/
theorem memLiouvilleClass_realTranslate_subConst {b : CoeffField d} {theta : ℝ}
    (htheta : 0 < theta) {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (h : MemLiouvilleClass b theta v Dv) (t : Vec d) (c : ℝ) :
    MemLiouvilleClass (fun y => b (y + t)) theta
      (fun y => v (y + t) - c) (fun y => Dv (y + t)) := by
  obtain ⟨hH1, hweak, hgrowth⟩ := h
  exact ⟨memH1sLoc_realTranslate_subConst hH1 t c,
    hweak.translateCoeffField_univ t,
    tendsto_growth_realTranslate_subConst htheta v t c hgrowth⟩

/-- **The residue, discharged.** -/
theorem realTranslateLiouville (d : ℕ) : RealTranslateLiouville d :=
  fun _ _ htheta _ _ t c h =>
    memLiouvilleClass_realTranslate_subConst htheta h t c

/-- **Clause (1)'s engine input, unconditional.**  On the translated sample the
normalized-gauge Liouville membership needed by the translated-gradient
identification engine follows from the untranslated one and nothing else.

Every binder is consumer-supplied: `hS` is `RootAssembly`'s own positive-definite
binder, `htheta` is `0 < rootCorrectorGrowth = 1/2` at the frozen constant, and
`hLiou` is the corrector construction applied at `normalizedSample abar hS a`. -/
theorem engine_liouville_input [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (G : NormalizedLocalH1Carrier d) (e : Vec d)
    {theta : ℝ} (htheta : 0 < theta)
    (hLiou : MemLiouvilleClass (gaugeCoeff a abar hS) theta
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        G.globalValueRepresentative y)
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        G.globalGradientRepresentative y))
    (z : Fin d → ℤ) :
    MemLiouvilleClass (gaugeCoeff (translateCoeff z a) abar hS) theta
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        G.globalValueRepresentative
          (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)))
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        G.globalGradientRepresentative
          (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z))) :=
  engine_liouville_input_of_realTranslate (realTranslateLiouville d) a abar hS G e
    htheta hLiou z

end

end Root
end HighContrast
end HCPolySupport
