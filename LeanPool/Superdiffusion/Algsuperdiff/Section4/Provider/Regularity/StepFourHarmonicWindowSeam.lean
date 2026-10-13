/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdFinalInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestriction

/-!
# StepFourHarmonicWindowSeam

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Weak harmonicity restricts to open subsets -/

/-- The zero extension of an `H¹₀(V)` test gradient integrates against any
vector field over `W` exactly as it does over `V`.  A local re-derivation of the
`private` step behind `EquationRestriction.isDivFormWeakSolutionOn_restrict`,
needed here because that step is not exported. -/
private theorem setIntegral_vecDot_h10Extend {V W : Set (Vec d)}
    (hV : MeasurableSet V) (hVW : V ⊆ W) (F : Vec d → Vec d) (phi : H10Function V) :
    ∫ x in W, vecDot (F x)
        ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x) ∂volume =
      ∫ x in V, vecDot (F x) (phi.toH1Function.grad x) ∂volume := by
  have hindicator :
      (fun x => vecDot (F x)
          ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x)) =
        Set.indicator V (fun x => vecDot (F x) (phi.toH1Function.grad x)) := by
    funext x
    by_cases hx : x ∈ V
    · simp only [h10ExtendToSuperset_grad, h10ZeroExtensionGrad_of_mem phi hx,
        Set.indicator_of_mem hx]
    · simp only [h10ExtendToSuperset_grad, h10ZeroExtensionGrad_of_not_mem phi hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [hindicator, MeasureTheory.integral_indicator hV,
    Measure.restrict_restrict hV, Set.inter_eq_left.mpr hVW]

/-- **Weak harmonicity restricts to every open subset.**

If `v` is weakly harmonic on `W` and `V ⊆ W` is open, the restriction of `v` is
weakly harmonic on `V`: every test function of `H¹₀(V)` extends by zero to one
of `H¹₀(W)`. -/
theorem isWeaklyHarmonicOn_restrict {W V : Set (Vec d)} (hV : IsOpen V)
    (hVW : V ⊆ W) {v : H1Function W} (h : IsWeaklyHarmonicOn W v) :
    IsWeaklyHarmonicOn V (v.restrict hV hVW) := by
  intro phi
  have hext := setIntegral_vecDot_h10Extend hV.measurableSet hVW v.grad phi
  have hgradEq : (v.restrict hV hVW).grad = v.grad := rfl
  calc
    ∫ x in V, vecDot ((v.restrict hV hVW).grad x) (phi.toH1Function.grad x) ∂volume =
        ∫ x in W, vecDot (v.grad x)
          ((h10ExtendToSuperset phi hV.measurableSet hVW).toH1Function.grad x)
          ∂volume := by
          rw [hgradEq, hext]
    _ = 0 := h (h10ExtendToSuperset phi hV.measurableSet hVW)

end

end Algsuperdiff.Section4.Provider.Regularity
