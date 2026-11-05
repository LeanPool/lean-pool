/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitHarmonic
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumZeroTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflectionCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepTriangle

/-!
# OneStepBoundaryComposeGlue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two structural glues of the boundary composition

Two mechanical pieces the boundary branch's assembly needs, and nothing else.

## 1. The `H¹` algebra of the manuscript competitor

The boundary producer at the split datum
takes the manuscript's odd competitor `V_odd = v − ℓ_h − v₁` as a *packaged*
`H¹` realization `vodd` together with its weak harmonicity `hvharm` and the
packaging identity `heq`.  Both are supplied here from the chain's own data by
the proved `H¹` algebra: `H1Function` is an `AddCommGroup`
(`Homogenization.H1Function.sub_toFun`/`sub_grad`), weak harmonicity is
subtractive (`AffineSplitHarmonic.isWeaklyHarmonicOn_sub`) and the affine lift
is weakly harmonic because its weak gradient is constant
(`AffineSplitHarmonic.isWeaklyHarmonicOn_affineLiftH1`).  No analytic input.

## 2. The affine-minimizer datum at the consumption window

The odd-class apparatus consumes `IsAffineMinimizer U₂ V (c − A·x) A`.  On a
truncated window this is a **theorem**, not a hypothesis: the window carries the
axis-cube sandwich, hence the two-sided affine nondegeneracy, hence attainment
(`SandwichNondegeneracyAttainment` through
`OneStepTriangle.exists_isAffineMinimizer_truncatedWindow`).  The only work here
is the change of affine parametrization `(c₀, g) ↦ (c₀ + g·x, g)` that puts the
minimizer in the `(c − A·x, A)` display the boundary producers print.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube H1Function MemH10)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `H¹` glue: the packaged competitor `v − ℓ_h − v₁` -/

/-- **The manuscript competitor as an `H¹` datum.**

`V_odd = v − ℓ_h − v₁` is realized in `H¹(U₂)`, is weakly harmonic there, and
has the packaging identity, purely from the `H¹` algebra: `v` and `v₁` are
weakly harmonic by hypothesis and the affine lift `ℓ_h` is weakly harmonic
because its weak gradient is the constant `A_ℓ`. -/
theorem exists_h1_oddCompetitor_affineSplit {m k : ℤ} {x : Vec d}
    {v v₁ : H1Function (truncatedWindow x m k)}
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hv₁ : IsWeaklyHarmonicOn (truncatedWindow x m k) v₁) (cl : ℝ) (Al : Vec d) :
    ∃ vodd : H1Function (truncatedWindow x m k),
      IsWeaklyHarmonicOn (truncatedWindow x m k) vodd ∧
      ∀ y, vodd.toFun y = v.toFun y - affineLift x cl Al y - v₁.toFun y := by
  have : IsFiniteMeasure (HCPolySupport.volumeMeasureOn (truncatedWindow x m k)) :=
    (isOpenBoundedConvexDomain_truncatedWindow x m k).isFiniteMeasure_restrict_volume
  set hSob := (isOpenBoundedConvexDomain_truncatedWindow x m k).isSobolevRegularDomain
    with hSobdef
  set l : H1Function (truncatedWindow x m k) := affineLiftH1 hSob x cl Al with hldef
  refine ⟨v - l - v₁, ?_, ?_⟩
  · exact isWeaklyHarmonicOn_sub
      (isWeaklyHarmonicOn_sub hv (isWeaklyHarmonicOn_affineLiftH1 hSob x cl Al)) hv₁
  · intro y
    have hl : l.toFun y = affineLift x cl Al y := by
      rw [hldef, affineLiftH1_toFun]
    simp only [HCPolySupport.H1Function.sub_toFun]
    rw [hl]

/-! ## 2. The affine-minimizer datum at the consumption window -/

/-- **`hmin` at consumption.**  On the truncated window the affine minimum is
attained, in the `(c − A·x, A)` parametrization the boundary producers print. -/
theorem exists_isAffineMinimizer_shifted_truncatedWindow {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {V : Vec d → ℝ}
    (hV : MemLp V 2 (volume.restrict (truncatedWindow x m k))) :
    ∃ (c : ℝ) (A : Vec d),
      IsAffineMinimizer (truncatedWindow x m k) V (c - vecDot A x) A := by
  obtain ⟨c₀, g, hmin⟩ := exists_isAffineMinimizer_truncatedWindow hx hkm hV
  refine ⟨c₀ + vecDot g x, g, ?_⟩
  have hc : c₀ + vecDot g x - vecDot g x = c₀ := by ring
  rw [hc]
  exact hmin

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
