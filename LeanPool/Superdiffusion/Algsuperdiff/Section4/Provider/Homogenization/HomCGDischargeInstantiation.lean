/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# HomCGDischargeInstantiation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The spine's own binders feed the printed coarse-graining display

## What is established

`HomCGDischargeAssembly` proves the printed finite-`p` display at the
smooth-dual reading under `CoarseGraining`'s own hypothesis spelling
(`IsForcedEquation`, `IsScalarForcedEquation`, `HasH10Difference`).  The
spine's bundle (`SpineDatumCoarseGrainingGauge` of `HomSpineRepClose`) instead
carries **two `IsDirichletSolutionOn` binders against a common boundary datum
`h` and a common forcing `g`**:

```text
  hsol: IsDirichletSolutionOn (coefficientCutoff M.nu L ω).toCoeffField □_m u h g
  hcomp: IsDirichletSolutionOn (fun _ => σ_m • 1)                     □_m v h g
```

This file shows that **these two binders ARE the printed pair**, with nothing
added:

* `isForcedEquation_of_dirichletSolutionOn` — `hsol` is `-∇·𝐚∇u = ∇·𝐠`;
* `isScalarForcedEquation_of_dirichletSolutionOn` — `hcomp` is `-∇·σ₀∇v = ∇·𝐠`
  (`scalarMatrix σ₀` is by definition `σ₀ • 1`, so the two spellings are the
  same function);
* `hasH10Difference_of_dirichletPair` — the two zero-trace-difference clauses
  against the SAME `h` give `u - v ∈ H¹₀(□_m)`, because
  `(u - h) - (v - h) = u - v` and `H¹₀` is closed under subtraction.

Then `exists_printedCoarseGraining_of_dirichletPair` restates the display with
exactly those binders.

## The itemized spine-side feed

For the `CoarseGraining` display at `(m, n, s₁, s, s₂, p, 𝐚, σ₀, 𝐠, u, v)` one
needs, and only needs:

| `CoarseGraining` hypothesis | spine-side source |
| --- | --- |
| `2 ≤ d` | standing |
| `2 ≤ p.exponent` | the bundle's own `p` (it also carries `s + d/p ≤ 1/2`) |
| `n < m` | the bundle's mesoscale depth `jn`, at `n = m - jn`, `jn ≥ 1` |
| `s₁.1 < s.1 < s₂.1` | the `s₁ = s/4` pin plus `s < s₂` |
| `𝐚: CoeffOn (cubeDomain □_m)` | `coefficientCutoffCoeffOn M L ω □_m` |
| `0 < σ₀` | `hsig: 0 < σ_m` |
| `𝐠 ∈ W^{s₂,p}(□_m)` | **NOT a spine binder** — see the residue below |
| `-∇·𝐚∇u = ∇·𝐠` | `hsol.isDivFormWeakSolutionOn` |
| `-∇·σ₀∇v = ∇·𝐠` | `hcomp.isDivFormWeakSolutionOn` |
| `u - v ∈ H¹₀(□_m)` | `hsol.hasZeroTraceDifferenceOn` + `hcomp.…` |

The single item the spine does **not** supply is the forcing regularity
`MemCubeEuclideanFullWsp □_m s₂ p 𝐠`: the bundle only carries `𝐠`'s Hölder
seminorm `hKg`.  That is the honest residue of the instantiation layer, and it
is a hypothesis of the printed proposition itself (`𝐠 ∈ W^{s₂,p}(□_m)`), not an
artifact.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26
open Algsuperdiff.Section4.Support
open MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The three hypothesis bridges -/

/-- The spine's Dirichlet binder IS the printed heterogeneous equation. -/
theorem isForcedEquation_of_dirichletSolutionOn {Q : TriadicCube d}
    (A : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionOn A.toCoeffField Q u h g) :
    IsForcedEquation Q A u g :=
  hu.isDivFormWeakSolutionOn

/-- The spine's comparator binder IS the printed scalar equation.  No bridging
occurs: `scalarMatrix σ₀` unfolds to `σ₀ • 1`, which is the spine's spelling. -/
theorem isScalarForcedEquation_of_dirichletSolutionOn {Q : TriadicCube d}
    {sigma0 : ℝ} {v h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hv : IsDirichletSolutionOn (fun _ => sigma0 • (1 : Mat d)) Q v h g) :
    IsScalarForcedEquation Q sigma0 v g :=
  hv.isDivFormWeakSolutionOn

/-- **Two Dirichlet solutions with a COMMON boundary datum differ by an
`H¹₀` function.**  This is the printed `u - v ∈ H¹₀(□_m)`, produced from the
spine's two binders and nothing else. -/
theorem hasH10Difference_of_dirichletPair {Q : TriadicCube d}
    {A B : CoeffField d} {u v h : H1Function (openCubeSet Q)} {g g' : Vec d → Vec d}
    (hu : IsDirichletSolutionOn A Q u h g)
    (hv : IsDirichletSolutionOn B Q v h g') :
    HasH10Difference Q u v := by
  obtain ⟨w1, hw1val, _⟩ := hu.hasZeroTraceDifferenceOn
  obtain ⟨w2, hw2val, _⟩ := hv.hasZeroTraceDifferenceOn
  refine ⟨w1 - w2, Filter.Eventually.of_forall fun x => ?_⟩
  show (w1 - w2).toH1Function.toFun x = u.toFun x - v.toFun x
  have hsub : (w1 - w2).toH1Function.toFun x =
      w1.toH1Function.toFun x - w2.toH1Function.toFun x := by
    change (w1.toH1Function - w2.toH1Function).toFun x = _
    rw [H1Function.sub_toFun]
  rw [hsub, hw1val x, hw2val x]
  ring

/-! ## 2. The printed display at the spine's binder shape -/

/-- **The printed finite-`p` display, entered at the spine's own binders.**

Same conclusion as `exists_printedCoarseGrainingFiniteP_smoothDual`, but the
elliptic pair is presented as the spine presents it: two Dirichlet solutions
on `□_m` against a common boundary datum `h` and a common forcing `𝐠`. -/
theorem exists_printedCoarseGraining_of_dirichletPair (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m) (s1 s s2 : FractionalOrder),
        s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
      ∀ u v h : H1Function (openCubeSet (originCube d m)),
        IsDirichletSolutionOn a.toCoeffField (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ => sigma0 • (1 : Mat d)) (originCube d m) v h g →
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p ≤
          localCoarseGrainingLpRHS C (originCube d m) n
            (by simpa [originCube] using hnm.le) a sigma0 hsigma0 g u s1 s s2 p := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hC⟩ := exists_printedCoarseGrainingFiniteP_smoothDual d hd p hp
  refine ⟨C, hCtop, ?_⟩
  intro m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u v h hsol hcomp
  exact hC m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u v
    (isForcedEquation_of_dirichletSolutionOn a hsol)
    (isScalarForcedEquation_of_dirichletSolutionOn hcomp)
    (hasH10Difference_of_dirichletPair hsol hcomp)

end

end Algsuperdiff.Section4.Provider.Homogenization
