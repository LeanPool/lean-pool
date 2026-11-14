/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineGamma0
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutSupport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRepChain

/-!
# HomSpineRecutClose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: THE BUNDLE RE-CUT — the multiscale clause alone

## What changes

`HomSpineRepClose.SpineDatumCoarseGrainingGauge` carries the transcribed source
hypothesis `hCG'` at ALL THREE of its clauses and the Schauder external's
Step-4 output `hC4ex` as an item.  The two DUALITY clauses and `hC4ex` are
PRODUCIBLE from the root's own binders.  This module performs the resulting
re-cut:

```text
  the re-cut bundle  =  SpineDatumCoarseGrainingGauge
      with  hCG'   ↦  its MULTISCALE clause alone
      with  hC4ex  DELETED
      plus  the four slot dominations + hlevelDual, at the display pin
            s₁′ = s/8, s′ = 7s/8, with Gen:= printedLocalEnergy.
```

* the two duality clauses come from the printed display through
  the two duality slots at the spine's own cutoff pair, whose own inputs
  are the root's two `IsDirichletSolutionOn` binders and the root's `C^{0,1/2}`
  binder on `𝐠`;
* `hC4ex` comes from
  the Step-4 comparator-energy producer — the
  external supplies the comparator, and the three `H¹`-level integrability facts
  are PRODUCED here (`memVectorL2_coeffFlux`), not assumed;
* the four slot dominations are the price of route (i): they tie the bundle's
  abstract numbers `Ccg, 𝓔₁, 𝓔₂, D_g` to the printed carriers of the display.
  `HomSpineRecutSupport` machine-checks that every one of those carriers is
  FINITE, so each domination is satisfiable by pinning the number to the
  carrier's own `toReal`.  No printed finiteness requirement survives.

### The order pin, and why it is forced

`HomCGCarrierEnergy`'s comparison needs `wgap ≤ s′ - s₁′`, and the bundle's own
`wgap` is `s - s/4 = 3s/4`.  The pin `s₁′ = s/8`, `s′ = 7s/8` meets it with
EQUALITY, and the order loss `s - s′ = s/8` keeps the duality window `0 <
(s-s′)p′ < d` open.  The per-site
reading is the disposition of the correction.

## The final conditional set is still exactly two entries

1. `htail` — the Theorem-C minimal-scale tail, a declared dependency
   edge (Theorem C), not an internal §4.5 obligation;
2. `hcg` — the per-`ω` re-cut bundle, whose items are
   the MULTISCALE clause of `hCG'` (a declared source hypothesis), the
   energy slot `hS`, the level conditions `hlevel`/`hlevelDual`, the four slot
   dominations, `hEB`/`hdom`, and the numerical frame.  NO duality clause, NO
   `hC4ex`, NO frame item.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The three `H¹`-level integrability facts, PRODUCED -/

/-- **The flux of an `H¹` function against a Chapter-2 coefficient is `L²`.**

The public coefficient object is only a.e.-elliptic, so the proof passes to the
internal pointwise-good representative and transports back — `CoarseGraining`'s
own route for `Solution.flux_memVectorL2`, here for a bare `H¹` function. -/
theorem memVectorL2_coeffFlux {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q) (fun x => matVecMul (a.toCoeffField x) (u.grad x)) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a
  have hb : Book.Ch02.CoeffOn.AEEq b a := by
    simpa [b] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn (Book.Ch02.cubeDomain Q) a
  have hbase : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  refine MeasureTheory.MemLp.ae_eq ?_ hbase
  exact hb.mono fun x hx => by simp [hx]

/-- The `u`-energy density is integrable on the window. -/
theorem integrableOn_selfEnergy {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 (memVectorL2_coeffFlux a u)

/-- The comparator's energy density is integrable on the window. -/
theorem integrableOn_comparatorEnergy {Q : TriadicCube d} (sigma0 : ℝ)
    (v : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot (v.grad x) (sigma0 • v.grad x)) (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
    (v.grad_memVectorL2.const_smul sigma0)

/-- The cross term is integrable on the window. -/
theorem integrableOn_crossEnergy {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u v : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (v.grad x))
      (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_coeffFlux a u) v.grad_memVectorL2

/-! ## 2. The Step-3c leg from the MULTISCALE clause alone -/

/-- The scale index the display is entered at: `n = m - jn`. -/
theorem recutParentScale (m : ℤ) (jn : ℕ) :
    (originCube d m).scale - (jn : ℤ) ≤ (originCube d m).scale :=
  sub_le_self _ (Int.natCast_nonneg jn)

end

end Algsuperdiff.Section4.Provider.Homogenization
