/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealScalarBase
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealComparator
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealOddGlue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealDatumStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPoincareWindow

/-!
# ResidueInterface

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary scalar `S` at the **harmonic-approximation** residue interface

## What is proved

`exists_scalarControl_boundaryBranch_comparator` re-cuts the proved composed
scalar theorem of the boundary lane's seal chain so
that its third right-hand summand is no longer the *gradient* residue
`3^n·Σᵢ‖∂ᵢu‖_{L²(K')}` but the strictly smaller **harmonic-approximation error
at the flush sub-cube**: the theorem now *produces* a `Δ`-harmonic comparator
`w = u + ρ`, `ρ ∈ H¹₀(K')`, together with the estimate

```text
  S ≤ C(d) · ( ‖u − (u)_{W'}‖_{L²(W')}                        (the FIRST leg)
             + 3^n · Σᵢ ‖∂ᵢh‖_{L²(W')}                        (the FIFTH leg)
             + ‖u − w‖_{L²(K')} )                             (the RESIDUE)
```

with `V₁` the anchor's covering cube, `W' = (z+□_{n+3}) ∩ □_m` the frozen
window, `K' = flushSubCentre z m n i σ + □_n` the flush scale-`n` sub-cube, and
`C(d)` explicit and dimension-only.

## Why the re-cut matters

The proved statement's residue has exactly one coefficient-free producer, the
Dirichlet-principle Poincaré `‖u − w‖ ≤ C·3^n·Σᵢ‖∂ᵢu‖` of `SealComparator`;
composing it with the fitted boundary Caccioppoli costs `√(σ/ν)`.  Exposing
the comparator instead removes that composition from the interface: `‖u −
w‖_{L²(K')}` is *literally* an instance of the harmonic-approximation display
the development's anchor proves, read at the flush sub-cube `K'` instead of at
the anchor's child cube `x+□_n`.  Applying `SealComparator`'s Poincaré bound
to the produced `w` recovers the proved statement verbatim, so this is a strict
sharpening — nothing is lost.  The `∀`-budget form consumed by the assembly is
`ResidueBudget.exists_scalarControl_of_boundaryBranch_harmonicResidue`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The scalar control at the harmonic-approximation residue interface -/

private abbrev residueInterface_comparisonBounds3_statement : Prop :=
    ∀ (d : ℕ) (CA : ℝ) (_ : (0 : ℝ) ≤ CA),
      let c1 : ℝ := √((3 : ℝ) ^ d) + √((27 : ℝ) ^ d) + CA * ((2 : ℝ) * √((27 : ℝ) ^ d));
        let c2 : ℝ :=
          datumStepConst d + comparatorPoincareConst d * √((27 : ℝ) ^ d) +
            CA * ((2 : ℝ) * (comparatorPoincareConst d * √((27 : ℝ) ^ d)) +
              unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d));
          let c3 : ℝ := (1 : ℝ) + CA * (2 : ℝ);
          ∀ (_ : (0 : ℝ) ≤ c1) (_ : (0 : ℝ) ≤ c2) (_ : (0 : ℝ) ≤
            c3) {n m : ℤ}
            {x z : Vec d} {i : Fin d} {σ : ℝ} (u h : H1Function (openCubeSet (originCube d m))),
            let c' : Vec d := flushSubCentre z m n i σ;
            ∀
              (_ :
                (0 : ℝ) <
                  ((volume : (a : Set (Vec d)) → ℝ≥0∞)
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))).toReal)
              (_ :
                (volume : (a : Set (Vec d)) → ℝ≥0∞)
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m)) ≠
                  ∞)
              (_ :
                (volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
                  (originCube d n)) ≠ ∞)
              (_ :
                IsFiniteMeasure
                  (volume.restrict
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m))))
              (_ :
                (volume : (a : Set (Vec d)) → ℝ≥0∞)
                    ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ)))) ≠
                  ∞)
              (wu wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
              (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
                (originCube d n))))
              (_ :
                MemLp u.toFun (2 : ℝ≥0∞) (volume.restrict ((fun (y : Vec d) => c' + y) ''
                  openCubeSet (originCube d n))))
              (_ :
                MemLp h.toFun (2 : ℝ≥0∞) (volume.restrict ((fun (y : Vec d) => c' + y) ''
                  openCubeSet (originCube d n))))
              (_ :
                MemLp u.toFun (2 : ℝ≥0∞)
                  (volume.restrict
                    ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ))))))
              (_ :
                MemLp h.toFun (2 : ℝ≥0∞)
                  (volume.restrict
                    ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ))))))
              (_ :
                MemLp u.toFun (2 : ℝ≥0∞)
                  (volume.restrict
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m)))),
              let XX : ℝ :=
                normalizedL2On
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m))
                  fun (y : Vec d) =>
                  u.toFun y -
                    volumeAverage
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      u.toFun;
                let HH : ℝ :=
                  ∑ i' : Fin d,
                    (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal;
                ∀ (_ : (0 : ℝ) ≤ XX) (_ : (0 : ℝ) ≤ HH) (_ : (0 : ℝ) ≤ (3 : ℝ) ^ n)
                  (_ :
                    (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (y : Vec d) =>
                        h.toFun y - wh.toFun y) ≤
                      comparatorPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH)
                  (_ :
                    |volumeAverage ((fun (y : Vec d) =>
                      c' + y) '' openCubeSet (originCube d n)) fun (y : Vec d) =>
                          wu.toFun y - wh.toFun y| ≤
                      CA *
                        normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) fun (y : Vec d) =>
                          wu.toFun y - wh.toFun y -
                            volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                              d n)) fun (y' : Vec d) =>
                              wu.toFun y' - wh.toFun y')
                  (_ :
                    |volumeAverage ((fun (y : Vec d) =>
                      flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n))
                          fun (x : Vec d) => u.toFun x - h.toFun x| ≤
                      ((normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                        openCubeSet (originCube d n))
                            fun (x : Vec d) => u.toFun x - wu.toFun x) +
                          normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                            openCubeSet (originCube d n))
                            fun (x : Vec d) => wh.toFun x - h.toFun x) +
                        |volumeAverage ((fun (y : Vec d) =>
                          flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n))
                            fun (x : Vec d) => wu.toFun x - wh.toFun x|),
                  let A1 : ℝ :=
                    volumeAverage
                      ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                        openCubeSet (originCube d (n + (2 : ℤ))))
                      u.toFun;
                    let A2 : ℝ :=
                      volumeAverage
                        ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                          openCubeSet (originCube d (n + (2 : ℤ))))
                        h.toFun;
                      let B1 : ℝ := volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                        (originCube d n)) u.toFun;
                      ∀
                        (_ :
                          (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                            d n)) fun (y : Vec d) =>
                              u.toFun y - B1) ≤
                            (2 : ℝ) * √((27 : ℝ) ^ d) * XX)
                        (_ : |A1 - B1| ≤ (√((3 : ℝ) ^ d) + √((27 : ℝ) ^ d)) * XX)
                        ,
                        let B2 : ℝ := volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                          (originCube d n)) h.toFun;
                        ∀
                          (_ :
                            (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet
                              (originCube d n)) fun (y : Vec d) =>
                                h.toFun y - B2) ≤
                              unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH)
                          (_ :
                            |A2 - B2| ≤
                              datumStepConst d * (3 : ℝ) ^ n *
                                ∑ i : Fin d,
                                  (eLpNorm (fun (y : Vec d) => h.grad y i) (2 : ℝ≥0∞)
                                      (normalizedVolumeMeasureOn
                                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d
                                          (n + (3 : ℤ))) ∩
                                          openCubeSet (originCube d m)))).toReal)
                          (_ :
                            (normalizedL2On
                                ((fun (y : Vec d) => flushSubCentre z m n i σ + y) '' openCubeSet
                                  (originCube d n))
                                fun (x : Vec d) =>
                                wu.toFun x - wh.toFun x -
                                  volumeAverage
                                    ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                      openCubeSet (originCube d n))
                                    fun (y : Vec d) => wu.toFun y - wh.toFun y) ≤
                              ((((2 : ℝ) *
                                      normalizedL2On
                                        ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                          openCubeSet (originCube d n))
                                        fun (x : Vec d) => u.toFun x - wu.toFun x) +
                                    (2 : ℝ) *
                                      normalizedL2On
                                        ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                          openCubeSet (originCube d n))
                                        fun (x : Vec d) => h.toFun x - wh.toFun x) +
                                  normalizedL2On
                                    ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                      openCubeSet (originCube d n))
                                    fun (x : Vec d) => u.toFun x - B1) +
                                normalizedL2On
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  fun (x : Vec d) => h.toFun x - B2)
                          ,
                          (|volumeAverage
                                  ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                                    openCubeSet (originCube d (n + (2 : ℤ))))
                                  fun (y : Vec d) => u.toFun y - h.toFun y| ≤
                              c1 * XX + c2 * ((3 : ℝ) ^ n * HH) +
                                c3 *
                                  normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet
                                    (originCube d n))
                                    fun (y : Vec d) => u.toFun y - wu.toFun y) ∧
                            XX =
                                (eLpNorm
                                    (fun (y : Vec d) =>
                                      u.toFun y -
                                        volumeAverage
                                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube
                                            d (n + (3 : ℤ))) ∩
                                            openCubeSet (originCube d m))
                                          u.toFun)
                                    (2 : ℝ≥0∞)
                                    (normalizedVolumeMeasureOn
                                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d
                                        (n + (3 : ℤ))) ∩
                                        openCubeSet (originCube d m)))).toReal ∧
                              (c1 * XX + c2 * ((3 : ℝ) ^ n * HH) +
                                  c3 *
                                    normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet
                                      (originCube d n))
                                      fun (y : Vec d) => u.toFun y - wu.toFun y) ≤
                                (c1 + c2 + c3) *
                                  (XX + (3 : ℝ) ^ n * HH +
                                    normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet
                                      (originCube d n))
                                      fun (y : Vec d) => u.toFun y - wu.toFun y)

private abbrev residueInterface_comparisonBounds2_statement : Prop :=
    ∀ (d : ℕ) (CA : ℝ)
      (_ :
        ∀ {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ},
          n + (2 : ℤ) ≤ m →
            σ = (1 : ℝ) ∨ σ = (-1 : ℝ) →
              wellPlacedHalfGap m (n + (2 : ℤ)) < σ * z i →
                ∀ (v : H1Function (truncatedWindow (flushSubCentre z m n i σ) m n)),
                  IsWeaklyHarmonicOn (truncatedWindow (flushSubCentre z m n i σ) m n) v →
                    ∀ (w0 : H10Function (openCubeSet (originCube d m)))
                      (rho_u rho_h : H10Function (truncatedWindow (flushSubCentre z m n i σ) m n)),
                      (∀ (y : Vec d), v.toFun y = w0.toFun y + rho_u.toFun y - rho_h.toFun y) →
                        |volumeAverage ((fun (y : Vec d) =>
                          flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n))
                              v.toFun| ≤
                          CA *
                            normalizedL2On
                              ((fun (y : Vec d) => flushSubCentre z m n i σ + y) '' openCubeSet
                                (originCube d n))
                              fun (y : Vec d) =>
                              v.toFun y -
                                volumeAverage
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  v.toFun)
      (_ : (0 : ℝ) ≤ comparatorPoincareConst d) {n m : ℤ} {x z : Vec d} {i : Fin d} {σ : ℝ} (_ : n
        + (2 : ℤ) ≤ m)
      (_ : x ∈ openCubeSet (originCube d m)) (_ : z ∈ openCubeSet (originCube d m))
      (_ :
        (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
          (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩ openCubeSet
            (originCube d m))
      (_ : σ = (1 : ℝ) ∨ σ = (-1 : ℝ)) (_ : wellPlacedHalfGap m (n + (2 : ℤ)) < σ * z i)
      (u h : H1Function (openCubeSet (originCube d m))) (_ : HasZeroTraceDifferenceOn (openCubeSet
        (originCube d m)) u h),
      let c' : Vec d := flushSubCentre z m n i σ;
      ∀
        (_ :
          (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆
            (fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩ openCubeSet
              (originCube d m))
        (_ :
          (fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩ openCubeSet
            (originCube d m) ⊆
            openCubeSet (originCube d m))
        (_ :
          (0 : ℝ) <
            ((volume : (a : Set (Vec d)) → ℝ≥0∞)
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))).toReal)
        (_ :
          (0 : ℝ) <
            ((volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
              (originCube d n))).toReal)
        (_ : (volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n)) ≠ ∞)
        (_ :
          IsFiniteMeasure
            (volume.restrict
              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))))
        (_ : (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆ openCubeSet (originCube
          d m))
        (wu : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (rhou : H10Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : IsWeaklyHarmonicOn (translateSet c' (openCubeSet (originCube d n))) wu)
        (_ : ∀ (y : Vec d), wu.toFun y = u.toFun y + rhou.toFun y)
        (wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (rhoh : H10Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : IsWeaklyHarmonicOn (translateSet c' (openCubeSet (originCube d n))) wh)
        (_ : ∀ (y : Vec d), wh.toFun y = h.toFun y + rhoh.toFun y)
        (_ :
          (normalizedL2On (translateSet c' (openCubeSet (originCube d n))) fun (y : Vec d) =>
            h.toFun y - wh.toFun y) ≤
            comparatorPoincareConst d * (3 : ℝ) ^ n *
              ∑ i : Fin d, normalizedL2On (translateSet c' (openCubeSet (originCube d n))) fun (y
                : Vec d) => h.grad y i)
        (_ : (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) = translateSet c'
          (openCubeSet (originCube d n)))
        (_ :
          ∀ (f : Vec d → ℝ),
            normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) f =
              normalizedL2On (translateSet c' (openCubeSet (originCube d n))) f)
        (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n)))),
        let HH : ℝ :=
          ∑ i' : Fin d,
            (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                (normalizedVolumeMeasureOn
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m)))).toReal;
        ∀
          (_ : (0 : ℝ) ≤ (3 : ℝ) ^ n),
          |volumeAverage
                    ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ))))
                    h.toFun -
                  volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                    h.toFun| ≤
              datumStepConst d * (3 : ℝ) ^ n *
                ∑ i : Fin d,
                  (eLpNorm (fun (y : Vec d) => h.grad y i) (2 : ℝ≥0∞)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal ∧
            (∀ (i' : Fin d),
                (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun
                  (y : Vec d) =>
                    h.grad y i') ≤
                  √((27 : ℝ) ^ d) *
                    (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal) ∧
              (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (y
                : Vec d) =>
                    h.toFun y - wh.toFun y) ≤
                  comparatorPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH ∧
                |volumeAverage ((fun (y : Vec d) =>
                  c' + y) '' openCubeSet (originCube d n)) fun (y : Vec d) =>
                      wu.toFun y - wh.toFun y| ≤
                  CA *
                    normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (y : Vec d) =>
                      wu.toFun y - wh.toFun y -
                        volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) fun (y' : Vec d) =>
                          wu.toFun y' - wh.toFun y'

/-- Comparator oscillation and mean bounds from finite local L² data. -/
theorem boundaryComparatorOscillationAndMeanBounds :
    ∀ (d : ℕ) {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ} (u h : H1Function (openCubeSet (originCube
      d m))),
      let c' : Vec d := flushSubCentre z m n i σ;
      ∀ (_ : MeasurableSet ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)))
        (_ :
          (0 : ℝ) <
            ((volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
              (originCube d n))).toReal)
        (_ : (volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n)) ≠ ∞)
        (wu wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n))))
        (_ : MemLp u.toFun (2 : ℝ≥0∞) (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n))))
        (_ : MemLp h.toFun (2 : ℝ≥0∞) (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n))))
        (_ :
          MemLp (fun (y : Vec d) => wu.toFun y) (2 : ℝ≥0∞)
            (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))))
        (_ :
          MemLp (fun (y : Vec d) => wh.toFun y) (2 : ℝ≥0∞)
            (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))))
        (_ :
          MemLp (fun (y : Vec d) => u.toFun y - wu.toFun y) (2 : ℝ≥0∞)
            (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))))
        (_ :
          MemLp (fun (y : Vec d) => h.toFun y - wh.toFun y) (2 : ℝ≥0∞)
            (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)))),
        ((normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (x :
          Vec d) =>
              wu.toFun x - wh.toFun x -
                volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (y
                  : Vec d) =>
                  wu.toFun y - wh.toFun y) ≤
            ((((2 : ℝ) *
                    normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (x : Vec d) =>
                      u.toFun x - wu.toFun x) +
                  (2 : ℝ) *
                    normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (x : Vec d) =>
                      h.toFun x - wh.toFun x) +
                normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun
                  (x : Vec d) =>
                  u.toFun x - volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                    (originCube d n)) u.toFun) +
              normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (x
                : Vec d) =>
                h.toFun x - volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                  d n)) h.toFun) ∧
          |volumeAverage ((fun (y : Vec d) =>
            c' + y) '' openCubeSet (originCube d n)) fun (x : Vec d) =>
                u.toFun x - h.toFun x| ≤
            ((normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (x
              : Vec d) =>
                  u.toFun x - wu.toFun x) +
                normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun
                  (x : Vec d) =>
                  wh.toFun x - h.toFun x) +
              |volumeAverage ((fun (y : Vec d) =>
                c' + y) '' openCubeSet (originCube d n)) fun (x : Vec d) =>
                  wu.toFun x - wh.toFun x| := by
  intro d n _ _ _ _ u h c' hK'meas hK'pos hK'top wu wh _ hmemU_K hmemH_K hWU_K hWH_K hUWU hHWH
  have hosc := oscillation_comparatorDifference_le
    (V := (fun y => c' + y) '' openCubeSet (originCube d n))
    hK'meas hK'pos hK'top
    (integrableOn_of_memLp_two hK'top hmemU_K)
    (integrableOn_of_memLp_two hK'top hmemH_K)
    (integrableOn_of_memLp_two hK'top hWU_K)
    (integrableOn_of_memLp_two hK'top hWH_K)
    (by
      have h1 := hUWU.integrable_sq
      simpa only [IntegrableOn] using h1)
    (by
      have h1 := hHWH.integrable_sq
      simpa only [IntegrableOn] using h1)
    (by
      have hfun : (fun y => wu.toFun y - u.toFun y) =
          fun y => -(u.toFun y - wu.toFun y) := by
        funext y
        ring
      rw [hfun]
      exact hUWU.neg)
    (by
      have hfun : (fun y => wh.toFun y - h.toFun y) =
          fun y => -(h.toFun y - wh.toFun y) := by
        funext y
        ring
      rw [hfun]
      exact hHWH.neg)
    (hmemU_K.sub (memLp_const _))
    (hmemH_K.sub (memLp_const _))
    (hWU_K.sub (memLp_const _))
    ((hWH_K.sub (memLp_const _)).neg)
  -- L D1: the comparator split at the flush sub-cube
  have hsplit := abs_volumeAverage_sub_le_comparatorSplit
    (V := (fun y => c' + y) '' openCubeSet (originCube d n))
    hK'meas hK'pos
    (u := u.toFun) (h := h.toFun) (vbar := wu.toFun) (hbar := wh.toFun)
    (integrableOn_of_memLp_two hK'top hUWU)
    (by
      have hfun : (fun y => wh.toFun y - h.toFun y) =
          fun y => -(h.toFun y - wh.toFun y) := by
        funext y
        ring
      rw [hfun]
      exact (integrableOn_of_memLp_two hK'top hHWH).neg)
    (integrableOn_of_memLp_two hK'top (hWU_K.sub hWH_K))
    (by
      have h1 := hUWU.integrable_sq
      simpa only [IntegrableOn] using h1)
    (by
      have hfun : (fun y => (wh.toFun y - h.toFun y) ^ 2) =
          fun y => (h.toFun y - wh.toFun y) ^ 2 := by
        funext y
        ring
      rw [hfun]
      have h1 := hHWH.integrable_sq
      simpa only [IntegrableOn] using h1)
  exact ⟨hosc, hsplit⟩

/-- Transport each gradient coordinate from a contained cube to its anchor window. -/
theorem normalizedL2On_grad_le_anchorWindow {n m : ℤ} {z c : Vec d}
    (h : H1Function (openCubeSet (originCube d m)))
    (hsub : (fun y => c + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))
    (hWpos : 0 < (volume (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))).toReal)
    (hKpos : 0 < (volume ((fun y => c + y) '' openCubeSet (originCube d n))).toReal)
    (hKtop : volume ((fun y => c + y) '' openCubeSet (originCube d n)) ≠ ⊤) (i : Fin d) :
    normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n))
      (fun y => h.grad y i) ≤ Real.sqrt ((27 : ℝ) ^ d) *
        (eLpNorm (fun y => h.grad y i) 2 (Support.normalizedVolumeMeasureOn
          (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))).toReal := by
  have hKne : volume ((fun y => c + y) '' openCubeSet (originCube d n)) ≠ 0 := by
    intro heq
    simp only [heq, ENNReal.toReal_zero, lt_self_iff_false] at hKpos
  have hWne : volume (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) ≠ 0 := by
    intro heq
    simp only [heq, ENNReal.toReal_zero, lt_self_iff_false] at hWpos
  rw [Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
    (pos_iff_ne_zero.mpr hKne) hKtop (memLp_grad_of_subset h (hsub.trans Set.inter_subset_right) i)]
  exact toReal_eLpNorm_scaleN_cube_le_anchorWindow hsub
    (memLp_normalizedVolumeMeasureOn_of_restrict hWne
      (memLp_grad_of_subset h Set.inter_subset_right i)).eLpNorm_ne_top

/-- Sum transported gradients in the comparator Poincaré estimate. -/
theorem normalizedL2On_sub_comparator_le_of_gradient_transport {n : ℤ} {c : Vec d}
    {u w : Vec d → ℝ} {g : Fin d → Vec d → ℝ} {K : ℝ} {B : Fin d → ℝ}
    (hbound : normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n))
      (fun y => u y - w y) ≤ comparatorPoincareConst d * (3 : ℝ) ^ n *
        ∑ i, normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n)) (g i))
    (hgrad : ∀ i, normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n))
      (g i) ≤ K * B i) :
    normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n)) (fun y => u y - w y) ≤
      comparatorPoincareConst d * K * (3 : ℝ) ^ n * ∑ i, B i := by
  have hsum : ∑ i, normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n))
      (g i) ≤ K * ∑ i, B i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hgrad i
  have hnonneg : 0 ≤ comparatorPoincareConst d * (3 : ℝ) ^ n :=
    mul_nonneg (comparatorPoincareConst_nonneg d) (le_of_lt (zpow_pos (by norm_num) n))
  refine hbound.trans ((mul_le_mul_of_nonneg_left hsum hnonneg).trans_eq ?_)
  ring

/-- Transport a harmonic comparator difference before applying a mean estimate. -/
theorem abs_volumeAverage_comparator_sub_le_of_setEq {U V W A : Set (Vec d)}
    {CA : ℝ} (hUV : U = V) (w0 : H10Function W)
    (hmean : ∀ v : H1Function U, IsWeaklyHarmonicOn U v →
      ∀ ru rh : H10Function U,
        (∀ y, v.toFun y = w0.toFun y + ru.toFun y - rh.toFun y) →
        |volumeAverage A v.toFun| ≤ CA * normalizedL2On A
          (fun y => v.toFun y - volumeAverage A v.toFun))
    (wu wh : H1Function V) (ru rh : H10Function V)
    (hu : IsWeaklyHarmonicOn V wu) (hh : IsWeaklyHarmonicOn V wh)
    (hsplit : ∀ y, wu.toFun y - wh.toFun y = w0.toFun y + ru.toFun y - rh.toFun y) :
    |volumeAverage A (fun y => wu.toFun y - wh.toFun y)| ≤ CA * normalizedL2On A
      (fun y => (wu.toFun y - wh.toFun y) -
        volumeAverage A (fun x => wu.toFun x - wh.toFun x)) := by
  let vd : H1Function U := h1FunctionOfSetEq hUV.symm (wu - wh)
  have hvdval : vd.toFun = fun y => wu.toFun y - wh.toFun y := by
    dsimp only [vd]
    rw [h1FunctionOfSetEq_toFun, H1Function.sub_toFun]
  have hharm : IsWeaklyHarmonicOn U vd :=
    isWeaklyHarmonicOn_h1FunctionOfSetEq hUV.symm (isWeaklyHarmonicOn_sub_h1 hu hh)
  have hval : ∀ y, vd.toFun y = w0.toFun y +
      (h10FunctionOfSetEq hUV.symm ru).toFun y -
      (h10FunctionOfSetEq hUV.symm rh).toFun y := by
    intro y
    rw [hvdval, h10FunctionOfSetEq_toFun, h10FunctionOfSetEq_toFun]
    exact hsplit y
  simpa only [hvdval] using hmean vd hharm
    (h10FunctionOfSetEq hUV.symm ru) (h10FunctionOfSetEq hUV.symm rh) hval

/-- Assemble comparator oscillation, approximation, and parent-to-child mean bounds. -/
theorem comparator_mean_bound_of_legs
    {CA a b c p q X H NU NH P A B child comp osc oscU oscH : ℝ} (hCA : 0 ≤ CA)
    (htri : P ≤ A + B + child) (hA : A ≤ a * X) (hB : B ≤ b * H)
    (hsplit : child ≤ NU + NH + comp) (hcomp : comp ≤ CA * osc)
    (hosc : osc ≤ 2 * NU + 2 * NH + oscU + oscH)
    (hoscU : oscU ≤ 2 * q * X) (hoscH : oscH ≤ p * H) (hNH : NH ≤ c * H) :
    P ≤ (a + CA * (2 * q)) * X + (b + c + CA * (2 * c + p)) * H +
      (1 + CA * 2) * NU := by
  have hosc' : osc ≤ 2 * NU + 2 * NH + 2 * q * X + p * H := by
    linarith only [hosc, hoscU, hoscH]
  have hcomp' := hcomp.trans (mul_le_mul_of_nonneg_left hosc' hCA)
  have hCAmul := mul_le_mul_of_nonneg_left hNH (mul_nonneg hCA (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith only [htri, hA, hB, hsplit, hcomp', hNH, hCAmul]

private theorem residueInterface_comparisonBounds2 :
  residueInterface_comparisonBounds2_statement := by
  classical
  intro d CA hCA hCP0 n m _ z i _σ hnm hx hz hgeom hσ hover _ h hzt c' hKW' hW'm hW'pos hK'pos
    hK'top this hK'm wu rhou hharmu hvalu wh rhoh hharmh hvalh hboundh hKT hNormSet this HH h3n0
  have hc' :
    c' = flushSubCentre z m n i _σ
    := rfl
  have hlegC := abs_volumeAverage_datum_sub_le_datumStep (c' := c') hnm hx hz hgeom
    (by rw [hc']; exact flushSubCube_subset_flushCube z i hσ) h
  -- L D3: the h-comparator error, transported to the window
  have hgradHtrans := normalizedL2On_grad_le_anchorWindow h hKW' hW'pos hK'pos hK'top
  have hlegD3 : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => h.toFun y - wh.toFun y) ≤
      comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH := by
    exact normalizedL2On_sub_comparator_le_of_gradient_transport
      (by simpa only [← hNormSet] using hboundh) hgradHtrans
  -- L A: the comparator-difference mean, through the odd-harmonic glue
  have hTW : truncatedWindow c' m n =
      (fun y => c' + y) '' openCubeSet (originCube d n) := by
    rw [hc']
    exact truncatedWindow_eq_flushSubCube hnm z i hσ
  have hTWts : truncatedWindow c' m n =
      translateSet c' (openCubeSet (originCube d n)) := by
    rw [hTW, hKT]
  obtain ⟨w0, hw0val, _hw0grad⟩ := hzt
  have hlegA : |volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => wu.toFun y - wh.toFun y)| ≤
      CA * normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => (wu.toFun y - wh.toFun y) -
          volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
            (fun y' => wu.toFun y' - wh.toFun y')) := by
    refine abs_volumeAverage_comparator_sub_le_of_setEq hTWts w0
      (fun v hv ru rh hval => hCA hnm hσ hover v hv w0 ru rh hval)
      wu wh rhou rhoh hharmu hharmh ?_
    intro y
    have hu := hvalu y
    have hh := hvalh y
    have hw0 := hw0val y
    linarith only [hu, hh, hw0]
  exact ⟨hlegC, hgradHtrans, hlegD3, hlegA⟩

private theorem residueInterface_comparisonBounds3 :
  residueInterface_comparisonBounds3_statement := by
  classical
  intro d CA hCA0 c1 c2 c3 hc10 hc20 hc30 n m x z _ _ u h c' hW'pos hW'top hK'top this hV1top wu
    wh this hmemU_K hmemH_K hmemU_V1 hmemH_V1 hmemU_W XX HH hXX0 hHH0 h3n0 hlegD3 hlegA hsplit A1
    A2 B1 hoscU hlegB B2 hoscH hlegC hosc
  have hc1 :
    c1 = √((3 : ℝ) ^ d) + √((27 : ℝ) ^ d) + CA * ((2 : ℝ) * √((27 : ℝ) ^ d))
    := rfl
  have hc2 :
    c2 =
              datumStepConst d + comparatorPoincareConst d * √((27 : ℝ) ^ d) +
                CA *
                  ((2 : ℝ) * (comparatorPoincareConst d * √((27 : ℝ) ^ d)) +
                    unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d))
    := rfl
  have hc3 :
    c3 = (1 : ℝ) + CA * (2 : ℝ)
    := rfl
  have hXXdef :
    XX =
                    normalizedL2On
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      fun (y : Vec d) =>
                      u.toFun y -
                        volumeAverage
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m))
                          u.toFun
    := rfl
  have hA1 :
    A1 =
                        volumeAverage
                          ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                            openCubeSet (originCube d (n + (2 : ℤ))))
                          u.toFun
    := rfl
  have hA2 :
    A2 =
                          volumeAverage
                            ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                              openCubeSet (originCube d (n + (2 : ℤ))))
                            h.toFun
    := rfl
  have hB1' :
    B1 = volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                          (originCube d n)) u.toFun
    := rfl
  have hB2' :
    B2 = volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                            (originCube d n)) h.toFun
    := rfl
  have hmeanV1 : volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - h.toFun y) =
      A1 - A2 := by
    rw [hA1, hA2]
    exact volumeAverage_sub_eq
      (integrableOn_of_memLp_two hV1top hmemU_V1)
      (integrableOn_of_memLp_two hV1top hmemH_V1)
  have hmeanK : volumeAverage ((fun y => c' + y) ''
      openCubeSet (originCube d n)) (fun y => u.toFun y - h.toFun y) =
      B1 - B2 := by
    rw [hB1', hB2']
    exact volumeAverage_sub_eq
      (integrableOn_of_memLp_two hK'top hmemU_K)
      (integrableOn_of_memLp_two hK'top hmemH_K)
  have htri0 : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - h.toFun y)| ≤
      |A1 - B1| + |A2 - B2| +
        |volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          (fun y => u.toFun y - h.toFun y)| := by
    rw [hmeanV1]
    have hid : A1 - A2 = ((A1 - B1) - (A2 - B2)) + (B1 - B2) := by ring
    rw [hid]
    have t1 := abs_add_le ((A1 - B1) - (A2 - B2)) (B1 - B2)
    have t2 := abs_sub (A1 - B1) (A2 - B2)
    rw [hmeanK]
    linarith only [t1, t2]
  -- the five normalized quantities
  set NU : ℝ := normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
    (fun y => u.toFun y - wu.toFun y) with hNU
  set NH : ℝ := normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
    (fun y => h.toFun y - wh.toFun y) with hNH
  have hNU0 : 0 ≤ NU := normalizedL2On_nonneg _ _
  have hsplit' : |volumeAverage ((fun y => c' + y) ''
      openCubeSet (originCube d n)) (fun y => u.toFun y - h.toFun y)| ≤
      NU + NH +
        |volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          (fun y => wu.toFun y - wh.toFun y)| := by
    have h1 := hsplit
    have hcomm : normalizedL2On ((fun y => c' + y) ''
        openCubeSet (originCube d n)) (fun y => wh.toFun y - h.toFun y) = NH := by
      rw [hNH]
      exact normalizedL2On_sub_comm _ _ _
    rw [hcomm] at h1
    rw [hNU]
    exact h1
  have htotal : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - h.toFun y)| ≤
      c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU := by
    rw [hc1, hc2, hc3]
    exact comparator_mean_bound_of_legs hCA0 htri0 hlegB
      (by simpa only [mul_assoc] using hlegC) hsplit' hlegA hosc hoscU
      (by simpa only [mul_assoc] using hoscH)
      (by simpa only [mul_assoc] using hlegD3)
  -- the final constant regrouping and the `eLpNorm` spelling of `XX`
  have hXXe : XX = (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal := by
    rw [hXXdef]
    exact Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
      (ENNReal.toReal_pos_iff.mp hW'pos).1 hW'top (hmemU_W.sub (memLp_const _))
  have hfinal : c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU ≤
      (c1 + c2 + c3) * (XX + (3 : ℝ) ^ n * HH + NU) := by
    have t1 : 0 ≤ (3 : ℝ) ^ n * HH := mul_nonneg h3n0 hHH0
    nlinarith only [hc10, hc20, hc30, hXX0, t1, hNU0]
  exact ⟨htotal, hXXe, hfinal⟩

/-- Mean-zero Poincaré on a translated cube after transporting each gradient coordinate. -/
theorem normalizedL2On_sub_average_le_of_gradient_transport
    {n m : ℤ} {c : Vec d} (h : H1Function (openCubeSet (originCube d m)))
    (hK'm : (fun y => c + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m)) {K : ℝ} {B : Fin d → ℝ}
    (hgradHtrans : ∀ i, normalizedL2On
      ((fun y => c + y) '' openCubeSet (originCube d n)) (fun y => h.grad y i) ≤ K * B i) :
    normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d n))
      (fun y => h.toFun y - volumeAverage
        ((fun y => c + y) '' openCubeSet (originCube d n)) h.toFun) ≤
      unitMeanZeroPoincareConst d * K * (3 : ℝ) ^ n * (∑ i, B i) := by
  let c' := c
  have hK'pos := volume_toReal_image_add_openCubeSet_pos c n
  have hK'top := volume_image_add_openCubeSet_ne_top c n
  have : IsFiniteMeasure (volume.restrict
      ((fun y => c' + y) '' openCubeSet (originCube d n))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hK'top⟩
  have hmemH_K := memLp_toFun_of_subset h hK'm
  have humz0 := unitMeanZeroPoincareConst_nonneg d
  have h3n0 : 0 ≤ (3 : ℝ) ^ n := (zpow_pos (by norm_num) n).le
  have hpo := eLpNorm_sub_average_translatedCube_le_meanZeroPoincare
    (j := n) (c := c') hK'm h
  have hbridge : normalizedL2On ((fun y => c' + y) ''
      openCubeSet (originCube d n))
      (fun y => h.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          h.toFun) =
      (eLpNorm (fun y => h.toFun y -
        volumeAverage ((fun y' => c' + y') '' openCubeSet (originCube d n))
          h.toFun) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y' => c' + y') '' openCubeSet (originCube d n)))).toReal := by
    refine Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
      ?_ hK'top (hmemH_K.sub (memLp_const _))
    by_contra hcon
    push Not at hcon
    have h0 : volume ((fun y => c' + y) '' openCubeSet (originCube d n)) = 0 :=
      le_antisymm hcon zero_le
    have := hK'pos
    rw [h0] at this
    simp only [ENNReal.toReal_zero] at this
    exact lt_irrefl _ this
  rw [hbridge]
  refine hpo.trans ?_
  have hsum : ∑ i' : Fin d,
      (eLpNorm (fun y => h.grad y i') 2
        (Support.normalizedVolumeMeasureOn
          ((fun y' => c' + y') '' openCubeSet (originCube d n)))).toReal ≤
      K * (∑ i, B i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i' _ => ?_
    have h1 := hgradHtrans i'
    have hbr : normalizedL2On ((fun y => c' + y) ''
        openCubeSet (originCube d n)) (fun y => h.grad y i') =
        (eLpNorm (fun y => h.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((fun y' => c' + y') '' openCubeSet (originCube d n)))).toReal := by
      refine Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
        ?_ hK'top (memLp_grad_of_subset h hK'm i')
      by_contra hcon
      push Not at hcon
      have h0 : volume ((fun y => c' + y) '' openCubeSet (originCube d n)) = 0 :=
        le_antisymm hcon zero_le
      have := hK'pos
      rw [h0] at this
      simp only [ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    rw [← hbr]
    exact h1
  calc unitMeanZeroPoincareConst d * (3 : ℝ) ^ n *
      ∑ i' : Fin d,
        (eLpNorm (fun y => h.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((fun y' => c' + y') '' openCubeSet (originCube d n)))).toReal
      ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ n *
          (K * (∑ i, B i)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg humz0 h3n0)
    _ = unitMeanZeroPoincareConst d * K * (3 : ℝ) ^ n *
          (∑ i, B i) := by ring

/-- Restricting to a finite positive-volume set controls its centered norm by
its volume ratio against the containing window. -/
theorem normalizedL2On_sub_average_le_twice_sqrt_ratio
    {m : ℤ} {A W : Set (Vec d)} {R : ℝ}
    (hK'meas : MeasurableSet A) (hKW' : A ⊆ W)
    (hW'm : W ⊆ openCubeSet (originCube d m))
    (hW'pos : 0 < (volume W).toReal) (hK'pos : 0 < (volume A).toReal)
    (hK'top : volume A ≠ ⊤) (hW'top : volume W ≠ ⊤)
    (hR : (volume W).toReal / (volume A).toReal ≤ R)
    (u : H1Function (openCubeSet (originCube d m))) :
    normalizedL2On A (fun y => u.toFun y - volumeAverage A u.toFun) ≤
      2 * Real.sqrt R * normalizedL2On W (fun y => u.toFun y - volumeAverage W u.toFun) := by
  have : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hK'top⟩
  have hmemU_K := memLp_toFun_of_subset u (hKW'.trans hW'm)
  have hmemU_W := memLp_toFun_of_subset u hW'm
  let XX := normalizedL2On W (fun y => u.toFun y - volumeAverage W u.toFun)
  have hXXdef : XX = normalizedL2On W
      (fun y => u.toFun y - volumeAverage W u.toFun) := rfl
  set aW : ℝ := volumeAverage W u.toFun with haW
  have hgap : |volumeAverage A u.toFun - aW| ≤
      Real.sqrt R * XX := by
    rw [hXXdef, haW]
    exact abs_avg_cube_sub_window_le (m := m) hK'meas hKW' hW'm hW'pos hK'pos
      hK'top hW'top hR u
  have htransport : normalizedL2On A (fun y => u.toFun y - aW) ≤
      Real.sqrt R * XX := by
    have hsq : IntegrableOn (fun y => (u.toFun y - aW) ^ 2)
        W volume :=
      integrableOn_sub_const_sq hW'top hmemU_W aW
    have h1 := normalizedL2On_le_of_subset (W := W)
      (W' := A)
      (f := fun y => u.toFun y - aW) hKW' hW'pos hK'pos hsq
    refine h1.trans ?_
    rw [hXXdef, haW]
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hR)
      (normalizedL2On_nonneg _ _)
  have hdecomp : (fun y => u.toFun y -
      volumeAverage A
        u.toFun) = fun y => (u.toFun y - aW) +
      (aW - volumeAverage A u.toFun) := by
    funext y
    ring
  have hmem1 : MemLp (fun y => u.toFun y - aW) 2
      (volume.restrict A) :=
    hmemU_K.sub (memLp_const aW)
  have hmem2 : MemLp (fun _ : Vec d => aW -
      volumeAverage A
        u.toFun) 2
      (volume.restrict A) :=
    memLp_const _
  rw [hdecomp]
  have hmink := normalizedL2On_add_le hmem1 hmem2
  refine hmink.trans ?_
  have hconst : normalizedL2On A
      (fun _ => aW - volumeAverage A u.toFun) =
      |aW - volumeAverage A u.toFun| :=
    normalizedL2On_const_abs hK'pos _
  rw [hconst]
  have habs : |aW - volumeAverage A u.toFun| =
      |volumeAverage A u.toFun - aW| := abs_sub_comm _ _
  rw [habs]
  linarith only [htransport, hgap]

private theorem residueInterface_estimate3 :
    ∀ (d : ℕ) {n m : ℤ} {x z : Vec d} {i : Fin d} {σ : ℝ}
      (u : H1Function (openCubeSet (originCube d m))),
      let c' : Vec d := flushSubCentre z m n i σ;
      let XX : ℝ :=
        normalizedL2On
          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩ openCubeSet
            (originCube d m))
          fun (y : Vec d) =>
          u.toFun y -
            volumeAverage
              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))
              u.toFun;
      ∀
        (_ :
          |volumeAverage
                  ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) '' openCubeSet
                    (originCube d (n + (2 : ℤ))))
                  u.toFun -
                volumeAverage
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m))
                  u.toFun| ≤
            √((3 : ℝ) ^ d) *
              normalizedL2On
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))
                fun (y : Vec d) =>
                u.toFun y -
                  volumeAverage
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m))
                    u.toFun)
        (_ :
          |volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) u.toFun -
                volumeAverage
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m))
                  u.toFun| ≤
            √((27 : ℝ) ^ d) *
              normalizedL2On
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))
                fun (y : Vec d) =>
                u.toFun y -
                  volumeAverage
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m))
                    u.toFun),
        |volumeAverage
                ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) '' openCubeSet
                  (originCube d (n + (2 : ℤ))))
                u.toFun -
              volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) u.toFun| ≤
          (√((3 : ℝ) ^ d) + √((27 : ℝ) ^ d)) * XX := by
  intro d n m x z _ _ u c' XX hB1 hB2
  have hXXdef : XX =
            normalizedL2On
              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))
              fun (y : Vec d) =>
              u.toFun y -
                volumeAverage
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m))
                  u.toFun := rfl
  have htri := abs_sub (volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) u.toFun -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun)
    (volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun)
  have heq : volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) u.toFun -
      volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun =
      (volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2))) u.toFun -
        volumeAverage ((((fun y' => z + y') ''
            openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) -
      (volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun -
        volumeAverage ((((fun y' => z + y') ''
            openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) := by
    ring
  rw [heq]
  calc |_ - _| ≤ _ + _ := htri
    _ ≤ Real.sqrt ((3 : ℝ) ^ d) * XX + Real.sqrt ((27 : ℝ) ^ d) * XX := by
        rw [hXXdef]
        exact add_le_add hB1 hB2
    _ = (Real.sqrt ((3 : ℝ) ^ d) + Real.sqrt ((27 : ℝ) ^ d)) * XX := by ring

/-- Square-integrability of two functions, their local comparators and their differences.
The three comparison regions can be arbitrary subsets of the original domain. -/
theorem residueInterface_comparatorIntegrability
    {d : ℕ} {U K V W : Set (Vec d)} (u h : H1Function U)
    (hKU : K ⊆ U) (hVU : V ⊆ U) (hWU : W ⊆ U) (wu wh : H1Function K) :
    MemLp u.toFun (2 : ℝ≥0∞) (volume.restrict K) ∧
      MemLp h.toFun (2 : ℝ≥0∞) (volume.restrict K) ∧
      MemLp u.toFun (2 : ℝ≥0∞) (volume.restrict V) ∧
      MemLp h.toFun (2 : ℝ≥0∞) (volume.restrict V) ∧
      MemLp u.toFun (2 : ℝ≥0∞) (volume.restrict W) ∧
      MemLp wu.toFun (2 : ℝ≥0∞) (volume.restrict K) ∧
      MemLp wh.toFun (2 : ℝ≥0∞) (volume.restrict K) ∧
      MemLp (fun x => u.toFun x - wu.toFun x) (2 : ℝ≥0∞) (volume.restrict K) ∧
      MemLp (fun x => h.toFun x - wh.toFun x) (2 : ℝ≥0∞) (volume.restrict K) := by
  have huK := MemLp.mono_measure (Measure.restrict_mono_set volume hKU) u.memL2
  have hhK := MemLp.mono_measure (Measure.restrict_mono_set volume hKU) h.memL2
  have hwu : MemLp wu.toFun (2 : ℝ≥0∞) (volume.restrict K) := wu.memL2
  have hwh : MemLp wh.toFun (2 : ℝ≥0∞) (volume.restrict K) := wh.memL2
  exact ⟨huK, hhK, MemLp.mono_measure (Measure.restrict_mono_set volume hVU) u.memL2,
    MemLp.mono_measure (Measure.restrict_mono_set volume hVU) h.memL2,
    MemLp.mono_measure (Measure.restrict_mono_set volume hWU) u.memL2,
    hwu, hwh, huK.sub hwu, hhK.sub hwh⟩

/-- **The boundary scalar `S`, composed, with the residue exhibited as the
harmonic-approximation error at the flush sub-cube.**

`S = |⨍_{V₁}(u−h)|` is priced, coefficient-free, by the frozen shape, the
frozen shape, and any real `R` dominating `‖u − w‖_{L²(K')}` for every
`Δ`-harmonic comparator `w = u + ρ`, `ρ ∈ H¹₀(K')`. -/
theorem exists_scalarControl_boundaryBranch_comparator (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n m : ℤ} {x z : Vec d} {i : Fin d} {σ : ℝ},
        n + 2 ≤ m →
        x ∈ openCubeSet (originCube d m) →
        z ∈ openCubeSet (originCube d m) →
        ((fun y => x + y) '' openCubeSet (originCube d n) ⊆
          ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
            openCubeSet (originCube d m)) →
        (σ = 1 ∨ σ = -1) →
        wellPlacedHalfGap m (n + 2) < σ * z i →
        ∀ u h : H1Function (openCubeSet (originCube d m)),
          Support.HasZeroTraceDifferenceOn (openCubeSet (originCube d m)) u h →
          ∃ (w : H1Function (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n))))
            (rho : H10Function (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n)))),
            IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n))) w ∧
            (∀ y, w.toFun y = u.toFun y + rho.toH1Function.toFun y) ∧
            (∀ y, w.grad y = u.grad y + rho.toH1Function.grad y) ∧
          |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
              openCubeSet (originCube d (n + 2)))
              (fun y => u.toFun y - h.toFun y)| ≤
            C * ((eLpNorm (fun y => u.toFun y -
                  volumeAverage ((((fun y' => z + y') ''
                      openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) u.toFun) 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal +
              (3 : ℝ) ^ n *
                ∑ i' : Fin d,
                  (eLpNorm (fun y => h.grad y i') 2
                    (Support.normalizedVolumeMeasureOn
                      ((((fun y' => z + y') ''
                          openCubeSet (originCube d (n + 3))) ∩
                        openCubeSet (originCube d m))))).toReal +
              normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
                  openCubeSet (originCube d n))
                (fun y => u.toFun y - w.toFun y)) ∧
            normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
                openCubeSet (originCube d n))
              (fun y => u.toFun y - w.toFun y) ≤
              comparatorPoincareConst d * (3 : ℝ) ^ n *
                ∑ i' : Fin d,
                  normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
                    openCubeSet (originCube d n)) (fun y => u.grad y i') := by
  classical
  obtain ⟨CA, hCA0, hCA⟩ :=
    exists_abs_volumeAverage_le_normalizedL2On_flushComparator d
  have hCP0 : 0 ≤ comparatorPoincareConst d := comparatorPoincareConst_nonneg d
  have hdsc0 : 0 ≤ datumStepConst d := datumStepConst_nonneg d
  have humz0 : 0 ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have hs3 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hs27 : (0 : ℝ) ≤ Real.sqrt ((27 : ℝ) ^ d) := Real.sqrt_nonneg _
  -- the three coefficient groups
  set c1 : ℝ := Real.sqrt ((3 : ℝ) ^ d) + Real.sqrt ((27 : ℝ) ^ d) +
    CA * (2 * Real.sqrt ((27 : ℝ) ^ d)) with hc1
  set c2 : ℝ := datumStepConst d +
    comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) +
    CA * (2 * (comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d)) +
      unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d)) with hc2
  set c3 : ℝ := 1 + CA * 2 with hc3
  have hc10 : 0 ≤ c1 := by
    rw [hc1]
    have := mul_nonneg hCA0 (by linarith only [hs27] : (0 : ℝ) ≤ 2 * Real.sqrt ((27 : ℝ) ^ d))
    linarith only [hs3, hs27, this]
  have hc20 : 0 ≤ c2 := by
    rw [hc2]
    have h1 : 0 ≤ comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) :=
      mul_nonneg hCP0 hs27
    have h2 : 0 ≤ unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) :=
      mul_nonneg humz0 hs27
    have h3 : 0 ≤ CA * (2 * (comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d)) +
        unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d)) :=
      mul_nonneg hCA0 (by linarith only [h1, h2])
    linarith only [hdsc0, h1, h3]
  have hc30 : 0 ≤ c3 := by
    rw [hc3]
    have := mul_nonneg hCA0 (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    linarith only [this]
  refine ⟨c1 + c2 + c3, by linarith only [hc10, hc20, hc30], ?_⟩
  intro n m x z i σ hnm hx hz hgeom hσ hover u h hzt
  -- ---------------------------------------------------------------- geometry
  set c' : Vec d := flushSubCentre z m n i σ with hc'
  have hKW' : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
    rw [hc']
    exact flushSubCube_subset_anchorWindow hnm hz i hσ
  have hV1W' : (fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
    image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom
  have hW'm : (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) ⊆ openCubeSet (originCube d m) :=
    Set.inter_subset_right
  have hW'meas : MeasurableSet
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) :=
    ((isOpen_image_add_openCubeSet_originCube z (n + 3)).inter
      (isOpen_openCubeSet (originCube d m))).measurableSet
  have hW'pos := volume_toReal_anchorWindow_pos (c' := c') hKW'
  have hW'top := volume_anchorWindow_ne_top (n + 3) m z
  have hK'meas := measurableSet_image_add_openCubeSet_originCube c' n
  have hK'pos := volume_toReal_image_add_openCubeSet_pos c' n
  have hK'top := volume_image_add_openCubeSet_ne_top c' n
  have : IsFiniteMeasure (volume.restrict
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_anchorWindow_ne_top (n + 3) m z)
  have hV1meas := measurableSet_image_add_openCubeSet_originCube
    (wellPlacedCentre x m (n + 2)) (n + 2)
  have hV1pos := volume_toReal_image_add_openCubeSet_pos
    (wellPlacedCentre x m (n + 2)) (n + 2)
  have hV1top := volume_image_add_openCubeSet_ne_top
    (wellPlacedCentre x m (n + 2)) (n + 2)
  have hK'm : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := hKW'.trans hW'm
  have hV1m : (fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆ openCubeSet (originCube d m) :=
    hV1W'.trans hW'm
  -- ---------------------------------------------------------- the comparators
  have hsubTS : translateSet c' (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet]
    exact hK'm
  obtain ⟨wu, rhou, hharmu, hvalu, hgradu, hboundu⟩ :=
    exists_deltaComparator_translatedCube (m := m) (j := n) (c := c') hsubTS u
  obtain ⟨wh, rhoh, hharmh, hvalh, _hgradh, hboundh⟩ :=
    exists_deltaComparator_translatedCube (m := m) (j := n) (c := c') hsubTS h
  have hKT : (fun y => c' + y) '' openCubeSet (originCube d n) =
      translateSet c' (openCubeSet (originCube d n)) :=
    image_add_eq_translateSet c' _
  have hNormSet : ∀ f : Vec d → ℝ,
      normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n)) f =
        normalizedL2On (translateSet c' (openCubeSet (originCube d n))) f :=
    fun f => congrArg (fun S => normalizedL2On S f) hKT
  have hpoin : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => u.toFun y - wu.toFun y) ≤
      comparatorPoincareConst d * (3 : ℝ) ^ n *
        ∑ i' : Fin d,
          normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
            (fun y => u.grad y i') := by
    rw [hNormSet]
    refine hboundu.trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun i' _ => (hNormSet _).symm
  refine ⟨wu, rhou, hharmu, hvalu, hgradu, ?_, hpoin⟩
  have : IsFiniteMeasure (volume.restrict
      ((fun y => c' + y) '' openCubeSet (originCube d n))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hK'top
  -- ------------------------------------------------- integrability inventory
  have inventory := residueInterface_comparatorIntegrability
    (K := translateSet c' (openCubeSet (originCube d n)))
    u h (by rw [← hKT]; exact hK'm) hV1m hW'm wu wh
  rw [congrArg (Measure.restrict volume) hKT.symm] at inventory
  obtain ⟨hmemU_K, hmemH_K, hmemU_V1, hmemH_V1, hmemU_W, hWU_K, hWH_K, hUWU, hHWH⟩ := inventory
  -- ---------------------------------------------------------------- the legs
  set XX : ℝ := normalizedL2On
    ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)))
    (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) with hXXdef
  set HH : ℝ := ∑ i' : Fin d,
    (eLpNorm (fun y => h.grad y i') 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHHdef
  have hXX0 : 0 ≤ XX := normalizedL2On_nonneg _ _
  have hHH0 : 0 ≤ HH :=
    Finset.sum_nonneg fun i' _ => ENNReal.toReal_nonneg
  have h3n0 : (0 : ℝ) ≤ (3 : ℝ) ^ n := le_of_lt (zpow_pos (by norm_num) n)
  -- L B: the u-mean transfer through the window
  have hB1 := abs_avg_cube_sub_window_le (m := m) hV1meas hV1W' hW'm hW'pos
    hV1pos hV1top hW'top
    (ratio_anchorWindow_coveringCube_le n m x z) u
  have hB2 := abs_avg_cube_sub_window_le (m := m) hK'meas hKW' hW'm hW'pos
    hK'pos hK'top hW'top
    (ratio_anchorWindow_scaleN_le n m z c') u
  have hlegB : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) u.toFun -
      volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun| ≤
      (Real.sqrt ((3 : ℝ) ^ d) + Real.sqrt ((27 : ℝ) ^ d)) * XX  := @residueInterface_estimate3
        (d) (n) (m) (x) (z) (i) (σ) (u)  (hB1) (hB2)
  -- L C: the datum step (proved)
  obtain ⟨stage_hlegC, stage_hgradHtrans, stage_hlegD3, stage_hlegA⟩ :=
    @residueInterface_comparisonBounds2 (d) (CA) (hCA) (hCP0) (n) (m) (x) (z) (i) (σ) (hnm) (hx)
      (hz) (hgeom) (hσ) (hover) (u) (h) (hzt)  (hKW') (hW'm) (hW'pos) (hK'pos) (hK'top) (by
        infer_instance) (hK'm) (wu) (rhou) (hharmu) (hvalu) (wh) (rhoh) (hharmh) (hvalh) (hboundh)
          (hKT) (hNormSet) (by infer_instance)  (h3n0)
  let hlegC := stage_hlegC
  have hgradHtrans : ∀ i' : Fin d,
      normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => h.grad y i') ≤
      Real.sqrt ((27 : ℝ) ^ d) *
        (eLpNorm (fun y => h.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := stage_hgradHtrans
  have hlegD3 : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => h.toFun y - wh.toFun y) ≤
      comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH := stage_hlegD3
  have hlegA : |volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => wu.toFun y - wh.toFun y)| ≤
      CA * normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => (wu.toFun y - wh.toFun y) -
          volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
            (fun y' => wu.toFun y' - wh.toFun y')) := stage_hlegA
  -- L D5: the oscillation of the comparator difference
  have hoscU : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => u.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          u.toFun) ≤ 2 * Real.sqrt ((27 : ℝ) ^ d) * XX :=
      normalizedL2On_sub_average_le_twice_sqrt_ratio
      hK'meas hKW' hW'm hW'pos hK'pos hK'top hW'top
      (ratio_anchorWindow_scaleN_le n m z c') u
  have hoscH : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => h.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          h.toFun) ≤
      unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n *
        HH  := normalizedL2On_sub_average_le_of_gradient_transport h hK'm hgradHtrans
  obtain ⟨hosc, hsplit⟩ :=
    @boundaryComparatorOscillationAndMeanBounds (d) (n) (m) (z) (i) (σ) (u) (h) (hK'meas) (hK'pos)
      (hK'top) (wu) (wh) (this) (hmemU_K) (hmemH_K) (hWU_K) (hWH_K) (hUWU) (hHWH)
  -- ------------------------------------------------------------ the assembly
  set A1 : ℝ := volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
    openCubeSet (originCube d (n + 2))) u.toFun with hA1
  set A2 : ℝ := volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
    openCubeSet (originCube d (n + 2))) h.toFun with hA2
  set B1 : ℝ := volumeAverage ((fun y => c' + y) ''
    openCubeSet (originCube d n)) u.toFun with hB1'
  set B2 : ℝ := volumeAverage ((fun y => c' + y) ''
    openCubeSet (originCube d n)) h.toFun with hB2'
  obtain ⟨htotal, hXXe, hfinal⟩ :=
    @residueInterface_comparisonBounds3 (d) (CA) (hCA0)    (hc10) (hc20) (hc30) (n)
      (m) (x) (z) (i) (σ) (u) (h) (hW'pos) (hW'top) (hK'top) (by infer_instance) (hV1top) (wu)
        (wh) (by infer_instance) (hmemU_K) (hmemH_K) (hmemU_V1) (hmemH_V1) (hmemU_W)
          (hXX0) (hHH0) (h3n0) (hlegD3) (hlegA) (hsplit)   (hoscU) (hlegB)
            (hoscH) (hlegC) (hosc)
  set NU : ℝ := normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
    (fun y => u.toFun y - wu.toFun y) with hNU
  set NH : ℝ := normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
    (fun y => h.toFun y - wh.toFun y) with hNH
  refine htotal.trans (hfinal.trans (le_of_eq ?_))
  rw [hXXe]


end

end Algsuperdiff.Section4.Provider.ExcessDecay
