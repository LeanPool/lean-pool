/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueDatumFlush

/-!
# ResidueScalarFlush

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary scalar at the **flush covering cube**, at the residue interface

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`ResidueInterface.exists_scalarControl_boundaryBranch_comparator` prices the
anchor's own scalar `|⨍_{V₁}(u−h)|`, `V₁ = wellPlacedCentre x m (n+2) +
□_{n+2}`.

```text
  K = wellPlacedCentre z m (n+2) + □_{n+2} .
```

`exists_scalarControl_flushCube_comparator` is the same estimate read at `K`:

```text
  |⨍_K (u−h)| ≤ C(d) · ( ‖u − (u)_{W'}‖_{L²(W')}
                       + 3^n · Σᵢ ‖∂ᵢh‖_{L²(W')}
                       + ‖u − w‖_{L²(K')} )
```

for the produced `Δ`-harmonic comparator `w = u + ρ`, `ρ ∈ H¹₀(K')`, together
with the `∀`-budget form `exists_scalarControl_flushCube_harmonicResidue`.

This is the exact statement that closes the `S`-loop of route 1: the
composition's `S`-companion is bounded by the composition's own legs plus its
own left-hand side.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The scalar at the flush cube, with the comparator produced -/

private abbrev residueScalarFlush_comparisonBounds2_statement : Prop :=
    ∀ (d : ℕ) (_ : (0 : ℝ) ≤ comparatorPoincareConst d) {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ}
      (_ : n + (2 : ℤ) ≤ m) (_ : z ∈ openCubeSet (originCube d m)) (_ : σ = (1 : ℝ) ∨ σ = (-1 : ℝ))
      (u h : H1Function (openCubeSet (originCube d m))),
      let c' : Vec d := flushSubCentre z m n i σ;
      ∀ (_ : c' = flushSubCentre z m n i σ),
        let cz : Vec d := wellPlacedCentre z m (n + (2 : ℤ));
        ∀ (_ : cz = wellPlacedCentre z m (n + (2 : ℤ)))
          (_ :
            (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆
              (fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))
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
          (_ : (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆ openCubeSet
            (originCube d m))
          (wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
          (_ :
            (normalizedL2On (translateSet c' (openCubeSet (originCube d n))) fun (y : Vec d) =>
              h.toFun y - wh.toFun y) ≤
              comparatorPoincareConst d * (3 : ℝ) ^ n *
                ∑ i : Fin d, normalizedL2On (translateSet c' (openCubeSet (originCube d n))) fun
                  (y : Vec d) => h.grad y i)
          (_ :
            ∀ (f : Vec d → ℝ),
              normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) f =
                normalizedL2On (translateSet c' (openCubeSet (originCube d n))) f)
          (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
            (originCube d n)))),
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
          ∀
            (_ :
              XX =
                normalizedL2On
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m))
                  fun (y : Vec d) =>
                  u.toFun y -
                    volumeAverage
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      u.toFun),
            let HH : ℝ :=
              ∑ i' : Fin d,
                (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                    (normalizedVolumeMeasureOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m)))).toReal;
            ∀
              (_ :
                HH =
                  ∑ i' : Fin d,
                    (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal)
              (_ : (0 : ℝ) ≤ (3 : ℝ) ^ n)
              (_ :
                |volumeAverage ((fun (y : Vec d) =>
                  cz + y) '' openCubeSet (originCube d (n + (2 : ℤ)))) u.toFun -
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
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m))
                          u.toFun)
              (_ :
                |volumeAverage ((fun (y : Vec d) =>
                  c' + y) '' openCubeSet (originCube d n)) u.toFun -
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
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m))
                          u.toFun),
              |volumeAverage ((fun (y : Vec d) =>
                cz + y) '' openCubeSet (originCube d (n + (2 : ℤ)))) u.toFun -
                      volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                        u.toFun| ≤
                  (√((3 : ℝ) ^ d) + √((27 : ℝ) ^ d)) * XX ∧
                |volumeAverage ((fun (y : Vec d) =>
                  cz + y) '' openCubeSet (originCube d (n + (2 : ℤ)))) h.toFun -
                        volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) h.toFun| ≤
                    datumStepConst d * (3 : ℝ) ^ n * HH ∧
                  (∀ (i' : Fin d),
                      (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                        n)) fun (y : Vec d) =>
                          h.grad y i') ≤
                        √((27 : ℝ) ^ d) *
                          (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                              (normalizedVolumeMeasureOn
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3
                                  : ℤ))) ∩
                                  openCubeSet (originCube d m)))).toReal) ∧
                    (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (y : Vec d) =>
                        h.toFun y - wh.toFun y) ≤
                      comparatorPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH

private abbrev residueScalarFlush_comparisonBounds3_statement : Prop :=
    ∀ (d : ℕ) (CA : ℝ) (_ : (0 : ℝ) ≤ CA),
      let c1 : ℝ := √((3 : ℝ) ^ d) + √((27 : ℝ) ^ d) + CA * ((2 : ℝ) * √((27 : ℝ) ^ d));
      ∀ (_ : c1 = √((3 : ℝ) ^ d) + √((27 : ℝ) ^ d) + CA * ((2 : ℝ) * √((27 : ℝ) ^ d))),
        let c2 : ℝ :=
          datumStepConst d + comparatorPoincareConst d * √((27 : ℝ) ^ d) +
            CA * ((2 : ℝ) * (comparatorPoincareConst d * √((27 : ℝ) ^ d)) +
              unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d));
        ∀
          (_ :
            c2 =
              datumStepConst d + comparatorPoincareConst d * √((27 : ℝ) ^ d) +
                CA *
                  ((2 : ℝ) * (comparatorPoincareConst d * √((27 : ℝ) ^ d)) +
                    unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d))),
          let c3 : ℝ := (1 : ℝ) + CA * (2 : ℝ);
          ∀ (_ : c3 = (1 : ℝ) + CA * (2 : ℝ)) (_ : (0 : ℝ) ≤ c1) (_ : (0 : ℝ) ≤ c2) (_ : (0 : ℝ) ≤
            c3) {n m : ℤ}
            {z : Vec d} {i : Fin d} {σ : ℝ} (u h : H1Function (openCubeSet (originCube d m))),
            let c' : Vec d := flushSubCentre z m n i σ;
            let cz : Vec d := wellPlacedCentre z m (n + (2 : ℤ));
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
                IsFiniteMeasure
                  (volume.restrict
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m))))
              (wu wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
              (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
                (originCube d n))))
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
              ∀
                (_ :
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
                          u.toFun),
                let HH : ℝ :=
                  ∑ i' : Fin d,
                    (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal;
                ∀ (_ : (0 : ℝ) ≤ XX) (_ : (0 : ℝ) ≤ HH) (_ : (0 : ℝ) ≤ (3 : ℝ) ^ n)
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
                              wu.toFun y' - wh.toFun y'),
                  let A1 : ℝ :=
                    volumeAverage ((fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n +
                      (2 : ℤ)))) u.toFun;
                  let A2 : ℝ :=
                    volumeAverage ((fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n +
                      (2 : ℤ)))) h.toFun;
                  let B1 : ℝ := volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                    (originCube d n)) u.toFun;
                  ∀
                    (_ :
                      (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                        n)) fun (y : Vec d) =>
                          u.toFun y - B1) ≤
                        (2 : ℝ) * √((27 : ℝ) ^ d) * XX)
                    (_ : |A1 - B1| ≤ (√((3 : ℝ) ^ d) + √((27 : ℝ) ^ d)) * XX),
                    let B2 : ℝ := volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                      (originCube d n)) h.toFun;
                    ∀
                      (_ :
                        (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) fun (y : Vec d) =>
                            h.toFun y - B2) ≤
                          unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH)
                      (_ : |A2 - B2| ≤ datumStepConst d * (3 : ℝ) ^ n * HH)
                      (_ :
                        |volumeAverage ((fun (y : Vec d) =>
                          cz + y) '' openCubeSet (originCube d (n + (2 : ℤ))))
                              fun (y : Vec d) => u.toFun y - h.toFun y| ≤
                          |A1 - B1| + |A2 - B2| +
                            |volumeAverage ((fun (y : Vec d) =>
                              c' + y) '' openCubeSet (originCube d n)) fun (y : Vec d) =>
                                u.toFun y - h.toFun y|),
                      let NU : ℝ :=
                        normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) fun (y : Vec d) =>
                          u.toFun y - wu.toFun y;
                      ∀
                        (_ :
                          |volumeAverage ((fun (y : Vec d) =>
                            flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n))
                                fun (x : Vec d) => u.toFun x - h.toFun x| ≤
                            (NU +
                                normalizedL2On
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  fun (x : Vec d) => wh.toFun x - h.toFun x) +
                              |volumeAverage
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  fun (x : Vec d) => wu.toFun x - wh.toFun x|)
                        (_ :
                          NU =
                            normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                              d n)) fun (y : Vec d) =>
                              u.toFun y - wu.toFun y),
                        let NH : ℝ :=
                          normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                            n)) fun (y : Vec d) =>
                            h.toFun y - wh.toFun y;
                        ∀ (_ : NH ≤ comparatorPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH)
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
                              ((2 : ℝ) * NU + (2 : ℝ) * NH +
                                  normalizedL2On
                                    ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                      openCubeSet (originCube d n))
                                    fun (x : Vec d) => u.toFun x - B1) +
                                normalizedL2On
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  fun (x : Vec d) => h.toFun x - B2)
                          (_ :
                            NH =
                              normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet
                                (originCube d n))
                                fun (y : Vec d) => h.toFun y - wh.toFun y),
                          |volumeAverage ((fun (y : Vec d) =>
                            cz + y) '' openCubeSet (originCube d (n + (2 : ℤ))))
                                  fun (y : Vec d) => u.toFun y - h.toFun y| ≤
                              c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU ∧
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
                              c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU ≤ (c1 + c2 + c3) * (XX +
                                (3 : ℝ) ^ n * HH + NU)

private abbrev residueScalarFlush_comparisonBounds6_statement : Prop :=
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
      (_ : (0 : ℝ) ≤ comparatorPoincareConst d) (_ : (0 : ℝ) ≤ unitMeanZeroPoincareConst d) {n m :
        ℤ} {z : Vec d}
      {i : Fin d} {σ : ℝ} (_ : n + (2 : ℤ) ≤ m) (_ : z ∈ openCubeSet (originCube d m)) (_ : σ = (1
        : ℝ) ∨ σ = (-1 : ℝ))
      (_ : wellPlacedHalfGap m (n + (2 : ℤ)) < σ * z i) (u h : H1Function (openCubeSet (originCube
        d m)))
      (_ : HasZeroTraceDifferenceOn (openCubeSet (originCube d m)) u h),
      let c' : Vec d := flushSubCentre z m n i σ;
      ∀ (_ : c' = flushSubCentre z m n i σ),
        let cz : Vec d := wellPlacedCentre z m (n + (2 : ℤ));
        ∀ (_ : cz = wellPlacedCentre z m (n + (2 : ℤ)))
          (_ :
            (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆
              (fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))
          (_ :
            (fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n + (2 : ℤ))) ⊆
              (fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))
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
            (volume : (a : Set (Vec d)) → ℝ≥0∞)
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m)) ≠
              ∞)
          (_ : MeasurableSet ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)))
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
          (_ : MeasurableSet ((fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n + (2 :
            ℤ)))))
          (_ :
            (0 : ℝ) <
              ((volume : (a : Set (Vec d)) → ℝ≥0∞)
                  ((fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n + (2 : ℤ))))).toReal)
          (_ :
            (volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => cz + y) '' openCubeSet
              (originCube d (n + (2 : ℤ)))) ≠
              ∞)
          (_ : (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆ openCubeSet
            (originCube d m))
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
                ∑ i : Fin d, normalizedL2On (translateSet c' (openCubeSet (originCube d n))) fun
                  (y : Vec d) => h.grad y i)
          (_ :
            (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) = translateSet c'
              (openCubeSet (originCube d n)))
          (_ :
            ∀ (f : Vec d → ℝ),
              normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) f =
                normalizedL2On (translateSet c' (openCubeSet (originCube d n))) f)
          (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
            (originCube d n))))
          (_ :
            MemLp u.toFun (2 : ℝ≥0∞)
              (volume.restrict ((fun (y : Vec d) => flushSubCentre z m n i σ + y) '' openCubeSet
                (originCube d n))))
          (_ :
            MemLp h.toFun (2 : ℝ≥0∞)
              (volume.restrict ((fun (y : Vec d) => flushSubCentre z m n i σ + y) '' openCubeSet
                (originCube d n))))
          (_ :
            MemLp u.toFun (2 : ℝ≥0∞)
              (volume.restrict
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))))
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
          ∀
            (_ :
              XX =
                normalizedL2On
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m))
                  fun (y : Vec d) =>
                  u.toFun y -
                    volumeAverage
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      u.toFun),
            let HH : ℝ :=
              ∑ i' : Fin d,
                (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                    (normalizedVolumeMeasureOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m)))).toReal;
            ∀
              (_ :
                HH =
                  ∑ i' : Fin d,
                    (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal)
              (_ : (0 : ℝ) ≤ (3 : ℝ) ^ n),
              |volumeAverage ((fun (y : Vec d) =>
                cz + y) '' openCubeSet (originCube d (n + (2 : ℤ)))) u.toFun -
                      volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                        u.toFun| ≤
                  (√((3 : ℝ) ^ d) + √((27 : ℝ) ^ d)) * XX ∧
                |volumeAverage ((fun (y : Vec d) =>
                  cz + y) '' openCubeSet (originCube d (n + (2 : ℤ)))) h.toFun -
                        volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) h.toFun| ≤
                    datumStepConst d * (3 : ℝ) ^ n * HH ∧
                  (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                    fun (y : Vec d) =>
                        h.toFun y - wh.toFun y) ≤
                      comparatorPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH ∧
                    (|volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (y : Vec d) =>
                            wu.toFun y - wh.toFun y| ≤
                        CA *
                          normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                            n)) fun (y : Vec d) =>
                            wu.toFun y - wh.toFun y -
                              volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                                (originCube d n))
                                fun (y' : Vec d) => wu.toFun y' - wh.toFun y') ∧
                      (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                        n)) fun (y : Vec d) =>
                            u.toFun y -
                              volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                                (originCube d n)) u.toFun) ≤
                          (2 : ℝ) * √((27 : ℝ) ^ d) * XX ∧
                        (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n)) fun (y : Vec d) =>
                              h.toFun y -
                                volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet
                                  (originCube d n)) h.toFun) ≤
                            unitMeanZeroPoincareConst d * √((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH ∧
                          ((normalizedL2On
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
                                    fun (x : Vec d) =>
                                    u.toFun x -
                                      volumeAverage
                                        ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                          openCubeSet (originCube d n))
                                        u.toFun) +
                                normalizedL2On
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  fun (x : Vec d) =>
                                  h.toFun x -
                                    volumeAverage
                                      ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                        openCubeSet (originCube d n))
                                      h.toFun) ∧
                            |volumeAverage
                                  ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                    openCubeSet (originCube d n))
                                  fun (x : Vec d) => u.toFun x - h.toFun x| ≤
                              ((normalizedL2On
                                    ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                      openCubeSet (originCube d n))
                                    fun (x : Vec d) => u.toFun x - wu.toFun x) +
                                  normalizedL2On
                                    ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                      openCubeSet (originCube d n))
                                    fun (x : Vec d) => wh.toFun x - h.toFun x) +
                                |volumeAverage
                                    ((fun (y : Vec d) => flushSubCentre z m n i σ + y) ''
                                      openCubeSet (originCube d n))
                                    fun (x : Vec d) => wu.toFun x - wh.toFun x|

private theorem residueScalarFlush_comparisonBounds1 :
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

private theorem residueScalarFlush_comparisonBounds2 :
  residueScalarFlush_comparisonBounds2_statement := by
  intro d hCP0 n m z i _ hnm hz hσ u h c' hc' cz hcz hKW' hW'm hW'pos hK'pos hK'top this hK'm wh
    hboundh hNormSet this XX hXXdef HH hHHdef h3n0 hB1 hB2
  have hlegB : |volumeAverage ((fun y => cz + y) ''
      openCubeSet (originCube d (n + 2))) u.toFun -
      volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun| ≤
      (Real.sqrt ((3 : ℝ) ^ d) + Real.sqrt ((27 : ℝ) ^ d)) * XX := by
    have htri := abs_sub (volumeAverage ((fun y => cz + y) ''
        openCubeSet (originCube d (n + 2))) u.toFun -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun)
      (volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun)
    have heq : volumeAverage ((fun y => cz + y) ''
        openCubeSet (originCube d (n + 2))) u.toFun -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun =
        (volumeAverage ((fun y => cz + y) ''
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
  -- L C: the datum step at the flush pair
  have hlegC : |volumeAverage ((fun y => cz + y) ''
      openCubeSet (originCube d (n + 2))) h.toFun -
      volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) h.toFun| ≤
      datumStepConst d * (3 : ℝ) ^ n * HH := by
    rw [hHHdef, hcz, hc']
    exact abs_volumeAverage_datum_flushPair_le hnm hz i hσ h
  -- L D3: the h-comparator error, transported to the window
  have hgradHtrans : ∀ i' : Fin d,
      normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => h.grad y i') ≤
      Real.sqrt ((27 : ℝ) ^ d) *
        (eLpNorm (fun y => h.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
    intro i'
    have hmemK := memLp_grad_of_subset h hK'm i'
    have hmemW := memLp_grad_of_subset h hW'm i'
    have hbridge : normalizedL2On ((fun y => c' + y) ''
        openCubeSet (originCube d n)) (fun y => h.grad y i') =
        (eLpNorm (fun y => h.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((fun y => c' + y) '' openCubeSet (originCube d n)))).toReal := by
      refine Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
        ?_ hK'top hmemK
      have := hK'pos
      by_contra hcon
      push Not at hcon
      have h0 : volume ((fun y => c' + y) '' openCubeSet (originCube d n)) = 0 :=
        le_antisymm hcon zero_le
      rw [h0] at this
      simp only [ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    rw [hbridge]
    refine toReal_eLpNorm_scaleN_cube_le_anchorWindow hKW' ?_
    exact (memLp_normalizedVolumeMeasureOn_of_restrict
      (by
        intro hcon
        rw [hcon] at hW'pos
        simp only [ENNReal.toReal_zero] at hW'pos
        exact lt_irrefl _ hW'pos) hmemW).eLpNorm_ne_top
  have hlegD3 : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => h.toFun y - wh.toFun y) ≤
      comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH := by
    rw [hNormSet]
    refine hboundh.trans ?_
    have hsum : ∑ i' : Fin d,
        normalizedL2On (translateSet c' (openCubeSet (originCube d n)))
          (fun y => h.grad y i') ≤ Real.sqrt ((27 : ℝ) ^ d) * HH := by
      rw [hHHdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun i' _ => ?_
      rw [← hNormSet]
      exact hgradHtrans i'
    calc comparatorPoincareConst d * (3 : ℝ) ^ n *
        ∑ i' : Fin d,
          normalizedL2On (translateSet c' (openCubeSet (originCube d n)))
            (fun y => h.grad y i')
        ≤ comparatorPoincareConst d * (3 : ℝ) ^ n *
            (Real.sqrt ((27 : ℝ) ^ d) * HH) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hCP0 h3n0)
      _ = comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n *
            HH := by ring
  exact ⟨hlegB, hlegC, hgradHtrans, hlegD3⟩

private theorem residueScalarFlush_comparisonBounds3 :
  residueScalarFlush_comparisonBounds3_statement := by
  intro d CA hCA0 c1 hc1 c2 hc2 c3 hc3 hc10 hc20 hc30 n m z _ _ u h c' cz hW'pos hW'top this wu wh
    this hmemU_W XX hXXdef HH hXX0 hHH0 h3n0 hlegA A1 A2 B1 hoscU hlegB B2 hoscH hlegC htri0 NU
      hsplit hNU NH hlegD3 hosc hNH
  have hNU0 : 0 ≤ NU := normalizedL2On_nonneg _ _
  have hNH0 : 0 ≤ NH := normalizedL2On_nonneg _ _
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
  have hoscbound : normalizedL2On ((fun y => c' + y) ''
      openCubeSet (originCube d n))
      (fun y => (wu.toFun y - wh.toFun y) -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          (fun y' => wu.toFun y' - wh.toFun y')) ≤
      2 * NU + 2 * NH + 2 * Real.sqrt ((27 : ℝ) ^ d) * XX +
        unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n *
          HH := by
    have h1 := hosc
    have h2 : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => u.toFun y -
          volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
            u.toFun) ≤ 2 * Real.sqrt ((27 : ℝ) ^ d) * XX := hoscU
    have h3 := hoscH
    linarith only [h1, h2, h3]
  have hlegAfull : |volumeAverage ((fun y => c' + y) ''
      openCubeSet (originCube d n)) (fun y => wu.toFun y - wh.toFun y)| ≤
      CA * (2 * NU + 2 * NH + 2 * Real.sqrt ((27 : ℝ) ^ d) * XX +
        unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n *
          HH) := by
    refine hlegA.trans ?_
    exact mul_le_mul_of_nonneg_left hoscbound hCA0
  have hNHb : NH ≤ comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) *
      (3 : ℝ) ^ n * HH := hlegD3
  have hAB1 : |A1 - B1| ≤
      (Real.sqrt ((3 : ℝ) ^ d) + Real.sqrt ((27 : ℝ) ^ d)) * XX := hlegB
  have hAB2 : |A2 - B2| ≤ datumStepConst d * (3 : ℝ) ^ n * HH := hlegC
  have htotal : |volumeAverage ((fun y => cz + y) ''
      openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - h.toFun y)| ≤
      c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU := by
    have hCAmul2 : CA * (2 * NH) ≤ CA * (2 * (comparatorPoincareConst d *
        Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH)) := by
      refine mul_le_mul_of_nonneg_left ?_ hCA0
      linarith only [hNHb]
    rw [hc1, hc2, hc3]
    have hx1 := htri0
    have hx2 := hsplit'
    have hx3 := hlegAfull
    nlinarith only [hx1, hx2, hx3, hAB1, hAB2, hNHb, hCAmul2,
      hCA0, hNU0, hNH0]
  have hXXe : XX = (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal := by
    rw [hXXdef]
    refine Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
      ?_ hW'top (hmemU_W.sub (memLp_const _))
    by_contra hcon
    push Not at hcon
    have h0 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) = 0 := le_antisymm hcon zero_le
    have := hW'pos
    rw [h0] at this
    simp only [ENNReal.toReal_zero] at this
    exact lt_irrefl _ this
  have hfinal : c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU ≤
      (c1 + c2 + c3) * (XX + (3 : ℝ) ^ n * HH + NU) := by
    have t1 : 0 ≤ (3 : ℝ) ^ n * HH := mul_nonneg h3n0 hHH0
    nlinarith only [hc10, hc20, hc30, hXX0, t1, hNU0]
  exact ⟨htotal, hXXe, hfinal⟩

private theorem residueScalarFlush_comparisonBounds4 :
    ∀ (d : ℕ) {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ} (u h : H1Function (openCubeSet (originCube
      d m))),
      let c' : Vec d := flushSubCentre z m n i σ;
      let cz : Vec d := wellPlacedCentre z m (n + (2 : ℤ));
      ∀
        (_ :
          (fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩ openCubeSet
            (originCube d m) ⊆
            openCubeSet (originCube d m))
        (_ : (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) ⊆ openCubeSet (originCube
          d m))
        (_ : (fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n + (2 : ℤ))) ⊆ openCubeSet
          (originCube d m))
        (wu : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (rhou : H10Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : ∀ (y : Vec d), wu.toFun y = u.toFun y + rhou.toFun y)
        (wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (rhoh : H10Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : ∀ (y : Vec d), wh.toFun y = h.toFun y + rhoh.toFun y)
        (_ :
          (fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n) = translateSet c'
            (openCubeSet (originCube d n))),
        MemLp u.toFun (2 : ℝ≥0∞) (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n))) ∧
          MemLp h.toFun (2 : ℝ≥0∞) (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
            (originCube d n))) ∧
            MemLp u.toFun (2 : ℝ≥0∞)
                (volume.restrict ((fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n + (2
                  : ℤ))))) ∧
              MemLp h.toFun (2 : ℝ≥0∞)
                  (volume.restrict ((fun (y : Vec d) => cz + y) '' openCubeSet (originCube d (n +
                    (2 : ℤ))))) ∧
                MemLp u.toFun (2 : ℝ≥0∞)
                    (volume.restrict
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))) ∧
                  MemLp (fun (y : Vec d) => wu.toFun y) (2 : ℝ≥0∞)
                      (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                        n))) ∧
                    MemLp (fun (y : Vec d) => wh.toFun y) (2 : ℝ≥0∞)
                        (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d
                          n))) ∧
                      MemLp (fun (y : Vec d) => u.toFun y - wu.toFun y) (2 : ℝ≥0∞)
                          (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                            d n))) ∧
                        MemLp (fun (y : Vec d) => h.toFun y - wh.toFun y) (2 : ℝ≥0∞)
                          (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                            d n))) := by
  intro d n _ _ _ _ u h c' _ hW'm hK'm hV1m wu rhou hvalu wh rhoh hvalh hKT
  have hmemU_K := memLp_toFun_of_subset u hK'm
  have hmemH_K := memLp_toFun_of_subset h hK'm
  have hmemU_V1 := memLp_toFun_of_subset u hV1m
  have hmemH_V1 := memLp_toFun_of_subset h hV1m
  have hmemU_W := memLp_toFun_of_subset u hW'm
  have hRhoU : MemLp (fun y => rhou.toH1Function.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := by
    rw [hKT]
    exact rhou.toH1Function.memL2
  have hRhoH : MemLp (fun y => rhoh.toH1Function.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := by
    rw [hKT]
    exact rhoh.toH1Function.memL2
  have hWU_K : MemLp (fun y => wu.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := by
    have hfun : (fun y => wu.toFun y) =
        fun y => u.toFun y + rhou.toH1Function.toFun y := by
      funext y
      exact hvalu y
    rw [hfun]
    exact hmemU_K.add hRhoU
  have hWH_K : MemLp (fun y => wh.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := by
    have hfun : (fun y => wh.toFun y) =
        fun y => h.toFun y + rhoh.toH1Function.toFun y := by
      funext y
      exact hvalh y
    rw [hfun]
    exact hmemH_K.add hRhoH
  have hUWU : MemLp (fun y => u.toFun y - wu.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) :=
    hmemU_K.sub hWU_K
  have hHWH : MemLp (fun y => h.toFun y - wh.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) :=
    hmemH_K.sub hWH_K
  exact ⟨hmemU_K, hmemH_K, hmemU_V1, hmemH_V1, hmemU_W, hWU_K, hWH_K, hUWU, hHWH⟩

private theorem residueScalarFlush_comparisonBounds5 :
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
      {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ} (_ : n + (2 : ℤ) ≤ m) (_ : σ = (1 : ℝ) ∨ σ = (-1 :
        ℝ))
      (_ : wellPlacedHalfGap m (n + (2 : ℤ)) < σ * z i) (u h : H1Function (openCubeSet (originCube
        d m))),
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
          (volume : (a : Set (Vec d)) → ℝ≥0∞)
              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m)) ≠
            ∞)
        (_ : MeasurableSet ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)))
        (_ :
          (0 : ℝ) <
            ((volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
              (originCube d n))).toReal)
        (_ : (volume : (a : Set (Vec d)) → ℝ≥0∞) ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n)) ≠ ∞)
        (wu : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (rhou : H10Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : IsWeaklyHarmonicOn (translateSet c' (openCubeSet (originCube d n))) wu)
        (_ : ∀ (y : Vec d), wu.toFun y = u.toFun y + rhou.toFun y)
        (wh : H1Function (translateSet c' (openCubeSet (originCube d n))))
        (rhoh : H10Function (translateSet c' (openCubeSet (originCube d n))))
        (_ : IsWeaklyHarmonicOn (translateSet c' (openCubeSet (originCube d n))) wh)
        (_ : ∀ (y : Vec d), wh.toFun y = h.toFun y + rhoh.toFun y)
        (_ : IsFiniteMeasure (volume.restrict ((fun (y : Vec d) => c' + y) '' openCubeSet
          (originCube d n))))
        (_ :
          MemLp u.toFun (2 : ℝ≥0∞)
            (volume.restrict ((fun (y : Vec d) => flushSubCentre z m n i σ + y) '' openCubeSet
              (originCube d n))))
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
        ∀
          (_ :
            XX =
              normalizedL2On
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))
                fun (y : Vec d) =>
                u.toFun y -
                  volumeAverage
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m))
                    u.toFun)
          (_ : truncatedWindow c' m n = translateSet c' (openCubeSet (originCube d n)))
          (w0 : H10Function (openCubeSet (originCube d m))) (_ : ∀ (x : Vec d), u.toFun x =
            h.toFun x + w0.toFun x),
          (|volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (y :
            Vec d) =>
                  wu.toFun y - wh.toFun y| ≤
              CA *
                normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun
                  (y : Vec d) =>
                  wu.toFun y - wh.toFun y -
                    volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n))
                      fun (y' : Vec d) =>
                      wu.toFun y' - wh.toFun y') ∧
            (normalizedL2On ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube d n)) fun (y :
              Vec d) =>
                u.toFun y - volumeAverage ((fun (y : Vec d) => c' + y) '' openCubeSet (originCube
                  d n)) u.toFun) ≤
              (2 : ℝ) * √((27 : ℝ) ^ d) * XX := by
  classical
  intro d CA hCA n m z _ _ hnm hσ hover u _ c' hKW' hW'm hW'pos hW'top hK'meas hK'pos hK'top wu
    rhou hharmu hvalu wh rhoh hharmh hvalh _ hmemU_K hmemU_W XX hXXdef hTWts w0 hw0val
  have hlegA : |volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => wu.toFun y - wh.toFun y)| ≤
      CA * normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => (wu.toFun y - wh.toFun y) -
          volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
            (fun y' => wu.toFun y' - wh.toFun y')) := by
    set vd : H1Function (truncatedWindow c' m n) :=
      h1FunctionOfSetEq hTWts.symm (wu - wh) with hvd
    have hvdval : ∀ y, vd.toFun y = wu.toFun y - wh.toFun y := by
      intro y
      rw [hvd]
      have h1 : (h1FunctionOfSetEq hTWts.symm (wu - wh)).toFun = (wu - wh).toFun :=
        h1FunctionOfSetEq_toFun hTWts.symm (wu - wh)
      rw [h1, H1Function.sub_toFun]
    have hharmd : IsWeaklyHarmonicOn (truncatedWindow c' m n) vd := by
      rw [hvd]
      exact isWeaklyHarmonicOn_h1FunctionOfSetEq hTWts.symm
        (isWeaklyHarmonicOn_sub_h1 hharmu hharmh)
    have hvald : ∀ y, vd.toFun y = w0.toH1Function.toFun y +
        (h10FunctionOfSetEq hTWts.symm rhou).toH1Function.toFun y -
        (h10FunctionOfSetEq hTWts.symm rhoh).toH1Function.toFun y := by
      intro y
      rw [hvdval y]
      have h1 : (h10FunctionOfSetEq hTWts.symm rhou).toH1Function.toFun =
          rhou.toH1Function.toFun := h10FunctionOfSetEq_toFun hTWts.symm rhou
      have h2 : (h10FunctionOfSetEq hTWts.symm rhoh).toH1Function.toFun =
          rhoh.toH1Function.toFun := h10FunctionOfSetEq_toFun hTWts.symm rhoh
      rw [h1, h2]
      have hu := hvalu y
      have hh := hvalh y
      have hw0 := hw0val y
      linarith only [hu, hh, hw0]
    have hA := hCA hnm hσ hover vd hharmd w0
      (h10FunctionOfSetEq hTWts.symm rhou) (h10FunctionOfSetEq hTWts.symm rhoh)
      hvald
    have hfun : vd.toFun = fun y => wu.toFun y - wh.toFun y := by
      funext y
      exact hvdval y
    simp only [hfun] at hA
    exact hA
  -- L D5: the oscillation of the comparator difference
  have hoscU : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => u.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          u.toFun) ≤ 2 * Real.sqrt ((27 : ℝ) ^ d) * XX := by
    set aW : ℝ := volumeAverage ((((fun y' => z + y') ''
        openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) u.toFun with haW
    have hgap : |volumeAverage ((fun y => c' + y) ''
        openCubeSet (originCube d n)) u.toFun - aW| ≤
        Real.sqrt ((27 : ℝ) ^ d) * XX := by
      rw [hXXdef, haW]
      exact abs_avg_cube_sub_window_le (m := m) hK'meas hKW' hW'm hW'pos hK'pos
        hK'top hW'top (ratio_anchorWindow_scaleN_le n m z c') u
    have htransport : normalizedL2On ((fun y => c' + y) ''
        openCubeSet (originCube d n)) (fun y => u.toFun y - aW) ≤
        Real.sqrt ((27 : ℝ) ^ d) * XX := by
      have hsq : IntegrableOn (fun y => (u.toFun y - aW) ^ 2)
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) volume :=
        integrableOn_sub_const_sq hW'top hmemU_W aW
      have h1 := normalizedL2On_le_of_subset (W := (((fun y' => z + y') ''
          openCubeSet (originCube d (n + 3))) ∩ openCubeSet (originCube d m)))
        (W' := (fun y => c' + y) '' openCubeSet (originCube d n))
        (f := fun y => u.toFun y - aW) hKW' hW'pos hK'pos hsq
      refine h1.trans ?_
      rw [hXXdef, haW]
      exact mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (ratio_anchorWindow_scaleN_le n m z c'))
        (normalizedL2On_nonneg _ _)
    have hdecomp : (fun y => u.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          u.toFun) = fun y => (u.toFun y - aW) +
        (aW - volumeAverage ((fun y => c' + y) ''
          openCubeSet (originCube d n)) u.toFun) := by
      funext y
      ring
    have hmem1 : MemLp (fun y => u.toFun y - aW) 2
        (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) :=
      hmemU_K.sub (memLp_const aW)
    have hmem2 : MemLp (fun _ : Vec d => aW -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          u.toFun) 2
        (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) :=
      memLp_const _
    rw [hdecomp]
    have hmink := normalizedL2On_add_le hmem1 hmem2
    refine hmink.trans ?_
    have hconst : normalizedL2On ((fun y => c' + y) ''
        openCubeSet (originCube d n))
        (fun _ => aW - volumeAverage ((fun y => c' + y) ''
          openCubeSet (originCube d n)) u.toFun) =
        |aW - volumeAverage ((fun y => c' + y) ''
          openCubeSet (originCube d n)) u.toFun| :=
      normalizedL2On_const_abs hK'pos _
    rw [hconst]
    have habs : |aW - volumeAverage ((fun y => c' + y) ''
        openCubeSet (originCube d n)) u.toFun| =
        |volumeAverage ((fun y => c' + y) ''
          openCubeSet (originCube d n)) u.toFun - aW| := abs_sub_comm _ _
    rw [habs]
    linarith only [htransport, hgap]
  exact ⟨hlegA, hoscU⟩

private theorem residueScalarFlush_comparisonBounds6 :
  residueScalarFlush_comparisonBounds6_statement := by
  classical
  intro d CA hCA hCP0 humz0 n m z i σ hnm hz hσ hover u h hzt c' hc' cz hcz hKW' hV1W' hW'm hW'pos
    hW'top hK'meas hK'pos hK'top this hV1meas hV1pos hV1top hK'm wu rhou hharmu hvalu wh rhoh
      hharmh hvalh hboundh hKT hNormSet this hmemU_K hmemH_K hmemU_W hWU_K hWH_K hUWU hHWH XX
        hXXdef HH hHHdef h3n0
  have hB1 := abs_avg_cube_sub_window_le (m := m) hV1meas hV1W' hW'm hW'pos
    hV1pos hV1top hW'top
    (ratio_anchorWindow_coveringCube_le n m z z) u
  have hB2 := abs_avg_cube_sub_window_le (m := m) hK'meas hKW' hW'm hW'pos
    hK'pos hK'top hW'top
    (ratio_anchorWindow_scaleN_le n m z c') u
  obtain ⟨hlegB, hlegC, hgradHtrans, hlegD3⟩ :=
    (show (|volumeAverage ((fun y => cz + y) ''
      openCubeSet (originCube d (n + 2))) u.toFun -
      volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) u.toFun| ≤
      (Real.sqrt ((3 : ℝ) ^ d) + Real.sqrt ((27 : ℝ) ^ d)) * XX) ∧ (|volumeAverage ((fun y => cz +
        y) ''
      openCubeSet (originCube d (n + 2))) h.toFun -
      volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n)) h.toFun| ≤
      datumStepConst d * (3 : ℝ) ^ n * HH) ∧ (∀ i' : Fin d,
      normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => h.grad y i') ≤
      Real.sqrt ((27 : ℝ) ^ d) *
        (eLpNorm (fun y => h.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal) ∧ (normalizedL2On ((fun y => c' + y) ''
                openCubeSet (originCube d n))
      (fun y => h.toFun y - wh.toFun y) ≤
      comparatorPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n * HH) from
      @residueScalarFlush_comparisonBounds2 (d) (hCP0) (n) (m) (z) (i) (σ) (hnm) (hz) (hσ) (u) (h)
        (hc') (hcz) (hKW') (hW'm) (hW'pos) (hK'pos) (hK'top) (by infer_instance) (hK'm) (wh)
          (hboundh) (hNormSet) (by infer_instance) (hXXdef) (hHHdef) (h3n0) (hB1) (hB2))
  -- L A: the comparator-difference mean, through the odd-harmonic glue
  have hTW : truncatedWindow c' m n =
      (fun y => c' + y) '' openCubeSet (originCube d n) := by
    rw [hc']
    exact truncatedWindow_eq_flushSubCube hnm z i hσ
  have hTWts : truncatedWindow c' m n =
      translateSet c' (openCubeSet (originCube d n)) := by
    rw [hTW, hKT]
  obtain ⟨w0, hw0val, _hw0grad⟩ := hzt
  obtain ⟨hlegA, hoscU⟩ :=
    (show (|volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => wu.toFun y - wh.toFun y)| ≤
      CA * normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
        (fun y => (wu.toFun y - wh.toFun y) -
          volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
            (fun y' => wu.toFun y' - wh.toFun y'))) ∧ (normalizedL2On ((fun y => c' + y) ''
              openCubeSet (originCube d n))
      (fun y => u.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          u.toFun) ≤ 2 * Real.sqrt ((27 : ℝ) ^ d) * XX) from
      @residueScalarFlush_comparisonBounds5 (d) (CA) (hCA) (n) (m) (z) (i) (σ) (hnm) (hσ) (hover)
        (u) (h) (hKW') (hW'm) (hW'pos) (hW'top) (hK'meas) (hK'pos) (hK'top) (wu) (rhou) (hharmu)
          (hvalu) (wh) (rhoh) (hharmh) (hvalh) (by infer_instance) (hmemU_K) (hmemU_W) (hXXdef)
            (hTWts) (w0) (hw0val))
  have hoscH : normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
      (fun y => h.toFun y -
        volumeAverage ((fun y => c' + y) '' openCubeSet (originCube d n))
          h.toFun) ≤
      unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n *
        HH := by
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
        Real.sqrt ((27 : ℝ) ^ d) * HH := by
      rw [hHHdef, Finset.mul_sum]
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
            (Real.sqrt ((27 : ℝ) ^ d) * HH) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg humz0 h3n0)
      _ = unitMeanZeroPoincareConst d * Real.sqrt ((27 : ℝ) ^ d) * (3 : ℝ) ^ n *
            HH := by ring
  obtain ⟨hosc, hsplit⟩ :=
    @residueScalarFlush_comparisonBounds1 (d) (n) (m) (z) (i) (σ) (u) (h) (hK'meas) (hK'pos)
      (hK'top) (wu) (wh) (this) (hmemU_K) (hmemH_K) (hWU_K) (hWH_K) (hUWU) (hHWH)
  exact ⟨hlegB, hlegC, hlegD3, hlegA, hoscU, hoscH, hosc, hsplit⟩

/-- **The boundary scalar at the flush cube `K`, with the residue exhibited as
the harmonic-approximation error at `K'`.**

The binder-free sibling of
`ResidueInterface.exists_scalarControl_boundaryBranch_comparator`: the
anchor's geometry binder and its child centre `x` do not occur. -/
theorem exists_scalarControl_flushCube_comparator (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ},
        n + 2 ≤ m →
        z ∈ openCubeSet (originCube d m) →
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
          |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
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
                (fun y => u.toFun y - w.toFun y)) := by
  classical
  obtain ⟨CA, hCA0, hCA⟩ :=
    exists_abs_volumeAverage_le_normalizedL2On_flushComparator d
  have hCP0 : 0 ≤ comparatorPoincareConst d := comparatorPoincareConst_nonneg d
  have hdsc0 : 0 ≤ datumStepConst d := datumStepConst_nonneg d
  have humz0 : 0 ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have hs3 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hs27 : (0 : ℝ) ≤ Real.sqrt ((27 : ℝ) ^ d) := Real.sqrt_nonneg _
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
  intro n m z i σ hnm hz hσ hover u h hzt
  -- ---------------------------------------------------------------- geometry
  set c' : Vec d := flushSubCentre z m n i σ with hc'
  set cz : Vec d := wellPlacedCentre z m (n + 2) with hcz
  have hKW' : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
    rw [hc']
    exact flushSubCube_subset_anchorWindow hnm hz i hσ
  have hV1W' : (fun y => cz + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
    rw [hcz]
    exact image_add_wellPlacedCentre_z_subset_anchorWindow hnm hz
  have hW'm : (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) ⊆ openCubeSet (originCube d m) :=
    Set.inter_subset_right
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
  have hV1meas := measurableSet_image_add_openCubeSet_originCube cz (n + 2)
  have hV1pos := volume_toReal_image_add_openCubeSet_pos cz (n + 2)
  have hV1top := volume_image_add_openCubeSet_ne_top cz (n + 2)
  have hK'm : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := hKW'.trans hW'm
  have hV1m : (fun y => cz + y) '' openCubeSet (originCube d (n + 2)) ⊆
      openCubeSet (originCube d m) := hV1W'.trans hW'm
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
  refine ⟨wu, rhou, hharmu, hvalu, hgradu, ?_⟩
  have : IsFiniteMeasure (volume.restrict
      ((fun y => c' + y) '' openCubeSet (originCube d n))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hK'top
  -- ------------------------------------------------- integrability inventory
  obtain ⟨stage_hmemU_K, stage_hmemH_K, stage_hmemU_V1, stage_hmemH_V1, stage_hmemU_W,
    stage_hWU_K, stage_hWH_K, stage_hUWU, stage_hHWH⟩ :=
    @residueScalarFlush_comparisonBounds4 (d) (n) (m) (z) (i) (σ) (u) (h) (hW'm) (hK'm) (hV1m)
      (wu) (rhou) (hvalu) (wh) (rhoh) (hvalh) (hKT)
  have hmemU_K := stage_hmemU_K
  have hmemH_K := stage_hmemH_K
  have hmemU_V1 := stage_hmemU_V1
  have hmemH_V1 := stage_hmemH_V1
  have hmemU_W := stage_hmemU_W
  have hWU_K : MemLp (fun y => wu.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := stage_hWU_K
  have hWH_K : MemLp (fun y => wh.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := stage_hWH_K
  have hUWU : MemLp (fun y => u.toFun y - wu.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := stage_hUWU
  have hHWH : MemLp (fun y => h.toFun y - wh.toFun y) 2
      (volume.restrict ((fun y => c' + y) '' openCubeSet (originCube d n))) := stage_hHWH
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
  obtain ⟨hlegB, hlegC, hlegD3, hlegA, hoscU, hoscH, hosc, hsplit⟩ :=
    @residueScalarFlush_comparisonBounds6 (d) (CA) (hCA) (hCP0) (humz0) (n) (m) (z) (i) (σ) (hnm)
      (hz) (hσ) (hover) (u) (h) (hzt) (hc') (hcz) (hKW') (hV1W') (hW'm) (hW'pos) (hW'top)
        (hK'meas) (hK'pos) (hK'top) (by infer_instance) (hV1meas) (hV1pos) (hV1top) (hK'm) (wu)
          (rhou) (hharmu) (hvalu) (wh) (rhoh) (hharmh) (hvalh) (hboundh) (hKT) (hNormSet) (by
            infer_instance) (hmemU_K) (hmemH_K) (hmemU_W) (hWU_K) (hWH_K) (hUWU) (hHWH) (hXXdef)
              (hHHdef) (h3n0)
  -- ------------------------------------------------------------ the assembly
  set A1 : ℝ := volumeAverage ((fun y => cz + y) ''
    openCubeSet (originCube d (n + 2))) u.toFun with hA1
  set A2 : ℝ := volumeAverage ((fun y => cz + y) ''
    openCubeSet (originCube d (n + 2))) h.toFun with hA2
  set B1 : ℝ := volumeAverage ((fun y => c' + y) ''
    openCubeSet (originCube d n)) u.toFun with hB1'
  set B2 : ℝ := volumeAverage ((fun y => c' + y) ''
    openCubeSet (originCube d n)) h.toFun with hB2'
  have hmeanV1 : volumeAverage ((fun y => cz + y) ''
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
  have htri0 : |volumeAverage ((fun y => cz + y) ''
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
  set NU : ℝ := normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
    (fun y => u.toFun y - wu.toFun y) with hNU
  set NH : ℝ := normalizedL2On ((fun y => c' + y) '' openCubeSet (originCube d n))
    (fun y => h.toFun y - wh.toFun y) with hNH
  obtain ⟨htotal, hXXe, hfinal⟩ :=
    (show (|volumeAverage ((fun y => cz + y) ''
      openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - h.toFun y)| ≤
      c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU) ∧ (XX = (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal) ∧ (c1 * XX + c2 * ((3 : ℝ) ^ n * HH) + c3 * NU ≤
      (c1 + c2 + c3) * (XX + (3 : ℝ) ^ n * HH + NU)) from
      @residueScalarFlush_comparisonBounds3 (d) (CA) (hCA0) (hc1) (hc2) (hc3) (hc10) (hc20) (hc30)
        (n) (m) (z) (i) (σ) (u) (h) (hW'pos) (hW'top) (by infer_instance) (wu) (wh) (by
          infer_instance) (hmemU_W) (hXXdef) (hXX0) (hHH0) (h3n0) (hlegA) (hoscU) (hlegB) (hoscH)
            (hlegC) (htri0) (hsplit) (hNU) (hlegD3) (hosc) (hNH))
  refine htotal.trans (hfinal.trans (le_of_eq ?_))
  rw [hXXe]

/-! ## 2. The `∀`-budget form -/

/-- **The boundary scalar at the flush cube, at an abstract residue budget.**

`R` is any real dominating the harmonic-approximation error at `K'` for every
`Δ`-harmonic comparator of `u` there.  This is the form the route-1 loop
consumes. -/
theorem exists_scalarControl_flushCube_harmonicResidue (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ},
        n + 2 ≤ m →
        z ∈ openCubeSet (originCube d m) →
        (σ = 1 ∨ σ = -1) →
        wellPlacedHalfGap m (n + 2) < σ * z i →
        ∀ u h : H1Function (openCubeSet (originCube d m)),
          Support.HasZeroTraceDifferenceOn (openCubeSet (originCube d m)) u h →
          ∀ R : ℝ,
          (∀ (w : H1Function (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n))))
             (rho : H10Function (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n)))),
            IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n))) w →
            (∀ y, w.toFun y = u.toFun y + rho.toH1Function.toFun y) →
            (∀ y, w.grad y = u.grad y + rho.toH1Function.grad y) →
            normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
                openCubeSet (originCube d n))
              (fun y => u.toFun y - w.toFun y) ≤ R) →
          |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
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
              R) := by
  classical
  obtain ⟨C, hC0, hmain⟩ := exists_scalarControl_flushCube_comparator d
  refine ⟨C, hC0, ?_⟩
  intro n m z i σ hnm hz hσ hover u h hzt R hres
  obtain ⟨w, rho, hharm, hval, hgrad, hbound⟩ := hmain hnm hz hσ hover u h hzt
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  have hR := hres w rho hharm hval hgrad
  linarith only [hR]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
