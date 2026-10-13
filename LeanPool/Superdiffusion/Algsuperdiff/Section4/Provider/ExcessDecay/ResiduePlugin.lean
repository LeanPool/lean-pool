/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueRouteOne
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueScalarFlush
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueAbsorption

/-!
# ResiduePlugin

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The plug-in: route 1 closed at an explicit `ε`-smallness

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`ResidueRouteOne.exists_flushResidue_route1_composed` prices the harmonic
approximation residue at the flush sub-cube on five legs, the first and the last
carrying `s^{-4}·𝓔` and the last being the boundary scalar `S` at the flush cube
`K` — a self-consistency loop.  `ResidueScalarFlush` closes that loop: it
bounds `S` by the same window legs plus the residue itself.

`exists_flushResidue_le_displayLegs_of_epsPin` runs the loop under **one**
explicit, disclosed hypothesis

```text
  hepsPin :  A · 𝓔  ≤  s⁴ ,        𝓔 = fluxCorrectedErrorRepresentative M L (n+3)
                                        ⟨s/8⟩ (translate z ω) ,
```

with `A > 0` produced by the theorem, and delivers, for **every** `Δ`-harmonic
comparator `w = u + ρ`, `ρ ∈ H¹₀(K')`,

```text
  ‖u − w‖_{L²(K')} ≤ K · ( ‖u − (u)_{W'}‖_{L²(W')}
                          + s^{-6}·3^{n}·‖∇h‖_{L²(W')}
                          + s^{-6}·3^{(1+s)n}·[∇h]_{H^s(W')}
                          + s^{-7}·σ_{n+3}^{-1}·3^{(1+s)n}·[g]_{H^s(W')} ) .
```

Nothing in this module asserts it.

## The room, honestly stated (a correction to's table)

's legal-producer contract asks for the residue at the four `s`-powers `(0, 0,
−2, −3σ^{-1})`.  Route 1 does **not** meet that contract, and cannot:

* the `3^n‖∇h‖` and `3^{(1+s)n}[∇h]` legs arrive at `s^{-6}`, and the
  `3^{(1+s)n}[g]` leg at `s^{-7}σ^{-1}` — *the frozen display's own powers*;
* the `[g]` leg's dominant part comes from the coarse-graining **force** term
  and the interior correction leg, neither of which carries `𝓔`, so no
  `ε`-smallness improves it.

The contract is nevertheless sufficient, not necessary.  **The pin is therefore
consumed twice** — once to resolve the `S`-loop here, once downstream to absorb
the residue's own `s`-powers.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The loop-resolution arithmetic -/

/-! ## 2. The plug-in corollary -/

private theorem residuePlugin_comparisonBounds1 :
    ∀ (d : ℕ) (CS : ℝ)
      (_ :
        ∀ {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ},
          n + (2 : ℤ) ≤ m →
            z ∈ openCubeSet (originCube d m) →
              σ = (1 : ℝ) ∨ σ = (-1 : ℝ) →
                wellPlacedHalfGap m (n + (2 : ℤ)) < σ * z i →
                  ∀ (u h : H1Function (openCubeSet (originCube d m))),
                    HasZeroTraceDifferenceOn (openCubeSet (originCube d m)) u h →
                      ∀ (R : ℝ),
                        (∀ (w : H1Function (translateSet (flushSubCentre z m n i σ) (openCubeSet (originCube d n))))
                            (rho : H10Function (translateSet (flushSubCentre z m n i σ) (openCubeSet (originCube d n)))),
                            IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i σ) (openCubeSet (originCube d n))) w →
                              (∀ (y : Vec d), w.toFun y = u.toFun y + rho.toFun y) →
                                (∀ (y : Vec d), w.grad y = u.grad y + rho.grad y) →
                                  (normalizedL2On
                                      ((fun (y : Vec d) => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n))
                                      fun (y : Vec d) => u.toFun y - w.toFun y) ≤
                                    R) →
                          |volumeAverage
                                ((fun (y : Vec d) => wellPlacedCentre z m (n + (2 : ℤ)) + y) ''
                                  openCubeSet (originCube d (n + (2 : ℤ))))
                                fun (y : Vec d) => u.toFun y - h.toFun y| ≤
                            CS *
                              ((eLpNorm
                                      (fun (y : Vec d) =>
                                        u.toFun y -
                                          volumeAverage
                                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                              openCubeSet (originCube d m))
                                            u.toFun)
                                      (2 : ENNReal)
                                      (normalizedVolumeMeasureOn
                                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                          openCubeSet (originCube d m)))).toReal +
                                  (3 : ℝ) ^ n *
                                    ∑ i' : Fin d,
                                      (eLpNorm (fun (y : Vec d) => h.grad y i') (2 : ENNReal)
                                          (normalizedVolumeMeasureOn
                                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                              openCubeSet (originCube d m)))).toReal +
                                R))
      (M : ABKModel d) (L m n : ℤ) (z : Vec d) (_ : z ∈ openCubeSet (originCube d m)) (i : Fin d) (sigma : ℝ)
      (_ : sigma = (1 : ℝ) ∨ sigma = (-1 : ℝ)) (_ : wellPlacedHalfGap m (n + (2 : ℤ)) < sigma * z i)
      (_ : n + (2 : ℤ) ≤ m) (omega : Cutoff.CutoffSample d) (u hdat : H1Function (openCubeSet (originCube d m)))
      (g : Vec d → Vec d)
      (_ : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g),
      (∀ (Rarg : ℝ),
          (∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))))
              (rho' : H10Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)))),
              IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))) w' →
                (∀ (y : Vec d), w'.toFun y = u.toFun y + rho'.toFun y) →
                  (∀ (y : Vec d), w'.grad y = u.grad y + rho'.grad y) →
                    (normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))
                        fun (y : Vec d) => u.toFun y - w'.toFun y) ≤
                      Rarg) →
            |volumeAverage
                  ((fun (y : Vec d) => wellPlacedCentre z m (n + (2 : ℤ)) + y) '' openCubeSet (originCube d (n + (2 : ℤ))))
                  fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
              CS *
                ((eLpNorm
                        (fun (y : Vec d) =>
                          u.toFun y -
                            volumeAverage
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                openCubeSet (originCube d m))
                              u.toFun)
                        (2 : ENNReal)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal +
                    (3 : ℝ) ^ n *
                      ∑ i' : Fin d,
                        (eLpNorm (fun (y : Vec d) => hdat.grad y i') (2 : ENNReal)
                            (normalizedVolumeMeasureOn
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                openCubeSet (originCube d m)))).toReal +
                  Rarg)) ∧
        ∑ i' : Fin d,
              (eLpNorm (fun (y : Vec d) => hdat.grad y i') (2 : ENNReal)
                  (normalizedVolumeMeasureOn
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m)))).toReal ≤
            (↑d : ℝ) *
              (eLpNorm hdat.grad (2 : ENNReal)
                  (normalizedVolumeMeasureOn
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m)))).toReal ∧
          (3 : ℝ) ^ n = Real.rpow (3 : ℝ) (↑n : ℝ) := by
  intro d CS hScal _ _ m n z hz i sigma hsigma hover hnm2 _ u hdat _ hsol
  have hscal0 : ∀ Rarg : ℝ,
      (∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma)
            (openCubeSet (originCube d n))))
        (rho' : H10Function (translateSet (flushSubCentre z m n i sigma)
            (openCubeSet (originCube d n)))),
        Support.IsWeaklyHarmonicOn
            (translateSet (flushSubCentre z m n i sigma)
              (openCubeSet (originCube d n))) w' →
        (∀ y, w'.toFun y = u.toFun y + rho'.toH1Function.toFun y) →
        (∀ y, w'.grad y = u.grad y + rho'.toH1Function.grad y) →
        normalizedL2On ((fun y => flushSubCentre z m n i sigma + y) ''
            openCubeSet (originCube d n))
          (fun y => u.toFun y - w'.toFun y) ≤ Rarg) →
      |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))
          (fun y => u.toFun y - hdat.toFun y)| ≤
        CS * ((eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal +
          (3 : ℝ) ^ n *
            ∑ i' : Fin d,
              (eLpNorm (fun y => hdat.grad y i') 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') ''
                      openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal + Rarg) :=
    fun Rarg hR => hScal hnm2 hz hsigma hover u hdat hsol.1 Rarg hR
  -- (3) the coordinate sum against the vector norm
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 :=
    volume_anchorWindow_ne_zero_of_flushSubCube hnm2 hz i hsigma
  have hvecfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ :=
    (memLp_normalizedVolumeMeasureOn_of_restrict hW30
      (hdat.grad_memVectorL2.mono_measure
        (Measure.restrict_mono Set.inter_subset_right le_rfl))).eLpNorm_ne_top
  have hsumb : (∑ i' : Fin d,
      (eLpNorm (fun y => hdat.grad y i') 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal) ≤
      (d : ℝ) * (eLpNorm hdat.grad 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal := by
    calc (∑ i' : Fin d,
        (eLpNorm (fun y => hdat.grad y i') 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal)
        ≤ ∑ _i' : Fin d, (eLpNorm hdat.grad 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal :=
          Finset.sum_le_sum fun i' _ => ENNReal.toReal_mono hvecfin
            (eLpNorm_mono ((continuous_apply i').comp_aestronglyMeasurable
              (aestronglyMeasurable_of_eLpNorm_ne_top hvecfin))
              fun y => norm_le_pi_norm (hdat.grad y) i')
      _ = (d : ℝ) * (eLpNorm hdat.grad 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hzr : (3 : ℝ) ^ n = Real.rpow (3 : ℝ) (n : ℝ) := (Real.rpow_intCast 3 n).symm
  exact ⟨hscal0, hsumb, hzr⟩

private theorem residuePlugin_comparisonBounds2 :
    ∀ (d : ℕ) (Cfin : ℝ) (_ : (0 : ℝ) < Cfin) (CS : ℝ) (_ : (0 : ℝ) ≤ CS) (_ : (0 : ℝ) ≤ (↑d : ℝ))
      (m n : ℤ) (z : Vec d) (i : Fin d) (sigma : ℝ) (u : H1Function (openCubeSet (originCube d m)))
      (w : H1Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))))
      (rho : H10Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))))
      (_ : IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))) w)
      (_ : ∀ (y : Vec d), w.toFun y = u.toFun y + rho.toFun y) (_ : ∀ (y : Vec d), w.grad y = u.grad y + rho.grad y)
      (X Hn Sm : ℝ) (_ : Sm ≤ (↑d : ℝ) * Hn) (S6 R3n S0 : ℝ)
      (_ :
        ∀ (Rarg : ℝ),
          (∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))))
              (rho' : H10Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)))),
              IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))) w' →
                (∀ (y : Vec d), w'.toFun y = u.toFun y + rho'.toFun y) →
                  (∀ (y : Vec d), w'.grad y = u.grad y + rho'.grad y) →
                    (normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))
                        fun (y : Vec d) => u.toFun y - w'.toFun y) ≤
                      Rarg) →
            S0 ≤ CS * (X + R3n * Sm + Rarg))
      (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Hn) (_ : (0 : ℝ) ≤ S0) (_ : (0 : ℝ) ≤ R3n) (_ : (1 : ℝ) ≤ S6) (Lg : ℝ)
      (_ : (0 : ℝ) ≤ Lg) (Lh : ℝ) (_ : (0 : ℝ) ≤ Lh) (Ln : ℝ) (_ : Ln = S6 * R3n * Hn) (_ : (0 : ℝ) ≤ Ln)
      (p : ℝ)
      (_ :
        ∀ (Sarg : ℝ),
          S0 ≤ Sarg →
            ∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))))
              (rho' : H10Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)))),
              IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))) w' →
                (∀ (y : Vec d), w'.toFun y = u.toFun y + rho'.toFun y) →
                  (∀ (y : Vec d), w'.grad y = u.grad y + rho'.grad y) →
                    (normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))
                        fun (y : Vec d) => u.toFun y - w'.toFun y) ≤
                      Cfin * (p * X + Lg + Lh + Ln + p * Sarg))
      (_ : (0 : ℝ) ≤ p) (q : ℝ) (_ : q = Cfin * p) (_ : (0 : ℝ) ≤ q) (_ : (2 : ℝ) * q ≤ (1 : ℝ))
      (_ : (2 : ℝ) * (q * CS) ≤ (1 : ℝ)) (_ : (2 : ℝ) * (q * CS * (↑d : ℝ)) ≤ (1 : ℝ)) (Rb : ℝ)
      (_ : Rb = Cfin * (p * X + Lg + Lh + Ln + p * S0)),
      Rb ≤
          (2 : ℝ) * (q * X) + (2 : ℝ) * (Cfin * (Lg + Lh + Ln)) + (2 : ℝ) * (q * CS * X) +
            (2 : ℝ) * (q * CS * ((↑d : ℝ) * Ln)) ∧
        (2 : ℝ) * (q * X) ≤ X ∧
          (2 : ℝ) * (q * CS * X) ≤ X ∧
            (2 : ℝ) * (q * CS * ((↑d : ℝ) * Ln)) ≤ Ln ∧
              (normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))
                  fun (y : Vec d) => u.toFun y - w.toFun y) ≤
                Rb := by
  intro d Cfin hCfin CS hCS0 hd0 m n z i sigma u w rho hharm hval hgrad X Hn Sm hsumb S6 R3n S0 hscal0 hX0 hHn0 hS00 hR3n0 hS61 Lg hLg0 Lh hLh0 Ln hLndef hLn0 p hres0 hp0 q hqdef hq0 h2q h2qCS h2qCSd Rb hRbdef
  have hRb0 : 0 ≤ Rb := by
    rw [hRbdef]
    have h1 : 0 ≤ p * X := mul_nonneg hp0 hX0
    have h2 : 0 ≤ p * S0 := mul_nonneg hp0 hS00
    exact mul_nonneg hCfin.le (by linarith only [h1, h2, hLg0, hLh0, hLn0])
  have hres1 : ∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma)
        (openCubeSet (originCube d n))))
      (rho' : H10Function (translateSet (flushSubCentre z m n i sigma)
        (openCubeSet (originCube d n)))),
      Support.IsWeaklyHarmonicOn
          (translateSet (flushSubCentre z m n i sigma)
            (openCubeSet (originCube d n))) w' →
      (∀ y, w'.toFun y = u.toFun y + rho'.toH1Function.toFun y) →
      (∀ y, w'.grad y = u.grad y + rho'.toH1Function.grad y) →
      normalizedL2On ((fun y => flushSubCentre z m n i sigma + y) ''
          openCubeSet (originCube d n))
        (fun y => u.toFun y - w'.toFun y) ≤ Rb := by
    rw [hRbdef]
    exact hres0 S0 (le_refl _)
  have hS0le := hscal0 Rb hres1
  -- the loop arithmetic
  have hSmLn : R3n * Sm ≤ (d : ℝ) * Ln := by
    have h1 : R3n * Sm ≤ R3n * ((d : ℝ) * Hn) :=
      mul_le_mul_of_nonneg_left hsumb hR3n0
    have hRH : 0 ≤ R3n * Hn := mul_nonneg hR3n0 hHn0
    have h2 : R3n * Hn ≤ S6 * (R3n * Hn) := le_mul_of_one_le_left hRH hS61
    have h3 : R3n * ((d : ℝ) * Hn) = (d : ℝ) * (R3n * Hn) := by ring
    have h4 : (d : ℝ) * (R3n * Hn) ≤ (d : ℝ) * (S6 * (R3n * Hn)) :=
      mul_le_mul_of_nonneg_left h2 hd0
    have h5 : (d : ℝ) * (S6 * (R3n * Hn)) = (d : ℝ) * Ln := by rw [hLndef]; ring
    linarith only [h1, h3, h4, h5]
  have hS0' : S0 ≤ CS * X + CS * ((d : ℝ) * Ln) + CS * Rb := by
    have hmul := mul_le_mul_of_nonneg_left hSmLn hCS0
    linarith only [hS0le, hmul]
  have hRbeq : Rb = q * X + Cfin * (Lg + Lh + Ln) + q * S0 := by
    rw [hRbdef, hqdef]
    ring
  have hstepA : Rb ≤ q * X + Cfin * (Lg + Lh + Ln) +
      q * (CS * X + CS * ((d : ℝ) * Ln) + CS * Rb) := by
    have h := mul_le_mul_of_nonneg_left hS0' hq0
    linarith only [hRbeq, h]
  have hhalf : 2 * (q * CS) * Rb ≤ Rb :=
    by have h := mul_le_mul_of_nonneg_right h2qCS hRb0; linarith only [h]
  have hRb4 : Rb ≤ 2 * (q * X) + 2 * (Cfin * (Lg + Lh + Ln)) +
      2 * (q * CS * X) + 2 * (q * CS * ((d : ℝ) * Ln)) := by
    linarith only [hstepA, hhalf]
  have hA1 : 2 * (q * X) ≤ X := by
    have h := mul_le_mul_of_nonneg_right h2q hX0
    linarith only [h]
  have hA2 : 2 * (q * CS * X) ≤ X := by
    have h := mul_le_mul_of_nonneg_right h2qCS hX0
    linarith only [h]
  have hA3 : 2 * (q * CS * ((d : ℝ) * Ln)) ≤ Ln := by
    have h := mul_le_mul_of_nonneg_right h2qCSd hLn0
    linarith only [h]
  have hfin := hres1 w rho hharm hval hgrad
  exact ⟨hRb4, hA1, hA2, hA3, hfin⟩

/-- **Route 1, closed at the `ε`-pin.**

The harmonic-approximation residue at the flush sub-cube `K'`, priced on the
frozen display's own four legs, under the single explicit hypothesis
`A·𝓔 ≤ s⁴`.  `A` is produced by the theorem, so the caller knows exactly what
smallness the re-pinning must supply. -/
private theorem residuePlugin_fluxCancellation :
    ∀ (d : ℕ) (Cfin : ℝ) (M : ABKModel d) (s : ℝ) (hs : (0 : ℝ) < s)
      (L m n : ℤ) (z : Vec d) (i : Fin d) (sigma : ℝ) (omega : Cutoff.CutoffSample d)
      (hcompw :
        omega ∈
            Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 : ℤ)) z
              ⟨s / (8 : ℝ),
                (by
                  solve
                  | norm_num
                  | positivity
                  | assumption
                  | omega
                  | linarith)⟩
              (1 / 2 : ℝ) →
          ∀ (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (S : ℝ),
            IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g →
              MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) hdat.grad) (2 : ENNReal)
                      (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                    |volumeAverage
                            ((fun (y : Vec d) => wellPlacedCentre z m (n + (2 : ℤ)) + y) ''
                              openCubeSet (originCube d (n + (2 : ℤ))))
                            fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                        S →
                      ∀
                        (v :
                          H1Function
                            ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n)))
                        (w :
                          H10Function
                            ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))),
                        IsWeaklyHarmonicOn
                            ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n)) v →
                          (∀ (y : Vec d), v.toFun y = u.toFun y - w.toFun y) →
                            (∀ (y : Vec d), v.grad y = u.grad y - w.grad y) →
                              (eLpNorm (fun (y : Vec d) => u.toFun y - v.toFun y) (2 : ENNReal)
                                    (normalizedVolumeMeasureOn
                                      ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) ''
                                        openCubeSet (originCube d n)))).toReal ≤
                                Cfin *
                                  (s.rpow (-4 : ℝ) *
                                              fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                                                ⟨s / (8 : ℝ),
                                                  (by
                                                    solve
                                                    | norm_num
                                                    | positivity
                                                    | assumption
                                                    | omega
                                                    | linarith)⟩
                                                (Cutoff.translateCutoffSample z omega) *
                                            (eLpNorm
                                                (fun (y : Vec d) =>
                                                  u.toFun y -
                                                    volumeAverage
                                                      ((fun (y' : Vec d) => z + y') ''
                                                          openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                                        openCubeSet (originCube d m))
                                                      u.toFun)
                                                (2 : ENNReal)
                                                (normalizedVolumeMeasureOn
                                                  ((fun (y' : Vec d) => z + y') ''
                                                      openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                                    openCubeSet (originCube d m)))).toReal +
                                          s.rpow (-7 : ℝ) * (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)⁻¹ *
                                              Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) *
                                            (normalizedGagliardoESeminormOn
                                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                                  openCubeSet (originCube d m))
                                                s g).toReal +
                                        s.rpow (-6 : ℝ) * Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) *
                                          (normalizedGagliardoESeminormOn
                                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                                openCubeSet (originCube d m))
                                              s hdat.grad).toReal +
                                      s.rpow (-6 : ℝ) * Real.rpow (3 : ℝ) (↑n : ℝ) *
                                        (eLpNorm hdat.grad (2 : ENNReal)
                                            (normalizedVolumeMeasureOn
                                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                                openCubeSet (originCube d m)))).toReal +
                                    s.rpow (-4 : ℝ) *
                                        fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                                          ⟨s / (8 : ℝ),
                                            (by
                                              solve
                                              | norm_num
                                              | positivity
                                              | assumption
                                              | omega
                                              | linarith)⟩
                                          (Cutoff.translateCutoffSample z omega) *
                                      S))
      (hmem :
        omega ∈
          Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 : ℤ)) z
            ⟨s / (8 : ℝ),
              (by
                solve
                | norm_num
                | positivity
                | assumption
                | omega
                | linarith)⟩
            (1 / 2 : ℝ))
      (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (hsol : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g)
      (hgL2 : MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
      (hgW :
        MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
      (hhW :
        MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) hdat.grad) (2 : ENNReal)
          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
      (hK'top :
        (volume : (a : Set (Vec d)) → ENNReal)
            ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n)) ≠
          ⊤)
      (hK'volpos :
        (0 : ENNReal) <
          (volume : (a : Set (Vec d)) → ENNReal)
            ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n)))
      (hKT :
        (fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n) =
          translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)))
      (hmemU :
        MemLp u.toFun (2 : ENNReal)
          (volume.restrict ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))))
      (Sarg : ℝ),
      |volumeAverage
              ((fun (y : Vec d) => wellPlacedCentre z m (n + (2 : ℤ)) + y) '' openCubeSet (originCube d (n + (2 : ℤ))))
              fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
          Sarg →
        ∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))))
          (rho' : H10Function (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)))),
          IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n))) w' →
            (∀ (y : Vec d), w'.toFun y = u.toFun y + rho'.toFun y) →
              (∀ (y : Vec d), w'.grad y = u.grad y + rho'.grad y) →
                (normalizedL2On ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n))
                    fun (y : Vec d) => u.toFun y - w'.toFun y) ≤
                  Cfin *
                    (s.rpow (-4 : ℝ) *
                                fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                                  (Cutoff.translateCutoffSample z omega) *
                              (eLpNorm
                                  (fun (y : Vec d) =>
                                    u.toFun y -
                                      volumeAverage
                                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                          openCubeSet (originCube d m))
                                        u.toFun)
                                  (2 : ENNReal)
                                  (normalizedVolumeMeasureOn
                                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                      openCubeSet (originCube d m)))).toReal +
                            s.rpow (-7 : ℝ) * (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) *
                              (normalizedGagliardoESeminormOn
                                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                    openCubeSet (originCube d m))
                                  s g).toReal +
                          s.rpow (-6 : ℝ) * Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) *
                            (normalizedGagliardoESeminormOn
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                  openCubeSet (originCube d m))
                                s hdat.grad).toReal +
                        s.rpow (-6 : ℝ) * Real.rpow (3 : ℝ) (↑n : ℝ) *
                          (eLpNorm hdat.grad (2 : ENNReal)
                              (normalizedVolumeMeasureOn
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                  openCubeSet (originCube d m)))).toReal +
                      s.rpow (-4 : ℝ) *
                          fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                            (Cutoff.translateCutoffSample z omega) *
                        Sarg) := by
  intro d Cfin M s hs L m n z i sigma omega hcompw hmem u hdat g hsol hgL2 hgW hhW hK'top hK'volpos hKT hmemU Sarg hmeanS w' rho' hharm' hval' hgrad'
  set v : H1Function ((fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n)) := h1FunctionOfSetEq hKT.symm w' with hvdef
  set wneg : H10Function ((fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n)) :=
    h10FunctionOfSetEq hKT.symm (-rho') with hwnegdef
  have hvfun : ∀ y, v.toFun y = w'.toFun y := by
    intro y
    rw [hvdef]
    exact congrFun (h1FunctionOfSetEq_toFun hKT.symm w') y
  have hvgradfun : ∀ y, v.grad y = w'.grad y := by
    intro y
    rw [hvdef]
    exact congrFun (h1FunctionOfSetEq_grad hKT.symm w') y
  have hnegfun : ∀ y, wneg.toH1Function.toFun y = -(rho'.toH1Function.toFun y) := by
    intro y
    rw [hwnegdef]
    have h1 : (h10FunctionOfSetEq hKT.symm (-rho')).toH1Function.toFun =
        (-rho').toH1Function.toFun := h10FunctionOfSetEq_toFun hKT.symm (-rho')
    rw [h1]
    change ((-1 : ℝ) • rho'.toH1Function).toFun y = -(rho'.toH1Function.toFun y)
    rw [H1Function.smul_toFun]
    ring
  have hneggrad : ∀ y, wneg.toH1Function.grad y = -(rho'.toH1Function.grad y) := by
    intro y
    rw [hwnegdef]
    have h1 : (h10FunctionOfSetEq hKT.symm (-rho')).toH1Function.grad =
        (-rho').toH1Function.grad := h10FunctionOfSetEq_grad hKT.symm (-rho')
    rw [h1]
    change ((-1 : ℝ) • rho'.toH1Function).grad y = -(rho'.toH1Function.grad y)
    rw [H1Function.smul_grad]
    funext r
    change (-1 : ℝ) * rho'.toH1Function.grad y r = -(rho'.toH1Function.grad y r)
    ring
  have hharmv : Support.IsWeaklyHarmonicOn
      ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n)) v := by
    rw [hvdef]
    exact isWeaklyHarmonicOn_h1FunctionOfSetEq hKT.symm hharm'
  have hvalv : ∀ y, v.toFun y = u.toFun y - wneg.toH1Function.toFun y := by
    intro y
    rw [hvfun y, hval' y, hnegfun y]
    ring
  have hgradv : ∀ y, v.grad y = u.grad y - wneg.toH1Function.grad y := by
    intro y
    rw [hvgradfun y, hgrad' y, hneggrad y]
    funext r
    change u.grad y r + rho'.toH1Function.grad y r =
      u.grad y r - -(rho'.toH1Function.grad y r)
    ring
  have hbound := hcompw hmem u hdat g Sarg hsol hgL2 hgW hhW hmeanS
    v wneg hharmv hvalv hgradv
  have hRho : MemLp (fun y => rho'.toH1Function.toFun y) 2
      (volume.restrict ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n))) := by
    rw [hKT]
    exact rho'.toH1Function.memL2
  have hWmem : MemLp (fun y => w'.toFun y) 2
      (volume.restrict ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n))) := by
    have hfun : (fun y => w'.toFun y) =
        fun y => u.toFun y + rho'.toH1Function.toFun y := by
      funext y
      exact hval' y
    rw [hfun]
    exact hmemU.add hRho
  have hbridge : normalizedL2On ((fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n)) (fun y => u.toFun y - w'.toFun y) =
      (eLpNorm (fun y => u.toFun y - w'.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => flushSubCentre z m n i sigma + y) ''
            openCubeSet (originCube d n)))).toReal :=
    Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hK'volpos
      hK'top (hmemU.sub hWmem)
  have hfun : (fun y => u.toFun y - v.toFun y) =
      fun y => u.toFun y - w'.toFun y := by
    funext y
    rw [hvfun y]
  rw [hfun] at hbound
  rw [hbridge]
  exact hbound

theorem exists_flushResidue_le_displayLegs_of_epsPin (d : ℕ) [NeZero d] :
    ∃ C A K : ℝ, 0 < C ∧ 0 < A ∧ 0 ≤ K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
          ∀ (i : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) →
            wellPlacedHalfGap m (n + 2) < sigma * z i →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                A * Support.fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) ≤ s ^ (4 : ℕ) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  ∀ (w : H1Function (translateSet (flushSubCentre z m n i sigma)
                        (openCubeSet (originCube d n))))
                    (rho : H10Function (translateSet (flushSubCentre z m n i sigma)
                        (openCubeSet (originCube d n)))),
                    Support.IsWeaklyHarmonicOn
                        (translateSet (flushSubCentre z m n i sigma)
                          (openCubeSet (originCube d n))) w →
                    (∀ y, w.toFun y = u.toFun y + rho.toH1Function.toFun y) →
                    (∀ y, w.grad y = u.grad y + rho.toH1Function.grad y) →
                      normalizedL2On ((fun y => flushSubCentre z m n i sigma + y) ''
                          openCubeSet (originCube d n))
                        (fun y => u.toFun y - w.toFun y) ≤
                        K * ((eLpNorm (fun y => u.toFun y -
                                volumeAverage ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) u.toFun) 2
                              (Support.normalizedVolumeMeasureOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))))).toReal +
                          Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                            (eLpNorm hdat.grad 2
                              (Support.normalizedVolumeMeasureOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))))).toReal +
                          Real.rpow s (-(6 : ℝ)) *
                            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                            (Support.normalizedGagliardoESeminormOn
                              ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))) s hdat.grad).toReal +
                          Real.rpow s (-(7 : ℝ)) *
                            ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                            (Support.normalizedGagliardoESeminormOn
                              ((((fun y' => z + y') ''
                                  openCubeSet (originCube d (n + 3))) ∩
                                openCubeSet (originCube d m))) s g).toReal) := by
  classical
  obtain ⟨C1, Cfin, hC1, hCfin, hcomp⟩ := exists_flushResidue_route1_composed d
  obtain ⟨CS, hCS0, hScal⟩ := exists_scalarControl_flushCube_harmonicResidue d
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  refine ⟨C1, 2 * Cfin + 2 * (Cfin * CS) + 2 * (Cfin * CS) * (d : ℝ) + 1,
    3 + 2 * Cfin, hC1, by positivity, by positivity, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
  filter_upwards [hcomp M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma
    hsigma hover] with omega hcompw
  intro hmem hpin u hdat g hsol hgL2 hgW hhW w rho hharm hval hgrad
  -- the flush geometry
  have hK'm : (fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n) ⊆ openCubeSet (originCube d m) :=
    flushSubCube_subset_openCubeSet hnm2 z i hsigma
  have hK'pos := volume_toReal_image_add_openCubeSet_pos
    (flushSubCentre z m n i sigma) n
  have hK'top := volume_image_add_openCubeSet_ne_top (flushSubCentre z m n i sigma) n
  have hK'volpos : 0 < volume ((fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n)) := by
    by_contra hcon
    push Not at hcon
    have h0 : volume ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n)) = 0 := le_antisymm hcon (zero_le)
    rw [h0] at hK'pos
    simp only [ENNReal.toReal_zero] at hK'pos
    exact lt_irrefl _ hK'pos
  have hKT : (fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n) =
      translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)) :=
    image_add_eq_translateSet _ _
  have hmemU := memLp_toFun_of_subset u hK'm
  -- (1) the residue budget at an abstract scalar, stated before any abbreviation
  have hres0 : ∀ Sarg : ℝ,
      |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))
          (fun y => u.toFun y - hdat.toFun y)| ≤ Sarg →
      ∀ (w' : H1Function (translateSet (flushSubCentre z m n i sigma)
            (openCubeSet (originCube d n))))
        (rho' : H10Function (translateSet (flushSubCentre z m n i sigma)
            (openCubeSet (originCube d n)))),
        Support.IsWeaklyHarmonicOn
            (translateSet (flushSubCentre z m n i sigma)
              (openCubeSet (originCube d n))) w' →
        (∀ y, w'.toFun y = u.toFun y + rho'.toH1Function.toFun y) →
        (∀ y, w'.grad y = u.grad y + rho'.toH1Function.grad y) →
        normalizedL2On ((fun y => flushSubCentre z m n i sigma + y) ''
            openCubeSet (originCube d n))
          (fun y => u.toFun y - w'.toFun y) ≤
          Cfin *
            (Real.rpow s (-(4 : ℝ)) *
                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                  ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) *
                (eLpNorm (fun y => u.toFun y -
                    volumeAverage ((((fun y' => z + y') ''
                        openCubeSet (originCube d (n + 3))) ∩
                      openCubeSet (originCube d m))) u.toFun) 2
                  (Support.normalizedVolumeMeasureOn
                    ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                      openCubeSet (originCube d m))))).toReal +
              Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) s g).toReal +
              Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) s hdat.grad).toReal +
              Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                (eLpNorm hdat.grad 2
                  (Support.normalizedVolumeMeasureOn
                    ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                      openCubeSet (originCube d m))))).toReal +
              Real.rpow s (-(4 : ℝ)) *
                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                  ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) * Sarg)  := @residuePlugin_fluxCancellation (d) (Cfin) (M) (s) (hs) (L) (m) (n) (z) (i) (sigma) (omega) (hcompw) (hmem) (u) (hdat) (g) (hsol) (hgL2) (hgW) (hhW) (hK'top) (hK'volpos) (hKT) (hmemU)
  -- (2) the scalar control at an abstract budget
  obtain ⟨hscal0, hsumb, hzr⟩ :=
    @residuePlugin_comparisonBounds1 (d) (CS) (hScal) (M) (L) (m) (n) (z) (hz) (i) (sigma)
      (hsigma) (hover) (hnm2) (omega) (u) (hdat) (g) (hsol)
  rw [hzr] at hscal0
  -- (4) the pin
  have hApos : (0 : ℝ) ≤
      2 * Cfin + 2 * (Cfin * CS) + 2 * (Cfin * CS) * (d : ℝ) + 1 := by positivity
  have hErep0 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hPcap : (2 * Cfin + 2 * (Cfin * CS) + 2 * (Cfin * CS) * (d : ℝ) + 1) *
      Real.rpow s (-(4 : ℝ)) *
      Support.fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) ≤ 1 :=
    coarseGrainingResidue_coefficient_le_of_error_small hs hApos hErep0 hpin
  -- the abbreviations
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hXdef
  set Gs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s g).toReal with hGsdef
  set Hs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s hdat.grad).toReal with hHsdef
  set Hn : ℝ := (eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHndef
  set Sm : ℝ := ∑ i' : Fin d,
    (eLpNorm (fun y => hdat.grad y i') 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hSmdef
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S6 : ℝ := Real.rpow s (-(6 : ℝ)) with hS6def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S0 : ℝ := |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
    openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - hdat.toFun y)| with hS0def
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hGs0 : 0 ≤ Gs := ENNReal.toReal_nonneg
  have hHs0 : 0 ≤ Hs := ENNReal.toReal_nonneg
  have hHn0 : 0 ≤ Hn := ENNReal.toReal_nonneg
  have hS00 : 0 ≤ S0 := abs_nonneg _
  have hsig : (0 : ℝ) < sig := (Annealed.sigmaBar M (n + 3)).2
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have hS40 : 0 ≤ S4 := Real.rpow_nonneg hs.le _
  have hS60 : 0 ≤ S6 := Real.rpow_nonneg hs.le _
  have hS70 : 0 ≤ S7 := Real.rpow_nonneg hs.le _
  have hQ1s0 : 0 ≤ Q1s := Real.rpow_nonneg (by norm_num) _
  have hR3n0 : 0 ≤ R3n := Real.rpow_nonneg (by norm_num) _
  have hS61 : (1 : ℝ) ≤ S6 := by
    rw [hS6def]
    have h := Real.rpow_le_rpow_of_exponent_ge hs hs1
      (show (-(6 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  have hErepnn : 0 ≤ Erep := hErep0
  clear_value X Gs Hs Hn Sm Erep sig S4 S6 S7 Q1s R3n S0
  -- the three legs, as atoms
  obtain ⟨Lg, hLgdef, hLg0⟩ : ∃ t : ℝ, t = S7 * sig⁻¹ * Q1s * Gs ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg (mul_nonneg (mul_nonneg hS70 hsiginv0) hQ1s0) hGs0⟩
  obtain ⟨Lh, hLhdef, hLh0⟩ : ∃ t : ℝ, t = S6 * Q1s * Hs ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg (mul_nonneg hS60 hQ1s0) hHs0⟩
  obtain ⟨Ln, hLndef, hLn0⟩ : ∃ t : ℝ, t = S6 * R3n * Hn ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg (mul_nonneg hS60 hR3n0) hHn0⟩
  obtain ⟨p, hpdef, hp0⟩ : ∃ t : ℝ, t = S4 * Erep ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg hS40 hErepnn⟩
  obtain ⟨q, hqdef, hq0⟩ : ∃ t : ℝ, t = Cfin * p ∧ 0 ≤ t :=
    ⟨_, rfl, mul_nonneg hCfin.le hp0⟩
  rw [← hLgdef, ← hLhdef, ← hLndef, ← hpdef] at hres0
  rw [← hLgdef, ← hLhdef, ← hLndef]
  -- the pin, in the two forms consumed
  have hpA : (2 * Cfin + 2 * (Cfin * CS) + 2 * (Cfin * CS) * (d : ℝ) + 1) * p ≤ 1 := by
    rw [hpdef]
    linarith only [hPcap]
  have hn1 : (0 : ℝ) ≤ 2 * Cfin * p := mul_nonneg (by positivity) hp0
  have hn2 : (0 : ℝ) ≤ 2 * (Cfin * CS) * p := mul_nonneg (by positivity) hp0
  have hn3 : (0 : ℝ) ≤ 2 * (Cfin * CS) * (d : ℝ) * p := mul_nonneg (by positivity) hp0
  have h2q : 2 * q ≤ 1 := by
    rw [hqdef]
    linarith only [hpA, hn2, hn3, hp0]
  have h2qCS : 2 * (q * CS) ≤ 1 := by
    rw [hqdef]
    linarith only [hpA, hn1, hn3, hp0]
  have h2qCSd : 2 * (q * CS * (d : ℝ)) ≤ 1 := by
    rw [hqdef]
    linarith only [hpA, hn1, hn2, hp0]
  -- the residue budget at the free scalar, and the loop
  obtain ⟨Rb, hRbdef⟩ : ∃ t : ℝ,
      t = Cfin * (p * X + Lg + Lh + Ln + p * S0) := ⟨_, rfl⟩
  obtain ⟨hRb4, hA1, hA2, hA3, hfin⟩ :=
    @residuePlugin_comparisonBounds2 (d) (Cfin) (hCfin) (CS) (hCS0) (hd0) (m) (n) (z) (i) (sigma)
      (u) (w) (rho) (hharm) (hval) (hgrad) (X) (Hn) (Sm) (hsumb) (S6) (R3n) (S0) (hscal0) (hX0)
        (hHn0) (hS00) (hR3n0) (hS61) (Lg) (hLg0) (Lh) (hLh0) (Ln) (hLndef) (hLn0) (p) (hres0)
          (hp0) (q) (hqdef) (hq0) (h2q) (h2qCS) (h2qCSd) (Rb) (hRbdef)
  refine hfin.trans ?_
  have hCX : 0 ≤ Cfin * X := mul_nonneg hCfin.le hX0
  linarith only [hRb4, hA1, hA2, hA3, hCX, hLg0, hLh0, hLn0, hX0]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
