/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResiduePlugin

/-!
# ShellScalarPriced

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary scalar `S`, priced: the residue leg discharged

## What is proved

`exists_boundaryScalar_le_displayLegs_of_epsPin`: on the boundary branch, the
scalar

```text
  S  =  |⨍_{V₁}(u − h)| ,      V₁ = wellPlacedCentre z m (n+2) + □_{n+2} ,
```

obeys, for a.e. sample, on the good event and under the `ε`-pin
`A·𝓔 ≤ s⁴`,

```text
  S ≤ K · ( ‖u − (u)_{W'}‖_{L²(W')}                      (the FIRST leg)
          + 3ⁿ · Σᵢ ‖∂ᵢh‖_{L²(W')}                       (the FIFTH leg)
          + s^{-6}·3ⁿ·‖∇h‖_{L²(W')}
          + s^{-6}·3^{(1+s)n}·[∇h]_{Hˢ(W')}
          + s^{-7}·σ_{n+3}⁻¹·3^{(1+s)n}·[g]_{Hˢ(W')} ) ,
```

with `W' = (z+□_{n+3}) ∩ □_m` the frozen window and `K` explicit.  **No gradient
residue appears on the right-hand side.**

## Why this module exists

The boundary lane's chain prices `S` with a
third leg `3ⁿ·Σᵢ‖∂ᵢu‖_{L²(K')}` — the Euclidean gradient at the flush scale-`n`
sub-cube — which has no legal producer: the fitted boundary Caccioppoli's
left-hand side is the `ν`-weighted energy, so extracting the Euclidean gradient
costs `√(σ/ν)`.  `ResidueScalarFlush` re-cuts the scalar theorem so that the
residue becomes the *harmonic-approximation distance* `‖u − w‖_{L²(K')}`
(`ResidueScalarFlush.exists_scalarControl_flushCube_harmonicResidue`), and
`ResiduePlugin` prices that residue on the display's own four legs
(`ResiduePlugin.exists_flushResidue_le_displayLegs_of_epsPin`).  The two
have never been composed into a residue-free statement about `S` itself: the
proved compositions (`StitchDisplayLegs`, `StitchDisplayLegsErrorWeighted`) price the
display's `S`-**leg** `s^{-4}·𝓔·S`, i.e. `S` multiplied by the flux factor,
which is what the frozen theorem's own assembly consumes.

The `t.regularity` Step-7 shell route needs `S` **bare**: the mean gap enters
`‖u(·+c) − v‖_{L²(□_k)}` at the same weight as the first leg, with no `𝓔`
factor available to help.  This module supplies exactly that.

## The scale the Step-7 shell consumes

The shell route runs
`BoundaryOuterAssembly.exists_boundaryWindowEnergy_le_dirichletDatumRHS` at
`k := n+3`, `x := z`, `c := wellPlacedCentre z m (n+3)`, so the
mean gap it must kill sits on `c + □_{n+3}`.  That is this theorem's `V₁` after
the instantiation `n ↦ n+1`: the covering cube becomes `wellPlacedCentre z m
(n+3) + □_{n+3}`, the flush sub-cube sits at scale `n+1`, the window at
`(z+□_{n+4}) ∩ □_m`, and the good event and the pin are read at `(n+4, z)`.
The overhang costs nothing there: `wellPlacedHalfGap m k` is *decreasing* in
`k`, so the boundary branch's own `wellPlacedHalfGap m (n+2) < σ zᵢ` already
implies the instantiated `wellPlacedHalfGap m (n+3) < σ zᵢ`.  What the
instantiation does cost is `n + 4 ≤ m`, the good event and the pin one triadic
scale deeper, and the window read at `(z+□_{n+4}) ∩ □_m`; those are the
consumer's to supply and are NOT claimed here.

## Why the print does not have to do this

Move 3 of `l.coarse.grained.Caccioppoli.RHS` **does** absorb the datum internally:
`‖v‖_{L²(□₀)}` is bounded by the two printed data legs alone, using `v − h ∈
H¹₀(□₀)` and the lemma's standing hypothesis `(h)_{□₀} = 0`.  But that
hypothesis is a *normalization of `h`*, while Step 2 of
`l.harmonic.approximation.good.scales` normalizes *`u`* instead ("by
subtracting `(u)_{(x+□_{n+1})∩□_m}` from `u`").  The shift freedom `(u,h) ↦
(u+a, h+a)` is ONE scalar and the two normalizations are TWO conditions; their
difference is exactly `S`.  The printed Step 2 sets it to zero silently.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS` (statement, move 3);
  `l.harmonic.approximation.good.scales`, Step 2; `t.regularity` Step 7.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The composition arithmetic -/

/-- **The two-theorem composition, in the abstract.**

The scalar theorem returns `CS·(X + G + R)` with `R` an arbitrary residue
budget; the plug-in returns `R ≤ K·(X + Ln + Lh + Lg)`.  Substituting and
regrouping costs the single constant `CS·(1+K)` on the five legs.  Nothing here
is a norm: `X, G, Ln, Lh, Lg` are free reals and only `G, Ln, Lh, Lg` need to
be nonnegative. -/
private theorem compose_arith {CS K X G Ln Lh Lg : ℝ} (hCS0 : 0 ≤ CS) (hK0 : 0 ≤ K)
    (hG0 : 0 ≤ G) (hLn0 : 0 ≤ Ln) (hLh0 : 0 ≤ Lh) (hLg0 : 0 ≤ Lg) :
    CS * (X + G + K * (X + Ln + Lh + Lg)) ≤ CS * (1 + K) * (X + G + Ln + Lh + Lg) := by
  have hdiff : CS * (1 + K) * (X + G + Ln + Lh + Lg) -
      CS * (X + G + K * (X + Ln + Lh + Lg)) = CS * (Ln + Lh + Lg) + CS * K * G := by ring
  have h1 : 0 ≤ CS * (Ln + Lh + Lg) :=
    mul_nonneg hCS0 (by linarith only [hLn0, hLh0, hLg0])
  have h2 : 0 ≤ CS * K * G := mul_nonneg (mul_nonneg hCS0 hK0) hG0
  linarith only [hdiff, h1, h2]

/-! ## 2. The boundary scalar, priced with no gradient residue -/

/-- **The boundary scalar `S`, priced on five legs, residue-free.**

`S = |⨍_{V₁}(u − h)|` at the anchor's own covering cube is bounded by the
frozen first leg, the frozen fifth leg, and the three tail legs of the display,
under the pin `A·𝓔 ≤ s⁴` with `A` produced by the theorem.  The Euclidean
gradient residue of the earlier chain — the `ν`-division that has no legal
producer — does not occur. -/
theorem exists_boundaryScalar_le_displayLegs_of_epsPin (d : ℕ) [NeZero d] :
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
                  |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - hdat.toFun y)| ≤
                    K * ((eLpNorm (fun y => u.toFun y -
                            volumeAverage ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))) u.toFun) 2
                          (Support.normalizedVolumeMeasureOn
                            ((((fun y' => z + y') ''
                                openCubeSet (originCube d (n + 3))) ∩
                              openCubeSet (originCube d m))))).toReal +
                      (3 : ℝ) ^ n *
                        ∑ i' : Fin d,
                          (eLpNorm (fun y => hdat.grad y i') 2
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
  obtain ⟨CS, hCS0, hScal⟩ := exists_scalarControl_flushCube_harmonicResidue d
  obtain ⟨C, A, K, hC, hA, hK0, hplug⟩ := exists_flushResidue_le_displayLegs_of_epsPin d
  refine ⟨C, A, CS * (1 + K), hC, hA, by positivity, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  filter_upwards [hplug M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma
    hsigma hover] with omega hw
  intro hmem hpin u hdat g hsol hgL2 hgW hhW
  have hnm2 : n + 2 ≤ m := by omega
  have hmain := hScal hnm2 hz hsigma hover u hdat hsol.hasZeroTraceDifferenceOn _
    (fun w rho h1 h2 h3 => hw hmem hpin u hdat g hsol hgL2 hgW hhW w rho h1 h2 h3)
  refine hmain.trans (compose_arith hCS0 hK0 ?_ ?_ ?_ ?_)
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (inv_nonneg.mpr (Annealed.sigmaBar M (n + 3)).2.le))
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
