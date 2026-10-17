/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ProviderBoundaryErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseSealDistanceErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GradHSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api

/-!
# HarmonicApproximationProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `l.harmonic.approximation.good.scales`, the provider

## What is proved

One public theorem, `harmonic_approximation_provider`, and it carries no
hypothesis beyond the anchor's own regime, funding line and geometry binders:
for every dimension `d` there is a constant `C > 0` such that, almost surely in
the cutoff sample, every Dirichlet solution `u` on `□_m` with datum `h` and
force `g`, and every weakly `ã`-harmonic competitor `v = u − w` on the child
cube `x + □_n` (`w ∈ H¹₀`), satisfies **two** displays.

* **The general clause**, at every centre `z`, gated on the good event
  `𝒢(n+3, z; s/8, C⁻¹ s⁴)`:
  ```text
    1_𝒢 ‖u − v‖_{L²(x+□_n)}
        ≤ C s^{-4} 𝓔_{n+3} ( ‖u − (u)_{W'}‖_{L²(W')} + s^{-3/2} 3^n |(∇h)_W| )
          + C s^{-7} σ_n^{-1} 3^{(1+s)n} [g]_{H^s(W')}
          + C s^{-6}          3^{(1+s)n} [∇h]_{H^s(W')}
          + C s^{-6} 𝓔_{n+3}  3^n        |(∇h)_W| ,
        W = (z + □_{n+2}) ∩ □_m ,   W' = (z + □_{n+3}) ∩ □_m .
  ```

* **The interior clause**, triggered by the frontier-empty gate
  `(z + □_{n+2}) ∩ ∂□_m = ∅` and gated at the literal `1/2` event
  `𝒢(n+2, z; s/8, 1/2)`, with its own `n+2` windows and its own `s`-powers.

Here `𝓔_{n+3} = fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩ (τ_z ω)` is the
coarse-graining error factor read at the clause's own flux slot, and `σ_n` is
the annealed comparator at the child scale.

## The flux-corrected error factor on the flat leg

The last leg is the manuscript's scale-weighted window average of `∇h`, carried
**multiplied by `𝓔`**.  Bounding `𝓔 · 1_𝒢` by a constant multiple of the event's
own threshold is a monotone one-way step; the chain below declines it on that
row, so the leg vanishes with the flux-corrected error instead of being priced
against it.  The row is re-proved rather than transferred, through
`AssemblyComposedErrorWeighted` and `ResidueRouteOneErrorWeighted` (the two
composition sites), `ResiduePluginErrorWeighted` and
`StitchDisplayLegsErrorWeighted` (the residue lane's second consumer),
`AssemblyBoundaryClauseErrorWeighted` and `ProviderBoundaryErrorWeighted` (the
repackaging), and `RebaseGeneralClauseErrorWeighted`, `RebaseJoinErrorWeighted`,
`RebaseSealDistanceErrorWeighted` (statement-only re-typings, the leg being pure
nonnegative slack on the frontier-empty branch).

## The last step, and what it costs

`exists_harmonicApproximation_provider_of_boundaryClauseReal_errorWeighted`
delivers the display with that leg still in normalized-`L²` form.  The mean-zero
fractional Poincaré inequality on the `n+3` window (`GradHSplit`) turns it into
the printed average leg plus a multiple of the display's own Gagliardo `∇h` leg,

```text
  ‖∇h‖_{L²(W')} ≤ ‖(∇h)_W‖ + C(d)·3^{ns}·[∇h]_{H^s(W')} ,
```

and `3^n · 3^{ns} = 3^{(1+s)n}` is exactly that leg's weight, so **no `s`-power
is consumed**.  The remainder carries `𝓔`, which is shed under the good-event
indicator by the proved caps step
`ReindexSlot.ae_errorRepresentative_le_harmonicSlot_addThree` (`𝓔 ≤ C_𝓔/2`
there).  The whole price is the constant re-choice
`C := max ((1 + κ(d)·C_𝓔/2)·C₀) (max 2 C_𝓔)`, a function of `d` alone.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the coarse-graining energy
  slot and the flat `∇h` leg.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-- **The one arithmetic move of the recut, in the abstract.**

The incoming display's normalized-`L²` flat leg `e·Hn` is replaced by the
printed average leg `F` plus a multiple `G·P` of the display's own Gagliardo
`∇h` leg; the widened Gagliardo coefficient `c₃ + G` is absorbed into the
re-chosen one.  Nothing here is a norm: every letter is a free element of
`ℝ≥0∞`. -/
private theorem flatLeg_absorb {a b c3 e F G P Hn A1 B1 C3' F' : ℝ≥0∞}
    (h1 : a ≤ A1) (h2 : b ≤ B1) (hsplit : e * Hn ≤ F + G * P)
    (h3 : c3 + G ≤ C3') (h5 : F ≤ F') :
    a + b + c3 * P + e * Hn ≤ A1 + B1 + C3' * P + F' := by
  calc a + b + c3 * P + e * Hn ≤ a + b + c3 * P + (F + G * P) := add_le_add le_rfl hsplit
    _ = a + b + (c3 + G) * P + F := by ring
    _ ≤ A1 + B1 + C3' * P + F' :=
        add_le_add (add_le_add (add_le_add h1 h2) (mul_le_mul_left h3 P)) h5

/-- Monotonicity of a three-factor product in its leading constant. -/
private theorem mul_three_mono {C C' a b : ℝ} (h : C ≤ C') (ha : 0 ≤ a) (hb : 0 ≤ b) :
    C * a * b ≤ C' * a * b :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb

/-- Monotonicity of a four-factor product in its leading constant. -/
private theorem mul_four_mono {C C' a b c : ℝ} (h : C ≤ C') (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : C * a * b * c ≤ C' * a * b * c :=
  mul_le_mul_of_nonneg_right (mul_three_mono h ha hb) hc

private theorem harmonicApproximationProvider_comparisonBounds1 :
  ∀ (d : ℕ) (C0 : ℝ) (_ : (0 : ℝ) < C0) (M : ABKModel d) (s : ℝ) (hs : (0 : ℝ) < s) (L m n : ℤ)
   (z : Vec d) (omega : Cutoff.CutoffSample d) (h : H1Function (openCubeSet (originCube d m))),
   (0 : ℝ) ≤ s.rpow (-4 : ℝ) ∧
    (0 : ℝ) ≤ s.rpow (-6 : ℝ) ∧
     (0 : ℝ) ≤ s.rpow (-7 : ℝ) ∧
      (0 : ℝ) ≤ s.rpow (-(19 / 2 : ℝ)) ∧
       (0 : ℝ) ≤ Real.rpow (3 : ℝ) (↑n : ℝ) ∧
        (0 : ℝ) ≤ Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) ∧
         (0 : ℝ) ≤ (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ ∧
          (0 : ℝ) ≤
            Support.fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
             ⟨s / (8 : ℝ), by exact div_pos hs (by norm_num)⟩
             (Cutoff.translateCutoffSample z omega) ∧
           (0 : ℝ) ≤
             Support.fluxCorrectedErrorRepresentative M L (n + (2 : ℤ))
              ⟨s / (8 : ℝ), by exact div_pos hs (by norm_num)⟩
              (Cutoff.translateCutoffSample z omega) ∧
            (0 : ℝ) ≤
              C0 * s.rpow (-6 : ℝ) *
                Support.fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                 ⟨s / (8 : ℝ), by exact div_pos hs (by norm_num)⟩
                 (Cutoff.translateCutoffSample z omega) *
               Real.rpow (3 : ℝ) (↑n : ℝ) ∧
             Integrable h.grad
               (volume.restrict
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3
                 : ℤ))) ∩
                 openCubeSet (originCube d m))) ∧
              Real.rpow (3 : ℝ) (↑n : ℝ) * Real.rpow (3 : ℝ) ((↑n : ℝ) * s) =
               Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))  := by
  intro d C0 hC0pos M s hs L m n z omega h
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS19 : (0 : ℝ) ≤ Real.rpow s (-(19 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hR3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hQ1s : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsig : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hflux3 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hflux2 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 2)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hcoef0 : (0 : ℝ) ≤ C0 * Real.rpow s (-(6 : ℝ)) *
      Support.fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
      Real.rpow (3 : ℝ) (n : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0pos.le hS6) hflux3) hR3n
  -- `∇h` is integrable on the `n+3` window
  have hfin : IsFiniteMeasure (volume.restrict
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (volume_anchorWindow_ne_top (n + 3) m z)
  have hgradint : Integrable h.grad (volume.restrict
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) :=
    (h.grad_memVectorL2.mono_measure
      (Measure.restrict_mono Set.inter_subset_right le_rfl)).integrable (by norm_num)
  -- the `3`-power bookkeeping: `3^n · 3^{ns} = 3^{(1+s)n}`
  have h3mul : Real.rpow (3 : ℝ) (n : ℝ) * Real.rpow (3 : ℝ) ((n : ℝ) * s) =
      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by
    have hbase := Real.rpow_add (by norm_num : (0 : ℝ) < 3) ((n : ℝ)) ((n : ℝ) * s)
    have hexp : (n : ℝ) + (n : ℝ) * s = (1 + s) * (n : ℝ) := by ring
    rw [hexp] at hbase
    exact hbase.symm
  exact ⟨hS4, hS6, hS7, hS19, hR3n, hQ1s, hsig, hflux3, hflux2, hcoef0, hgradint, h3mul⟩

/-- **`l.harmonic.approximation.good.scales`, the provider — unconditional.**

The harmonic-approximation display on good scales, with the general clause's
flat leg carried as the manuscript's own scale-weighted window average of `∇h`
at the `n+2` window, multiplied by the clause's own coarse-graining error factor
`𝓔`.  Proved by running the boundary chain with the monotone error discard
declined on that one row (`ProviderBoundaryErrorWeighted`,
`RebaseSealDistanceErrorWeighted`) and then applying the fractional Poincaré
split of `GradHSplit`. -/
theorem harmonic_approximation_provider (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : HCPolySupport.Vec d,
            x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            z ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            (fun y => x + y) '' HCPolySupport.openCubeSet (HCPolySupport.originCube d n) ⊆
              ((fun y => z + y) ''
                  HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 1))) ∩
                HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u h : HCPolySupport.H1Function
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                (g : HCPolySupport.Vec d → HCPolySupport.Vec d),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (HCPolySupport.originCube d m) u h g →
                MeasureTheory.MemLp g 2
                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 g) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                ∀ (v : HCPolySupport.H1Function
                      ((fun y => x + y) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d n)))
                  (w : HCPolySupport.H10Function
                      ((fun y => x + y) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d n))),
                  Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                      ((fun y => x + y) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  (Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                          ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              ((fun y => x + y) ''
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d n))))
                        omega ≤
                      ENNReal.ofReal
                          (C * Real.rpow s (-(4 : ℝ)) *
                            Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                              (n + 3) ⟨s / 8, by linarith only [hs]⟩
                              (Cutoff.translateCutoffSample z omega)) *
                        (MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                HCPolySupport.volumeAverage
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 3))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) +
                          ENNReal.ofReal
                            (Real.rpow s (-(3 / 2 : ℝ)) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              ‖HCPolySupport.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 2))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  h.grad‖)) +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(7 : ℝ)) *
                              (Annealed.sigmaBar M n : ℝ)⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                HCPolySupport.openCubeSet
                                  (HCPolySupport.originCube d (n + 3))) ∩
                              HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s g +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                HCPolySupport.openCubeSet
                                  (HCPolySupport.originCube d (n + 3))) ∩
                              HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s
                            h.grad +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              ‖HCPolySupport.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 2))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  h.grad‖)) ∧
                    ((((fun y' => z + y') ''
                            HCPolySupport.openCubeSet
                              (HCPolySupport.originCube d (n + 2))) ∩
                          frontier
                            (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) =
                        ∅) →
                      Set.indicator
                          (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 2) z
                            ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
                          (fun _omega' =>
                            MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                ((fun y => x + y) ''
                                  HCPolySupport.openCubeSet (HCPolySupport.originCube d n))))
                          omega ≤
                        ENNReal.ofReal
                            (C * Real.rpow s (-(4 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 2) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega)) *
                          MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                HCPolySupport.volumeAverage
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 2))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 2))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) +
                          ENNReal.ofReal
                              (C * Real.rpow s (-(19 / 2 : ℝ)) *
                                (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                            Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 2))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s g)
    := by
  classical
  obtain ⟨C0, hC0pos, hmain⟩ :=
    exists_harmonicApproximation_provider_of_boundaryClauseReal_errorWeighted d
      (exists_boundaryClauseReal_errorWeighted d)
  obtain ⟨CE, hCEpos, hcapE⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  have hkappos : 0 < gradHSplitConst d := gradHSplitConst_pos d
  have hfac1 : (1 : ℝ) ≤ 1 + gradHSplitConst d * (CE * (1 / 2)) := by
    have : (0 : ℝ) < gradHSplitConst d * (CE * (1 / 2)) := by positivity
    linarith only [this]
  have hle2 : (2 : ℝ) ≤ max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) :=
    le_trans (le_max_left 2 CE) (le_max_right _ _)
  have hleCE : CE ≤ max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) :=
    le_trans (le_max_right 2 CE) (le_max_right _ _)
  have hleK : (1 + gradHSplitConst d * (CE * (1 / 2))) * C0 ≤
      max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) := le_max_left _ _
  have hCle : C0 ≤ max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) :=
    le_trans (le_mul_of_one_le_left hC0pos.le hfac1) hleK
  have hCpos : (0 : ℝ) <
      max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) :=
    lt_of_lt_of_le (by norm_num) hle2
  refine ⟨max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE), hCpos, ?_⟩
  intro M s hsIcc hgam1 hgam2 hs L m n hmL hnm x z hx hz hsub
  have hs1 : s ≤ 1 := hsIcc.2
  have hinvle : (max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE))⁻¹ ≤ C0⁻¹ :=
    inv_anti₀ hC0pos hCle
  -- the two hoisted hypotheses, read at the smaller constant
  have hgam1' : M.gamma ≤ C0⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    have hc : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) := by positivity
    exact hgam1.trans (mul_le_mul_of_nonneg_right hinvle hc)
  have hgam2' : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C0⁻¹ * s ^ (4 : ℕ)) := by
    have hpre : (0 : ℝ) ≤ Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hs]) _) (by positivity)
    have hstep : (max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE))⁻¹ *
        s ^ (4 : ℕ) ≤ C0⁻¹ * s ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right hinvle (by positivity)
    exact hgam2.trans (mul_le_mul_of_nonneg_left hstep hpre)
  -- the `(1/2)`-slot reads that the caps step consumes
  have hep0 : (0 : ℝ) ≤
      (max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE))⁻¹ * s ^ (4 : ℕ) :=
    clauseEpsilon_nonneg hCpos hs.le
  have hephalf : (max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE))⁻¹ *
      s ^ (4 : ℕ) ≤ 1 / 2 := clauseEpsilon_le_half hle2 hs.le hs1
  have hepC0 : (max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE))⁻¹ *
      s ^ (4 : ℕ) ≤ C0⁻¹ * s ^ (4 : ℕ) := clauseEpsilon_anti hC0pos hCle hs.le
  have hfundHalf : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) :=
    funding_le_of_epsilon_le hs hephalf hgam2
  have hregimeCE : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hgam1.trans (mul_le_mul_of_nonneg_right (inv_anti₀ hCEpos hleCE) (by positivity))
  filter_upwards [hmain M s hsIcc hgam1' hgam2' hs L m n hmL hnm x z hx hz hsub,
    hcapE M s hsIcc hregimeCE hfundHalf hs n z] with omega homega hcapw
  intro u h g hdir hg2 hgG hhG v w hharm hval hgrad
  obtain ⟨hgen, hint⟩ := homega u h g hdir hg2 hgG hhG v w hharm hval hgrad
  obtain ⟨hS4, hS6, hS7, hS19, hR3n, hQ1s, hsig, hflux3, hflux2, hcoef0, hgradint, h3mul⟩ :=
    @harmonicApproximationProvider_comparisonBounds1 (d) (C0) (hC0pos) (M) (s) (hs) (L) (m) (n)
      (z) (omega) (h)
  refine ⟨?_, ?_⟩
  · refine indicator_le_of_mem ?_
    intro hmemC
    have hmem0 := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
      (Support.cgEllipLowerConstant d) (n + 3) z ⟨s / 8, by linarith only [hs]⟩
      hep0 hepC0 hmemC
    have hmemHalf := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
      (Support.cgEllipLowerConstant d) (n + 3) z ⟨s / 8, by linarith only [hs]⟩
      hep0 hephalf hmemC
    have hErepCap : Support.fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) ≤
        CE * (1 / 2) := hcapw hmemHalf L (le_trans hnm hmL)
    rw [Set.indicator_of_mem hmem0] at hgen
    refine le_trans hgen ?_
    refine flatLeg_absorb
      (F := ENNReal.ofReal (C0 * Real.rpow s (-(6 : ℝ)) *
        Support.fluxCorrectedErrorRepresentative M L (n + 3)
          ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
        Real.rpow (3 : ℝ) (n : ℝ) *
        ‖volumeAverageVec
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
              openCubeSet (originCube d m))) h.grad‖))
      (G := ENNReal.ofReal (C0 * gradHSplitConst d * Real.rpow s (-(6 : ℝ)) *
        Support.fluxCorrectedErrorRepresentative M L (n + 3)
          ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
        Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)))) ?_ ?_ ?_ ?_ ?_
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_three_mono hCle hS4 hflux3)) _
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_four_mono hCle hS7 hsig hQ1s)) _
    · -- the fractional Poincaré split, applied to the `𝓔`-multiplied leg
      have hsplit := eLpNorm_windowThree_le_volumeAverageVec_windowTwo_add_gagliardo
        (n := n) (m := m) (x := x) (z := z) (s := s) (f := h.grad) hz hnm hs.le hs1 hsub
        hgradint
      have hring : C0 * Real.rpow s (-(6 : ℝ)) *
          Support.fluxCorrectedErrorRepresentative M L (n + 3)
            ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
          Real.rpow (3 : ℝ) (n : ℝ) *
          (gradHSplitConst d * Real.rpow (3 : ℝ) ((n : ℝ) * s)) =
          C0 * gradHSplitConst d * Real.rpow s (-(6 : ℝ)) *
            Support.fluxCorrectedErrorRepresentative M L (n + 3)
              ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by
        rw [← h3mul]
        ring
      calc ENNReal.ofReal (C0 * Real.rpow s (-(6 : ℝ)) *
            Support.fluxCorrectedErrorRepresentative M L (n + 3)
              ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
            Real.rpow (3 : ℝ) (n : ℝ)) *
            eLpNorm h.grad 2 (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))
          ≤ ENNReal.ofReal (C0 * Real.rpow s (-(6 : ℝ)) *
              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
              Real.rpow (3 : ℝ) (n : ℝ)) *
              (ENNReal.ofReal ‖volumeAverageVec
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
                    openCubeSet (originCube d m))) h.grad‖ +
                ENNReal.ofReal (gradHSplitConst d * Real.rpow (3 : ℝ) ((n : ℝ) * s)) *
                  Support.normalizedGagliardoESeminormOn
                    ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                      openCubeSet (originCube d m))) s h.grad) :=
            mul_le_mul_right hsplit _
        _ = ENNReal.ofReal (C0 * Real.rpow s (-(6 : ℝ)) *
                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                  ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
                Real.rpow (3 : ℝ) (n : ℝ) *
                ‖volumeAverageVec
                    ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
                      openCubeSet (originCube d m))) h.grad‖) +
              ENNReal.ofReal (C0 * gradHSplitConst d * Real.rpow s (-(6 : ℝ)) *
                  Support.fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) *
                  Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) s h.grad := by
            rw [mul_add, ← ENNReal.ofReal_mul hcoef0, ← mul_assoc,
              ← ENNReal.ofReal_mul hcoef0, hring]
    · -- the widened Gagliardo coefficient: H the discard is taken, on the event
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC0pos.le hS6) hQ1s)
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0pos.le hkappos.le) hS6)
          hflux3) hQ1s)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
        mul_nonneg hS6 hQ1s
      have hcoefle : C0 * (1 + gradHSplitConst d *
          Support.fluxCorrectedErrorRepresentative M L (n + 3)
            ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega)) ≤
          max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) := by
        have hkap := mul_le_mul_of_nonneg_left hErepCap hkappos.le
        have hstep : C0 * (1 + gradHSplitConst d *
            Support.fluxCorrectedErrorRepresentative M L (n + 3)
              ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega)) ≤
            C0 * (1 + gradHSplitConst d * (CE * (1 / 2))) :=
          mul_le_mul_of_nonneg_left (by linarith only [hkap]) hC0pos.le
        have hcomm : C0 * (1 + gradHSplitConst d * (CE * (1 / 2))) =
            (1 + gradHSplitConst d * (CE * (1 / 2))) * C0 := by ring
        linarith only [hstep, hcomm, hleK]
      have hmul := mul_le_mul_of_nonneg_right hcoefle hb
      calc C0 * Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) +
            C0 * gradHSplitConst d * Real.rpow s (-(6 : ℝ)) *
              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))
          = C0 * (1 + gradHSplitConst d *
              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega)) *
              (Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) := by
            ring
        _ ≤ max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) *
              (Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) := hmul
        _ = max ((1 + gradHSplitConst d * (CE * (1 / 2))) * C0) (max 2 CE) *
              Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by ring
    · refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_mul_of_nonneg_right (mul_four_mono hCle hS6 hflux3 hR3n)
        (norm_nonneg _)
  · intro hfront
    refine le_trans (hint hfront) ?_
    refine add_le_add ?_ ?_
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_three_mono hCle hS4 hflux2)) _
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_four_mono hCle hS19 hsig hQ1s)) _

end

end Algsuperdiff.Section4.Provider.ExcessDecay
