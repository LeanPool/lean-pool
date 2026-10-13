/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SigmaBarIndex
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell

/-!
# HarmonicProviderFinalInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The frozen theorem's interior clause, in the frozen theorem's own shape

`InteriorComposed.exists_interiorClause_honest` is a **real** inequality between
`toReal` values, at `σ_{n+2}^{-1}`, under the standing `[NeZero d]`.  The frozen
anchor's second (frontier-empty) clause is an **`ℝ≥0∞`** inequality with an
indicator on the left, at `σ_n^{-1}`, and quantifies over a bare `(d : ℕ)`.
This module closes that distance:

* the `σ` index move `σ_{n+2}^{-1} ≤ 4 σ_n^{-1}`, binder-free inside the
  anchor's own regime (`SigmaBarIndex.exists_inv_sigmaBar_add_two_le`);
* the `ℝ≥0∞` shell (`EnnrealShell`): the indicator collapse, the finiteness of
  the anchor's left-hand side through its own `H¹₀` witness, and the
  `ofReal`-product regrouping;
* the `d = 0` branch: `ABKModel d` carries `2 ≤ d` (`ShellLawPrefix.dimension`),
  so the universally quantified statement is vacuous there and `[NeZero d]` is
  *not* part of this export.

The conclusion is the frozen block's second conjunct **verbatim**: same gate,
same indicator, same good event at `(n+2, z, s/8, 1/2)`, same
`fluxCorrectedErrorRepresentative` at the translated sample, same
mean-subtracted parent norm, same `normalizedGagliardo` on the
parent-intersected window, same two `s`-powers `-4` and `-19/2`, same
`σ_n^{-1}` and `3^{(1+s)n}`.  Nothing is weakened and no exponent is moved.

## What is *not* here (disclosed)

The anchor's **first** clause (the unconditional general clause, force leg at
`s^{-7}`, both `∇h` legs) is not proved here and is not implied by this one:
the two clauses are incomparable (`s^{-19/2} ≥ s^{-7}` on `(0,1]`), so the
provider-final still needs the boundary lane.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Frozen/Section4/HarmonicApproximation.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. The constant absorption, on abstract reals -/

/-- The two-summand constant absorption of the assembly: the first summand pays
`Cfin ≤ C`, the second pays `4 Cfin ≤ C` against the `σ` index ratio.  Stated on
abstract reals so that no `Real.rpow` atom is ever unfolded. -/
private theorem interior_constant_absorb {Cf C p e xr r sg2 sgn q yr : ℝ}
    (hCf : 0 ≤ Cf) (hp : 0 ≤ p) (he : 0 ≤ e) (hxr : 0 ≤ xr) (hr : 0 ≤ r)
    (hsgn : 0 ≤ sgn) (hq : 0 ≤ q) (hyr : 0 ≤ yr) (hratio : sg2 ≤ 4 * sgn)
    (h1 : Cf ≤ C) (h4 : 4 * Cf ≤ C) :
    Cf * (p * e * xr + r * sg2 * q * yr) ≤ C * p * e * xr + C * r * sgn * q * yr := by
  have hpx : (0 : ℝ) ≤ p * e * xr := mul_nonneg (mul_nonneg hp he) hxr
  have hrqy : (0 : ℝ) ≤ r * (q * yr) := mul_nonneg hr (mul_nonneg hq hyr)
  have hA : Cf * (p * e * xr) ≤ C * p * e * xr := by
    have h := mul_le_mul_of_nonneg_right h1 hpx
    linarith only [h]
  have hstep : sg2 * (r * (q * yr)) ≤ 4 * sgn * (r * (q * yr)) :=
    mul_le_mul_of_nonneg_right hratio hrqy
  have hB : Cf * (r * sg2 * q * yr) ≤ C * r * sgn * q * yr := by
    calc Cf * (r * sg2 * q * yr)
        = Cf * (sg2 * (r * (q * yr))) := by ring
      _ ≤ Cf * (4 * sgn * (r * (q * yr))) := mul_le_mul_of_nonneg_left hstep hCf
      _ = 4 * Cf * (sgn * (r * (q * yr))) := by ring
      _ ≤ C * (sgn * (r * (q * yr))) :=
          mul_le_mul_of_nonneg_right h4 (mul_nonneg hsgn hrqy)
      _ = C * r * sgn * q * yr := by ring
  linarith only [hA, hB]

/-! ## 2. The interior clause at the frozen theorem's own shape -/

/-- **The anchor's second (frontier-empty) clause, verbatim.**

Entered at the frozen theorem's own binders and concluded in the frozen
theorem's own `ℝ≥0∞` carriers, with the anchor's own two `s`-powers.  This is
the exact second conjunct of the frozen block, under a provider name and with
no standing `NeZero` hypothesis. -/
theorem exists_interiorClause_anchorShape (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 2 ≤ m →
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
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s
                              g) := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension (by omega)
  have : NeZero d := ⟨hd⟩
  obtain ⟨CI, Cfin, hCI, hCfin, hI⟩ := exists_interiorClause_honest d
  obtain ⟨CS, hCS, hS⟩ := exists_inv_sigmaBar_add_two_le d
  have hleI : CI ≤ max (max CI CS) (4 * Cfin) :=
    le_trans (le_max_left CI CS) (le_max_left _ _)
  have hleS : CS ≤ max (max CI CS) (4 * Cfin) :=
    le_trans (le_max_right CI CS) (le_max_left _ _)
  have hle4 : 4 * Cfin ≤ max (max CI CS) (4 * Cfin) := le_max_right _ _
  have hCpos : (0 : ℝ) < max (max CI CS) (4 * Cfin) := lt_of_lt_of_le hCI hleI
  have hfin1 : Cfin ≤ max (max CI CS) (4 * Cfin) := by linarith only [hCfin, hle4]
  refine ⟨max (max CI CS) (4 * Cfin), hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z _hx hz hgeom
  have hregimeI : M.gamma ≤ CI⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCI hleI
    rw [one_div, one_div] at h1
    exact h1
  have hregimeS : M.gamma ≤ CS⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCS hleS
    rw [one_div, one_div] at h1
    exact h1
  have hratio := hS M hregimeS n
  by_cases hfr : ((fun y' => z + y') ''
      HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 2))) ∩
      frontier (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) = ∅
  · filter_upwards [hI M s hsrange hregimeI hsmall hs L m n hmL hnm x z hz hgeom hfr]
      with omega hom
    intro u hdat g hsol hgL2 hgW _hhW v w hharm hval hgrad _hgate
    have hne : eLpNorm (fun y => u.toFun y - v.toFun y) 2
        (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
          ((fun y => x + y) '' openCubeSet (originCube d n))) ≠ ⊤ :=
      eLpNorm_ne_top_of_eq_h10 (volume_image_add_openCubeSet_ne_zero x (originCube d n)) w
        (fun y => by rw [hval y]; ring)
    refine indicator_le_of_mem ?_
    intro hmem
    have hreal := hom hmem u hdat g hsol hgL2 hgW v w hharm hval hgrad
    refine le_ofReal_mul_add_ofReal_mul hne ?_ ?_ ?_
    · refine mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hs.le _)) ?_
      exact Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
    · refine mul_nonneg (mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hs.le _)) ?_)
        (Real.rpow_nonneg (by norm_num) _)
      exact inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
    · refine hreal.trans ?_
      refine interior_constant_absorb hCfin.le (Real.rpow_nonneg hs.le _)
        (Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _)
        ENNReal.toReal_nonneg (Real.rpow_nonneg hs.le _)
        (inv_nonneg.mpr (Annealed.sigmaBar M n).2.le) (Real.rpow_nonneg (by norm_num) _)
        ENNReal.toReal_nonneg hratio hfin1 hle4
  · filter_upwards with omega
    intro u _hdat _g _hsol _hgL2 _hgW _hhW _v _w _hharm _hval _hgrad hgate
    exact absurd hgate hfr

end

end Algsuperdiff.Section4.Provider.ExcessDecay
