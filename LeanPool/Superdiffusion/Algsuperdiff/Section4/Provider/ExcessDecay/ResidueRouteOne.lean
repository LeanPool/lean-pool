/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueEnergyLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapChild
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueFlushTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# ResidueRouteOne

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Route 1, machine-assembled at the flush sub-cube `K'`

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

derived, from the *shapes* of the proved theorems, that the `p = 2`
coarse-graining comparison read at the flush scale-`n` sub-cube `K' =
flushSubCentre z m n i σ + □_n` prices the harmonic-approximation residue `‖u −
w‖_{L²(K')}` on the five canonical legs, but could not assemble it, because
the proved caps carry the anchor's geometry binder and `K'` provably fails it.
This module *is* that assembly:

```text
  ‖u − w‖_{L²(K')} ≤ Cfin ·
      ( s^{-4}·𝓔·‖u − (u)_{W'}‖_{L²(W')}
      + s^{-7}·σ_{n+3}^{-1}·3^{(1+s)n}·[g]_{H^s(W')}
      + s^{-6}·3^{(1+s)n}·[∇h]_{H^s(W')}
      + s^{-6}·3^{n}·‖∇h‖_{L²(W')}
      + s^{-4}·𝓔·S )
```

with `𝓔 = fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩ (translate z ω)`
carried **explicitly** (not substituted by the frozen good event's `ε = 1/2`),
and `S` the boundary scalar at the flush cube `K = wellPlacedCentre z m (n+2) +
□_{n+2}` — which is the covering cube of `K'`
(`ResidueCapGeometry.wellPlacedCentre_flushSubCentre`).

* the deterministic `x`-frame envelope
  `ReindexEllipticity.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree`
  (binder-free: it needs only `translateSet x □_n ⊆ □_m`);
* the boundary energy leg at the two hinges (`ResidueEnergyLeg`);
* the child cube's `𝓔`-cap and forcing bracket at hinge (C)
  (`ResidueCapChild`);
* the **one-hop** Gagliardo transport `K' → W'` (`ResidueFlushTransport`) in
  place of the proved two-hop route through the `(n+2)` window, which `K'` does
  not meet.

## The `σ`-cancellation, machine-verified

The envelope is divided by `σ₀ = σ_{n+3}` and the energy term carries
`‖a₀‖^{1/2} = √σ_{n+3}` (`constantCoeffMatrixNormHalf_scalarComparator_sqrt`).
The two identities `√σ·√σ = σ` and `√σ·√(σ^{-1}) = 1` are consumed at `h1` and `h2`
below: they cancel `σ` exactly on the four `√σ` legs and leave exactly one
`σ^{-1}` on the force leg.  **No `ν` is divided anywhere**: CoarseGraining's
`h1EnergyNormOnCube` at the re-based family equals `√(ν·⨍|∇u|²)`, and that
quantity is consumed *whole* by the boundary energy leg — it is never converted
to a Euclidean gradient.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-- **Route 1, composed at the flush sub-cube.**

The harmonic-approximation residue at `K'`, priced on the five canonical legs
with the good-event error `𝓔` carried explicitly. -/
theorem exists_flushResidue_route1_composed (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
          ∀ (i : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) →
            wellPlacedHalfGap m (n + 2) < σ * z i →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (S : ℝ),
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
                      (fun y => u.toFun y - hdat.toFun y)| ≤ S →
                  ∀ (v : H1Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n)))
                    (w : H10Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => flushSubCentre z m n i σ + y) ''
                          openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                        (Support.normalizedVolumeMeasureOn
                          ((fun y => flushSubCentre z m n i σ + y) ''
                            openCubeSet (originCube d n)))).toReal ≤
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
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(7 : ℝ)) *
                              ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s hdat.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) * S) := by
  classical
  obtain ⟨CE, hCEpos, hCE⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  obtain ⟨CB, KE, hCBpos, hKEpos, hEnergyLeg⟩ :=
    ae_h1EnergyNormOnCube_boundary_le_anchorLegs_atHinges d
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  have hkappa : 0 ≤ kappa := mul_nonneg (Real.sqrt_nonneg _) (by norm_num)
  set e0 : ℝ := kappa * (CE * (1 / 2)) with he0def
  have he0 : 0 ≤ e0 := mul_nonneg hkappa (mul_nonneg hCEpos.le (by norm_num))
  set k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1) with hk0def
  have hk0 : 0 ≤ k0 :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg d))
      (add_nonneg (sq_nonneg e0) zero_le_one)
  set b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0 with hb0def
  have hb0 : 0 ≤ b0 :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) he0) (mul_nonneg zero_le_two hk0)
  set cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d with hcgdef
  have hcg : 0 ≤ cg :=
    mul_nonneg (mul_nonneg (by norm_num) (negNormBaseConst_pos d).le)
      (coarseGrainingP2Const_pos d).le
  set A1 : ℝ := cg * 216 * (kappa * KE) with hA1def
  have hA1 : 0 ≤ A1 := by
    rw [hA1def]
    exact mul_nonneg (mul_nonneg hcg (by norm_num)) (mul_nonneg hkappa hKEpos.le)
  set A2 : ℝ := cg * 1944 * (b0 * (besovGagliardoConstant d * flushWindowConst d))
    with hA2def
  have hA2 : 0 ≤ A2 := by
    have h1 : 0 ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
    have h3 : 0 < flushWindowConst d := flushWindowConst_pos d
    rw [hA2def]
    exact mul_nonneg (mul_nonneg hcg (by norm_num))
      (mul_nonneg hb0 (mul_nonneg h1 h3.le))
  set A3 : ℝ := interiorCorrectionConst d * flushWindowConst d with hA3def
  have hA3 : 0 ≤ A3 := by
    have h1 : 0 < interiorCorrectionConst d := interiorCorrectionConst_pos d
    have h3 : 0 < flushWindowConst d := flushWindowConst_pos d
    rw [hA3def]
    exact mul_nonneg h1.le h3.le
  have hCE2 : (0 : ℝ) ≤ 9 * (CE * (1 / 2)) * A1 :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCEpos.le (by norm_num))) hA1
  have hCE3 : (0 : ℝ) ≤ CE * (1 / 2) * A1 :=
    mul_nonneg (mul_nonneg hCEpos.le (by norm_num)) hA1
  refine ⟨max CE CB,
    A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1,
    lt_of_lt_of_le hCEpos (le_max_left _ _),
    add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hA1 hCE2) hCE3) hA2) hA3)
      zero_lt_one, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
  have hregimeCE : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans
      (mul_le_mul_of_nonneg_right ?_ (Even.pow_nonneg (by norm_num) _))
    have h1 := one_div_le_one_div_of_le hCEpos (le_max_left CE CB)
    rw [one_div, one_div] at h1
    exact h1
  have hregimeCB : M.gamma ≤ CB⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans
      (mul_le_mul_of_nonneg_right ?_ (Even.pow_nonneg (by norm_num) _))
    have h1 := one_div_le_one_div_of_le hCBpos (le_max_right CE CB)
    rw [one_div, one_div] at h1
    exact h1
  have hxc : flushSubCentre z m n i sigma ∈ openCubeSet (originCube d m) :=
    flushSubCentre_mem_openCubeSet hnm2 z i hsigma
  have hcov : (fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
    image_add_flushCoveringCube_subset_anchorWindow hnm2 hz i hsigma
  have hPhinge : translateSet
      (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) - z)
      (cubeSet (originCube d (n + 2))) ⊆ cubeSet (originCube d (n + 3)) :=
    translateSet_cubeSet_flushCoveringCube_subset_anchorParent hnm2 hz i hsigma
  have hChinge : translateSet (flushSubCentre z m n i sigma - z)
      (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 3)) :=
    translateSet_cubeSet_flushSubCube_subset_anchorParent hnm2 hz i hsigma
  filter_upwards [hCE M s hsrange hregimeCE hsmall hs n z,
    hEnergyLeg M s hsrange hregimeCB hsmall hs L m n hmL hnm
      (flushSubCentre z m n i sigma) z hxc hcov hPhinge,
    ae_coarseGrainingErrorAtDepth_rebased_le_representative_gapThree M L n z hs hs1,
    ae_forceBracket_rebased_le_gapThree M L n z hs hs1] with omega hcapE hEnLeg herrD hbrk
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hsubx : translateSet (flushSubCentre z m n i sigma)
      (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m) :=
    translateSet_flushSubCube_subset_openCubeSet hnm2 z i hsigma
  have hsubimg : (fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n) ⊆ openCubeSet (originCube d m) :=
    flushSubCube_subset_openCubeSet hnm2 z i hsigma
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 :=
    volume_anchorWindow_ne_zero_of_flushSubCube hnm2 hz i hsigma
  have hgWW3 := memLp_normalizedGagliardoMeasureOn_subset
    (Set.inter_subset_right
      (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 3))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  -- the deterministic `x`-frame composition at `K'`
  have hxf := eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree (z := z) M L omega
    hs hs1 hsubx u hdat g hsol hgL2 hgW v w hharm hval hgrad
    (Annealed.sigmaBar M (n + 3)).2
  -- the energy leg, at the covering cube of `K'`
  have hmeanFlush : |volumeAverage
      ((fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
      (fun y => u.toFun y - hdat.toFun y)| ≤ S := by
    rw [wellPlacedCentre_flushSubCentre hnm2 hsigma hover]
    exact hmean
  have hEn := hEnLeg hmem u hdat g S hsol hgL2 hgW hhW hmeanFlush hsubx
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  have hErepCap : Erep ≤ CE * (1 / 2) := hcapE hmem L (le_trans hnm hmL)
  have hErep0 : 0 ≤ Erep := Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (3 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
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
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => flushSubCentre z m n i sigma + y) ''
          openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hP2def
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set S6 : ℝ := Real.rpow s (-(6 : ℝ)) with hS6def
  set Sm3 : ℝ := Real.rpow s (-(3 : ℝ)) with hSm3def
  set Sm2 : ℝ := Real.rpow s (-(2 : ℝ)) with hSm2def
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hGs0 : 0 ≤ Gs := ENNReal.toReal_nonneg
  have hHs0 : 0 ≤ Hs := ENNReal.toReal_nonneg
  have hHn0 : 0 ≤ Hn := ENNReal.toReal_nonneg
  have hYchild0 : 0 ≤ Ychild := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) hmean
  have hP20 : 0 ≤ P2 := Real.rpow_nonneg (by norm_num) _
  have hQ3s0 : 0 ≤ Q3s := Real.rpow_nonneg (by norm_num) _
  have hQ3sn0 : 0 ≤ Q3sn := Real.rpow_nonneg (by norm_num) _
  have hQ1s0 : 0 ≤ Q1s := Real.rpow_nonneg (by norm_num) _
  have hR3n0 : 0 ≤ R3n := Real.rpow_nonneg (by norm_num) _
  have hS40 : 0 ≤ S4 := Real.rpow_nonneg hs.le _
  have hS70 : 0 ≤ S7 := Real.rpow_nonneg hs.le _
  have hS60 : 0 ≤ S6 := Real.rpow_nonneg hs.le _
  have hSm30 : 0 ≤ Sm3 := Real.rpow_nonneg hs.le _
  have hSm20 : 0 ≤ Sm2 := Real.rpow_nonneg hs.le _
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  -- the off-grid error factor
  have hEb0 : 0 ≤ Eb := by
    rw [hEbdef]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0)
  have hEbkappa : Eb ≤ kappa * Erep := by
    have h1 : Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) ≤
        Real.sqrt (192 * (d : ℝ)) :=
      Real.sqrt_le_sqrt (offGridStabilityConst_slot_le hs hs1)
    have h2 : ((3 : ℝ) ^ (3 * (s / 8))) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [hs1] : 3 * (s / 8) ≤ (1 : ℝ))
      rwa [Real.rpow_one] at h
    have h3 : (3 : ℝ) ^ (3 * (s / 8)) * Erep ≤ 3 * Erep :=
      mul_le_mul_of_nonneg_right h2 hErep0
    have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ (3 * (s / 8)) * Erep :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
    rw [hEbdef]
    calc Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
          ((3 : ℝ) ^ (3 * (s / 8)) * Erep)
        ≤ Real.sqrt (192 * (d : ℝ)) * (3 * Erep) :=
          mul_le_mul h1 h3 h4 (Real.sqrt_nonneg _)
      _ = kappa * Erep := by rw [hkappadef]; ring
  have hEbe0 : Eb ≤ e0 := by
    refine hEbkappa.trans ?_
    rw [he0def]
    exact mul_le_mul_of_nonneg_left hErepCap hkappa
  -- (b) the bracket cap
  have hKble : 2 * (d : ℝ) * (Eb ^ 2 + 1) ≤ k0 := by
    rw [hk0def]
    have hsq : Eb ^ 2 ≤ e0 ^ 2 := pow_le_pow_left₀ hEb0 hEbe0 2
    exact mul_le_mul_of_nonneg_left (by linarith only [hsq])
      (mul_nonneg zero_le_two (Nat.cast_nonneg d))
  have hbrkCap : coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0 := by
    refine (hbrk (flushSubCentre z m n i sigma) hChinge).trans ?_
    rw [hb0def]
    have h1 : Real.sqrt (2 * (d : ℝ) * (Eb ^ 2 + 1)) * Eb ≤ Real.sqrt k0 * e0 :=
      mul_le_mul (Real.sqrt_le_sqrt hKble) hEbe0 hEb0 (Real.sqrt_nonneg _)
    have h2 : 2 * (2 * (d : ℝ) * (Eb ^ 2 + 1)) ≤ 2 * k0 := by linarith only [hKble]
    linarith only [h1, h2]
  -- (c) the energy term, with the boundary energy leg substituted
  have hEnergy0 : 0 ≤ Ch03.h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx)) :=
    h1EnergyNormOnCube_nonneg _ _ _
  have hET : coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx)) ≤
      kappa * KE * Erep *
        (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)) := by
    have hEcap : Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
        (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
        (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 ≤ kappa * Erep :=
      (herrD (flushSubCentre z m n i sigma) hChinge).trans hEbkappa
    rw [coarseGrainingEnergyTerm, constantCoeffMatrixNormHalf_scalarComparator_sqrt]
    have hstep : Real.sqrt sig *
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
          (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
          (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 *
        Ch03.h1EnergyNormOnCube (originCube d n)
          (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
          (H1Function.untranslate (flushSubCentre z m n i sigma)
            (u.restrict (isOpen_translateSet_openCubeSet
              (flushSubCentre z m n i sigma) n) hsubx)) ≤
        Real.sqrt sig * (kappa * Erep) *
          (KE * (Real.sqrt sig * P2 * X + Real.sqrt sig * P2 * S +
            Sm3 * Real.sqrt sig⁻¹ * Q3s * Gs + Sm2 * Real.sqrt sig * Q3s * Hs +
            Sm2 * Real.sqrt sig * Hn)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hEcap (Real.sqrt_nonneg _)) hEn
        hEnergy0 ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hkappa hErep0)
    refine hstep.trans (le_of_eq ?_)
    have h1 : Real.sqrt sig * Real.sqrt sig = sig := Real.mul_self_sqrt hsig.le
    have h2 : Real.sqrt sig * Real.sqrt sig⁻¹ = 1 := sqrt_mul_sqrt_inv hsig
    calc Real.sqrt sig * (kappa * Erep) *
          (KE * (Real.sqrt sig * P2 * X + Real.sqrt sig * P2 * S +
            Sm3 * Real.sqrt sig⁻¹ * Q3s * Gs + Sm2 * Real.sqrt sig * Q3s * Hs +
            Sm2 * Real.sqrt sig * Hn))
        = kappa * KE * Erep *
            ((Real.sqrt sig * Real.sqrt sig) * (P2 * X) +
              (Real.sqrt sig * Real.sqrt sig) * (P2 * S) +
              (Real.sqrt sig * Real.sqrt sig⁻¹) * (Sm3 * (Q3s * Gs)) +
              (Real.sqrt sig * Real.sqrt sig) * (Sm2 * (Q3s * Hs)) +
              (Real.sqrt sig * Real.sqrt sig) * (Sm2 * Hn)) := by ring
      _ = kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) +
            1 * (Sm3 * (Q3s * Gs)) + sig * (Sm2 * (Q3s * Hs)) + sig * (Sm2 * Hn)) := by
          rw [h1, h2]
      _ = kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)) := by ring
  -- (d) the forcing leg, through the one-hop window move
  have hGbes : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + flushSubCentre z m n i sigma)) ≤
      besovGagliardoConstant d * Q3sn * Ychild := by
    have h := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
      (originCube d n) hs hs1 hgL2child hgWchild
    rwa [cubeBesovScaleWeight_neg_originCube (d := d) n s] at h
  have hGbes0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d n) s (fun y => -g (y + flushSubCentre z m n i sigma)) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild)
  have hYchild3 : Ychild ≤ flushWindowConst d * Gs := by
    rw [hYchilddef, hGsdef]
    exact normalizedGagliardoESeminormOn_flushSubCube_toReal_le hnm2 hz i hsigma g hgWW3
  have hFT : coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + flushSubCentre z m n i sigma)) ≤
      b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)) := by
    rw [coarseGrainingForceTerm]
    refine mul_le_mul hbrkCap ?_ hGbes0 hb0
    refine hGbes.trans ?_
    exact mul_le_mul_of_nonneg_left hYchild3
      (mul_nonneg (besovGagliardoConstant_nonneg d) hQ3sn0)
  -- (e) the frame division
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + flushSubCentre z m n i sigma))
    with hFTdef
  have hW1 : cubeBesovScaleWeight (1 : ℝ) (originCube d n) =
      Real.rpow (3 : ℝ) (-(n : ℝ)) := by
    have h := cubeBesovScaleWeight_neg_originCube (d := d) n (-1)
    rw [neg_neg] at h
    rw [h]
    congr 1
    ring
  rw [hW1] at hxf
  have hxfr : sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs) ≤
      cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild := hxf
  have hfac0 : (0 : ℝ) ≤ sig⁻¹ * R3n := mul_nonneg hsiginv0 hR3n0
  have hsinv : sig⁻¹ * sig = 1 := inv_mul_cancel₀ hsig.ne'
  have hid : sig⁻¹ * R3n * (sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs)) = Lhs := by
    have h2 : Real.rpow (3 : ℝ) (-(n : ℝ)) * R3n = 1 := rpow_three_neg_mul_self n
    calc sig⁻¹ * R3n * (sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs))
        = (sig⁻¹ * sig) * ((Real.rpow (3 : ℝ) (-(n : ℝ)) * R3n) * Lhs) := by ring
      _ = 1 * (1 * Lhs) := by rw [hsinv, h2]
      _ = Lhs := by ring
  have hstep : Lhs ≤ (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hxfr hfac0
  -- (f) the monotone replacement of the three legs
  have hccorr0 : (0 : ℝ) ≤ interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn :=
    mul_nonneg (mul_nonneg (interiorCorrectionConst_pos d).le
      (Real.rpow_nonneg hs.le _)) hQ3sn0
  have hleg1 : 216 * (s⁻¹) ^ (4 : ℕ) * ET ≤
      216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) :=
    mul_le_mul_of_nonneg_left hET
      (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr hs.le) 4))
  have hleg2 : 1944 * (s⁻¹) ^ (6 : ℕ) * FT ≤
      1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))) :=
    mul_le_mul_of_nonneg_left hFT
      (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr hs.le) 6))
  have hleg3 : interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (flushWindowConst d * Gs) :=
    mul_le_mul_of_nonneg_left hYchild3 hccorr0
  have hmono := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hleg1 hleg2) hcg) hleg3
  clear_value Lhs X Gs Hs Hn Ychild ET FT Erep Eb sig P2 Q3s Q3sn Q1s R3n S4 S7 S6
    Sm3 Sm2 A3 A2 A1 cg b0 k0 e0 kappa
  -- (g) the regrouping
  have hS4eq : (s⁻¹) ^ (4 : ℕ) = S4 := by
    rw [hS4def, inv_pow_eq_rpow_neg hs 4]
    congr 1
  have hS6eq : (s⁻¹) ^ (6 : ℕ) = S6 := by
    rw [hS6def, inv_pow_eq_rpow_neg hs 6]
    congr 1
  have hS4Sm3 : S4 * Sm3 = S7 := by
    rw [hS4def, hSm3def, hS7def]
    exact rpow_s_four_mul_three hs
  have hS4Sm2 : S4 * Sm2 = S6 := by
    rw [hS4def, hSm2def, hS6def]
    exact rpow_neg_four_mul_neg_two hs
  have hS6le : S6 ≤ S7 := by
    rw [hS6def, hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  have hQScle : Real.rpow s (-(1 / 2 : ℝ)) ≤ S7 := by
    rw [hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  have hRP2 : R3n * P2 ≤ 1 := by
    rw [hR3ndef, hP2def]
    exact rpow_three_frame_l2_le_one n
  have hRQ3s : R3n * Q3s ≤ 9 * Q1s := by
    rw [hR3ndef, hQ3sdef, hQ1sdef]
    exact rpow_three_frame_force_le n hs1
  have hRQ3sn : R3n * Q3sn = Q1s := by
    rw [hR3ndef, hQ3sndef, hQ1sdef]
    exact rpow_three_mul_eq_one_add s n
  have hT1 : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        (CE * (1 / 2) * A1) * (S6 * R3n * Hn) + A1 * (S4 * Erep * S) := by
    have hsplit : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
          (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) =
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * X)))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * S)))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) *
            (Erep * ((sig⁻¹ * sig) * (Sm2 * ((R3n * Q3s) * Hs))))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * (Sm2 * (R3n * Hn))))) := by
      rw [hA1def]; ring
    rw [hsplit, hsinv]
    have hsinv4 : (0 : ℝ) ≤ (s⁻¹) ^ (4 : ℕ) := pow_nonneg (inv_nonneg.mpr hs.le) 4
    have hi : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X)))) ≤
        A1 * (S4 * Erep * X) := by
      have h1 : (R3n * P2) * X ≤ X := by
        have h := mul_le_mul_of_nonneg_right hRP2 hX0
        linarith only [h]
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * X))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * X)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
        _ = A1 * (S4 * Erep * X) := by rw [hS4eq]; ring
    have hii : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S)))) ≤
        A1 * (S4 * Erep * S) := by
      have h1 : (R3n * P2) * S ≤ S := by
        have h := mul_le_mul_of_nonneg_right hRP2 hS0
        linarith only [h]
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * S))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * S)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
        _ = A1 * (S4 * Erep * S) := by rw [hS4eq]; ring
    have hiii : A1 * ((s⁻¹) ^ (4 : ℕ) *
        (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) ≤
        (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
      have h2 : (R3n * Q3s) * (Sm3 * Gs) ≤ (9 * Q1s) * (Sm3 * Gs) :=
        mul_le_mul_of_nonneg_right hRQ3s (mul_nonneg hSm30 hGs0)
      have h2nn : (0 : ℝ) ≤ sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)) :=
        mul_nonneg hsiginv0 (mul_nonneg (mul_nonneg hR3n0 hQ3s0)
          (mul_nonneg hSm30 hGs0))
      have hinner : Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))) ≤
          (CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))) :=
        mul_le_mul hErepCap (mul_le_mul_of_nonneg_left h2 hsiginv0) h2nn
          (le_trans hErep0 hErepCap)
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)))))
          ≤ A1 * ((s⁻¹) ^ (4 : ℕ) *
              ((CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
        _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm3) * sig⁻¹ * Q1s * Gs) := by
            ring
        _ = (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
            rw [hS4eq, hS4Sm3]
    have hiv : A1 * ((s⁻¹) ^ (4 : ℕ) *
        (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs))))) ≤
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by
      have h2 : Sm2 * ((R3n * Q3s) * Hs) ≤ Sm2 * ((9 * Q1s) * Hs) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRQ3s hHs0) hSm20
      have h2nn : (0 : ℝ) ≤ Sm2 * ((R3n * Q3s) * Hs) :=
        mul_nonneg hSm20 (mul_nonneg (mul_nonneg hR3n0 hQ3s0) hHs0)
      have hinner : Erep * (Sm2 * ((R3n * Q3s) * Hs)) ≤
          (CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)) :=
        mul_le_mul hErepCap h2 h2nn (le_trans hErep0 hErepCap)
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs)))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (Sm2 * ((R3n * Q3s) * Hs)))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * ((CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
        _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm2) * Q1s * Hs) := by ring
        _ = (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by rw [hS4eq, hS4Sm2]
    have hv : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * (R3n * Hn))))) ≤
        (CE * (1 / 2) * A1) * (S6 * R3n * Hn) := by
      have h2nn : (0 : ℝ) ≤ Sm2 * (R3n * Hn) :=
        mul_nonneg hSm20 (mul_nonneg hR3n0 hHn0)
      have hinner : Erep * (Sm2 * (R3n * Hn)) ≤
          (CE * (1 / 2)) * (Sm2 * (R3n * Hn)) :=
        mul_le_mul_of_nonneg_right hErepCap h2nn
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * (R3n * Hn)))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (Sm2 * (R3n * Hn)))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * ((CE * (1 / 2)) * (Sm2 * (R3n * Hn)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
        _ = (CE * (1 / 2) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm2) * R3n * Hn) := by ring
        _ = (CE * (1 / 2) * A1) * (S6 * R3n * Hn) := by rw [hS4eq, hS4Sm2]
    linarith only [hi, hii, hiii, hiv, hv]
  have hT2 : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) ≤
      A2 * (S7 * sig⁻¹ * Q1s * Gs) := by
    have hrw : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) =
        A2 * ((s⁻¹) ^ (6 : ℕ) * (sig⁻¹ * ((R3n * Q3sn) * Gs))) := by
      rw [hA2def]; ring
    rw [hrw, hRQ3sn, hS6eq]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Gs) :=
      mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hGs0)
    calc A2 * (S6 * (sig⁻¹ * (Q1s * Gs)))
        ≤ A2 * (S7 * (sig⁻¹ * (Q1s * Gs))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS6le hnn) hA2
      _ = A2 * (S7 * sig⁻¹ * Q1s * Gs) := by ring
  have hT3 : (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
        Q3sn * (flushWindowConst d * Gs)) ≤ A3 * (S7 * sig⁻¹ * Q1s * Gs) := by
    have hrw : (sig⁻¹ * R3n) * (interiorCorrectionConst d *
          Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * (flushWindowConst d * Gs)) =
        A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * ((R3n * Q3sn) * Gs))) := by
      rw [hA3def]; ring
    rw [hrw, hRQ3sn]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Gs) :=
      mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hGs0)
    calc A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * (Q1s * Gs)))
        ≤ A3 * (S7 * (sig⁻¹ * (Q1s * Gs))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQScle hnn) hA3
      _ = A3 * (S7 * sig⁻¹ * Q1s * Gs) := by ring
  -- (h) the conclusion
  have hXterm : (0 : ℝ) ≤ S4 * Erep * X := mul_nonneg (mul_nonneg hS40 hErep0) hX0
  have hSterm : (0 : ℝ) ≤ S4 * Erep * S := mul_nonneg (mul_nonneg hS40 hErep0) hS0
  have hGterm : (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs :=
    mul_nonneg (mul_nonneg (mul_nonneg hS70 hsiginv0) hQ1s0) hGs0
  have hHsterm : (0 : ℝ) ≤ S6 * Q1s * Hs :=
    mul_nonneg (mul_nonneg hS60 hQ1s0) hHs0
  have hHnterm : (0 : ℝ) ≤ S6 * R3n * Hn :=
    mul_nonneg (mul_nonneg hS60 hR3n0) hHn0
  refine hstep.trans (le_trans (mul_le_mul_of_nonneg_left hmono hfac0) ?_)
  have hdistrib : (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
            (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
              Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) +
          1944 * (s⁻¹) ^ (6 : ℕ) *
            (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (flushWindowConst d * Gs)) =
      (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
          (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) +
        (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) +
        (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
          Q3sn * (flushWindowConst d * Gs)) := by ring
  rw [hdistrib]
  have habs : A1 * (S4 * Erep * X) +
        (9 * (CE * (1 / 2)) * A1 + A2 + A3) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        (CE * (1 / 2) * A1) * (S6 * R3n * Hn) + A1 * (S4 * Erep * S) ≤
      (A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1) *
        (S4 * Erep * X + S7 * sig⁻¹ * Q1s * Gs + S6 * Q1s * Hs + S6 * R3n * Hn +
          S4 * Erep * S) :=
    five_leg_bound le_rfl (by linarith only [hCE2, hCE3, hA2, hA3])
      (by linarith only [hA1, hCE3]) (by linarith only [hA1, hCE3, hA2, hA3])
      (by linarith only [hA1, hCE2, hA2, hA3])
      (by linarith only [hCE2, hCE3, hA2, hA3]) hXterm hGterm hHsterm hHnterm hSterm
  linarith only [hT1, hT2, hT3, habs]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
