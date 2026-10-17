/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.HarmonicApproximation
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEntry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# EdAssemblyAnchorErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The error-weighted anchor at the one-step window choice

## The flat `∇h` leg

The general clause's flat `∇h` leg is the print's own average form,
`𝓔`-multiplied at the general clause's own flux-corrected-error slot (index
`n+3`, subtype `s/8`, sample `τ_z ω` — the first bracket's factor verbatim):

```text
   ofReal( C s^{-6} · 𝓔_{n+3}(τ_z ω) · 3^n · ‖(∇h)_{(z+□_{n+2})∩□_m}‖ ) .
```

Read at the excess-decay lane's window choice (anchor index `n-2`) this is `C
s^{-6} · 𝓔_{n-2+3} · 3^{n-2} · ‖(∇h)_{(z+□_{n-2+2})∩□_m}‖`, which is exactly
what `edLeg_four_le_errorWeighted` consumes — at the anchor's own subterms, no
repackaging.

## The discard that is NOT taken

The print's own step replaces `𝓔 1_𝒢` by `C(d) ε`.  That is the single monotone
move that loses the `𝓔` factor, and it is declined throughout this provider
chain: `𝓔` is only ever bounded downstream (`𝓔 ≤ ε_j`), never inverted.

## What the expansion costs, and what it saves

That leg is a bare `ofReal`, with no `ℝ≥0∞` carrier of its own.  So
the shell atoms change shape — `ofReal c₁ * (X + ofReal b) + ofReal c₂ * Y +
ofReal c₃ * Z + ofReal c₄` instead of the four-carrier form — and
the finiteness slot needs three finite carriers instead of four: the `∇h` `L²`
`MemLp` obligation of the unweighted anchor is gone, because a real number's
`ofReal` is finite outright.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the anchor);
  `l.excess.decay.good.scales`, and its proof's window-choice and
  harmonic-approximation steps; the `𝓔`-multiplied slot and the declined
  discard.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. The shell atoms -/

/-- **The `B.toReal` expansion of the general clause's display.**

Unconditional — `.toReal` is multiplicative and subadditive outright, so a `⊤`
carrier only collapses the left-hand side to `0`. -/
theorem toReal_ofReal_mul_bracket_add_two_add_flat_le {c₁ b c₂ c₃ c₄ : ℝ}
    (X Y Z : ℝ≥0∞) (hc₁ : 0 ≤ c₁) (hb : 0 ≤ b) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hc₄ : 0 ≤ c₄) :
    (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄).toReal ≤
      c₁ * (X.toReal + b) + c₂ * Y.toReal + c₃ * Z.toReal + c₄ := by
  have hbracket : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b)).toReal ≤
      c₁ * (X.toReal + b) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁]
    refine mul_le_mul_of_nonneg_left ?_ hc₁
    refine le_trans ENNReal.toReal_add_le (le_of_eq ?_)
    rw [ENNReal.toReal_ofReal hb]
  have hY : (ENNReal.ofReal c₂ * Y).toReal = c₂ * Y.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂]
  have hZ : (ENNReal.ofReal c₃ * Z).toReal = c₃ * Z.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₃]
  have hW : (ENNReal.ofReal c₄).toReal = c₄ := ENNReal.toReal_ofReal hc₄
  have hstep1 : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄).toReal ≤
      (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z).toReal + (ENNReal.ofReal c₄).toReal :=
    ENNReal.toReal_add_le
  have hstep2 : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
        ENNReal.ofReal c₃ * Z).toReal ≤
      (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y).toReal +
        (ENNReal.ofReal c₃ * Z).toReal :=
    ENNReal.toReal_add_le
  have hstep3 : (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y).toReal ≤
      (ENNReal.ofReal c₁ * (X + ENNReal.ofReal b)).toReal + (ENNReal.ofReal c₂ * Y).toReal :=
    ENNReal.toReal_add_le
  linarith only [hstep1, hstep2, hstep3, hbracket, hY, hZ, hW]

/-- The `hB` slot of the one-step consumers, at this shell.  There is no `∇h`
`L²` carrier: the flat `∇h` leg is a bare `ofReal`, finite outright. -/
theorem ofReal_mul_bracket_add_two_add_flat_ne_top {c₁ b c₂ c₃ c₄ : ℝ} {X Y Z : ℝ≥0∞}
    (hX : X ≠ ⊤) (hY : Y ≠ ⊤) (hZ : Z ≠ ⊤) :
    ENNReal.ofReal c₁ * (X + ENNReal.ofReal b) + ENNReal.ofReal c₂ * Y +
      ENNReal.ofReal c₃ * Z + ENNReal.ofReal c₄ ≠ ⊤ := by
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ⟩, ENNReal.ofReal_ne_top⟩
  exact ENNReal.add_ne_top.mpr ⟨hX, ENNReal.ofReal_ne_top⟩

/-! ## 2. The anchor at the one-step window choice -/

/-- **The harmonic-approximation anchor, applied at the one-step window
choice.**

The harmonic-approximation anchor bound re-run at the error-weighted
statement.  For a.e.  `ω`, every Dirichlet datum on `□_m` and every harmonic
replacement on the moved cube `y + □_{n-2}`, the general clause is available as
a finite bound `B` on the (unchanged) gated indicator, together with the
expansion of `B.toReal` into the four printed legs — the fourth of which is the
`𝓔`-multiplied flat `∇h` average, at the anchor's own subterms.  The
`𝓔 1_𝒢 ≤ C` discard is declined. -/
theorem exists_oneStepAnchorBound_errorWeighted (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n - 2 + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ truncatedWindow z m (n - 3) →
            z ∈ openCubeSet (originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u hdat g →
                MemLp g 2
                    (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                ∀ (v : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                        openCubeSet (originCube d (n - 2))))
                  (w : H10Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                        openCubeSet (originCube d (n - 2)))),
                  IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                    openCubeSet (originCube d (n - 2))) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
                    Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (cgEllipLowerConstant d) (n - 2 + 3) z
                          ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (normalizedVolumeMeasureOn
                              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                                openCubeSet (originCube d (n - 2)))))
                        omega ≤ B ∧
                    B.toReal ≤
                      C * Real.rpow s (-(4 : ℝ)) *
                          fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                            ⟨s / 8, by linarith only [hs]⟩
                            (Cutoff.translateCutoffSample z omega) *
                          ((MeasureTheory.eLpNorm
                              (fun y => u.toFun y -
                                HCPolySupport.volumeAverage
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n - 2 + 3))) ∩
                                    openCubeSet (originCube d m)) u.toFun) 2
                              (normalizedVolumeMeasureOn
                                (((fun y' => z + y') ''
                                    openCubeSet (originCube d (n - 2 + 3))) ∩
                                  openCubeSet (originCube d m)))).toReal +
                            Real.rpow s (-(3 / 2 : ℝ)) *
                                Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                              ‖HCPolySupport.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n - 2 + 2))) ∩
                                    openCubeSet (originCube d m)) hdat.grad‖) +
                        C * Real.rpow s (-(7 : ℝ)) *
                            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                openCubeSet (originCube d (n - 2 + 3))) ∩
                              openCubeSet (originCube d m)) s g).toReal +
                        C * Real.rpow s (-(6 : ℝ)) *
                            Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                openCubeSet (originCube d (n - 2 + 3))) ∩
                              openCubeSet (originCube d m)) s hdat.grad).toReal +
                        C * Real.rpow s (-(6 : ℝ)) *
                            fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                              ⟨s / 8, by linarith only [hs]⟩
                              (Cutoff.translateCutoffSample z omega) *
                            Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                          ‖HCPolySupport.volumeAverageVec
                              (((fun y' => z + y') ''
                                  openCubeSet (originCube d (n - 2 + 2))) ∩
                                openCubeSet (originCube d m)) hdat.grad‖ := by
  classical
  obtain ⟨C, hC, hclause⟩ :=
    Algsuperdiff.Frozen.Section4.harmonic_approximation_good_scales d
  refine ⟨C, hC, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz
  have hnm2 : n - 2 ≤ m := by omega
  have hym : wellPlacedCentre x m (n - 2) ∈ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet x hnm2
      ⟨0, zero_mem_openCubeSet_originCube d (n - 2), by simp⟩
  have hgeom : (fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n - 2 + 1))) ∩
        openCubeSet (originCube d m) := by
    have h := image_add_wellPlacedCentre_subset_windowChoice hxz hnm2
    rw [truncatedWindow] at h
    rw [show n - 2 + 1 = n - 1 by ring]
    exact h
  -- the two display windows and their volumes, at the anchor's own indices
  have hWtop := volume_anchorWindow_ne_top (n - 2 + 3) m z
  have hW20 : volume ((((fun y' => z + y') ''
      openCubeSet (originCube d (n - 2 + 2))) ∩
      openCubeSet (originCube d m))) ≠ 0 := volume_anchorWindowInner_ne_zero hgeom
  have hW30 : volume ((((fun y' => z + y') ''
      openCubeSet (originCube d (n - 2 + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
    intro hzero
    have hmono := measure_mono (μ := (volume : Measure (Vec d)))
      (anchorWindowInner_subset_anchorWindow (d := d) (n - 2) m z)
    rw [hzero, le_zero_iff] at hmono
    exact hW20 hmono
  have := isProbabilityMeasure_normalizedVolumeMeasureOn hW30 hWtop
  -- the sign data of the four printed coefficients
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (n - 2)).2.le
  filter_upwards [hclause M s hsrange hregime hfund hs L m (n - 2) hmL hnm
    (wellPlacedCentre x m (n - 2)) z hym hz hgeom] with omega hom
  intro u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  obtain ⟨hgen, -⟩ := hom u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  -- the anchor's clause (iv) and `H¹` data, read on the display window
  have hum : MemLp u.toFun 2
      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) u.memL2
  have hu3 : MemLp u.toFun 2
      (normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hum
  have hg3 : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hgh3 : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhW
  refine ⟨_, ofReal_mul_bracket_add_two_add_flat_ne_top
    (hu3.sub (memLp_const _)).eLpNorm_ne_top hg3.eLpNorm_ne_top hgh3.eLpNorm_ne_top, hgen, ?_⟩
  exact toReal_ofReal_mul_bracket_add_two_add_flat_le _ _ _
    (mul_nonneg (mul_nonneg hC.le hS4)
      (fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
    (mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hS7) hsgn) h3sn)
    (mul_nonneg (mul_nonneg hC.le hS6) h3sn)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hS6)
      (fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _)) h3n) (norm_nonneg _))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
