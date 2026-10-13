/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueEnergyLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryEnergyRebaseWindow

/-!
# ResidueEnergyLegWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The boundary lane's energy leg at the anchor's own WINDOW, gate-free.**

`ResidueEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs_atHinges`
with its child-cube left-hand side — and the inclusion binder `x + □_n ⊆ □_m`
that side requires — replaced by the Step-7 window scalar `√(ν
⨍_{(x+□_n)∩□_m}|∇u|²)`.  Every constant, index and right-hand-side leg is the
parent's. -/
theorem ae_windowEnergy_boundary_le_anchorLegs_atHinges (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          x ∈ openCubeSet (originCube d m) →
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
              openCubeSet (originCube d (n + 2)) ⊆
            (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) →
          (translateSet (wellPlacedCentre x m (n + 2) - z)
              (cubeSet (originCube d (n + 2))) ⊆
            cubeSet (originCube d (n + 3))) →
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
                |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                    openCubeSet (originCube d (n + 2)))
                    (fun y => u.toFun y - hdat.toFun y)| ≤ S →
                  Real.sqrt (M.nu *
                      normalizedSetAverage (truncatedWindow x m n)
                        (fun y => vecNormSq (u.grad y))) ≤
                    K * (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                            Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
                            (eLpNorm (fun y => u.toFun y -
                                volumeAverage ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) u.toFun) 2
                              (Support.normalizedVolumeMeasureOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))))).toReal +
                          Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * S +
                          Real.rpow s (-(3 : ℝ)) *
                              Real.sqrt (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) *
                              Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s g).toReal +
                          Real.rpow s (-(2 : ℝ)) *
                              Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s hdat.grad).toReal +
                          Real.rpow s (-(2 : ℝ)) *
                              Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal) := by
  classical
  obtain ⟨CB1, CB2, hCB1, hCB2, hB2⟩ :=
    exists_boundaryWindowEnergy_rebased_window_le_dirichletDatumRHS d
  obtain ⟨CG1, CG2, hCG1, hCG2, hGA⟩ :=
    exists_cubeLpNorm_datumDifference_le_dirichletEnergyRHS d
  obtain ⟨CP, KP, hCP, hKP, hpref⟩ := ae_coveringCubePrefactor_le_gapThree d
  obtain ⟨CR, KR, hCR, hKR, hratio⟩ := ae_coveringCubeRatioCap_le_gapThree d
  obtain ⟨Pcap, hPcapdef, hPcap0⟩ :
      ∃ t : ℝ, t = (6 * max 1 CB1) ^ (14 : ℕ) * 64 * (KP * KP) ^ (6 : ℕ) ∧ 0 ≤ t :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨alpha, halphadef, halpha0⟩ :
      ∃ t : ℝ, t = Real.sqrt (2 * (3 : ℝ) ^ d * (Pcap * KP)) ∧ 0 ≤ t :=
    ⟨_, rfl, Real.sqrt_nonneg _⟩
  obtain ⟨beta, hbetadef, hbeta0⟩ :
      ∃ t : ℝ, t = Real.sqrt (2 * (3 : ℝ) ^ d * (18 : ℝ) ^ d) ∧ 0 ≤ t :=
    ⟨_, rfl, Real.sqrt_nonneg _⟩
  obtain ⟨sK, hsKdef, hsK0⟩ : ∃ t : ℝ, t = Real.sqrt KR ∧ 0 ≤ t :=
    ⟨_, rfl, Real.sqrt_nonneg _⟩
  have hCbg0 : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
  have hCgw0 : (0 : ℝ) ≤ gagliardoWindowConst d := (gagliardoWindowConst_pos d).le
  have hgP0 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have h3d0 : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hnegC0 : (0 : ℝ) ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hn1 : (0 : ℝ) ≤ alpha * (3 : ℝ) ^ d := mul_nonneg halpha0 h3d0
  have hn3 : (0 : ℝ) ≤ alpha * CG1 * CG2 * KR * besovGagliardoConstant d *
      gagliardoWindowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha0 hCG1.le)
      hCG2.le) hKR.le) hCbg0) hCgw0
  have hn4 : (0 : ℝ) ≤ alpha * CG1 * KR * besovGagliardoConstant d *
      gagliardoWindowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha0 hCG1.le) hKR.le) hCbg0) hCgw0
  have hn5 : (0 : ℝ) ≤ beta * CB2 * sK * besovGagliardoConstant d *
      gagliardoWindowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbeta0 hCB2.le) hsK0) hCbg0) hCgw0
  have hn6 : (0 : ℝ) ≤ alpha * unitMeanZeroPoincareConst d * (d : ℝ) * (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg halpha0 hgP0) (Nat.cast_nonneg d)) h3d0
  have hn7 : (0 : ℝ) ≤ alpha * CG1 * CG2 * KR * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha0 hCG1.le)
      hCG2.le) hKR.le) hsd0) h3d0
  have hn8 : (0 : ℝ) ≤ Real.sqrt (3 / 2 : ℝ) * alpha * CG1 * Real.sqrt (d : ℝ) *
      (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hnegC0 halpha0) hCG1.le) hsd0) h3d0
  have hn9 : (0 : ℝ) ≤ beta * CB2 * sK * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbeta0 hCB2.le) hsK0) hsd0) h3d0
  refine ⟨max CP CR,
    alpha * (3 : ℝ) ^ d + alpha +
      (8 * alpha * CG1 * CG2 * KR * besovGagliardoConstant d * gagliardoWindowConst d +
        8 * alpha * CG1 * KR * besovGagliardoConstant d * gagliardoWindowConst d +
        3 * beta * CB2 * sK * besovGagliardoConstant d * gagliardoWindowConst d) +
      (4 * alpha * CG1 * CG2 * KR * besovGagliardoConstant d * gagliardoWindowConst d +
        2 * beta * CB2 * sK * besovGagliardoConstant d * gagliardoWindowConst d) +
      (alpha * unitMeanZeroPoincareConst d * (d : ℝ) * (3 : ℝ) ^ d +
        4 * alpha * CG1 * CG2 * KR * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d +
        Real.sqrt (3 / 2 : ℝ) * alpha * CG1 * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d +
        2 * beta * CB2 * sK * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d) + 1,
    lt_of_lt_of_le hCP (le_max_left _ _),
    by linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9], ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hcov hP
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hregimeP : M.gamma ≤ CP⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCP (le_max_left CP CR)
    rw [one_div, one_div] at h1
    exact h1
  have hregimeR : M.gamma ≤ CR⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCR (le_max_right CP CR)
    rw [one_div, one_div] at h1
    exact h1
  filter_upwards [hpref M s hsrange hregimeP hsmall hs L m n hmL hnm z,
    hratio M s hsrange hregimeR hsmall hs L m n hmL hnm z (s / 2)
      (by linarith only [hs]) (by linarith only [hs1])
      (offGridStabilityConst_pinHalf_le hs hs1),
    hratio M s hsrange hregimeR hsmall hs L m n hmL hnm z (s / 4)
      (by linarith only [hs]) (by linarith only [hs1])
      (offGridStabilityConst_pinQuarter_le hs hs1)] with omega hpre hr2 hr4
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean
  obtain ⟨hprefcap, hlamScap⟩ := hpre hmem x hP CB1 hCB1
  obtain ⟨hLam2, -⟩ := hr2 hmem x hP
  obtain ⟨-, hlam4⟩ := hr4 hmem x hP
  rw [← hPcapdef] at hprefcap
  -- the anchor's data on the two windows and on the covering cube
  have hhL2m : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) hdat.grad_memVectorL2
  have huL2m : MemLp u.toFun 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) u.memL2
  have hW3top := volume_anchorWindow_ne_top (n + 3) m z
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
    intro hzero
    have hle := measure_mono (μ := (volume : Measure (Vec d))) hcov
    rw [hzero] at hle
    exact volume_image_add_openCubeSet_ne_zero (wellPlacedCentre x m (n + 2))
      (originCube d (n + 2)) (le_antisymm hle zero_le)
  have := isProbabilityMeasure_normalizedVolumeMeasureOn hW30 hW3top
  have huL2W : MemLp u.toFun 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 huL2m
  have hhL2W : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhL2m
  have hgWW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hhWW : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhW
  have hXfin : eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ :=
    (huL2W.sub (memLp_const _)).eLpNorm_ne_top
  have hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ := hhL2W.eLpNorm_ne_top
  have hgL2cov := memLp_two_coveringCube_of_clause_iv (x := x) hnm2 hgL2
  have hgWcov := memLp_two_gagliardo_coveringCube_of_clause_iv (x := x) (s := s) hnm2 hgW
  have hhL2cov := memLp_two_coveringCube_of_clause_iv (x := x) hnm2 hhL2m
  have hhWcov := memLp_two_gagliardo_coveringCube_of_clause_iv (x := x) (s := s) hnm2 hhW
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_neg_of_clause_iv hnm2 hs hs1 le_rfl hgL2 hgW
  have hgreg2 : ForceBesovRegularity (originCube d (n + 2)) (s / 2)
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_neg_of_clause_iv hnm2 hs hs1
      (by linarith only [hs]) hgL2 hgW
  have hhreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_datumGrad_of_clause_iv hnm2 hs hs1 le_rfl hhL2m hhW
  have hhreg2 : ForceBesovRegularity (originCube d (n + 2)) (s / 2)
      (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_datumGrad_of_clause_iv hnm2 hs hs1
      (by linarith only [hs]) hhL2m hhW
  have hsubc : translateSet (wellPlacedCentre x m (n + 2))
      (openCubeSet (originCube d (n + 2))) ⊆ openCubeSet (originCube d m) :=
    translateSet_wellPlacedCentre_subset x hnm2
  -- the boundary Caccioppoli at `(1/2, s/3)` and the pin `r = s/2`
  obtain ⟨v, hvval, hvgrad, hB2disp⟩ :=
    hB2 M L omega m n x z (1 / 2) (s / 3) (s / 2) u hdat g hx hnm2 hsol
      (by norm_num) (by norm_num) (by linarith only [hs]) (by linarith only [hs1])
      (by linarith only [hs1]) (by linarith only [hs]) (by linarith only [hs1])
      hgreg2 hhreg2
  have hbg : dirichletBoundaryGradientField v =
      fun y => hdat.grad (y + wellPlacedCentre x m (n + 2)) := by
    funext y
    rw [dirichletBoundaryGradientField, hvgrad y]
  have hbgreg2 : ForceBesovRegularity (originCube d (n + 2)) (s / 2)
      (dirichletBoundaryGradientField v) := by rw [hbg]; exact hhreg2
  -- the square root of the display
  have hDirB0 : (0 : ℝ) ≤ dirichletEnergyWithRHSRHS CB2 (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) (s / 2)
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) v :=
    dirichletEnergyWithRHSRHS_nonneg v hCB2.le (by linarith only [hs]) hgreg2 hbgreg2
  have hP0 : (0 : ℝ) ≤ caccioppoliWithRHSPrefactor CB1 (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (1 / 2) (s / 3) :=
    caccioppoliWithRHSPrefactor_nonneg hCB1.le (by norm_num) (by linarith only [hs])
      (by linarith only [hs1])
  have hLam0 : (0 : ℝ) ≤ Ch02.lambdaS (originCube d (n + 2)) (s / 3)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) :=
    Ch02.lambdaSq_nonneg (originCube d (n + 2)) _ (by linarith only [hs]) (by norm_num)
  have hsqrt := sqrt_le_of_boundaryCaccioppoliDisplay h3d0 hP0 hLam0
    (show (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) from
      Real.rpow_nonneg (by norm_num) _)
    (normalizedL2SqOnSet_nonneg _ _
      (isOpen_openCubeSet (originCube d (n + 2))).measurableSet)
    (by positivity : (0 : ℝ) ≤ (18 : ℝ) ^ d) hDirB0 hB2disp
  have hT2sqrt : Real.sqrt (Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ))) =
      Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) := by
    rw [show (-2 : ℝ) * (((n + 2 : ℤ)) : ℝ) = 2 * (-(((n + 2 : ℤ)) : ℝ)) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  rw [hT2sqrt, ← hbetadef] at hsqrt
  -- the datum pricing, and the parent-`L²` pricing scaled by the frame factor
  have hGA1 := hGA (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) s
    (fun y => -g (y + wellPlacedCentre x m (n + 2))) v hs hs1 hgreg2 hbgreg2
  have hB4 := rpow_three_neg_mul_sqrt_coveringDifference_le_atWindow (x := x) (z := z)
    (S := S) hnm2 hcov u hdat v
    (H1Function.untranslate (wellPlacedCentre x m (n + 2))
      (u.restrict
        (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + 2)) (n + 2)) hsubc))
    (fun _ => rfl) hvval hXfin hHfin hmean hGA1
  -- the energy legs, at the two Dirichlet-energy constants
  have hDirBle := dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow
    (c := wellPlacedCentre x m (n + 2)) (C₂ := CB2) (K := KR)
    (sigma := (Annealed.sigmaBar M (n + 3) : ℝ)) rfl hcov hs hs1 hCB2.le hsig
    hKR.le hdat v hvgrad hlam4 hLam2 hgreg hhreg hgL2cov hgWcov hgWW hhL2cov hhWcov
    hhWW hhL2W
  have hDirGle := dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow
    (c := wellPlacedCentre x m (n + 2)) (C₂ := CG2) (K := KR)
    (sigma := (Annealed.sigmaBar M (n + 3) : ℝ)) rfl hcov hs hs1 hCG2.le hsig
    hKR.le hdat v hvgrad hlam4 hLam2 hgreg hhreg hgL2cov hgWcov hgWW hhL2cov hhWcov
    hhWW hhL2W
  rw [← hsKdef] at hDirBle hDirGle
  -- the coarse caps of the prefactor and of the datum pricing's two factors
  have hA : Real.sqrt (2 * (3 : ℝ) ^ d *
      (caccioppoliWithRHSPrefactor CB1 (originCube d (n + 2))
          (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
          (1 / 2) (s / 3) *
        Ch02.lambdaS (originCube d (n + 2)) (s / 3)
          (parentRebasedFamily M L (n + 3)
            (wellPlacedCentre x m (n + 2)) z omega))) ≤
      alpha * Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) := by
    have hprod := mul_le_mul hprefcap hlamScap hLam0 hPcap0
    have hmul : 2 * (3 : ℝ) ^ d *
        (caccioppoliWithRHSPrefactor CB1 (originCube d (n + 2))
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
            (1 / 2) (s / 3) *
          Ch02.lambdaS (originCube d (n + 2)) (s / 3)
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)) ≤
        (2 * (3 : ℝ) ^ d * (Pcap * KP)) * (Annealed.sigmaBar M (n + 3) : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hprod
        (by positivity : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ d)
      calc 2 * (3 : ℝ) ^ d * _ ≤ 2 * (3 : ℝ) ^ d * (Pcap * (KP * _)) := h1
        _ = (2 * (3 : ℝ) ^ d * (Pcap * KP)) * (Annealed.sigmaBar M (n + 3) : ℝ) := by
            ring
    rw [halphadef, ← Real.sqrt_mul
      (mul_nonneg (by positivity) (mul_nonneg hPcap0 hKP.le))]
    exact Real.sqrt_le_sqrt hmul
  have hlow : poincareLowerEllipticityFactor (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (s / 4) (Ch02.MultiscaleExponent.finite 2) ≤
      sK * Real.sqrt (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) := by
    rw [poincareLowerEllipticityFactor, hsKdef]
    exact rpow_neg_half_le_of_lower_cap
      (Ch02.lambdaSq_nonneg (originCube d (n + 2)) _ (by linarith only [hs])
        (by norm_num)) hsig hKR.le hlam4
  have hlamInv : Real.rpow (Ch02.lambdaSq (originCube d (n + 2)) (s / 4)
      (Ch02.MultiscaleExponent.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega))
      (-1 : ℝ) ≤ KR * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ :=
    rpow_neg_one_lambdaSq_le_of_lower_cap
      (Ch02.lambdaSq_finite_pos (originCube d (n + 2)) _ (by linarith only [hs])
        (by norm_num)) hsig hlam4
  have hBg : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2))
      (s / 2) (fun y => -g (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s g).toReal) :=
    (scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le
      (originCube d (n + 2)) _ (by linarith only [hs]) hgreg).trans
      (besovVectorSeminormTwo_coveringCube_atWindow hcov hs hs1
        hgL2cov hgWcov hgWW)
  have hgradcube : MemVectorL2 (cubeSet (originCube d (n + 2)))
      (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) :=
    memVectorL2_cubeSet_of_openCubeSet
      (H1Function.untranslate (wellPlacedCentre x m (n + 2))
        (hdat.restrict
          (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + 2)) (n + 2))
          hsubc)).grad_memVectorL2
  have hHn : normalizedEuclideanL2 (originCube d (n + 2))
      (dirichletBoundaryGradientField v) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm hdat.grad 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
    rw [hbg]
    exact normalizedEuclideanL2_datumGrad_coveringCube_atWindow hcov hhL2W hgradcube
  have hnegf : negativeToL2Factor s ≤
      Real.sqrt (3 / 2 : ℝ) * Real.rpow s (-(2 : ℝ)) :=
    (negativeToL2Factor_le_rpow_neg_half hs hs1).trans
      (mul_le_mul_of_nonneg_left (rpow_neg_half_le_neg_two hs hs1) hnegC0)
  -- the composed real bound, then the arithmetic
  have hmain := hsqrt.trans (add_le_add (mul_le_mul hA hB4
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
    (mul_nonneg halpha0 (Real.sqrt_nonneg _))) le_rfl)
  refine five_leg_bound (boundary_energy_arith halpha0 hbeta0 (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hsK0 hKR.le hCG1.le hCB2.le hgP0 (Nat.cast_nonneg d) h3d0
    hsd0 hCbg0 hCgw0 (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg hs.le _) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (Real.rpow_nonneg (by linarith only [hs]) _)
    (Real.rpow_nonneg (by linarith only [hs]) _)
    (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      hgreg2)
    (normalizedEuclideanL2_nonneg _ _)
    (dirichletEnergyWithRHSRHS_nonneg v hCG2.le (by linarith only [hs]) hgreg2 hbgreg2)
    hsig (sqrt_mul_sqrt_inv hsig) (sqrt_mul_inv_eq_sqrt_inv hsig)
    (by rw [hsKdef]; exact Real.mul_self_sqrt hKR.le)
    (pin_force_sq hs) (pin_gradh_prod hs) (pin_force_cube hs)
    (pin_force_half_le hs hs1) (pin_gradh_half_le hs hs1) (one_le_rpow_neg_two hs hs1)
    hlow hlamInv hBg hHn hnegf hnegC0 hDirGle hDirBle hmain) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (by norm_num) _)) (le_trans (abs_nonneg _) hmean)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.sqrt_nonneg _))
      ENNReal.toReal_nonneg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
