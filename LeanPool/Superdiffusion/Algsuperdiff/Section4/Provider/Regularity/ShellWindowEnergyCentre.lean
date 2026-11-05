/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueEnergyLegWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccBoundaryGate

/-!
# ShellWindowEnergyCentre

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two covering inclusions at the diagonal -/

/-- **The covering cube inside the `n+3` parent, half-open, off the displacement
datum.**
`BoundaryCoveringSlot.translateSet_cubeSet_coveringCube_subset_anchorParent`
with its geometry binder replaced by the only consequence its proof uses. -/
theorem translateSet_cubeSet_coveringCube_subset_anchorParent_of_sub {n m : ℤ}
    {x z : Vec d} (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hw : x - z ∈ openCubeSet (originCube d (n + 1))) :
    translateSet (wellPlacedCentre x m (n + 2) - z) (cubeSet (originCube d (n + 2))) ⊆
      cubeSet (originCube d (n + 3)) := by
  exact ExcessDecay.translateSet_cubeSet_coveringCube_subset_anchorParent_of_sub hnm hx hw

/-- **The covering inclusion at the diagonal.**  At `x = z` the displacement datum
is `0 ∈ □_{n+1}`, so the half-open containment holds for centre of `□_m`. -/
theorem translateSet_cubeSet_coveringCube_subset_anchorParent_self {n m : ℤ}
    {z : Vec d} (hnm : n + 2 ≤ m) (hz : z ∈ openCubeSet (originCube d m)) :
    translateSet (wellPlacedCentre z m (n + 2) - z) (cubeSet (originCube d (n + 2))) ⊆
      cubeSet (originCube d (n + 3)) := by
  refine translateSet_cubeSet_coveringCube_subset_anchorParent_of_sub hnm hz ?_
  rw [sub_self, mem_openCubeSet_originCube_iff]
  intro i
  have h := half_three_zpow_pos' (n + 1)
  refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> linarith only [h]

/-- **The clamped outer cube inside the anchor window, at the diagonal.**
`StepSevenCaccBoundaryGate.image_add_wellPlacedCentre_subset_truncatedWindow_succ`
at `j = n+2`, with the scale normalized. -/
theorem image_add_wellPlacedCentre_subset_anchorWindow_self {n m : ℤ} {z : Vec d}
    (hnm : n + 2 ≤ m) (hz : z ∈ openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre z m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
  have hsub := image_add_wellPlacedCentre_subset_truncatedWindow_succ (j := n + 2)
    (m := m) hnm hz
  rw [show n + 2 + 1 = n + 3 by ring] at hsub
  exact hsub

/-! ## 2. The boundary energy leg at every centre -/

/-- **The boundary lane's energy leg at the anchor's own window centre.**

unit 4 with its two covering-geometry hypotheses discharged at the diagonal `x
= z`.  There is no geometry binder left: interior, boundary centres are all
covered. -/
theorem ae_windowEnergy_boundary_le_anchorLegs_atCentre (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
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
                  Real.sqrt (M.nu *
                      normalizedSetAverage (truncatedWindow z m n)
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
  obtain ⟨C, K, hC, hK, hmain⟩ := ae_windowEnergy_boundary_le_anchorLegs_atHinges d
  refine ⟨C, K, hC, hK, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz
  exact hmain M s hsrange hregime hsmall hs L m n hmL hnm z z hz
    (image_add_wellPlacedCentre_subset_anchorWindow_self (by omega) hz)
    (translateSet_cubeSet_coveringCube_subset_anchorParent_self (by omega) hz)

end

end Algsuperdiff.Section4.Provider.Regularity
