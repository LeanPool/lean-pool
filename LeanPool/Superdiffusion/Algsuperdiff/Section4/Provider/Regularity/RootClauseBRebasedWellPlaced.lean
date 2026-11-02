/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCoarseFrameWellPlaced
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccBoundaryLattice
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEnergyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportAssembly

/-!
# RootClauseBRebasedWellPlaced

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `hgradE` identity at the re-based family, at the gate -/

/-- **The `hgradE` identity at the gate, at the re-based family.**
The gate identity for the child's flux-corrected family, with that family
replaced by `parentRebasedFamily`: both have
symmetric part `ν Id`, so the identity is unchanged. -/
theorem forcedSolutionEnergyNorm_rebased_eq_nuGradNorm_gate (M : ABKModel d)
    (L kk m j : ℤ) {c zr : Vec d} (omega : Cutoff.CutoffSample d)
    {g : Vec d → Vec d}
    (u : ForcedCubeSolution (originCube d j) (parentRebasedFamily M L kk c zr omega) g)
    (G : Vec d → Vec d) (hg : ∀ y, u.toH1.grad y = G (y + c))
    (hgate : (fun y => c + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m)) :
    forcedSolutionEnergyNorm (originCube d j)
        (parentRebasedFamily M L kk c zr omega) u =
      stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow c m j) G := by
  rw [forcedSolutionEnergyNorm, h1EnergyNormOnCube, stepSevenNuGradNorm]
  congr 1
  rw [localizedCoeffEnergyValue_parentRebasedFamily_eq]
  have hfun : (fun x => vecNormSq (u.toH1.grad x)) = fun x => vecNormSq (G (x + c)) := by
    funext x
    rw [hg x]
  have h1 := normalizedSetAverage_vecNormSq_translateSet c
    (openCubeSet (originCube d j)) G
  rw [truncatedWindow_eq_translateSet_of_gate hgate, hfun]
  exact congrArg (fun t : ℝ => (M.nu : ℝ) * t) h1.symm

/-! ## 2. The coarse solution object at the well-placed frame, re-based -/

/-- **The Caccioppoli's coarse solution object at the print's own frame centre, at
the re-based family.**  The coarse-frame solution object with the family moved
onto `parentRebasedFamily` through `InteriorRebase`'s equation transport; the
gate is discharged from `k ≤ m` alone, so no geometry binder survives. -/
theorem exists_coarseFrameSolutionRebased {m k : ℤ} (M : ABKModel d) (L kk : ℤ)
    {z : Vec d} (zr : Vec d) (omega : Cutoff.CutoffSample d)
    {uglob hdat : H1Function (openCubeSet (originCube d m))} {gsrc : Vec d → Vec d}
    (hkm : k ≤ m)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) uglob hdat
      gsrc) :
    ∃ v : H1Function (Ch02.cubeDomain (originCube d k) : Set (Vec d)),
      (∀ y, v.toFun y = uglob.toFun (y + wellPlacedCentre z m k)) ∧
      (∀ y, v.grad y = uglob.grad (y + wellPlacedCentre z m k)) ∧
      IsForcedEquation (originCube d k)
        (parentRebasedFamily M L kk (wellPlacedCentre z m k) zr omega) v
        (fun x => -gsrc (x + wellPlacedCentre z m k)) := by
  have hsub : translateSet (wellPlacedCentre z m k) (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet]
    exact image_add_wellPlacedCentre_subset_openCubeSet z hkm
  refine ⟨H1Function.untranslate (wellPlacedCentre z m k)
      (uglob.restrict
        (isOpen_translateSet_openCubeSet (wellPlacedCentre z m k) k) hsub),
    ?_, ?_, ?_⟩
  · intro y
    exact untranslate_restrict_toFun uglob hsub y
  · intro _
    rfl
  · exact isForcedEquation_parentRebasedFamily M L (wellPlacedCentre z m k) zr omega
      hsub hsol.2

/-! ## 3. The energy-norm domination at the well-placed frame, re-based -/

/-- **The coarse `hgradE` slot at the re-based family, at no geometry binder.**
The coarse-frame energy-norm domination with the family moved onto
`parentRebasedFamily`; the constant is still the printed volume ratio
`rootClauseBTopKg d m k`. -/
theorem forcedSolutionEnergyNorm_coarseFrameRebased_le (M : ABKModel d)
    (L kk k m : ℤ) {z : Vec d} (zr : Vec d) (omega : Cutoff.CutoffSample d)
    {g : Vec d → Vec d}
    (u : ForcedCubeSolution (originCube d k)
      (parentRebasedFamily M L kk (wellPlacedCentre z m k) zr omega) g)
    (uglob : H1Function (openCubeSet (originCube d m)))
    (hg : ∀ y, u.toH1.grad y = uglob.grad (y + wellPlacedCentre z m k))
    (hkm : k ≤ m) :
    forcedSolutionEnergyNorm (originCube d k)
        (parentRebasedFamily M L kk (wellPlacedCentre z m k) zr omega) u ≤
      rootClauseBTopKg d m k *
        stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad := by
  rw [forcedSolutionEnergyNorm_rebased_eq_nuGradNorm_gate M L kk m k omega u
    uglob.grad hg (coarseFrame_subset_openCubeSet z hkm)]
  exact stepSevenNuGradNorm_window_le_cube_gate d (le_of_lt M.nu_pos)
    (coarseFrame_subset_openCubeSet z hkm) uglob

end

end Algsuperdiff.Section4.Provider.Regularity
