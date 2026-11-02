/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryEnergyRebase

/-!
# CoarseAssemblyDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Boundary Caccioppoli with the full boundary datum

The cube estimate specializes the shared window theorem and retains the value
and gradient identities of the comparison solution's boundary data.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The boundary Caccioppoli, with the full datum identity exported.**

`BoundaryEnergyRebase.exists_boundaryWindowEnergy_rebased_le_dirichletDatum
with the produced comparison solution's boundary datum identified with the
anchor's transported datum in **both** halves — values and gradients.  The
gradient half is what the Dirichlet-energy leg needs in order to read
`dirichletEnergyWith's boundary-gradient leg on `∇h(· + c)`. -/
theorem exists_boundaryWindowEnergy_rebased_le_dirichletDatumRHS_full
    (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (m n : ℤ)
        (x z : Vec d) (s t r : ℝ)
        (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        x ∈ openCubeSet (originCube d m) → n + 2 ≤ m →
        ∀ hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
            openCubeSet (originCube d m),
        Support.IsDirichletSolutionOn
          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m)
          u hdat g →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 → 0 < r → r < 1 →
        ForceBesovRegularity (originCube d (n + 2)) r
          (fun y => -g (y + wellPlacedCentre x m (n + 2))) →
        ForceBesovRegularity (originCube d (n + 2)) r
          (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) →
          ∃ v : DirichletForcedCubeSolution (originCube d (n + 2))
              (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
              (fun y => -g (y + wellPlacedCentre x m (n + 2))),
            (∀ y, v.boundaryData.toFun y =
                hdat.toFun (y + wellPlacedCentre x m (n + 2))) ∧
            (∀ y, v.boundaryData.grad y =
                hdat.grad (y + wellPlacedCentre x m (n + 2))) ∧
              localizedCoeffEnergyValue (openCubeSet (originCube d n))
                  ((parentRebasedFamily M L (n + 3) x z omega).coeffOn (originCube d n))
                  (H1Function.untranslate x
                    (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
                (3 : ℝ) ^ d *
                  (2 * (caccioppoliWithRHSPrefactor C₁ (originCube d (n + 2))
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) s t *
                      (Ch02.lambdaS (originCube d (n + 2)) t
                          (parentRebasedFamily M L (n + 3)
                            (wellPlacedCentre x m (n + 2)) z omega) *
                        Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
                        normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
                          (fun y => u.toFun (y + wellPlacedCentre x m (n + 2)) -
                            v.toH1.toFun y))) +
                    2 * ((18 : ℝ) ^ d *
                      dirichletEnergyWithRHSRHS C₂ (originCube d (n + 2))
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) r
                        (fun y => -g (y + wellPlacedCentre x m (n + 2))) v ^ 2)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hmain⟩ :=
    exists_boundaryWindowEnergy_rebased_window_le_dirichletDatumRHS d
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M L omega m n x z s t r u hdat g hx hnm hsubx hsol hs hs1 ht ht2 hst hr hr1 hgTr hhTr
  obtain ⟨v, hv, hgrad, henergy⟩ :=
    hmain M L omega m n x z s t r u hdat g hx hnm hsol hs hs1 ht ht2 hst hr hr1 hgTr hhTr
  refine ⟨v, hv, hgrad, ?_⟩
  have hwin : truncatedWindow x m n = translateSet x (openCubeSet (originCube d n)) := by
    rw [truncatedWindow, image_add_eq_translateSet]
    exact Set.inter_eq_self_of_subset_left hsubx
  rw [hwin, normalizedSetAverage_vecNormSq_translateSet x (openCubeSet (originCube d n))
    u.grad] at henergy
  rw [localizedCoeffEnergyValue_parentRebasedFamily_eq M L (n + 3) x z omega (originCube d n)]
  exact henergy

end

end Algsuperdiff.Section4.Provider.ExcessDecay
