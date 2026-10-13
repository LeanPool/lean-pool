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
# The boundary-Caccioppoli export sibling: the full boundary-datum identity

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## Why this module exists

`BoundaryEnergyRebase.exists_boundaryWindowEnergy_rebased_le_dirichletDatumRHS` (the
general-data boundary Caccioppoli) produces the covering-cube Dirichlet
comparison `v` and exports only the **value** half of its datum identity,

```text
  ∀ y, v.boundaryData.toFun y = hdat.toFun (y + c) ,   c = wellPlacedCentre x m (n+2) .
```

The Dirichlet-energy leg
(`CoarseDirichletEnergy.dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs`) consumes
the **gradient** half,

```text
  ∀ y, v.boundaryData.grad y = hdat.grad (y + c) ,
```

because CoarseGraining's `dirichletEnergyWithRHSRHS` reads the datum through
`dirichletBoundaryGradientField`.  The underlying producer
(`BoundaryAssemblyDirichlet.exists_dirichletForcedCubeSolution_boundaryData`)
already returns the full `H1Function` equality `v.boundaryData = h`, so both
halves are available at no cost; only the export was narrow.

This module re-runs that script with the full identity exported.  The tracked
file is **not** edited: `exists_boundaryWindowEnergy_rebased_le_dirichletDatumRHS`
stays exactly as it is and this is an independent public sibling.

## References

* CoarseGraining: `Book/Ch03/Definitions.lean` (`DirichletForcedCubeSolution`),
  `Book/Ch03/Theorems/Energy/Theory.lean`.
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
    exists_boundaryCaccioppoliEnergy_withLocalizedBoundaryDatum d
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M L omega m n x z s t r u hdat g hx hnm hsubx hsol hs hs1 ht ht2 hst hr hr1 hgTr hhTr
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set aFam : Ch03.CoeffFamily d := parentRebasedFamily M L (n + 3) c z omega with haFam
  set hsub : translateSet c (openCubeSet (originCube d (n + 2))) ⊆
      openCubeSet (originCube d m) := translateSet_wellPlacedCentre_subset x hnm
    with hsubdef
  set utr : H1Function (openCubeSet (originCube d (n + 2))) :=
    H1Function.untranslate c
      (u.restrict (isOpen_translateSet_openCubeSet c (n + 2)) hsub) with hutr
  set htr : H1Function (openCubeSet (originCube d (n + 2))) :=
    H1Function.untranslate c
      (hdat.restrict (isOpen_translateSet_openCubeSet c (n + 2)) hsub) with hhtr
  have heq : IsForcedEquation (originCube d (n + 2)) aFam utr (fun y => -g (y + c)) := by
    rw [haFam, hutr]
    exact isForcedEquation_parentRebasedFamily (k := n + 3) M L c z omega hsub hsol.2
  have hgL2 : MemVectorL2 (openCubeSet (originCube d (n + 2))) (fun y => -g (y + c)) :=
    memVectorL2_openCubeSet_of_forceBesovRegularity hgTr
  obtain ⟨v, hvdat, sigma, hsigma⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData (originCube d (n + 2)) aFam htr hgL2
  refine ⟨v, fun y => ?_, fun y => ?_, ?_⟩
  · rw [hvdat, hhtr]
    rfl
  · rw [hvdat, hhtr]
    rfl
  obtain ⟨rho, hrhoval, _hrhograd⟩ := hsol.1
  have hUV : ∀ y, utr.toFun y - v.toH1.toFun y =
      rho.toH1Function.toFun (y + c) - sigma.toH1Function.toFun y := by
    intro y
    have hu : utr.toFun y = u.toFun (y + c) := rfl
    have hh : htr.toFun y = hdat.toFun (y + c) := rfl
    rw [hu, hrhoval (y + c), hsigma y, hh]
    ring
  have hloc := localizedZeroTraceFunctionOn_wellPlacedDifference x hnm rho sigma hUV
  have hscale : (originCube d (n + 2)).scale - 1 = n + 2 - 1 := by
    rw [scale_originCube]
  have hloc' : Ch01.LocalizedZeroTraceFunctionOn
      (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d))
      (openCubeAtScale (x - c) ((originCube d (n + 2)).scale - 1))
      (fun y => utr.toFun y - v.toH1.toFun y) := by
    rw [hscale]
    exact hloc
  have hhv : ForceBesovRegularity (originCube d (n + 2)) r
      (dirichletBoundaryGradientField v) := by
    rw [dirichletBoundaryGradientField, hvdat]
    exact hhTr
  have hxk : x - c ∈ openCubeSet (originCube d (n + 2)) :=
    sub_wellPlacedCentre_mem_openCubeSet hx hnm
  have hcacc := hmain (Q := originCube d (n + 2)) (a := aFam) (s := s) (t := t) (r := r)
    (x := x - c) (g := fun y => -g (y + c)) utr v heq hloc' hs hs1 ht ht2 hst hr hr1
    hgTr hhv hxk
  rw [scale_originCube] at hcacc
  have hcov := localizedCoeffEnergyValue_childCube_le_three_pow_mul_coveringCore
    (z := z) M L (n + 3) omega hx hnm hsubx u
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  refine hcov.trans (mul_le_mul_of_nonneg_left ?_ h3d)
  exact hcacc

end

end Algsuperdiff.Section4.Provider.ExcessDecay
