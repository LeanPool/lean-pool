/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryOuterAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEnergyBridge

/-!
# BoundaryEnergyRebase

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary energy estimate, re-based on the parent's `(n+3)` flux increment

`BoundaryOuterAssembly.exists_boundaryWindowEnergy_le_dirichletDatum` runs the
boundary Caccioppoli at the covering cube's **own** flux-corrected family
`wellPlacedFluxCorrectedFamily M L m k x ω`.  Every coarse-grained cap the
frozen general clause supplies — `BoundaryPrefactor`'s
`ae_coveringCubeCapsPair_le` and `ae_coveringCubePrefactor_le` — is
written at the **parent-rebased** family `parentRebasedFamily M L (n+3) c z ω`,
`c = wellPlacedCentre x m (n+2)`, because that is the family the good
event `𝒢(n+3, z; s/8, 1/2)` controls.  This module re-runs the boundary energy
estimate at that family.

**No `Λ`/`λ` is converted by invariance anywhere in this module** (`R-ii`).

## The left-hand side is `ν`-free

`BoundaryOuterAssembly` states its conclusion as `ν ⨍|∇u|²` on the anchor's own
window.  Here the same quantity is written as CoarseGraining's own
`localizedCoeffEnergyValue` on the child cube `□_n` at the `x`-frame re-based
family — the object `ReindexComposed`'s chain consumes as
`h1EnergyNormOnCube²` — so that **no estimate slot of this module carries
`ν`**.  Both sides of the transport are `ν ⨍|∇u|²` on their own window, so `ν`
cancels inside the proof and the inequality is the pure `3^d` volume ratio.

## References

* ABK26, `l.coarse.grained.Caccioppoli`;
  `l.harmonic.approximation.good.scales`, (the "differ by a constant
  anti-symmetric matrix" observation).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The covering transport at the re-based family -/

/-- **The anchor's child-cube energy, transported onto CoarseGraining's Caccioppoli
core.**

The localized coefficient energy of the `x`-frame re-based family on the child
cube `□_n` is at most `3^d` times the localized coefficient energy of the
`c`-frame re-based family on CoarseGraining's Caccioppoli core of the covering
cube, `c = wellPlacedCentre x m (n+2)`. -/
theorem nu_mul_normalizedSetAverage_truncatedWindow_le_coreEnergy_rebased
    (M : ABKModel d) (L k : ℤ) (omega : Cutoff.CutoffSample d) {m n : ℤ} {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n + 2 ≤ m)
    (u : H1Function (openCubeSet (originCube d m))) :
    M.nu * normalizedSetAverage (truncatedWindow x m n)
        (fun y => vecNormSq (u.grad y)) ≤
      (3 : ℝ) ^ d *
        localizedCoeffEnergyValue
          (caccioppoliCoreSet (originCube d (n + 2)) (x - wellPlacedCentre x m (n + 2)))
          ((parentRebasedFamily M L k (wellPlacedCentre x m (n + 2)) z omega).coeffOn
            (originCube d (n + 2)))
          (H1Function.untranslate (wellPlacedCentre x m (n + 2))
            (u.restrict
              (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + 2)) (n + 2))
              (translateSet_wellPlacedCentre_subset x hnm))) := by
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set core : Set (Vec d) := caccioppoliCoreSet (originCube d (n + 2)) (x - c) with hcore
  have hcore_sub : ((fun y => c + y) '' core) ⊆ openCubeSet (originCube d m) := by
    intro p hp
    rw [mem_image_add_iff] at hp
    have hp' : p - c ∈ openCubeSet (originCube d (n + 2)) := hp.1
    have hmem : p ∈ translateSet c (openCubeSet (originCube d (n + 2))) :=
      (mem_translateSet_iff_sub_mem).2 hp'
    exact translateSet_wellPlacedCentre_subset x hnm hmem
  have hmono : volumeMeasureOn ((fun y => c + y) '' core) ≤
      volumeMeasureOn (openCubeSet (originCube d m)) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hcore_sub
  have hgradL2 : MemVectorL2 ((fun y => c + y) '' core) u.grad :=
    u.grad_memVectorL2.mono_measure hmono
  have hsq : MeasureTheory.IntegrableOn (fun y => vecNormSq (u.grad y))
      ((fun y => c + y) '' core) MeasureTheory.volume :=
    integrableOn_vecDot_of_memVectorL2 hgradL2 hgradL2
  have hint : MeasureTheory.IntegrableOn (fun y => M.nu * vecNormSq (u.grad y))
      ((fun y => c + y) '' core) MeasureTheory.volume := hsq.const_mul M.nu
  have hf : ∀ y ∈ (fun y => c + y) '' core, 0 ≤ M.nu * vecNormSq (u.grad y) :=
    fun y _ => mul_nonneg M.nu_pos.le (vecNormSq_nonneg (u.grad y))
  have hcov :=
    normalizedSetAverage_truncatedWindow_le_three_pow_mul_untranslatedCore hx hnm hf hint
  have hlhs : normalizedSetAverage (truncatedWindow x m (n + 2 - 2))
      (fun y => M.nu * vecNormSq (u.grad y)) =
      M.nu * normalizedSetAverage (truncatedWindow x m n)
        (fun y => vecNormSq (u.grad y)) := by
    rw [show n + 2 - 2 = n by ring, normalizedSetAverage_const_mul]
  have hrhs : normalizedSetAverage core (fun y => M.nu * vecNormSq (u.grad (y + c))) =
      localizedCoeffEnergyValue core
        ((parentRebasedFamily M L k c z omega).coeffOn (originCube d (n + 2)))
        (H1Function.untranslate c
          (u.restrict (isOpen_translateSet_openCubeSet c (n + 2))
            (translateSet_wellPlacedCentre_subset x hnm))) := by
    rw [localizedCoeffEnergyValue_parentRebasedFamily_eq M L k c z omega
      (originCube d (n + 2)), ← normalizedSetAverage_const_mul]
    rfl
  rw [hlhs, hrhs] at hcov
  exact hcov

/-! ## 2. The boundary energy estimate at the re-based family, at the window -/

/-- **The boundary-regime energy estimate at the `(n+3)` re-based family, read at the
anchor's own truncated window.**

`BoundaryEnergyRebase`'s display with its `localizedCoeffEnergyValue (□_n)`
left-hand side — and the inclusion binder `x + □_n ⊆ □_m` it requires —
replaced by `BoundaryOuterAssembly`'s gate-free `ν ⨍_{(x+□_n)∩□_m} |∇u|²`.  The
comparison solution `v` on the covering cube is **produced**, carrying the
transported boundary datum `h(·+c)`. -/
theorem exists_boundaryWindowEnergy_rebased_window_le_dirichletDatumRHS
    (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (m n : ℤ)
        (x z : Vec d) (s t r : ℝ)
        (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        x ∈ openCubeSet (originCube d m) → n + 2 ≤ m →
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
              M.nu * normalizedSetAverage (truncatedWindow x m n)
                  (fun y => vecNormSq (u.grad y)) ≤
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
  intro M L omega m n x z s t r u hdat g hx hnm hsol hs hs1 ht ht2 hst hr hr1 hgTr hhTr
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
  have hcov := nu_mul_normalizedSetAverage_truncatedWindow_le_coreEnergy_rebased
    (z := z) M L (n + 3) omega hx hnm u
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  refine hcov.trans (mul_le_mul_of_nonneg_left ?_ h3d)
  exact hcacc


theorem localizedCoeffEnergyValue_childCube_le_three_pow_mul_coveringCore
    (M : ABKModel d) (L k : ℤ) (omega : Cutoff.CutoffSample d) {m n : ℤ} {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n + 2 ≤ m)
    (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) :
    localizedCoeffEnergyValue (openCubeSet (originCube d n))
        ((parentRebasedFamily M L k x z omega).coeffOn (originCube d n))
        (H1Function.untranslate x
          (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      (3 : ℝ) ^ d *
        localizedCoeffEnergyValue
          (caccioppoliCoreSet (originCube d (n + 2)) (x - wellPlacedCentre x m (n + 2)))
          ((parentRebasedFamily M L k (wellPlacedCentre x m (n + 2)) z omega).coeffOn
            (originCube d (n + 2)))
          (H1Function.untranslate (wellPlacedCentre x m (n + 2))
            (u.restrict
              (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + 2)) (n + 2))
              (translateSet_wellPlacedCentre_subset x hnm))) := by
  have h := nu_mul_normalizedSetAverage_truncatedWindow_le_coreEnergy_rebased
    (z := z) M L k omega hx hnm u
  have hwin : truncatedWindow x m n = translateSet x (openCubeSet (originCube d n)) := by
    rw [truncatedWindow, image_add_eq_translateSet]
    exact Set.inter_eq_self_of_subset_left hsubx
  rw [hwin, normalizedSetAverage_vecNormSq_translateSet x (openCubeSet (originCube d n))
    u.grad] at h
  rw [localizedCoeffEnergyValue_parentRebasedFamily_eq M L k x z omega (originCube d n)]
  exact h

/-! ## 2. The boundary energy estimate at the re-based family -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
