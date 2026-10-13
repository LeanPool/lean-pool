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
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set core : Set (Vec d) := caccioppoliCoreSet (originCube d (n + 2)) (x - c) with hcore
  -- the covering core sits inside the anchor's cube
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
  -- the anchor's own window at scale `n` is the translated child cube
  have hwin : truncatedWindow x m n = translateSet x (openCubeSet (originCube d n)) := by
    rw [truncatedWindow, image_add_eq_translateSet]
    exact Set.inter_eq_self_of_subset_left hsubx
  have hlhs : normalizedSetAverage (truncatedWindow x m (n + 2 - 2))
      (fun y => M.nu * vecNormSq (u.grad y)) =
      M.nu * normalizedSetAverage (openCubeSet (originCube d n))
        (fun y => vecNormSq (u.grad (y + x))) := by
    rw [show n + 2 - 2 = n by ring, hwin, normalizedSetAverage_const_mul,
      normalizedSetAverage_vecNormSq_translateSet x (openCubeSet (originCube d n)) u.grad]
  have hrhs : normalizedSetAverage core (fun y => M.nu * vecNormSq (u.grad (y + c))) =
      M.nu * normalizedSetAverage core (fun y => vecNormSq (u.grad (y + c))) :=
    normalizedSetAverage_const_mul _ M.nu _
  rw [hlhs, hrhs] at hcov
  rw [localizedCoeffEnergyValue_parentRebasedFamily_eq M L k x z omega (originCube d n),
    localizedCoeffEnergyValue_parentRebasedFamily_eq M L k c z omega (originCube d (n + 2))]
  exact hcov

/-! ## 2. The boundary energy estimate at the re-based family -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
