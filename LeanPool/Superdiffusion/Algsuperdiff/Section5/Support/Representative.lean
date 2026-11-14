/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability

/-!
# Representative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Continuous representatives on the cube `y + □_n`

The Section 5 error and regularity quantities measure a solution in the
supremum norm and in the `1/2`-Hölder seminorm, both taken **pointwise** on
`y + □_n`.  An `H¹` witness is only determined away from a null set, so those
quantities are attached not to the witness but to a continuous representative of
it.  This module names that datum and proves that it is unique where it is
asserted.

## Main definitions

* `HasCubeContinuousRepresentativeAt y n u` — the `H¹` witness `u` has an
  everywhere-defined representative that agrees with it away from a null set and
  is continuous on `y + □_n`.

## Main results

* `eqOn_of_ae_eq_of_continuousOn` — on an open set, two functions that agree away
  from a null set and are continuous there agree at every point.
* `hasCubeContinuousRepresentativeAt_unique` — any two representatives of the
  same witness agree at every point of `y + □_n`.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Continuity pins a representative -/

/-- **On an open set, an almost-everywhere identity between two functions that
are continuous there is a pointwise identity.**  The set where they differ is
open, and a nonempty open subset of `ℝ^d` has positive volume. -/
theorem eqOn_of_ae_eq_of_continuousOn {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hae : f =ᵐ[volume.restrict U] g)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    Set.EqOn f g U := by
  by_contra hne
  rw [Set.EqOn] at hne
  push Not at hne
  obtain ⟨x, hxU, hxne⟩ := hne
  have hdiff : U ∩ {z | f z ≠ g z} = ((f - g) ⁻¹' ({0} : Set ℝ)ᶜ) ∩ U := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, Pi.sub_apply, sub_eq_zero]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hVopen : IsOpen (U ∩ {z | f z ≠ g z}) := by
    obtain ⟨W, hWopen, hW⟩ :=
      (continuousOn_iff'.1 (hf.sub hg)) (({0} : Set ℝ)ᶜ) isOpen_compl_singleton
    rw [hdiff, hW]
    exact hWopen.inter hU
  have hpos : 0 < volume (U ∩ {z | f z ≠ g z}) :=
    hVopen.measure_pos volume ⟨x, hxU, hxne⟩
  have hzero : volume (U ∩ {z | f z ≠ g z}) = 0 := by
    have hres : (volume.restrict U) {z | ¬ f z = g z} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      exact hae
    rw [Measure.restrict_apply₀' hU.measurableSet.nullMeasurableSet] at hres
    rwa [Set.inter_comm]
  exact hpos.ne' hzero

/-! ## 2. The representative datum on `y + □_n` -/

/-- **`u` has a representative continuous on `y + □_n`.**

This is the datum the Section 5 regularity quantity needs in order to measure
`u` in the `1/2`-Hölder seminorm at every point of the cube, not merely away
from a null set.  No finiteness of that seminorm is required: where the source
takes the seminorm of the continuous representative, an infinite value is a
legitimate value and must be recorded as such. -/
def HasCubeContinuousRepresentativeAt (y : Vec d) (n : ℤ)
    (u : H1Function (cubeSetAt y n)) : Prop :=
  ∃ uRep : Vec d → ℝ,
    uRep =ᵐ[volume.restrict (cubeSetAt y n)] u.toFun ∧
      ContinuousOn uRep (cubeSetAt y n)

/-- **The representative is unique on the cube.**  Two representatives of the
same `H¹` witness agree at every point of `y + □_n`, so every pointwise quantity
built from one of them is independent of the choice. -/
theorem hasCubeContinuousRepresentativeAt_unique {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {u₁ u₂ : Vec d → ℝ}
    (h₁ : u₁ =ᵐ[volume.restrict (cubeSetAt y n)] u.toFun)
    (hc₁ : ContinuousOn u₁ (cubeSetAt y n))
    (h₂ : u₂ =ᵐ[volume.restrict (cubeSetAt y n)] u.toFun)
    (hc₂ : ContinuousOn u₂ (cubeSetAt y n)) :
    Set.EqOn u₁ u₂ (cubeSetAt y n) :=
  eqOn_of_ae_eq_of_continuousOn (isOpen_cubeSetAt y n) (h₁.trans h₂.symm) hc₁ hc₂

/-- Two representatives of the same witness have the same Hölder seminorm on the
cube. -/
theorem holderSeminormOn_eq_of_hasCubeContinuousRepresentativeAt {y : Vec d} {n : ℤ}
    {alpha : ℝ} {u : H1Function (cubeSetAt y n)} {u₁ u₂ : Vec d → ℝ}
    (h₁ : u₁ =ᵐ[volume.restrict (cubeSetAt y n)] u.toFun)
    (hc₁ : ContinuousOn u₁ (cubeSetAt y n))
    (h₂ : u₂ =ᵐ[volume.restrict (cubeSetAt y n)] u.toFun)
    (hc₂ : ContinuousOn u₂ (cubeSetAt y n)) :
    holderSeminormOn (cubeSetAt y n) alpha u₁ =
      holderSeminormOn (cubeSetAt y n) alpha u₂ := by
  have heq := hasCubeContinuousRepresentativeAt_unique h₁ hc₁ h₂ hc₂
  refine le_antisymm ?_ ?_ <;>
    simp only [holderSeminormOn, iSup_le_iff] <;>
    intro x hx z hz hne
  · rw [heq hx, heq hz]
    exact le_holderSeminormOn hx hz hne
  · rw [← heq hx, ← heq hz]
    exact le_holderSeminormOn hx hz hne

end

end Algsuperdiff.Section5.Support
