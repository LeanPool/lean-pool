/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalVelocityLp
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Stability Local Finite

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- A local box in `def:sws` has finite space-time measure. -/
theorem stability_localBox_finiteMeasure
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    IsFiniteMeasure (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
  obtain ⟨_hopen, hΩcompact, _hΩsub, _hconn, hJcompact, _hJsub⟩ := hbox
  let K : Set ParabolicPoint := closure Ω' ×ˢ closure J
  have hK : IsCompact K := by
    apply parabolicHomeomorph.isCompact_preimage.mpr
    change IsCompact (closure Ω' ×ˢ closure J)
    exact hΩcompact.prod hJcompact
  have hsub : CKN.spaceTimeSet Ω' J ⊆ K := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨subset_closure hx, subset_closure ht⟩
  have hfinite : IsFiniteMeasure (volume.restrict K) :=
    CKN.isFiniteMeasure_restrict_of_isCompact hK
  apply isFiniteMeasure_restrict.mpr
  have hμ : (volume : Measure ParabolicPoint) (CKN.spaceTimeSet Ω' J) < ⊤ := by
    calc
      (volume : Measure ParabolicPoint) (CKN.spaceTimeSet Ω' J) ≤ volume K :=
        measure_mono hsub
      _ < ⊤ := by
        simpa using hfinite.measure_univ_lt_top
  exact hμ.ne

end CKN
