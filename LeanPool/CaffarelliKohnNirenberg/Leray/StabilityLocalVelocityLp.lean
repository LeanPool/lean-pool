/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.VelocityTenThirds

/-!
# Stability Local Velocity Lp

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- A suitable velocity belongs to `L³` on every local box, as required for
the strong limit in `thm:stability`. -/
theorem stability_velocity_memLp_three_on_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolution Ω I q u Du p 0)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J) :
    MemLp u 3 (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
  obtain ⟨_hopen, hΩcompact, hΩsub, _hconn, hJcompact, hJsub⟩ := hbox
  let K : Set ParabolicPoint := closure Ω' ×ˢ closure J
  have hK : IsCompact K := by
    apply parabolicHomeomorph.isCompact_preimage.mpr
    change IsCompact (closure Ω' ×ˢ closure J)
    exact hΩcompact.prod hJcompact
  have hKsub : K ⊆ CKN.spaceTimeSet Ω I := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hΩsub hx, hJsub ht⟩
  have hboxsub : CKN.spaceTimeSet Ω' J ⊆ K := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨subset_closure hx, subset_closure ht⟩
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p 0 :=
    (CKN.isSuitableWeakSolution_iff_integrable.mp hsol).toData
  have hLp := (CKN.velocity_memLp_three_on_compact_of_data hdata hK hKsub).mono_measure
    (Measure.restrict_mono hboxsub le_rfl)
  norm_num at hLp ⊢
  exact hLp

end CKN
