/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.HigherWeakDeriv


/-!
# Smoothness of a locally smooth representative

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (p. 334) is proved on
balls: the Sobolev ladder runs inside a ball compactly contained in the region, and produces a
smooth function agreeing almost everywhere with the solution there. The theorem is stated on the
region. This file is the passage between the two, the only part of that argument with no
analysis.

Two observations do the work.

* **Agreement of the local representatives on their overlap.** Both are continuous on the
  intersection of their balls, which is open, and agree almost everywhere with the same class
  there. A nonempty open set has positive Lebesgue measure, so two continuous functions agreeing
  almost everywhere on one agree on it.
* **So no gluing is needed.** Sending `x` to the value at `x` of the representative attached to
  `x` itself already agrees with every local representative on all of that representative's
  ball, by the previous point. Smoothness is then local, and the almost everywhere identity
  follows from a countable subcover.

## Main declarations

* `eqOn_of_ae_eq_of_continuousOn`: continuous functions agreeing almost everywhere on an open
  set agree on it.
* `exists_contDiffOn_of_locally_ae`: local smooth representatives assemble into one.
* `exists_contDiffOn_of_compact_ae`: the same, with the local hypothesis stated over compact
  subsets rather than open balls, which is the shape a bootstrap run on a compact exhaustion
  supplies.
* `exists_contDiffOn_of_closedBall_ae`: the same, stated over closed balls, which is what a
  bootstrap such as `interior_smooth` supplies directly.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

variable {d : ℕ}

/-- **Almost everywhere equality upgrades to equality for continuous functions on an open set.**
Where they differ at a point they differ on an open neighbourhood, which has positive Lebesgue
measure. -/
theorem eqOn_of_ae_eq_of_continuousOn {W : Set (EuclideanSpace ℝ (Fin d))} (hW : IsOpen W)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (hae : f =ᵐ[volume.restrict W] g) : Set.EqOn f g W := by
  intro x hx
  by_contra hne
  have hcont : ContinuousAt (fun y => f y - g y) x :=
    (hf.sub hg).continuousAt (hW.mem_nhds hx)
  have hev : ∀ᶠ y in nhds x, ¬ f y = g y := by
    filter_upwards [hcont.eventually_ne (sub_ne_zero.2 hne)] with y hy hc
    exact hy (by rw [hc, sub_self])
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.1 (Filter.inter_mem hev (hW.mem_nhds hx))
  have hOW : O ⊆ W := fun y hy => (hOsub hy).2
  have hzero : volume.restrict W O = 0 :=
    nonpos_iff_eq_zero.1
      ((measure_mono (fun y hy => (hOsub hy).1)).trans (ae_iff.1 hae).le)
  rw [Measure.restrict_apply hOo.measurableSet,
    Set.inter_eq_self_of_subset_left hOW] at hzero
  exact absurd hzero (hOo.measure_pos volume ⟨x, hxO⟩).ne'

/-- **Local smooth representatives assemble into one.** If every point of an open `U` has an
open ball inside `U` on which some smooth function agrees almost everywhere with `u`, then a
single smooth function does so on all of `U`.

No gluing construction appears. The value at `x` is taken from the representative attached to
`x`, and `eqOn_of_ae_eq_of_continuousOn` makes that choice agree with every other representative
on all of its own ball, which is what turns pointwise selection into a locally smooth function. -/
theorem exists_contDiffOn_of_locally_ae {U : Set (EuclideanSpace ℝ (Fin d))} (hUo : IsOpen U)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ∀ x ∈ U, ∃ B : Set (EuclideanSpace ℝ (Fin d)), IsOpen B ∧ x ∈ B ∧ B ⊆ U ∧
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v B ∧
        v =ᵐ[volume.restrict B] u) :
    ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
      u' =ᵐ[volume.restrict U] u ∧ ContDiffOn ℝ (⊤ : ℕ∞) u' U := by
  classical
  choose B hBo hxB hBU v hvc hvae using h
  -- The representative attached to `x` agrees with the one attached to `y` on `B y`.
  have key : ∀ (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ U),
      Set.EqOn (fun x => if hx : x ∈ U then v x hx x else 0) (v y hy) (B y hy) := by
    intro y hy x hxB'
    have hxU : x ∈ U := hBU y hy hxB'
    have hInt : IsOpen (B x hxU ∩ B y hy) := (hBo x hxU).inter (hBo y hy)
    have hmono : ∀ (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ U),
        B x hxU ∩ B y hy ⊆ B z hz → v z hz =ᵐ[volume.restrict (B x hxU ∩ B y hy)] u :=
      fun z hz hsub =>
        (hvae z hz).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hagree : Set.EqOn (v x hxU) (v y hy) (B x hxU ∩ B y hy) :=
      eqOn_of_ae_eq_of_continuousOn hInt
        ((hvc x hxU).continuousOn.mono Set.inter_subset_left)
        ((hvc y hy).continuousOn.mono Set.inter_subset_right)
        ((hmono x hxU Set.inter_subset_left).trans
          (hmono y hy Set.inter_subset_right).symm)
    simp only [dite_eq_left hxU]
    exact hagree ⟨hxB x hxU, hxB'⟩
  refine ⟨fun x => if hx : x ∈ U then v x hx x else 0, ?_, ?_⟩
  · -- Almost everywhere on `U`, through a countable subcover.
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : {x : EuclideanSpace ℝ (Fin d) // x ∈ U} => B i.1 i.2) (fun i => hBo i.1 i.2)
    have hUeq : U = ⋃ i ∈ T, B i.1 i.2 := by
      rw [hTU]
      refine Set.Subset.antisymm (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxB x hx⟩) ?_
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hBU i.1 i.2 hi
    set N : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | ¬ (if hx : x ∈ U then v x hx x else 0) = u x} with hN
    have hNi : ∀ i ∈ T, volume (N ∩ B i.1 i.2) = 0 := by
      intro i _
      have hlocal : ∀ᵐ x ∂(volume.restrict (B i.1 i.2)),
          (if hx : x ∈ U then v x hx x else 0) = u x := by
        filter_upwards [hvae i.1 i.2, ae_restrict_mem (hBo i.1 i.2).measurableSet] with x h1 h2
        have hk : (if hx : x ∈ U then v x hx x else 0) = v i.1 i.2 x := key i.1 i.2 h2
        rw [hk, h1]
      have hz := ae_iff.1 hlocal
      rw [hN]
      rwa [Measure.restrict_apply₀' (hBo i.1 i.2).measurableSet.nullMeasurableSet] at hz
    have hsplit : N ∩ U = ⋃ i ∈ T, N ∩ B i.1 i.2 := by
      rw [← Set.inter_iUnion₂, ← hUeq]
    rw [Filter.EventuallyEq, ae_iff,
      Measure.restrict_apply₀' hUo.measurableSet.nullMeasurableSet]
    change volume (N ∩ U) = 0
    rw [hsplit]
    exact (measure_biUnion_null_iff hTc).2 hNi
  · -- Smoothness is local, and on each ball the function is a local representative.
    refine contDiffOn_of_locally_contDiffOn fun x hx => ⟨B x hx, hBo x hx, hxB x hx, ?_⟩
    rw [Set.inter_eq_self_of_subset_right (hBU x hx)]
    exact (hvc x hx).congr fun y hy => key x hx hy

/-- **Local smooth representatives on compact sets assemble into one.** A version of
`exists_contDiffOn_of_locally_ae` whose local hypothesis is stated over compact subsets of `U`
rather than open balls: if every compact `V ⊆ U` has a smooth representative agreeing with `u`
almost everywhere on the interior of `V`, then a single smooth function does so on all of `U`.
This is the shape a bootstrap run on a compact exhaustion, such as `interior_smooth`, supplies
its conclusion in, one exhaustion piece at a time, with nothing relating two different pieces;
`interior_smooth_global` glues them through this lemma into one representative on the whole
region. -/
theorem exists_contDiffOn_of_compact_ae {U : Set (EuclideanSpace ℝ (Fin d))} (hUo : IsOpen U)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ∀ V : Set (EuclideanSpace ℝ (Fin d)), IsCompact V → V ⊆ U →
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
        v =ᵐ[volume.restrict (interior V)] u ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (interior V)) :
    ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
      u' =ᵐ[volume.restrict U] u ∧ ContDiffOn ℝ (⊤ : ℕ∞) u' U := by
  refine exists_contDiffOn_of_locally_ae hUo u fun x hx => ?_
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hUo x hx
  have hcl : Metric.closedBall x (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  obtain ⟨v, hvae, hvc⟩ := h _ (isCompact_closedBall x (r / 2)) hcl
  have hBint : Metric.ball x (r / 2) ⊆ interior (Metric.closedBall x (r / 2)) :=
    interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
  refine ⟨Metric.ball x (r / 2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith),
    Metric.ball_subset_closedBall.trans hcl, v, hvc.mono hBint, ?_⟩
  exact hvae.filter_mono (ae_mono (Measure.restrict_mono hBint le_rfl))

/-- A version of `exists_contDiffOn_of_compact_ae` asking only for closed balls, which is what
the local hypotheses of a difference-quotient bootstrap supply directly, with no compact set to
name first. -/
theorem exists_contDiffOn_of_closedBall_ae {U : Set (EuclideanSpace ℝ (Fin d))} (hUo : IsOpen U)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ∀ x r, 0 < r → Metric.closedBall x r ⊆ U →
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
        v =ᵐ[volume.restrict (Metric.ball x r)] u ∧
          ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball x r)) :
    ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
      u' =ᵐ[volume.restrict U] u ∧ ContDiffOn ℝ (⊤ : ℕ∞) u' U := by
  refine exists_contDiffOn_of_locally_ae hUo u fun x hx => ?_
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hUo x hx
  have hcl : Metric.closedBall x (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  obtain ⟨v, hvae, hvc⟩ := h x (r / 2) (by linarith) hcl
  exact ⟨Metric.ball x (r / 2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith),
    Metric.ball_subset_closedBall.trans hcl, v, hvc, hvae⟩

end EllipticPdes.Regularity
