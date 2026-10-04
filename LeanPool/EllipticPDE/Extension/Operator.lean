/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.LocalExtension


/-!
# Gluing the local extensions

Guo's third step covers the boundary, fixes a partition of unity subordinate to that cover with
each support compactly inside its neighbourhood, and sets `ū = ∑ᵢ Pᵢ ūᵢ`. This file carries out
that sum.

Each piece is a local extension cut down by its piece of the partition, so the cutoff comes
after the extension. That order is what makes the sum agree with the class: where a piece of the
partition is nonzero the point lies in that chart's ball, where the local extension agrees with
the class, so the piece equals `Pᵢ u` there and off the ball both sides vanish. The pieces then
add to `u` because the partition adds to one.

`supp(Pᵢ) ⋐ Wᵢ` is compact containment, and the local extension of step 2 lives on a ball
strictly inside the chart's, so the support is first pushed into a smaller ball. A compact
subset of an open ball admits one.

The support clause follows by one more cutoff, which is how Guo reaches it: any open set the
closure of the domain sits in admits a smooth cutoff equal to one on that closure, and
multiplying by it moves the support inside without disturbing the agreement.

## Constant of clause (iii)

The partition, the charts, the radii and the supremum of each piece and of its partials all
depend on the domain alone, so `exists_extension_bound` fixes them before the class appears and
sums the local constants of `exists_localExtension_bound` over the finitely many pieces. That is
clause (iii): one constant, depending on the domain and the exponent, bounding the extension and
its gradient by the class and its gradient over the domain.

## Main declarations

* `EllipticPdes.Extension.exists_lt_radius_of_isCompact_subset_ball`: a compact subset of an open
  ball sits in a strictly smaller one.
* `EllipticPdes.Extension.exists_extension_bound`: the class extends across the whole boundary,
  with a constant taken before the class.
* `EllipticPdes.Extension.exists_extension`: the same with the constant discarded.
* `EllipticPdes.Extension.exists_cutoff_one_on_compact`: a smooth cutoff between a compact set
  and an open one.
* `EllipticPdes.Extension.exists_extension_subset_bound`: the three clauses of the theorem.
* `EllipticPdes.Extension.exists_extension_subset`: clauses (i) and (ii).

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 22); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding
  (HasWeakGradOn hasWeakGradOn_univ_mul_cutoff hasWeakGradOn_finsetSum integrableOn_mul_bounded)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Shrinking an open ball around a compact subset.** -/
theorem exists_lt_radius_of_isCompact_subset_ball {K : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) (hK : IsCompact K)
    (hKR : K ⊆ ball x R) : ∃ r, r < R ∧ 0 < r ∧ K ⊆ ball x r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R / 2, by linarith, by linarith, by simp⟩
  · obtain ⟨y, hyK, hy⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
    have hyR : dist y x < R := mem_ball.mp (hKR hyK)
    refine ⟨(dist y x + R) / 2, by linarith, by
      have : 0 ≤ dist y x := dist_nonneg
      linarith, fun z hz => ?_⟩
    have hle : dist z x ≤ dist y x := hy hz
    exact mem_ball.mpr (by linarith)

private theorem intMul {B : Set (EuclideanSpace ℝ (Fin d))}
    {w h : EuclideanSpace ℝ (Fin d) → ℝ} (hw : IntegrableOn w B volume) (hcs : HasCompactSupport h)
    (hc : Continuous h) : IntegrableOn (fun x => h x * w x) B volume := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  exact (integrableOn_mul_bounded hw hc hC).congr
    (Filter.Eventually.of_forall fun x => mul_comm (w x) (h x))

/-- **One bound for a smooth compactly supported factor and for each of its partials.** The
product rule against a piece of the partition uses both, and a single number bounds them. -/
private theorem exists_bound_with_partials {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) h) (hcs : HasCompactSupport h) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y, ‖h y‖ ≤ C) ∧ ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k h y‖ ≤ C := by
  classical
  have hpc : ∀ k : Fin d, Continuous (partialD k h) := fun k =>
    (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : ∀ k : Fin d, HasCompactSupport (partialD k h) := fun k =>
    hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  obtain ⟨C₀, hC₀⟩ := hcs.exists_bound_of_continuous hc.continuous
  choose Ck hCk using fun k => (hpcs k).exists_bound_of_continuous (hpc k)
  have hC₀0 : (0 : ℝ) ≤ C₀ := (norm_nonneg _).trans (hC₀ 0)
  have hCk0 : ∀ k, (0 : ℝ) ≤ Ck k := fun k => (norm_nonneg _).trans (hCk k 0)
  have hsum0 : (0 : ℝ) ≤ ∑ k, Ck k := Finset.sum_nonneg fun k _ => hCk0 k
  refine ⟨C₀ + ∑ k, Ck k, by linarith, fun y => (hC₀ y).trans (by linarith), fun k y => ?_⟩
  have h1 : Ck k ≤ ∑ j, Ck j :=
    Finset.single_le_sum (f := fun j => Ck j) (fun j _ => hCk0 j) (Finset.mem_univ k)
  exact (hCk k y).trans (by linarith)

/-! ### The partition, the radii and the pieces, all fixed by the domain -/

/-- A boundary piece of the partition is supported in its chart's ball, hence compactly. -/
theorem hasCompactSupport_part_some {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (P : BoundaryPartition d Ω) (x : {x // x ∈ P.centres}) :
    HasCompactSupport (P.part (some x)) :=
  (isCompact_closedBall (x : EuclideanSpace ℝ (Fin d)) (P.chart x).radius).of_isClosed_subset
    (isClosed_tsupport _) ((P.part_boundary x).trans ball_subset_closedBall)

/-- The ball the local extension of a boundary piece is taken on: strictly inside the chart's,
and still containing the support of the piece. Chosen from the partition alone. -/
def pieceRadius {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (x : {x // x ∈ P.centres}) : ℝ :=
  (exists_lt_radius_of_isCompact_subset_ball (P.chart x).radius_pos
    (hasCompactSupport_part_some P x) (P.part_boundary x)).choose

/-- What `pieceRadius` was chosen for. -/
theorem pieceRadius_spec {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (x : {x // x ∈ P.centres}) :
    pieceRadius P x < (P.chart x).radius ∧ 0 < pieceRadius P x ∧
      tsupport (P.part (some x)) ⊆ ball (x : EuclideanSpace ℝ (Fin d)) (pieceRadius P x) :=
  (exists_lt_radius_of_isCompact_subset_ball (P.chart x).radius_pos
    (hasCompactSupport_part_some P x) (P.part_boundary x)).choose_spec

/-- The chosen ball sits strictly inside the chart's. -/
theorem pieceRadius_lt {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (x : {x // x ∈ P.centres}) : pieceRadius P x < (P.chart x).radius :=
  (pieceRadius_spec P x).1

/-- The chosen ball still contains the support of the piece. -/
theorem tsupport_part_subset_pieceRadius {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (P : BoundaryPartition d Ω) (x : {x // x ∈ P.centres}) :
    tsupport (P.part (some x)) ⊆ ball (x : EuclideanSpace ℝ (Fin d)) (pieceRadius P x) :=
  (pieceRadius_spec P x).2.2

/-- **One piece of the glued extension.** The interior piece is the class extended by zero and
cut down by its piece of the partition; a boundary piece is the local extension of its chart,
cut down the same way. The cutoff comes after the extension, which is what makes the piece
agree with `Pᵢ u` on the domain. -/
def extPiece {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (i : Option {x // x ∈ P.centres}) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  match i with
  | none => fun y => P.part none y * Ω.indicator u y
  | some x => fun y => P.part (some x) y *
      (ball (x : EuclideanSpace ℝ (Fin d)) (pieceRadius P x)).indicator
        (localExt (P.chart x) x (pieceRadius_lt P x) u) y

/-- **Gradient of one piece**, with the product rule's second term. -/
def extPieceGrad {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (i : Option {x // x ∈ P.centres}) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  match i with
  | none => fun y => P.part none y * Ω.indicator (g k) y
      + partialD k (P.part none) y * Ω.indicator u y
  | some x => fun y => P.part (some x) y *
      (ball (x : EuclideanSpace ℝ (Fin d)) (pieceRadius P x)).indicator
        (localExtGrad (P.chart x) x (pieceRadius_lt P x) u g k) y
      + partialD k (P.part (some x)) y *
        (ball (x : EuclideanSpace ℝ (Fin d)) (pieceRadius P x)).indicator
          (localExt (P.chart x) x (pieceRadius_lt P x) u) y

/-- **Glued extension.** The pieces add to the class on the domain because the partition
adds to one there. -/
def extFun {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => ∑ i, extPiece P i u y

/-- **Gradient of the glued extension.** -/
def extFunGrad {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => ∑ i, extPieceGrad P i u g k y

/-- **Guo's third step with its constant** (Theorem III.2.2, proof step 3, p. 22): the local
extensions glued with the partition of unity extend the class across the whole boundary, and one
constant, taken before the class, bounds the extension and its gradient by the class and its
gradient over the domain. -/
theorem extension_bound {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (P : BoundaryPartition d Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
        HasWeakGradOn Set.univ (extFun P u) (extFunGrad P u g) ∧
          Integrable (extFun P u) volume ∧
          (∀ k, Integrable (extFunGrad P u g k) volume) ∧
          (∀ y ∈ Ω, extFun P u y = u y) ∧
          eLpNorm (extFun P u) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (extFunGrad P u g k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  classical
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hpiece : ∀ i : Option {x // x ∈ P.centres}, ∃ Ki : ℝ≥0,
      ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
          HasWeakGradOn Set.univ (extPiece P i u) (extPieceGrad P i u g) ∧
            Integrable (extPiece P i u) volume ∧
            (∀ k, Integrable (extPieceGrad P i u g k) volume) ∧
            (∀ y ∈ Ω, extPiece P i u y = P.part i y * u y) ∧
            eLpNorm (extPiece P i u) p volume ≤ (Ki : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) ∧
            ∀ k, eLpNorm (extPieceGrad P i u g k) p volume
              ≤ (Ki : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
                + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) := by
    rintro (_ | x)
    · -- The interior piece, applied to the class extended by zero.
      have hcs : HasCompactSupport (P.part none) :=
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset
          (isClosed_tsupport _) (P.part_interior.trans hRb)
      have hpc : Continuous (P.part none) := (P.part_contDiff none).continuous
      have hpd : ∀ k : Fin d, Continuous (partialD k (P.part none)) := fun k =>
        ((P.part_contDiff none).continuous_fderiv (by simp)).clm_apply continuous_const
      have hpdcs : ∀ k : Fin d, HasCompactSupport (partialD k (P.part none)) := fun k =>
        hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
      obtain ⟨C, hC0, hCb, hCd⟩ := exists_bound_with_partials (P.part_contDiff none) hcs
      refine ⟨Real.toNNReal C, fun u g hu hgi hwg => ?_⟩
      have hcoe : ((Real.toNNReal C : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal C := rfl
      have hiu : IntegrableOn (Ω.indicator u) Set.univ volume :=
        (hu.integrable_indicator hΩopen.measurableSet).integrableOn
      have hig : ∀ k, IntegrableOn (Ω.indicator (g k)) Set.univ volume := fun k =>
        ((hgi k).integrable_indicator hΩopen.measurableSet).integrableOn
      have hind : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ,
          eLpNorm (Ω.indicator w) p volume = eLpNorm w p (volume.restrict Ω) := fun w =>
        eLpNorm_indicator_eq_eLpNorm_restrict hΩopen.measurableSet
      simp only [extPiece, extPieceGrad]
      refine ⟨hasWeakGradOn_univ_mul_cutoff hΩopen.measurableSet (P.part_contDiff none) hcs
          P.part_interior hu hgi hwg,
        integrableOn_univ.mp (intMul hiu hcs hpc),
        fun k => integrableOn_univ.mp ((intMul (hig k) hcs hpc).add (intMul hiu (hpdcs k) (hpd k))),
        ?_, ?_, ?_⟩
      · intro y hy
        rw [Set.indicator_of_mem hy]
      · rw [hcoe]
        calc eLpNorm (fun y => P.part none y * Ω.indicator u y) p volume
            ≤ ENNReal.ofReal C * eLpNorm (Ω.indicator u) p volume :=
              eLpNorm_bounded_mul_le hC0 hCb
                (integrableOn_univ.mp (intMul hiu hcs hpc)).1
          _ ≤ ENNReal.ofReal C * (eLpNorm u p (volume.restrict Ω)
              + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) := by
              rw [hind]
              exact mul_le_mul_right le_self_add _
      · intro k
        rw [hcoe]
        have hm1 : AEStronglyMeasurable
            (fun y => P.part none y * Ω.indicator (g k) y) volume :=
          (integrableOn_univ.mp (intMul (hig k) hcs hpc)).1
        have hm2 : AEStronglyMeasurable
            (fun y => partialD k (P.part none) y * Ω.indicator u y) volume :=
          (integrableOn_univ.mp (intMul hiu (hpdcs k) (hpd k))).1
        calc eLpNorm (fun y => P.part none y * Ω.indicator (g k) y
                + partialD k (P.part none) y * Ω.indicator u y) p volume
            ≤ eLpNorm (fun y => P.part none y * Ω.indicator (g k) y) p volume
              + eLpNorm (fun y => partialD k (P.part none) y * Ω.indicator u y) p volume :=
              eLpNorm_add_le hp
          _ ≤ ENNReal.ofReal C * eLpNorm (Ω.indicator (g k)) p volume
              + ENNReal.ofReal C * eLpNorm (Ω.indicator u) p volume :=
              add_le_add (eLpNorm_bounded_mul_le hC0 hCb hm1)
                (eLpNorm_bounded_mul_le hC0 (hCd k) hm2)
          _ ≤ ENNReal.ofReal C * (eLpNorm u p (volume.restrict Ω)
              + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) := by
              have hgk : eLpNorm (g k) p (volume.restrict Ω)
                  ≤ ∑ j, eLpNorm (g j) p (volume.restrict Ω) :=
                Finset.single_le_sum (f := fun j => eLpNorm (g j) p (volume.restrict Ω))
                  (fun _ _ => zero_le) (Finset.mem_univ k)
              rw [hind, hind, ← mul_add]
              refine mul_le_mul_right ?_ _
              calc eLpNorm (g k) p (volume.restrict Ω) + eLpNorm u p (volume.restrict Ω)
                  ≤ (∑ j, eLpNorm (g j) p (volume.restrict Ω))
                    + eLpNorm u p (volume.restrict Ω) := add_le_add_left hgk _
                _ = eLpNorm u p (volume.restrict Ω)
                    + ∑ j, eLpNorm (g j) p (volume.restrict Ω) := add_comm _ _
    · -- A boundary piece, applied to the local extension of its chart.
      have hcs : HasCompactSupport (P.part (some x)) :=
        (isCompact_closedBall (x : EuclideanSpace ℝ (Fin d)) (P.chart x).radius).of_isClosed_subset
          (isClosed_tsupport _) ((P.part_boundary x).trans ball_subset_closedBall)
      set r : ℝ := pieceRadius P x with hrdef
      have hrlt : r < (P.chart x).radius := pieceRadius_lt P x
      have hrsub : tsupport (P.part (some x)) ⊆ ball (x : EuclideanSpace ℝ (Fin d)) r :=
        tsupport_part_subset_pieceRadius P x
      obtain ⟨Kx, hKx⟩ := localExtension_bound (P.chart x) hΩopen.measurableSet
        (P.chart_fits x x.2) hrlt hp
      have hpc : Continuous (P.part (some x)) := (P.part_contDiff (some x)).continuous
      have hpd : ∀ k : Fin d, Continuous (partialD k (P.part (some x))) := fun k =>
        ((P.part_contDiff (some x)).continuous_fderiv (by simp)).clm_apply continuous_const
      have hpdcs : ∀ k : Fin d, HasCompactSupport (partialD k (P.part (some x))) := fun k =>
        hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
      obtain ⟨C, hC0, hCb, hCd⟩ := exists_bound_with_partials (P.part_contDiff (some x)) hcs
      refine ⟨(Real.toNNReal C + Real.toNNReal C) * Kx, fun u g hu hgi hwg => ?_⟩
      have hcoe : (((Real.toNNReal C + Real.toNNReal C) * Kx : ℝ≥0) : ℝ≥0∞)
          = (ENNReal.ofReal C + ENNReal.ofReal C) * (Kx : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ENNReal.coe_add]; rfl
      obtain ⟨hUxwg, hUxint, hGxint, hUxag, hUxb, hGxb⟩ := hKx u g hu hgi hwg
      set Ux : EuclideanSpace ℝ (Fin d) → ℝ := localExt (P.chart x) x hrlt u with hUxdef
      set Gx : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
        localExtGrad (P.chart x) x hrlt u g with hGxdef
      have hUxOn : IntegrableOn Ux (ball (x : EuclideanSpace ℝ (Fin d)) r) volume :=
        MeasureTheory.Integrable.integrableOn hUxint
      have hGxOn : ∀ k, IntegrableOn (Gx k) (ball (x : EuclideanSpace ℝ (Fin d)) r) volume :=
        fun k => MeasureTheory.Integrable.integrableOn (hGxint k)
      have hiu : IntegrableOn ((ball (x : EuclideanSpace ℝ (Fin d)) r).indicator Ux)
          Set.univ volume :=
        integrableOn_univ.mpr ((integrable_indicator_iff measurableSet_ball).mpr hUxOn)
      have hig : ∀ k, IntegrableOn
          ((ball (x : EuclideanSpace ℝ (Fin d)) r).indicator (Gx k)) Set.univ volume := fun k =>
        integrableOn_univ.mpr ((integrable_indicator_iff measurableSet_ball).mpr (hGxOn k))
      -- the indicator leaves the seminorm alone
      have hind : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ,
          eLpNorm ((ball (x : EuclideanSpace ℝ (Fin d)) r).indicator w) p volume
            ≤ eLpNorm w p volume := by
        intro w
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
        exact eLpNorm_mono_measure _ Measure.restrict_le_self
      simp only [extPiece, extPieceGrad, ← hrdef, ← hUxdef, ← hGxdef]
      refine ⟨hasWeakGradOn_univ_mul_cutoff measurableSet_ball (P.part_contDiff (some x)) hcs
          hrsub hUxOn hGxOn hUxwg,
        integrableOn_univ.mp (intMul hiu hcs hpc),
        fun k => integrableOn_univ.mp ((intMul (hig k) hcs hpc).add (intMul hiu (hpdcs k) (hpd k))),
        ?_, ?_, ?_⟩
      · intro y hy
        by_cases hyb : y ∈ ball (x : EuclideanSpace ℝ (Fin d)) r
        · rw [Set.indicator_of_mem hyb, hUxag y ⟨hy, hyb⟩]
        · rw [Set.indicator_of_notMem hyb,
            image_eq_zero_of_notMem_tsupport (fun hc => hyb (hrsub hc)), zero_mul, zero_mul]
      · rw [hcoe, mul_assoc]
        refine le_trans (eLpNorm_bounded_mul_le hC0 hCb
          (integrableOn_univ.mp (intMul hiu hcs hpc)).1) ?_
        refine le_trans (mul_le_mul_right ((hind Ux).trans hUxb) (ENNReal.ofReal C)) ?_
        exact mul_le_mul_left le_self_add _
      · intro k
        rw [hcoe, mul_assoc]
        have hm1 : AEStronglyMeasurable (fun y => P.part (some x) y
            * (ball (x : EuclideanSpace ℝ (Fin d)) r).indicator (Gx k) y) volume :=
          (integrableOn_univ.mp (intMul (hig k) hcs hpc)).1
        have hm2 : AEStronglyMeasurable (fun y => partialD k (P.part (some x)) y
            * (ball (x : EuclideanSpace ℝ (Fin d)) r).indicator Ux y) volume :=
          (integrableOn_univ.mp (intMul hiu (hpdcs k) (hpd k))).1
        refine le_trans (eLpNorm_add_le hp) ?_
        refine le_trans (add_le_add (eLpNorm_bounded_mul_le hC0 hCb hm1)
          (eLpNorm_bounded_mul_le hC0 (hCd k) hm2)) ?_
        refine le_trans (add_le_add (mul_le_mul_right ((hind (Gx k)).trans (hGxb k)) _)
          (mul_le_mul_right ((hind Ux).trans hUxb) _)) ?_
        rw [add_mul]
  choose Ki hKi using hpiece
  refine ⟨∑ i, Ki i, ?_⟩
  intro u g hu hgi hwg
  have hwgi : ∀ i, HasWeakGradOn Set.univ (extPiece P i u) (extPieceGrad P i u g) :=
    fun i => (hKi i u g hu hgi hwg).1
  have hint : ∀ i, Integrable (extPiece P i u) volume :=
    fun i => (hKi i u g hu hgi hwg).2.1
  have hgint : ∀ i k, Integrable (extPieceGrad P i u g k) volume :=
    fun i => (hKi i u g hu hgi hwg).2.2.1
  have hag : ∀ i, ∀ y ∈ Ω, extPiece P i u y = P.part i y * u y :=
    fun i => (hKi i u g hu hgi hwg).2.2.2.1
  have hUb : ∀ i, eLpNorm (extPiece P i u) p volume ≤ (Ki i : ℝ≥0∞)
      * (eLpNorm u p (volume.restrict Ω) + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) :=
    fun i => (hKi i u g hu hgi hwg).2.2.2.2.1
  have hGb : ∀ i k, eLpNorm (extPieceGrad P i u g k) p volume ≤ (Ki i : ℝ≥0∞)
      * (eLpNorm u p (volume.restrict Ω) + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) :=
    fun i => (hKi i u g hu hgi hwg).2.2.2.2.2
  have hsumfun : ∀ w : Option {x // x ∈ P.centres} → EuclideanSpace ℝ (Fin d) → ℝ,
      (fun y => ∑ i, w i y) = ∑ i, w i := by
    intro w
    funext y
    rw [Finset.sum_apply]
  have hbound : ∀ w : Option {x // x ∈ P.centres} → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, AEStronglyMeasurable (w i) volume) →
      (∀ i, eLpNorm (w i) p volume ≤ (Ki i : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
        + ∑ j, eLpNorm (g j) p (volume.restrict Ω))) →
      eLpNorm (fun y => ∑ i, w i y) p volume
        ≤ ((∑ i, Ki i : ℝ≥0) : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
          + ∑ j, eLpNorm (g j) p (volume.restrict Ω)) := by
    intro w hwm hwb
    rw [hsumfun w]
    refine le_trans (eLpNorm_sum_le hp) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => hwb i) ?_
    rw [← Finset.sum_mul, ENNReal.ofNNReal_finsetSum]
  simp only [extFun]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hasWeakGradOn_finsetSum Finset.univ (fun i _ => (hint i).integrableOn)
      (fun i _ k => (hgint i k).integrableOn) (fun i _ => hwgi i)
  · exact MeasureTheory.integrable_finsetSum _ fun i _ => hint i
  · exact fun k => MeasureTheory.integrable_finsetSum _ fun i _ => hgint i k
  · intro y hy
    calc (∑ i, extPiece P i u y) = ∑ i, P.part i y * u y :=
          Finset.sum_congr rfl fun i _ => hag i y hy
      _ = (∑ i, P.part i y) * u y := (Finset.sum_mul _ _ _).symm
      _ = u y := by rw [P.part_sum y (subset_closure hy), one_mul]
  · exact hbound (fun i => extPiece P i u) (fun i => (hint i).1) hUb
  · exact fun k => hbound (fun i => extPieceGrad P i u g k)
      (fun i => (hgint i k).1) (fun i => hGb i k)

/-- **Guo's third step with its constant**, with the partition and the extension quantified
away. This is the form the support clause and the embedding consume. -/
theorem exists_extension_bound (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn Set.univ U G ∧ Integrable U volume ∧
          (∀ k, Integrable (G k) volume) ∧ (∀ y ∈ Ω, U y = u y) ∧
          eLpNorm U p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (G k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨K, hK⟩ := extension_bound hΩopen hΩb P hp
  refine ⟨K, fun u g hu hgi hwg => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hK u g hu hgi hwg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩

/-- **Guo's third step** (Theorem III.2.2, proof step 3, p. 22): the local extensions glued with
the partition of unity extend the class across the whole boundary. -/
theorem exists_extension (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn Set.univ U G ∧ Integrable U volume ∧
        (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω, U y = u y := by
  obtain ⟨K, hK⟩ := exists_extension_bound hd hΩopen hΩb hC1 (p := 1) le_rfl
  obtain ⟨U, G, hwgU, hUint, hGint, hag, -, -⟩ := hK u g hu hgi hwg
  exact ⟨U, G, hwgU, hUint, hGint, hag⟩

/-- **Cutting between a compact set and an open one.** A smooth cutoff equal to one on the
compact set and compactly supported inside the open one. -/
theorem exists_cutoff_one_on_compact {K U : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ y ∈ K, χ y = 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
      (isOpen_interior (s := L)).isClosed_compl hK.isClosed
      (by
        rw [Set.disjoint_compl_left_iff_subset]
        exact hKL)
  have hsupp : tsupport (fun y => f y) ⊆ L := by
    refine closure_minimal ?_ hLc.isClosed
    intro y hy
    by_contra hc
    exact hy (hf0 fun hcc => hc (interior_subset hcc))
  exact ⟨fun y => f y, contMDiff_iff_contDiff.mp f.contMDiff,
    hLc.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hLU,
    fun y hy => hf1 hy⟩

/-- **Extension with its support cut into a given open set.** One more cutoff, equal to
one on the closure of the domain, which leaves the agreement alone and moves the support. -/
def extSubsetFun {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => χ y * extFun P u y

/-- **Gradient of that extension**, with the cutoff's own derivative. -/
def extSubsetGrad {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => χ y * extFunGrad P u g k y + partialD k χ y * extFun P u y

/-- `extSubsetFun` unapplied, which is the form the support statements read. -/
theorem extSubsetFun_eq {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    extSubsetFun P χ u = fun y => χ y * extFun P u y := rfl

/-- `extSubsetGrad` unapplied. -/
theorem extSubsetGrad_eq {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) :
    extSubsetGrad P χ u g k
      = fun y => χ y * extFunGrad P u g k y + partialD k χ y * extFun P u y := rfl

/-- **Guo's Theorem III.2.2** (p. 20), all three clauses. The extension agrees with the class on
the domain, is supported inside any open set the closure of the domain sits in, and is bounded
in every `Lᵖ` seminorm, together with its gradient, by the class and its gradient over the
domain, with one constant taken before the class. -/
theorem extension_subset_bound {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (P : BoundaryPartition d Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcs : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω')
    (hχ1 : ∀ y ∈ closure Ω, χ y = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
        HasWeakGradOn Set.univ (extSubsetFun P χ u) (extSubsetGrad P χ u g) ∧
          HasCompactSupport (extSubsetFun P χ u) ∧ tsupport (extSubsetFun P χ u) ⊆ Ω' ∧
          Integrable (extSubsetFun P χ u) volume ∧
          (∀ k, Integrable (extSubsetGrad P χ u g k) volume) ∧
          (∀ y ∈ Ω, extSubsetFun P χ u y = u y) ∧
          eLpNorm (extSubsetFun P χ u) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (extSubsetGrad P χ u g k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  classical
  obtain ⟨K₀, hK₀⟩ := extension_bound hΩopen hΩb P hp
  obtain ⟨C, hC0, hCb, hCd⟩ := exists_bound_with_partials hχc hχcs
  have hχpc : ∀ k : Fin d, Continuous (partialD k χ) := fun k =>
    (hχc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχpcs : ∀ k : Fin d, HasCompactSupport (partialD k χ) := fun k =>
    hχcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  refine ⟨(Real.toNNReal C + Real.toNNReal C) * K₀, fun u g hu hgi hwg => ?_⟩
  have hcoe : (((Real.toNNReal C + Real.toNNReal C) * K₀ : ℝ≥0) : ℝ≥0∞)
      = (ENNReal.ofReal C + ENNReal.ofReal C) * (K₀ : ℝ≥0∞) := by
    rw [ENNReal.coe_mul, ENNReal.coe_add]; rfl
  obtain ⟨hwg0, hint0, hgint0, hag0, hUb0, hGb0⟩ := hK₀ u g hu hgi hwg
  set U₀ : EuclideanSpace ℝ (Fin d) → ℝ := extFun P u with hU₀def
  set G₀ : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := extFunGrad P u g with hG₀def
  have hmul := hasWeakGradOn_univ_mul_cutoff (B := Set.univ) MeasurableSet.univ hχc hχcs
    (Set.subset_univ _) hint0.integrableOn (fun k => (hgint0 k).integrableOn) hwg0
  simp only [Set.indicator_univ] at hmul
  have hprod : ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ),
      Integrable w volume → HasCompactSupport h → Continuous h →
      Integrable (fun y => h y * w y) volume := by
    intro w h hw hcs hc
    obtain ⟨C', hC'⟩ := hcs.exists_bound_of_continuous hc
    exact integrableOn_univ.mp ((integrableOn_mul_bounded hw.integrableOn hc hC').congr
      (Filter.Eventually.of_forall fun y => mul_comm (w y) (h y)))
  have hsuppU : tsupport (fun y => χ y * U₀ y) ⊆ Ω' := by
    refine subset_trans (closure_mono ?_) hχs
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hc
    exact hy (by rw [hc, zero_mul])
  simp only [extSubsetFun_eq, extSubsetGrad_eq, ← hU₀def, ← hG₀def]
  refine ⟨hmul,
    hχcs.of_isClosed_subset (isClosed_tsupport _) ?_, hsuppU,
    hprod _ _ hint0 hχcs hχc.continuous,
    fun k => (hprod _ _ (hgint0 k) hχcs hχc.continuous).add
      (hprod _ _ hint0 (hχpcs k) (hχpc k)), ?_, ?_, ?_⟩
  · refine subset_trans (closure_mono ?_) subset_rfl
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hc
    exact hy (by rw [hc, zero_mul])
  · intro y hy
    rw [hχ1 y (subset_closure hy), one_mul, hag0 y hy]
  · rw [hcoe, mul_assoc]
    refine le_trans (eLpNorm_bounded_mul_le hC0 hCb
      (hprod _ _ hint0 hχcs hχc.continuous).1) ?_
    refine le_trans (mul_le_mul_right hUb0 (ENNReal.ofReal C)) ?_
    exact mul_le_mul_left le_self_add _
  · intro k
    rw [hcoe, mul_assoc]
    have hm1 : AEStronglyMeasurable (fun y => χ y * G₀ k y) volume :=
      (hprod _ _ (hgint0 k) hχcs hχc.continuous).1
    have hm2 : AEStronglyMeasurable (fun y => partialD k χ y * U₀ y) volume :=
      (hprod _ _ hint0 (hχpcs k) (hχpc k)).1
    refine le_trans (eLpNorm_add_le hp) ?_
    refine le_trans (add_le_add (eLpNorm_bounded_mul_le hC0 hCb hm1)
      (eLpNorm_bounded_mul_le hC0 (hCd k) hm2)) ?_
    refine le_trans (add_le_add (mul_le_mul_right (hGb0 k) _)
      (mul_le_mul_right hUb0 _)) ?_
    rw [add_mul]

/-- **Guo's Theorem III.2.2** (p. 20), all three clauses, with the partition, the cutoff and
the extension quantified away. -/
theorem exists_extension_subset_bound (hd : 0 < d) {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω') {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn Set.univ U G ∧ HasCompactSupport U ∧ tsupport U ⊆ Ω' ∧
          Integrable U volume ∧ (∀ k, Integrable (G k) volume) ∧ (∀ y ∈ Ω, U y = u y) ∧
          eLpNorm U p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (G k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hclc : IsCompact (closure Ω) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset isClosed_closure
      (closure_minimal hRb (isClosed_closedBall))
  obtain ⟨χ, hχc, hχcs, hχs, hχ1⟩ := exists_cutoff_one_on_compact hclc hΩ'open hsub
  obtain ⟨K, hK⟩ := extension_subset_bound hΩopen hΩb P hχc hχcs hχs hχ1 hp
  refine ⟨K, fun u g hu hgi hwg => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hK u g hu hgi hwg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **Clauses (i) and (ii) of Guo's Theorem III.2.2** (p. 20). The extension agrees with the class
on the domain and is supported inside any open set the closure of the domain sits in. -/
theorem exists_extension_subset (hd : 0 < d) {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn Set.univ U G ∧ HasCompactSupport U ∧ tsupport U ⊆ Ω' ∧
        Integrable U volume ∧ (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω, U y = u y := by
  obtain ⟨K, hK⟩ :=
    exists_extension_subset_bound hd hΩopen hΩb hC1 hΩ'open hsub (p := 1) le_rfl
  obtain ⟨U, G, hwgU, hcsU, hsuppU, hUint, hGint, hag, -, -⟩ := hK u g hu hgi hwg
  exact ⟨U, G, hwgU, hcsU, hsuppU, hUint, hGint, hag⟩

end EllipticPdes.Extension
