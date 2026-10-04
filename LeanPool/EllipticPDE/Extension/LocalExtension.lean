/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.PartitionOfUnity
public import LeanPool.EllipticPDE.Extension.Patch
public import LeanPool.EllipticPDE.Extension.Motion
public import LeanPool.EllipticPDE.Extension.Linearity


/-!
# Local boundary extension

Guo's Theorem III.2.2 reaches its third step with a local extension for each chart: a class on
the chart's neighbourhood agreeing with the original on the part of the domain that
neighbourhood meets. This file proves that statement, which is the whole content of his step 2
once the chart is in hand.

The proof composes what the chapter has built. A cutoff between two balls makes the class reach
the whole region above the chart's graph, the rigid motion of the chart takes it into the
coordinates the graph is written in, the reflection extends it across the graph, and the motion
takes the result back. Guo's step 2 works with a function smooth up to the boundary and reads
the chain rule off it; here every step is a weak gradient.

Two points where the statement is narrower than the machinery. The chart asks nothing of the
gradient of its graph, as Evans' definition does not, so the proof runs on the bounded graph
`exists_bounded_graph` supplies, whose region agrees with the chart's on exactly the ball in
play. The conclusion is on a ball strictly inside the chart's, which is where the cutoff is one,
and is what a partition of unity subordinate to the cover asks for anyway.

## Constant before the class

Clause (iii) of the theorem asks for a constant quantified before the class, and the chain the
construction runs through re-chooses data at three places: the bounded graph of
`exists_bounded_graph`, the cutoff between the two balls, and the bound each supplies. All three
depend on the chart and the two radii alone, so `exists_localExtension_bound` fixes them first
and lets the class come after. The bound then threads the five estimates the chain has: the
cutoff's supremum, the rigid motion, the reflection, the shear, and the sum over the coordinates
the motion mixes.

## Main declarations

* `EllipticPdes.Extension.exists_localExtension_bound`: the local boundary extension with a
  constant fixed before the class.
* `EllipticPdes.Extension.exists_localExtension`: the same with the constant discarded.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### Two seminorm estimates the chain threads -/

/-- **Seminorm of a coordinate combination.** A combination of finitely many classes whose
coefficients are at most one in absolute value has seminorm at most the sum of theirs. This is
what the rigid motion of a chart contributes, the coordinates of the image of a unit direction
being at most one. -/
theorem eLpNorm_sum_coord_le {p : ℝ≥0∞} (hp : 1 ≤ p)
    {μ : Measure (EuclideanSpace ℝ (Fin d))} {a : Fin d → ℝ} (ha : ∀ i, |a i| ≤ 1)
    {w : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hw : ∀ i, AEStronglyMeasurable (w i) μ) :
    eLpNorm (fun y => ∑ i, a i * w i y) p μ ≤ ∑ i, eLpNorm (w i) p μ := by
  have hfun : (fun y => ∑ i, a i * w i y) = ∑ i, fun y => a i * w i y := by
    funext y
    rw [Finset.sum_apply]
  rw [hfun]
  refine le_trans (eLpNorm_sum_le hp)
    (Finset.sum_le_sum fun i _ => ?_)
  refine eLpNorm_mono_ae ((hw i).const_mul _) (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs (a i)]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha i)

/-- **Seminorm of a class cut off inside a neighbourhood.** The cutoff vanishes off `W`, and on
`S ∩ W` the class is read on `T`, so the product over `S` is bounded by the supremum of the
cutoff against the seminorm over `T`. This is what lets an estimate taken over the region above
a chart's graph be stated against the domain. -/
theorem eLpNorm_mul_cutoff_le {S W T : Set (EuclideanSpace ℝ (Fin d))}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    {ξ v : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖ξ y‖ ≤ C)
    (hoff : ∀ y, y ∉ W → ξ y = 0) (hSW : S ∩ W ⊆ T) {p : ℝ≥0∞}
    (hξv : AEStronglyMeasurable (fun y => ξ y * v y) (volume.restrict S)) :
    eLpNorm (fun y => ξ y * v y) p (volume.restrict S)
      ≤ ENNReal.ofReal C * eLpNorm v p (volume.restrict T) := by
  have hptwise : ∀ y, y ∈ S → ‖ξ y * v y‖ ≤ ‖(C • T.indicator v) y‖ := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hyT : y ∈ T := hSW ⟨hy, hyW⟩
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hyT, norm_mul,
        Real.norm_eq_abs C, abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
    · rw [hoff y hyW, zero_mul, norm_zero]
      exact norm_nonneg _
  calc eLpNorm (fun y => ξ y * v y) p (volume.restrict S)
      ≤ eLpNorm (C • T.indicator v) p (volume.restrict S) :=
        eLpNorm_mono_ae hξv
          ((ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall hptwise))
    _ = ENNReal.ofReal C * eLpNorm (T.indicator v) p (volume.restrict S) := by
        rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC0]
    _ ≤ ENNReal.ofReal C * eLpNorm (T.indicator v) p volume :=
        mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _
    _ = ENNReal.ofReal C * eLpNorm v p (volume.restrict T) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hT]

/-- **Seminorm of a class scaled by a bounded factor**, the factor written first. -/
theorem eLpNorm_bounded_mul_le {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {h v : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖h y‖ ≤ C)
    {p : ℝ≥0∞} (hhv : AEStronglyMeasurable (fun y => h y * v y) μ) :
    eLpNorm (fun y => h y * v y) p μ ≤ ENNReal.ofReal C * eLpNorm v p μ := by
  have heq : (fun y => h y * v y) = fun y => v y * h y := by
    funext y
    exact mul_comm _ _
  rw [heq] at hhv ⊢
  exact eLpNorm_mul_bounded_le hC0 hC hhv

/-! ### The local extension -/

/-- **Local extension as a formula in the class.** The class is read in the chart's
coordinates, cut off there, extended across the flattened boundary, and returned. Every step
but the class itself is fixed by the chart, its graph `γ` and the cutoff `ξ`, so the whole is
linear in the class. -/
def localExtFun (c : C1Chart d) (γ ξ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => chartExt c.dir γ
    (fun z => ξ (c.motion.symm z) * u (c.motion.symm z)) (c.motion y)

/-- **Gradient of the local extension.** The cutoff contributes its own derivative by the
product rule, the chart's rigid motion mixes the coordinates on the way in and on the way
out, and the shear and the reflection supply the rest. -/
def localExtGradFun (c : C1Chart d) (γ ξ u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => ∑ i, c.motion (EuclideanSpace.single k (1 : ℝ)) i *
    chartExtGrad c.dir γ
      (fun k' z => ∑ i', c.motion.symm (EuclideanSpace.single k' (1 : ℝ)) i' *
        (ξ (c.motion.symm z) * g i' (c.motion.symm z)
          + partialD i' ξ (c.motion.symm z) * u (c.motion.symm z))) i (c.motion y)


/-- The bounded graph the chart's extension runs on. A chart's own graph need not have a
bounded gradient, which every statement about the shear asks for, and `exists_bounded_graph`
supplies one agreeing with it on the chart's ball. The choice is made from the chart alone,
before any class appears, which is what keeps the extension linear. -/
def chartGraph (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  (exists_bounded_graph c.graph_contDiff c.graph_indep (c.motion x) c.radius_pos).choose

/-- What `chartGraph` was chosen for. -/
theorem chartGraph_spec (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ M : ℝ, ContDiff ℝ 1 (chartGraph c x) ∧ IndepCoord c.dir (chartGraph c x) ∧
      (∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
        ‖partialD k (chartGraph c x) y‖ ≤ M) ∧
      aboveGraph c.dir (chartGraph c x) ∩ ball (c.motion x) c.radius
        = aboveGraph c.dir c.graph ∩ ball (c.motion x) c.radius :=
  (exists_bounded_graph c.graph_contDiff c.graph_indep (c.motion x) c.radius_pos).choose_spec

/-- The cutoff between the ball the extension is asked for and the chart's own. Chosen from
the two radii alone, before any class appears. -/
def chartCutoff (x : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hrR : r < R) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  (exists_cutoff_one_on_ball x hrR).choose

/-- What `chartCutoff` was chosen for. -/
theorem chartCutoff_spec (x : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (chartCutoff x hrR) ∧
      (∀ y ∈ closedBall x r, chartCutoff x hrR y = 1) ∧
      tsupport (chartCutoff x hrR) ⊆ ball x R :=
  (exists_cutoff_one_on_ball x hrR).choose_spec

/-- **Local extension of a class.** `localExtFun` at the graph and the cutoff the chart
fixes, so the only argument left is the class. -/
def localExt (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hrc : r < c.radius)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  localExtFun c (chartGraph c x) (chartCutoff x hrc) u

/-- **Gradient of the local extension of a class.** -/
def localExtGrad (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hrc : r < c.radius)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
  localExtGradFun c (chartGraph c x) (chartCutoff x hrc) u g

private lemma chart_gradient_bound : ∀ {d : ℕ} (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin
  d))} {x : EuclideanSpace ℝ (Fin d)}
  {r : ℝ} (hrc : r < c.radius) {p : ℝ≥0∞} (_ : 1 ≤ p),
  let γ := chartGraph c x;
  let A := aboveGraph c.dir γ;
  let A' := ⇑c.motion ⁻¹' A;
  let ξ := chartCutoff x hrc;
  ∀ (Cξ : ℝ) (Cd : (k : Fin d) → ℝ),
    let B := Cξ + ∑ k, Cd k;
    ∀ (_ : MeasurePreserving (⇑c.motion.symm) (volume.restrict A) (volume.restrict A'))
      (_ : ∀ (k i : Fin d), |(c.motion.symm (EuclideanSpace.single k 1)).ofLp i| ≤ 1)
      (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      let N := eLpNorm u p (volume.restrict Ω) + ∑ i, eLpNorm (g i) p (volume.restrict Ω);
      ∀ (_ : N = eLpNorm u p (volume.restrict Ω) + ∑ i, eLpNorm (g i) p (volume.restrict Ω))
        (_ : ∀ (k : Fin d), IntegrableOn (fun y => ξ y * g k y + partialD k ξ y * u y) A' volume),
        let H := fun k y =>
          ∑ i,
            (c.motion.symm (EuclideanSpace.single k 1)).ofLp i *
              (ξ (c.motion.symm y) * g i (c.motion.symm y) + partialD i ξ (c.motion.symm y) * u
                (c.motion.symm y));
        ∀
          (_ :
            ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ),
              IntegrableOn w A' volume → IntegrableOn (fun y => w (c.motion.symm y)) A volume)
          (_ :
            ∀ (i : Fin d),
              eLpNorm (fun y => ξ y * g i y + partialD i ξ y * u y) p (volume.restrict A') ≤
                ENNReal.ofReal B * eLpNorm (g i) p (volume.restrict Ω) +
                  ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω))
          (k : Fin d), eLpNorm (H k) p (volume.restrict A) ≤ ENNReal.ofReal B * (↑d + 1) * N := by
  classical
  intro d c Ω x r hrc p hp γ A A' ξ Cξ Cd B hresS hcoordS u g N hNdef hIg H htrans hWA k
  have hmeasA : ∀ i : Fin d, AEStronglyMeasurable
      (fun y => (fun z => ξ z * g i z + partialD i ξ z * u z) (c.motion.symm y))
      (volume.restrict A) := fun i => (htrans _ (hIg i)).1
  have hstep := eLpNorm_sum_coord_le (p := p) hp (hcoordS k) hmeasA
  refine hstep.trans ?_
  have htr : ∀ i : Fin d,
      eLpNorm ((fun z => ξ z * g i z + partialD i ξ z * u z) ∘
          (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)))
          p (volume.restrict A)
        = eLpNorm (fun z => ξ z * g i z + partialD i ξ z * u z) p (volume.restrict A') :=
    fun i => eLpNorm_comp_measurePreserving (hIg i).1 hresS
  refine le_trans (Finset.sum_le_sum fun i _ => le_of_eq (htr i)) ?_
  calc ∑ i, eLpNorm (fun z => ξ z * g i z + partialD i ξ z * u z) p (volume.restrict A')
      ≤ ∑ _i : Fin d, (ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω)
          + ENNReal.ofReal B * ∑ j, eLpNorm (g j) p (volume.restrict Ω)) := by
        refine Finset.sum_le_sum fun i _ => (hWA i).trans ?_
        rw [add_comm]
        gcongr
        exact Finset.single_le_sum
          (f := fun j => eLpNorm (g j) p (volume.restrict Ω)) (fun _ _ => zero_le)
          (Finset.mem_univ i)
    _ = (d : ℝ≥0∞) * (ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω)
          + ENNReal.ofReal B * ∑ j, eLpNorm (g j) p (volume.restrict Ω)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N := by
        rw [hNdef]
        rw [show ENNReal.ofReal B * ((d : ℝ≥0∞) + 1)
            * (eLpNorm u p (volume.restrict Ω) + ∑ j, eLpNorm (g j) p (volume.restrict Ω))
          = (d : ℝ≥0∞) * (ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω)
              + ENNReal.ofReal B * ∑ j, eLpNorm (g j) p (volume.restrict Ω))
            + (ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω)
              + ENNReal.ofReal B * ∑ j, eLpNorm (g j) p (volume.restrict Ω)) from by ring]
        exact le_self_add


private lemma chart_function_bound {d : ℕ} (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))} {x
  : EuclideanSpace ℝ (Fin d)}
  {r : ℝ} (hrc : r < c.radius) {p : ℝ≥0∞} (hp : 1 ≤ p) (M : ℝ) :
  let γ := chartGraph c x;
  ∀ (_ : IndepCoord c.dir γ),
    let A := aboveGraph c.dir γ;
    let ξ := chartCutoff x hrc;
    ∀ (Cξ : ℝ) (Cd : (k : Fin d) → ℝ),
      let B := Cξ + ∑ k, Cd k;
      ∀ (_ : Differentiable ℝ γ) (_ : MeasurePreserving (⇑c.motion) volume volume),
        let Kre := 2 * ENNReal.ofReal B + ↑d * (2 + 4 * ENNReal.ofReal M) * (ENNReal.ofReal B *
          (↑d + 1));
        ∀ (_ : Kre = 2 * ENNReal.ofReal B + ↑d * (2 + 4 * ENNReal.ofReal M) *
          (ENNReal.ofReal B * (↑d + 1)))
          (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
          let N := eLpNorm u p (volume.restrict Ω) + ∑ i, eLpNorm (g i) p (volume.restrict Ω);
          ∀ (_ : N = eLpNorm u p (volume.restrict Ω) + ∑ i, eLpNorm (g i) p (volume.restrict
            Ω)),
            let V := fun y => ξ (c.motion.symm y) * u (c.motion.symm y);
            ∀ (_ : IntegrableOn V A volume) (_ : Integrable (chartExt c.dir γ V) volume)
              (_ : eLpNorm V p (volume.restrict A) ≤ ENNReal.ofReal B * eLpNorm u p
                (volume.restrict Ω)),
              eLpNorm (chartExt c.dir γ V ∘ ⇑c.motion) p volume ≤ Kre * N := by
  classical
  intro γ hγind A ξ Cξ Cd B hγd hmpM Kre hKredef u g N hNdef V hVint hIext hVA
  have hmv : AEStronglyMeasurable (chartExt c.dir γ V) volume := hIext.1
  have h1 : eLpNorm (chartExt c.dir γ V ∘
        (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))) p volume
      = eLpNorm (chartExt c.dir γ V) p volume :=
    eLpNorm_comp_measurePreserving hmv hmpM
  rw [h1]
  refine le_trans (eLpNorm_chartExt_le hγd hγind hp hVint.1) ?_
  calc 2 * eLpNorm V p (volume.restrict A)
      ≤ 2 * (ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω)) := by gcongr
    _ ≤ 2 * ENNReal.ofReal B * N := by
        rw [mul_assoc]
        gcongr
        rw [hNdef]
        exact le_self_add
    _ ≤ Kre * N := by
        rw [hKredef]
        gcongr
        exact le_self_add


private lemma chart_extension_gradient_bound : ∀ {d : ℕ} (c : C1Chart d) {Ω : Set (EuclideanSpace
  ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
  {r : ℝ} (hrc : r < c.radius) {p : ℝ≥0∞} (_ : 1 ≤ p) (M : ℝ),
  let γ := chartGraph c x;
  ∀ (_ : ContDiff ℝ 1 γ) (_ : IndepCoord c.dir γ)
    (_ : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M) (_ : 0 ≤ M),
    let A := aboveGraph c.dir γ;
    let ξ := chartCutoff x hrc;
    ∀ (Cξ : ℝ) (Cd : (k : Fin d) → ℝ),
      let B := Cξ + ∑ k, Cd k;
      let Kre := 2 * ENNReal.ofReal B + ↑d * (2 + 4 * ENNReal.ofReal M) * (ENNReal.ofReal B * (↑d
        + 1));
      ∀ (_ : Kre = 2 * ENNReal.ofReal B + ↑d * (2 + 4 * ENNReal.ofReal M) * (ENNReal.ofReal
        B * (↑d + 1)))
        (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        let N := eLpNorm u p (volume.restrict Ω) + ∑ i, eLpNorm (g i) p (volume.restrict Ω);
        let H := fun k y =>
          ∑ i,
            (c.motion.symm (EuclideanSpace.single k 1)).ofLp i *
              (ξ (c.motion.symm y) * g i (c.motion.symm y) + partialD i ξ (c.motion.symm y) * u
                (c.motion.symm y));
        ∀ (_ : ∀ (k : Fin d), IntegrableOn (H k) A volume)
          (_ : ∀ (k : Fin d), Integrable (chartExtGrad c.dir γ H k) volume)
          (_ : ∀ (k : Fin d), eLpNorm (H k) p (volume.restrict A) ≤ ENNReal.ofReal B * (↑d + 1)
            * N) (k : Fin d),
          eLpNorm (fun y => ∑ i, (c.motion (EuclideanSpace.single k 1)).ofLp i * chartExtGrad
            c.dir γ H i (c.motion y))
              p volume ≤
            Kre * N := by
  classical
  intro d c Ω x r hrc p hp M γ hγC1 hγind hγb hM0 A ξ Cξ Cd B Kre hKredef u g N H hGint hIextG hHA k
  refine le_trans (eLpNorm_grad_comp_linearIsometry_le hp (fun i => (hIextG i).1) c.motion k) ?_
  have hstep : ∀ i : Fin d, eLpNorm (chartExtGrad c.dir γ H i) p volume
      ≤ (2 + 4 * ENNReal.ofReal M) * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N) := by
    intro i
    refine le_trans (eLpNorm_chartExtGrad_le hγC1 hγind hM0 hγb hp
      (fun j => (hGint j).1) i) ?_
    calc 2 * eLpNorm (H i) p (volume.restrict A)
          + 4 * ENNReal.ofReal M * eLpNorm (H c.dir) p (volume.restrict A)
        ≤ 2 * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N)
          + 4 * ENNReal.ofReal M * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N) := by
          gcongr
          · exact hHA i
          · exact hHA c.dir
      _ = (2 + 4 * ENNReal.ofReal M) * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N) := by ring
  calc ∑ i, eLpNorm (chartExtGrad c.dir γ H i) p volume
      ≤ ∑ _i : Fin d, (2 + 4 * ENNReal.ofReal M)
          * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N) := Finset.sum_le_sum fun i _ => hstep i
    _ = (d : ℝ≥0∞) * (2 + 4 * ENNReal.ofReal M)
          * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1)) * N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ Kre * N := by
        rw [hKredef]
        gcongr
        exact le_add_self

private lemma integrableOn_mul_cutoff {B W Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) (hW : MeasurableSet W) (hsub : B ∩ W ⊆ Ω)
    {u ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hu : IntegrableOn u Ω volume)
    (hξ : Continuous ξ) {C : ℝ} (hC : ∀ y, ‖ξ y‖ ≤ C)
    (hoff : ∀ y, y ∉ W → ξ y = 0) : IntegrableOn (fun y => ξ y * u y) B volume := by
  refine integrableOn_of_vanishing_off hB hW ?_ ?_
  · exact (EllipticPdes.Embedding.integrableOn_mul_bounded (hu.mono_set hsub) hξ hC).congr
      (Filter.Eventually.of_forall fun y => mul_comm (u y) (ξ y))
  · intro y hy
    rw [hoff y hy, zero_mul]


private theorem combined_cutoff_bound {Cξ : ℝ} {Cd : Fin d → ℝ}
    (hCξ0 : 0 ≤ Cξ) (hCd0 : ∀ k, 0 ≤ Cd k) :
    0 ≤ Cξ + ∑ k, Cd k ∧ Cξ ≤ Cξ + ∑ k, Cd k ∧ ∀ k, Cd k ≤ Cξ + ∑ j, Cd j := by
  have hs : (0 : ℝ) ≤ ∑ k, Cd k := Finset.sum_nonneg fun k _ => hCd0 k
  refine ⟨add_nonneg hCξ0 hs, le_add_of_nonneg_right hs, fun k => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hCd0 j) (Finset.mem_univ k)).trans
    (le_add_of_nonneg_left hCξ0)

private theorem partialD_zero_off_cutoff_ball {ξ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hξs : tsupport ξ ⊆ ball x r) :
    ∀ (k : Fin d) y, y ∉ ball x r → partialD k ξ y = 0 := by
  intro k y hy
  have hxs : y ∉ tsupport ξ := fun hc => hy (hξs hc)
  have hev : ξ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport ξ).isOpen_compl.mem_nhds hxs] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  rw [partialD, hev.fderiv_eq]
  simp

/-- **Guo's local boundary extension with its constant** (Theorem III.2.2, proof step 2, p. 21).
Near a boundary point the class extends across the boundary: on any ball strictly inside the
chart's, `localExt` has a weak gradient there and agrees with the original on the part of the
domain the ball meets, and both it and its gradient are bounded in every `Lᵖ` seminorm by the
class and its gradient over the domain, with one constant taken before the class.

The extension is named rather than existentially quantified, which is what lets the operator
be assembled as a linear map. -/
theorem localExtension_bound (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ}
    (hrc : r < c.radius) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      HasWeakGradOn (ball x r) (localExt c x hrc u) (localExtGrad c x hrc u g) ∧
        Integrable (localExt c x hrc u) volume ∧
          (∀ k, Integrable (localExtGrad c x hrc u g k) volume) ∧
          (∀ y ∈ Ω ∩ ball x r, localExt c x hrc u y = u y) ∧
          eLpNorm (localExt c x hrc u) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (localExtGrad c x hrc u g k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  classical
  simp only [localExt, localExtGrad, localExtFun]
  obtain ⟨M, hγC1, hγind, hγb, hγeq⟩ := chartGraph_spec c x
  set γ : EuclideanSpace ℝ (Fin d) → ℝ := chartGraph c x with hγdef
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hγb c.dir 0)
  -- the region of the bounded graph, in the original coordinates
  set A : Set (EuclideanSpace ℝ (Fin d)) := aboveGraph c.dir γ with hAdef
  set A' : Set (EuclideanSpace ℝ (Fin d)) :=
    (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A with hA'def
  have hAopen : IsOpen A := isOpen_aboveGraph (hγC1.differentiable (by simp)).continuous
  have hA'open : IsOpen A' := hAopen.preimage c.motion.continuous
  -- it agrees with the domain on the chart's ball
  have hAW : A' ∩ ball x c.radius = Ω ∩ ball x c.radius := by
    have h1 : A' ∩ ball x c.radius
        = (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
            (A ∩ ball (c.motion x) c.radius) := by
      rw [Set.preimage_inter, preimage_motion_ball]
    rw [h1, hγeq, ← C1Chart.region, Set.preimage_inter, preimage_motion_ball,
      ← c.fits_ball hfits]
  have hsub : A' ∩ ball x c.radius ⊆ Ω := by rw [hAW]; exact Set.inter_subset_left
  -- the cutoff between the two balls
  obtain ⟨hξC1, hξ1, hξs⟩ := chartCutoff_spec x hrc
  set ξ : EuclideanSpace ℝ (Fin d) → ℝ := chartCutoff x hrc with hξdef
  have hξcs : HasCompactSupport ξ :=
    (isCompact_closedBall x c.radius).of_isClosed_subset (isClosed_tsupport ξ)
      (hξs.trans ball_subset_closedBall)
  -- the cutoff and its derivatives vanish off the chart's ball
  have hξ0 : ∀ y, y ∉ ball x c.radius → ξ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hc => hy (hξs hc)
  have hξd0 := partialD_zero_off_cutoff_ball hξs
  have hξpc : ∀ k : Fin d, Continuous (partialD k ξ) := fun k =>
    (hξC1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hξpcs : ∀ k : Fin d, HasCompactSupport (partialD k ξ) := fun k =>
    hξcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  -- one bound for the cutoff and for each of its derivatives
  obtain ⟨Cξ, hCξ⟩ := hξcs.exists_bound_of_continuous hξC1.continuous
  choose Cd hCd using fun k => (hξpcs k).exists_bound_of_continuous (hξpc k)
  set B : ℝ := Cξ + ∑ k, Cd k with hBdef
  have hCξ0 : (0 : ℝ) ≤ Cξ := (norm_nonneg _).trans (hCξ 0)
  have hCd0 : ∀ k, (0 : ℝ) ≤ Cd k := fun k => (norm_nonneg _).trans (hCd k 0)
  obtain ⟨hB0, hCξB, hCdB⟩ := combined_cutoff_bound hCξ0 hCd0
  have hξB : ∀ y, ‖ξ y‖ ≤ B := fun y => (hCξ y).trans hCξB
  have hdB : ∀ (k : Fin d) y, ‖partialD k ξ y‖ ≤ B :=
    fun k y => (hCd k y).trans (hCdB k)
  -- the chart's coordinates, and the motions between them
  have hAeq : (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A'
      = A := by
    rw [hA'def, ← Set.preimage_comp]
    ext y
    simp
  have hγd : Differentiable ℝ γ := hγC1.differentiable (by simp)
  have hnegd : Differentiable ℝ fun z => -γ z := hγd.neg
  have hmpS : MeasurePreserving
      (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) volume volume :=
    c.motion.symm.measurePreserving
  have hmeS : MeasurableEmbedding
      (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    c.motion.symm.toHomeomorph.measurableEmbedding
  have hmpM : MeasurePreserving
      (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) volume volume :=
    c.motion.measurePreserving
  have hmeM : MeasurableEmbedding
      (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    c.motion.toHomeomorph.measurableEmbedding
  -- the restricted motion, which is what the seminorms travel along
  have hresS : MeasurePreserving
      (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (volume.restrict A) (volume.restrict A') := by
    have h := hmpS.restrict_preimage_emb hmeS A'
    rwa [hAeq] at h
  -- the coordinates of the image of a unit direction, each at most one
  have hcoordS : ∀ (k : Fin d) (i : Fin d),
      |c.motion.symm (EuclideanSpace.single k (1 : ℝ)) i| ≤ 1 := by
    intro k i
    refine (abs_coord_le_norm _ i).trans ?_
    rw [c.motion.symm.norm_map, PiLp.norm_single, norm_one]
  -- the constant
  set Kre : ℝ≥0∞ := 2 * ENNReal.ofReal B
      + (d : ℝ≥0∞) * (2 + 4 * ENNReal.ofReal M) * (ENNReal.ofReal B * ((d : ℝ≥0∞) + 1))
    with hKredef
  have hKrefin : Kre ≠ ⊤ := by
    rw [hKredef]
    refine (ENNReal.add_ne_top).mpr ⟨by finiteness, ?_⟩
    finiteness
  refine ⟨Kre.toNNReal, ?_⟩
  have hKcoe : (Kre.toNNReal : ℝ≥0∞) = Kre := ENNReal.coe_toNNReal hKrefin
  rw [hKcoe]
  intro u g hu hgi hwg
  set N : ℝ≥0∞ := eLpNorm u p (volume.restrict Ω)
    + ∑ i, eLpNorm (g i) p (volume.restrict Ω) with hNdef
  -- the class cut off, on the region of the bounded graph
  have hcut := hasWeakGradOn_mul_cutoff_inter hA'open.measurableSet hξC1 hξs
    (hu.mono_set hsub) (fun k => (hgi k).mono_set hsub) (hwg.mono hsub)
  have hIu := integrableOn_mul_cutoff hA'open.measurableSet measurableSet_ball
    hsub hu hξC1.continuous hCξ hξ0
  have hIg1 := fun k => integrableOn_mul_cutoff hA'open.measurableSet measurableSet_ball
    hsub (hgi k) hξC1.continuous hCξ hξ0
  have hIg2 := fun k => integrableOn_mul_cutoff hA'open.measurableSet measurableSet_ball
    hsub hu (hξpc k) (hCd k) (hξd0 k)
  have hIg : ∀ k, IntegrableOn (fun y => ξ y * g k y + partialD k ξ y * u y) A' volume :=
    fun k => (hIg1 k).add (hIg2 k)
  -- into the chart's coordinates
  have hchart := hasWeakGradOn_comp_linearIsometry hIu hIg hcut c.motion.symm
  rw [hAeq] at hchart
  set V : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun y => ξ (c.motion.symm y) * u (c.motion.symm y) with hVdef
  set H : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun k y => ∑ i, c.motion.symm (EuclideanSpace.single k (1 : ℝ)) i *
      (ξ (c.motion.symm y) * g i (c.motion.symm y)
        + partialD i ξ (c.motion.symm y) * u (c.motion.symm y)) with hHdef
  have htrans : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ, IntegrableOn w A' volume →
      IntegrableOn (fun y => w (c.motion.symm y)) A volume := by
    intro w hw
    have h := (hmpS.integrableOn_comp_preimage hmeS (f := w) (s := A')).mpr hw
    rwa [hAeq] at h
  have hVint : IntegrableOn V A volume := htrans _ hIu
  have hGint : ∀ k : Fin d, IntegrableOn (H k) A volume := by
    intro k
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact ((htrans _ (hIg i)).const_mul _)
  have hext := hasWeakGradOn_chartExt hγC1 hγind hγb hVint hGint hchart
  -- global integrability of the extension and of its gradient
  have hmpT : MeasurePreserving (shear c.dir fun z => -γ z) volume volume :=
    measurePreserving_shear hnegd hγind.neg
  have hmeT : MeasurableEmbedding (shear c.dir fun z => -γ z) :=
    measurableEmbedding_shear hnegd.continuous hγind.neg
  have hback : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ, Integrable w volume →
      Integrable (w ∘ shear c.dir fun z => -γ z) volume := fun w hw =>
    (hmpT.integrable_comp_emb hmeT).mpr hw
  have hVhalf : IntegrableOn (fun z => V (shear c.dir γ z)) (halfSpace c.dir) volume :=
    ((measurePreserving_shear_halfSpace hγd hγind).integrable_comp hVint.1).mpr hVint
  have hIext : Integrable (chartExt c.dir γ V) volume :=
    hback _ (integrable_evenExt hVhalf)
  have hSGhalf : ∀ k, IntegrableOn (shearGrad c.dir γ H k) (halfSpace c.dir) volume := by
    intro k
    have hck : Continuous (partialD k γ) :=
      (hγC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h1 : ∀ i : Fin d, IntegrableOn (fun z => H i (shear c.dir γ z))
        (halfSpace c.dir) volume := fun i =>
      ((measurePreserving_shear_halfSpace hγd hγind).integrable_comp (hGint i).1).mpr (hGint i)
    exact (h1 k).add (EllipticPdes.Embedding.integrableOn_mul_bounded (h1 c.dir) hck (hγb k))
  have hIextG : ∀ k, Integrable (chartExtGrad c.dir γ H k) volume := by
    intro k
    have hck : Continuous (partialD k γ) :=
      (hγC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h1 : Integrable
        (evenExtGrad c.dir (shearGrad c.dir γ H) k ∘ shear c.dir fun z => -γ z) volume :=
      hback _ (integrable_evenExtGrad k (hSGhalf k))
    have h2 : Integrable
        (evenExtGrad c.dir (shearGrad c.dir γ H) c.dir ∘ shear c.dir fun z => -γ z) volume :=
      hback _ (integrable_evenExtGrad c.dir (hSGhalf c.dir))
    exact h1.sub (integrableOn_univ.mp
      (EllipticPdes.Embedding.integrableOn_mul_bounded (integrableOn_univ.mpr h2) hck (hγb k)))
  -- back to the original coordinates, and restricted to the smaller ball
  have hfinal := hasWeakGradOn_comp_linearIsometry hIext.integrableOn
    (fun k => (hIextG k).integrableOn) hext c.motion
  rw [Set.preimage_univ] at hfinal
  /- The five estimates, run in the order the chain composes them. -/
  -- the cut-off class over the region, against the domain
  have hVA : eLpNorm V p (volume.restrict A)
      ≤ ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω) := by
    have hmeas : AEStronglyMeasurable (fun y => ξ y * u y) (volume.restrict A') := hIu.1
    have htr : eLpNorm ((fun y => ξ y * u y) ∘
          (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)))
          p (volume.restrict A)
        = eLpNorm (fun y => ξ y * u y) p (volume.restrict A') :=
      eLpNorm_comp_measurePreserving hmeas hresS
    calc eLpNorm V p (volume.restrict A)
        = eLpNorm (fun y => ξ y * u y) p (volume.restrict A') := htr
      _ ≤ ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω) :=
          eLpNorm_mul_cutoff_le hA'open.measurableSet hΩm hB0 hξB hξ0 hsub hIu.1
  -- the cut-off gradient over the region, against the class and its gradient
  have hWA : ∀ i : Fin d,
      eLpNorm (fun y => ξ y * g i y + partialD i ξ y * u y) p (volume.restrict A')
        ≤ ENNReal.ofReal B * eLpNorm (g i) p (volume.restrict Ω)
          + ENNReal.ofReal B * eLpNorm u p (volume.restrict Ω) := by
    intro i
    refine le_trans (eLpNorm_add_le hp) (add_le_add ?_ ?_)
    · exact eLpNorm_mul_cutoff_le hA'open.measurableSet hΩm hB0 hξB hξ0 hsub (hIg1 i).1
    · exact eLpNorm_mul_cutoff_le hA'open.measurableSet hΩm hB0 (hdB i)
        (fun y hy => hξd0 i y hy) hsub (hIg2 i).1
  -- the same, moved into the chart's coordinates and summed over what the motion mixes
  have hHA : ∀ k : Fin d,
      eLpNorm (H k) p (volume.restrict A) ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) + 1) * N := by
    exact chart_gradient_bound c hrc hp Cξ Cd hresS hcoordS u g hNdef hIg htrans hWA
  -- the reflection, and the return through the motion
  have hUbound : eLpNorm (chartExt c.dir γ V ∘
      (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))) p volume
      ≤ Kre * N := by
    exact chart_function_bound c hrc hp M hγind Cξ Cd hγd hmpM hKredef u g hNdef hVint hIext hVA
  have hGbound : ∀ k : Fin d, eLpNorm
      (fun y => ∑ i, c.motion (EuclideanSpace.single k (1 : ℝ)) i
        * chartExtGrad c.dir γ H i (c.motion y)) p volume ≤ Kre * N := by
    exact chart_extension_gradient_bound c hrc hp M hγC1 hγind hγb hM0 Cξ Cd hKredef u g hGint
      hIextG hHA
  refine ⟨hfinal.mono (Set.subset_univ _),
    (hmpM.integrable_comp_emb hmeM).mpr hIext,
    fun k => MeasureTheory.integrable_finsetSum _ fun i _ =>
      ((hmpM.integrable_comp_emb hmeM).mpr (hIextG i)).const_mul _, ?_, hUbound, hGbound⟩
  intro y hy
  have hyA' : y ∈ A' := by
    have hmem : y ∈ Ω ∩ ball x c.radius := ⟨hy.1, ball_subset_ball hrc.le hy.2⟩
    rw [← hAW] at hmem
    exact hmem.1
  change chartExt c.dir γ V (c.motion y) = u y
  rw [chartExt_eq_of_mem hγind hyA', hVdef]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [hξ1 y (ball_subset_closedBall hy.2), one_mul]

/-! ### Linearity of the local extension -/

/-- The chart extension of a class read through the chart is additive in the class. -/
theorem localExtFun_add (c : C1Chart d) (γ ξ u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    localExtFun c γ ξ (fun y => u y + v y)
      = fun y => localExtFun c γ ξ u y + localExtFun c γ ξ v y := by
  have h : (fun z => ξ (c.motion.symm z) * (u (c.motion.symm z) + v (c.motion.symm z)))
      = fun z => ξ (c.motion.symm z) * u (c.motion.symm z)
        + ξ (c.motion.symm z) * v (c.motion.symm z) := by
    funext z; ring
  funext y
  simp only [localExtFun, h, chartExt_add]

/-- The chart extension of a class read through the chart commutes with a scalar. -/
theorem localExtFun_smul (c : C1Chart d) (a : ℝ) (γ ξ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    localExtFun c γ ξ (fun y => a * u y) = fun y => a * localExtFun c γ ξ u y := by
  have h : (fun z => ξ (c.motion.symm z) * (a * u (c.motion.symm z)))
      = fun z => a * (ξ (c.motion.symm z) * u (c.motion.symm z)) := by
    funext z; ring
  funext y
  simp only [localExtFun, h, chartExt_smul]

/-- The gradient of that extension is additive in the class and its gradient. -/
theorem localExtGradFun_add (c : C1Chart d) (γ ξ u v : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    localExtGradFun c γ ξ (fun y => u y + v y) (fun i y => g i y + h i y) k
      = fun y => localExtGradFun c γ ξ u g k y + localExtGradFun c γ ξ v h k y := by
  have hfam : (fun k' z => ∑ i', c.motion.symm (EuclideanSpace.single k' (1 : ℝ)) i' *
        (ξ (c.motion.symm z) * (g i' (c.motion.symm z) + h i' (c.motion.symm z))
          + partialD i' ξ (c.motion.symm z) * (u (c.motion.symm z) + v (c.motion.symm z))))
      = fun k' z => (∑ i', c.motion.symm (EuclideanSpace.single k' (1 : ℝ)) i' *
          (ξ (c.motion.symm z) * g i' (c.motion.symm z)
            + partialD i' ξ (c.motion.symm z) * u (c.motion.symm z)))
        + ∑ i', c.motion.symm (EuclideanSpace.single k' (1 : ℝ)) i' *
          (ξ (c.motion.symm z) * h i' (c.motion.symm z)
            + partialD i' ξ (c.motion.symm z) * v (c.motion.symm z)) := by
    funext k' z
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i' _ => by ring
  funext y
  simp only [localExtGradFun, hfam, chartExtGrad_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The gradient of that extension commutes with a scalar. -/
theorem localExtGradFun_smul (c : C1Chart d) (a : ℝ) (γ ξ u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    localExtGradFun c γ ξ (fun y => a * u y) (fun i y => a * g i y) k
      = fun y => a * localExtGradFun c γ ξ u g k y := by
  have hfam : (fun k' z => ∑ i', c.motion.symm (EuclideanSpace.single k' (1 : ℝ)) i' *
        (ξ (c.motion.symm z) * (a * g i' (c.motion.symm z))
          + partialD i' ξ (c.motion.symm z) * (a * u (c.motion.symm z))))
      = fun k' z => a * ∑ i', c.motion.symm (EuclideanSpace.single k' (1 : ℝ)) i' *
          (ξ (c.motion.symm z) * g i' (c.motion.symm z)
            + partialD i' ξ (c.motion.symm z) * u (c.motion.symm z)) := by
    funext k' z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  funext y
  simp only [localExtGradFun, hfam, chartExtGrad_smul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Local extension is additive in the class.** -/
theorem localExt_add (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hrc : r < c.radius) (u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    localExt c x hrc (fun y => u y + v y)
      = fun y => localExt c x hrc u y + localExt c x hrc v y :=
  localExtFun_add c _ _ u v

/-- **Local extension commutes with a scalar.** -/
theorem localExt_smul (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hrc : r < c.radius) (a : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    localExt c x hrc (fun y => a * u y) = fun y => a * localExt c x hrc u y :=
  localExtFun_smul c a _ _ u

/-- **Gradient of the local extension is additive in the class and its gradient.** -/
theorem localExtGrad_add (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hrc : r < c.radius) (u v : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    localExtGrad c x hrc (fun y => u y + v y) (fun i y => g i y + h i y) k
      = fun y => localExtGrad c x hrc u g k y + localExtGrad c x hrc v h k y :=
  localExtGradFun_add c _ _ u v g h k

/-- **Gradient of the local extension commutes with a scalar.** -/
theorem localExtGrad_smul (c : C1Chart d) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hrc : r < c.radius) (a : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    localExtGrad c x hrc (fun y => a * u y) (fun i y => a * g i y) k
      = fun y => a * localExtGrad c x hrc u g k y :=
  localExtGradFun_smul c a _ _ u g k

/-- **Guo's local boundary extension with its constant**, with the extension quantified away.
This is the form the gluing of step 3 consumes. -/
theorem exists_localExtension_bound (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ}
    (hrc : r < c.radius) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn (ball x r) U G ∧ Integrable U volume ∧
          (∀ k, Integrable (G k) volume) ∧ (∀ y ∈ Ω ∩ ball x r, U y = u y) ∧
          eLpNorm U p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (G k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨K, hK⟩ := localExtension_bound c hΩm hfits hrc hp
  refine ⟨K, fun u g hu hgi hwg => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hK u g hu hgi hwg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩

/-- **Guo's local boundary extension** (Theorem III.2.2, proof step 2, p. 21). Near a boundary
point the class extends across the boundary: on any ball strictly inside the chart's, there is a
class with a weak gradient there agreeing with the original on the part of the domain the ball
meets. -/
theorem exists_localExtension (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ}
    (hrc : r < c.radius) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn (ball x r) U G ∧ Integrable U volume ∧
        (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω ∩ ball x r, U y = u y := by
  obtain ⟨K, hK⟩ := exists_localExtension_bound c hΩm hfits hrc (p := 1) le_rfl
  obtain ⟨U, G, hwgU, hUint, hGint, hag, -, -⟩ := hK u g hu hgi hwg
  exact ⟨U, G, hwgU, hUint, hGint, hag⟩

end EllipticPdes.Extension
