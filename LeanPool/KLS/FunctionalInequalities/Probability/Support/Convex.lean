/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Data.EReal.Operations
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Convex support of a finite measure: uniform halfspace mass and point control

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Lemma 16 and its proof, for a
finite Borel measure `μ`
on a finite-dimensional real inner product space and `x₀` in the interior of the convex hull of its
support:

* bound (54), probability specialization:
  `exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support` gives
  `m ∈ (0, 1]` bounding the mass of every strict open halfspace through `x₀` (in dimension 0 the
  unit sphere is empty);
  proof by a support point on each side, a ball of positive mass in nearby halfspaces and a finite
  cover of the unit sphere
  (finite PRODUCT of ball masses; three private product lemmas);
* bound (54) for finite measures, `0 < m ≤ μ(E)`, by normalization (section
  `FiniteMeasureHalfspace`);
* finiteness near the interior: `x₀` is interior to the effective domain of every nonnegative
  extended-real `φ` with convex
  real epigraph, a.e.-measurable `toENNReal` and finite lintegral (section `EffectiveDomain`);
* **Lemma 16**, the pointwise bound `φ x₀ ≤ C · (∫⁻ φ dμ).toReal` with `C > 0` chosen before `φ`
  (`exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`, section `PointControl`), via the
  halfspace-or-global-minimum
  geometry of extended-real convex functions.

Not provided: the existence of a moment potential, attainment in the variational problem, or
Letwin's quadratic-form bound
with constant 8.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section MeasurableSpace

variable [MeasurableSpace E]

/--
A nonzero direction has a support point strictly on its positive side of an interior point of the
convex hull of
the support. -/
theorem exists_mem_support_inner_sub_pos_of_mem_interior_convexHull (μ : ProbabilityMeasure E)
    {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) {u : E} (hu : u ≠ 0) :
    ∃ y ∈ (μ : Measure E).support, 0 < ⟪u, y - x₀⟫ := by
  by_contra hneg
  push Not at hneg
  have hconv : Convex ℝ {y : E | ⟪u, y - x₀⟫ ≤ 0} := by
    intro a ha b hb α β hα hβ hab
    change ⟪u, a - x₀⟫ ≤ 0 at ha
    change ⟪u, b - x₀⟫ ≤ 0 at hb
    change ⟪u, (α • a + β • b) - x₀⟫ ≤ 0
    calc
      ⟪u, (α • a + β • b) - x₀⟫ = α * ⟪u, a - x₀⟫ + β * ⟪u, b - x₀⟫ := by
        simp only [inner_sub_right, inner_add_right, inner_smul_right]
        linear_combination ⟪u, x₀⟫ * hab
      _ ≤ 0 :=
        add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα ha) (mul_nonpos_of_nonneg_of_nonpos hβ hb)
  have hsubset : convexHull ℝ (μ : Measure E).support ⊆ {y : E | ⟪u, y - x₀⟫ ≤ 0} := by
    apply convexHull_min
    · intro y hy
      exact hneg y hy
    · exact hconv
  have hxnhds := mem_interior_iff_mem_nhds.mp hx₀
  rcases Metric.mem_nhds_iff.mp hxnhds with ⟨ε, hε, hball⟩
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let t : ℝ := ε / (2 * ‖u‖)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  let z : E := x₀ + t • u
  have heq : t * ‖u‖ = ε / 2 := by
    dsimp [t]
    field_simp [ne_of_gt hnorm]
  have hdist : dist z x₀ < ε := by
    dsimp [z]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, heq]
    linarith
  have hzball : z ∈ Metric.ball x₀ ε := Metric.mem_ball.mpr hdist
  have hzmem : z ∈ convexHull ℝ (μ : Measure E).support := hball hzball
  have hzhalf := hsubset hzmem
  change ⟪u, z - x₀⟫ ≤ 0 at hzhalf
  have hzpos : 0 < ⟪u, z - x₀⟫ := by
    dsimp [z]
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
    positivity
  exact (not_lt_of_ge hzhalf) hzpos

/--
Around a support point strictly on the positive side of `u`: a ball of positive mass inside every
open halfspace
`{x | 0 < ⟪v, x - x₀⟫}` with `v` near `u`. -/
theorem exists_pos_ball_inner_sub_pos_of_mem_support (μ : ProbabilityMeasure E) {x₀ u y : E}
    (hy : y ∈ (μ : Measure E).support) (hpos : 0 < ⟪u, y - x₀⟫) :
    ∃ δ > 0,
      ∃ r > 0,
        0 < (μ : Measure E) (Metric.ball y r) ∧
          ∀ v : E, ‖v - u‖ < δ → ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫ := by
  let c : ℝ := ⟪u, y - x₀⟫
  have hc : 0 < c := by
    dsimp [c]
    exact hpos
  let r : ℝ := c / (4 * (‖u‖ + 1))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let δ : ℝ := c / (4 * (‖y - x₀‖ + r + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, r, hr, ?_⟩
  constructor
  · by_contra h
    have hz : (μ : Measure E) (Metric.ball y r) = 0 := by
      apply le_antisymm
      · exact le_of_not_gt h
      · positivity
    have hev : ∀ᶠ s : Set E in (nhds y).smallSets, ¬0 < (μ : Measure E) s := by
      refine (Filter.hasBasis_smallSets (nhds y)).mem_iff.2 ?_
      refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, ?_⟩
      intro s hs hspos
      have hle : (μ : Measure E) s ≤ (μ : Measure E) (Metric.ball y r) :=
        MeasureTheory.measure_mono hs
      rw [hz] at hle
      exact (not_lt_of_ge hle) hspos
    exact (Measure.mem_support_iff.mp hy) hev
  · intro v hv x hx
    have hxy : ‖x - y‖ < r := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hx)
    have hxnorm : ‖x - x₀‖ ≤ ‖y - x₀‖ + r := by
      calc
        ‖x - x₀‖ = ‖(x - y) + (y - x₀)‖ := by
          congr 1
          abel
        _ ≤ ‖x - y‖ + ‖y - x₀‖ := norm_add_le _ _
        _ ≤ r + ‖y - x₀‖ := by linarith
        _ = ‖y - x₀‖ + r := by ring
    have hK : 0 < ‖y - x₀‖ + r + 1 := by positivity
    have hterm₁ : ‖v - u‖ * ‖x - x₀‖ < c / 4 := by
      calc
        ‖v - u‖ * ‖x - x₀‖ ≤ ‖v - u‖ * (‖y - x₀‖ + r) :=
          mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _)
        _ ≤ ‖v - u‖ * (‖y - x₀‖ + r + 1) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · exact norm_nonneg _
        _ < δ * (‖y - x₀‖ + r + 1) := mul_lt_mul_of_pos_right hv hK
        _ = c / 4 := by
          dsimp [δ]
          field_simp
    have hterm₂ : ‖u‖ * ‖x - y‖ < c / 4 := by
      have hu : ‖u‖ < ‖u‖ + 1 := by linarith
      calc
        ‖u‖ * ‖x - y‖ ≤ ‖u‖ * r := mul_le_mul_of_nonneg_left (le_of_lt hxy) (norm_nonneg _)
        _ < (‖u‖ + 1) * r := mul_lt_mul_of_pos_right hu hr
        _ = c / 4 := by
          dsimp [r]
          field_simp
    have habs₁ : |⟪v - u, x - x₀⟫| ≤ ‖v - u‖ * ‖x - x₀‖ := abs_real_inner_le_norm _ _
    have habs₂ : |⟪u, x - y⟫| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    have hlow₁ : -c / 4 < ⟪v - u, x - x₀⟫ := by
      have hle : -|⟪v - u, x - x₀⟫| ≤ ⟪v - u, x - x₀⟫ := neg_abs_le _
      linarith
    have hlow₂ : -c / 4 < ⟪u, x - y⟫ := by
      have hle : -|⟪u, x - y⟫| ≤ ⟪u, x - y⟫ := neg_abs_le _
      linarith
    have hid : ⟪v, x - x₀⟫ = c + ⟪v - u, x - x₀⟫ + ⟪u, x - y⟫ := by
      calc
        ⟪v, x - x₀⟫ = ⟪u, x - x₀⟫ + ⟪v - u, x - x₀⟫ := by
          rw [← inner_add_left]
          congr 1
          abel
        _ = ⟪u, (y - x₀) + (x - y)⟫ + ⟪v - u, x - x₀⟫ := by
          congr 1
          abel_nf
        _ = ⟪u, y - x₀⟫ + ⟪u, x - y⟫ + ⟪v - u, x - x₀⟫ := by rw [inner_add_right]
        _ = c + ⟪v - u, x - x₀⟫ + ⟪u, x - y⟫ := by
          dsimp [c]
          ring
    rw [hid]
    linarith

end MeasurableSpace

section FiniteIndex

variable {α : Type*}
  [DecidableEq α]

omit [DecidableEq α] in
private lemma product_pos_of_pos
    (s : Finset α) (f : α → ℝ) (hf : ∀ a ∈ s, 0 < f a) :
    0 < ∏ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_pos (hf a (Finset.mem_insert_self a s))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

omit [DecidableEq α] in
private lemma product_le_one_of_nonneg_of_le_one
    (s : Finset α) (f : α → ℝ)
    (h₀ : ∀ a ∈ s, 0 ≤ f a) (h₁ : ∀ a ∈ s, f a ≤ 1) :
    (∏ a ∈ s, f a) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hprod : 0 ≤ ∏ b ∈ s, f b := by
        exact Finset.prod_nonneg (fun b hb => h₀ b (Finset.mem_insert_of_mem hb))
      have hprod' : (∏ b ∈ s, f b) ≤ 1 := by
        apply ih
        · intro b hb
          exact h₀ b (Finset.mem_insert_of_mem hb)
        · intro b hb
          exact h₁ b (Finset.mem_insert_of_mem hb)
      have ha₀ : 0 ≤ f a := h₀ a (Finset.mem_insert_self a s)
      have ha₁ : f a ≤ 1 := h₁ a (Finset.mem_insert_self a s)
      calc
        f a * (∏ b ∈ s, f b) ≤ 1 * (∏ b ∈ s, f b) :=
          mul_le_mul_of_nonneg_right ha₁ hprod
        _ = ∏ b ∈ s, f b := one_mul _
        _ ≤ 1 := hprod'

omit [DecidableEq α] in
private lemma product_le_factor_of_nonneg_of_le_one
    (s : Finset α) (f : α → ℝ) {a : α} (ha : a ∈ s)
    (h₀ : ∀ b ∈ s, 0 ≤ f b) (h₁ : ∀ b ∈ s, f b ≤ 1) :
    (∏ b ∈ s, f b) ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at ha
  | @insert b s hb ih =>
      rw [Finset.prod_insert hb]
      by_cases hba : a = b
      · subst a
        have hprod : 0 ≤ ∏ c ∈ s, f c := by
          exact Finset.prod_nonneg (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
        have hprod' : (∏ c ∈ s, f c) ≤ 1 := by
          exact product_le_one_of_nonneg_of_le_one s f
            (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
            (fun c hc => h₁ c (Finset.mem_insert_of_mem hc))
        have hb₀ : 0 ≤ f b := h₀ b (Finset.mem_insert_self b s)
        calc
          f b * (∏ c ∈ s, f c) ≤ f b * 1 :=
            mul_le_mul_of_nonneg_left hprod' hb₀
          _ = f b := mul_one _
      · have ha' : a ∈ s := by
          simpa [hba] using ha
        have hi :
            (∏ c ∈ s, f c) ≤ f a :=
          ih ha'
            (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
            (fun c hc => h₁ c (Finset.mem_insert_of_mem hc))
        have hprod : 0 ≤ ∏ c ∈ s, f c := by
          exact Finset.prod_nonneg (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
        have hb₁ : f b ≤ 1 := h₁ b (Finset.mem_insert_self b s)
        calc
          f b * (∏ c ∈ s, f c) ≤ 1 * (∏ c ∈ s, f c) :=
            mul_le_mul_of_nonneg_right hb₁ hprod
          _ = ∏ c ∈ s, f c := one_mul _
          _ ≤ f a := hi

end FiniteIndex

/--
Uniform positive mass of the strict open halfspaces through an interior point of the convex hull of
the support. -/
theorem exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support
    [FiniteDimensional ℝ E] [MeasurableSpace E] (μ : ProbabilityMeasure E)
    {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) :
    ∃ m : ℝ,
      0 < m ∧ m ≤ 1 ∧ ∀ u : E, ‖u‖ = 1 → m ≤ ((μ : Measure E) {x | 0 < ⟪u, x - x₀⟫}).toReal := by
  classical
  let S := Metric.sphere (0 : E) 1
  have hchoice :
    ∀ u : S,
      ∃ y ∈ (μ : Measure E).support,
        ∃ δ > 0,
          ∃ r > 0,
            0 < (μ : Measure E) (Metric.ball y r) ∧
              ∀ v : E, ‖v - (u : E)‖ < δ → ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫ := by
    intro u
    have hu : (u : E) ≠ 0 := by
      intro hzero
      have hu' := u.property
      rw [Metric.mem_sphere, hzero, dist_zero_right, norm_zero] at hu'
      norm_num at hu'
    obtain ⟨y, hy, hinner⟩ :=
      exists_mem_support_inner_sub_pos_of_mem_interior_convexHull μ hx₀ hu
    obtain ⟨δ, hδ, r, hr, hm, hh⟩ := exists_pos_ball_inner_sub_pos_of_mem_support μ hy hinner
    exact ⟨y, hy, δ, hδ, r, hr, hm, hh⟩
  choose y hy δ hδ r hr hmass hhalf using hchoice
  have hsub : ∀ u : S, IsOpen (Metric.ball (u : E) (δ u)) := fun u => Metric.isOpen_ball
  have hcov : S ⊆ ⋃ u : S, Metric.ball (u : E) (δ u) := by
    intro u hu
    let v : S := ⟨u, hu⟩
    have hv : u ∈ Metric.ball (v : E) (δ v) := by
      rw [Metric.mem_ball, dist_self]
      exact hδ v
    exact Set.mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_sphere (0 : E) 1).elim_finite_subcover (fun u : S => Metric.ball (u : E) (δ u))
      hsub hcov
  let f : S → ℝ := fun u => ((μ : Measure E) (Metric.ball (y u) (r u))).toReal
  let m : ℝ := ∏ u ∈ t, f u
  have hfpos : ∀ u ∈ t, 0 < f u := by
    intro u hu
    dsimp [f]
    exact ENNReal.toReal_pos (ne_of_gt (hmass u)) (measure_ne_top _ _)
  have hfnonneg : ∀ u ∈ t, 0 ≤ f u := by
    intro u hu
    exact le_of_lt (hfpos u hu)
  have hfleone : ∀ u ∈ t, f u ≤ 1 := by
    intro u hu
    dsimp [f]
    have hle : (μ : Measure E) (Metric.ball (y u) (r u)) ≤ (μ : Measure E) Set.univ :=
      measure_mono (Set.subset_univ _)
    have hle' :
      ((μ : Measure E) (Metric.ball (y u) (r u))).toReal ≤ ((μ : Measure E) Set.univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hle
    simpa using hle'
  have hmpos : 0 < m := by
    dsimp [m]
    exact product_pos_of_pos t f hfpos
  have hmleone : m ≤ 1 := by
    dsimp [m]
    exact product_le_one_of_nonneg_of_le_one t f hfnonneg hfleone
  refine ⟨m, hmpos, hmleone, ?_⟩
  intro u hu
  have huS : u ∈ S := by
    change u ∈ Metric.sphere (0 : E) 1
    rw [Metric.mem_sphere, dist_zero_right]
    exact hu
  have hucover : u ∈ ⋃ v ∈ t, Metric.ball (v : E) (δ v) := ht huS
  rcases Set.mem_iUnion.mp hucover with ⟨v, huv⟩
  rcases Set.mem_iUnion.mp huv with ⟨hv, huv⟩
  have huv' : ‖u - (v : E)‖ < δ v := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using huv
  have hmlefv : m ≤ f v := by
    dsimp [m]
    exact product_le_factor_of_nonneg_of_le_one t f hv hfnonneg hfleone
  have hball : Metric.ball (y v) (r v) ⊆ {x : E | 0 < ⟪u, x - x₀⟫} := by
    intro x hx
    exact hhalf v u huv' x hx
  have hmeasure :
    (μ : Measure E) (Metric.ball (y v) (r v)) ≤ (μ : Measure E) {x : E | 0 < ⟪u, x - x₀⟫} :=
    measure_mono hball
  have hreal : f v ≤ ((μ : Measure E) {x : E | 0 < ⟪u, x - x₀⟫}).toReal := by
    dsimp [f]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  exact hmlefv.trans hreal

end InnerProduct


section EffectiveDomain

/-! Cordero-Erausquin–Klartag (2015), Lemma 16, finiteness near the interior: an extended-real
convex potential with finite
integral is finite on a neighbourhood of every interior point of the convex hull of the support. -/

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

omit [MeasurableSpace E] in
private lemma effective_domain_convex (φ : E → EReal)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) : Convex ℝ {x | φ x ≠ ⊤} := by
  have himage : (LinearMap.fst ℝ E ℝ) '' {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} = {x | φ x ≠ ⊤} := by
    ext x
    constructor
    · rintro ⟨⟨y, t⟩, hp, hxy⟩
      change y = x at hxy
      subst y
      change φ x ≤ (t : EReal) at hp
      exact (lt_of_le_of_lt hp (EReal.coe_lt_top t)).ne
    · intro hx
      refine ⟨(x, (φ x).toReal), ?_, rfl⟩
      exact EReal.le_coe_toReal hx
  rw [← himage]
  exact hφ.linear_image (LinearMap.fst ℝ E ℝ)

/--
An interior point of the convex hull of the support of a finite measure is interior to the effective
domain of every
nonnegative extended-real potential with convex real epigraph and finite integral. -/
theorem mem_interior_setOf_ne_top_of_lintegral_ne_top [FiniteDimensional ℝ E]
    (μ : Measure E) (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∀ φ : E → EReal,
        (∀ x, 0 ≤ φ x) →
          Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
            AEMeasurable (fun x => (φ x).toENNReal) μ →
              (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ → x₀ ∈ interior {x | φ x ≠ ⊤} := by
  intro hx₀ φ _h_nonneg h_epi h_meas h_int
  let D : Set E := {x | φ x ≠ ⊤}
  have hD : Convex ℝ D := effective_domain_convex φ h_epi
  have h_ae : ∀ᵐ x ∂μ, x ∈ D := by
    filter_upwards [ae_lt_top' h_meas h_int] with x hx
    exact EReal.toENNReal_ne_top_iff.mp hx.ne
  have h_support : μ.support ⊆ closure D :=
    Measure.support_subset_of_isClosed isClosed_closure
      (h_ae.mono fun _ hx => subset_closure hx)
  have h_closed_span : closure D ⊆ (affineSpan ℝ D : Set E) :=
    closure_minimal (subset_affineSpan ℝ D) (affineSpan ℝ D).isClosed_of_finiteDimensional
  have h_support_span : affineSpan ℝ μ.support = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior ⟨x₀, hx₀⟩
  have h_span : affineSpan ℝ D = ⊤ := by
    apply top_unique
    rw [← h_support_span]
    exact affineSpan_le.mpr (h_support.trans h_closed_span)
  have h_interior : (interior D).Nonempty :=
    hD.interior_nonempty_iff_affineSpan_eq_top.mpr h_span
  have h_hull : convexHull ℝ μ.support ⊆ closure D := convexHull_min h_support hD.closure
  have hx_closure : x₀ ∈ interior (closure D) := interior_mono h_hull hx₀
  rwa [hD.interior_closure_eq_interior_of_nonempty_interior h_interior] at hx_closure

end EffectiveDomain

section FiniteMeasureHalfspace

/-! Cordero-Erausquin–Klartag (2015), Lemma 16, bound (54) for a FINITE Borel measure (the source's
generality): the
probability specialization `exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`
transported by
normalization `ν = μ(E)⁻¹ • μ` (same support; `μ ≠ 0` follows from the support-hull hypothesis,
never from the zero-mass
fallback of `FiniteMeasure.normalize`). The bound `m ≤ μ(E)` keeps the positive total mass for the
global-minimum
alternative; in dimension 0 the direction condition is vacuous. -/

/--
Uniform positive mass, at most the total mass, of the strict open halfspaces through an interior
point of the convex
hull of the support of a finite Borel measure. -/
theorem exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] {x₀ : E}
    (hx₀ : x₀ ∈ interior (convexHull ℝ μ.support)) :
    ∃ m : ℝ,
      0 < m ∧ m ≤ μ.real Set.univ ∧ ∀ u : E, ‖u‖ = 1 → m ≤ μ.real {x | 0 < ⟪u, x - x₀⟫} := by
  classical
  have hμne : μ ≠ 0 := by
    intro hz
    simp [hz] at hx₀
  let fm : FiniteMeasure E := ⟨μ, inferInstance⟩
  have hfmne : fm ≠ 0 := by
    intro hz
    exact hμne (congrArg (fun η : FiniteMeasure E => (η : Measure E)) hz)
  have hmassne : fm.mass ≠ 0 := fm.mass_ne_zero_iff.mpr hfmne
  have hmasspos : 0 < (fm.mass : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hmassne)
  let ν : ProbabilityMeasure E := fm.normalize
  have hnull (s : Set E) : (ν : Measure E) s = 0 ↔ μ s = 0 := by
    change (ν : Measure E) s = 0 ↔ (fm : Measure E) s = 0
    rw [← ν.ennreal_coeFn_eq_coeFn_toMeasure s, ← fm.ennreal_coeFn_eq_coeFn_toMeasure s]
    rw [ENNReal.coe_eq_zero, ENNReal.coe_eq_zero, fm.self_eq_mass_mul_normalize s, mul_eq_zero]
    simp [hmassne, ν]
  have hsupp : (ν : Measure E).support = μ.support := by
    ext x
    simp only [Measure.mem_support_iff_forall, pos_iff_ne_zero]
    exact forall_congr' fun s => forall_congr' fun _ => not_congr (hnull s)
  have hscale (s : Set E) : μ.real s = (fm.mass : ℝ) * (ν : Measure E).real s := by
    change (fm s : ℝ) = (fm.mass : ℝ) * (ν s : ℝ)
    exact_mod_cast fm.self_eq_mass_mul_normalize s
  have hν : x₀ ∈ interior (convexHull ℝ (ν : Measure E).support) := by rwa [hsupp]
  obtain ⟨m, hmpos, hmone, hhalf⟩ :=
    exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support ν hν
  refine ⟨(fm.mass : ℝ) * m, mul_pos hmasspos hmpos, ?_, ?_⟩
  · change (fm.mass : ℝ) * m ≤ (fm.mass : ℝ)
    exact mul_le_of_le_one_right hmasspos.le hmone
  · intro u hu
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hhalf u hu) hmasspos.le

end FiniteMeasureHalfspace

section PointControl

/-! Cordero-Erausquin–Klartag (2015), Lemma 16: the pointwise bound follows from the
finite-near theorem, the finite-measure bound (54), and convex effective-domain geometry.
Private geometry uses `effective_domain_convex` in section `EffectiveDomain`;
`real_convexOn_effective_domain` is the public effective-domain interface. -/

open Set

private lemma finite_value_coe {E : Type*} {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) {x : E} (hx : φ x ≠ ⊤) :
    ((φ x).toReal : EReal) = φ x := by
  exact EReal.coe_toReal hx (ne_of_gt (EReal.bot_lt_zero.trans_le (h0 x)))

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
For a nonnegative extended-real function with convex real epigraph, its real part is convex on the
effective domain
`{φ ≠ ⊤}`. -/
lemma real_convexOn_effective_domain {φ : E → EReal} (h0 : ∀ x, 0 ≤ φ x)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    ConvexOn ℝ {x | φ x ≠ ⊤} (fun x => (φ x).toReal) := by
  have hepi :
    {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} =
      {p : E × ℝ | p.1 ∈ {x | φ x ≠ ⊤} ∧ (φ p.1).toReal ≤ p.2} := by
    ext p
    constructor
    · intro hp
      change φ p.1 ≤ (p.2 : EReal) at hp
      have hx : φ p.1 ≠ ⊤ := (lt_of_le_of_lt hp (EReal.coe_lt_top p.2)).ne
      refine ⟨hx, ?_⟩
      rw [← finite_value_coe h0 hx] at hp
      exact EReal.coe_le_coe_iff.mp hp
    · rintro ⟨hx, hp⟩
      change φ p.1 ≤ (p.2 : EReal)
      rw [← finite_value_coe h0 hx]
      exact EReal.coe_le_coe_iff.mpr hp
  rw [hepi] at hφ
  exact convexOn_of_convex_epigraph hφ

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private lemma strict_sublevel_convex_and_interior {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)})
    {x₀ y : E} (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) (hy : φ y < φ x₀) :
    Convex ℝ {x | φ x < φ x₀} ∧ (interior {x | φ x < φ x₀}).Nonempty := by
  let D : Set E := {x | φ x ≠ ⊤}
  let f : E → ℝ := fun x => (φ x).toReal
  have hxD : x₀ ∈ D := interior_subset hx₀
  have hyD : y ∈ D := (hy.trans_le le_top).ne
  have hDconv : Convex ℝ D := effective_domain_convex φ hφ
  have hcf : ConvexOn ℝ D f := real_convexOn_effective_domain h0 hφ
  have hS : {x | φ x < φ x₀} = {x ∈ D | f x < f x₀} := by
    ext x
    constructor
    · intro hx
      change φ x < φ x₀ at hx
      have hxD' : x ∈ D := (hx.trans_le le_top).ne
      refine ⟨hxD', ?_⟩
      rw [← finite_value_coe h0 hxD', ← finite_value_coe h0 hxD] at hx
      exact EReal.coe_lt_coe_iff.mp hx
    · rintro ⟨hxD', hx⟩
      change φ x < φ x₀
      rw [← finite_value_coe h0 hxD', ← finite_value_coe h0 hxD]
      exact EReal.coe_lt_coe_iff.mpr hx
  have hconv : Convex ℝ {x | φ x < φ x₀} := by
    rw [hS]
    exact hcf.convex_lt (f x₀)
  let z : E := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • x₀
  have hzD : z ∈ interior D :=
    hDconv.combo_self_interior_mem_interior hyD hx₀ (by norm_num) (by norm_num) (by norm_num)
  have hyf : f y < f x₀ := by
    rw [← finite_value_coe h0 hyD, ← finite_value_coe h0 hxD] at hy
    exact EReal.coe_lt_coe_iff.mp hy
  have hzle : f z ≤ (1 / 2 : ℝ) * f y + (1 / 2 : ℝ) * f x₀ :=
    hcf.2 hyD hxD (by norm_num) (by norm_num) (by norm_num)
  have hzlt : f z < f x₀ := by linarith
  have hcont : ContinuousOn f (interior D) :=
    (hcf.subset interior_subset hDconv.interior).continuousOn isOpen_interior
  have hopen : IsOpen (interior D ∩ f ⁻¹' Set.Iio (f x₀)) :=
    hcont.isOpen_inter_preimage isOpen_interior isOpen_Iio
  have hsubset : interior D ∩ f ⁻¹' Set.Iio (f x₀) ⊆ {x | φ x < φ x₀} := by
    rw [hS]
    intro x hx
    exact ⟨interior_subset hx.1, hx.2⟩
  have hzU : z ∈ interior (interior D ∩ f ⁻¹' Set.Iio (f x₀)) := by
    rw [hopen.interior_eq]
    exact ⟨hzD, hzlt⟩
  exact ⟨hconv, ⟨z, (interior_mono hsubset) hzU⟩⟩

private theorem exists_unit_halfspace_le_or_isMin_of_convex_epigraph {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) {x₀ : E}
    (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) :
    (∃ u : E, ‖u‖ = 1 ∧ ∀ x, 0 < ⟪u, x - x₀⟫ → φ x₀ ≤ φ x) ∨ ∀ x, φ x₀ ≤ φ x := by
  classical
  by_cases hmin : ∀ x, φ x₀ ≤ φ x
  · exact Or.inr hmin
  obtain ⟨y, hy⟩ := not_forall.mp hmin
  have hylt : φ y < φ x₀ := lt_of_not_ge hy
  obtain ⟨hSconv, hSint⟩ := strict_sublevel_convex_and_interior h0 hφ hx₀ hylt
  obtain ⟨L, hL, hsep⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point (x := x₀) hSconv
      (by
        intro hx
        have hx' : x₀ ∈ {x | φ x < φ x₀} := interior_subset hx
        exact (lt_irrefl (φ x₀)) hx')
      hSint
  let w : E := (InnerProductSpace.toDual ℝ E).symm L
  have hw : w ≠ 0 := by
    intro hwzero
    apply hL
    have h := congrArg (InnerProductSpace.toDual ℝ E) hwzero
    simpa only [w, LinearIsometryEquiv.apply_symm_apply, map_zero] using h
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  left
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos), inv_mul_cancel₀ hwpos.ne']
  · intro x hx
    by_contra hnot
    have hs : x ∈ {x | φ x < φ x₀} := lt_of_not_ge hnot
    have hle : L x ≤ L x₀ := hsep x hs
    have hinner : ⟪w, x - x₀⟫ = L x - L x₀ := by
      dsimp [w]
      rw [inner_sub_right, InnerProductSpace.toDual_symm_apply,
        InnerProductSpace.toDual_symm_apply]
    rw [real_inner_smul_left, hinner] at hx
    exact
      (not_lt_of_ge
          (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg w))
            (sub_nonpos.mpr hle)))
        hx

end FiniteDimensional

/--
**CEK Lemma 16, pointwise bound.** For a finite Borel measure and an interior point of the convex
hull of its support
there is `C > 0`, chosen before `φ`, with `φ x₀ ≤ C · (∫⁻ φ dμ).toReal` for every nonnegative
extended-real `φ` with convex
real epigraph, a.e.-measurable `toENNReal` and finite lintegral. -/
theorem exists_pos_le_mul_lintegral_toReal_of_convex_epigraph [MeasurableSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∃ C : ℝ,
        0 < C ∧
          ∀ φ : E → EReal,
            (∀ x, 0 ≤ φ x) →
              Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
                AEMeasurable (fun x => (φ x).toENNReal) μ →
                  (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
                    φ x₀ ≤ ((C * (∫⁻ x, (φ x).toENNReal ∂μ).toReal : ℝ) : EReal) := by
  intro hx₀
  obtain ⟨m, hmpos, hmass, hhalf⟩ :=
    exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure μ hx₀
  refine ⟨m⁻¹, inv_pos.mpr hmpos, ?_⟩
  intro φ h_nonneg h_epi h_meas h_int
  have hxD : x₀ ∈ interior {x | φ x ≠ ⊤} :=
    mem_interior_setOf_ne_top_of_lintegral_ne_top μ x₀ hx₀ φ h_nonneg h_epi h_meas h_int
  have hset : ∃ S : Set E, m ≤ μ.real S ∧ ∀ x ∈ S, φ x₀ ≤ φ x := by
    rcases exists_unit_halfspace_le_or_isMin_of_convex_epigraph h_nonneg h_epi hxD with hgeo |
      hmin
    · obtain ⟨u, hu, hbound⟩ := hgeo
      exact ⟨{x | 0 < ⟪u, x - x₀⟫}, hhalf u hu, fun x hx => hbound x hx⟩
    · exact ⟨Set.univ, hmass, fun x _ => hmin x⟩
  obtain ⟨S, hSmass, hSphi⟩ := hset
  have hlow : (φ x₀).toENNReal * μ S ≤ ∫⁻ x, (φ x).toENNReal ∂μ := by
    rw [← setLIntegral_const]
    exact
      (setLIntegral_mono_ae h_meas.restrict
            (Filter.Eventually.of_forall fun x hx =>
              EReal.toENNReal_le_toENNReal (hSphi x hx))).trans
        (setLIntegral_le_lintegral S _)
  have hreal := ENNReal.toReal_mono h_int hlow
  rw [ENNReal.toReal_mul, EReal.toReal_toENNReal (h_nonneg x₀)] at hreal
  have hmq : m * (φ x₀).toReal ≤ (∫⁻ x, (φ x).toENNReal ∂μ).toReal := by
    calc
      m * (φ x₀).toReal ≤ μ.real S * (φ x₀).toReal :=
        mul_le_mul_of_nonneg_right hSmass (EReal.toReal_nonneg (h_nonneg x₀))
      _ = (φ x₀).toReal * (μ S).toReal := by rw [measureReal_def, mul_comm]
      _ ≤ (∫⁻ x, (φ x).toENNReal ∂μ).toReal := hreal
  rw [← finite_value_coe h_nonneg (interior_subset hxD)]
  apply EReal.coe_le_coe_iff.mpr
  simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀' hmpos).mpr hmq

end InnerProduct

end PointControl

end FunctionalInequalities.Probability

/-! ### CEK Proposition 12: interior of a centered convex support -/

namespace FunctionalInequalities.Probability


section
-- The origin is interior to the convex hull of a centred support.

open MeasureTheory
/--
The origin is interior to the convex hull of the support of a nonzero finite measure with finite
first moment and
zero barycenter that is not concentrated on any proper linear subspace. -/
theorem zero_mem_interior_convexHull_support_of_integral_eq_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
     (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    (0 : E) ∈ interior (convexHull ℝ μ.support) := by
  classical
  let : NeZero μ := ⟨hμ⟩
  have hmass : 0 < μ.real Set.univ := measureReal_univ_pos
  have hzero (L : E →L[ℝ] ℝ) : (∫ x, L x ∂μ) = 0 := by
    simpa only [hbar, map_zero] using L.integral_comp_comm hint
  have hker (L : E →L[ℝ] ℝ) (hz : ∀ᵐ x ∂μ, L x = 0) : L = 0 := by
    have hk : μ (L.toLinearMap.ker : Set E)ᶜ = 0 := by
      change μ {x | ¬L x = 0} = 0
      exact ae_iff.mp hz
    have ht : L.toLinearMap.ker = ⊤ := hsub _ hk
    have hl : L.toLinearMap = 0 := LinearMap.ker_eq_top.mp ht
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hl
  have hspan : affineSpan ℝ μ.support = ⊤ := by
    obtain ⟨p, hp⟩ := μ.nonempty_support hμ
    let A := affineSpan ℝ μ.support
    have hpA : p ∈ A := mem_affineSpan ℝ hp
    by_contra hA
    have hdir : A.direction ≠ ⊤ := by
      intro hd
      exact hA ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p, hpA⟩).mp hd)
    obtain ⟨g, hg, hgd⟩ := A.direction.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hdir)
    let L : E →L[ℝ] ℝ := g.toContinuousLinearMap
    have hconstant (x : E) (hx : x ∈ μ.support) : L x = L p := by
      have hd := A.vsub_mem_direction (mem_affineSpan ℝ hx) hpA
      have hk : g (x - p) = 0 := hgd hd
      change g x = g p
      exact sub_eq_zero.mp (by simpa only [map_sub] using hk)
    have hae : (fun x => L x) =ᵐ[μ] (fun _ => L p) := by
      filter_upwards [μ.support_mem_ae] with x hx
      exact hconstant x hx
    have hpzero : L p = 0 := by
      have hm : μ.real Set.univ * L p = 0 := by
        calc
          μ.real Set.univ * L p = ∫ _ : E, L p ∂μ := by simp only [integral_const, smul_eq_mul]
          _ = ∫ x, L x ∂μ := (integral_congr_ae hae).symm
          _ = 0 := hzero L
      exact (mul_eq_zero.mp hm).resolve_left hmass.ne'
    have hl : L = 0 := hker L (by filter_upwards [hae] with x hx; exact hx.trans hpzero)
    apply hg
    ext x
    exact congrArg (fun f : E →L[ℝ] ℝ => f x) hl
  have hinterior : (interior (convexHull ℝ μ.support)).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  by_contra hnot
  obtain ⟨L, hL, hle⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point (convex_convexHull ℝ μ.support) hnot
      hinterior
  have hnonpos : ∀ᵐ x ∂μ, L x ≤ 0 := by
    filter_upwards [μ.support_mem_ae] with x hx
    simpa only [map_zero] using hle x (subset_convexHull ℝ μ.support hx)
  have hi : Integrable (fun x => -L x) μ := (L.integrable_comp hint).neg
  have hn : 0 ≤ᵐ[μ] (fun x => -L x) := by
    filter_upwards [hnonpos] with x hx
    exact neg_nonneg.mpr hx
  have hnint : (∫ x, -L x ∂μ) = 0 := by rw [integral_neg, hzero L, neg_zero]
  have hnzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hnint
  have hz : ∀ᵐ x ∂μ, L x = 0 := by
    filter_upwards [hnzero] with x hx
    exact neg_eq_zero.mp hx
  exact hL (hker L hz)

end

end FunctionalInequalities.Probability
