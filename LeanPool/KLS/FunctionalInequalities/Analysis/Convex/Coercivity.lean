/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Minimum and compact sublevels of a convex potential with integrable `e^{-φ}`

Letwin arXiv:2607.24164v1, Lemma A.4 (p. 17), first sentence of the proof: a finite convex `φ` on a
finite-dimensional real inner product space with `e^{-φ}` integrable for an additive Haar measure
attains its minimum, and every sublevel set is compact
(`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`). No minimum, coercivity
or bounded-sublevel premise; the source normalisation `∫ e^{-φ} = 1` only supplies
the integrability.
Dimension zero is included.

Route: every sublevel has finite Haar volume; a convex set of finite volume containing a ball is
bounded (otherwise it contains arbitrarily many disjoint translates of a smaller ball); closed and
bounded sublevels are compact, and the minimum over the nonempty sublevel `{φ ≤ φ 0}` is global.

`isBounded_of_convex_of_measure_lt_top` isolates the shared normed-space boundedness step; the
moment-potential ball-truncation construction uses this same producer.
-/

@[expose] public section

open MeasureTheory

namespace FunctionalInequalities.Analysis

section ConvexSets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A convex set of finite additive Haar measure containing a ball around the origin is bounded.

The disjoint-ball argument uses only the real normed-space structure, translation invariance and
positive measure of open balls. No finite-dimensionality, completeness, inner product, closedness
or measurability of the convex set is required. This is the common boundedness step in Letwin
arXiv:2607.24164v1, Lemma A.4, and the linear-growth support for CEK arXiv:1304.0630v1, (7). -/
theorem isBounded_of_convex_of_measure_lt_top (m : Measure E) [m.IsAddHaarMeasure]
    (s : Set E) (hcs : Convex ℝ s)
    (hms : m s < (⊤ : ENNReal))
    (hrball : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : E) r ⊆ s) : Bornology.IsBounded s := by
  obtain ⟨r, hr, hball⟩ := hrball
  have hzero : (0 : E) ∈ s := hball (by simpa using hr)
  let b : ENNReal := m (Metric.ball (0 : E) (r / 2))
  have hbfinite : b < (⊤ : ENNReal) := by
    apply lt_of_le_of_lt _ hms
    apply measure_mono
    exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans hball
  have hbne : b ≠ 0 := ne_of_gt (Metric.measure_ball_pos m (0 : E) (by linarith : 0 < r / 2))
  have hbpos : 0 < b.toReal := by
    by_contra hh
    have hz : b.toReal = 0 := le_antisymm (le_of_not_gt hh) ENNReal.toReal_nonneg
    have he := ENNReal.ofReal_toReal (ne_of_lt hbfinite)
    rw [hz, ENNReal.ofReal_zero] at he
    exact hbne he.symm
  have hballmeasure (z : E) : m (Metric.ball z (r / 2)) = b := by
    dsimp [b]
    have hh : Metric.ball (0 : E) (r / 2) = (z + ·) ⁻¹' Metric.ball z (r / 2) := by
      simp [preimage_add_ball]
    rw [hh, measure_preimage_add]
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((m s).toReal / b.toReal) 1)
  have hNratio : (m s).toReal / b.toReal < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : 0 < (N : ℝ) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (lt_of_le_of_lt (le_max_right _ _) hN)
  apply (Metric.isBounded_iff_subset_closedBall (0 : E)).2
  refine ⟨2 * (N : ℝ) * r, ?_⟩
  intro x hx
  change dist x 0 ≤ 2 * (N : ℝ) * r
  rw [dist_zero_right]
  by_contra hnx
  have hlarge : 2 * (N : ℝ) * r < ‖x‖ := lt_of_not_ge hnx
  have hxpos : 0 < ‖x‖ := lt_trans (by positivity) hlarge
  let f : Fin N → E := fun i => ((i.val : ℝ) * r / ‖x‖) • x
  have hinside (i : Fin N) : Metric.ball (f i) (r / 2) ⊆ s := by
    intro z hz
    let t : ℝ := (i.val : ℝ) * r / ‖x‖
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    have hi : (i.val : ℝ) < (N : ℝ) := by exact_mod_cast i.isLt
    have hir : (i.val : ℝ) * r < (N : ℝ) * r := mul_lt_mul_of_pos_right hi hr
    have htupper : 2 * t ≤ 1 := by
      dsimp [t]
      rw [← mul_div_assoc, div_le_iff₀ hxpos]
      nlinarith [hir, hlarge]
    have hu : (2 : ℝ) • (z - t • x) ∈ s := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hz' : ‖z - t • x‖ < r / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        simpa [f, t] using hz
      linarith
    have hv : (2 * t) • x ∈ s := by
      have hv' :=
        hcs hzero hx (a := 1 - 2 * t) (b := 2 * t) (by linarith) (by positivity) (by ring)
      simpa using hv'
    have hm :=
      hcs hu hv (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num)
    have he : (1 / 2 : ℝ) • ((2 : ℝ) • (z - t • x)) + (1 / 2 : ℝ) • ((2 * t) • x) = z := by
      module
    rwa [he] at hm
  have hdis :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun i => Metric.ball (f i) (r / 2)) := by
    intro i _ j _ hij
    apply Metric.ball_disjoint_ball
    have hdist : dist (f i) (f j) = |(i.val : ℝ) - (j.val : ℝ)| * r := by
      dsimp [f]
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have he :
        (i.val : ℝ) * r / ‖x‖ - (j.val : ℝ) * r / ‖x‖ =
          ((i.val : ℝ) - (j.val : ℝ)) * (r / ‖x‖) := by
        ring
      rw [he, abs_mul, abs_of_pos (div_pos hr hxpos)]
      field_simp [ne_of_gt hxpos]
    have hval : i.val ≠ j.val := by
      intro he
      exact hij (Fin.ext he)
    have habs : 1 ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      have hord : i.val + 1 ≤ j.val ∨ j.val + 1 ≤ i.val := by omega
      rcases hord with hij' | hji'
      · have hh : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hij'
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hh : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hji'
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hmul : (1 : ℝ) * r ≤ |(i.val : ℝ) - (j.val : ℝ)| * r :=
      mul_le_mul_of_nonneg_right habs (le_of_lt hr)
    rw [hdist]
    nlinarith [hmul]
  have hmass : (N : ENNReal) * b ≤ m s := by
    calc
      _ = ∑ i : Fin N, b := by simp [nsmul_eq_mul]
      _ = ∑ i : Fin N, m (Metric.ball (f i) (r / 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hballmeasure (f i)).symm
      _ = ∑ i ∈ (Finset.univ : Finset (Fin N)), m (Metric.ball (f i) (r / 2)) := by simp
      _ = m (⋃ i ∈ (Finset.univ : Finset (Fin N)), Metric.ball (f i) (r / 2)) :=
        (measure_biUnion_finset hdis (fun _ _ => measurableSet_ball)).symm
      _ ≤ m s := by
        apply measure_mono
        intro z hz
        obtain ⟨i, _, hzi⟩ := Set.mem_iUnion₂.mp hz
        exact hinside i hzi
  have hreal := ENNReal.toReal_mono (ne_of_lt hms) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  have hstrict : (m s).toReal < (N : ℝ) * b.toReal := (div_lt_iff₀ hbpos).mp hNratio
  exact (not_lt_of_ge hreal) hstrict

end ConvexSets

section IntegrablePotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
**Coercivity from integrability** (Letwin Lemma A.4, p. 17): a convex `φ` with `e^{-φ}` integrable
for an additive Haar measure has a global minimiser, and all its sublevel sets are compact. -/
theorem exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
    (m : Measure E) [m.IsAddHaarMeasure] {φ : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ φ) (hint : Integrable (fun x => Real.exp (-φ x)) m) :
    (∃ y₀ : E, ∀ y, φ y₀ ≤ φ y) ∧ ∀ c : ℝ, IsCompact {y | φ y ≤ c} := by
  classical
  have hcont : Continuous φ := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hfinite : (∫⁻ x, ENNReal.ofReal (Real.exp (-φ x)) ∂m) < (⊤ : ENNReal) := by
    simpa [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hint.hasFiniteIntegral
  -- Use exponential integrability to make every sublevel have finite measure.
  have hlevel_finite (c : ℝ) : m {x | φ x ≤ c} < (⊤ : ENNReal) := by
    have hs : MeasurableSet {x | φ x ≤ c} := (isClosed_le hcont continuous_const).measurableSet
    have hmajor :
      ENNReal.ofReal (Real.exp (-c)) * m {x | φ x ≤ c} ≤
        ∫⁻ x, ENNReal.ofReal (Real.exp (-φ x)) ∂m := by
      calc
        _ =
            ∫⁻ x,
              ({x | φ x ≤ c} : Set E).indicator (fun _ => ENNReal.ofReal (Real.exp (-c)))
                x ∂m := by
          rw [lintegral_indicator hs, setLIntegral_const]
        _ ≤ _ := by
          apply lintegral_mono
          intro x
          by_cases hx : φ x ≤ c
          · have hx' : x ∈ ({x : E | φ x ≤ c} : Set E) := hx
            rw [Set.indicator_of_mem hx']
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hx))
          · have hx' : x ∉ ({x : E | φ x ≤ c} : Set E) := hx
            rw [Set.indicator_of_notMem hx']
            exact bot_le
    have hprod := lt_of_le_of_lt hmajor hfinite
    have hne : ENNReal.ofReal (Real.exp (-c)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    by_contra hn
    have ht : m {x | φ x ≤ c} = (⊤ : ENNReal) := top_unique (le_of_not_gt hn)
    simp [ht, hne] at hprod
  have hlevel_convex (c : ℝ) : Convex ℝ {x | φ x ≤ c} := by
    intro x hx y hy a b ha hb hab
    have hh := hconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    change φ x ≤ c at hx
    change φ y ≤ c at hy
    change φ (a • x + b • y) ≤ c
    have hweight : a * φ x + b * φ y ≤ c := by
      calc
        a * φ x + b * φ y ≤ a * c + b * c :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = (a + b) * c := by ring
        _ = c := by rw [hab, one_mul]
    exact hh.trans hweight
  -- Obtain compact sublevels and a global minimizer.
  have hcompact (c : ℝ) : IsCompact {x | φ x ≤ c} := by
    let d : ℝ := max c (φ 0 + 1)
    have hcd : c ≤ d := le_max_left _ _
    have hzero : φ (0 : E) < d := by
      have hd : φ (0 : E) + 1 ≤ d := le_max_right _ _
      linarith
    have hopen : IsOpen {x | φ x < d} := isOpen_lt hcont continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
    have hbd : Bornology.IsBounded {x | φ x ≤ d} := by
      apply isBounded_of_convex_of_measure_lt_top m _ (hlevel_convex d) (hlevel_finite d)
      exact
        ⟨r, hr, fun x hx => by
          have hxlt : φ x < d := show x ∈ {x | φ x < d} from hball hx
          change x ∈ {x | φ x ≤ d}
          exact le_of_lt hxlt⟩
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
    exact
      hbd.subset
        (fun x hx => by
          change φ x ≤ d
          exact le_trans (show φ x ≤ c from hx) hcd)
  obtain ⟨y₀, hy₀, hmin⟩ :=
    (hcompact (φ 0)).exists_isMinOn
      (show ({y : E | φ y ≤ φ 0} : Set E).Nonempty from
        ⟨0, by
          change φ (0 : E) ≤ φ 0
          exact le_rfl⟩)
      hcont.continuousOn
  refine ⟨⟨y₀, ?_⟩, hcompact⟩
  intro y
  by_cases hy : φ y ≤ φ 0
  · exact hmin (show y ∈ {y : E | φ y ≤ φ 0} from hy)
  · exact le_trans (show φ y₀ ≤ φ 0 from hy₀) (le_of_lt (lt_of_not_ge hy))

end IntegrablePotential

/-! ## Linear growth from a strict minimum and attained minima -/

section LinearGrowth

open Set Metric Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/--
**Linear growth from a strict minimum.** A continuous convex `f` on a proper normed space with a
strict global minimum at `a` satisfies `c ‖x‖ + b ≤ f x` for some `c > 0` and `b` (convexity along
the rays through the unit sphere around `a`). -/
theorem exists_linear_lower_bound_of_strict_min {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hc : Continuous f) (a : E) (hm : ∀ x, x ≠ a → f a < f x) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ, ∀ x, c * ‖x‖ + b ≤ f x := by
  have hmin (x : E) : f a ≤ f x := by
    by_cases h : x = a
    · subst x; exact le_rfl
    · exact (hm x h).le
  obtain ⟨m, ham, hms⟩ :=
    (isCompact_sphere a (1 : ℝ)).exists_forall_le' hc.continuousOn
      (fun x hx => hm x (by intro h; subst x; simp at hx))
  let c := m - f a
  have hcp : 0 < c := sub_pos.mpr ham
  have hg (x : E) : f a + c * (‖x - a‖ - 1) ≤ f x := by
    by_cases hlarge : 1 ≤ ‖x - a‖
    · have hd : 0 < ‖x - a‖ := lt_of_lt_of_le zero_lt_one hlarge
      let t := ‖x - a‖⁻¹
      have ht : 0 < t := inv_pos.mpr hd
      have ht1 : t ≤ 1 := by
        dsimp only [t]
        exact inv_le_one_of_one_le₀ hlarge
      have hy : (1 - t) • a + t • x ∈ sphere a 1 := by
        rw [mem_sphere, dist_eq_norm]
        have heq : ((1 - t) • a + t • x) - a = t • (x - a) := by module
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        exact inv_mul_cancel₀ hd.ne'
      have hj : f ((1 - t) • a + t • x) ≤ (1 - t) * f a + t * f x := by
        simpa only [smul_eq_mul] using
          hf.2 (mem_univ a) (mem_univ x) (sub_nonneg.mpr ht1) ht.le (by ring)
      have hp : c ≤ t * (f x - f a) := by
        have h := hms ((1 - t) • a + t • x) hy
        dsimp only [c]
        nlinarith
      have hprod := mul_le_mul_of_nonneg_left hp hd.le
      dsimp only [t] at hprod
      rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at hprod
      nlinarith
    · have hd : ‖x - a‖ < 1 := lt_of_not_ge hlarge
      calc
        _ ≤ f a := by nlinarith
        _ ≤ f x := hmin x
  refine ⟨c, hcp, f a - c * (‖a‖ + 1), fun x => ?_⟩
  have hn : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by simpa only [sub_add_cancel] using norm_add_le (x - a) a
  have hmul := mul_le_mul_of_nonneg_left hn hcp.le
  have h := hg x
  nlinarith

omit [NormedSpace ℝ E] in
/--
A continuous `f` on a proper space with `c ‖x‖ + b ≤ f x` for some `c > 0` attains its global
minimum. -/
theorem exists_min_of_linear_lower_bound {f : E → ℝ} (hf : Continuous f) {c b : ℝ} (hc : 0 < c)
    (hb : ∀ x, c * ‖x‖ + b ≤ f x) : ∃ a, ∀ x, f a ≤ f x := by
  apply hf.exists_forall_le' (0 : E)
  filter_upwards [(isCompact_closedBall (0 : E) ((f 0 - b) / c)).compl_mem_cocompact] with x hx
  have hn : (f 0 - b) / c < ‖x‖ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hx
  have h := (div_lt_iff₀ hc).mp hn
  have hbound := hb x
  nlinarith

end LinearGrowth

end FunctionalInequalities.Analysis
