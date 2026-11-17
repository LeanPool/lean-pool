/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.CrossOrthogonalityDirectCross

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

/-- Clamping an interval to `(-∞, t]` either collapses it or leaves its left endpoint alone. -/
lemma min_eq_or_lt_min {p q : ℝ} (h : p < q) (t : ℝ) :
    min p t = min q t ∨ (min p t = p ∧ p < min q t) := by
  rcases lt_or_ge t q with htq | hqt
  · rcases lt_or_ge p t with hpt | htp
    · exact Or.inr ⟨min_eq_left hpt.le, by rw [min_eq_right htq.le]; exact hpt⟩
    · exact Or.inl (by rw [min_eq_right htp, min_eq_right htq.le])
  · exact Or.inr ⟨min_eq_left (h.le.trans hqt), by rw [min_eq_left hqt]; exact h⟩

/-- The square of a Brownian increment over a possibly degenerate interval is integrable. -/
lemma integrable_increment_sq (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    Integrable (fun ω => (V.W q ω - V.W p ω) ^ 2) P := by
  rcases eq_or_lt_of_le hpq with h | h
  · have hz : (fun ω => (V.W q ω - V.W p ω) ^ 2) = fun _ => (0 : ℝ) := by
      funext ω; rw [← h]; simp
    rw [hz]
    exact integrable_zero Ω ℝ P
  · exact brownian_increment_sq_integrable V hp h

/-- A product of two bounded coefficients and two Brownian increments is integrable. -/
lemma integrable_cross_term (V₁ V₂ : BrownianMotion P) {p q r v : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hr : 0 ≤ r) (hrv : r ≤ v) {ξ η : Ω → ℝ} (hξm : Measurable ξ) (hηm : Measurable η)
    {Mξ Mη : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω))
      * (η ω * (V₂.W v ω - V₂.W r ω))) P := by
  have hm1 : Measurable fun ω => V₁.W q ω - V₁.W p ω :=
    (V₁.measurable_eval q).sub (V₁.measurable_eval p)
  have hm2 : Measurable fun ω => V₂.W v ω - V₂.W r ω :=
    (V₂.measurable_eval v).sub (V₂.measurable_eval r)
  have hprod : Integrable (fun ω => (V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) P := by
    have hdom : Integrable (fun ω => 1 / 2 * (V₁.W q ω - V₁.W p ω) ^ 2
        + 1 / 2 * (V₂.W v ω - V₂.W r ω) ^ 2) P :=
      ((integrable_increment_sq V₁ hp hpq).const_mul (1 / 2 : ℝ)).add
        ((integrable_increment_sq V₂ hr hrv).const_mul (1 / 2 : ℝ))
    refine Integrable.mono' hdom (hm1.mul hm2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (V₁.W q ω - V₁.W p ω), sq_abs (V₂.W v ω - V₂.W r ω),
      sq_nonneg (|V₁.W q ω - V₁.W p ω| - |V₂.W v ω - V₂.W r ω|)]
  have heq : (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω)) * (η ω * (V₂.W v ω - V₂.W r ω)))
      = fun ω => (ξ ω * η ω) * ((V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) := by
    funext ω; ring
  rw [heq]
  refine Integrable.bdd_mul (c := |Mξ| * |Mη|) hprod (hξm.mul hηm).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- **The cross term vanishes, when the `Wʲ` interval starts last.** -/
theorem integral_cross_increment_eq_zero_of_le (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  have hΔ : ∀ (V : BrownianMotion P) (x y : ℝ), Measurable fun ω => V.W y ω - V.W x ω :=
    fun V x y => (V.measurable_eval y).sub (V.measurable_eval x)
  have hΔℱ : ∀ (k : Fin d) {x y s : ℝ}, x ≤ s → y ≤ s →
      Measurable[ℱ s] fun ω => (W.W k).W y ω - (W.W k).W x ω := fun k x y s hxs hys =>
    (((hcoord k).measurable y).mono (ℱ.mono hys) le_rfl).sub
      (((hcoord k).measurable x).mono (ℱ.mono hxs) le_rfl)
  have hξη : StronglyMeasurable[ℱ r] fun ω => ξ ω * η ω := (hξ.mono (ℱ.mono hpr)).mul hη
  have hξηb : ∀ ω, |ξ ω * η ω| ≤ |Mξ| * |Mη| := fun ω => by
    rw [abs_mul]
    exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  rcases le_or_gt q r with hqr | hrq
  · -- the `Wⁱ` increment is already known at time `r`
    have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W p ω) * η ω :=
      ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr hqr).stronglyMeasurable).mul hη
    have h := integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
      ((hξm.mul (hΔ (W.W i) p q)).mul hηm)
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- split the `Wⁱ` increment at `r`
    have hsplit : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
          * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
        = fun ω => (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω))
          + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) := by
      funext ω; ring
    rw [hsplit,
      integral_add (integrable_cross_term (W.W i) (W.W j) hp hpr hr hrv.le hξm hηm hξb hηb)
        (integrable_cross_term (W.W i) (W.W j) hr hrq.le hr hrv.le hξm hηm hξb hηb)]
    have h1 : ∫ ω, (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
        * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
      have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W r ω - (W.W i).W p ω) * η ω :=
        ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr le_rfl).stronglyMeasurable).mul hη
      have h := integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
        ((hξm.mul (hΔ (W.W i) p r)).mul hηm)
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, zero_add]
    -- both increments now start at `r`
    rcases lt_trichotomy q v with hqv | rfl | hvq
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))
            + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
                * ((W.W j).W v ω - (W.W j).W q ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))) P := by
        have := integrable_cross_term (W.W i) (W.W j) hr hrq.le hr hrq.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          * ((W.W j).W v ω - (W.W j).W q ω)) P := by
        have := integrable_cross_term (W.W i) (W.W j) hr hrq.le (hr.trans hrq.le) hqv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        integral_mul_increment_mul_increment_eq_zero W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb,
        integral_mul_increment_eq_zero (W.W j) (hcoord j) (hr.trans hrq.le) hqv
          (Y := fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          (((hξ.mono (ℱ.mono (hpr.trans hrq.le))).mul
            (hΔℱ i hrq.le le_rfl).stronglyMeasurable).mul (hη.mono (ℱ.mono hrq.le)))
          ((hξm.mul (hΔ (W.W i) r q)).mul hηm), add_zero]
    · have heq : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W q ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
              * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω)) := by
        funext ω; ring
      rw [heq]
      exact integral_mul_increment_mul_increment_eq_zero W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))
            + (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
                * ((W.W i).W q ω - (W.W i).W v ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))) P := by
        have := integrable_cross_term (W.W i) (W.W j) hr hrv.le hr hrv.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          * ((W.W i).W q ω - (W.W i).W v ω)) P := by
        have := integrable_cross_term (W.W i) (W.W j) (hr.trans hrv.le) hvq.le hr hrv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        integral_mul_increment_mul_increment_eq_zero W hij hcoord hr hrv hξη (hξm.mul hηm) hξηb,
        integral_mul_increment_eq_zero (W.W i) (hcoord i) (hr.trans hrv.le) hvq
          (Y := fun ω => ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          (((hξ.mono (ℱ.mono (hpr.trans hrv.le))).mul (hη.mono (ℱ.mono hrv.le))).mul
            (hΔℱ j hrv.le le_rfl).stronglyMeasurable)
          ((hξm.mul hηm).mul (hΔ (W.W j) r v)), add_zero]

/-- **The cross term vanishes.** For distinct coordinates the two increments are uncorrelated
against bounded coefficients measurable at the left endpoints, in either order. -/
theorem integral_cross_increment_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpq : p < q) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  rcases le_or_gt p r with hpr | hrp
  · exact integral_cross_increment_eq_zero_of_le W hij hcoord hp hr hrv hpr hξ hξm hξb hη hηm hηb
  · have h := integral_cross_increment_eq_zero_of_le W hij.symm hcoord (q := v) hr hp hpq hrp.le
      hη hηm hηb hξ hξm hξb
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

/-- A single clamped cross term is integrable and has zero mean. -/
lemma integrable_and_integral_cross_clamped (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hpq : p < q)
    (hr : 0 ≤ r) (hrv : r < v) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) P
    ∧ ∫ ω, (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω)) ∂P = 0 := by
  rcases min_eq_or_lt_min hpq t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
        * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
  · rcases min_eq_or_lt_min hrv t' with hc' | ⟨hre, hrlt⟩
    · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
          * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
        funext ω; rw [hc']; ring
      rw [hz]
      exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
    · rw [hpe, hre]
      exact ⟨integrable_cross_term (W.W i) (W.W j) hp hplt.le hr hrlt.le hξm hηm hξb hηb,
        integral_cross_increment_eq_zero W hij hcoord hp hr hrlt hplt hξ hξm hξb hη hηm hηb⟩

/-- **Orthogonality on simple integrands.** Elementary integrals against distinct Brownian
coordinates have zero pairing, at any pair of times. -/
theorem integral_simpleIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {TH TK : ℝ}
    (H : SimplePredictable Ω TH)
    (K : SimplePredictable Ω TK)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    (hK : ∀ b : Fin K.N, StronglyMeasurable[ℱ (K.partition b.castSucc)] (K.ξ b))
    (t t' : ℝ) :
    ∫ ω, simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω ∂P = 0 := by
  have hHnn : ∀ a : Fin H.N, 0 ≤ H.partition a.castSucc := fun a => by
    have h := H.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [H.partition_zero] at h
  have hKnn : ∀ b : Fin K.N, 0 ≤ K.partition b.castSucc := fun b => by
    have h := K.partition_strictMono.monotone (Fin.zero_le b.castSucc)
    rwa [K.partition_zero] at h
  have hHlt : ∀ a : Fin H.N, H.partition a.castSucc < H.partition a.succ := fun a =>
    H.partition_strictMono Fin.castSucc_lt_succ
  have hKlt : ∀ b : Fin K.N, K.partition b.castSucc < K.partition b.succ := fun b =>
    K.partition_strictMono Fin.castSucc_lt_succ
  have key : ∀ (a : Fin H.N) (b : Fin K.N),
      Integrable (fun ω => (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω))) P
      ∧ ∫ ω, (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) ∂P = 0 := by
    intro a b
    obtain ⟨Mξ, hMξ⟩ := H.ξ_bounded a
    obtain ⟨Mη, hMη⟩ := K.ξ_bounded b
    exact integrable_and_integral_cross_clamped W hij hcoord (hHnn a) (hHlt a) (hKnn b) (hKlt b)
      (hH a) (H.ξ_measurable a) hMξ (hK b) (K.ξ_measurable b) hMη t t'
  have hexp : (fun ω => simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω)
      = fun ω => ∑ a : Fin H.N, ∑ b : Fin K.N,
        (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) := by
    funext ω
    rw [simpleIntegral, simpleIntegral]
    exact Finset.sum_mul_sum _ _ _ _
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (key a b).1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (key a b).1]
  exact Finset.sum_eq_zero fun b _ => (key a b).2

end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

/-- An elementary integral is square-integrable at every time. -/
lemma memLp_simpleIntegral (V : BrownianMotion P) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) :
    MemLp (fun ω => simpleIntegral V G t ω) 2 P := by
  have hnn : ∀ a : Fin G.N, 0 ≤ G.partition a.castSucc := fun a => by
    have h := G.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [G.partition_zero] at h
  have hlt : ∀ a : Fin G.N, G.partition a.castSucc < G.partition a.succ := fun a =>
    G.partition_strictMono Fin.castSucc_lt_succ
  have hrw : (fun ω => simpleIntegral V G t ω) = fun ω => ∑ a : Fin G.N,
      G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω) := rfl
  rw [hrw]
  refine memLp_finsetSum (f := fun (a : Fin G.N) ω => G.ξ a ω
    * (V.W (min (G.partition a.succ) t) ω - V.W (min (G.partition a.castSucc) t) ω))
    Finset.univ fun a _ => ?_
  rcases min_eq_or_lt_min (hlt a) t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω)) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact memLp_const 0
  · obtain ⟨M, hM⟩ := G.ξ_bounded a
    rw [hpe]
    exact memLp_mul_increment V (hnn a) hplt 2 (by simp) (G.ξ_measurable a) hM

omit [IsProbabilityMeasure P] in
/-- The `L²` inner product of two `Lp` representatives is the integral of their product. -/
lemma inner_toLp_eq_integral_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (inner ℝ (hf.toLp f) (hg.toLp g) : ℝ) = ∫ ω, f ω * g ω ∂P := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [RCLike.inner_apply, h1, h2]
  simp [mul_comm]

omit [IsProbabilityMeasure P] in
/-- The `L²` pairing is continuous, so a pairing that vanishes along `L²`-convergent sequences
vanishes in the limit. -/
theorem integral_mul_eq_zero_of_tendsto_eLpNorm {u v : Ω → ℝ} {un vn : ℕ → Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hun : ∀ n, MemLp (un n) 2 P) (hvn : ∀ n, MemLp (vn n) 2 P)
    (h0 : ∀ n, ∫ ω, un n ω * vn n ω ∂P = 0)
    (hcu : Filter.Tendsto (fun n => eLpNorm (fun ω => un n ω - u ω) 2 P) Filter.atTop (nhds 0))
    (hcv : Filter.Tendsto (fun n => eLpNorm (fun ω => vn n ω - v ω) 2 P) Filter.atTop (nhds 0)) :
    ∫ ω, u ω * v ω ∂P = 0 := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hUn : Filter.Tendsto (fun n => (hun n).toLp (un n)) Filter.atTop (nhds (hu.toLp u)) := by
    rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm _ u hu]
    have heq : ∀ n, eLpNorm (⇑((hun n).toLp (un n)) - u) 2 P
        = eLpNorm (fun ω => un n ω - u ω) 2 P := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hun n).coeFn_toLp] with ω h
      simp [h]
    simp_rw [heq]
    exact hcu
  have hVn : Filter.Tendsto (fun n => (hvn n).toLp (vn n)) Filter.atTop (nhds (hv.toLp v)) := by
    rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm _ v hv]
    have heq : ∀ n, eLpNorm (⇑((hvn n).toLp (vn n)) - v) 2 P
        = eLpNorm (fun ω => vn n ω - v ω) 2 P := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hvn n).coeFn_toLp] with ω h
      simp [h]
    simp_rw [heq]
    exact hcv
  have hinner : Filter.Tendsto
      (fun n => (inner ℝ ((hun n).toLp (un n)) ((hvn n).toLp (vn n)) : ℝ)) Filter.atTop
      (nhds (inner ℝ (hu.toLp u) (hv.toLp v) : ℝ)) := hUn.inner hVn
  have hzero : ∀ n, (inner ℝ ((hun n).toLp (un n)) ((hvn n).toLp (vn n)) : ℝ) = 0 := fun n => by
    rw [inner_toLp_eq_integral_mul (hun n) (hvn n)]; exact h0 n
  simp_rw [hzero] at hinner
  have hlim := tendsto_nhds_unique tendsto_const_nhds hinner
  rw [inner_toLp_eq_integral_mul hu hv] at hlim
  exact hlim.symm

/-- **Orthogonality of Itô integrals against distinct Brownian coordinates.** -/
theorem integral_stochasticIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t ω
      * stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t ω ∂P = 0 := by
  have hui : MemLp (stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (stochasticIntegralBrownian_ae_eq (W.W i)
      ℱ (hcoord i) H hHm hHp hHs t).symm
  have huj : MemLp (stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (stochasticIntegralBrownian_ae_eq (W.W j)
      ℱ (hcoord j) K hKm hKp hKs t).symm
  refine integral_mul_eq_zero_of_tendsto_eLpNorm
    (un := fun n ω => simpleIntegral (W.W i) (masterApprox ℱ H hHm hHp hHs n) t ω)
    (vn := fun n ω => simpleIntegral (W.W j) (masterApprox ℱ K hKm hKp hKs n) t ω)
    hui huj (fun n => memLp_simpleIntegral _ _ t) (fun n => memLp_simpleIntegral _ _ t)
    (fun n => integral_simpleIntegral_mul_eq_zero W hij hcoord _ _
      (masterApprox_adapt ℱ H hHm hHp hHs n)
      (masterApprox_adapt ℱ K hKm hKp hKs n) t t)
    (masterApprox_tendsto_L2 (W.W i) ℱ (hcoord i) H hHm hHp hHs ht)
    (masterApprox_tendsto_L2 (W.W j) ℱ (hcoord j) K hKm hKp hKs ht)

end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian
