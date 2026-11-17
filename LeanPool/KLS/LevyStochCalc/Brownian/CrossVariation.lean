/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebra
public import LeanPool.KLS.LevyStochCalc.Brownian.CrossOrthogonality

/-!
# The cross-variation of Itô integrals against distinct coordinates

A coefficient measurable at the left endpoint of a cell, carried on that cell, is a simple
integrand, so multiplying an increment of an Itô integral by such a coefficient is again an Itô
integral. The product of increments against two distinct Brownian coordinates therefore pairs to
zero against every weight known at the left endpoint, which is to say it is conditionally
centred there.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section TwoCell

/-- The simple integrand carrying a coefficient on one cell `(a, b]` and nothing before it. -/
noncomputable def twoCell {a b : ℝ} (ha : 0 < a) (hab : a < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) : SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := rfl
  partition_le_T := le_rfl
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, Z]
  ξ_bounded := by
    intro i
    fin_cases i
    · exact ⟨0, fun ω => by simp⟩
    · exact ⟨M, hZb⟩
  ξ_measurable := by
    intro i
    fin_cases i
    · simp
    · simpa using hZm

theorem twoCell_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) (Z : Ω → ℝ) (hZm : Measurable Z)
    {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (s : ℝ) (ω : Ω) :
    (twoCell ha hab Z hZm hZb).eval s ω = if a < s ∧ s ≤ b then Z ω else 0 := by
  classical
  change (∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
        ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
      then (![fun _ : Ω => (0 : ℝ), Z] : Fin 2 → Ω → ℝ) i ω else 0)
    = if a < s ∧ s ≤ b then Z ω else 0
  rw [Fin.sum_univ_two]
  change (if (0 : ℝ) < s ∧ s ≤ a then (0 : ℝ) else 0)
      + (if a < s ∧ s ≤ b then Z ω else 0) = _
  by_cases h2 : a < s ∧ s ≤ b <;> simp [h2]

theorem twoCell_adapted {a b : ℝ} (ha : 0 < a) (hab : a < b) {Z : Ω → ℝ} (hZm : Measurable Z)
    {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (hZa : StronglyMeasurable[ℱ a] Z) :
    ∀ i : Fin (twoCell ha hab Z hZm hZb).N,
      StronglyMeasurable[ℱ ((twoCell ha hab Z hZm hZb).partition i.castSucc)]
        ((twoCell ha hab Z hZm hZb).ξ i) := by
  intro i
  fin_cases i
  · change StronglyMeasurable[ℱ 0] fun _ : Ω => (0 : ℝ)
    exact stronglyMeasurable_const
  · change StronglyMeasurable[ℱ a] Z
    exact hZa

theorem twoCell_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (twoCell ha hab Z hZm hZb).integralAgainst Y t ω
      = Z ω * (Y (min b t) ω - Y (min a t) ω) := by
  change (∑ i : Fin 2, (![fun _ : Ω => (0 : ℝ), Z] : Fin 2 → Ω → ℝ) i ω
      * (Y (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
        - Y (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω))
    = Z ω * (Y (min b t) ω - Y (min a t) ω)
  rw [Fin.sum_univ_two]
  simp

/-- The simple integrand carrying a coefficient on the single cell `(0, b]`. -/
noncomputable def oneCell {b : ℝ} (hb : 0 < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) : SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := rfl
  partition_le_T := le_rfl
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![Z]
  ξ_bounded := by
    intro i
    fin_cases i
    exact ⟨M, hZb⟩
  ξ_measurable := by
    intro i
    fin_cases i
    simpa using hZm

theorem oneCell_eval {b : ℝ} (hb : 0 < b) (Z : Ω → ℝ) (hZm : Measurable Z)
    {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (s : ℝ) (ω : Ω) :
    (oneCell hb Z hZm hZb).eval s ω = if 0 < s ∧ s ≤ b then Z ω else 0 := by
  classical
  change (∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
        ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
      then (![Z] : Fin 1 → Ω → ℝ) i ω else 0)
    = if 0 < s ∧ s ≤ b then Z ω else 0
  rw [Fin.sum_univ_one]
  simp

theorem oneCell_adapted {b : ℝ} (hb : 0 < b) {Z : Ω → ℝ} (hZm : Measurable Z)
    {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (hZ0 : StronglyMeasurable[ℱ 0] Z) :
    ∀ i : Fin (oneCell hb Z hZm hZb).N,
      StronglyMeasurable[ℱ ((oneCell hb Z hZm hZb).partition i.castSucc)]
        ((oneCell hb Z hZm hZb).ξ i) := by
  intro i
  fin_cases i
  change StronglyMeasurable[ℱ 0] Z
  exact hZ0

theorem oneCell_integralAgainst {b : ℝ} (hb : 0 < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (oneCell hb Z hZm hZb).integralAgainst Y t ω
      = Z ω * (Y (min b t) ω - Y (min 0 t) ω) := by
  change (∑ i : Fin 1, (![Z] : Fin 1 → Ω → ℝ) i ω
      * (Y (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
        - Y (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω))
    = Z ω * (Y (min b t) ω - Y (min 0 t) ω)
  rw [Fin.sum_univ_one]
  simp

end TwoCell

section PullOut

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- **A weight known at the left endpoint comes inside the integral.** For `Z` bounded and
measurable for `ℱ a`, the weighted increment of an Itô integral over `(a, b]` is the Itô integral
of `Z` carried on that cell against the integrand. -/
theorem mul_sub_stochasticIntegralBrownian_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) {Z : Ω → ℝ}
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) {t : ℝ} (hbt : b ≤ t) :
    (fun ω => Z ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (twoCell ha hab Z hZm hZb).eval s ω * H ω s)
        ((twoCell ha hab Z hZm hZb).measurable_uncurry_eval_mul hm)
        ((twoCell ha hab Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
          (twoCell_adapted ha hab hZm hZb hZa) hp)
        ((twoCell ha hab Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) t := by
  have ht : 0 < t := lt_of_lt_of_le (ha.trans hab) hbt
  have hkey := stochasticIntegralBrownian_integralAgainst W ℱ hℱ (twoCell ha hab Z hZm hZb)
    (twoCell_adapted ha hab hZm hZb hZa) H hm hp hq
    ((twoCell ha hab Z hZm hZb).measurable_uncurry_eval_mul hm)
    ((twoCell ha hab Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
      (twoCell_adapted ha hab hZm hZb hZa) hp)
    ((twoCell ha hab Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) ht
  refine Filter.EventuallyEq.trans ?_ hkey
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [twoCell_integralAgainst, min_eq_left hbt, min_eq_left (le_trans hab.le hbt)]

/-- The pull-out at the left end of the horizon, where the cell is `(0, b]`. -/
theorem mul_sub_stochasticIntegralBrownian_ae_zero {b : ℝ} (hb : 0 < b) {Z : Ω → ℝ}
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZ0 : StronglyMeasurable[ℱ 0] Z) {t : ℝ} (hbt : b ≤ t) :
    (fun ω => Z ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq 0 ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (oneCell hb Z hZm hZb).eval s ω * H ω s)
        ((oneCell hb Z hZm hZb).measurable_uncurry_eval_mul hm)
        ((oneCell hb Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
          (oneCell_adapted hb hZm hZb hZ0) hp)
        ((oneCell hb Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) t := by
  have ht : 0 < t := lt_of_lt_of_le hb hbt
  have hkey := stochasticIntegralBrownian_integralAgainst W ℱ hℱ (oneCell hb Z hZm hZb)
    (oneCell_adapted hb hZm hZb hZ0) H hm hp hq
    ((oneCell hb Z hZm hZb).measurable_uncurry_eval_mul hm)
    ((oneCell hb Z hZm hZb).progressivelyMeasurable_eval_mul ℱ
      (oneCell_adapted hb hZm hZb hZ0) hp)
    ((oneCell hb Z hZm hZb).lintegral_eval_mul_sq_lt_top hq) ht
  refine Filter.EventuallyEq.trans ?_ hkey
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [oneCell_integralAgainst, min_eq_left hbt, min_eq_left ht.le]

/-- **The weighted increment of an Itô integral is an Itô integral.** For `Z` bounded and
measurable for `ℱ a`, some admissible integrand has `Z · (M_b − M_a)` as its integral. -/
theorem exists_pullout_mul_sub_stochasticIntegralBrownian {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) {t : ℝ} (hbt : b ≤ t) :
    ∃ (G : Ω → ℝ → ℝ) (hGm : Measurable (Function.uncurry G))
      (hGp : Probability.ProgressivelyMeasurable ℱ G)
      (hGs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω => Z ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω))
        =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ G hGm hGp hGs t := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact ⟨_, _, _, _,
      mul_sub_stochasticIntegralBrownian_ae_zero W hℱ H hm hp hq hab hZm hZb hZa hbt⟩
  · exact ⟨_, _, _, _,
      mul_sub_stochasticIntegralBrownian_ae W hℱ H hm hp hq ha' hab hZm hZb hZa hbt⟩

end PullOut

section Cross

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- **The cross-variation pairs to zero against a weight known at the left endpoint.** For
distinct coordinates, the product of the increments of the two Itô integrals over a cell is
orthogonal to every bounded weight measurable at the cell's left endpoint. -/
theorem integral_mul_cross_increment_eq_zero {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {Z : Ω → ℝ} (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) :
    ∫ ω, Z ω * ((stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) ∂P = 0 := by
  have ht : (0 : ℝ) ≤ b := le_trans ha hab.le
  have hone : ∀ _ω : Ω, |(1 : ℝ)| ≤ 1 := fun _ => le_of_eq abs_one
  obtain ⟨G, hGm, hGp, hGs, h1⟩ := exists_pullout_mul_sub_stochasticIntegralBrownian
    (W.W i) (hcoord i) H hHm hHp hHs ha hab hZm hZb hZa (le_refl b)
  obtain ⟨G', hGm', hGp', hGs', h2⟩ := exists_pullout_mul_sub_stochasticIntegralBrownian
    (W.W j) (hcoord j) K hKm hKp hKs ha hab (Z := fun _ => (1 : ℝ)) measurable_const hone
    stronglyMeasurable_const (le_refl b)
  have hcross := MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero W hij hcoord
    hGm hGp hGs hGm' hGp' hGs' ht
  simp only [stochasticIntegral] at hcross
  refine Eq.trans ?_ hcross
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with ω e1 e2
  simp only [one_mul] at e2
  rw [← e1, ← e2]
  ring

/-- **The cross-variation is conditionally centred at the left endpoint.** The product of the
increments of the Itô integrals against two distinct coordinates has vanishing conditional
expectation at the left endpoint of the cell. -/
theorem condExp_mul_cross_increment_eq_zero {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    P[fun ω => (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω) | ℱ a]
      =ᵐ[P] 0 := by
  classical
  have hLi : ∀ u : ℝ,
      MemLp (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs u) 2 P :=
    fun u => (MeasureTheory.Lp.memLp _).ae_eq
      (stochasticIntegralBrownian_ae_eq (W.W i) ℱ (hcoord i) H hHm hHp hHs u).symm
  have hLj : ∀ u : ℝ,
      MemLp (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs u) 2 P :=
    fun u => (MeasureTheory.Lp.memLp _).ae_eq
      (stochasticIntegralBrownian_ae_eq (W.W j) ℱ (hcoord j) K hKm hKp hKs u).symm
  have hint : Integrable (fun ω =>
      (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) P :=
    MemLp.integrable_mul ((hLi b).sub (hLi a)) ((hLj b).sub (hLj a))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) hint
    (fun s _ _ => (integrable_zero Ω ℝ P).integrableOn) (fun s hs _ => ?_)
    (aestronglyMeasurable_const (b := (0 : ℝ)))).symm
  simp only [Pi.zero_apply, MeasureTheory.integral_zero]
  have hind : StronglyMeasurable[ℱ a] (s.indicator fun _ : Ω => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hs
  have hbd : ∀ ω : Ω, |s.indicator (fun _ : Ω => (1 : ℝ)) ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have hkey := integral_mul_cross_increment_eq_zero W hcoord hHm hHp hHs hKm hKp hKs hij
    ha hab (Z := s.indicator fun _ => (1 : ℝ))
    ((measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator (ℱ.le a s hs)) hbd hind
  refine (Eq.trans ?_ hkey).symm
  rw [← MeasureTheory.integral_indicator (ℱ.le a s hs)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ s <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]

end Cross

end LevyStochCalc.Brownian.Ito
