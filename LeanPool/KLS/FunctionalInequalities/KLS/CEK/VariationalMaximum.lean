/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.Competitors
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Baseline
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Compactness
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.IsLUB

/-!
# CEK Proposition 12: variational attainment

Cordero-Erausquin–Klartag (arXiv:1304.0630v1), Proposition 12 (38): for a probability measure with
finite first
moment, barycenter zero and full-dimensional support, a convex lower semicontinuous admissible
potential with
Legendre exponential mass one maximizes the functional over every admissible competitor
(`exists_variational_maximum`). Not provided: essential continuity, the Euler–Lagrange
identification, Theorem 2.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.KLS.CEK

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

section
-- A normalized maximizing sequence.

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The actual normalized functional range has a finite real supremum and an
actual sequence of normalized potentials approaching it. No sequence, supremum
value, mass convergence or desired bound is supplied. -/
theorem exists_normalized_maximizing_sequence (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (φ : ℕ → E → EReal),
      (∀ j, ConvexPotential (φ j)) ∧ (∀ j, PotentialIntegrable (φ j) μ) ∧
      (∀ j x, 0 ≤ φ j x) ∧ (∀ j, φ j 0 = 0) ∧
      Tendsto (fun j => variationalFunctional dx μ (φ j)) atTop (𝓝 (S : EReal)) ∧
      ∀ ψ : E → EReal, ConvexPotential ψ → PotentialIntegrable ψ μ →
        (∀ x, 0 ≤ ψ x) → ψ 0 = 0 → variationalFunctional dx μ ψ ≤ (S : EReal) := by
  classical
  let N : Set ℝ := {r | ∃ φ : E → EReal,
    ConvexPotential φ ∧ PotentialIntegrable φ μ ∧ (∀ x, 0 ≤ φ x) ∧ φ 0 = 0 ∧
      variationalFunctional dx μ φ = (r : EReal)}
  obtain ⟨hNormConv, hNormPot, L, hL⟩ := norm_baseline_finite dx μ hfirst
  have hN : N.Nonempty := ⟨L, (fun x : E => (‖x‖ : EReal)), hNormConv, hNormPot,
    (fun x => EReal.coe_nonneg.mpr (norm_nonneg x)), (by simp), hL⟩
  obtain ⟨U, hU⟩ := exists_uniform_functional_upper dx μ hsub hfirst hbar
  have hNb : BddAbove N := by
    refine ⟨U, ?_⟩
    rintro r ⟨φ, _hc, hp, _hnn, _hzero, hr⟩
    have h := hU φ hp
    rw [hr] at h
    exact EReal.coe_le_coe_iff.mp h
  obtain ⟨u, _huMono, huT, huN⟩ := exists_seq_tendsto_sSup hN hNb
  have hw : ∀ j, ∃ φ : E → EReal,
      ConvexPotential φ ∧ PotentialIntegrable φ μ ∧ (∀ x, 0 ≤ φ x) ∧ φ 0 = 0 ∧
        variationalFunctional dx μ φ = (u j : EReal) := huN
  choose φ hconv hpot hnn hzero hval using hw
  refine ⟨sSup N, φ, hconv, hpot, hnn, hzero, ?_, ?_⟩
  · simpa only [hval] using EReal.tendsto_coe.mpr huT
  · intro ψ hc hp hnonneg hz
    by_cases hb : variationalFunctional dx μ ψ = ⊥
    · rw [hb]
      exact bot_le
    have ht : variationalFunctional dx μ ψ ≠ ⊤ :=
      ne_of_lt ((hU ψ hp).trans_lt (EReal.coe_lt_top U))
    lift variationalFunctional dx μ ψ to ℝ using ⟨ht, hb⟩ with r hr
    have hrN : r ∈ N := ⟨ψ, hc, hp, hnonneg, hz, hr.symm⟩
    exact EReal.coe_le_coe_iff.mpr (le_csSup hNb hrN)

end

section
-- Attainment of the variational maximum.

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- First extract an actual real-integral limit, then apply the actual full
Lemma17 to that same subsequence. Both limit inequalities and the composed
indices feed the independently rechecked actual extended-log limit helper. -/
theorem exists_limit_ge_normalized_supremum (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (ψ : E → EReal),
      ConvexPotential ψ ∧
        PotentialIntegrable ψ μ ∧
          (∀ x, 0 ≤ ψ x) ∧
            ψ 0 = 0 ∧
              0 < mass dx (legendre ψ) ∧
                mass dx (legendre ψ) ≠ ⊤ ∧
                  (S : EReal) ≤ variationalFunctional dx μ ψ ∧
                    ∀ η : E → EReal,
                      ConvexPotential η →
                        PotentialIntegrable η μ →
                          (∀ x, 0 ≤ η x) →
                            η 0 = 0 → variationalFunctional dx μ η ≤ (S : EReal) := by
  obtain ⟨S, φ, hconv, hpot, hnn, hzero, hF, hsup⟩ :=
    exists_normalized_maximizing_sequence dx μ hsub hfirstMoment hbar
  obtain ⟨B, _hB, hBphi, hbounded⟩ :=
    exists_integral_bound_of_tendsto_functional_above dx μ hsub hfirstMoment hbar φ hnn hzero
      hconv hpot (S : EReal) (S - 1) (EReal.coe_lt_coe_iff.mpr (by linarith)) hF
  have hmnn : ∀ j, 0 ≤ ∫ x, (φ j x).toReal ∂μ := fun j =>
    (lintegral_nonneg_potential (φ j) (hpot j) (hnn j)).2.2
  obtain ⟨M, _hM, t, ht, hmT⟩ :=
    isCompact_Icc.tendsto_subseq
      (fun j => (show (∫ x, (φ j x).toReal ∂μ) ∈ Icc 0 B from ⟨hmnn j, hBphi j⟩))
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp only [hz, FunLike.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have h0 :=
    FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero
      μ hμ hsub hfirstMoment hbar
  have hboundedT : (⨆ j, ∫⁻ x, (φ (t j) x).toENNReal ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hbounded
      (iSup_le fun j => le_iSup (fun k => ∫⁻ x, (φ k x).toENNReal ∂μ) (t j))
  obtain
    ⟨s, ψ, hs, hψnn, hψ0, hψconv, _hψmeas, _hpoint, _hrad, _hoff, hpψ, hZfin, hfirst,
      hsecond⟩ :=
    exists_subseq_integral_bounds_of_convex_epigraph dx μ h0 (fun j => φ (t j))
      (fun j => hnn (t j)) (fun j => hzero (t j)) (fun j => (hconv (t j)).2)
      (fun j => (lintegral_nonneg_potential (φ (t j)) (hpot (t j)) (hnn (t j))).1) hboundedT
  have hFts :
    Tendsto (fun j => variationalFunctional dx μ (φ (t (s j)))) atTop (𝓝 (S : EReal)) :=
    hF.comp (ht.tendsto_atTop.comp hs.tendsto_atTop)
  have hmts : Tendsto (fun j => ∫ x, (φ (t (s j)) x).toReal ∂μ) atTop (𝓝 M) :=
    hmT.comp hs.tendsto_atTop
  have hψlin := (lintegral_nonneg_potential ψ hpψ hψnn).2.1
  have hseqlin (j : ℕ) :=
    (lintegral_nonneg_potential (φ (t (s j))) (hpot (t (s j))) (hnn (t (s j)))).2.1
  have hfirstScalar :
    ENNReal.ofReal (∫ x, (ψ x).toReal ∂μ) ≤
      liminf (fun j => ENNReal.ofReal (∫ x, (φ (t (s j)) x).toReal ∂μ)) atTop := by
    simpa only [hψlin, hseqlin] using hfirst
  obtain ⟨hZpos, hvalue⟩ :=
    log_sub_ge_of_integral_limits (fun j => mass dx (legendre (φ (t (s j)))))
      (fun j => ∫ x, (φ (t (s j)) x).toReal ∂μ) (mass dx (legendre ψ)) (∫ x, (ψ x).toReal ∂μ) S
      M (fun j => hmnn (t (s j))) hFts hmts hfirstScalar hsecond
  exact
    ⟨S, ψ, ⟨fun x => ne_of_gt (EReal.bot_lt_zero.trans_le (hψnn x)), hψconv⟩, hpψ, hψnn, hψ0,
      hZpos, hZfin, hvalue, hsup⟩
/-- **CEK Proposition12 (38).** Actual variational attainment for every
admissible competitor, with an actual convex lsc admissible witness whose
Legendre exponential mass is1. Original measure hypotheses only; neither a
maximizing sequence, convergence, desired bound nor maximizer is supplied. -/
theorem exists_variational_maximum (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ φ : E → EReal,
      ConvexPotential φ ∧
        LowerSemicontinuous φ ∧
          PotentialIntegrable φ μ ∧
            mass dx (legendre φ) = 1 ∧
              ∀ f : E → EReal,
                PotentialIntegrable f μ →
                  variationalFunctional dx μ f ≤ variationalFunctional dx μ φ := by
  obtain ⟨S, ψ, _hψconv, hpψ, hψnn, hψ0, hZpos, hZfin, hS, hnormSup⟩ :=
    exists_limit_ge_normalized_supremum dx μ hsub hfirstMoment hbar
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp only [hz, FunLike.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have htr : lowerTruncate ψ 0 = ψ := by
    funext x
    simpa only [lowerTruncate, neg_zero, EReal.coe_zero] using max_eq_left (hψnn x)
  have hwit : ∃ x, ψ x ≠ ⊤ := ⟨0, by rw [hψ0]; exact EReal.zero_ne_top⟩
  obtain ⟨hc, _hclsc, _hproper, _hbounds, hdual⟩ := lowerTruncate_convexification ψ 0 hwit
  have hpc := biconjugate_lowerTruncate_potentialIntegrable ψ 0 hμ hpψ
  have hint := integral_biconjugate_lowerTruncate_le ψ 0 hμ hpψ
  simp only [htr] at hc hdual hpc hint
  let c : E → EReal := legendre (legendre ψ)
  have hdualfun : legendre c = legendre ψ := funext hdual
  have hmass : mass dx (legendre c) = mass dx (legendre ψ) := congrArg (mass dx) hdualfun
  have hZcpos : 0 < mass dx (legendre c) := by rw [hmass]; exact hZpos
  have hZcfin : mass dx (legendre c) ≠ ⊤ := by rw [hmass]; exact hZfin
  have hIc : variationalFunctional dx μ ψ ≤ variationalFunctional dx μ c := by
    unfold variationalFunctional
    rw [hmass]
    exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr hint)
  let V : ℝ := Real.log (mass dx (legendre c)).toReal - ∫ x, (c x).toReal ∂μ
  have hV : variationalFunctional dx μ c = (V : EReal) := by
    unfold variationalFunctional
    rw [ENNReal.log_pos_real hZcpos.ne' hZcfin, ← EReal.coe_sub]
  have hmax :
    ∀ f : E → EReal,
      PotentialIntegrable f μ → variationalFunctional dx μ f ≤ variationalFunctional dx μ c := by
    intro f hf
    have heps : ∀ ε : ℝ, 0 < ε → variationalFunctional dx μ f ≤ ((V + ε : ℝ) : EReal) := by
      intro ε hε
      obtain ⟨η, hcη, hpη, hnnη, hzη, hvalue⟩ :=
        exists_normalized_competitor dx μ hsub hfirstMoment hbar f hf ε hε
      have hη := (hnormSup η hcη hpη hnnη hzη).trans (hS.trans hIc)
      rw [hV] at hη
      simpa only [EReal.coe_add] using hvalue.trans (add_le_add hη (le_refl (ε : EReal)))
    rw [hV]
    have ht : Tendsto (fun ε : ℝ => ((V + ε : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (V : EReal)) := by
      have hcont : Continuous (fun ε : ℝ => ((V + ε : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp (continuous_const.add continuous_id)
      simpa only [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact heps ε hε
  let b : ℝ := Real.log (mass dx (legendre c)).toReal
  let φ := affineSubtract c 0 b
  have hpφ : PotentialIntegrable φ μ :=
    affineSubtract_potentialIntegrable c 0 b hpc hfirstMoment
  have hcφ : ConvexPotential φ := ⟨hpφ.1, convex_epigraph_affineSubtract c 0 b hc.2⟩
  have hlsφ : LowerSemicontinuous φ := by
    have heq : φ = legendre (affineSubtract (legendre ψ) 0 (-b)) := by
      funext x
      rw [legendre_affineSubtract]
      simp only [φ, c, affineSubtract, inner_zero_left, zero_add, add_zero, EReal.coe_neg,
        sub_eq_add_neg]
    rw [heq]
    exact lowerSemicontinuous_legendre _
  have hmassφ : mass dx (legendre φ) = 1 := by
    apply ENNReal.log_injective
    rw [log_mass_legendre_affineSubtract dx c 0 b, ENNReal.log_pos_real hZcpos.ne' hZcfin]
    change ((b : EReal) - (b : EReal)) = ENNReal.log 1
    rw [← EReal.coe_sub, sub_self, EReal.coe_zero, ENNReal.log_one]
  have hIφ : variationalFunctional dx μ φ = variationalFunctional dx μ c :=
    variationalFunctional_affineSubtract dx c 0 b hpc hfirstMoment hbar
  refine ⟨φ, hcφ, hlsφ, hpφ, hmassφ, ?_⟩
  intro f hf
  rw [hIφ]
  exact hmax f hf

end

end FunctionalInequalities.KLS.CEK
