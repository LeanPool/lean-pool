/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.DecreasingNets
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicIntegrability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Local `L¹` convergence of actual decreasing nets

Existing main-branch ball-deficit estimates produce local integrability and
almost-everywhere finiteness. They are reused, rather than assumed as a PSH
certificate. Dominated convergence is applied only to the constructed actual
sequence, then pointwise order compares every later net index with a selected
sequence index. Thus the original directed set need not be countably cofinal.
-/

@[expose] public section

namespace SGPT.PSH

open Set Filter Metric MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
/-- The actual main-branch integrability locus gives finite values almost
everywhere on every compact subset of a preconnected source domain. -/
theorem PSHOn.ae_finite_on_compact {u : E → EReal} {U K : Set E}
    (hu : PSHOn u U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᵐ x ∂μ.restrict K, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  have hlocus := hu.disc.plurisubharmonicOn hU |>.subset_pshIntegrabilityLocus
    μ hconn hu.nontrivial
  refine IsCompact.induction_on hK (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ae_restrict_of_ae_restrict_of_subset hst ht
  · intro s t hs ht
    exact (ae_restrict_union_iff s t _).mpr ⟨hs, ht⟩
  · intro x hx
    obtain ⟨V, hV, hxV, hae, _⟩ := hlocus (hKU hx)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), hae⟩

/-- Genuine local `L¹` convergence of the original directed net on every
compact subset of a connected Euclidean source domain. Finiteness and local
integrability are produced by the existing ball-deficit theorem. No
countable cofinality of the original index preorder is assumed. -/
theorem tendsto_localL1_iInf {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → E → EReal} {U K : Set E}
    (hu : ∀ i, PSHOn (u i) U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hanti : ∀ x ∈ U, Antitone (fun i ↦ u i x))
    (hn : ∃ x ∈ U, (⨅ i, u i x) ≠ ⊥)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hK : IsCompact K) (hKU : K ⊆ U) :
    Tendsto (fun i ↦ ∫ x in K, ‖(u i x).toReal - (⨅ j, u j x).toReal‖ ∂μ)
      atTop (𝓝 0) := by
  let v : E → EReal := fun x ↦ ⨅ i, u i x
  have hv : PSHOn v U := pshOn_iInf_of_antitone hu hanti hn
  have hvI : IntegrableOn (fun x ↦ (v x).toReal) K μ :=
    (hv.disc.plurisubharmonicOn hU |>.locallyIntegrableOn_toReal μ hconn hv.nontrivial)
      |>.integrableOn_compact_subset hKU hK
  have hIu (i : I) : IntegrableOn (fun x ↦ (u i x).toReal) K μ :=
    ((hu i).disc.plurisubharmonicOn hU |>.locallyIntegrableOn_toReal
      μ hconn (hu i).nontrivial).integrableOn_compact_subset hKU hK
  have hfin := hv.ae_finite_on_compact hU hconn μ hK hKU
  have hmem : ∀ᵐ x ∂μ.restrict K, x ∈ U :=
    (ae_restrict_mem hK.measurableSet).mono hKU
  have hvle (x : E) (i : I) : v x ≤ u i x := iInf_le (fun i ↦ u i x) i
  have hbot (x : E) (hx : v x ≠ ⊥) (i : I) : u i x ≠ ⊥ := by
    intro hi
    exact hx (le_bot_iff.mp (by simpa only [hi] using hvle x i))
  have hreal_lower (x : E) (hxU : x ∈ U) (hx : v x ≠ ⊥) (i : I) :
      (v x).toReal ≤ (u i x).toReal :=
    EReal.toReal_le_toReal (hvle x i) hx ((hu i).disc.ne_top x hxU)
  have hreal_anti (x : E) (hxU : x ∈ U) (hx : v x ≠ ⊥) :
      Antitone (fun i ↦ (u i x).toReal) := by
    intro i j hij
    exact EReal.toReal_le_toReal (hanti x hxU hij) (hbot x hx j)
      ((hu i).disc.ne_top x hxU)
  obtain ⟨a, ha, heq⟩ := exists_monotone_subfamily_iInf
    (fun i (x : U) ↦ u i x)
    (fun i ↦ upperSemicontinuousOn_iff_restrict.mpr (hu i).disc.upperSemicontinuousOn)
    (fun x ↦ hanti x.1 x.2)
  have hseq : Tendsto (fun n ↦ ∫ x in K, ‖(u (a n) x).toReal - (v x).toReal‖ ∂μ)
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ x ∂μ.restrict K, Tendsto
        (fun n ↦ ‖(u (a n) x).toReal - (v x).toReal‖) atTop (𝓝 0) := by
      filter_upwards [hfin, hmem] with x hx hxU
      have hclim : Tendsto (fun n ↦ u (a n) x) atTop (𝓝 (v x)) := by
        change Tendsto (fun n ↦ u (a n) x) atTop (𝓝 (⨅ i, u i x))
        rw [← heq ⟨x, hxU⟩]
        exact tendsto_atTop_iInf (fun i j hij ↦ hanti x hxU (ha hij))
      simpa using ((EReal.tendsto_toReal hx.1 hx.2).comp hclim).sub
        (tendsto_const_nhds (x := (v x).toReal)) |>.norm
    have hbound (n : ℕ) : ∀ᵐ x ∂μ.restrict K,
        ‖‖(u (a n) x).toReal - (v x).toReal‖‖ ≤
          ‖(u (a 0) x).toReal‖ + ‖(v x).toReal‖ := by
      filter_upwards [hfin, hmem] with x hx hxU
      rw [norm_norm, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hreal_lower x hxU hx.2 (a n)))]
      have hh := hreal_anti x hxU hx.2 (ha (Nat.zero_le n))
      have h0 := le_abs_self (u (a 0) x).toReal
      have hv0 := neg_le_abs (v x).toReal
      simpa only [Real.norm_eq_abs] using (by linarith :
        (u (a n) x).toReal - (v x).toReal ≤
          |(u (a 0) x).toReal| + |(v x).toReal|)
    simpa using tendsto_integral_of_dominated_convergence
      (μ := μ.restrict K) (fun x ↦ ‖(u (a 0) x).toReal‖ + ‖(v x).toReal‖)
      (fun n ↦ ((hIu (a n)).sub hvI).norm.aestronglyMeasurable)
      ((hIu (a 0)).norm.add hvI.norm) hbound hlim
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall (fun i ↦ hr.trans_le (integral_nonneg (fun x ↦ norm_nonneg _)))
  · intro r hr
    obtain ⟨n, hn'⟩ := eventually_atTop.mp (hseq.eventually (gt_mem_nhds hr))
    have hn := hn' n le_rfl
    exact (eventually_ge_atTop (a n)).mono (fun i hi ↦ (integral_mono_ae
      ((hIu i).sub hvI).norm ((hIu (a n)).sub hvI).norm (by
        filter_upwards [hfin, hmem] with x hx hxU
        change ‖(u i x).toReal - (v x).toReal‖ ≤
          ‖(u (a n) x).toReal - (v x).toReal‖
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (hreal_lower x hxU hx.2 i)),
          abs_of_nonneg (sub_nonneg.mpr (hreal_lower x hxU hx.2 (a n)))]
        exact sub_le_sub_right (hreal_anti x hxU hx.2 hi) (v x).toReal)).trans_lt hn)

end SGPT.PSH
