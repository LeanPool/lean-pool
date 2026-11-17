/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Bases

/-!
# Pointwise compactness of bounded convex functions

A sequence of nonnegative real convex functions on an open set `K` of a finite-dimensional real
normed space, bounded at
every point of `K`, has one strictly increasing subsequence converging at every point of `K`, and
the limit is convex on
`K` (`exists_subseq_tendsto_of_convexOn_of_bddAbove`; `K = ∅` allowed). This is the case of
Rockafellar, *Convex Analysis*,
Theorem 10.9, used in the proof of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1),
Lemma 17.

Proof: the pointwise supremum is convex and finite on `K`, hence locally bounded, giving common
local Lipschitz bounds; a
subsequence converges on a countable dense subset (one diagonal extraction over `ℕ` coordinates) and
the convergence extends
to all of `K` by the Cauchy criterion; convexity passes to the limit. Four private helpers.

Section `LinearBounds`: convex functions on a finite-dimensional real normed space with uniform
two-sided linear
bounds `α‖x‖ − β ≤ ψ_l(x) ≤ L‖x‖ + γ`, `α ≥ 0`, have a subsequence converging pointwise on the whole
space to a convex
function (`exists_subseq_tendsto_of_linear_bounds`), as used in Klartag, *Logarithmically-concave
moment measures I*
(arXiv:1309.2767v1), Proposition 2.1.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

section NormedSpace

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem convexOn_pointwise_sup
    {K : Set E} (f : ℕ → E → ℝ) (hf : ∀ n, ConvexOn ℝ K (f n))
    (hbdd : ∀ x ∈ K, BddAbove (Set.range fun n => f n x)) :
    ConvexOn ℝ K (fun x => sSup (Set.range fun n => f n x)) := by
  refine ⟨(hf 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  calc
    f n (a • x + b • y) ≤ a • f n x + b • f n y := (hf n).2 hx hy ha hb hab
    _ ≤ a • sSup (Set.range fun n => f n x) + b • sSup (Set.range fun n => f n y) := by
      simpa only [smul_eq_mul] using add_le_add
        (mul_le_mul_of_nonneg_left (le_csSup (hbdd x hx) (Set.mem_range_self n)) ha)
        (mul_le_mul_of_nonneg_left (le_csSup (hbdd y hy) (Set.mem_range_self n)) hb)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private theorem exists_uniform_local_lipschitz {K : Set E} (hK : IsOpen K)
    (f : ℕ → E → ℝ) (hf : ∀ n, ConvexOn ℝ K (f n))
    (hnn : ∀ n, ∀ x ∈ K, 0 ≤ f n x)
    (hbdd : ∀ x ∈ K, BddAbove (Set.range fun n => f n x)) {x : E} (hx : x ∈ K) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ K ∧
      ∃ L : NNReal, ∀ n, LipschitzOnWith L (f n) (Metric.ball x r) := by
  let F : E → ℝ := fun y => sSup (Set.range fun n => f n y)
  have hF : ConvexOn ℝ K F := convexOn_pointwise_sup f hf hbdd
  have hcont : ContinuousOn F K := hF.continuousOn hK
  have hopen : IsOpen (K ∩ F ⁻¹' Set.Iio (F x + 1)) :=
    hcont.isOpen_inter_preimage hK isOpen_Iio
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨hx, by simp⟩
  have hbK : Metric.ball x r ⊆ K := fun y hy => (hball hy).1
  refine ⟨r / 2, by positivity, ?_, (2 * (F x + 1) / (r / 2)).toNNReal, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans hbK
  · intro n
    have hc : ConvexOn ℝ (Metric.ball x r) (f n) := (hf n).subset hbK (convex_ball x r)
    have hbound : ∀ y, dist y x < r → |f n y| ≤ F x + 1 := by
      intro y hy
      have hyK := hbK hy
      rw [abs_of_nonneg (hnn n y hyK)]
      exact (le_csSup (hbdd y hyK) (Set.mem_range_self n)).trans (hball hy).2.le
    have h := hc.lipschitzOnWith_of_abs_le (by positivity : 0 < r / 2) hbound
    have hradius : r - r / 2 = r / 2 := by ring
    simpa only [hradius] using h

private theorem exists_subseq_pointwise_on_nat (f : ℕ → ℕ → ℝ)
    (hnn : ∀ n i, 0 ≤ f n i)
    (hbdd : ∀ i, BddAbove (Set.range fun n => f n i)) :
    ∃ (s : ℕ → ℕ) (g : ℕ → ℝ), StrictMono s ∧
      ∀ i, Filter.Tendsto (fun n => f (s n) i) Filter.atTop (nhds (g i)) := by
  classical
  choose B hB using hbdd
  have hcompact : IsCompact {g : ℕ → ℝ | ∀ i, g i ∈ Set.Icc 0 (B i)} :=
    isCompact_pi_infinite (fun i => isCompact_Icc)
  have hmem : ∀ n, f n ∈ {g : ℕ → ℝ | ∀ i, g i ∈ Set.Icc 0 (B i)} := by
    intro n i
    exact ⟨hnn n i, hB i (Set.mem_range_self n)⟩
  obtain ⟨g, _, s, hs, hlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨s, g, hs, ?_⟩
  intro i
  exact (tendsto_pi_nhds.mp hlim) i

private theorem cauchy_at_point_of_dense_local_lipschitz {E : Type*} [PseudoMetricSpace E]
    {K : Set E} (f : ℕ → E → ℝ) (d : ℕ → E)
    (hd : ∀ x ∈ K, ∀ ε > (0 : ℝ), ∃ i, dist x (d i) < ε)
    (hc : ∀ i, CauchySeq (fun n => f n (d i)))
    {x : E} (hx : x ∈ K) (r : ℝ) (hr : 0 < r) (L : NNReal)
    (hL : ∀ n, LipschitzOnWith L (f n) (Metric.ball x r)) :
    CauchySeq (fun n => f n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hA : 0 < (L : ℝ) + 1 := by positivity
  have hδ : 0 < min r ((ε / 3) / ((L : ℝ) + 1)) := by positivity
  obtain ⟨i, hi⟩ := hd x hx _ hδ
  have hyr : d i ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_comm]
    exact hi.trans_le (min_le_left _ _)
  have hxy : ((L : ℝ) + 1) * dist x (d i) < ε / 3 := by
    have ht := hi.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ hA).mp ht
    nlinarith
  have hxball : x ∈ Metric.ball x r := by simpa using hr
  have hside : ∀ n, dist (f n x) (f n (d i)) < ε / 3 := by
    intro n
    have hbound := (hL n).dist_le_mul x hxball (d i) hyr
    have hmul : (L : ℝ) * dist x (d i) ≤ ((L : ℝ) + 1) * dist x (d i) := by
      nlinarith [show 0 ≤ dist x (d i) from dist_nonneg]
    exact hbound.trans_lt (hmul.trans_lt hxy)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hc i) (ε / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmxy := hside m
  have hnxy := hside n
  have hmid := hN m hm n hn
  have htri := dist_triangle (f m x) (f m (d i)) (f n x)
  have htri' := dist_triangle (f m (d i)) (f n (d i)) (f n x)
  rw [dist_comm (f n (d i)) (f n x)] at htri'
  linarith

/--
Nonnegative convex functions on an open set, bounded at every point, have a subsequence converging
at every point of
the set to a convex function. -/
theorem exists_subseq_tendsto_of_convexOn_of_bddAbove {K : Set E} (hK : IsOpen K)
    (f : ℕ → E → ℝ) (hf : ∀ ℓ, ConvexOn ℝ K (f ℓ)) (hnn : ∀ ℓ, ∀ x ∈ K, 0 ≤ f ℓ x)
    (hbdd : ∀ x ∈ K, BddAbove (Set.range fun ℓ => f ℓ x)) :
    ∃ (s : ℕ → ℕ) (g : E → ℝ),
      StrictMono s ∧
        ConvexOn ℝ K g ∧
          ∀ x ∈ K, Filter.Tendsto (fun j => f (s j) x) Filter.atTop (nhds (g x)) := by
  classical
  by_cases hne : K.Nonempty
  · let : Nonempty K := hne.to_subtype
    let d₀ : ℕ → K := TopologicalSpace.denseSeq K
    let d : ℕ → E := fun i => d₀ i
    have hd : ∀ x ∈ K, ∀ ε > (0 : ℝ), ∃ i, dist x (d i) < ε := by
      intro x hx ε hε
      obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq K).exists_dist_lt (⟨x, hx⟩ : K) hε
      exact ⟨i, hi⟩
    obtain ⟨s, g₀, hs, hlim₀⟩ :=
      exists_subseq_pointwise_on_nat (fun n i => f n (d i))
        (fun n i => hnn n (d i) (d₀ i).property) (fun i => hbdd (d i) (d₀ i).property)
    have hc : ∀ x ∈ K, CauchySeq (fun n => f (s n) x) := by
      intro x hx
      obtain ⟨r, hr, _, L, hL⟩ := exists_uniform_local_lipschitz hK f hf hnn hbdd hx
      exact
        cauchy_at_point_of_dense_local_lipschitz (fun n => f (s n)) d hd
          (fun i => (hlim₀ i).cauchySeq) hx r hr L (fun n => hL (s n))
    let g : E → ℝ := fun x => Filter.limUnder Filter.atTop (fun n => f (s n) x)
    have hlim : ∀ x ∈ K, Filter.Tendsto (fun n => f (s n) x) Filter.atTop (nhds (g x)) :=
      fun x hx => (hc x hx).tendsto_limUnder
    refine ⟨s, g, hs, ⟨(hf 0).1, ?_⟩, hlim⟩
    intro x hx y hy a b ha hb hab
    have hxy : a • x + b • y ∈ K := (hf 0).1 hx hy ha hb hab
    apply
      le_of_tendsto_of_tendsto (hlim _ hxy)
        (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b))
    exact Filter.Eventually.of_forall fun n => (hf (s n)).2 hx hy ha hb hab
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    refine ⟨id, fun _ => 0, strictMono_id, convexOn_const 0 convex_empty, ?_⟩
    simp

end FiniteDimensional

end NormedSpace

section LinearBounds

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Convex functions with uniform two-sided linear bounds have a subsequence converging pointwise
to a convex function. -/
theorem exists_subseq_tendsto_of_linear_bounds {ψ : ℕ → E → ℝ} {α β γ L : ℝ}
    (hψ : ∀ l, ConvexOn ℝ univ (ψ l)) (hα : 0 ≤ α)
    (hb : ∀ l x, α * ‖x‖ - β ≤ ψ l x ∧ ψ l x ≤ L * ‖x‖ + γ) :
    ∃ (s : ℕ → ℕ) (F : E → ℝ), StrictMono s ∧ ConvexOn ℝ univ F ∧
      ∀ x, Tendsto (fun j => ψ (s j) x) atTop (𝓝 (F x)) := by
  let f : ℕ → E → ℝ := fun l x => ψ l x + β
  have hf : ∀ l, ConvexOn ℝ univ (f l) := by
    intro l
    exact (hψ l).add_const β
  have hnn : ∀ l, ∀ x ∈ (univ : Set E), 0 ≤ f l x := by
    intro l x _
    dsimp [f]
    have hmul := mul_nonneg hα (norm_nonneg x)
    have hlo := (hb l x).1
    linarith
  have hbdd : ∀ x ∈ (univ : Set E), BddAbove (Set.range fun l => f l x) := by
    intro x _
    refine ⟨L * ‖x‖ + γ + β, ?_⟩
    rintro y ⟨l, rfl⟩
    dsimp [f]
    have hhi := (hb l x).2
    linarith
  obtain ⟨s, g, hs, hg, hlim⟩ :=
    Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove isOpen_univ f hf hnn hbdd
  refine ⟨s, fun x => g x - β, hs, ?_, ?_⟩
  · have heq : (fun x => g x - β) = g + (fun _ => -β) := by
      funext x
      exact sub_eq_add_neg (g x) β
    rw [heq]
    exact hg.add_const (-β)
  · intro x
    simpa only [f, add_sub_cancel_right] using
      (hlim x (mem_univ x)).sub_const β

end LinearBounds

end FunctionalInequalities.Analysis
