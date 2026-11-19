/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.QuadraticPreEnergy
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Sequential relaxation of the squared norm of a partially defined operator

Source: Blueprint `lem:covariance-core-closure`, last displayed identity, in its generic Hilbert
form. Read `exists_mem_of_isClosed_of_frequently_norm_le`, then `PreEnergy.ofLinearPMap`,
`sequentialRelaxation_ofLinearPMap_of_mem` and `sequentialRelaxation_ofLinearPMap_of_notMem`,
and finally the closure-of-a-core lemmas.

A partially defined linear operator `T : X →ₗ.[ℝ] H` from a normed space into a Hilbert space
defines the finite pre-energy `f ↦ ‖T f‖²` on its domain, realized by inclusion. This module
proves, for a closable `T` with closure `Tbar`:

* the sequential relaxation of that pre-energy equals `‖Tbar x‖²` on the domain of `Tbar` and `⊤`
  outside it; in particular it equals the raw energy `‖T f‖²` on every point of the domain;
* the pre-energy is quadratic, and its realization is dense exactly when the domain is dense;
* restricting `T` to a submodule of its domain that is dense for the graph norm does not change
  the closure, and neither does enlarging such a core inside the domain.

The only analytic input is the Hilbert-space selection lemma
`exists_mem_of_isClosed_of_frequently_norm_le`: a closed subspace of `X × H` containing pairs
`(x n, y n)` with `x n → x₀` and `‖y n‖ ≤ L` frequently contains a pair `(x₀, y₀)` with
`‖y₀‖ ≤ L`. It is proved by minimizing the norm over the closed convex hulls of the tails and
using the parallelogram law, without weak topologies.

Nothing here decides whether a concrete operator is closable; that is the analytic content of the
concrete modules. No Markov, Poincaré or spectral statement is made.
-/

@[expose] public section

noncomputable section

open Filter Topology Set

namespace FunctionalInequalities.Energy

section Selection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Hilbert selection along a closed subspace of pairs: if `(x n, y n)` lie in a closed
subspace `G`, `x n → x₀`, and `‖y n‖ ≤ L` frequently, then `G` contains a pair `(x₀, y₀)`
with `‖y₀‖ ≤ L`. The pair is found by minimizing the norm over the closed convex hulls of the
tails of `y`; the minimizers form a Cauchy sequence by the parallelogram law. -/
theorem exists_mem_of_isClosed_of_frequently_norm_le
    {G : Submodule ℝ (X × H)} (hG : IsClosed (G : Set (X × H)))
    {x : ℕ → X} {y : ℕ → H} (hxy : ∀ n, (x n, y n) ∈ G)
    {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) {L : ℝ} (hL : ∃ᶠ n in atTop, ‖y n‖ ≤ L) :
    ∃ y₀ : H, (x₀, y₀) ∈ G ∧ ‖y₀‖ ≤ L := by
  -- tails of the graph sequence and their closed convex hulls in the second coordinate
  set P : ℕ → Set (X × H) := fun n ↦ (fun j ↦ (x j, y j)) '' Ici n with hP
  set C : ℕ → Set H := fun n ↦ closure (convexHull ℝ (Prod.snd '' P n)) with hC
  have hPG : ∀ n, P n ⊆ (G : Set (X × H)) := by
    rintro n _ ⟨j, -, rfl⟩
    exact hxy j
  have hP_anti : ∀ n, P (n + 1) ⊆ P n := fun n ↦
    image_mono (Ici_subset_Ici.mpr (Nat.le_succ n))
  have hC_anti : ∀ n, C (n + 1) ⊆ C n := fun n ↦
    closure_mono (convexHull_mono (image_mono (hP_anti n)))
  have hC_antitone : Antitone C := antitone_nat_of_succ_le hC_anti
  have hyC : ∀ n j, n ≤ j → y j ∈ C n := fun n j hj ↦
    subset_closure (subset_convexHull ℝ _ ⟨(x j, y j), ⟨j, hj, rfl⟩, rfl⟩)
  have hC_ne : ∀ n, (C n).Nonempty := fun n ↦ ⟨y n, hyC n n le_rfl⟩
  have hC_closed : ∀ n, IsClosed (C n) := fun n ↦ isClosed_closure
  have hC_convex : ∀ n, Convex ℝ (C n) := fun n ↦ (convex_convexHull ℝ _).closure
  -- minimal-norm elements of the tails
  have hmin : ∀ n, ∃ z ∈ C n, ∀ w ∈ C n, ‖z‖ ≤ ‖w‖ := by
    intro n
    obtain ⟨z, hz, hzmin⟩ := exists_norm_eq_iInf_of_complete_convex (hC_ne n)
      (hC_closed n).isComplete (hC_convex n) 0
    refine ⟨z, hz, fun w hw ↦ ?_⟩
    have h1 : ‖(0 : H) - z‖ = ⨅ w : C n, ‖(0 : H) - (w : H)‖ := hzmin
    simp only [zero_sub, norm_neg] at h1
    rw [h1]
    have hbdd : BddBelow (range fun w : C n ↦ ‖(w : H)‖) :=
      ⟨0, by rintro _ ⟨w', rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hbdd ⟨w, hw⟩
  choose z hzC hzmin using hmin
  have hz_mono : Monotone fun n ↦ ‖z n‖ :=
    monotone_nat_of_le_succ fun n ↦ hzmin n (z (n + 1)) (hC_anti n (hzC (n + 1)))
  have hz_le : ∀ n, ‖z n‖ ≤ L := by
    intro n
    obtain ⟨j, hj, hjL⟩ := frequently_atTop.mp hL n
    exact (hzmin n (y j) (hyC n j hj)).trans hjL
  set S : ℝ := ⨆ n, ‖z n‖ with hS
  have hz_bdd : BddAbove (range fun n ↦ ‖z n‖) := ⟨L, by rintro _ ⟨n, rfl⟩; exact hz_le n⟩
  have hz_tendsto : Tendsto (fun n ↦ ‖z n‖) atTop (𝓝 S) := tendsto_atTop_ciSup hz_mono hz_bdd
  have hz_le_S : ∀ n, ‖z n‖ ≤ S := fun n ↦ le_ciSup hz_bdd n
  -- the minimizers are Cauchy by the parallelogram law
  have hz_cauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hsq : Tendsto (fun n ↦ ‖z n‖ ^ 2) atTop (𝓝 (S ^ 2)) := hz_tendsto.pow 2
    have hev : ∀ᶠ n in atTop, S ^ 2 - ‖z n‖ ^ 2 < ε ^ 2 / 2 := by
      have := (tendsto_const_nhds (x := S ^ 2)).sub hsq
      rw [sub_self] at this
      exact (this.eventually (gt_mem_nhds (by positivity)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun n hn ↦ ?_⟩
    -- the midpoint lies in the tail `C N`, so its norm dominates `‖z N‖`
    have hmid : (1 / 2 : ℝ) • z N + (1 / 2 : ℝ) • z n ∈ C N :=
      (hC_convex N) (hzC N) (hC_antitone hn (hzC n)) (by norm_num) (by norm_num) (by norm_num)
    have hmid_norm : ‖z N‖ ≤ ‖z n + z N‖ / 2 := by
      have := hzmin N _ hmid
      rwa [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        one_div, inv_mul_eq_div, add_comm] at this
    have hpar := parallelogram_law_with_norm ℝ (z n) (z N)
    have hbound : ‖z n - z N‖ ^ 2 ≤ 2 * (S ^ 2 - ‖z N‖ ^ 2) := by
      have h4 : 4 * ‖z N‖ ^ 2 ≤ ‖z n + z N‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hmid_norm (by norm_num : (0 : ℝ) ≤ 2)
        rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at this
        nlinarith [norm_nonneg (z N), norm_nonneg (z n + z N)]
      have hn_le : ‖z n‖ ^ 2 ≤ S ^ 2 := by
        have := hz_le_S n
        nlinarith [norm_nonneg (z n)]
      nlinarith
    have hlt : ‖z n - z N‖ ^ 2 < ε ^ 2 := by
      have := hN N le_rfl
      nlinarith
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  obtain ⟨z₀, hz₀⟩ := cauchySeq_tendsto_of_complete hz_cauchy
  refine ⟨z₀, ?_, le_of_tendsto hz₀.norm (Eventually.of_forall hz_le)⟩
  -- approximate each minimizer by a convex combination of graph points
  have hsel : ∀ n, ∃ p ∈ convexHull ℝ (P n), dist (z n) p.2 < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp (hzC n) (1 / ((n : ℝ) + 1)) (by positivity)
    have hw' : w ∈ (LinearMap.snd ℝ X H) '' convexHull ℝ (P n) := by
      rw [LinearMap.image_convexHull]
      simpa using hw
    obtain ⟨p, hp, rfl⟩ := hw'
    exact ⟨p, hp, hdist⟩
  choose p hp hpdist using hsel
  have hpG : ∀ n, p n ∈ (G : Set (X × H)) := fun n ↦
    convexHull_min (hPG n) G.convex (hp n)
  have hp2 : Tendsto (fun n ↦ (p n).2) atTop (𝓝 z₀) := by
    refine hz₀.congr_dist ?_
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hpdist n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hp1 : Tendsto (fun n ↦ (p n).1) atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (ε / 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hball : Prod.fst '' P n ⊆ Metric.closedBall x₀ (ε / 2) := by
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact Metric.mem_closedBall.mpr (hN j (hn.trans hj)).le
    have hmem : (p n).1 ∈ (LinearMap.fst ℝ X H) '' convexHull ℝ (P n) := ⟨p n, hp n, rfl⟩
    rw [LinearMap.image_convexHull] at hmem
    have hsub : convexHull ℝ ((LinearMap.fst ℝ X H) '' P n) ⊆ Metric.closedBall x₀ (ε / 2) :=
      convexHull_min (by simpa using hball) (convex_closedBall x₀ (ε / 2))
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp (hsub hmem)) (half_lt_self hε)
  have hp_tendsto : Tendsto p atTop (𝓝 (x₀, z₀)) := by
    have := hp1.prodMk_nhds hp2
    simpa using this
  exact hG.mem_of_tendsto hp_tendsto (Eventually.of_forall hpG)

end Selection

section Closability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A partially defined operator is closable as soon as the closure of its graph contains no
pair `(0, y)` with `y ≠ 0`. -/
theorem isClosable_of_graph_closure_snd_eq_zero (T : X →ₗ.[ℝ] H)
    (h : ∀ p ∈ T.graph.topologicalClosure, p.1 = 0 → p.2 = 0) : T.IsClosable :=
  ⟨T.graph.topologicalClosure.toLinearPMap, (Submodule.toLinearPMap_graph_eq _ h).symm⟩

/-- Membership in the closure of the graph is sequential convergence of graph points. -/
theorem mem_graph_topologicalClosure_iff (T : X →ₗ.[ℝ] H) (p : X × H) :
    p ∈ T.graph.topologicalClosure ↔
      ∃ f : ℕ → T.domain, Tendsto (fun n ↦ ((f n : X), T (f n))) atTop (𝓝 p) := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨q, hq, hqp⟩
    choose f hf using fun n ↦ (T.mem_graph_iff.mp (hq n))
    refine ⟨f, ?_⟩
    have : (fun n ↦ ((f n : X), T (f n))) = q := by
      funext n
      exact Prod.ext (hf n).1 (hf n).2
    rwa [this]
  · rintro ⟨f, hf⟩
    exact ⟨fun n ↦ ((f n : X), T (f n)), fun n ↦ T.mem_graph (f n), hf⟩

/-- If every graph point of `T` is a limit of graph points of the restriction of `T` to a
submodule `S` of its domain, then the restriction has the same closure as `T`. -/
theorem IsClosable.closure_domRestrict_eq {T : X →ₗ.[ℝ] H} (hT : T.IsClosable)
    {S : Submodule ℝ X} (hS : S ≤ T.domain)
    (hcore : ∀ f : T.domain, ∃ s : ℕ → S,
      Tendsto (fun n ↦ ((s n : X), T ⟨s n, hS (s n).2⟩)) atTop (𝓝 ((f : X), T f))) :
    (T.domRestrict S).closure = T.closure := by
  have hle : T.domRestrict S ≤ T := LinearPMap.domRestrict_le
  have hres : (T.domRestrict S).IsClosable := hT.leIsClosable hle
  apply le_antisymm (hT.closure_mono hle)
  apply LinearPMap.le_of_le_graph
  rw [← hT.graph_closure_eq_closure_graph, ← hres.graph_closure_eq_closure_graph]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  intro q hq
  obtain ⟨f, rfl⟩ := T.mem_graph_iff'.mp hq
  obtain ⟨s, hs⟩ := hcore f
  rw [mem_graph_topologicalClosure_iff]
  have hmem : ∀ n, (s n : X) ∈ (T.domRestrict S).domain := fun n ↦
    ⟨(s n).2, hS (s n).2⟩
  refine ⟨fun n ↦ ⟨s n, hmem n⟩, ?_⟩
  refine hs.congr fun n ↦ ?_
  refine Prod.ext rfl ?_
  exact (LinearPMap.domRestrict_apply rfl).symm

/-- Enlarging a graph-norm core inside the domain does not change the closure. -/
theorem IsClosable.closure_domRestrict_eq_of_le {T : X →ₗ.[ℝ] H} (hT : T.IsClosable)
    {S S' : Submodule ℝ X} (hSS' : S ≤ S') (_hS' : S' ≤ T.domain)
    (hS : (T.domRestrict S).closure = T.closure) :
    (T.domRestrict S').closure = T.closure := by
  have h1 : T.domRestrict S ≤ T.domRestrict S' := by
    refine ⟨fun x hx ↦ ⟨hSS' hx.1, hx.2⟩, ?_⟩
    intro x y hxy
    have hx : (x : X) ∈ S ⊓ T.domain := x.2
    have e1 : T.domRestrict S x = T ⟨x, hx.2⟩ :=
      LinearPMap.domRestrict_apply (x := x) (y := ⟨x, hx.2⟩) rfl
    have e2 : T.domRestrict S' y = T ⟨x, hx.2⟩ :=
      LinearPMap.domRestrict_apply (x := y) (y := ⟨x, hx.2⟩) hxy.symm
    rw [e1, e2]
  have h2 : T.domRestrict S' ≤ T := LinearPMap.domRestrict_le
  apply le_antisymm (hT.closure_mono h2)
  rw [← hS]
  exact (hT.leIsClosable h2).closure_mono h1

end Closability

section PreEnergy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The finite pre-energy `f ↦ ‖T f‖²` of a partially defined operator, realized by inclusion of
the domain. -/
def PreEnergy.ofLinearPMap (T : X →ₗ.[ℝ] H) : PreEnergy X where
  Test := T.domain
  toAmbient := Subtype.val
  energy f := ‖T f‖₊ ^ 2

namespace PreEnergy

variable (T : X →ₗ.[ℝ] H)

instance : AddCommGroup (ofLinearPMap T).Test := inferInstanceAs (AddCommGroup T.domain)

instance : Module ℝ (ofLinearPMap T).Test := inferInstanceAs (Module ℝ T.domain)

omit [CompleteSpace H] in
@[simp]
theorem ofLinearPMap_toAmbient (f : T.domain) : (ofLinearPMap T).toAmbient f = (f : X) := rfl

omit [CompleteSpace H] in
@[simp]
theorem ofLinearPMap_energy (f : T.domain) : (ofLinearPMap T).energy f = ‖T f‖₊ ^ 2 := rfl

section OperatorRelaxation

omit [CompleteSpace H]
/-- The squared-norm pre-energy of a linear operator is quadratic. -/
theorem ofLinearPMap_quadratic : (ofLinearPMap T).Quadratic := by
  have hsmul : ∀ (c : ℝ) (f : T.domain), ‖T (c • f)‖₊ ^ 2 = ‖c‖₊ ^ 2 * ‖T f‖₊ ^ 2 := by
    intro c f
    rw [T.map_smul, nnNorm_smul, mul_pow]
  have hpar : ∀ f g : T.domain,
      ‖T (f + g)‖₊ ^ 2 + ‖T (f - g)‖₊ ^ 2 = 2 * ‖T f‖₊ ^ 2 + 2 * ‖T g‖₊ ^ 2 := by
    intro f g
    apply NNReal.eq
    push_cast
    rw [T.map_add, T.map_sub, ← mul_add]
    exact parallelogram_law_with_norm ℝ _ _
  exact
    { map_zero := rfl
      map_add := fun _ _ ↦ rfl
      map_smul := fun _ _ ↦ rfl
      energy_zero := by
        change ‖T 0‖₊ ^ 2 = 0
        simp
      energy_smul := fun c f ↦ hsmul c f
      parallelogram := fun f g ↦ hpar f g }

/-- The realization is dense exactly when the domain is dense. -/
theorem ofLinearPMap_denseRealization_iff :
    (ofLinearPMap T).DenseRealization ↔ Dense (T.domain : Set X) := by
  change Dense (Set.range (Subtype.val : T.domain → X)) ↔ _
  rw [Subtype.range_coe]

/-- The relaxed energy is at most `‖Tbar x‖²` on the domain of the closure. -/
theorem sequentialRelaxation_ofLinearPMap_le (hT : T.IsClosable) (x : T.closure.domain) :
    (ofLinearPMap T).sequentialRelaxation x ≤ (‖T.closure x‖₊ ^ 2 : NNReal) := by
  have hmem : ((x : X), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  obtain ⟨f, hf⟩ := (mem_graph_topologicalClosure_iff T _).mp hmem
  have h1 : Tendsto (fun n ↦ (ofLinearPMap T).toAmbient (f n)) atTop (𝓝 (x : X)) :=
    (continuous_fst.tendsto _).comp hf
  have h2 : Tendsto (fun n ↦ ((ofLinearPMap T).energy (f n) : ENNReal)) atTop
      (𝓝 ((‖T.closure x‖₊ ^ 2 : NNReal) : ENNReal)) := by
    have h3 : Tendsto (fun n ↦ T (f n)) atTop (𝓝 (T.closure x)) :=
      (continuous_snd.tendsto _).comp hf
    have h4 : Tendsto (fun n ↦ ‖T (f n)‖₊ ^ 2) atTop (𝓝 (‖T.closure x‖₊ ^ 2)) :=
      (h3.nnNorm).pow 2
    exact (ENNReal.tendsto_coe.mpr h4)
  refine ((ofLinearPMap T).sequentialRelaxation_le_sequenceEnergy ⟨f, h1⟩).trans_eq ?_
  exact h2.liminf_eq

end OperatorRelaxation

/-- Any approximating sequence with frequently bounded energies forces membership in the domain
of the closure, with the corresponding norm bound. -/
theorem mem_closure_domain_of_frequently (hT : T.IsClosable) {x : X}
    (f : (ofLinearPMap T).ApproximatingSequence x) {L : NNReal}
    (hL : ∃ᶠ n in atTop, ‖T (f.1 n)‖₊ ≤ L) :
    ∃ hx : x ∈ T.closure.domain, ‖T.closure ⟨x, hx⟩‖₊ ≤ L := by
  have hG : IsClosed (T.closure.graph : Set (X × H)) := hT.closure_isClosed
  let g : ℕ → T.domain := f.1
  have hxy : ∀ n, ((g n : X), T (g n)) ∈ T.closure.graph := fun n ↦
    (LinearPMap.le_graph_of_le (T.le_closure)) (T.mem_graph (g n))
  have hx : Tendsto (fun n ↦ (g n : X)) atTop (𝓝 x) := f.2
  have hL' : ∃ᶠ n in atTop, ‖T (g n)‖ ≤ (L : ℝ) := by
    refine hL.mono fun n hn ↦ ?_
    exact_mod_cast hn
  obtain ⟨y₀, hy₀, hy₀L⟩ := exists_mem_of_isClosed_of_frequently_norm_le hG hxy hx hL'
  have hxdom : x ∈ T.closure.domain := LinearPMap.mem_domain_of_mem_graph hy₀
  refine ⟨hxdom, ?_⟩
  have : y₀ = T.closure ⟨x, hxdom⟩ := (LinearPMap.image_iff hxdom).mpr hy₀
  rw [← this]
  exact_mod_cast hy₀L

/-- Outside the domain of the closure the relaxed energy is infinite. -/
theorem sequentialRelaxation_ofLinearPMap_of_notMem (hT : T.IsClosable) {x : X}
    (hx : x ∉ T.closure.domain) : (ofLinearPMap T).sequentialRelaxation x = ⊤ := by
  rw [sequentialRelaxation_apply]
  refine le_antisymm le_top (le_iInf fun f ↦ ?_)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hfreq : ∃ᶠ n in atTop, ‖T (f.1 n)‖₊ ≤ NNReal.sqrt r := by
    have := frequently_lt_of_liminf_lt (by isBoundedDefault) hr.1
    refine this.mono fun n hn ↦ ?_
    have hn' : (‖T (f.1 n)‖₊ ^ 2 : NNReal) < r := by
      have := hn
      change ((‖T (f.1 n)‖₊ ^ 2 : NNReal) : ENNReal) < (r : ENNReal) at this
      exact_mod_cast this
    have := NNReal.sqrt_le_sqrt.mpr hn'.le
    rwa [NNReal.sqrt_sq] at this
  obtain ⟨hxdom, -⟩ := mem_closure_domain_of_frequently T hT f hfreq
  exact hx hxdom

/-- On the domain of the closure the relaxed energy is exactly `‖Tbar x‖²`. -/
theorem sequentialRelaxation_ofLinearPMap_of_mem (hT : T.IsClosable) (x : T.closure.domain) :
    (ofLinearPMap T).sequentialRelaxation x = (‖T.closure x‖₊ ^ 2 : NNReal) := by
  refine le_antisymm (sequentialRelaxation_ofLinearPMap_le T hT x) ?_
  rw [sequentialRelaxation_apply]
  refine le_iInf fun f ↦ ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hfreq : ∃ᶠ n in atTop, ‖T (f.1 n)‖₊ ≤ NNReal.sqrt r := by
    have := frequently_lt_of_liminf_lt (by isBoundedDefault) hr.1
    refine this.mono fun n hn ↦ ?_
    have hn' : (‖T (f.1 n)‖₊ ^ 2 : NNReal) < r := by
      have := hn
      change ((‖T (f.1 n)‖₊ ^ 2 : NNReal) : ENNReal) < (r : ENNReal) at this
      exact_mod_cast this
    have := NNReal.sqrt_le_sqrt.mpr hn'.le
    rwa [NNReal.sqrt_sq] at this
  obtain ⟨hxdom, hle⟩ := mem_closure_domain_of_frequently T hT f hfreq
  have hr2 : r < ‖T.closure x‖₊ ^ 2 := by exact_mod_cast hr.2
  have hx' : (⟨(x : X), hxdom⟩ : T.closure.domain) = x := Subtype.ext rfl
  rw [hx'] at hle
  have : ‖T.closure x‖₊ ^ 2 ≤ r := by
    calc ‖T.closure x‖₊ ^ 2 ≤ (NNReal.sqrt r) ^ 2 := by gcongr
      _ = r := NNReal.sq_sqrt r
  exact absurd hr2 (not_lt.mpr this)

/-- Relaxation returns the raw energy on every point of the original domain: this is the
"agreement on tests" consequence of closability. -/
theorem sequentialRelaxation_ofLinearPMap_toAmbient (hT : T.IsClosable) (f : T.domain) :
    (ofLinearPMap T).sequentialRelaxation (f : X) = ((ofLinearPMap T).energy f : ENNReal) := by
  have hmem : (f : X) ∈ T.closure.domain := T.le_closure.1 f.2
  rw [sequentialRelaxation_ofLinearPMap_of_mem T hT ⟨f, hmem⟩]
  change ((‖T.closure ⟨f, hmem⟩‖₊ ^ 2 : NNReal) : ENNReal) = ((‖T f‖₊ ^ 2 : NNReal) : ENNReal)
  rw [T.le_closure.2 (x := f) (y := ⟨f, hmem⟩) rfl]

open Classical in
/-- The extended energy `x ↦ ‖S x‖²` of a partially defined operator, infinite off its domain. -/
def normSqEnergy {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] (S : X →ₗ.[ℝ] H') :
    Functional X where
  toFun x := if h : x ∈ S.domain then ((‖S ⟨x, h⟩‖₊ ^ 2 : NNReal) : ENNReal) else ⊤

section NormedSpace

variable {H' : Type*}
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

open Classical in
omit [CompleteSpace H] in
theorem normSqEnergy_of_mem
    (S : X →ₗ.[ℝ] H') (x : S.domain) :
    normSqEnergy S x = ((‖S x‖₊ ^ 2 : NNReal) : ENNReal) := by
  change (if h : (x : X) ∈ S.domain then ((‖S ⟨x, h⟩‖₊ ^ 2 : NNReal) : ENNReal) else ⊤) = _
  rw [dite_eq_left x.2]

open Classical in
omit [CompleteSpace H] in
theorem normSqEnergy_of_notMem
    (S : X →ₗ.[ℝ] H') {x : X} (hx : x ∉ S.domain) : normSqEnergy S x = ⊤ := by
  change (if h : x ∈ S.domain then ((‖S ⟨x, h⟩‖₊ ^ 2 : NNReal) : ENNReal) else ⊤) = _
  rw [dite_eq_right hx]

end NormedSpace

/-- The sequential relaxation of `‖T f‖²` is the squared-norm energy of the closure of `T`:
the graph-closed form, in the language of the pinned CMH source. -/
theorem sequentialRelaxation_ofLinearPMap_eq_normSqEnergy (hT : T.IsClosable) :
    (ofLinearPMap T).sequentialRelaxation = normSqEnergy T.closure := by
  ext x
  by_cases hx : x ∈ T.closure.domain
  · rw [sequentialRelaxation_ofLinearPMap_of_mem T hT ⟨x, hx⟩, normSqEnergy_of_mem _ ⟨x, hx⟩]
  · rw [sequentialRelaxation_ofLinearPMap_of_notMem T hT hx, normSqEnergy_of_notMem _ hx]

/-- The finite-energy domain of the relaxation is the domain of the closure. -/
theorem mem_domain_sequentialRelaxation_ofLinearPMap_iff (hT : T.IsClosable) (x : X) :
    x ∈ (ofLinearPMap T).sequentialRelaxation.domain ↔ x ∈ T.closure.domain := by
  constructor
  · intro hx
    by_contra hnot
    have := sequentialRelaxation_ofLinearPMap_of_notMem T hT hnot
    exact hx this
  · intro hx
    change (ofLinearPMap T).sequentialRelaxation x ≠ ⊤
    rw [sequentialRelaxation_ofLinearPMap_of_mem T hT ⟨x, hx⟩]
    exact ENNReal.coe_ne_top

end PreEnergy

end PreEnergy

end FunctionalInequalities.Energy
