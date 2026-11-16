/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Normed.Lp.PiLp

public import LeanPool.SteinerSpanners.Defs
public import LeanPool.SteinerSpanners.Geometry

/-! # Projection infrastructure for Steiner spanners

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib. -/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.Projection

private lemma weightedWalk_nonnegative {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
  (hweight : ∀ e ∈ H.edgeSet, 0 ≤ w e) : ∀ {u v : V} (q_w : H.Walk u v), 0 ≤ walkWeight w q_w := by
  intro u v q_w
  induction q_w with
  | nil => exact le_rfl
  | @cons u b v hadj q' ih =>
    exact add_nonneg (hweight s(u, b) (H.mem_edgeSet.mpr hadj)) ih

private lemma weightedWalk_append {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ {u v z :
    V} (q₁ : H.Walk u v) (q₂ : H.Walk v z),
    walkWeight w (q₁.append q₂) = walkWeight w q₁ + walkWeight w q₂ := by
  intro u v z q₁ q₂
  induction q₁ with
  | nil =>
    rw [SimpleGraph.Walk.nil_append]
    simp [walkWeight]
  | @cons u b v _ q' ih =>
    rw [SimpleGraph.Walk.cons_append]
    simp only [walkWeight, ih, add_assoc]

private lemma weightedWalk_reverse {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ {u v : V}
    (q_w : H.Walk u v),
    walkWeight w q_w.reverse = walkWeight w q_w := by
  have hww_append := @weightedWalk_append _ H w
  intro u v q_w
  induction q_w with
  | nil =>
    rw [SimpleGraph.Walk.reverse_nil]
  | @cons u b v _ q' ih =>
    rw [SimpleGraph.Walk.reverse_cons, hww_append, ih]
    simp only [walkWeight, add_zero]
    rw [@Sym2.eq_swap _ b u, add_comm]

private lemma weightedGraphDist_self {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ u : V,
    graphDist H w u u = 0 := by
  intro u
  apply nonpos_iff_eq_zero.mp
  calc
    graphDist H w u u ≤ ENNReal.ofReal (walkWeight w SimpleGraph.Walk.nil) :=
      iInf_le _ SimpleGraph.Walk.nil
    _ = 0 := by simp [walkWeight]

private lemma weightedGraphDist_symm {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ u v :
    V, graphDist H w u v = graphDist H w v u := by
  have hww_reverse := @weightedWalk_reverse _ H w
  have hle : ∀ u v : V, graphDist H w u v ≤ graphDist H w v u := by
    intro u v
    unfold graphDist
    refine le_iInf (fun q_w => ?_)
    calc
      (⨅ p_w : H.Walk u v, ENNReal.ofReal (walkWeight w p_w))
        ≤ ENNReal.ofReal (walkWeight w q_w.reverse) := iInf_le _ q_w.reverse
      _ = ENNReal.ofReal (walkWeight w q_w) := by rw [hww_reverse]
  exact fun u v => le_antisymm (hle u v) (hle v u)

private lemma weightedGraphDist_adj_le {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ {u v
    : V}, H.Adj u v →
    graphDist H w u v ≤ ENNReal.ofReal (w s(u, v)) := by
  intro u v hadj
  calc
    graphDist H w u v ≤ ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj .nil)) :=
      iInf_le _ (SimpleGraph.Walk.cons hadj .nil)
    _ = ENNReal.ofReal (w s(u, v)) := by simp [walkWeight]

private lemma weightedGraphDist_triangle {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
  (hweight : ∀ e ∈ H.edgeSet, 0 ≤ w e) : ∀ u v z : V,
    graphDist H w u z ≤ graphDist H w u v + graphDist H w v z := by
  have hww_nonneg := @weightedWalk_nonnegative _ H w hweight
  have hww_append := @weightedWalk_append _ H w
  intro u v z
  unfold graphDist
  rw [ENNReal.iInf_add]
  refine le_iInf (fun q₁ => ?_)
  rw [ENNReal.add_iInf]
  refine le_iInf (fun q₂ => ?_)
  rw [← ENNReal.ofReal_add (hww_nonneg q₁) (hww_nonneg q₂), ← hww_append]
  exact iInf_le _ (q₁.append q₂)

private lemma finiteMetricGap (P : Type) [MetricSpace P] [Finite P] (s : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : P, dist a b < s + ε → dist a b ≤ s := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let BadPairs : Finset (P × P) := Finset.univ.filter (fun ab : P × P => s < dist ab.1 ab.2)
  let ε : ℝ :=
    if hne : BadPairs.Nonempty then
      (BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s)) / 2
    else 1
  have hε_pos : 0 < ε := by
    dsimp only [ε]
    split_ifs with hne
    · have hinf_pos : 0 < BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s) := by
        rw [Finset.lt_inf'_iff]
        intro ab hab
        have hlt : s < dist ab.1 ab.2 := (Finset.mem_filter.mp hab).2
        linarith
      linarith
    · norm_num
  let B : ℝ := s + ε
  have h_gap : ∀ a b : P, dist a b < B → dist a b ≤ s := by
    intro a b hlt
    by_contra hnot
    have hgt : s < dist a b := not_le.mp hnot
    have hmem : (a, b) ∈ BadPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
    have hne : BadPairs.Nonempty := ⟨(a, b), hmem⟩
    have hε_eq : ε = (BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s)) / 2 := dite_eq_left hne
    have hinf_le : BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s) ≤ dist a b - s :=
      Finset.inf'_le _ hmem
    dsimp [B] at hlt
    linarith
  exact ⟨ε, hε_pos, h_gap⟩

/-- **Theorem 2.1(a) (Metric Nearest-Terminal Projection, Module 1)** -/
theorem thm_2_1a_proof :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C r : ℝ), 1 ≤ C → 0 < r →
        ∀ (S : Type) [Fintype S]
          (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ),
          IsGeneralNonMetricSteinerSpanner C H w →
          ∃ G_hat : SimpleGraph P,
            Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
            (∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r) ∧
            (∀ x y : P, 0 < dist x y → dist x y ≤ r →
              ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r) := by
  classical
  intro P _ _ hP_card C r hC hr S _ H w hSpan
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ε, hε_pos, h_gap⟩ := finiteMetricGap P (C * r)
  let B : ℝ := C * r + ε
  have hCr_pos : 0 < C * r := mul_pos (by linarith) hr
  have hB_pos : 0 < B := by dsimp [B]; linarith
  have h_transfer : ∀ a b : P,
      graphDist H w (.inl a) (.inl b) < ENNReal.ofReal B → dist a b ≤ C * r := by
    intro a b hlt
    have hof : ENNReal.ofReal (dist a b) < ENNReal.ofReal B :=
      lt_of_le_of_lt (hSpan.noncontracting a b) hlt
    exact h_gap a b ((ENNReal.ofReal_lt_ofReal_iff hB_pos).mp hof)
  have hww_nonneg := @weightedWalk_nonnegative _ H w hSpan.weight_nonneg
  have hgd_self := weightedGraphDist_self H w
  have hgd_symm := weightedGraphDist_symm H w
  have hgd_adj_le := @weightedGraphDist_adj_le _ H w
  have hgd_triangle := weightedGraphDist_triangle H w hSpan.weight_nonneg
  have hπ_ex : ∀ u : P ⊕ S, ∃ z ∈ (Finset.univ : Finset P),
      ∀ z' ∈ (Finset.univ : Finset P),
        graphDist H w u (.inl z) ≤ graphDist H w u (.inl z') :=
    fun u => Finset.exists_min_image Finset.univ (fun z => graphDist H w u (.inl z))
      Finset.univ_nonempty
  let π : P ⊕ S → P := fun u => Classical.choose (hπ_ex u)
  have hπ_min : ∀ (u : P ⊕ S) (z : P),
      graphDist H w u (.inl (π u)) ≤ graphDist H w u (.inl z) :=
    fun u z => (Classical.choose_spec (hπ_ex u)).2 z (Finset.mem_univ z)
  have hπ_inl : ∀ x : P, π (.inl x) = x := by
    intro x
    by_contra hne
    have hd_pos : 0 < dist x (π (.inl x)) := dist_pos.mpr (Ne.symm hne)
    have hgd_pos : 0 < graphDist H w (.inl x) (.inl (π (.inl x))) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd_pos) (hSpan.noncontracting x (π (.inl x)))
    have hgd_zero : graphDist H w (.inl x) (.inl (π (.inl x))) ≤ 0 := by
      calc
        graphDist H w (.inl x) (.inl (π (.inl x)))
          ≤ graphDist H w (.inl x) (.inl x) := hπ_min (.inl x) x
        _ = 0 := hgd_self (.inl x)
    exact (not_lt_of_ge hgd_zero) hgd_pos
  let G_hat : SimpleGraph P :=
    { Adj := fun a b => a ≠ b ∧ dist a b ≤ C * r ∧
        ∃ u v : P ⊕ S, H.Adj u v ∧ s(π u, π v) = s(a, b)
      symm := ⟨by
        intro a b ⟨hab, hd, u, v, huv, hs⟩
        refine ⟨hab.symm, ?_, u, v, huv, ?_⟩
        · rwa [dist_comm]
        · rw [hs, Sym2.eq_swap]⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  have hG_edge : ∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r :=
    fun _ _ h => ⟨dist_pos.mpr h.1, h.2.1⟩
  have hG_card : Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet := by
    have hex : ∀ e' : G_hat.edgeSet, ∃ e : H.edgeSet, Sym2.map π e.1 = e'.1 := by
      rintro ⟨s', hs'⟩
      revert hs'
      refine Sym2.ind (fun a b hs' => ?_) s'
      rw [SimpleGraph.mem_edgeSet] at hs'
      obtain ⟨_, _, u, v, huv, hs⟩ := hs'
      refine ⟨⟨s(u, v), H.mem_edgeSet.mpr huv⟩, ?_⟩
      simpa only [Sym2.map_mk] using hs
    let f : G_hat.edgeSet → H.edgeSet := fun e' => Classical.choose (hex e')
    have hf_spec : ∀ e' : G_hat.edgeSet, Sym2.map π (f e').1 = e'.1 :=
      fun e' => Classical.choose_spec (hex e')
    have hf_inj : Function.Injective f := by
      intro e₁ e₂ heq
      apply Subtype.ext
      rw [← hf_spec e₁, ← hf_spec e₂, heq]
    exact Nat.card_le_card_of_injective f hf_inj
  have hG_path : ∀ x y : P, 0 < dist x y → dist x y ≤ r →
      ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r := by
    intro x y _ hxy_le
    have hC_dist_lt : C * dist x y < B := by
      have h1 : C * dist x y ≤ C * r := mul_le_mul_of_nonneg_left hxy_le (by linarith)
      dsimp [B]; linarith
    have hgd_xy_lt : graphDist H w (.inl x) (.inl y) < ENNReal.ofReal B :=
      lt_of_le_of_lt (hSpan.stretch x y) ((ENNReal.ofReal_lt_ofReal_iff hB_pos).mpr hC_dist_lt)
    obtain ⟨q_H, hq_H⟩ : ∃ q_H : H.Walk (.inl x) (.inl y),
        ENNReal.ofReal (walkWeight w q_H) < ENNReal.ofReal B := by
      unfold graphDist at hgd_xy_lt
      exact iInf_lt_iff.mp hgd_xy_lt
    have h_ball : ∀ (u : P ⊕ S) (q_rem : H.Walk u (.inl y)),
        graphDist H w (.inl x) u + ENNReal.ofReal (walkWeight w q_rem) < ENNReal.ofReal B →
        dist x (π u) ≤ C * r := by
      intro u q_rem hbud
      apply h_transfer x (π u)
      have h1 : graphDist H w u (.inl (π u)) ≤ ENNReal.ofReal (walkWeight w q_rem) :=
        le_trans (hπ_min u y) (iInf_le _ q_rem)
      calc
        graphDist H w (.inl x) (.inl (π u))
          ≤ graphDist H w (.inl x) u + graphDist H w u (.inl (π u)) :=
            hgd_triangle (.inl x) u (.inl (π u))
        _ ≤ graphDist H w (.inl x) u + ENNReal.ofReal (walkWeight w q_rem) :=
            add_le_add le_rfl h1
        _ < ENNReal.ofReal B := hbud
    have h_ind : ∀ (u v₀ : P ⊕ S) (q₂ : H.Walk u v₀),
        v₀ = .inl y →
        graphDist H w (.inl x) u + ENNReal.ofReal (walkWeight w q₂) < ENNReal.ofReal B →
        ∃ q₀ : G_hat.Walk (π u) y,
          ∀ z ∈ q₀.support, dist x z ≤ C * r := by
      intro u v₀ q₂
      induction q₂ with
      | @nil u =>
        intro hv₀ hbud
        subst hv₀
        have hu_ball : dist x (π (.inl y)) ≤ C * r := h_ball (.inl y) .nil hbud
        rw [hπ_inl y] at hu_ball ⊢
        refine ⟨SimpleGraph.Walk.nil, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        rwa [hz]
      | @cons u v v₀ hadj q₂' ih =>
        intro hv₀ hbud
        subst hv₀
        have hu_ball : dist x (π u) ≤ C * r := h_ball u (.cons hadj q₂') hbud
        have hw_nn : 0 ≤ w s(u, v) := hSpan.weight_nonneg s(u, v) (H.mem_edgeSet.mpr hadj)
        have hsplit : ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj q₂')) =
            ENNReal.ofReal (w s(u, v)) + ENNReal.ofReal (walkWeight w q₂') := by
          simp only [walkWeight]
          exact ENNReal.ofReal_add hw_nn (hww_nonneg q₂')
        have hbud_v :
            graphDist H w (.inl x) v + ENNReal.ofReal (walkWeight w q₂') < ENNReal.ofReal B := by
          have hstep : graphDist H w (.inl x) v ≤
              graphDist H w (.inl x) u + ENNReal.ofReal (w s(u, v)) :=
            le_trans (hgd_triangle (.inl x) u v) (add_le_add le_rfl (hgd_adj_le hadj))
          calc
            graphDist H w (.inl x) v + ENNReal.ofReal (walkWeight w q₂')
              ≤ (graphDist H w (.inl x) u + ENNReal.ofReal (w s(u, v))) +
                  ENNReal.ofReal (walkWeight w q₂') :=
                add_le_add hstep le_rfl
            _ = graphDist H w (.inl x) u +
                  ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj q₂')) := by
                rw [hsplit, add_assoc]
            _ < ENNReal.ofReal B := hbud
        obtain ⟨q_tail, hq_tail⟩ := ih rfl hbud_v
        by_cases heq : π u = π v
        · rw [heq]
          exact ⟨q_tail, hq_tail⟩
        · have h_adj_hat : G_hat.Adj (π u) (π v) := by
            refine ⟨heq, ?_, u, v, hadj, rfl⟩
            apply h_transfer (π u) (π v)
            have h_left : graphDist H w (.inl (π u)) u ≤ graphDist H w (.inl x) u := by
              rw [hgd_symm (.inl (π u)) u, hgd_symm (.inl x) u]
              exact hπ_min u x
            have h_mid : graphDist H w u v ≤ ENNReal.ofReal (w s(u, v)) := hgd_adj_le hadj
            have h_right : graphDist H w v (.inl (π v)) ≤ ENNReal.ofReal (walkWeight w q₂') :=
              le_trans (hπ_min v y) (iInf_le _ q₂')
            calc
              graphDist H w (.inl (π u)) (.inl (π v))
                ≤ graphDist H w (.inl (π u)) u + graphDist H w u (.inl (π v)) :=
                  hgd_triangle (.inl (π u)) u (.inl (π v))
              _ ≤ graphDist H w (.inl (π u)) u +
                    (graphDist H w u v + graphDist H w v (.inl (π v))) :=
                  add_le_add le_rfl (hgd_triangle u v (.inl (π v)))
              _ ≤ graphDist H w (.inl x) u +
                    (ENNReal.ofReal (w s(u, v)) + ENNReal.ofReal (walkWeight w q₂')) :=
                  add_le_add h_left (add_le_add h_mid h_right)
              _ = graphDist H w (.inl x) u +
                    ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj q₂')) := by
                  rw [hsplit]
              _ < ENNReal.ofReal B := hbud
          refine ⟨SimpleGraph.Walk.cons h_adj_hat q_tail, ?_⟩
          intro z hz
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz_tail
          · exact hu_ball
          · exact hq_tail z hz_tail
    have hbud_init :
        graphDist H w (.inl x) (.inl x) + ENNReal.ofReal (walkWeight w q_H) < ENNReal.ofReal B := by
      rwa [hgd_self (.inl x), zero_add]
    have h_proj := h_ind (.inl x) (.inl y) q_H rfl hbud_init
    rw [hπ_inl x] at h_proj
    obtain ⟨q₀, hq₀⟩ := h_proj
    refine ⟨q₀.bypass, q₀.bypass_isPath, ?_⟩
    intro z hz
    exact hq₀ z (q₀.support_bypass_subset_support hz)
  exact ⟨G_hat, hG_card, hG_edge, hG_path⟩

/-- Compatibility name for the shared one-hot embedding distance formula. -/
lemma oneHotEmbed_lpDist {N q : ℕ} (p : ℝ) (hp : 1 ≤ p) : ∀ x y : Fin N → Fin q,
    lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p) :=
  Geometry.oneHotEmbed_lpDist p hp

lemma oneHotEmbed_injective {N q : ℕ} : Function.Injective (@oneHotEmbed N q) := by
  classical
  intro x y hxy
  funext v
  have hk := congrFun hxy (finProdFinEquiv (v, x v))
  dsimp only [oneHotEmbed] at hk
  simp only [Equiv.symm_apply_apply, ↓reduceIte] at hk
  split_ifs at hk with hyx
  · exact hyx.symm
  · norm_num at hk

/-- **Theorem 2.1(b) (Boolean-Hypercube Reduction Across `ℓ_p`, Module 1)** -/
theorem thm_2_1b_proof :
    ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)) := by
  intro N q L rStar C₁ _ _ hrStar hN_eq p C hp hC hC₁
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hinv_nn : 0 ≤ 1 / p := div_nonneg zero_le_one (le_of_lt hp_pos)
  have hinv_le1 : 1 / p ≤ 1 := div_le_one_of_le₀ hp (le_of_lt hp_pos)
  have h_onehot_lp := oneHotEmbed_lpDist (N := N) (q := q) p hp
  refine ⟨h_onehot_lp, ?_⟩
  intro X hX_card hX_min e P
  have hP_bool : ∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1 := by
    intro i k
    dsimp only [P, oneHotEmbed]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have h_onehot_inj := @oneHotEmbed_injective N q
  have hP_inj : Function.Injective P :=
    h_onehot_inj.comp (Subtype.val_injective.comp e.injective)
  have hP_ar : aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) := by
    have hlp_le : ∀ i j : Fin X.card,
        lpDist p (P i) (P j) ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) := by
      intro i j
      have hd_nat : hammingDist (e i).val (e j).val ≤ 2 ^ L * rStar := by
        rw [← hN_eq]
        simpa [hammingDist] using
          Finset.card_le_univ (Finset.univ.filter (fun v : Fin N => (e i).val v ≠ (e j).val v))
      have hd_cast : (hammingDist (e i).val (e j).val : ℝ) ≤ (2 ^ L : ℝ) * (rStar : ℝ) := by
        exact_mod_cast hd_nat
      have h2d : 2 * (hammingDist (e i).val (e j).val : ℝ) ≤
          (2 : ℝ) ^ (L + 1) * (rStar : ℝ) := by
        rw [pow_succ]
        linarith
      have hrpow1 : (2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p) ≤
          ((2 : ℝ) ^ (L + 1) * (rStar : ℝ)) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) h2d hinv_nn
      have hrpow2 : ((2 : ℝ) ^ (L + 1) * (rStar : ℝ)) ^ (1 / p) =
          ((2 : ℝ) ^ (L + 1)) ^ (1 / p) * (rStar : ℝ) ^ (1 / p) :=
        Real.mul_rpow (by positivity) (by positivity)
      have h2L1_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (L + 1) := one_le_pow₀ (by norm_num)
      have hrpow3 : ((2 : ℝ) ^ (L + 1)) ^ (1 / p) ≤ (2 : ℝ) ^ (L + 1) := by
        calc
          ((2 : ℝ) ^ (L + 1)) ^ (1 / p) ≤ ((2 : ℝ) ^ (L + 1)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h2L1_ge1 hinv_le1
          _ = (2 : ℝ) ^ (L + 1) := Real.rpow_one _
      dsimp only [P]
      rw [h_onehot_lp]
      calc
        (2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p)
          ≤ ((2 : ℝ) ^ (L + 1)) ^ (1 / p) * (rStar : ℝ) ^ (1 / p) := by rwa [hrpow2] at hrpow1
        _ ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) :=
          mul_le_mul_of_nonneg_right hrpow3 (by positivity)
    have hlp_ge : ∀ i j : Fin X.card, i ≠ j → (rStar : ℝ) ^ (1 / p) ≤ lpDist p (P i) (P j) := by
      intro i j hij
      have hval_ne : (e i).val ≠ (e j).val :=
        fun h => hij (e.injective (Subtype.ext h))
      have hmin_ij : (rStar : ℝ) / 2 ≤ (hammingDist (e i).val (e j).val : ℝ) :=
        hX_min (e i).val (e i).prop (e j).val (e j).prop hval_ne
      have hmin2 : (rStar : ℝ) ≤ 2 * (hammingDist (e i).val (e j).val : ℝ) := by linarith
      dsimp only [P]
      rw [h_onehot_lp]
      exact Real.rpow_le_rpow (by positivity) hmin2 hinv_nn
    have hn0 : 0 < X.card := by omega
    have hmax : maxPairwiseDist p P ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) := by
      unfold maxPairwiseDist
      rw [dite_eq_left hn0]
      exact Finset.sup'_le _ _ fun ij _ => hlp_le ij.1 ij.2
    let i0 : Fin X.card := ⟨0, by omega⟩
    let i1 : Fin X.card := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [i0, i1] at hv
      omega
    have hmin : (rStar : ℝ) ^ (1 / p) ≤ minDistinctPairwiseDist p P := by
      unfold minDistinctPairwiseDist
      set offDiag := Finset.univ.filter (fun ij : Fin X.card × Fin X.card => ij.1 ≠ ij.2)
      have hmem01 : (i0, i1) ∈ offDiag := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi01⟩
      have hne : offDiag.Nonempty := ⟨(i0, i1), hmem01⟩
      rw [dite_eq_left hne]
      exact Finset.le_inf' _ _ fun ij hij => hlp_ge ij.1 ij.2 (Finset.mem_filter.mp hij).2
    have hr_pos : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
    have hrp_pos : 0 < (rStar : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos hr_pos _
    have hmin_pos : 0 < minDistinctPairwiseDist p P := lt_of_lt_of_le hrp_pos hmin
    unfold aspectRatio
    rw [div_le_iff₀ hmin_pos]
    calc
      maxPairwiseDist p P ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) := hmax
      _ ≤ (2 : ℝ) ^ (L + 1) * minDistinctPairwiseDist p P :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
  refine ⟨hP_bool, hP_inj, hP_ar, ?_⟩
  intro S _ H w hSpan
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let embLp : Fin X.card → WithLp (ENNReal.ofReal p) (Fin (N * q) → ℝ) :=
    fun i => WithLp.toLp (ENNReal.ofReal p) (P i)
  have hemb_inj : Function.Injective embLp := by
    intro i j hij
    exact hP_inj (congrArg WithLp.ofLp hij)
  let msFin : MetricSpace (Fin X.card) := MetricSpace.induced embLp hemb_inj inferInstance
  have hdist_eq : ∀ i j : Fin X.card,
      @dist (Fin X.card) msFin.toDist i j = lpDist p (P i) (P j) := by
    intro i j
    exact (Geometry.lpDist_eq_toLp_dist p hp (P i) (P j)).symm
  have hGen : @IsGeneralNonMetricSteinerSpanner (Fin X.card) msFin _ C S _ H w :=
    { weight_nonneg := hSpan.weight_nonneg
      noncontracting := fun i j => by rw [hdist_eq]; exact hSpan.noncontracting i j
      stretch := fun i j => by rw [hdist_eq]; exact hSpan.stretch i j }
  let r : ℝ := (2 * (rStar : ℝ)) ^ (1 / p)
  have h2r_pos : 0 < 2 * (rStar : ℝ) := by
    have : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
    linarith
  have hr_pos : 0 < r := Real.rpow_pos_of_pos h2r_pos (1 / p)
  have hcard_fin : 2 ≤ Fintype.card (Fin X.card) := by rwa [Fintype.card_fin]
  obtain ⟨G_fin, hG_card, hG_edge, hG_path⟩ :=
    @thm_2_1a_proof (Fin X.card) msFin _ hcard_fin C r hC hr_pos S _ H w hGen
  have hCp_le : C ^ p ≤ (C₁ : ℝ) := by
    calc
      C ^ p ≤ (⌈C ^ p⌉₊ : ℝ) := Nat.le_ceil (C ^ p)
      _ ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
  have h_ham_le : ∀ i j : Fin X.card,
      @dist (Fin X.card) msFin.toDist i j ≤ C * r →
      hammingDist (e i).val (e j).val ≤ C₁ * rStar := by
    intro i j hd_le
    rw [hdist_eq i j] at hd_le
    dsimp only [P] at hd_le
    rw [h_onehot_lp] at hd_le
    have hpow_le :
        ((2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p)) ^ p ≤ (C * r) ^ p :=
      Real.rpow_le_rpow (by positivity) hd_le (le_of_lt hp_pos)
    have hlhs : ((2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p)) ^ p =
        2 * (hammingDist (e i).val (e j).val : ℝ) := by
      rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ 1 hp_ne, Real.rpow_one]
    have hrhs : (C * r) ^ p = C ^ p * (2 * (rStar : ℝ)) := by
      dsimp only [r]
      rw [Real.mul_rpow (by linarith) (le_of_lt hr_pos),
        ← Real.rpow_mul (le_of_lt h2r_pos), div_mul_cancel₀ 1 hp_ne, Real.rpow_one]
    rw [hlhs, hrhs] at hpow_le
    have h1 : C ^ p * (2 * (rStar : ℝ)) ≤ (C₁ : ℝ) * (2 * (rStar : ℝ)) :=
      mul_le_mul_of_nonneg_right hCp_le (le_of_lt h2r_pos)
    have h2 : (hammingDist (e i).val (e j).val : ℝ) ≤ ((C₁ * rStar : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  let G_hat : SimpleGraph ↥X :=
    { Adj := fun a b => G_fin.Adj (e.symm a) (e.symm b)
      symm := ⟨fun _ _ h => G_fin.adj_symm h⟩
      loopless := ⟨fun a h => G_fin.irrefl h⟩ }
  have hGhat_card : Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet := by
    let f_edge : G_hat.edgeSet → G_fin.edgeSet := fun s =>
      ⟨Sym2.map e.symm s.1, by
        rcases s with ⟨s, hs⟩
        revert hs
        refine Sym2.ind (fun a b hs => ?_) s
        simpa [SimpleGraph.mem_edgeSet, G_hat] using hs⟩
    have hf_inj : Function.Injective f_edge := fun s₁ s₂ heq =>
      Subtype.ext (Sym2.map.injective e.symm.injective (Subtype.mk.inj heq))
    exact le_trans (Nat.card_le_card_of_injective f_edge hf_inj) hG_card
  have hGhat_edge : ∀ a b : ↥X, G_hat.Adj a b →
      0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar := by
    intro a b hadj
    obtain ⟨hd_pos, hd_le⟩ := hG_edge (e.symm a) (e.symm b) hadj
    have hab_ne : a.val ≠ b.val := by
      intro hval
      have heq_sub : a = b := Subtype.ext hval
      subst heq_sub
      exact G_fin.irrefl hadj
    have h_ub := h_ham_le (e.symm a) (e.symm b) hd_le
    rw [e.apply_symm_apply, e.apply_symm_apply] at h_ub
    exact ⟨hammingDist_pos.mpr hab_ne, h_ub⟩
  have hGhat_path : ∀ x y : ↥X, hammingDist x.val y.val = rStar →
      ∃ q_walk : G_hat.Walk x y,
        q_walk.IsPath ∧
        ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar := by
    intro x y hxy_ham
    have hdist_xy : @dist (Fin X.card) msFin.toDist (e.symm x) (e.symm y) = r := by
      rw [hdist_eq]
      dsimp only [P, r]
      rw [h_onehot_lp, e.apply_symm_apply, e.apply_symm_apply, hxy_ham]
    obtain ⟨q_fin, _, hq_supp⟩ :=
      hG_path (e.symm x) (e.symm y) (by rw [hdist_xy]; exact hr_pos) (by rw [hdist_xy])
    let φ : G_fin →g G_hat :=
      { toFun := e
        map_rel' := fun {u v} h => by
          dsimp [G_hat]
          rwa [e.symm_apply_apply, e.symm_apply_apply] }
    let q_raw : G_hat.Walk x y :=
      (q_fin.map φ).copy (e.apply_symm_apply x) (e.apply_symm_apply y)
    refine ⟨q_raw.bypass, q_raw.bypass_isPath, ?_⟩
    intro z hz
    have hz_raw : z ∈ q_raw.support := q_raw.support_bypass_subset_support hz
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hz_raw
    obtain ⟨u, hu_supp, rfl⟩ := hz_raw
    have h_ub := h_ham_le (e.symm x) u (hq_supp u hu_supp)
    rw [e.apply_symm_apply] at h_ub
    exact h_ub
  exact ⟨G_hat, hGhat_card, hGhat_edge, hGhat_path⟩

/-- **Theorem 1.2 from Theorem 1.3 (`S = PEmpty` specialization)** -/
theorem thm_1_2_from_1_3
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    (h_1_3 : ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ)) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (c c₀ A β₁ β₂ : ℝ),
            (2 : ℝ) ^ (-M * C ^ (4 * p)) ≤ (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
            (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c ∧
            0 < c₀ ∧ 0 < A ∧ 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * Real.logb 2 (nSeq j : ℝ) ∧
                  (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A ∧
                  ∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) := by
  obtain ⟨M₁, c, c₀, β₁, β₂, A, hM₁_pos, h_consts, h_main⟩ := h_1_3
  refine ⟨81 * M₁, by positivity, ?_⟩
  intro p hp C hC
  let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
  obtain ⟨_, hc₀_pos, hβ₁_pos, hβ₁_le, hA_pos⟩ := h_consts C₁ (le_max_left 3 _)
  obtain ⟨hc_4p, hc_3p, nSeq, hn_strict, hn_ge2, h_inst⟩ := h_main p hp C hC
  refine ⟨c C₁, c₀ C₁, A C₁, β₁ C₁, β₂ C₁, hc_4p, hc_3p, hc₀_pos, hA_pos, hβ₁_pos, hβ₁_le,
    nSeq, hn_strict, hn_ge2, ?_⟩
  intro j
  obtain ⟨d, P, hd_pos, hd_lo, hd_hi, hP_bool, hP_inj, hP_ar, h_span⟩ := h_inst j
  refine ⟨d, P, hd_pos, hd_lo, hd_hi, hP_bool, hP_inj, hP_ar, ?_⟩
  intro G hGeom
  obtain ⟨H, w, hSpan, hEdge_le⟩ :=
    Geometry.geometric_spanner_to_steiner h_lp hp P C G hGeom
  exact le_trans (h_span PEmpty H w hSpan) hEdge_le

end HighDimSteinerSpanners.Proofs.Projection
