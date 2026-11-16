/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

public import Mathlib.Analysis.Normed.Lp.PiLp
public import LeanPool.SteinerSpanners.Defs

/-! # Metric and embedding infrastructure for Steiner spanners

Ported from the upstream formalization and shared by the geometric, projection, bucketing,
and hypercube constructions. -/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.Geometry

noncomputable section

/-- The explicit finite-coordinate distance agrees with Mathlib's `WithLp` metric. -/
lemma lpDist_eq_toLp_dist (p : ℝ) (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → ℝ) :
    lpDist p x y =
      dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by
  have hp0 : 0 < p := by linarith
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by positivity
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [PiLp.dist_eq_sum (p := ENNReal.ofReal p) (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
  simp only [ENNReal.toReal_ofReal hp0.le, lpDist, Real.dist_eq, one_div]

/-- One-hot embedding turns Hamming distance into the corresponding scaled `ell-p` distance. -/
lemma oneHotEmbed_lpDist {N q : ℕ} (p : ℝ) (hp : 1 ≤ p) : ∀ x y : Fin N → Fin q,
    lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p) := by
  classical
  have hp_ne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  intro x y
  unfold lpDist
  congr 1
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  have h_inner : ∀ v : Fin N,
      (∑ c : Fin q,
        |oneHotEmbed x (finProdFinEquiv (v, c)) - oneHotEmbed y (finProdFinEquiv (v, c))| ^ p) =
        2 * (if x v ≠ y v then (1 : ℝ) else 0) := by
    intro v
    dsimp only [oneHotEmbed]
    simp only [Equiv.symm_apply_apply]
    by_cases hne : x v = y v
    · simp [hne, Real.zero_rpow hp_ne]
    · simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte, mul_one]
      rw [← Finset.sum_subset (Finset.subset_univ ({x v, y v} : Finset (Fin q)))]
      · rw [Finset.sum_pair hne]
        have hne' : y v ≠ x v := Ne.symm hne
        simp only [↓reduceIte, hne, hne', sub_zero, zero_sub, abs_one, abs_neg, Real.one_rpow]
        norm_num
      · intro c _ hc
        have h1 : x v ≠ c := fun h => hc (by simp [h])
        have h2 : y v ≠ c := fun h => hc (by simp [h])
        simp [h1, h2, Real.zero_rpow hp_ne]
  simp_rw [h_inner, ← Finset.mul_sum]
  rw [Finset.sum_boole]
  rfl

private lemma lpDist_nonneg {p : ℝ} {d : ℕ} (x y : Fin d → ℝ) :
    0 ≤ lpDist p x y := by
  unfold lpDist
  positivity

/-- A geometric spanner is a nonmetric Steiner spanner with no added vertices and
no increase in edge count, provided `lpDist` agrees with the standard `WithLp` distance. -/
lemma geometric_spanner_to_steiner
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 1 ≤ p) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) (hGeom : IsGeometricSpanner p P C G) :
    ∃ (H : SimpleGraph (Fin n ⊕ PEmpty)) (w : Sym2 (Fin n ⊕ PEmpty) → ℝ),
      IsNonMetricSteinerSpanner p P C H w ∧
      (Nat.card H.edgeSet : ℝ) ≤ (Nat.card G.edgeSet : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let proj : Fin n ⊕ PEmpty → Fin n := Sum.elim id PEmpty.elim
  let wG : Sym2 (Fin n) → ℝ :=
    Sym2.lift ⟨fun u v => lpDist p (P u) (P v), fun u v => by
      simp only [lpDist, abs_sub_comm]⟩
  let H : SimpleGraph (Fin n ⊕ PEmpty) :=
    { Adj := fun x y => G.Adj (proj x) (proj y)
      symm := ⟨fun _ _ h => G.adj_symm h⟩
      loopless := ⟨fun _ h => G.irrefl h⟩ }
  let w : Sym2 (Fin n ⊕ PEmpty) → ℝ := fun e => wG (Sym2.map proj e)
  refine ⟨H, w, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro e _
      revert e
      refine Sym2.ind (fun x y _ => ?_)
      simpa [w, wG] using lpDist_nonneg (P (proj x)) (P (proj y))
    · intro i j
      have hwalk_lb : ∀ {u v : Fin n ⊕ PEmpty} (q : H.Walk u v),
          lpDist p (P (proj u)) (P (proj v)) ≤ walkWeight w q := by
        intro u v q
        induction q with
        | @nil u =>
          simp [walkWeight, h_lp p hp]
        | @cons u b v _ q' ih =>
          have htri : lpDist p (P (proj u)) (P (proj v)) ≤
              lpDist p (P (proj u)) (P (proj b)) + lpDist p (P (proj b)) (P (proj v)) := by
            simp only [h_lp p hp]
            exact dist_triangle _ _ _
          have hw_eq : w s(u, b) = lpDist p (P (proj u)) (P (proj b)) := by
            simp [w, wG]
          simp only [walkWeight, hw_eq]
          linarith
      exact le_iInf (fun q => ENNReal.ofReal_le_ofReal (hwalk_lb q))
    · intro i j
      let emb : G →g H := ⟨Sum.inl, fun h => h⟩
      have hww_map : ∀ {u v : Fin n} (q : G.Walk u v),
          walkWeight w (q.map emb) = walkWeight wG q := by
        intro u v q
        induction q with
        | nil => simp [walkWeight]
        | @cons u b v _ q' ih =>
          simp only [SimpleGraph.Walk.map_cons, walkWeight, ih]
          rfl
      have hle_gd : graphDist H w (.inl i) (.inl j) ≤ graphDist G wG i j := by
        unfold graphDist
        refine le_iInf (fun q => ?_)
        calc
          (⨅ p_w : H.Walk (.inl i) (.inl j), ENNReal.ofReal (walkWeight w p_w))
            ≤ ENNReal.ofReal (walkWeight w (q.map emb)) := iInf_le _ (q.map emb)
          _ = ENNReal.ofReal (walkWeight wG q) := by rw [hww_map]
      exact le_trans hle_gd (hGeom i j)
  · have hproj_inj : Function.Injective proj := by
      rintro (u | s) (v | s) h
      · exact congrArg Sum.inl h
      · exact PEmpty.elim s
      · exact PEmpty.elim s
      · exact PEmpty.elim s
    let f_edge : H.edgeSet → G.edgeSet := fun e =>
      ⟨Sym2.map proj e.1, by
        rcases e with ⟨s, hs⟩
        revert hs
        refine Sym2.ind (fun x y hs => ?_) s
        simpa [SimpleGraph.mem_edgeSet] using hs⟩
    have hf_inj : Function.Injective f_edge := by
      intro e₁ e₂ heq
      apply Subtype.ext
      exact Sym2.map.injective hproj_inj (Subtype.mk.inj heq)
    have hnat : Nat.card H.edgeSet ≤ Nat.card G.edgeSet :=
      Nat.card_le_card_of_injective f_edge hf_inj
    exact_mod_cast hnat

end

end HighDimSteinerSpanners.Proofs.Geometry
