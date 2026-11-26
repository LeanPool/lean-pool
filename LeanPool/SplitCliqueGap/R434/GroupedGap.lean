/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.GroupedHosts
public import LeanPool.SplitCliqueGap.R434.FiniteR434
import Mathlib.Tactic.Ring

/-! Transfer with compressed role matchings and the compact exterior coloring. -/

@[expose] public section
namespace GapExtremal.R434.EHPS
open Finset

/-- The host-count multiplier for the grouped assignment construction. -/
def groupedHostFactor (j : ℕ) := 81 + 288 * j

theorem grouped_host_order (m j : ℕ) [NeZero m] :
    Fintype.card ((H54.Role × ProductGrid m j) ⊕
      H54.GroupedHost (ProductGrid m j) (CompactExterior.Label j)) =
      groupedHostFactor j * (m ^ 2) ^ j := by
  have hc : Fintype.card (ProductGrid m j) = (m ^ 2) ^ j := by simp [ZMod.card, pow_two]
  simp only [H54.GroupedHost, Fintype.card_sum, Fintype.card_prod, hc, Fintype.card_fin,
    H54.missing_role_count, groupedHostFactor]
  ring

theorem finite_gap_of_product_grouped {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m) (hj : 1 ≤ j) (hn₀ : 0 < n)
    (hn : groupedHostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G 0 ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  classical
  let fallback : CompactExterior.Label j := (⟨0,by omega⟩,0,0,0)
  let χ (a : ProductGrid m j) := (CompactExterior.colour hm hε a).getD fallback
  have hχ (a b : ProductGrid m j) (ha : a ∉ productSupport ε m j)
      (hb : b ∉ productSupport ε m j) (hc : χ a = χ b) :
      productHalf m j * (a+b) ∉ productSupport ε m j := by
    apply CompactExterior.mid_outside hm hε ha hb
    simp only [CompactExterior.colour, dite_eq_left ha, dite_eq_left hb, Option.some.injEq]
    simpa only [χ, CompactExterior.colour, dite_eq_left ha, dite_eq_left hb, Option.getD_some]
      using hc
  have base := H54.grouped_host_hyp (productHalf m j) (productSupport ε m j)
    (productHalf_spec hm) χ hχ
  exact finite_gap_of_product_with hε hε₁ hm fun I _ hi hy => by
    obtain ⟨V,fV,dV,G,hcard,hs,hconn,hgap⟩ :=
      exact_graph_of_host_scores base ((0,0),0) n ((grouped_host_order m j).trans_le hn) I hi hy
    exact ⟨V,fV,dV,G,hcard,hs,hconn,⟨hcard ▸ hn₀,fun _ hd => (Nat.not_lt_zero _ hd).elim⟩,hgap⟩

end GapExtremal.R434.EHPS
