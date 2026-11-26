/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.TripartiteSlack
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Saturated tripartite pieces and their edge-disjoint triangles. -/

@[expose] public section

open Finset

namespace GapExtremal.R434

variable {V : Type} [Fintype V] [DecidableEq V]
variable (B : SimpleGraph V) [DecidableRel B.Adj]

theorem tight_tripartite (c : V → Fin 3) (hc : ∀ ⦃u v⦄, B.Adj u v → c u ≠ c v)
    (Q : Finset V) (ht : 3 * e B Q = Q.card ^ 2) :
    (∀ i : Fin 3, 3 * (partOf c Q i).card = Q.card) ∧
      (∀ ⦃u v⦄, u ∈ Q → v ∈ Q → c u ≠ c v → B.Adj u v) := by
  let a := (partOf c Q 0).card
  let b := (partOf c Q 1).card
  let d := (partOf c Q 2).card
  have hsub := induced_edges_subset_crossPairs B c hc Q
  have hcard : ((crossPairs c Q).image (fun p => s(p.1,p.2))).card = a * b + a * d + b * d := by
    rw [card_image_of_injOn (crossPairs_injOn c Q), crossPairs_card]
  have hle := card_le_card hsub
  rw [hcard] at hle
  change e B Q ≤ a * b + a * d + b * d at hle
  have hn : Q.card = a + b + d := partOf_card_sum c Q
  have ht' := ht
  rw [hn] at ht'
  have hR : (3 : ℝ) * e B Q = ((a : ℝ) + b + d) ^ 2 := by exact_mod_cast ht'
  have hleR : (e B Q : ℝ) ≤ (a : ℝ) * b + a * d + b * d := by exact_mod_cast hle
  have hab0 := sq_nonneg ((a : ℝ) - b)
  have had0 := sq_nonneg ((a : ℝ) - d)
  have hbd0 := sq_nonneg ((b : ℝ) - d)
  have hab : a = b := by
    have hz : ((a : ℝ) - b) ^ 2 = 0 := by nlinarith only [hR, hleR, hab0, had0, hbd0]
    have hdiff : (a : ℝ) - b = 0 := (pow_eq_zero_iff (by decide)).mp hz
    exact_mod_cast (sub_eq_zero.mp hdiff)
  have had : a = d := by
    have hz : ((a : ℝ) - d) ^ 2 = 0 := by nlinarith only [hR, hleR, hab0, had0, hbd0]
    have hdiff : (a : ℝ) - d = 0 := (pow_eq_zero_iff (by decide)).mp hz
    exact_mod_cast (sub_eq_zero.mp hdiff)
  have he : e B Q = a * b + a * d + b * d := by
    have hR' : (e B Q : ℝ) = (a : ℝ) * b + a * d + b * d := by
      have habR : (a : ℝ) = b := by exact_mod_cast hab
      have hadR : (a : ℝ) = d := by exact_mod_cast had
      rw [← habR, ← hadR] at hR ⊢
      linarith [show ((a : ℝ) + a + a) ^ 2 = 9 * (a : ℝ) ^ 2 by ring]
    exact_mod_cast hR'
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard]; exact he.ge)
  constructor
  · intro i
    fin_cases i
    · change 3 * a = Q.card
      omega
    · change 3 * b = Q.card
      omega
    · change 3 * d = Q.card
      omega
  · intro u v hu hv hne
    suffices h : s(u,v) ∈ (inducedOn B Q).edgeFinset from
      (show B.Adj u v ∧ u ∈ Q ∧ v ∈ Q from SimpleGraph.mem_edgeFinset.mp h).1
    rw [heq]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mem_image.mpr ⟨(u,v), crossPairs_iff.mpr ⟨hu, hv, hlt⟩, rfl⟩
    · exact mem_image.mpr ⟨(v,u), crossPairs_iff.mpr ⟨hv, hu, hgt⟩, Sym2.eq_swap⟩

theorem induced_edges_disjoint_of_pack {P : Finset (Finset V)} (hP : IsPack P) :
    (P : Set (Finset V)).PairwiseDisjoint (fun Q => (inducedOn B Q).edgeFinset) := by
  intro Q hQ Q' hQ' hne
  change Disjoint (inducedOn B Q).edgeFinset (inducedOn B Q').edgeFinset
  rw [Finset.disjoint_left]
  intro f h₁ h₂
  induction f using Sym2.inductionOn with
  | _ u v =>
    have hu : B.Adj u v ∧ u ∈ Q ∧ v ∈ Q := SimpleGraph.mem_edgeFinset.mp h₁
    have hv : B.Adj u v ∧ u ∈ Q' ∧ v ∈ Q' := SimpleGraph.mem_edgeFinset.mp h₂
    have hsub : ({u,v} : Finset V) ⊆ Q ∩ Q' := by
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact mem_inter.mpr ⟨hu.2.1, hv.2.1⟩
      · exact mem_inter.mpr ⟨hu.2.2, hv.2.2⟩
    have hcard := card_le_card hsub
    rw [Finset.card_pair hu.1.ne] at hcard
    have hle := hP Q hQ Q' hQ' hne
    omega

end GapExtremal.R434
