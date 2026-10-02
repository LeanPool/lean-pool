/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.TriangleWeight
import Aesop

/-!
# Counting rooted K₄ partners of a triangle edge

A low-degree vertex of a triangle bounds the possible fourth vertices of
every rooted K₄ transfer. This is the combinatorial part of nonnegativity.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For one edge of a triangle, the number of eligible rooted K₄ partners is at
most the minimum degree minus one, provided the triangle has a vertex of degree
at most the minimum degree plus one. -/
public theorem k4_partner_count_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (z : V) (hzt : z ∈ t) (hzdeg : G.degree z ≤ G.minDegree + 1) :
    ∀ e ∈ triEdges t,
      (((Finset.univ : Finset (Sym2 V)).filter
        (fun e' => K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e)).card : ℝ)
        ≤ (G.minDegree : ℝ) - 1 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
    is3Clique_iff.mp ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
  have hab' : a ≠ b := hab.ne
  have hac' : a ≠ c := hac.ne
  have hbc' : b ≠ c := hbc.ne
  have hcase (p q r : V) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
      (hpqA : G.Adj p q) (hprA : G.Adj p r) (hqrA : G.Adj q r)
      (hz : z ∈ ({p, q, r} : Finset V)) :
      ((Finset.univ.filter (fun e' : Sym2 V =>
        K4pair G (s(p, q)) e' ∧
          ∃ v, v ∈ ({p, q, r} : Finset V) ∧ v ∈ e' ∧ v ∉ s(p, q))).card : ℝ)
        ≤ (G.minDegree : ℝ) - 1 := by
    let W := G.neighborFinset z \ (({p, q, r} : Finset V).erase z)
    let S := Finset.univ.filter (fun e' : Sym2 V =>
      K4pair G (s(p, q)) e' ∧
        ∃ v, v ∈ ({p, q, r} : Finset V) ∧ v ∈ e' ∧ v ∉ s(p, q))
    have hsub : S ⊆ W.image (fun w => s(r, w)) := by
      intro e' he'
      have hh := (Finset.mem_filter.mp he').2
      rcases hh.2 with ⟨v, hvtri, hve', hvnot⟩
      have hv : v = r := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvtri
        simp only [Sym2.mem_iff, not_or] at hvnot
        aesop
      subst v
      induction e' using Sym2.inductionOn with | _ x y =>
        simp only [Sym2.mem_iff] at hve'
        have hcl := (k4pair_iff_clique G p q x y).mp hh.1
        have hdist := card4_pairwise hcl.card_eq
        rcases hve' with hxr | hyr
        · subst x
          refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
          apply Finset.mem_sdiff.mpr
          have hpy : p ≠ y := hdist.2.2.1
          have hqy : q ≠ y := hdist.2.2.2.2.1
          have hry : r ≠ y := hdist.2.2.2.2.2
          have hapy : G.Adj p y := hcl.1 (by simp) (by simp) hpy
          have haqy : G.Adj q y := hcl.1 (by simp) (by simp) hqy
          have hary : G.Adj r y := hcl.1 (by simp) (by simp) hry
          rcases (show z = p ∨ z = q ∨ z = r by simpa using hz) with rfl | rfl | rfl
          · exact ⟨(G.mem_neighborFinset _ _).mpr hapy, by
              intro hy
              simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
              aesop⟩
          · exact ⟨(G.mem_neighborFinset _ _).mpr haqy, by
              intro hy
              simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
              aesop⟩
          · exact ⟨(G.mem_neighborFinset _ _).mpr hary, by
              intro hy
              simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
              aesop⟩
        · subst y
          refine Finset.mem_image.mpr ⟨x, ?_, by rw [Sym2.eq_iff]; aesop⟩
          apply Finset.mem_sdiff.mpr
          have hpx : p ≠ x := hdist.2.1
          have hqx : q ≠ x := hdist.2.2.2.1
          have hxr : x ≠ r := hdist.2.2.2.2.2
          have hapx : G.Adj p x := hcl.1 (by simp) (by simp) hpx
          have haqx : G.Adj q x := hcl.1 (by simp) (by simp) hqx
          have harx : G.Adj r x := hcl.1 (by simp) (by simp) hxr.symm
          rcases (show z = p ∨ z = q ∨ z = r by simpa using hz) with rfl | rfl | rfl
          · exact ⟨(G.mem_neighborFinset _ _).mpr hapx, by
              intro hx
              simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
              aesop⟩
          · exact ⟨(G.mem_neighborFinset _ _).mpr haqx, by
              intro hx
              simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
              aesop⟩
          · exact ⟨(G.mem_neighborFinset _ _).mpr harx, by
              intro hx
              simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
              aesop⟩
    have hcard : S.card ≤ W.card := calc
      S.card ≤ (W.image (fun w => s(r, w))).card := Finset.card_le_card hsub
      _ ≤ W.card := Finset.card_image_le
    have htriCard : (({p, q, r} : Finset V).erase z).card = 2 := by
      have ht3 : ({p, q, r} : Finset V).card = 3 := by simp [hpq, hpr, hqr]
      rw [Finset.card_erase_of_mem hz, ht3]
    have heraseSub : ({p, q, r} : Finset V).erase z ⊆ G.neighborFinset z := by
      intro u hu
      have hut := (Finset.mem_erase.mp hu).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hut
      rcases (show z = p ∨ z = q ∨ z = r by simpa using hz) with rfl | rfl | rfl
      · rcases hut with rfl | rfl | rfl
        · exact False.elim ((Finset.mem_erase.mp hu).1 rfl)
        · exact (G.mem_neighborFinset _ _).mpr hpqA
        · exact (G.mem_neighborFinset _ _).mpr hprA
      · rcases hut with rfl | rfl | rfl
        · exact (G.mem_neighborFinset _ _).mpr hpqA.symm
        · exact False.elim ((Finset.mem_erase.mp hu).1 rfl)
        · exact (G.mem_neighborFinset _ _).mpr hqrA
      · rcases hut with rfl | rfl | rfl
        · exact (G.mem_neighborFinset _ _).mpr hprA.symm
        · exact (G.mem_neighborFinset _ _).mpr hqrA.symm
        · exact False.elim ((Finset.mem_erase.mp hu).1 rfl)
    have hW : W.card = G.degree z - 2 := by
      dsimp [W]
      rw [Finset.card_sdiff_of_subset heraseSub, G.card_neighborFinset_eq_degree, htriCard]
    have hz2 : 2 ≤ G.degree z := by
      have h := Finset.card_le_card heraseSub
      rw [htriCard, G.card_neighborFinset_eq_degree] at h
      exact h
    have hn : S.card ≤ G.minDegree - 1 := by
      rw [hW] at hcard
      omega
    have hnR : (S.card : ℝ) ≤ ((G.minDegree - 1 : ℕ) : ℝ) := by
      exact_mod_cast hn
    rw [Nat.cast_sub (by omega : 1 ≤ G.minDegree)] at hnR
    simpa [S] using hnR
  have hedge : triEdges {a, b, c} = {s(a, b), s(a, c), s(b, c)} := by
    ext f
    induction f using Sym2.inductionOn with | _ x y =>
      simp only [triEdges, mem_filter, mem_sym2_iff, mem_insert, mem_singleton,
        Sym2.mk_isDiag_iff, Sym2.eq_iff]
      aesop
  intro e he
  rw [hedge] at he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact hcase a b c hab' hac' hbc' hab hac hbc hzt
  · simpa [Finset.insert_comm, Finset.pair_comm] using
      hcase a c b hac' hab' hbc'.symm hac hab hbc.symm
        (by simp only [Finset.mem_insert, Finset.mem_singleton] at hzt ⊢; tauto)
  · simpa [Finset.insert_comm, Finset.pair_comm] using
      hcase b c a hbc' hab'.symm hac'.symm hbc hab.symm hac.symm
        (by simp only [Finset.mem_insert, Finset.mem_singleton] at hzt ⊢; tauto)

end LeanPool.DrossFractionalTriangleDecomposition
