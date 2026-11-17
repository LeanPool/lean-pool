/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

public import LeanPool.SteinerSpanners.CSP.ClosePairs

/-! # Existence for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

private abbrev Assignment (C₁ r : ℕ) := Fin (2 ^ cspL C₁ * r) → Fin (cspQ C₁)

private abbrev Outcome (C₁ r : ℕ) := cspIota (2 ^ cspL C₁ * r) (cspQ C₁) → Bool

private lemma hammingDistance_symm : ∀ {N q : ℕ} (x y : Fin N → Fin q), dHam x y = dHam y x :=
  by
  intro N q x y
  unfold dHam disagreeSet
  congr 1
  ext v
  simp [ne_comm]

private lemma symmetricRandomRelation : ∀ {N q : ℕ} (ω : cspIota N q → Bool), Symmetric2CSP
    (symROf ω) := by
  intro N q ω u v c₁ c₂
  unfold symROf
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · have hnot : ¬ v < u := lt_asymm hlt
    simp [hlt, hnot]
  · simp
  · have hnot : ¬ u < v := lt_asymm hgt
    simp [hgt, hnot]

private lemma homQueries_satisfyingSet_iff : ∀ {N q : ℕ} (ω : cspIota N q → Bool) (x : Fin N →
    Fin q),
    (∀ t ∈ homQueries x, ω (Sum.inl t) = true) ↔ x ∈ satisfyingSet (symROf ω) := by
  intro N q ω x
  simp only [satisfyingSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ht u v huv
    have h := ht (u, v, x u, x v) (by
      simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(u, v), huv, rfl⟩)
    simpa [symROf, ite_eq_left huv] using h
  · intro hhom t ht
    simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
    have h := hhom u v huv
    simpa [symROf, ite_eq_left huv] using h

private lemma weightedFilteredCardinality_sum : ∀ {Ω α : Type} [Fintype Ω] (W : Ω → ℝ) (S :
    Finset α)
    (P : Ω → α → Prop) [∀ ω, DecidablePred (P ω)],
    ∑ ω : Ω, W ω * ((S.filter (P ω)).card : ℝ) =
    ∑ a ∈ S, ∑ ω : Ω, (if P ω a then W ω else 0) := by
  intro Ω α _ W S P _
  have h1 : ∀ ω : Ω,
      W ω * ((S.filter (P ω)).card : ℝ) = ∑ a ∈ S, (if P ω a then W ω else 0) := by
    intro ω
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs <;> simp
  simp_rw [h1]
  exact Finset.sum_comm

private lemma degreeSquare_cardinality_bound : ∀ {V : Type} [Fintype V] [DecidableEq V]
    (Rel : V → V → Prop) [DecidableRel Rel] (S : Finset V),
    (∑ x ∈ S, ((S.filter (fun y => Rel x y)).card : ℝ) ^ 2) ≤
    (((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) +
    (((Finset.univ.filter (fun xyz : V × V × V =>
    Rel xyz.1 xyz.2.1 ∧ Rel xyz.1 xyz.2.2 ∧ xyz.2.1 ≠ xyz.2.2)).filter
    (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card : ℝ) := by
  intro V _ _ Rel _ S
  let Nx := fun x : V => S.filter (fun y => Rel x y)
  let T3_off := Finset.univ.filter (fun xyz : V × V × V =>
    Rel xyz.1 xyz.2.1 ∧ Rel xyz.1 xyz.2.2 ∧ xyz.2.1 ≠ xyz.2.2)
  have hsq_nat : ∀ x ∈ S,
      (Nx x).card ^ 2 ≤ (Nx x).card + ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card := by
    intro x _
    have hcard_prod : (Nx x).card ^ 2 = (Nx x ×ˢ Nx x).card := by
      rw [sq, Finset.card_product]
    have hcov_nx : Nx x ×ˢ Nx x ⊆
        (Nx x ×ˢ Nx x).filter (fun yz => yz.1 = yz.2) ∪
        (Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2) := by
      intro yz hyz
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases h : yz.1 = yz.2
      · exact Or.inl ⟨hyz, h⟩
      · exact Or.inr ⟨hyz, h⟩
    have hc1 := Finset.card_le_card hcov_nx
    have hc2 := Finset.card_union_le
      ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 = yz.2))
      ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2))
    have hdiag : ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 = yz.2)).card ≤ (Nx x).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro yz hyz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hyz
        exact hyz.1.1
      · intro yz₁ h₁ yz₂ h₂ heq
        simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
        ext
        · exact heq
        · rw [← h₁.2, ← h₂.2, heq]
    omega
  have hsum1 : ∑ x ∈ S, (Nx x).card =
      ((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card := by
    have hbi : (S ×ˢ S).filter (fun xy => Rel xy.1 xy.2) =
        S.biUnion (fun x => (Nx x).image (fun y => (x, y))) := by
      ext xy
      simp only [Nx, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨hx, hy⟩, hr_xy⟩
        exact ⟨xy.1, hx, xy.2, ⟨hy, hr_xy⟩, Prod.eta xy⟩
      · rintro ⟨x, hx, y, ⟨hy, hr_xy⟩, rfl⟩
        exact ⟨⟨hx, hy⟩, hr_xy⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl
        (fun x _ => (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm)
    · intro x₁ _ x₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
      exact hne (Prod.mk.inj hp).1.symm
  have hsum2 : ∑ x ∈ S, ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card ≤
      (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card := by
    have hdisj : (S : Set V).PairwiseDisjoint
        (fun x => (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image (fun yz => (x, yz)))) := by
      intro x₁ _ x₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
      exact hne (Prod.mk.inj hp).1.symm
    have hsub : S.biUnion
        (fun x => (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image (fun yz => (x, yz)))) ⊆
        T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S) := by
      intro xyz hxyz
      rcases Finset.mem_biUnion.mp hxyz with ⟨x, hx, himg⟩
      rcases Finset.mem_image.mp himg with ⟨⟨y, z⟩, hyz, rfl⟩
      simp only [Nx, Finset.mem_filter, Finset.mem_product] at hyz
      simp only [T3_off, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hyz.1.1.2, hyz.1.2.2, hyz.2⟩, hx, hyz.1.1.1, hyz.1.2.1⟩
    calc
      ∑ x ∈ S, ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card
        = ∑ x ∈ S, (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image
            (fun yz => (x, yz))).card := by
            refine Finset.sum_congr rfl (fun x _ =>
              (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm)
      _ = (S.biUnion (fun x => (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image
            (fun yz => (x, yz))))).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card :=
            Finset.card_le_card hsub
  have hnat_tot : ∑ x ∈ S, (Nx x).card ^ 2 ≤
      ((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card +
      (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card := by
    calc
      ∑ x ∈ S, (Nx x).card ^ 2
        ≤ ∑ x ∈ S, ((Nx x).card + ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card) :=
          Finset.sum_le_sum hsq_nat
      _ = (∑ x ∈ S, (Nx x).card) +
            ∑ x ∈ S, ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card :=
          Finset.sum_add_distrib
      _ ≤ ((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card +
            (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card := by
          rw [hsum1]
          exact Nat.add_le_add_left hsum2 _
  exact_mod_cast hnat_tot

private lemma edgeSquare_cardinality_bound : ∀ {V : Type} [Fintype V] [DecidableEq V]
    (Rel : V → V → Prop) [DecidableRel Rel], Std.Symm Rel → ∀ (S : Finset V),
    ((((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) ^ 2) ≤
    4 * (∑ x ∈ S, ((S.filter (fun y => Rel x y)).card : ℝ) ^ 2) +
    (((Finset.univ.filter (fun e₁₂ : (V × V) × (V × V) =>
    Rel e₁₂.1.1 e₁₂.1.2 ∧ Rel e₁₂.2.1 e₁₂.2.2 ∧
    e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
    e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)).filter
    (fun e₁₂ => e₁₂.1.1 ∈ S ∧ e₁₂.1.2 ∈ S ∧ e₁₂.2.1 ∈ S ∧ e₁₂.2.2 ∈ S)).card : ℝ) := by
  intro V _ _ Rel _ hSymm S
  let Eω := (S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)
  let Nx := fun x : V => S.filter (fun y => Rel x y)
  let T3ω := S.biUnion (fun x => ((Nx x ×ˢ Nx x).image (fun yz => (x, yz))))
  let E4_d := Finset.univ.filter (fun e₁₂ : (V × V) × (V × V) =>
    Rel e₁₂.1.1 e₁₂.1.2 ∧ Rel e₁₂.2.1 e₁₂.2.2 ∧
    e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
    e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)
  have hT3_card : T3ω.card = ∑ x ∈ S, (Nx x).card ^ 2 := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
        Finset.card_product, sq]
    · intro x₁ _ x₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
      exact hne (Prod.mk.inj hp).1.symm
  have hdisj_sub : ((Eω ×ˢ Eω).filter (fun e₁₂ =>
      e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
      e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)).card ≤
    (E4_d.filter (fun e₁₂ =>
      e₁₂.1.1 ∈ S ∧ e₁₂.1.2 ∈ S ∧ e₁₂.2.1 ∈ S ∧ e₁₂.2.2 ∈ S)).card := by
    apply Finset.card_le_card
    intro e₁₂ he
    simp only [Eω, E4_d, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at he ⊢
    exact ⟨⟨he.1.1.2, he.1.2.2, he.2⟩, he.1.1.1.1, he.1.1.1.2, he.1.2.1.1, he.1.2.1.2⟩
  let O₁ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.1 = e₁₂.1.1)
  let O₂ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.1 = e₁₂.1.2)
  let O₃ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.2 = e₁₂.1.1)
  let O₄ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.2 = e₁₂.1.2)
  have hcov : Eω ×ˢ Eω ⊆ ((O₁ ∪ O₂) ∪ (O₃ ∪ O₄)) ∪
      (Eω ×ˢ Eω).filter (fun e₁₂ =>
        e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
        e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2) := by
    intro e₁₂ he
    simp only [O₁, O₂, O₃, O₄, Finset.mem_union, Finset.mem_filter]
    by_cases h1 : e₁₂.2.1 = e₁₂.1.1
    · exact Or.inl (Or.inl (Or.inl ⟨he, h1⟩))
    · by_cases h2 : e₁₂.2.1 = e₁₂.1.2
      · exact Or.inl (Or.inl (Or.inr ⟨he, h2⟩))
      · by_cases h3 : e₁₂.2.2 = e₁₂.1.1
        · exact Or.inl (Or.inr (Or.inl ⟨he, h3⟩))
        · by_cases h4 : e₁₂.2.2 = e₁₂.1.2
          · exact Or.inl (Or.inr (Or.inr ⟨he, h4⟩))
          · exact Or.inr ⟨he, h1, h2, h3, h4⟩
  have hO₁ : O₁.card ≤ T3ω.card := by
    apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.1, (e₁₂.1.2, e₁₂.2.2)))
    · intro e₁₂ he
      simp only [O₁, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_image] at he ⊢
      refine ⟨e₁₂.1.1, he.1.1.1.1, (e₁₂.1.2, e₁₂.2.2), ?_, rfl⟩
      refine ⟨⟨he.1.1.1.2, he.1.1.2⟩, ⟨he.1.2.1.2, ?_⟩⟩
      rw [← he.2]
      exact he.1.2.2
    · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
      simp only [O₁, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      rw [h₁.2, h₂.2]
  have hO₂ : O₂.card ≤ T3ω.card := by
    apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.2, (e₁₂.1.1, e₁₂.2.2)))
    · intro e₁₂ he
      simp only [O₂, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_image] at he ⊢
      refine ⟨e₁₂.1.2, he.1.1.1.2, (e₁₂.1.1, e₁₂.2.2), ?_, rfl⟩
      refine ⟨⟨he.1.1.1.1, hSymm.symm _ _ he.1.1.2⟩, ⟨he.1.2.1.2, ?_⟩⟩
      rw [← he.2]
      exact he.1.2.2
    · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
      simp only [O₂, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      rw [h₁.2, h₂.2]
  have hO₃ : O₃.card ≤ T3ω.card := by
    apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.1, (e₁₂.1.2, e₁₂.2.1)))
    · intro e₁₂ he
      simp only [O₃, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_image] at he ⊢
      refine ⟨e₁₂.1.1, he.1.1.1.1, (e₁₂.1.2, e₁₂.2.1), ?_, rfl⟩
      refine ⟨⟨he.1.1.1.2, he.1.1.2⟩, ⟨he.1.2.1.1, ?_⟩⟩
      rw [← he.2]
      exact hSymm.symm _ _ he.1.2.2
    · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
      simp only [O₃, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      rw [h₁.2, h₂.2]
  have hO₄ : O₄.card ≤ T3ω.card := by
    apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.2, (e₁₂.1.1, e₁₂.2.1)))
    · intro e₁₂ he
      simp only [O₄, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_image] at he ⊢
      refine ⟨e₁₂.1.2, he.1.1.1.2, (e₁₂.1.1, e₁₂.2.1), ?_, rfl⟩
      refine ⟨⟨he.1.1.1.1, hSymm.symm _ _ he.1.1.2⟩, ⟨he.1.2.1.1, ?_⟩⟩
      rw [← he.2]
      exact hSymm.symm _ _ he.1.2.2
    · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
      simp only [O₄, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      rw [h₁.2, h₂.2]
  have hnat : Eω.card ^ 2 ≤
      4 * (∑ x ∈ S, (Nx x).card ^ 2) +
      (E4_d.filter (fun e₁₂ =>
        e₁₂.1.1 ∈ S ∧ e₁₂.1.2 ∈ S ∧ e₁₂.2.1 ∈ S ∧ e₁₂.2.2 ∈ S)).card := by
    have hprod : Eω.card ^ 2 = (Eω ×ˢ Eω).card := by rw [sq, Finset.card_product]
    have h0 := Finset.card_le_card hcov
    have h1 := Finset.card_union_le ((O₁ ∪ O₂) ∪ (O₃ ∪ O₄))
      ((Eω ×ˢ Eω).filter (fun e₁₂ =>
        e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
        e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2))
    have h2 := Finset.card_union_le (O₁ ∪ O₂) (O₃ ∪ O₄)
    have h3 := Finset.card_union_le O₁ O₂
    have h4 := Finset.card_union_le O₃ O₄
    omega
  exact_mod_cast hnat

open Classical in
private lemma existence_h_prod_iota :
    ∀ (C₁ r_star : ℕ) (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    ∏ i ∈ Finset.image Sum.inr V_keep ∪ Finset.image Sum.inl Q_edges, cspPIota C₁ r_star i =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card := by
  classical
  intro C₁ r_star V_keep Q_edges
  have hdisj : Disjoint
      (V_keep.image (Sum.inr : _ → cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)))
      (Q_edges.image (Sum.inl : _ → cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rcases Finset.mem_image.mp hi1 with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp hi2 with ⟨_, _, h⟩
    cases h
  rw [Finset.prod_union hdisj,
    Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h),
    Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h)]
  simp [cspPIota]

open Classical in
private lemma existence_h_exp_ind :
    ∀ (C₁ r_star : ℕ),
    (∀ (S : Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if ∀ i ∈ S, ω i = true then bernWeight (cspPIota C₁ r_star) ω else (0 : ℝ)) =
    ∏ i ∈ S, cspPIota C₁ r_star i) →
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    ∏ i ∈ Finset.image Sum.inr V_keep ∪ Finset.image Sum.inl Q_edges, cspPIota C₁ r_star i =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    ∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ ∀ t ∈ Q_edges, ω (Sum.inl t) = true then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card := by
  classical
  intro C₁ r_star h_cyl h_prod_iota V_keep Q_edges
  have hcond : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      ((∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ (∀ t ∈ Q_edges, ω (Sum.inl t) = true)) ↔
      (∀ i ∈ V_keep.image Sum.inr ∪ Q_edges.image Sum.inl, ω i = true) := by
    intro ω
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩ _ (⟨x, hx, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact h1 x hx
      · exact h2 t ht
    · intro h
      exact ⟨fun x hx => h _ (Or.inl ⟨x, hx, rfl⟩),
             fun t ht => h _ (Or.inr ⟨t, ht, rfl⟩)⟩
  simp_rw [hcond]
  rw [h_cyl, h_prod_iota]

open Classical in
private lemma existence_hM1 :
    ∀ (C₁ r_star : ℕ),
    ∑ x : Assignment C₁ r_star,
    cspPKeep C₁ r_star * cspPEdge C₁ r_star ^ (homQueries x).card =
    cspN0 C₁ r_star →
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ ∀ t ∈ Q_edges, ω (Sum.inl t) = true then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspPRaw ω).card : ℝ) ≤
    cspN0 C₁ r_star := by
  classical
  intro C₁ r_star h_M1_eq h_exp_ind
  have hM1_exact : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspPRaw ω).card : ℝ) = cspN0 C₁ r_star := by
    unfold cspPRaw
    rw [weightedFilteredCardinality_sum]
    have h1 : ∀ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (if ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true
           then bernWeight (cspPIota C₁ r_star) ω else 0) =
        cspPKeep C₁ r_star * (cspPEdge C₁ r_star) ^ (homQueries x).card := by
      intro x
      have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true) ↔
          ((∀ z ∈ ({x} : Finset _), ω (Sum.inr z) = true) ∧
           (∀ t ∈ homQueries x, ω (Sum.inl t) = true)) := by
        intro ω
        simp
      simp_rw [hiff]
      simpa using h_exp_ind {x} (homQueries x)
    simp_rw [h1]
    exact h_M1_eq
  exact le_of_eq hM1_exact

open Classical in
private lemma existence_h_pair_exp :
    ∀ (C₁ r_star : ℕ),
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ ∀ t ∈ Q_edges, ω (Sum.inl t) = true then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    ∀ {x y : Assignment C₁ r_star},
    x ≠ y →
    (∑ ω : Outcome C₁ r_star,
    if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω then bernWeight (cspPIota C₁ r_star) ω else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (2 : ℕ) * cspPEdge C₁ r_star ^ (homQueries x ∪ homQueries y).card := by
  classical
  intro C₁ r_star h_exp_ind x y hne
  have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω) ↔
      ((∀ z ∈ ({x, y} : Finset _), ω (Sum.inr z) = true) ∧
       (∀ t ∈ homQueries x ∪ homQueries y, ω (Sum.inl t) = true)) := by
    intro ω
    simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
      exact ⟨⟨hx1, hy1⟩, fun t ht => ht.elim (hx2 t) (hy2 t)⟩
    · rintro ⟨⟨hx1, hy1⟩, hq⟩
      exact ⟨⟨hx1, fun t ht => hq t (Or.inl ht)⟩, ⟨hy1, fun t ht => hq t (Or.inr ht)⟩⟩
  simp_rw [hiff]
  rw [h_exp_ind, Finset.card_pair hne]

open Classical in
private lemma existence_h_triple_exp :
    ∀ (C₁ r_star : ℕ),
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ ∀ t ∈ Q_edges, ω (Sum.inl t) = true then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    ∀ {x y z : Assignment C₁ r_star},
    x ≠ y →
    x ≠ z →
    y ≠ z →
    (∑ ω : Outcome C₁ r_star,
    if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω ∧ z ∈ cspPRaw ω then bernWeight (cspPIota C₁ r_star) ω else
    (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (3 : ℕ) * cspPEdge C₁ r_star ^ (homQueries x ∪ homQueries y ∪
    homQueries z).card := by
  classical
  intro C₁ r_star h_exp_ind x y z hxy hxz hyz
  have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω ∧ z ∈ cspPRaw ω) ↔
      ((∀ v ∈ ({x, y, z} : Finset _), ω (Sum.inr v) = true) ∧
       (∀ t ∈ homQueries x ∪ homQueries y ∪ homQueries z, ω (Sum.inl t) = true)) := by
    intro ω
    simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩
      refine ⟨⟨hx1, hy1, hz1⟩, fun t ht => ?_⟩
      rcases ht with (ht | ht) | ht
      · exact hx2 t ht
      · exact hy2 t ht
      · exact hz2 t ht
    · rintro ⟨⟨hx1, hy1, hz1⟩, hq⟩
      exact ⟨⟨hx1, fun t ht => hq t (Or.inl (Or.inl ht))⟩,
             ⟨hy1, fun t ht => hq t (Or.inl (Or.inr ht))⟩,
             ⟨hz1, fun t ht => hq t (Or.inr ht)⟩⟩
  have hcard3 : ({x, y, z} : Finset _).card = 3 := by
    have hx_not : x ∉ ({y, z} : Finset _) := by simp [hxy, hxz]
    rw [Finset.card_insert_of_notMem hx_not, Finset.card_pair hyz]
  simp_rw [hiff]
  rw [h_exp_ind, hcard3]

open Classical in
private lemma existence_h_quad_exp :
    ∀ (C₁ r_star : ℕ),
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)
    × Fin (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ ∀ t ∈ Q_edges, ω (Sum.inl t) = true then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    ∀ {x₁ y₁ x₂ y₂ : Assignment C₁ r_star},
    x₁ ≠ y₁ →
    x₂ ≠ y₂ →
    x₂ ≠ x₁ →
    x₂ ≠ y₁ →
    y₂ ≠ x₁ →
    y₂ ≠ y₁ →
    (∑ ω : Outcome C₁ r_star,
    if x₁ ∈ cspPRaw ω ∧ y₁ ∈ cspPRaw ω ∧ x₂ ∈ cspPRaw ω ∧ y₂ ∈ cspPRaw ω then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (4 : ℕ) *
    cspPEdge C₁ r_star ^ (homQueries x₁ ∪ homQueries y₁ ∪ homQueries x₂ ∪ homQueries y₂).card :=
      by
  classical
  intro C₁ r_star h_exp_ind x₁ y₁ x₂ y₂ h12 h34 h31 h32 h41 h42
  have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (x₁ ∈ cspPRaw ω ∧ y₁ ∈ cspPRaw ω ∧ x₂ ∈ cspPRaw ω ∧ y₂ ∈ cspPRaw ω) ↔
      ((∀ v ∈ ({x₁, y₁, x₂, y₂} : Finset _), ω (Sum.inr v) = true) ∧
       (∀ t ∈ homQueries x₁ ∪ homQueries y₁ ∪ homQueries x₂ ∪ homQueries y₂,
         ω (Sum.inl t) = true)) := by
    intro ω
    simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩, ⟨hw1, hw2⟩⟩
      refine ⟨⟨hx1, hy1, hz1, hw1⟩, fun t ht => ?_⟩
      rcases ht with ((ht | ht) | ht) | ht
      · exact hx2 t ht
      · exact hy2 t ht
      · exact hz2 t ht
      · exact hw2 t ht
    · rintro ⟨⟨hx1, hy1, hz1, hw1⟩, hq⟩
      exact ⟨⟨hx1, fun t ht => hq t (Or.inl (Or.inl (Or.inl ht)))⟩,
             ⟨hy1, fun t ht => hq t (Or.inl (Or.inl (Or.inr ht)))⟩,
             ⟨hz1, fun t ht => hq t (Or.inl (Or.inr ht))⟩,
             ⟨hw1, fun t ht => hq t (Or.inr ht)⟩⟩
  have hcard4 : ({x₁, y₁, x₂, y₂} : Finset _).card = 4 := by
    have hn1 : x₁ ∉ ({y₁, x₂, y₂} : Finset _) := by
      simp [h12, Ne.symm h31, Ne.symm h41]
    have hn2 : y₁ ∉ ({x₂, y₂} : Finset _) := by
      simp [Ne.symm h32, Ne.symm h42]
    rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
      Finset.card_pair h34]
  simp_rw [hiff]
  rw [h_exp_ind, hcard4]

open Classical in
private lemma existence_hE1_exact :
    ∀ (C₁ r_star : ℕ),
    ∑ xy : (Assignment C₁ r_star) × (Fin ((2 : ℕ) ^ cspL C₁ *
    r_star) → Fin (cspQ C₁)) with
    dHam xy.1 xy.2 = r_star,
    cspPKeep C₁ r_star ^ (2 : ℕ) * cspPEdge C₁ r_star ^ (homQueries xy.1 ∪ homQueries xy.2).card
      =
    cspN0 C₁ r_star * cspDStar C₁ r_star →
    (∀ {N q : ℕ} {x y : Fin N → Fin q}, dHam x y = r_star → x ≠ y) →
    (∀ {x y : Assignment C₁ r_star},
    x ≠ y →
    (∑ ω : Outcome C₁ r_star,
    if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω then bernWeight (cspPIota C₁ r_star) ω else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (2 : ℕ) * cspPEdge C₁ r_star ^ (homQueries x ∪ homQueries y).card) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑{xy ∈ cspPRaw ω ×ˢ cspPRaw ω | dHam xy.1 xy.2 =
    r_star}.card : ℝ) =
    cspN0 C₁ r_star * cspDStar C₁ r_star := by
  classical
  intro C₁ r_star h_M0_eq hdHam_ne_of_r h_pair_exp
  let E_all : Finset ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                      (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) :=
    Finset.univ.filter (fun xy => dHam xy.1 xy.2 = r_star)
  have hE_eq_filter : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star) =
        E_all.filter (fun xy => xy.1 ∈ cspPRaw ω ∧ xy.2 ∈ cspPRaw ω) := by
    intro ω
    ext xy
    simp only [E_all, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  simp_rw [hE_eq_filter]
  rw [weightedFilteredCardinality_sum]
  have hcongr : ∑ xy ∈ E_all, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (if xy.1 ∈ cspPRaw ω ∧ xy.2 ∈ cspPRaw ω
       then bernWeight (cspPIota C₁ r_star) ω else 0) =
    ∑ xy ∈ E_all,
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card
        := by
    refine Finset.sum_congr rfl (fun xy hxy => ?_)
    simp only [E_all, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    exact h_pair_exp (hdHam_ne_of_r hxy)
  rw [hcongr]
  exact h_M0_eq

open Classical in
private lemma existence_hW2 :
    ∀ (C₁ r_star : ℕ),
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (1000 : ℝ) ≤ (↑(cspLam0 C₁) : ℝ) →
    (0 : ℝ) < cspN0 C₁ r_star →
    (0 : ℝ) < cspDStar C₁ r_star →
    (1 : ℝ) ≤ cspGamma r_star →
    (∀ (ω : Outcome C₁ r_star),
    (0 : ℝ) ≤ bernWeight (cspPIota C₁ r_star) ω) →
    (∀ {N q : ℕ} {x y : Fin N → Fin q}, dHam x y = r_star → x ≠ y) →
    (∀ {x y z : Assignment C₁ r_star},
    x ≠ y →
    x ≠ z →
    y ≠ z →
    (∑ ω : Outcome C₁ r_star,
    if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω ∧ z ∈ cspPRaw ω then bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (3 : ℕ) *
    cspPEdge C₁ r_star ^ (homQueries x ∪ homQueries y ∪ homQueries z).card) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω *
    (↑{xy ∈ cspPRaw ω ×ˢ cspPRaw ω | dHam xy.1 xy.2 = r_star}.card : ℝ) =
    cspN0 C₁ r_star * cspDStar C₁ r_star →
    ∑ xyz :
    (Assignment C₁ r_star) ×
    (Assignment C₁ r_star) ×
    (Assignment C₁ r_star) with
    dHam xyz.1 xyz.2.1 = r_star ∧ dHam xyz.1 xyz.2.2 = r_star ∧ xyz.2.1 ≠ xyz.2.2,
    cspPKeep C₁ r_star ^ (3 : ℕ) *
    cspPEdge C₁ r_star ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
    (3 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * cspDStar C₁ r_star ^ (2 : ℕ) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω *
    ∑ x ∈ cspPRaw ω, (↑{y ∈ cspPRaw ω | dHam x y = r_star}.card : ℝ) ^ (2 : ℕ) ≤
    (2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * cspDStar C₁ r_star ^ (2 : ℕ) := by
  classical
  intro C₁ r_star hr_ge3001_real hlam0_real hn0_pos hD_pos hγ_ge1 hW_nn hdHam_ne_of_r
      h_triple_exp hE1_exact h_s6_deg
  let T3_off := Finset.univ.filter
    (fun xyz : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
               (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
               (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
      dHam xyz.1 xyz.2.1 = r_star ∧ dHam xyz.1 xyz.2.2 = r_star ∧ xyz.2.1 ≠ xyz.2.2)
  have hW2_off_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        ((T3_off.filter (fun xyz =>
          xyz.1 ∈ cspPRaw ω ∧ xyz.2.1 ∈ cspPRaw ω ∧ xyz.2.2 ∈ cspPRaw ω)).card : ℝ) ≤
      (3 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by
    rw [weightedFilteredCardinality_sum]
    have hcongr : ∑ xyz ∈ T3_off, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if xyz.1 ∈ cspPRaw ω ∧ xyz.2.1 ∈ cspPRaw ω ∧ xyz.2.2 ∈ cspPRaw ω
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
      ∑ xyz ∈ T3_off,
        (cspPKeep C₁ r_star) ^ 3 *
          (cspPEdge C₁ r_star) ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries
            xyz.2.2).card := by
      refine Finset.sum_congr rfl (fun xyz hxyz => ?_)
      simp only [T3_off, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz
      exact h_triple_exp (hdHam_ne_of_r hxyz.1) (hdHam_ne_of_r hxyz.2.1) hxyz.2.2
    rw [hcongr]
    exact h_s6_deg
  have hD_ge2 : (2 : ℝ) ≤ cspDStar C₁ r_star := by
    unfold cspDStar
    have hexp : (1 : ℝ) ≤ (1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
      nlinarith only [hlam0_real, hr_ge3001_real]
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        (∑ x ∈ cspPRaw ω, (((cspPRaw ω).filter (fun y => dHam x y = r_star)).card : ℝ) ^ 2) ≤
    (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        (((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ)) +
    (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        ((T3_off.filter (fun xyz =>
          xyz.1 ∈ cspPRaw ω ∧ xyz.2.1 ∈ cspPRaw ω ∧ xyz.2.2 ∈ cspPRaw ω)).card : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ω _ => ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (degreeSquare_cardinality_bound (fun x y => dHam x y = r_star) (cspPRaw ω)) (hW_nn ω)
  have hdiag_le : cspN0 C₁ r_star * cspDStar C₁ r_star ≤
      (1 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (1 / 2 : ℝ) * cspGamma r_star * cspDStar C₁ r_star := by
      nlinarith only [hγ_ge1, hD_ge2]
    have h2 : 0 ≤ cspN0 C₁ r_star * cspDStar C₁ r_star := by positivity
    have hmul := mul_le_mul_of_nonneg_right h1 h2
    linarith [show ((1 / 2 : ℝ) * cspGamma r_star * cspDStar C₁ r_star) *
      (cspN0 C₁ r_star * cspDStar C₁ r_star) =
      (1 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 by ring]
  linarith only [hstep1, hE1_exact, hW2_off_exp, hdiag_le]

open Classical in
private lemma existence_hE2 :
    ∀ (C₁ r_star : ℕ),
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (6000 : ℝ) ≤ (↑(cspBeta0 C₁) : ℝ) →
    (1 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) →
    (2 : ℝ) ^ ((99 / 100 : ℝ) * (↑(cspBeta0 C₁) : ℝ) * (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) * (↑r_star
    : ℝ)) ≤
    cspN0 C₁ r_star →
    (0 : ℝ) < cspN0 C₁ r_star →
    (0 : ℝ) < cspDStar C₁ r_star →
    (1 : ℝ) ≤ cspGamma r_star →
    (∀ (ω : Outcome C₁ r_star),
    (0 : ℝ) ≤ bernWeight (cspPIota C₁ r_star) ω) →
    (Std.Symm fun (x y : Assignment C₁ r_star) => dHam x y = r_star) →
    (∀ {N q : ℕ} {x y : Fin N → Fin q}, dHam x y = r_star → x ≠ y) →
    (∀ {x₁ y₁ x₂ y₂ : Assignment C₁ r_star},
    x₁ ≠ y₁ →
    x₂ ≠ y₂ →
    x₂ ≠ x₁ →
    x₂ ≠ y₁ →
    y₂ ≠ x₁ →
    y₂ ≠ y₁ →
    (∑ ω : Outcome C₁ r_star,
    if x₁ ∈ cspPRaw ω ∧ y₁ ∈ cspPRaw ω ∧ x₂ ∈ cspPRaw ω ∧ y₂ ∈ cspPRaw ω then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (4 : ℕ) *
    cspPEdge C₁ r_star ^
    (homQueries x₁ ∪ homQueries y₁ ∪ homQueries x₂ ∪ homQueries y₂).card) →
    ∑ e₁₂ :
    ((Assignment C₁ r_star) ×
    (Assignment C₁ r_star)) ×
    (Assignment C₁ r_star) ×
    (Assignment C₁ r_star) with
    dHam e₁₂.1.1 e₁₂.1.2 = r_star ∧
    dHam e₁₂.2.1 e₁₂.2.2 = r_star ∧
    e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧ e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2,
    cspPKeep C₁ r_star ^ (4 : ℕ) *
    cspPEdge C₁ r_star ^
    (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪ homQueries e₁₂.2.1 ∪
    homQueries e₁₂.2.2).card ≤
    (2 : ℝ) * cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ (2 : ℕ) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω *
    ∑ x ∈ cspPRaw ω, (↑{y ∈ cspPRaw ω | dHam x y = r_star}.card : ℝ) ^ (2 : ℕ) ≤
    (2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * cspDStar C₁ r_star ^ (2 : ℕ) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω *
    (↑{xy ∈ cspPRaw ω ×ˢ cspPRaw ω | dHam xy.1 xy.2 = r_star}.card : ℝ) ^ (2 : ℕ) ≤
    (3 : ℝ) * cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ (2 : ℕ) := by
  classical
  intro C₁ r_star hr_ge3001_real hbeta0_real h22L_real hn0_low hn0_pos hD_pos hγ_ge1 hW_nn
      hRel_symm hdHam_ne_of_r h_quad_exp h_s6_edge hW2
  let E4_disj := Finset.univ.filter
    (fun e₁₂ : ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) ×
               ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) =>
      dHam e₁₂.1.1 e₁₂.1.2 = r_star ∧ dHam e₁₂.2.1 e₁₂.2.2 = r_star ∧
      e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
      e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)
  have hE4_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        ((E4_disj.filter (fun e₁₂ =>
          e₁₂.1.1 ∈ cspPRaw ω ∧ e₁₂.1.2 ∈ cspPRaw ω ∧
          e₁₂.2.1 ∈ cspPRaw ω ∧ e₁₂.2.2 ∈ cspPRaw ω)).card : ℝ) ≤
      2 * cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 := by
    rw [weightedFilteredCardinality_sum]
    have hcongr : ∑ e₁₂ ∈ E4_disj, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if e₁₂.1.1 ∈ cspPRaw ω ∧ e₁₂.1.2 ∈ cspPRaw ω ∧
            e₁₂.2.1 ∈ cspPRaw ω ∧ e₁₂.2.2 ∈ cspPRaw ω
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
      ∑ e₁₂ ∈ E4_disj,
        (cspPKeep C₁ r_star) ^ 4 *
          (cspPEdge C₁ r_star) ^
            (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
             homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card := by
      refine Finset.sum_congr rfl (fun e₁₂ he => ?_)
      simp only [E4_disj, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact h_quad_exp (hdHam_ne_of_r he.1) (hdHam_ne_of_r he.2.1)
        he.2.2.1 he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2
    rw [hcongr]
    exact h_s6_edge
  have hn0_ge8 : (8 : ℝ) ≤ cspN0 C₁ r_star := by
    have hexp3 : (3 : ℝ) ≤
        (99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ) := by
      have hmul1 : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
        nlinarith only [hbeta0_real, h22L_real]
      nlinarith only [hmul1, hr_ge3001_real]
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h8]
    exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp3) hn0_low
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        ((((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ) ^ 2) ≤
    4 * (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        (∑ x ∈ cspPRaw ω, (((cspPRaw ω).filter (fun y => dHam x y = r_star)).card : ℝ) ^ 2)) +
    (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        ((E4_disj.filter (fun e₁₂ =>
          e₁₂.1.1 ∈ cspPRaw ω ∧ e₁₂.1.2 ∈ cspPRaw ω ∧
          e₁₂.2.1 ∈ cspPRaw ω ∧ e₁₂.2.2 ∈ cspPRaw ω)).card : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ω _ => ?_)
    have hp := mul_le_mul_of_nonneg_left
      (edgeSquare_cardinality_bound (fun x y => dHam x y = r_star) hRel_symm (cspPRaw ω)) (hW_nn ω)
    linarith [hp]
  have hov_bound : 8 * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 ≤
      cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 := by
    have hnn : 0 ≤ cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hn0_ge8 hnn
    linarith [show cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 * 8 =
                8 * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 by ring,
              show cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 * cspN0 C₁ r_star =
                cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 by ring]
  linarith only [hstep1, hW2, hE4_exp, hov_bound]

open Classical in
private lemma existence_hBD3_exp :
    ∀ (C₁ r_star : ℕ),
    (3001 : ℕ) ≤ r_star →
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (9 : ℝ) ≤ (↑(C₁ ^ (2 : ℕ)) : ℝ) →
    (1000 : ℝ) ≤ (↑(cspLam0 C₁) : ℝ) →
    (0 : ℝ) < cspPEdge C₁ r_star →
    (0 : ℝ) < cspPKeep C₁ r_star →
    ∑ ab :
    (Assignment C₁ r_star) ×
    (Assignment C₁ r_star) with
    ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star,
    cspPKeep C₁ r_star ^ (2 : ℕ) * cspPEdge C₁ r_star ^ (homQueries ab.1 ∪ homQueries ab.2).card
      ≤
    cspN0 C₁ r_star * (2 : ℝ) ^ ((7 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ) * (↑(cspLam0 C₁) : ℝ) *
    (↑r_star : ℝ)) →
    (0 : ℝ) < cspN0 C₁ r_star →
    (∀ (ω : Outcome C₁ r_star),
    (0 : ℝ) ≤ bernWeight (cspPIota C₁ r_star) ω) →
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset
    (Fin (2 ^ cspL C₁ * r_star) ×
    Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁) × Fin (cspQ C₁))),
    (∑ ω : Outcome C₁ r_star,
    if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ ∀ t ∈ Q_edges, ω (Sum.inl t) = true then
    bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    (∀ (x u : Assignment C₁ r_star),
    dHam x u ≤ C₁ * r_star →
    ∑ z : Assignment C₁ r_star with
    dHam x z ≤ C₁ * r_star ∧ r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card,
    cspPEdge C₁ r_star ^ (homQueries z \ (homQueries x ∪ homQueries u)).card ≤
    (2 : ℝ) ^ (-((12 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ)) * (↑(cspLam0 C₁) : ℝ) * (↑r_star : ℝ))) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBD3 C₁ r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  classical
  intro C₁ r_star hr_ge hr_ge3001_real hC₁_sq_real hlam0_real hp_edge_pos hp_keep_pos h_ball_sum
      hn0_pos hW_nn h_exp_ind h_s5_d3
  let BallPairs := Finset.univ.filter
    (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
              (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
      ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star)
  let Z_d3 := fun x u : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
    Finset.univ.filter (fun z =>
      dHam x z ≤ C₁ * r_star ∧
      r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card)
  let Triples_d3 := BallPairs.biUnion (fun xu => (Z_d3 xu.1 xu.2).image (fun z => (xu.1, (xu.2,
    z))))
  have hd3_distinct : ∀ {N q : ℕ} {x u z : Fin N → Fin q},
      r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card →
      x ≠ u ∧ x ≠ z ∧ u ≠ z := by
    intro N q x u z hlt
    have hpos : 0 < (threeWayDisagree x u z).card := by
      by_contra h0
      have heq0 : (threeWayDisagree x u z).card = 0 := by omega
      rw [heq0, mul_zero] at hlt
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact ⟨fun h => hv.1 (congr_fun h v),
           fun h => hv.2.1 (congr_fun h v),
           fun h => hv.2.2 (congr_fun h v)⟩
  have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (cspBD3 C₁ r_star ω).card ≤ (Triples_d3.filter (fun xuz =>
        xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
        (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true))).card := by
    intro ω
    have hsub : cspBD3 C₁ r_star ω ⊆ (Triples_d3.filter (fun xuz =>
        xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
        (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true))).image Prod.fst := by
      intro x hx
      simp only [cspBD3, Finset.mem_filter] at hx
      rcases hx with ⟨hxP, u, huP, z, hzHom, hdu, hdz, hlt⟩
      have hdist := hd3_distinct hlt
      rw [Finset.mem_image]
      refine ⟨(x, (u, z)), ?_, rfl⟩
      simp only [Triples_d3, BallPairs, Z_d3, Finset.mem_filter, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨(x, u), ⟨hdist.1, hdu⟩, z, ⟨hdz, hlt⟩, rfl⟩, hxP, huP, hzHom⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBD3 C₁ r_star ω).card : ℝ) ≤
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((Triples_d3.filter (fun xuz =>
          xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
          (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true))).card : ℝ) := by
    refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
    exact_mod_cast (hpt ω)
  rw [weightedFilteredCardinality_sum] at hstep1
  have h_d3_ind_exp : ∀ {x u z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)}, x ≠ u →
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if x ∈ cspPRaw ω ∧ u ∈ cspPRaw ω ∧ (∀ t ∈ homQueries z, ω (Sum.inl t) = true)
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries x ∪ homQueries u ∪ homQueries z).card := by
    intro x u z hxu
    have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (x ∈ cspPRaw ω ∧ u ∈ cspPRaw ω ∧ (∀ t ∈ homQueries z, ω (Sum.inl t) = true)) ↔
        ((∀ v ∈ ({x, u} : Finset _), ω (Sum.inr v) = true) ∧
         (∀ t ∈ homQueries x ∪ homQueries u ∪ homQueries z, ω (Sum.inl t) = true)) := by
      intro ω
      simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, ⟨hu1, hu2⟩, hz2⟩
        refine ⟨⟨hx1, hu1⟩, fun t ht => ?_⟩
        rcases ht with (ht | ht) | ht
        · exact hx2 t ht
        · exact hu2 t ht
        · exact hz2 t ht
      · rintro ⟨⟨hx1, hu1⟩, hq⟩
        exact ⟨⟨hx1, fun t ht => hq t (Or.inl (Or.inl ht))⟩,
               ⟨hu1, fun t ht => hq t (Or.inl (Or.inr ht))⟩,
               fun t ht => hq t (Or.inr ht)⟩
    simp_rw [hiff]
    rw [h_exp_ind, Finset.card_pair hxu]
  have hsum_bi : ∑ xuz ∈ Triples_d3, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (if xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
          (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true)
       then bernWeight (cspPIota C₁ r_star) ω else 0) =
    ∑ xu ∈ BallPairs, ((cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
      (∑ z ∈ Z_d3 xu.1 xu.2,
        (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries xu.1 ∪ homQueries xu.2)).card)) := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl (fun xu _ => ?_)
      rw [Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      simp only [Z_d3, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      have hdist := hd3_distinct hz.2
      rw [h_d3_ind_exp hdist.1]
      have hunion : (homQueries xu.1 ∪ homQueries xu.2 ∪ homQueries z).card =
          (homQueries xu.1 ∪ homQueries xu.2).card +
          (homQueries z \ (homQueries xu.1 ∪ homQueries xu.2)).card := by
        rw [← Finset.union_sdiff_self_eq_union (s := homQueries xu.1 ∪ homQueries xu.2) (t :=
          homQueries z),
          Finset.card_union_of_disjoint disjoint_sdiff_self_right]
      rw [hunion, pow_add]
      ring
    · intro xu₁ _ xu₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
      rcases Prod.mk.inj hp with ⟨h1, hp'⟩
      rcases Prod.mk.inj hp' with ⟨h2, _⟩
      exact hne (Prod.ext h1.symm h2.symm)
  have hstep2 : ∑ xu ∈ BallPairs, ((cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
      (∑ z ∈ Z_d3 xu.1 xu.2,
        (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries xu.1 ∪ homQueries xu.2)).card)) ≤
    cspN0 C₁ r_star * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
      (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
    calc
      ∑ xu ∈ BallPairs, _
        ≤ ∑ xu ∈ BallPairs, ((cspPKeep C₁ r_star) ^ 2 *
            (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
            (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
            refine Finset.sum_le_sum (fun xu hxu => ?_)
            simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxu
            exact mul_le_mul_of_nonneg_left (h_s5_d3 xu.1 xu.2 hxu.2) (by positivity)
      _ = (∑ xu ∈ BallPairs, (cspPKeep C₁ r_star) ^ 2 *
            (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
            (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
            (Finset.sum_mul _ _ _).symm
      _ ≤ cspN0 C₁ r_star *
            (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
            mul_le_mul_of_nonneg_right h_ball_sum (by positivity)
  have hstep3 : cspN0 C₁ r_star *
      (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
      (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    have hcomb : (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
        (1 / 4 : ℝ) * cspDeltaBad C₁ r_star := by
      unfold cspDeltaBad
      have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (- (2 : ℝ)) := by norm_num
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hquarter,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hprod_ge : (1 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_ge3001_real]
      nlinarith only [hC₁_sq_real, hprod_ge]
    have hm := mul_le_mul_of_nonneg_left hcomb (le_of_lt hn0_pos)
    linarith [hm,
      show cspN0 C₁ r_star * ((1 / 4 : ℝ) * cspDeltaBad C₁ r_star) =
        (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star by ring,
      mul_assoc (cspN0 C₁ r_star)
        ((2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
        ((2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))]
  rw [hsum_bi] at hstep1
  linarith only [hstep1, hstep2, hstep3]

private lemma exponentialMomentEstimate (A τ n₀ : ℝ) (order : ℕ)
    (hA : 9 ≤ A) (hτ : 1 ≤ τ) (horder : 20 * A ≤ (order : ℝ)) (hn₀ : 0 ≤ n₀) :
    n₀ * (2 : ℝ) ^ (7 * A * τ) * ((2 : ℝ) ^ (-(72 / 100 : ℝ) * τ)) ^ order ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(6 / 10 : ℝ) * τ) * n₀ := by
  have hcomb : (2 : ℝ) ^ (7 * A * τ) * ((2 : ℝ) ^ (-(72 / 100 : ℝ) * τ)) ^ order ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(6 / 10 : ℝ) * τ) := by
    have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (-(2 : ℝ)) := by norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hquarter,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hτ_nonneg : 0 ≤ τ := by linarith only [hτ]
    have hscaled := mul_le_mul_of_nonneg_right horder hτ_nonneg
    have hA_scaled := mul_le_mul_of_nonneg_right hA hτ_nonneg
    nlinarith only [hscaled, hA_scaled, hτ]
  calc
    _ = n₀ * ((2 : ℝ) ^ (7 * A * τ) * ((2 : ℝ) ^ (-(72 / 100 : ℝ) * τ)) ^ order) := by
      ring
    _ ≤ n₀ * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-(6 / 10 : ℝ) * τ)) :=
      mul_le_mul_of_nonneg_left hcomb hn₀
    _ = _ := by ring

open Classical in
private lemma existence_hBch_exp :
    ∀ (C₁ r_star : ℕ),
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (9 : ℝ) ≤ (↑(C₁ ^ (2 : ℕ)) : ℝ) →
    (1000 : ℝ) ≤ (↑(cspLam0 C₁) : ℝ) →
    ∑ ab :
    (Assignment C₁ r_star) ×
    (Assignment C₁ r_star) with
    ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star,
    cspPKeep C₁ r_star ^ (2 : ℕ) * cspPEdge C₁ r_star ^ (homQueries ab.1 ∪ homQueries ab.2).card
      ≤
    cspN0 C₁ r_star * (2 : ℝ) ^ ((7 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ) * (↑(cspLam0 C₁) : ℝ) *
    (↑r_star : ℝ)) →
    (0 : ℝ) < cspN0 C₁ r_star →
    (∀ (ω : Outcome C₁ r_star),
    (0 : ℝ) ≤ bernWeight (cspPIota C₁ r_star) ω) →
    (∀ i : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁),
    0 ≤ cspPIota C₁ r_star i ∧ cspPIota C₁ r_star i ≤ 1) →
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset
    (Fin (2 ^ cspL C₁ * r_star) ×
    Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁) × Fin (cspQ C₁))),
    ∏ i ∈ Finset.image Sum.inr V_keep ∪ Finset.image Sum.inl Q_edges, cspPIota C₁ r_star i =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    (∀ (x w₀ : Assignment C₁ r_star),
    dHam x w₀ ≤ C₁ * r_star →
    ∀ m < cspKCh C₁,
    ∀ (y_prev : Fin m → Assignment C₁ r_star),
    (∀ (t : Fin m), y_prev t ∈ cspPoolCh C₁ r_star x w₀) →
    ∑ y ∈ cspPoolCh C₁ r_star x w₀ \ Finset.image y_prev Finset.univ,
    ∏
    i ∈
    (Finset.image Sum.inr {y} ∪ Finset.image Sum.inl (homQueries y)) \
    cspUCh x w₀ m y_prev,
    cspPIota C₁ r_star i ≤
    (2 : ℝ) ^ (-(72 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑r_star : ℝ))) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBCh C₁ r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  classical
  intro C₁ r_star hr_ge3001_real hC₁_sq_real hlam0_real h_ball_sum hn0_pos hW_nn hp_iota
      h_prod_iota h_s5_ch
  have h_seq :=
    (finite_bernoulli_cylinder_and_sequential_moment (cspPIota C₁ r_star) hp_iota).2.2.2
  let BallPairs := Finset.univ.filter
    (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
              (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
      ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star)
  have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (cspBCh C₁ r_star ω).card ≤ (BallPairs.filter (fun xw =>
        (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
        cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter (fun y => y ∈ cspPRaw
          ω)).card)).card := by
    intro ω
    have hsub : cspBCh C₁ r_star ω ⊆ (BallPairs.filter (fun xw =>
        (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
        cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter
          (fun y => y ∈ cspPRaw ω)).card)).image Prod.fst := by
      intro x hx
      simp only [cspBCh, Finset.mem_filter] at hx
      rcases hx with ⟨hxP, w₀, hwP, hne, hd, hcard⟩
      rw [Finset.mem_image]
      refine ⟨(x, w₀), ?_, rfl⟩
      simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hne, hd⟩, ⟨hxP, hwP⟩, hcard⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBCh C₁ r_star ω).card : ℝ) ≤
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((BallPairs.filter (fun xw =>
          (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
          cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter
            (fun y => y ∈ cspPRaw ω)).card)).card : ℝ) := by
    refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
    exact_mod_cast (hpt ω)
  rw [weightedFilteredCardinality_sum] at hstep1
  let α_ch : ℝ := (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
  have h_pair_ch : ∀ xw ∈ BallPairs,
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
            cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter (fun y => y ∈ cspPRaw ω)).card
         then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
      ((cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries xw.1 ∪ homQueries xw.2).card) *
        α_ch ^ cspKCh C₁ := by
    rintro ⟨x, w₀⟩ hxw
    simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxw
    let S₀ : Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)) :=
      ({x, w₀} : Finset _).image Sum.inr ∪ (homQueries x ∪ homQueries w₀).image Sum.inl
    let Q_ch : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) → Unit →
        Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)) :=
      fun m y_prev y _ =>
        (({y} : Finset _).image Sum.inr ∪ (homQueries y).image Sum.inl) \
          cspUCh x w₀ m y_prev
    have hS₀_prod : ∏ i ∈ S₀, cspPIota C₁ r_star i =
        (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries x ∪ homQueries w₀).card := by
      change ∏ i ∈ ({x, w₀} : Finset _).image Sum.inr ∪
          (homQueries x ∪ homQueries w₀).image Sum.inl, cspPIota C₁ r_star i = _
      rw [h_prod_iota, Finset.card_pair hxw.1]
    rw [← hS₀_prod]
    apply h_seq (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) Unit
      (cspPoolCh C₁ r_star x w₀) (cspKCh C₁) α_ch (by positivity)
      (fun ω => x ∈ cspPRaw ω ∧ w₀ ∈ cspPRaw ω)
      (fun ω => (cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω))
      (fun _ => Finset.filter_subset _ _)
      S₀ (cspUCh x w₀) (fun _ _ _ => {()}) Q_ch
    · intro z₀ i hi
      simp only [S₀, cspUCh, Finset.mem_union, Finset.mem_image] at hi ⊢
      rcases hi with h | ⟨t, ht, rfl⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨t, Or.inl ht, rfl⟩
    · intro m _ y_prev b i hi
      simp only [cspUCh, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_biUnion] at hi ⊢
      rcases hi with (h | ⟨t, rfl⟩) | ⟨q_e, hq, rfl⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨t.castSucc, by simp [Fin.snoc_castSucc]⟩)
      · right
        refine ⟨q_e, ?_, rfl⟩
        rcases hq with hq1 | ⟨t, hqt⟩
        · exact Or.inl hq1
        · exact Or.inr ⟨t.castSucc, by simpa [Fin.snoc_castSucc] using hqt⟩
    · intro m _ y_prev _ _ y _ _ _ i hi
      simp only [Q_ch, Finset.mem_sdiff] at hi
      rw [Finset.mem_sdiff]
      refine ⟨?_, hi.2⟩
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
      simp only [cspUCh, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_biUnion]
      rcases hi.1 with ⟨_, rfl, rfl⟩ | ⟨t, ht, rfl⟩
      · exact Or.inl (Or.inr ⟨Fin.last m, by simp [Fin.snoc_last]⟩)
      · exact Or.inr ⟨t, Or.inr ⟨Fin.last m, by simpa [Fin.snoc_last] using ht⟩, rfl⟩
    · intro ω hBase
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hBase
        simp only [S₀, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at hi
        rcases hi with ⟨z, rfl | rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
        · exact hBase.1.1
        · exact hBase.2.1
        · exact hBase.1.2 t ht
        · exact hBase.2.2 t ht
      · intro z _ hz m
        refine ⟨(), Finset.mem_singleton_self (), ?_⟩
        intro i hi
        have hzm := hz m
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hzm
        simp only [Q_ch, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
          Finset.mem_singleton] at hi
        rcases hi.1 with ⟨_, rfl, rfl⟩ | ⟨t, ht, rfl⟩
        · exact hzm.2.1
        · exact hzm.2.2 t ht
    · intro m hm y_prev _ hpool
      simp only [Finset.sum_singleton, Q_ch]
      exact h_s5_ch x w₀ hxw.2 m hm y_prev hpool
  have hstep2 : ∑ xw ∈ BallPairs, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (if (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
          cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter (fun y => y ∈ cspPRaw ω)).card
       then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
    cspN0 C₁ r_star * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
      α_ch ^ cspKCh C₁ := by
    calc
      ∑ xw ∈ BallPairs, _
        ≤ ∑ xw ∈ BallPairs,
            ((cspPKeep C₁ r_star) ^ 2 *
              (cspPEdge C₁ r_star) ^ (homQueries xw.1 ∪ homQueries xw.2).card) *
              α_ch ^ cspKCh C₁ := Finset.sum_le_sum h_pair_ch
      _ = (∑ xw ∈ BallPairs, (cspPKeep C₁ r_star) ^ 2 *
            (cspPEdge C₁ r_star) ^ (homQueries xw.1 ∪ homQueries xw.2).card) *
            α_ch ^ cspKCh C₁ := (Finset.sum_mul _ _ _).symm
      _ ≤ cspN0 C₁ r_star *
            (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            α_ch ^ cspKCh C₁ :=
            mul_le_mul_of_nonneg_right h_ball_sum (by positivity)
  have hstep3 : cspN0 C₁ r_star *
      (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
      α_ch ^ cspKCh C₁ ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    simpa only [α_ch, cspDeltaBad, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      exponentialMomentEstimate ((C₁ ^ 2 : ℕ) : ℝ)
        ((cspLam0 C₁ : ℝ) * (r_star : ℝ)) (cspN0 C₁ r_star) (cspKCh C₁)
        hC₁_sq_real (by nlinarith only [hlam0_real, hr_ge3001_real])
        (by simp [cspKCh]) (le_of_lt hn0_pos)
  linarith only [hstep1, hstep2, hstep3]

open Classical in
private lemma existence_hBcand_exp :
    ∀ (C₁ : ℕ),
    (3 : ℕ) ≤ C₁ →
    ∀ (r_star : ℕ),
    (1000 : ℕ) * C₁ < r_star →
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (9 : ℝ) ≤ (↑(C₁ ^ (2 : ℕ)) : ℝ) →
    (1000 : ℝ) ≤ (↑(cspLam0 C₁) : ℝ) →
    (0 : ℝ) < cspSigmaEdge C₁ r_star →
    (∀ (s : ℕ),
    (↑((2 ^ cspL C₁ * r_star).choose s) : ℝ) * (↑(cspQ C₁ - (1 : ℕ)) : ℝ) ^ s *
    cspPEdge C₁ r_star ^ (s * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ))) ≤
    (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ))) →
    (0 : ℝ) < cspPKeep C₁ r_star →
    cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑r_star : ℝ)) →
    ∑ ab :
    (Assignment C₁ r_star) ×
    (Assignment C₁ r_star) with
    ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star,
    cspPKeep C₁ r_star ^ (2 : ℕ) *
    cspPEdge C₁ r_star ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
    cspN0 C₁ r_star *
    (2 : ℝ) ^ ((7 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑r_star : ℝ)) →
    cspSigmaEdge C₁ r_star * (↑r_star : ℝ) / (2 : ℝ) ≤
    (10001 / 10000 : ℝ) * (↑(cspBeta0 C₁) : ℝ) →
    (0 : ℝ) < cspN0 C₁ r_star →
    (∀ (ω : Outcome C₁ r_star),
    (0 : ℝ) ≤ bernWeight (cspPIota C₁ r_star) ω) →
    (∀ i : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁),
    0 ≤ cspPIota C₁ r_star i ∧ cspPIota C₁ r_star i ≤ 1) →
    (∀ (V_keep : Finset (Assignment C₁ r_star))
    (Q_edges :
    Finset
    (Fin (2 ^ cspL C₁ * r_star) ×
    Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁) × Fin (cspQ C₁))),
    ∏ i ∈ Finset.image Sum.inr V_keep ∪ Finset.image Sum.inl Q_edges,
    cspPIota C₁ r_star i =
    cspPKeep C₁ r_star ^ V_keep.card * cspPEdge C₁ r_star ^ Q_edges.card) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBCand C₁ r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  classical
  intro C₁ hC₁ r_star hr hr_ge3001_real hC₁_sq_real hlam0_real hσ_pos h_binom_edge
      hp_keep_pos hp_keep_up h_ball_sum hσ_up hn0_pos hW_nn hp_iota h_prod_iota
  have h_seq :=
    (finite_bernoulli_cylinder_and_sequential_moment (cspPIota C₁ r_star) hp_iota).2.2.2
  let BallPairs := Finset.univ.filter
    (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
              (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
      ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star)
  have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (cspBCand C₁ r_star ω).card ≤ (BallPairs.filter (fun ab =>
        (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
        cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star
          ab.1 ab.2)).card)).card := by
    intro ω
    have hsub : cspBCand C₁ r_star ω ⊆ (BallPairs.filter (fun ab =>
        (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
        cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star
          ab.1 ab.2)).card)).image
          Prod.fst := by
      intro a ha
      simp only [cspBCand, Finset.mem_filter] at ha
      rcases ha with ⟨haP, b, hbP, hne, hd, hcard⟩
      rw [Finset.mem_image]
      refine ⟨(a, b), ?_, rfl⟩
      simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hne, hd⟩, ⟨haP, hbP⟩, hcard⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBCand C₁ r_star ω).card : ℝ) ≤
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((BallPairs.filter (fun ab =>
          (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
          cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁
            r_star ab.1 ab.2)).card)).card : ℝ) := by
    refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
    exact_mod_cast (hpt ω)
  rw [weightedFilteredCardinality_sum] at hstep1
  let α_cand : ℝ := (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
  have h_pair_cand : ∀ ab ∈ BallPairs,
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
            cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁
              r_star ab.1 ab.2)).card
         then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
      ((cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card) *
        α_cand ^ cspKMom C₁ := by
    rintro ⟨a, b⟩ hab_mem
    simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hab_mem
    obtain ⟨M_wit, Q_cand, hQ_fresh, hQ_wit, hQ_step⟩ :=
      witness_list_step_query_sum_bound C₁ hC₁ r_star hr hσ_pos hσ_up
        h_binom_edge hp_keep_pos hp_keep_up a b hab_mem.2
    let S₀ : Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)) :=
      ({a, b} : Finset _).image Sum.inr ∪ (homQueries a ∪ homQueries b).image Sum.inl
    have hS₀_prod : ∏ i ∈ S₀, cspPIota C₁ r_star i =
        (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries a ∪ homQueries b).card := by
      change ∏ i ∈ ({a, b} : Finset _).image Sum.inr ∪
          (homQueries a ∪ homQueries b).image Sum.inl, cspPIota C₁ r_star i = _
      rw [h_prod_iota, Finset.card_pair hab_mem.1]
    rw [← hS₀_prod]
    apply h_seq (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))
      (candWitType (2 ^ cspL C₁ * r_star) C₁)
      (cspPoolCand C₁ r_star a b) (cspKMom C₁) α_cand (by positivity)
      (fun ω => a ∈ cspPRaw ω ∧ b ∈ cspPRaw ω)
      (fun ω => (cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b))
      (fun _ x hx => by
        simp only [bicliqueWitnessList, Finset.mem_filter] at hx
        rcases hx.2 with ⟨_, hnea, hneb, hda, hdb, _⟩
        simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hnea, hneb, hda, hdb⟩)
      S₀ (cspUCand a b) M_wit Q_cand
    · intro z₀ i hi
      simp only [S₀, cspUCand, cspRvc, homQueries, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rcases hi with h | ⟨t, (⟨⟨u, v⟩, huv, rfl⟩ | ⟨⟨u, v⟩, huv, rfl⟩), rfl⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨(u, v, a u, a v),
          ⟨huv, Or.inl (Or.inl ⟨u, rfl⟩), Or.inl (Or.inl ⟨v, rfl⟩)⟩, rfl⟩
      · exact Or.inr ⟨(u, v, b u, b v),
          ⟨huv, Or.inl (Or.inr ⟨u, rfl⟩), Or.inl (Or.inr ⟨v, rfl⟩)⟩, rfl⟩
    · intro m _ z_prev x_new
      have hrvc_sub : cspRvc a b m z_prev ⊆ cspRvc a b (m + 1) (Fin.snoc z_prev x_new) := by
        intro vc hvc
        simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion] at hvc ⊢
        rcases hvc with (h | h) | ⟨t, v, rfl⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨t.castSucc, v, by simp [Fin.snoc_castSucc]⟩
      intro i hi
      simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and] at hi ⊢
      rcases hi with (h | ⟨t, rfl⟩) | ⟨t, ⟨huv, h1, h2⟩, rfl⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨t.castSucc, by simp [Fin.snoc_castSucc]⟩)
      · exact Or.inr ⟨t, ⟨huv, hrvc_sub h1, hrvc_sub h2⟩, rfl⟩
    · intro m hm z_prev _ hpool
      exact hQ_fresh m hm z_prev hpool
    · intro ω hBase
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hBase
        simp only [S₀, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at hi
        rcases hi with ⟨z, rfl | rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
        · exact hBase.1.1
        · exact hBase.2.1
        · exact hBase.1.2 t ht
        · exact hBase.2.2 t ht
      · intro z hinj hz m
        let z_prev : Fin m.1 → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) :=
          fun t => z (t.castLE (Nat.le_of_lt m.isLt))
        have hpool_prev : ∀ t : Fin m.1, z_prev t ∈ cspPoolCand C₁ r_star a b := by
          intro t
          have hzt := hz (t.castLE (Nat.le_of_lt m.isLt))
          simp only [bicliqueWitnessList, Finset.mem_filter] at hzt
          rcases hzt.2 with ⟨_, hnea, hneb, hda, hdb, _⟩
          simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hnea, hneb, hda, hdb⟩
        have hzm := hz m
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hzm
        have hx_mem : z m ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev := by
          rw [Finset.mem_sdiff]
          refine ⟨?_, ?_⟩
          · have hbw := hzm.2
            simp only [bicliqueWitnessList, Finset.mem_filter] at hbw
            rcases hbw with ⟨_, hnea, hneb, hda, hdb, _⟩
            simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hnea, hneb, hda, hdb⟩
          · intro himg
            rcases Finset.mem_image.mp himg with ⟨t, _, heq⟩
            have ht_eq := congr_arg Fin.val (hinj heq)
            exact absurd ht_eq (Nat.ne_of_lt t.isLt)
        exact hQ_wit ω m.1 m.isLt z_prev hpool_prev (z m) hx_mem hzm.1.1 hzm.2
    · intro m hm z_prev _ hpool
      exact hQ_step m hm z_prev hpool
  have hstep2 : ∑ ab ∈ BallPairs, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (if (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
          cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁
            r_star ab.1 ab.2)).card
       then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
    cspN0 C₁ r_star * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
      α_cand ^ cspKMom C₁ := by
    calc
      ∑ ab ∈ BallPairs, _
        ≤ ∑ ab ∈ BallPairs,
            ((cspPKeep C₁ r_star) ^ 2 *
              (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card) *
              α_cand ^ cspKMom C₁ := Finset.sum_le_sum h_pair_cand
      _ = (∑ ab ∈ BallPairs, (cspPKeep C₁ r_star) ^ 2 *
            (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card) *
            α_cand ^ cspKMom C₁ := (Finset.sum_mul _ _ _).symm
      _ ≤ cspN0 C₁ r_star *
            (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            α_cand ^ cspKMom C₁ :=
            mul_le_mul_of_nonneg_right h_ball_sum (by positivity)
  have hstep3 : cspN0 C₁ r_star *
      (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
      α_cand ^ cspKMom C₁ ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    simpa only [α_cand, cspDeltaBad, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      exponentialMomentEstimate ((C₁ ^ 2 : ℕ) : ℝ)
        ((cspLam0 C₁ : ℝ) * (r_star : ℝ)) (cspN0 C₁ r_star) (cspKMom C₁)
        hC₁_sq_real (by nlinarith only [hlam0_real, hr_ge3001_real])
        (by simp [cspKMom]) (le_of_lt hn0_pos)
  linarith only [hstep1, hstep2, hstep3]

open Classical in
private lemma existence_hBDist_exp :
    ∀ (C₁ : ℕ),
    (3 : ℕ) ≤ C₁ →
    ∀ (r_star : ℕ),
    (1000 : ℕ) * C₁ < r_star →
    (0 : ℝ) < cspSigmaEdge C₁ r_star →
    (0 : ℝ) < cspPEdge C₁ r_star →
    (∀ s ≤ (2 : ℕ) ^ cspL C₁ * r_star,
    cspDOmega C₁ r_star s ≤
    (2 : ℝ) ^
    ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ) +
    cspSigmaEdge C₁ r_star * (↑(s.choose (2 : ℕ)) : ℝ))) →
    (0 : ℝ) < cspPKeep C₁ r_star →
    cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑r_star : ℝ)) →
    (∀ (x y : Assignment C₁ r_star),
    (homQueries x ∪ homQueries y).card =
    (2 ^ cspL C₁ * r_star).choose (2 : ℕ) +
    dHam x y * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) -
    (dHam x y).choose (2 : ℕ)) →
    cspSigmaEdge C₁ r_star * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) * (↑(cspBeta0 C₁) :
      ℝ) →
    (0 : ℝ) < cspN0 C₁ r_star →
    (∀ (ω : Outcome C₁ r_star),
    (0 : ℝ) ≤ bernWeight (cspPIota C₁ r_star) ω) →
    (∀ {x y : Assignment C₁ r_star},
    x ≠ y →
    (∑ ω : Outcome C₁ r_star,
    if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω then bernWeight (cspPIota C₁ r_star) ω
    else (0 : ℝ)) =
    cspPKeep C₁ r_star ^ (2 : ℕ) *
    cspPEdge C₁ r_star ^ (homQueries x ∪ homQueries y).card) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBDist r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  classical
  intro C₁ hC₁ r_star hr hσ_pos hp_edge_pos hDOm_s hp_keep_pos hp_keep_up h_union_card
      hσ_up hn0_pos hW_nn h_pair_exp
  let ClosePairs := Finset.univ.filter
    (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
              (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
      ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star)
  have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (cspBDist r_star ω).card ≤ (ClosePairs.filter (fun ab =>
        ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω)).card := by
    intro ω
    have hsub : cspBDist r_star ω ⊆ (ClosePairs.filter (fun ab =>
        ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω)).image Prod.fst := by
      intro x hx
      simp only [cspBDist, Finset.mem_filter] at hx
      rcases hx with ⟨hxP, y, hyP, hne, hlt⟩
      rw [Finset.mem_image]
      refine ⟨(x, y), ?_, rfl⟩
      simp only [ClosePairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hne, hlt⟩, hxP, hyP⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBDist r_star ω).card : ℝ) ≤
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((ClosePairs.filter (fun ab =>
          ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω)).card : ℝ) := by
    refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
    exact_mod_cast (hpt ω)
  rw [weightedFilteredCardinality_sum] at hstep1
  have hcongr : ∑ ab ∈ ClosePairs, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      (if ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω
       then bernWeight (cspPIota C₁ r_star) ω else 0) =
    ∑ ab ∈ ClosePairs,
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card := by
    refine Finset.sum_congr rfl (fun ab hab => ?_)
    simp only [ClosePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hab
    exact h_pair_exp hab.1
  rw [hcongr] at hstep1
  exact le_trans hstep1
    (close_pair_query_sum_bound C₁ hC₁ r_star hr hσ_pos hp_edge_pos hσ_up hDOm_s
      hp_keep_pos hp_keep_up hn0_pos h_union_card)

open Classical in
private lemma existence_hBad :
    ∀ (C₁ r_star : ℕ),
    (∀ (ω : Outcome C₁ r_star), (0 : ℝ) ≤ bernWeight
    (cspPIota C₁ r_star) ω) →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBD3 C₁ r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBCh C₁ r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBCand C₁ r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBDist r_star ω).card : ℝ) ≤
    (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star →
    ∑ ω : Outcome C₁ r_star,
    bernWeight (cspPIota C₁ r_star) ω * (↑(cspBBad C₁ r_star ω).card : ℝ) ≤
    cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  classical
  intro C₁ r_star hW_nn hBD3_exp hBch_exp hBcand_exp hBDist_exp
  have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBBad C₁ r_star ω).card : ℝ) ≤
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBD3 C₁ r_star ω).card : ℝ)) +
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBCh C₁ r_star ω).card : ℝ)) +
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBCand C₁ r_star ω).card : ℝ)) +
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBDist r_star ω).card : ℝ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ω _ => ?_)
    have h0 := Finset.card_union_le
      (cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω ∪ cspBCand C₁ r_star ω)
      (cspBDist r_star ω)
    have h1 := Finset.card_union_le (cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω) (cspBCand C₁ r_star ω)
    have h2 := Finset.card_union_le (cspBD3 C₁ r_star ω) (cspBCh C₁ r_star ω)
    have hnat : (cspBBad C₁ r_star ω).card ≤
        (cspBD3 C₁ r_star ω).card + (cspBCh C₁ r_star ω).card +
        (cspBCand C₁ r_star ω).card + (cspBDist r_star ω).card := by
      unfold cspBBad
      omega
    have hreal : ((cspBBad C₁ r_star ω).card : ℝ) ≤
        ((cspBD3 C₁ r_star ω).card : ℝ) + ((cspBCh C₁ r_star ω).card : ℝ) +
        ((cspBCand C₁ r_star ω).card : ℝ) + ((cspBDist r_star ω).card : ℝ) := by
      exact_mod_cast hnat
    have hm := mul_le_mul_of_nonneg_left hreal (hW_nn ω)
    linarith [hm]
  linarith only [hstep1, hBD3_exp, hBch_exp, hBcand_exp, hBDist_exp]

open Classical in
private lemma existence_h_margin :
    ∀ (C₁ r_star : ℕ),
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (1000 : ℝ) ≤ (↑(cspLam0 C₁) : ℝ) →
    (∀ c ≤ (4 : ℝ), c * (↑r_star : ℝ) / (2 : ℝ) ^ (998 : ℕ) ≤ (↑r_star : ℝ)) →
    (1 : ℝ) ≤ cspGamma r_star →
    (0 : ℝ) < cspDeltaBad C₁ r_star →
    (72 : ℝ) * (144 : ℝ) * cspGamma r_star ^ (3 : ℕ) * cspDeltaBad C₁ r_star ≤ (1 / 256 : ℝ) :=
      by
  classical
  intro C₁ r_star hr_ge3001_real hlam0_real hdiv998 hγ_ge1 hδ_pos
  have hconst : (72 * 144 : ℝ) ≤ (2 : ℝ) ^ (14 : ℝ) := by norm_num
  have hγ3 : (cspGamma r_star) ^ 3 = (2 : ℝ) ^ (3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) := by
    unfold cspGamma
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    rw [div_mul_eq_mul_div, mul_comm]
  have h1 : 72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star ≤
      (2 : ℝ) ^ ((14 : ℝ) + 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
        (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
    have hm : 72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star ≤
        (2 : ℝ) ^ (14 : ℝ) * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star := by
      have : 0 ≤ (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star := by positivity
      nlinarith only [hconst, this]
    calc
      72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star
        ≤ (2 : ℝ) ^ (14 : ℝ) * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star := hm
      _ = (2 : ℝ) ^ ((14 : ℝ) + 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
            (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
          rw [hγ3]
          unfold cspDeltaBad
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have h2 : (2 : ℝ) ^ ((14 : ℝ) + 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
        (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ≤ (1 / 256 : ℝ) := by
    have h256 : (1 / 256 : ℝ) = (2 : ℝ) ^ (- (8 : ℝ)) := by norm_num
    rw [h256]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    set d998 : ℝ := 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
    have hdiv_le : d998 ≤ (r_star : ℝ) := hdiv998 3 (by norm_num)
    clear_value d998
    have hlam_r : 600 * (r_star : ℝ) ≤ (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_right hlam0_real (Nat.cast_nonneg r_star)
      nlinarith only [hscaled]
    linarith only [hdiv_le, hlam_r, hr_ge3001_real]
  exact le_trans h1 h2

open Classical in
private lemma existence_h_final :
    ∀ (C₁ : ℕ),
    (3 : ℕ) ≤ C₁ →
    ∀ (r_star : ℕ),
    (0 : ℝ) < (↑r_star : ℝ) →
    (3001 : ℝ) ≤ (↑r_star : ℝ) →
    (1000 : ℝ) ≤ (↑(cspLam0 C₁) : ℝ) →
    (6000 : ℝ) ≤ (↑(cspBeta0 C₁) : ℝ) →
    (1 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) →
    (∀ c ≤ (4 : ℝ), c * (↑r_star : ℝ) / (2 : ℝ) ^ (998 : ℕ) ≤ (↑r_star : ℝ)) →
    (2 : ℝ) ^ ((99 / 100 : ℝ) * (↑(cspBeta0 C₁) : ℝ) * (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) * (↑r_star
    : ℝ)) ≤
    cspN0 C₁ r_star →
    cspN0 C₁ r_star ≤ (2 : ℝ) ^ ((↑(cspBeta0 C₁) : ℝ) * (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) * (↑r_star
    : ℝ)) →
    (0 : ℝ) < cspN0 C₁ r_star →
    (1 : ℝ) ≤ cspGamma r_star →
    ∀ (ω₀ : Outcome C₁ r_star),
    (1 / 1024 : ℝ) * (cspGamma r_star)⁻¹ ^ (2 : ℕ) * cspN0 C₁ r_star ≤
    (↑(cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).card : ℝ) →
    (↑(cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).card : ℝ) ≤
    (72 : ℝ) * cspGamma r_star * cspN0 C₁ r_star →
    cspDStar C₁ r_star / cspGamma r_star * (↑(cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).card : ℝ) ≤
    (192 : ℝ) *
    (↑{xy ∈
    (cspPRaw ω₀ \ cspBBad C₁ r_star ω₀) ×ˢ
    (cspPRaw ω₀ \ cspBBad C₁ r_star ω₀) |
    dHam xy.1 xy.2 = r_star}.card :
    ℝ) →
    ∃ (R :
    Fin (2 ^ cspL C₁ * r_star) → Fin (2 ^ cspL C₁ * r_star) →
    Fin (cspQ C₁) → Fin (cspQ C₁) → Prop)
    (X_set : Finset (Assignment C₁ r_star)),
    Symmetric2CSP R ∧
    X_set ⊆ satisfyingSet R ∧
    ((2 : ℝ) ^
    ((98 / 100 : ℝ) * (↑(cspBeta0 C₁) : ℝ) * (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) *
    (↑r_star : ℝ)) ≤
    (↑X_set.card : ℝ) ∧
    (↑X_set.card : ℝ) ≤
    (2 : ℝ) ^
    ((102 / 100 : ℝ) * (↑(cspBeta0 C₁) : ℝ) *
    (2 : ℝ) ^ ((2 : ℕ) * cspL C₁) *
    (↑r_star : ℝ))) ∧
    (2 : ℝ) ^ ((1 / 5 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑r_star : ℝ)) *
    (↑X_set.card : ℝ) ≤
    (192 : ℝ) * (↑{xy ∈ X_set ×ˢ X_set | dHam xy.1 xy.2 = r_star}.card : ℝ) ∧
    (∀ x ∈ X_set,
    ∀ u ∈ X_set,
    ∀ z ∈ satisfyingSet R,
    dHam x u ≤ C₁ * r_star →
    dHam x z ≤ C₁ * r_star →
    cspInvEta0 C₁ * (threeWayDisagree x u z).card ≤ r_star) ∧
    (∀ x ∈ X_set,
    ∀ w₀ ∈ X_set,
    x ≠ w₀ →
    dHam x w₀ ≤ C₁ * r_star →
    {y ∈ X_set |
    y ≠ x ∧
    y ≠ w₀ ∧
    dHam x y = r_star ∧
    r_star <
    (4 : ℕ) *
    (disagreeSet x w₀ ∩ disagreeSet x y).card}.card <
    cspKCh C₁) ∧
    (∀ a ∈ X_set,
    ∀ b ∈ X_set,
    a ≠ b →
    dHam a b ≤ C₁ * r_star →
    {x ∈ X_set | x ∈ bicliqueWitnessList R C₁ r_star a b}.card <
    cspKMom C₁) ∧
    ∀ x ∈ X_set, ∀ y ∈ X_set, x ≠ y → r_star ≤ (2 : ℕ) * dHam x y := by
  classical
  intro C₁ hC₁ r_star hr_pos_real hr_ge3001_real hlam0_real hbeta0_real h22L_real hdiv998
      hn0_low hn0_up hn0_pos hγ_ge1 ω₀ hX_low_raw hX_up_raw hE_dense_raw
  refine ⟨symROf ω₀, cspPRaw ω₀ \ cspBBad C₁ r_star ω₀, symmetricRandomRelation ω₀, ?_, ⟨?_,
    ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ cspPRaw ω₀ := (Finset.mem_sdiff.mp hx).1
    simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hxP
    exact (homQueries_satisfyingSet_iff ω₀ x).mp hxP.2
  · have h1024 : (1 / 1024 : ℝ) = (2 : ℝ) ^ (- (10 : ℝ)) := by norm_num
    have hγ_inv2 : (cspGamma r_star)⁻¹ ^ 2 =
        (2 : ℝ) ^ (- (2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))) := by
      unfold cspGamma
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      rw [neg_mul, div_mul_eq_mul_div, mul_comm (r_star : ℝ) 2]
    have hlow1 : (2 : ℝ) ^ (- (10 : ℝ) + (- (2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))) +
        (99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (1 / 1024 : ℝ) * (cspGamma r_star)⁻¹ ^ 2 * cspN0 C₁ r_star := by
      rw [h1024, hγ_inv2, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hn0_low (by positivity)
    have hlow2 : (2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) *
      (r_star : ℝ)) ≤
        (2 : ℝ) ^ (- (10 : ℝ) + (- (2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))) +
          (99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := 2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := hdiv998 2 (by norm_num)
      clear_value d998
      have hprod : 10 * (r_star : ℝ) ≤
          (1 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ) := by
        have hm : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
          nlinarith only [hbeta0_real, h22L_real]
        nlinarith only [hm, hr_pos_real]
      linarith only [hdiv_le, hprod, hr_ge3001_real]
    convert! le_trans hlow2 (le_trans hlow1 hX_low_raw) using 1
  · have h72 : (72 : ℝ) ≤ (2 : ℝ) ^ (7 : ℝ) := by norm_num
    have hup1 : 72 * cspGamma r_star * cspN0 C₁ r_star ≤
        (2 : ℝ) ^ ((7 : ℝ) + (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
          (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
      have hm1 : 72 * cspGamma r_star * cspN0 C₁ r_star ≤
          (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star * cspN0 C₁ r_star := by
        have : 0 ≤ cspGamma r_star * cspN0 C₁ r_star := by positivity
        nlinarith only [h72, this]
      have hm2 : (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star * cspN0 C₁ r_star ≤
          (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star *
            (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) :=
        mul_le_mul_of_nonneg_left hn0_up (by positivity)
      calc
        72 * cspGamma r_star * cspN0 C₁ r_star
          ≤ (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star *
              (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) :=
            le_trans hm1 hm2
        _ = (2 : ℝ) ^ ((7 : ℝ) + (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
              (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
            unfold cspGamma
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hup2 : (2 : ℝ) ^ ((7 : ℝ) + (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
          (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ))
          := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := by
        have h1 := hdiv998 1 (by norm_num); rwa [one_mul] at h1
      clear_value d998
      have hprod : 20 * (r_star : ℝ) ≤
          (2 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ) := by
        have hm : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
          nlinarith only [hbeta0_real, h22L_real]
        nlinarith only [hm, hr_pos_real]
      linarith only [hdiv_le, hprod, hr_ge3001_real]
    convert! le_trans hX_up_raw (le_trans hup1 hup2) using 1
  · have hD_div : (2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
        cspDStar C₁ r_star / cspGamma r_star := by
      unfold cspDStar cspGamma
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := by
        have h1 := hdiv998 1 (by norm_num); rwa [one_mul] at h1
      clear_value d998
      have hlam_r : (r_star : ℝ) ≤ (1 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_pos_real]
      linarith only [hdiv_le, hlam_r, hr_pos_real]
    convert! le_trans (mul_le_mul_of_nonneg_right hD_div (Nat.cast_nonneg _))
      hE_dense_raw using 1
  · intro x hx u hu z hz hdu hdz
    by_contra hgt
    push Not at hgt
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have huP := (Finset.mem_sdiff.mp hu).1
    have hzHom : ∀ t ∈ homQueries z, ω₀ (Sum.inl t) = true := (homQueries_satisfyingSet_iff ω₀
      z).mpr hz
    apply hx_sdiff.2
    simp only [cspBBad, cspBD3, Finset.mem_union, Finset.mem_filter]
    exact Or.inl (Or.inl (Or.inl ⟨hx_sdiff.1, u, huP, z, hzHom, hdu, hdz, hgt⟩))
  · intro x hx w₀ hw₀ hne hd_xw₀
    by_contra hge
    push Not at hge
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have hw₀P := (Finset.mem_sdiff.mp hw₀).1
    have hsub : (cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).filter (fun y =>
        y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
        r_star < 4 * (disagreeSet x w₀ ∩ disagreeSet x y).card) ⊆
      (cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω₀) := by
      intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      rcases hy with ⟨hyX, hneyx, hneyw, hdy, hov⟩
      have hy_sdiff := Finset.mem_sdiff.mp hyX
      refine ⟨?_, hy_sdiff.1⟩
      simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hneyx, hneyw, hdy, hov, ?_⟩
      have hd_xy_le : dHam x y ≤ C₁ * r_star := by
        rw [hdy]
        exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
      have hyHom : ∀ t ∈ homQueries y, ω₀ (Sum.inl t) = true := by
        have hyP := hy_sdiff.1
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hyP
        exact hyP.2
      by_contra hd3_gt
      push Not at hd3_gt
      apply hx_sdiff.2
      simp only [cspBBad, cspBD3, Finset.mem_union, Finset.mem_filter]
      exact Or.inl (Or.inl (Or.inl ⟨hx_sdiff.1, w₀, hw₀P, y, hyHom, hd_xw₀, hd_xy_le, hd3_gt⟩))
    have hcard_ge := le_trans hge (Finset.card_le_card hsub)
    apply hx_sdiff.2
    simp only [cspBBad, cspBCh, Finset.mem_union, Finset.mem_filter]
    exact Or.inl (Or.inl (Or.inr ⟨hx_sdiff.1, w₀, hw₀P, hne, hd_xw₀, hcard_ge⟩))
  · intro a ha b hb hne hd_ab
    by_contra hge
    push Not at hge
    have ha_sdiff := Finset.mem_sdiff.mp ha
    have hbP := (Finset.mem_sdiff.mp hb).1
    have hsub : (cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).filter
        (fun x => x ∈ bicliqueWitnessList (symROf ω₀) C₁ r_star a b) ⊆
      (cspPRaw ω₀).filter (fun x => x ∈ bicliqueWitnessList (symROf ω₀) C₁ r_star a b) :=
      Finset.filter_subset_filter _ Finset.sdiff_subset
    have hcard_ge := le_trans hge (Finset.card_le_card hsub)
    apply ha_sdiff.2
    simp only [cspBBad, cspBCand, Finset.mem_union, Finset.mem_filter]
    exact Or.inl (Or.inr ⟨ha_sdiff.1, b, hbP, hne, hd_ab, hcard_ge⟩)
  · intro x hx y hy hne
    by_contra hlt
    push Not at hlt
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have hyP := (Finset.mem_sdiff.mp hy).1
    apply hx_sdiff.2
    simp only [cspBBad, cspBDist, Finset.mem_union, Finset.mem_filter]
    exact Or.inr ⟨hx_sdiff.1, y, hyP, hne, hlt⟩

theorem complete_graph_2csp_expurgated_existence (C₁ : ℕ) (hC₁ : 3 ≤ C₁)
    (r_star : ℕ) (hr : 1000 * C₁ < r_star) :
    ∃ (R : Fin (2 ^ cspL C₁ * r_star) → Fin (2 ^ cspL C₁ * r_star) →
          Fin (cspQ C₁) → Fin (cspQ C₁) → Prop)
      (X_set : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))),
      Symmetric2CSP R ∧
      X_set ⊆ satisfyingSet R ∧
      ((2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (X_set.card : ℝ) ∧
       (X_set.card : ℝ) ≤
        (2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ))) ∧
      ((2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) * (X_set.card : ℝ) ≤
        192 * (((X_set ×ˢ X_set).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ)) ∧
      (∀ x ∈ X_set, ∀ u ∈ X_set, ∀ z ∈ satisfyingSet R,
        dHam x u ≤ C₁ * r_star → dHam x z ≤ C₁ * r_star →
        cspInvEta0 C₁ * (threeWayDisagree x u z).card ≤ r_star) ∧
      (∀ x ∈ X_set, ∀ w₀ ∈ X_set, x ≠ w₀ → dHam x w₀ ≤ C₁ * r_star →
        (X_set.filter (fun y =>
          y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
          r_star < 4 * (disagreeSet x w₀ ∩ disagreeSet x y).card)).card < cspKCh C₁) ∧
      (∀ a ∈ X_set, ∀ b ∈ X_set, a ≠ b → dHam a b ≤ C₁ * r_star →
        (X_set.filter (fun x => x ∈ bicliqueWitnessList R C₁ r_star a b)).card < cspKMom C₁) ∧
      (∀ x ∈ X_set, ∀ y ∈ X_set, x ≠ y → r_star ≤ 2 * dHam x y) :=
by
  classical
  have hr_ge : 3001 ≤ r_star := by omega
  have hr_pos_real : (0 : ℝ) < (r_star : ℝ) := by exact_mod_cast (show 0 < r_star by omega)
  have hr_ge3001_real : (3001 : ℝ) ≤ (r_star : ℝ) := by exact_mod_cast hr_ge
  have hC₁_sq_ge9 : 9 ≤ C₁ ^ 2 := by nlinarith only [hC₁]
  have hC₁_sq_real : (9 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hC₁_sq_ge9
  have hlam0_1000 := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge : 1000 ≤ cspLam0 C₁ := by omega
  have hlam0_real : (1000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam0_ge
  have hbeta0_ge : 6000 ≤ cspBeta0 C₁ := by unfold cspBeta0; omega
  have hbeta0_real : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) := by exact_mod_cast hbeta0_ge
  have h22L_real : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * cspL C₁) := by
    exact_mod_cast (Nat.one_le_two_pow (n := 2 * cspL C₁))
  have hpow998 : (4 : ℝ) ≤ (2 : ℝ) ^ (998 : ℕ) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (998 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv998 : ∀ c : ℝ, c ≤ 4 →
      c * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) ≤ (r_star : ℝ) := by
    intro c hc
    rw [div_le_iff₀ (by positivity)]
    have hc_le : c ≤ (2 : ℝ) ^ (998 : ℕ) := le_trans hc hpow998
    calc
      c * (r_star : ℝ) = (r_star : ℝ) * c := mul_comm _ _
      _ ≤ (r_star : ℝ) * ((2 : ℝ) ^ (998 : ℕ)) :=
        mul_le_mul_of_nonneg_left hc_le (Nat.cast_nonneg _)
  obtain ⟨hσ_pos, hp_edge_pos, hp_edge_lt1, h_cal, hσ_low_strict, hσ_up_strict,
    h_binom_edge, hDOm_s, _hDOm_low, _hDOm_up,
    hp_keep_pos, hp_keep_lt1, hp_keep_up,
    hn0_low, hn0_up,
    _h_hom_card, h_union_card, _,
    h_M1_eq, h_M0_eq, h_ball_sum⟩ :=
    csp_dyadic_calibration_and_first_moments C₁ hC₁ r_star hr
  have hσ_low : (cspBeta0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 :=
    le_of_lt hσ_low_strict
  have hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) :=
    le_of_lt hσ_up_strict
  have hn0_pos : 0 < cspN0 C₁ r_star := by
    have hpos : (0 : ℝ) <
        (2 : ℝ) ^ ((99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith only [hpos, hn0_low]
  have hD_pos : 0 < cspDStar C₁ r_star := by
    unfold cspDStar
    positivity
  have hγ_ge1 : 1 ≤ cspGamma r_star := by
    unfold cspGamma
    have hexp_nn : (0 : ℝ) ≤ (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) := by positivity
    calc
      (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_nn
  have hδ_pos : 0 < cspDeltaBad C₁ r_star := by
    unfold cspDeltaBad
    positivity
  have hp_iota : ∀ i : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁),
      0 ≤ cspPIota C₁ r_star i ∧ cspPIota C₁ r_star i ≤ 1 := by
    rintro (i | i)
    · exact ⟨le_of_lt hp_edge_pos, le_of_lt hp_edge_lt1⟩
    · exact ⟨le_of_lt hp_keep_pos, le_of_lt hp_keep_lt1⟩
  obtain ⟨hW_nn, hW_sum, h_cyl, _⟩ :=
    finite_bernoulli_cylinder_and_sequential_moment (cspPIota C₁ r_star) hp_iota
  have hRel_symm : Std.Symm
      (fun x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) => dHam x y = r_star) := by
    constructor
    intro x y hxy
    rwa [hammingDistance_symm y x]
  have hdHam_ne_of_r : ∀ {N q : ℕ} {x y : Fin N → Fin q}, dHam x y = r_star → x ≠ y := by
    intro N q x y hd hxy
    subst hxy
    have h0 : dHam x x = 0 := by simp [dHam, disagreeSet]
    omega
  have h_prod_iota :=
    @existence_h_prod_iota C₁ r_star
  have h_exp_ind :=
    @existence_h_exp_ind C₁ r_star h_cyl h_prod_iota
  have hM1 :=
    @existence_hM1 C₁ r_star h_M1_eq h_exp_ind
  have h_pair_exp :=
    @existence_h_pair_exp C₁ r_star h_exp_ind
  have h_triple_exp :=
    @existence_h_triple_exp C₁ r_star h_exp_ind
  have h_quad_exp :=
    @existence_h_quad_exp C₁ r_star h_exp_ind
  have hE1_exact :=
    @existence_hE1_exact C₁ r_star h_M0_eq hdHam_ne_of_r h_pair_exp
  have hE1 : cspN0 C₁ r_star * cspDStar C₁ r_star ≤
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          (((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ) :=
    le_of_eq hE1_exact.symm
  obtain ⟨h_s6_deg, h_s6_edge⟩ :=
    raw_degree_and_edge_second_moment_sums C₁ hC₁ r_star hr hσ_pos hp_edge_pos hp_edge_lt1
      h_cal hσ_low hp_keep_pos h_union_card h_M0_eq
  have hW2 :=
    @existence_hW2 C₁ r_star hr_ge3001_real hlam0_real hn0_pos hD_pos hγ_ge1 hW_nn hdHam_ne_of_r
        h_triple_exp hE1_exact h_s6_deg
  have hE2 :=
    @existence_hE2 C₁ r_star hr_ge3001_real hbeta0_real h22L_real hn0_low hn0_pos hD_pos hγ_ge1
        hW_nn hRel_symm hdHam_ne_of_r h_quad_exp h_s6_edge hW2
  obtain ⟨h_s5_d3, h_s5_ch⟩ :=
    d3_and_cherry_query_sum_bounds C₁ hC₁ r_star hr hσ_pos hp_edge_pos hp_edge_lt1
      h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up
  have hBD3_exp :=
    @existence_hBD3_exp C₁ r_star hr_ge hr_ge3001_real hC₁_sq_real hlam0_real hp_edge_pos
        hp_keep_pos h_ball_sum hn0_pos hW_nn h_exp_ind h_s5_d3
  have hBch_exp :=
    @existence_hBch_exp C₁ r_star hr_ge3001_real hC₁_sq_real hlam0_real h_ball_sum hn0_pos hW_nn
        hp_iota h_prod_iota h_s5_ch
  have hBcand_exp :=
    @existence_hBcand_exp C₁ hC₁ r_star hr hr_ge3001_real hC₁_sq_real hlam0_real hσ_pos
        h_binom_edge hp_keep_pos hp_keep_up h_ball_sum hσ_up hn0_pos hW_nn hp_iota
          h_prod_iota
  have hBDist_exp :=
    @existence_hBDist_exp C₁ hC₁ r_star hr hσ_pos hp_edge_pos hDOm_s hp_keep_pos hp_keep_up
        h_union_card hσ_up hn0_pos hW_nn h_pair_exp
  have hBad :=
    @existence_hBad C₁ r_star hW_nn hBD3_exp hBch_exp hBcand_exp hBDist_exp
  have h_margin :=
    @existence_h_margin C₁ r_star hr_ge3001_real hlam0_real hdiv998 hγ_ge1 hδ_pos
  obtain ⟨ω₀, hX_low_raw, hX_up_raw, hE_dense_raw⟩ :=
    paley_zygmund_markov_expurgation (Ω := cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool) (V
      := Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (bernWeight (cspPIota C₁ r_star)) hW_nn
      hW_sum
      (fun x y => dHam x y = r_star) hRel_symm cspPRaw (cspBBad C₁ r_star)
      (cspN0 C₁ r_star) (cspDStar C₁ r_star) (cspGamma r_star) (cspDeltaBad C₁ r_star)
      hn0_pos hD_pos hγ_ge1 hδ_pos h_margin hM1 hE1 hE2 hW2 hBad
  have h_final :=
    @existence_h_final C₁ hC₁ r_star hr_pos_real hr_ge3001_real hlam0_real hbeta0_real h22L_real
        hdiv998 hn0_low hn0_up hn0_pos hγ_ge1 ω₀ (by convert! hX_low_raw using 1; congr!)
        (by convert! hX_up_raw using 1; congr!) (by convert! hE_dense_raw using 1 <;> congr!)
  exact h_final

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
