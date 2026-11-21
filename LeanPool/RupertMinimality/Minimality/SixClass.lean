/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.SixGale

/-! # Six Class -/

@[expose] public section

namespace RupertMinimality

/-!
# Every polyhedron with at most six vertices is Rupert (L10)

Step 5 of `minimality.md`.  After a 2+4 split (Lemma 10.1) with positive
points `D, E` and the other four `W = {P, Q, R, S}`:
* if `W` is coplanar, the segment `DE` crosses `relint conv W` (Lemma 10.3,
  `isRupert_split_coplanar`);
* otherwise `D, E` have barycentric coordinates `β = l`, `γ = m` on `W`
  (`NF`), every point of `W` falls in one of the classes
  `I = (+,-)`, `I½ = (+,0)`, `II = (+,+)`, `II½ = (0,+)`, `III = (-,+)`, and the
  case table of Theorem 10.4 gives an octahedron, a bicapped tetrahedron, a
  T4, a T5 or a T3, each with its facets read off from Gale signs.

`isRupert_of_card_le_six` assembles L5–L10.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Normal form after a 2+4 split with `W` not coplanar: `l`, `m` are the
barycentric dependencies of `D`, `E` on `W = {P, Q, R, S}`, and the split
gives `(H)`. -/
structure NF (V : Finset ℝ³) (D E P Q R S : ℝ³) (l m : ℝ³ → ℝ) : Prop where
  six : Six V
  eq : V = {D, E, P, Q, R, S}
  nodup : [D, E, P, Q, R, S].Nodup
  hl : IsDepOn V l
  hm : IsDepOn V m
  lD : l D = -1
  mD : m D = 0
  lE : l E = 0
  mE : m E = -1
  H : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 0 < a * l P + b * m P ∧ 0 < a * l Q + b * m Q ∧
    0 < a * l R + b * m R ∧ 0 < a * l S + b * m S

/-! ### Relabelling -/

theorem NF.swapPQ {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V D E Q P R S l m := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, H⟩ := h
  refine ⟨six, ?_, ?_, hl, hm, lD, mD, lE, mE, ?_⟩
  · rw [eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at nodup ⊢
    tauto
  · obtain ⟨a, b, ha, hb, h1, h2, h3, h4⟩ := H
    exact ⟨a, b, ha, hb, h2, h1, h3, h4⟩

theorem NF.swapQR {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V D E P R Q S l m := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, H⟩ := h
  refine ⟨six, ?_, ?_, hl, hm, lD, mD, lE, mE, ?_⟩
  · rw [eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at nodup ⊢
    tauto
  · obtain ⟨a, b, ha, hb, h1, h2, h3, h4⟩ := H
    exact ⟨a, b, ha, hb, h1, h3, h2, h4⟩

theorem NF.swapRS {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V D E P Q S R l m := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, H⟩ := h
  refine ⟨six, ?_, ?_, hl, hm, lD, mD, lE, mE, ?_⟩
  · rw [eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at nodup ⊢
    tauto
  · obtain ⟨a, b, ha, hb, h1, h2, h3, h4⟩ := H
    exact ⟨a, b, ha, hb, h1, h2, h4, h3⟩

/-- The mirror `D ↔ E`, `l ↔ m` (classes `I ↔ III`, `I½ ↔ II½`). -/
theorem NF.mirror {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V E D S R Q P m l := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, H⟩ := h
  refine ⟨six, ?_, ?_, hm, hl, mE, lE, mD, lD, ?_⟩
  · rw [eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at nodup ⊢
    tauto
  · obtain ⟨a, b, ha, hb, h1, h2, h3, h4⟩ := H
    exact ⟨b, a, hb, ha, by linarith, by linarith, by linarith, by linarith⟩

/-! ### The case table (Theorem 10.4) -/

/-- Permutation of a six-element `Finset` literal. -/
macro "perm6" : tactic => `(tactic|
  first
  | with_reducible rfl
  | ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> rcases h with h | h | h | h | h | h <;>
      simp only [h, true_or, or_true])

/-- `Nodup` of a permuted six-element list, from the pairwise distinctness in
context. -/
macro "nodup6" : tactic => `(tactic| (
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  repeat' constructor
  all_goals (intro h; subst h; contradiction)))

/-- The order lemma for classes `I` and `III` (uses `(H)`). -/
theorem g_I_III {l m : ℝ³ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x z : ℝ³}
    (hx : 0 < a * l x + b * m x) (hz : 0 < a * l z + b * m z) (_hxl : 0 < l x) (hxm : m x < 0)
    (hzl : l z < 0) (_hzm : 0 < m z) : galeD l m z x < 0 := by
  have e1 : -(b * m x) < a * l x := by linarith
  have e2 : -(a * l z) < b * m z := by linarith
  have p1 : 0 < -(b * m x) := by nlinarith
  have p2 : 0 < -(a * l z) := by nlinarith
  have h := mul_lt_mul'' e1 e2 p1.le p2.le
  have key : 0 < (a * b) * (l x * m z - m x * l z) := by nlinarith
  have hab : 0 < a * b := mul_pos ha hb
  have : 0 < l x * m z - m x * l z := (pos_iff_pos_of_mul_pos key).mp hab
  simp only [galeD]; linarith

/-- The five classes of a point of `W`. -/
theorem nf_class {l m : ℝ³ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {X : ℝ³}
    (h : 0 < a * l X + b * m X) :
    (0 < l X ∧ m X < 0) ∨ (0 < l X ∧ m X = 0) ∨ (0 < l X ∧ 0 < m X) ∨ (l X = 0 ∧ 0 < m X) ∨
      (l X < 0 ∧ 0 < m X) := by
  rcases lt_trichotomy (l X) 0 with h1 | h1 | h1 <;>
    rcases lt_trichotomy (m X) 0 with h2 | h2 | h2
  · nlinarith [mul_neg_of_pos_of_neg ha h1, mul_neg_of_pos_of_neg hb h2]
  · rw [h2, mul_zero, add_zero] at h; nlinarith [mul_neg_of_pos_of_neg ha h1]
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))
  · rw [h1, mul_zero, zero_add] at h; nlinarith [mul_neg_of_pos_of_neg hb h2]
  · rw [h1, h2] at h; simp at h
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))

/-- `(Q, R) = (I, III)`: an octahedron with opposite pairs `PQ`, `DE`, `RS`. -/
theorem NF.case_oct {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q < 0) (hR : l R < 0 ∧
      0 < m R) (hS : l S < 0 ∧ 0 < m S) :
    IsRupert V := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, a, b, ha, hb, HP, HQ, HR, HS⟩ := h
  obtain ⟨hPl, hPm⟩ := hP
  obtain ⟨hQl, hQm⟩ := hQ
  obtain ⟨hRl, hRm⟩ := hR
  obtain ⟨hSl, hSm⟩ := hS
  have nd := nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    nd
  have gWD : ∀ X, galeD l m X D = m X := fun X => by simp only [galeD, lD, mD]; ring
  have gDW : ∀ X, galeD l m D X = -m X := fun X => by simp only [galeD, lD, mD]; ring
  have gWE : ∀ X, galeD l m X E = -l X := fun X => by simp only [galeD, lE, mE]; ring
  have gEW : ∀ X, galeD l m E X = l X := fun X => by simp only [galeD, lE, mE]; ring
  have gED : galeD l m E D = -1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have gDE : galeD l m D E = 1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have sRP : galeD l m R P < 0 := g_I_III ha hb HP HR hPl hPm hRl hRm
  have sRQ : galeD l m R Q < 0 := g_I_III ha hb HQ HR hQl hQm hRl hRm
  have sSP : galeD l m S P < 0 := g_I_III ha hb HP HS hPl hPm hSl hSm
  have sSQ : galeD l m S Q < 0 := g_I_III ha hb HQ HS hQl hQm hSl hSm
  have hVs : V = {P, Q, D, E, R, S} := by rw [eq]; perm6
  rw [hVs] at six hl hm ⊢
  exact isRupert_octahedron ⟨
    by nodup6,
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sRQ),
    isFacetTriangle_of_gale (X := Q) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := Q) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRQ),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sRP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRP)⟩

/-- `(Q, R) = (II, II)`: a bicapped tetrahedron with caps `E`, `D`. -/
theorem NF.case_bicap₁ {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ 0 < m Q) (hR : 0 < l R ∧
      0 < m R) (hS : l S < 0 ∧ 0 < m S) :
    IsRupert V := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, a, b, ha, hb, HP, HQ, HR, HS⟩ := h
  obtain ⟨hPl, hPm⟩ := hP
  obtain ⟨hQl, hQm⟩ := hQ
  obtain ⟨hRl, hRm⟩ := hR
  obtain ⟨hSl, hSm⟩ := hS
  have nd := nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    nd
  have gWD : ∀ X, galeD l m X D = m X := fun X => by simp only [galeD, lD, mD]; ring
  have gDW : ∀ X, galeD l m D X = -m X := fun X => by simp only [galeD, lD, mD]; ring
  have gWE : ∀ X, galeD l m X E = -l X := fun X => by simp only [galeD, lE, mE]; ring
  have gEW : ∀ X, galeD l m E X = l X := fun X => by simp only [galeD, lE, mE]; ring
  have gED : galeD l m E D = -1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have gDE : galeD l m D E = 1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have sQP : galeD l m Q P < 0 := by simp only [galeD]; nlinarith [hQl, hQm, hPl, hPm]
  have sRP : galeD l m R P < 0 := by simp only [galeD]; nlinarith [hRl, hRm, hPl, hPm]
  have sSP : galeD l m S P < 0 := g_I_III ha hb HP HS hPl hPm hSl hSm
  have sSQ : galeD l m S Q < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hQl, hQm]
  have sSR : galeD l m S R < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hRl, hRm]
  have hVs : V = {Q, P, S, R, E, D} := by rw [eq]; perm6
  rw [hVs] at six hl hm ⊢
  exact isRupert_bicappedTetrahedron ⟨
    by nodup6,
    affineIndependent_of_gale (X := E) (Y :=
      D) six hl hm (by perm6) (by nodup6) (by norm_num [gED]),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := Q) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sQP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := R) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSR),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := D) (Y := R) (Z := E) six hl hm (by perm6) (by nodup6)
      (by rw [gDW]; linarith) (by rw [gWE]; linarith)
      (by norm_num [gED]),
    isFacetTriangle_of_gale (X := D) (Y := Q) (Z := E) six hl hm (by perm6) (by nodup6)
      (by rw [gDW]; linarith) (by rw [gWE]; linarith)
      (by rw [gED]; norm_num)⟩

/-- `(Q, R) = (II, III)`: a bicapped tetrahedron with caps `E`, `P`. -/
theorem NF.case_bicap₂ {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ 0 < m Q) (hR : l R < 0 ∧
      0 < m R) (hS : l S < 0 ∧ 0 < m S) :
    IsRupert V := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, a, b, ha, hb, HP, HQ, HR, HS⟩ := h
  obtain ⟨hPl, hPm⟩ := hP
  obtain ⟨hQl, hQm⟩ := hQ
  obtain ⟨hRl, hRm⟩ := hR
  obtain ⟨hSl, hSm⟩ := hS
  have nd := nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    nd
  have gWD : ∀ X, galeD l m X D = m X := fun X => by simp only [galeD, lD, mD]; ring
  have gDW : ∀ X, galeD l m D X = -m X := fun X => by simp only [galeD, lD, mD]; ring
  have gWE : ∀ X, galeD l m X E = -l X := fun X => by simp only [galeD, lE, mE]; ring
  have gEW : ∀ X, galeD l m E X = l X := fun X => by simp only [galeD, lE, mE]; ring
  have gED : galeD l m E D = -1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have gDE : galeD l m D E = 1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have sQP : galeD l m Q P < 0 := by simp only [galeD]; nlinarith [hQl, hQm, hPl, hPm]
  have sRP : galeD l m R P < 0 := g_I_III ha hb HP HR hPl hPm hRl hRm
  have sRQ : galeD l m R Q < 0 := by simp only [galeD]; nlinarith [hRl, hRm, hQl, hQm]
  have sSP : galeD l m S P < 0 := g_I_III ha hb HP HS hPl hPm hSl hSm
  have sSQ : galeD l m S Q < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hQl, hQm]
  have hVs : V = {R, D, Q, S, E, P} := by rw [eq]; perm6
  rw [hVs] at six hl hm ⊢
  exact isRupert_bicappedTetrahedron ⟨
    by nodup6,
    affineIndependent_of_gale (X := E) (Y := P) six hl hm (by perm6) (by nodup6) (by
      rw [gEW]
      exact hPl.ne'),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := Q) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sQP),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sRQ),
    isFacetTriangle_of_gale (X := D) (Y := Q) (Z := E) six hl hm (by perm6) (by nodup6)
      (by rw [gDW]; linarith) (by rw [gWE]; linarith)
      (by norm_num [gED]),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sRP)⟩

/-- `(Q, R) = (I½, III)`: a T4. -/
theorem NF.case_T4 {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q = 0) (hR : l R < 0 ∧
      0 < m R) (hS : l S < 0 ∧ 0 < m S) :
    IsRupert V := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, a, b, ha, hb, HP, HQ, HR, HS⟩ := h
  obtain ⟨hPl, hPm⟩ := hP
  obtain ⟨hQl, hQm⟩ := hQ
  obtain ⟨hRl, hRm⟩ := hR
  obtain ⟨hSl, hSm⟩ := hS
  have nd := nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    nd
  have gWD : ∀ X, galeD l m X D = m X := fun X => by simp only [galeD, lD, mD]; ring
  have gDW : ∀ X, galeD l m D X = -m X := fun X => by simp only [galeD, lD, mD]; ring
  have gWE : ∀ X, galeD l m X E = -l X := fun X => by simp only [galeD, lE, mE]; ring
  have gEW : ∀ X, galeD l m E X = l X := fun X => by simp only [galeD, lE, mE]; ring
  have gED : galeD l m E D = -1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have gDE : galeD l m D E = 1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have sRP : galeD l m R P < 0 := g_I_III ha hb HP HR hPl hPm hRl hRm
  have sRQ : galeD l m R Q < 0 := by simp only [galeD]; nlinarith [hRl, hRm, hQl, hQm]
  have sSP : galeD l m S P < 0 := g_I_III ha hb HP HS hPl hPm hSl hSm
  have sSQ : galeD l m S Q < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hQl, hQm]
  have hVs : V = {R, D, Q, S, E, P} := by rw [eq]; perm6
  rw [hVs] at six hl hm ⊢
  exact isRupert_T4 ⟨
    by nodup6,
    affineIndependent_of_gale (X := E) (Y := P) six hl hm (by perm6) (by nodup6) (by
      rw [gEW]
      exact hPl.ne'),
    isFacet_quad_of_gale (X := D) (Y := Q) six hl hm (by perm6) (by nodup6)
      (by rw [gDW, hQm, neg_zero])
      (by rw [gDW, show galeD l m Q P = l Q * m P - m Q * l P from rfl, hQm]
          nlinarith [mul_pos hQl (mul_pos_of_neg_of_neg hPm hPm)]),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRP),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sRQ),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sRP)⟩

/-- `(Q, R) = (I½, II)`: a T5 with apex `Q`. -/
theorem NF.case_T5 {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q = 0) (hR : 0 < l R ∧
      0 < m R) (hS : l S < 0 ∧ 0 < m S) :
    IsRupert V := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, a, b, ha, hb, HP, HQ, HR, HS⟩ := h
  obtain ⟨hPl, hPm⟩ := hP
  obtain ⟨hQl, hQm⟩ := hQ
  obtain ⟨hRl, hRm⟩ := hR
  obtain ⟨hSl, hSm⟩ := hS
  have nd := nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    nd
  have gWD : ∀ X, galeD l m X D = m X := fun X => by simp only [galeD, lD, mD]; ring
  have gDW : ∀ X, galeD l m D X = -m X := fun X => by simp only [galeD, lD, mD]; ring
  have gWE : ∀ X, galeD l m X E = -l X := fun X => by simp only [galeD, lE, mE]; ring
  have gEW : ∀ X, galeD l m E X = l X := fun X => by simp only [galeD, lE, mE]; ring
  have gED : galeD l m E D = -1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have gDE : galeD l m D E = 1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have sRP : galeD l m R P < 0 := by simp only [galeD]; nlinarith [hRl, hRm, hPl, hPm]
  have sSP : galeD l m S P < 0 := g_I_III ha hb HP HS hPl hPm hSl hSm
  have sSQ : galeD l m S Q < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hQl, hQm]
  have sSR : galeD l m S R < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hRl, hRm]
  have hVs : V = {Q, P, R, E, S, D} := by rw [eq]; perm6
  rw [hVs] at six hl hm ⊢
  exact isRupert_cappedSquarePyramid_all ⟨
    by nodup6,
    affineIndependent_of_gale (X := S) (Y := D) six hl hm (by perm6) (by nodup6) (by
      rw [gWD]
      exact hSm.ne'),
    isFacet_quad_of_gale (X := D) (Y := Q) six hl hm (by perm6) (by nodup6)
      (by rw [gDW, hQm, neg_zero])
      (by rw [gDW, show galeD l m Q S = l Q * m S - m Q * l S from rfl, hQm]
          nlinarith [mul_pos hQl (mul_pos hSm hSm)]),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRP),
    isFacetTriangle_of_gale (X := D) (Y := R) (Z := E) six hl hm (by perm6) (by nodup6)
      (by rw [gDW]; linarith) (by rw [gWE]; linarith)
      (by norm_num [gED]),
    isFacetTriangle_of_gale (X := R) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSR),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSP)⟩

/-- `(Q, R) = (I½, II½)`: a T3. -/
theorem NF.case_T3 {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q = 0) (hR : l R = 0 ∧
      0 < m R) (hS : l S < 0 ∧ 0 < m S) :
    IsRupert V := by
  obtain ⟨six, eq, nodup, hl, hm, lD, mD, lE, mE, a, b, ha, hb, HP, HQ, HR, HS⟩ := h
  obtain ⟨hPl, hPm⟩ := hP
  obtain ⟨hQl, hQm⟩ := hQ
  obtain ⟨hRl, hRm⟩ := hR
  obtain ⟨hSl, hSm⟩ := hS
  have nd := nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    nd
  have gWD : ∀ X, galeD l m X D = m X := fun X => by simp only [galeD, lD, mD]; ring
  have gDW : ∀ X, galeD l m D X = -m X := fun X => by simp only [galeD, lD, mD]; ring
  have gWE : ∀ X, galeD l m X E = -l X := fun X => by simp only [galeD, lE, mE]; ring
  have gEW : ∀ X, galeD l m E X = l X := fun X => by simp only [galeD, lE, mE]; ring
  have gED : galeD l m E D = -1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have gDE : galeD l m D E = 1 := by simp only [galeD, lD, mD, lE, mE]; ring
  have sRP : galeD l m R P < 0 := by simp only [galeD]; nlinarith [hRl, hRm, hPl, hPm]
  have sSP : galeD l m S P < 0 := g_I_III ha hb HP HS hPl hPm hSl hSm
  have sSQ : galeD l m S Q < 0 := by simp only [galeD]; nlinarith [hSl, hSm, hQl, hQm]
  have hVs : V = {R, D, P, E, Q, S} := by rw [eq]; perm6
  rw [hVs] at six hl hm ⊢
  exact isRupert_T3 ⟨
    by nodup6,
    affineIndependent_of_gale (X := E) (Y := Q) six hl hm (by perm6) (by nodup6) (by
      rw [gEW]
      exact hQl.ne'),
    isFacet_quad_of_gale (X := D) (Y := Q) six hl hm (by perm6) (by nodup6)
      (by rw [gDW, hQm, neg_zero])
      (by rw [gDE, gWE]; linarith),
    isFacet_quad_of_gale (X := E) (Y := R) six hl hm (by perm6) (by nodup6)
      (by rw [gEW, hRl])
      (by rw [gEW, show galeD l m R Q = l R * m Q - m R * l Q from rfl, hRl, hQm]
          nlinarith [mul_pos hRm (mul_pos hQl hQl)]),
    isFacetTriangle_of_gale (X := Q) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSQ),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := R) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sRP),
    isFacetTriangle_of_gale (X := P) (Y := E) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWE]; linarith) (by rw [gEW]; linarith)
      (sSP),
    isFacetTriangle_of_gale (X := P) (Y := D) (Z := S) six hl hm (by perm6) (by nodup6)
      (by rw [gWD]; linarith) (by rw [gDW]; linarith)
      (sSP)⟩


/-- Every point of the normal form is one of the six. -/
theorem NF.mem {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) {t : ℝ³} (ht : t ∈ V) :
    t = D ∨ t = E ∨ t = P ∨ t = Q ∨ t = R ∨ t = S := by
  rw [h.eq] at ht; simpa only [Finset.mem_insert, Finset.mem_singleton] using ht

/-- **Theorem 10.4**, with `P ∈ I` and `S ∈ III`: the case table. -/
theorem NF.isRupert_core {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : m P < 0) (hS : l S < 0) : IsRupert V := by
  obtain ⟨a, b, ha, hb, HP, HQ, HR, HS⟩ := h.H
  have cP : 0 < l P ∧ m P < 0 := by
    refine ⟨?_, hP⟩
    have : 0 < a * l P := by nlinarith [mul_neg_of_pos_of_neg hb hP]
    exact (pos_iff_pos_of_mul_pos this).mp ha
  have cS : l S < 0 ∧ 0 < m S := by
    refine ⟨hS, ?_⟩
    have : 0 < b * m S := by nlinarith [mul_neg_of_pos_of_neg ha hS]
    exact (pos_iff_pos_of_mul_pos this).mp hb
  have mS : S ∈ V := by rw [h.eq]; simp
  have mP : P ∈ V := by rw [h.eq]; simp
  -- vertex conditions at `S` (via `-m`) and at `P` (via `-l`)
  have hγ : 0 < m Q ∨ 0 < m R := by
    by_contra hc
    push Not at hc
    refine h.six.not_single_neg h.hm.neg mS (by show -m S < 0; linarith [cS.2]) (fun t ht hts => ?_)
    rcases h.mem ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.mD]; norm_num
    · rw [h.mE]; norm_num
    · linarith
    · linarith [hc.1]
    · linarith [hc.2]
    · exact absurd rfl hts
  have hβ : 0 < l Q ∨ 0 < l R := by
    by_contra hc
    push Not at hc
    refine h.six.not_single_neg h.hl.neg mP (by show -l P < 0; linarith [cP.1]) (fun t ht htp => ?_)
    rcases h.mem ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.lD]; norm_num
    · rw [h.lE]; norm_num
    · exact absurd rfl htp
    · linarith [hc.1]
    · linarith [hc.2]
    · linarith
  rcases nf_class ha hb HQ with hQ | hQ | hQ | hQ | hQ <;>
    rcases nf_class ha hb HR with hR | hR | hR | hR | hR
  -- Q ∈ I
  · rcases hγ with h' | h' <;> linarith [hQ.2, hR.2]
  · rcases hγ with h' | h' <;> linarith [hQ.2, hR.2]
  · exact h.mirror.case_bicap₂ ⟨cS.2, cS.1⟩ ⟨hR.2, hR.1⟩ ⟨hQ.2, hQ.1⟩ ⟨cP.2, cP.1⟩
  · exact h.mirror.case_T4 ⟨cS.2, cS.1⟩ ⟨hR.2, hR.1⟩ ⟨hQ.2, hQ.1⟩ ⟨cP.2, cP.1⟩
  · exact h.case_oct cP hQ hR cS
  -- Q ∈ I½
  · rcases hγ with h' | h' <;> linarith [hQ.2, hR.2]
  · rcases hγ with h' | h' <;> linarith [hQ.2, hR.2]
  · exact h.case_T5 cP hQ hR cS
  · exact h.case_T3 cP hQ hR cS
  · exact h.case_T4 cP hQ hR cS
  -- Q ∈ II
  · exact h.swapQR.mirror.case_bicap₂ ⟨cS.2, cS.1⟩ ⟨hQ.2, hQ.1⟩ ⟨hR.2, hR.1⟩ ⟨cP.2, cP.1⟩
  · exact h.swapQR.case_T5 cP hR hQ cS
  · exact h.case_bicap₁ cP hQ hR cS
  · exact h.mirror.case_T5 ⟨cS.2, cS.1⟩ ⟨hR.2, hR.1⟩ ⟨hQ.2, hQ.1⟩ ⟨cP.2, cP.1⟩
  · exact h.case_bicap₂ cP hQ hR cS
  -- Q ∈ II½
  · exact h.swapQR.mirror.case_T4 ⟨cS.2, cS.1⟩ ⟨hQ.2, hQ.1⟩ ⟨hR.2, hR.1⟩ ⟨cP.2, cP.1⟩
  · exact h.swapQR.case_T3 cP hR hQ cS
  · exact h.swapQR.mirror.case_T5 ⟨cS.2, cS.1⟩ ⟨hQ.2, hQ.1⟩ ⟨hR.2, hR.1⟩ ⟨cP.2, cP.1⟩
  · rcases hβ with h' | h' <;> linarith [hQ.1, hR.1]
  · rcases hβ with h' | h' <;> linarith [hQ.1, hR.1]
  -- Q ∈ III
  · exact h.swapQR.case_oct cP hR hQ cS
  · exact h.swapQR.case_T4 cP hR hQ cS
  · exact h.swapQR.case_bicap₂ cP hR hQ cS
  · rcases hβ with h' | h' <;> linarith [hQ.1, hR.1]
  · rcases hβ with h' | h' <;> linarith [hQ.1, hR.1]

/-- **Theorem 10.4.** Every normal form is Rupert. -/
theorem NF.isRupert {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : IsRupert V := by
  obtain ⟨a, b, ha, hb, HP, HQ, HR, HS⟩ := h.H
  have mD : D ∈ V := by rw [h.eq]; simp
  have mE : E ∈ V := by rw [h.eq]; simp
  -- `E` and `D` are vertices: some `m w < 0` and some `l w < 0`
  have hm4 : m P < 0 ∨ m Q < 0 ∨ m R < 0 ∨ m S < 0 := by
    by_contra hc
    push Not at hc
    refine h.six.not_single_neg h.hm mE (by rw [h.mE]; norm_num) (fun t ht hte => ?_)
    rcases h.mem ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.mD]
    · exact absurd rfl hte
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2
  have hl4 : l P < 0 ∨ l Q < 0 ∨ l R < 0 ∨ l S < 0 := by
    by_contra hc
    push Not at hc
    refine h.six.not_single_neg h.hl mD (by rw [h.lD]; norm_num) (fun t ht htd => ?_)
    rcases h.mem ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl htd
    · rw [h.lE]
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2
  have no : ∀ X, 0 < a * l X + b * m X → m X < 0 → l X < 0 → False := fun X hX h1 h2 => by
    nlinarith [mul_neg_of_pos_of_neg ha h2, mul_neg_of_pos_of_neg hb h1]
  rcases hm4 with h1 | h1 | h1 | h1 <;> rcases hl4 with h2 | h2 | h2 | h2
  -- `m P < 0`
  · exact absurd h2 (fun h2 => no P HP h1 h2)
  · exact h.swapQR.swapRS.isRupert_core h1 h2
  · exact h.swapRS.isRupert_core h1 h2
  · exact h.isRupert_core h1 h2
  -- `m Q < 0`
  · exact h.swapPQ.swapQR.swapRS.isRupert_core h1 h2
  · exact absurd h2 (fun h2 => no Q HQ h1 h2)
  · exact h.swapPQ.swapRS.isRupert_core h1 h2
  · exact h.swapPQ.isRupert_core h1 h2
  -- `m R < 0`
  · exact h.swapQR.swapPQ.swapQR.swapRS.isRupert_core h1 h2
  · exact h.swapQR.swapPQ.swapRS.isRupert_core h1 h2
  · exact absurd h2 (fun h2 => no R HR h1 h2)
  · exact h.swapQR.swapPQ.isRupert_core h1 h2
  -- `m S < 0`
  · exact h.swapRS.swapQR.swapPQ.swapQR.swapRS.isRupert_core h1 h2
  · exact h.swapRS.swapQR.swapPQ.swapRS.isRupert_core h1 h2
  · exact h.swapRS.swapQR.swapPQ.isRupert_core h1 h2
  · exact absurd h2 (fun h2 => no S HS h1 h2)

/-! ### The split -/

theorem sum_four {M : Type*} [AddCommMonoid M] {a b c d : ℝ³} (hnd : [a, b, c, d].Nodup)
    (g : ℝ³ → M) : ∑ t ∈ ({a, b, c, d} : Finset ℝ³), g t = g a + g b + g c + g d := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd, -⟩ := hnd
  rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd]
  simp only [add_assoc]

/-- Four distinct listed points. -/
theorem exists_four_of_card {W : Finset ℝ³} (h : W.card = 4) :
    ∃ a b c d : ℝ³, [a, b, c, d].Nodup ∧ W = {a, b, c, d} := by
  classical
  obtain ⟨a, W₁, ha, rfl, h₁⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp h₁
  refine ⟨a, b, c, d, ?_, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  tauto

/-- **Lemma 10.3.**  A split with coplanar `W`: the segment `DE` crosses
`relint conv W`. -/
theorem isRupert_split_coplanar {V : Finset ℝ³} (hS : Six V) {D E P Q R S : ℝ³}
    (hV : V = {D, E, P, Q, R, S}) (hnd : [D, E, P, Q, R, S].Nodup) {μ : ℝ³ → ℝ}
    (hμ : IsDepOn V μ) (hD : 0 < μ D) (hE : 0 < μ E) (hP : μ P < 0) (hQ : μ Q < 0)
    (hR : μ R < 0) (hS' : μ S < 0) (hcop : Coplanar ℝ ({P, Q, R, S} : Set ℝ³)) :
    IsRupert V := by
  classical
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    hnd'
  have hndW : [P, Q, R, S].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS⟩
  obtain ⟨N, hN, c, hNc⟩ := exists_plane_of_coplanar hcop
  have cP : ⟪N, P⟫ = c := hNc P (by simp)
  have cQ : ⟪N, Q⟫ = c := hNc Q (by simp)
  have cR : ⟪N, R⟫ = c := hNc R (by simp)
  have cS : ⟪N, S⟫ = c := hNc S (by simp)
  have mem : ∀ x, (x = D ∨ x = E ∨ x = P ∨ x = Q ∨ x = R ∨ x = S) → x ∈ V := by
    intro x hx; rw [hV]; simpa using hx
  have sμ := hμ.1
  have vμ := hμ.2
  rw [hV, sum_six hnd] at sμ vμ
  set σ := μ D + μ E with hσ
  have hσ0 : 0 < σ := by linarith
  -- `D` is off the plane (no five coplanar)
  have hDc : ⟪N, D⟫ ≠ c := by
    intro h
    apply hS.no5 E (mem E (by simp))
    refine coplanar_of_plane hN (c := c) (fun x hx => ?_)
    have hx' := Finset.mem_erase.mp hx
    rw [hV] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with ⟨hxE, rfl | rfl | rfl | rfl | rfl | rfl⟩
    · exact h
    · exact absurd rfl hxE
    · exact cP
    · exact cQ
    · exact cR
    · exact cS
  have hu : ⟪N, E - D⟫ ≠ 0 := by
    intro h0
    rw [inner_sub_right, sub_eq_zero] at h0
    have := hμ.apply_inner N c
    rw [hV, sum_six hnd, cP, cQ, cR, cS, h0] at this
    have h2 : σ * (⟪N, D⟫ - c) = 0 := by rw [hσ]; linarith
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact hDc (by linarith)
  have hind : AffineIndependent ℝ ![P, Q, R] :=
    affineIndependent_of_cross_ne_zero (hS.cross_ne_zero (mem P (by simp)) (mem Q (by simp))
      (mem R (by simp)) hPQ hPR hQR)
  refine isRupert_of_crossing V {P, Q, R, S} (fun x hx => mem x (by simp at hx; tauto)) N c
    (fun x hx => hNc x (by simpa using hx))
    (by simp) (by simp) (by simp) hind (E - D) hu ?_
  -- the crossing point `X = (μ_D D + μ_E E)/σ`
  set w : ℝ³ → ℝ := fun t => -μ t / σ with hw
  have hwpos : ∀ x ∈ ({P, Q, R, S} : Finset ℝ³), 0 < w x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact div_pos (by linarith) hσ0
  have hwsum : ∑ x ∈ ({P, Q, R, S} : Finset ℝ³), w x = 1 := by
    rw [sum_four hndW]
    simp only [hw]
    rw [← add_div, ← add_div, ← add_div, div_eq_one_iff_eq hσ0.ne']
    linarith
  have hX : σ • (∑ x ∈ ({P, Q, R, S} : Finset ℝ³), w x • x) = μ D • D + μ E • E := by
    rw [sum_four hndW]
    simp only [hw, smul_add, smul_smul]
    have e : ∀ t : ℝ³, σ * (-μ t / σ) = -μ t := fun t => by field_simp
    rw [e, e, e, e]
    linear_combination (norm := module) -vμ
  have key : ∀ v t : ℝ, σ * t = v → (μ D + v) = σ * (1 + t) - μ E → True := fun _ _ _ _ => trivial
  intro v hv hvW
  rw [hV] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  rcases hv with rfl | rfl | h
  · refine ⟨μ E / σ, w, hwpos, hwsum, ?_⟩
    apply smul_right_injective _ hσ0.ne'
    simp only
    rw [hX]
    have e : σ * (μ E / σ) = μ E := by field_simp
    linear_combination (norm := module) e • (E - v) + hσ • v
  · refine ⟨-(μ D / σ), w, hwpos, hwsum, ?_⟩
    apply smul_right_injective _ hσ0.ne'
    simp only
    rw [hX]
    have e : σ * (μ D / σ) = μ D := by field_simp
    linear_combination (norm := module) -(e • (v - D)) + hσ • v
  · exact absurd h hvW

/-- A split with independent `W` gives a normal form. -/
theorem exists_NF_of_split {V : Finset ℝ³} (hS : Six V) {D E P Q R S : ℝ³}
    (hV : V = {D, E, P, Q, R, S}) (hnd : [D, E, P, Q, R, S].Nodup) {μ : ℝ³ → ℝ}
    (hμ : IsDepOn V μ) (hD : 0 < μ D) (hE : 0 < μ E) (hP : μ P < 0) (hQ : μ Q < 0)
    (hR : μ R < 0) (hS' : μ S < 0) (hind : ¬ Coplanar ℝ ({P, Q, R, S} : Set ℝ³)) :
    ∃ l m, NF V D E P Q R S l m := by
  classical
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hDE, hDP, hDQ, hDR, hDS⟩, ⟨hEP, hEQ, hER, hES⟩, ⟨hPQ, hPR, hPS⟩, ⟨hQR, hQS⟩, hRS, -⟩ :=
    hnd'
  have hdet : det3 (Q - P) (R - P) (S - P) ≠ 0 := fun h0 =>
    hind (coplanar_of_det4_eq_zero (by simpa [det4, det3] using h0))
  have hAI : AffineIndependent ℝ ![P, Q, R, S] := affineIndependent_of_det3 hdet
  obtain ⟨bP, bQ, bR, bS, hbs, hbD⟩ := exists_bary hAI D
  obtain ⟨cP, cQ, cR, cS, hcs, hcE⟩ := exists_bary hAI E
  set l : ℝ³ → ℝ := fun t => if t = D then -1 else if t = E then 0 else if t = P then bP
    else if t = Q then bQ else if t = R then bR else bS with hl
  set m : ℝ³ → ℝ := fun t => if t = D then 0 else if t = E then -1 else if t = P then cP
    else if t = Q then cQ else if t = R then cR else cS with hm
  have lD : l D = -1 := by simp [hl]
  have lE : l E = 0 := by simp [hl, Ne.symm hDE]
  have lP : l P = bP := by simp [hl, Ne.symm hDP, Ne.symm hEP]
  have lQ : l Q = bQ := by simp [hl, Ne.symm hDQ, Ne.symm hEQ, Ne.symm hPQ]
  have lR : l R = bR := by simp [hl, Ne.symm hDR, Ne.symm hER, Ne.symm hPR, Ne.symm hQR]
  have lS : l S = bS := by
    simp [hl, Ne.symm hDS, Ne.symm hES, Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
  have mD : m D = 0 := by simp [hm]
  have mE : m E = -1 := by simp [hm, Ne.symm hDE]
  have mP : m P = cP := by simp [hm, Ne.symm hDP, Ne.symm hEP]
  have mQ : m Q = cQ := by simp [hm, Ne.symm hDQ, Ne.symm hEQ, Ne.symm hPQ]
  have mR : m R = cR := by simp [hm, Ne.symm hDR, Ne.symm hER, Ne.symm hPR, Ne.symm hQR]
  have mS : m S = cS := by
    simp [hm, Ne.symm hDS, Ne.symm hES, Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
  -- `(H)` from the split and uniqueness of barycentric coordinates
  have sμ := hμ.1
  have vμ := hμ.2
  rw [hV, sum_six hnd] at sμ vμ
  have hk : cmb (Q - P) (R - P) (S - P) (μ D * bQ + μ E * cQ + μ Q) (μ D * bR + μ E * cR + μ R)
      (μ D * bS + μ E * cS + μ S) = 0 := by
    simp only [cmb]
    have vμ' : μ D • (bP • P + bQ • Q + bR • R + bS • S) + μ E • (cP • P + cQ • Q + cR • R +
      cS • S) +
        μ P • P + μ Q • Q + μ R • R + μ S • S = 0 := by rw [← hbD, ← hcE]; exact vμ
    linear_combination (norm := module) vμ' - (μ D * hbs + μ E * hcs + sμ) • P
  obtain ⟨hkQ, hkR, hkS⟩ := cmb_eq_zero hdet hk
  have hkP : μ D * bP + μ E * cP + μ P = 0 := by
    linear_combination μ D * hbs + μ E * hcs + sμ - hkQ - hkR - hkS
  refine ⟨l, m, ⟨hS, hV, hnd, ⟨?_, ?_⟩, ⟨?_, ?_⟩, lD, mD, lE, mE,
    μ D, μ E, hD, hE, ?_, ?_, ?_, ?_⟩⟩
  · rw [hV, sum_six hnd, lD, lE, lP, lQ, lR, lS]; linarith
  · rw [hV, sum_six hnd, lD, lE, lP, lQ, lR, lS, hbD]; module
  · rw [hV, sum_six hnd, mD, mE, mP, mQ, mR, mS]; linarith
  · rw [hV, sum_six hnd, mD, mE, mP, mQ, mR, mS, hcE]; module
  · rw [lP, mP]; linarith
  · rw [lQ, mQ]; linarith
  · rw [lR, mR]; linarith
  · rw [lS, mS]; linarith

/-- Every 2+4 split gives a passage. -/
theorem isRupert_of_split {V : Finset ℝ³} (hS : Six V) {D E : ℝ³} (hD : D ∈ V) (hE : E ∈ V)
    (hDE : D ≠ E) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ) (hμD : 0 < μ D) (hμE : 0 < μ E)
    (hμW : ∀ x ∈ V, x ≠ D → x ≠ E → μ x < 0) : IsRupert V := by
  classical
  have hW : ((V.erase D).erase E).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hDE.symm, hE⟩),
      Finset.card_erase_of_mem hD, hS.card]
  obtain ⟨P, Q, R, S, hndW, hWeq⟩ := exists_four_of_card hW
  have hmemW : ∀ x, x ∈ ({P, Q, R, S} : Finset ℝ³) ↔ x ≠ E ∧ x ≠ D ∧ x ∈ V := by
    intro x; rw [← hWeq]; simp only [Finset.mem_erase]
  obtain ⟨hPE, hPD, hP⟩ := (hmemW P).mp (by simp)
  obtain ⟨hQE, hQD, hQ⟩ := (hmemW Q).mp (by simp)
  obtain ⟨hRE, hRD, hR⟩ := (hmemW R).mp (by simp)
  obtain ⟨hSE, hSD, hS'⟩ := (hmemW S).mp (by simp)
  have hV : V = {D, E, P, Q, R, S} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases h1 : x = D; · exact Or.inl h1
      by_cases h2 : x = E; · exact Or.inr (Or.inl h2)
      have := (hmemW x).mpr ⟨h2, h1, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  have hnd : [D, E, P, Q, R, S].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hndW ⊢
    exact ⟨⟨hDE, Ne.symm hPD, Ne.symm hQD, Ne.symm hRD, Ne.symm hSD⟩,
      ⟨Ne.symm hPE, Ne.symm hQE, Ne.symm hRE, Ne.symm hSE⟩, hndW⟩
  have nP := hμW P hP hPD hPE
  have nQ := hμW Q hQ hQD hQE
  have nR := hμW R hR hRD hRE
  have nS := hμW S hS' hSD hSE
  by_cases hcop : Coplanar ℝ ({P, Q, R, S} : Set ℝ³)
  · exact isRupert_split_coplanar hS hV hnd hμ hμD hμE nP nQ nR nS hcop
  · obtain ⟨l, m, h⟩ := exists_NF_of_split hS hV hnd hμ hμD hμE nP nQ nR nS hcop
    exact h.isRupert

/-! ### Assembly -/

/-- Setting (S) is Rupert. -/
theorem Six.isRupert {V : Finset ℝ³} (hS : Six V) : IsRupert V := by
  obtain ⟨l, m, hF⟩ := hS.exists_galeFrame
  by_cases hall : ∀ i ∈ V, ∃ j ∈ V, IsOPair l m i j
  · exact isRupert_of_all_partners hS hF hall
  · push Not at hall
    obtain ⟨i, hi, hno⟩ := hall
    obtain ⟨D, hD, E, hE, hDE, μ, hμ, hμD, hμE, hμW⟩ := exists_split_of_no_partner hS hF hi hno
    exact isRupert_of_split hS hD hE hDE hμ hμD hμE hμW

/-- **Theorem 10.0.** Every convex polyhedron with at most six vertices is
Rupert.  `V` need not consist of vertices only. -/
theorem isRupert_of_card_le_six (V : Finset ℝ³) (hV : V.card ≤ 6)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  obtain ⟨V', hV'V, hhull, hmin⟩ := exists_hull_minimal V
  rw [← hhull] at hint
  apply (isRupert_congr_hull hhull).mp
  have h1 := Finset.card_le_card hV'V
  by_cases h5 : V'.card ≤ 5
  · exact isRupert_of_card_le_five V' h5 hint
  by_cases hpyr : ∃ E ∈ V', Coplanar ℝ ((V'.erase E : Finset ℝ³) : Set ℝ³)
  · obtain ⟨E, -, hE⟩ := hpyr
    exact isRupert_of_pyramid V' E hint hE
  push Not at hpyr
  exact Six.isRupert ⟨by omega, hmin, not_coplanar_of_interior_nonempty hint, hpyr⟩

end Minimality

end RupertMinimality
