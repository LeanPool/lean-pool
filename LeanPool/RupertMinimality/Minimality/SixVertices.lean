/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.BicappedTetrahedron
public import LeanPool.RupertMinimality.Minimality.Crossing

/-! # Six Vertices -/

@[expose] public section

namespace RupertMinimality

/-!
# L6 (partial): six-vertex types covered by the coplanar-silhouette theorem

All proved via `isRupert_of_crossing`:
* T2, pentagonal pyramids: `isRupert_of_pyramid`.
* T7, bicapped tetrahedra: `isRupert_bicappedTetrahedron`.
* T1, triangular prisms whose lateral lines meet at a point (`isRupert_frustum`),
  and prisms with parallel lateral edges not all of the same length
  (`isRupert_parallelPrism`, via `isRupert_prism_core`).  Translation prisms
  `T + [0, w]` are not covered here; see `Prism.lean` and `RightPrism.lean`.
* T5, capped square pyramids, unless the base edges `S₁S₄` and `S₂S₃` next to
  the capped base edge are parallel: `isRupert_cappedSquarePyramid`
  (combinatorial, via `IsCappedSquarePyramid.exists_normalForm`) and
  `isRupert_cappedSquarePyramid_normalForm` (barycentric normal form; the
  plane `ES₁S₂` when `γ₂ < b₂`, the lateral face `ES₃S₄` when `γ₂ > b₂`).
* T3, T4, T6 (octahedra) and the remaining T5 are not covered by this theorem;
  see `L8T3.lean`, `L8T4.lean`, `OctahedronAll.lean` and `L8Shapes.lean`.

The labels T1–T7 of the seven combinatorial types are listed in `README.md`.
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- **T1, concurrent lateral lines (frustum).**  A triangular prism whose
three lateral lines meet at a point `O`: the
small end is `A' = O + α (A - O)` etc. with `α, β, γ ∈ (0, 1)`, and `OABC` is
a nondegenerate tetrahedron.  View from `O` through the centroid of the big
end `ABC`. -/
theorem isRupert_frustum (A B C O : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, O]) (α β γ : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    IsRupert {A, B, C, O + α • (A - O), O + β • (B - O), O + γ • (C - O)} := by
  classical
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdet : det4 A B C O ≠ 0 := fun h0 =>
    not_coplanar_of_affineIndependent hind (coplanar_of_det4_eq_zero h0)
  set N := cross (B - A) (C - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hdet (by simp [det4, ← hNdef, h0])
  have hind3 : AffineIndependent ℝ ![A, B, C] := affineIndependent_of_cross_ne_zero hN
  have hinj := hind3.injective
  have hAB : A ≠ B := fun h => by have := @hinj 0 1 (by simp [h]); exact absurd this (by decide)
  have hAC : A ≠ C := fun h => by have := @hinj 0 2 (by simp [h]); exact absurd this (by decide)
  have hBC : B ≠ C := fun h => by have := @hinj 1 2 (by simp [h]); exact absurd this (by decide)
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) (C - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hNC : ⟪N, C⟫ = c := by
    have := inner_cross_right (B - A) (C - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({A, B, C} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNB
    · exact hNC
  set G := (1 / 3 : ℝ) • A + (1 / 3 : ℝ) • B + (1 / 3 : ℝ) • C
  have hNG : ⟪N, G⟫ = c := by
    simp only [G, inner_add_right, real_inner_smul_right, hNB, hNC, ← hc]; ring
  have hu₀ : ⟪N, G - O⟫ ≠ 0 := by
    rw [inner_sub_right, hNG]
    intro h0; apply hdet
    simp only [det4, ← hNdef, inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, C} (by intro x hx; simp at hx ⊢; tauto) N c hWN
    (by simp) (by simp) (by simp) hind3 (G - O) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact absurd rfl hvW.2.2
  · exact exists_weights3 hAB hAC hBC (t := 1 - α) (α := α + (1 - α) / 3)
      (β := (1 - α) / 3) (γ := (1 - α) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)
  · exact exists_weights3 hAB hAC hBC (t := 1 - β) (α := (1 - β) / 3)
      (β := β + (1 - β) / 3) (γ := (1 - β) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)
  · exact exists_weights3 hAB hAC hBC (t := 1 - γ) (α := (1 - γ) / 3)
      (β := (1 - γ) / 3) (γ := γ + (1 - γ) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)

/-- Weights on a four-point `Finset`. -/
theorem exists_weights4 {A B P Q v u : ℝ³} (hAB : A ≠ B) (hAP : A ≠ P) (hAQ : A ≠ Q)
    (hBP : B ≠ P) (hBQ : B ≠ Q) (hPQ : P ≠ Q)
    {t α β γ δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (h1 : α + β + γ + δ = 1) (h : v + t • u = α • A + β • B + γ • P + δ • Q) :
    ∃ t' : ℝ, ∃ μ : ℝ³ → ℝ, (∀ w ∈ ({A, B, P, Q} : Finset ℝ³), 0 < μ w) ∧
      ∑ w ∈ ({A, B, P, Q} : Finset ℝ³), μ w = 1 ∧
      v + t' • u = ∑ w ∈ ({A, B, P, Q} : Finset ℝ³), μ w • w := by
  classical
  refine ⟨t, fun w => if w = A then α else if w = B then β else if w = P then γ else δ,
    ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [hAB.symm, hAP.symm, hAQ.symm, hBP.symm, hBQ.symm, hPQ.symm, *]
  · rw [Finset.sum_insert (by simp [hAB, hAP, hAQ]), Finset.sum_insert (by simp [hBP, hBQ]),
      Finset.sum_insert (by simp [hPQ]), Finset.sum_singleton]
    simp [hAB.symm, hAP.symm, hAQ.symm, hBP.symm, hBQ.symm, hPQ.symm, ← h1, add_assoc]
  · rw [Finset.sum_insert (by simp [hAB, hAP, hAQ]), Finset.sum_insert (by simp [hBP, hBQ]),
      Finset.sum_insert (by simp [hPQ]), Finset.sum_singleton, h]
    simp [hAB.symm, hAP.symm, hAQ.symm, hBP.symm, hBQ.symm, hPQ.symm, add_assoc]

theorem cross_smul_left_self (k : ℝ) (w : ℝ³) : cross (k • w) w = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem cross_smul_right' (a : ℝ³) (k : ℝ) (w : ℝ³) : cross a (k • w) = k • cross a w := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- **Parallel prism, one quad face.**  The quad `A B B' A'` is admissible when
the opposite lateral edge `CC'` is shorter than `BB'`. -/
theorem isRupert_prism_core (A B C w : ℝ³) (hdet : ⟪cross (B - A) w, C - A⟫ ≠ 0)
    (sA sB sC : ℝ) (hA : 0 < sA) (hB : 0 < sB) (hC : 0 < sC) (hlt : sC < sB) :
    IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
  classical
  set N := cross (B - A) w with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hdet (by rw [h0, inner_zero_left])
  have hNw : ⟪N, w⟫ = 0 := inner_cross_right _ _
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) w; rw [← hNdef, inner_sub_right] at this; linarith
  have hw0 : w ≠ 0 := fun h0 => hN (by rw [hNdef, h0]; ext i; fin_cases i <;> simp [cross])
  have hBA : ∀ k : ℝ, B - A ≠ k • w := fun k h => hN (by rw [hNdef, h, cross_smul_left_self])
  -- the four quad vertices are distinct
  have hAB : A ≠ B := fun h => hBA 0 (by rw [h, sub_self, zero_smul])
  have hAA' : A ≠ A + sA • w := fun h => hw0 (by
    have : sA • w = 0 := by
      have := congrArg (fun x => x - A) h; simpa using this.symm
    exact (smul_eq_zero.mp this).resolve_left hA.ne')
  have hAB' : A ≠ B + sB • w := fun h => hBA (-sB) (by rw [h]; module)
  have hBA' : B ≠ A + sA • w := fun h => hBA sA (by rw [h]; module)
  have hBB' : B ≠ B + sB • w := fun h => hw0 (by
    have : sB • w = 0 := by
      have := congrArg (fun x => x - B) h; simpa using this.symm
    exact (smul_eq_zero.mp this).resolve_left hB.ne')
  have hA'B' : A + sA • w ≠ B + sB • w := fun h => hBA (sA - sB) (by
    have : B = A + sA • w - sB • w := by rw [h]; module
    rw [this]; module)
  have hWN : ∀ x ∈ ({A, B, A + sA • w, B + sB • w} : Finset ℝ³), ⟪N, x⟫ = c := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · exact hNB
    · rw [inner_add_right, real_inner_smul_right, hNw, mul_zero, add_zero]
    · rw [inner_add_right, real_inner_smul_right, hNw, mul_zero, add_zero, hNB]
  have hind3 : AffineIndependent ℝ ![A, B, A + sA • w] := by
    apply affineIndependent_of_cross_ne_zero
    rw [add_sub_cancel_left, cross_smul_right', ← hNdef]
    exact smul_ne_zero hA.ne' hN
  -- weights
  set r := sC / sB with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hB]; exact hlt
  have hrs : r * sB = sC := by rw [hr]; field_simp
  set δ := (1 - r) / 2
  set q := (1 + r) / 2
  set m := (q - r) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hm : 0 < m := by simp only [m, q]; linarith
  have hqm : 0 < q - m := by simp only [m, q]; linarith
  have hqmr : 0 < q - m - r := by simp only [m, q]; linarith
  have hsum : δ / 2 + (q - m) + δ / 2 + m = 1 := by simp only [δ, q]; ring
  set X := (δ / 2) • A + (q - m) • B + (δ / 2) • (A + sA • w) + m • (B + sB • w)
  have hNX : ⟪N, X⟫ = c := by
    simp only [X, inner_add_right, real_inner_smul_right, hNw, hNB, ← hc]
    linear_combination c * hsum
  have hu₀ : ⟪N, X - C⟫ ≠ 0 := by
    rw [inner_sub_right, hNX]
    intro h0; apply hdet
    rw [inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, A + sA • w, B + sB • w}
    (by intro x hx; simp at hx ⊢; tauto) N c hWN (by simp) (by simp) (by simp) hind3
    (X - C) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact exists_weights4 hAB hAA' hAB' hBA' hBB' hA'B' (t := 1) (by positivity) hqm
      (by positivity) hm hsum (by simp only [X]; module)
  · exact absurd rfl hvW.2.2.1
  · exact absurd rfl hvW.2.2.2
  · refine exists_weights4 hAB hAA' hAB' hBA' hBB' hA'B' (t := 1) (α := δ / 2)
      (β := q - m - r) (γ := δ / 2) (δ := m + r) (by positivity) hqmr (by positivity)
      (by positivity) (by linear_combination hsum) ?_
    rw [← hrs]; simp only [X]; module

/-- **T1, parallel lateral edges of unequal lengths.**  A triangular prism
with parallel lateral edges `A' = A + s_A w` etc. (`s_A, s_B, s_C > 0`, `w`
not parallel to the plane `ABC`), not a translation prism (the lengths are not
all equal): view through a lateral quadrilateral whose opposite lateral edge is
shorter than the longer of its two. -/
theorem isRupert_parallelPrism (A B C w : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, A + w])
    (sA sB sC : ℝ) (hA : 0 < sA) (hB : 0 < sB) (hC : 0 < sC) (hne : ¬ (sA = sB ∧ sB = sC)) :
    IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
  have hD0 : det4 A B C (A + w) ≠ 0 := fun h0 =>
    not_coplanar_of_affineIndependent hind (coplanar_of_det4_eq_zero h0)
  have hperm : ∀ P Q R : ℝ³, (P = A ∧ Q = B ∧ R = C) ∨ (P = B ∧ Q = A ∧ R = C) ∨
      (P = B ∧ Q = C ∧ R = A) ∨ (P = A ∧ Q = C ∧ R = B) →
      ⟪cross (Q - P) w, R - P⟫ ≠ 0 := by
    intro P Q R h h0
    apply hD0
    simp only [det4, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial] at h0 ⊢
    simp only [add_sub_cancel_left, Fin.isValue, PiLp.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] at h0 ⊢
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      first | linear_combination h0 | linear_combination -h0
  have hset : ∀ {X : Finset ℝ³}, X = {A, B, C, A + sA • w, B + sB • w, C + sC • w} →
      IsRupert X → IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
    intro X hX h; rwa [← hX]
  by_cases h1 : sC < sB
  · exact isRupert_prism_core A B C w (hperm A B C (Or.inl ⟨rfl, rfl, rfl⟩)) sA sB sC hA hB hC h1
  by_cases h2 : sC < sA
  · refine hset ?_ (isRupert_prism_core B A C w
      (hperm B A C (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) sB sA sC hB hA hC h2)
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  push Not at h1 h2
  by_cases h3 : sA < sC
  · refine hset ?_ (isRupert_prism_core B C A w
      (hperm B C A (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) sB sC sA hB hC hA h3)
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · have h4 : sB < sC := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd ⟨by linarith, h⟩ hne
    refine hset ?_ (isRupert_prism_core A C B w
      (hperm A C B (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))) sA sC sB hA hC hB h4)
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem cross_self (a : ℝ³) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- **T5, the lateral face `E S₃ S₄`** (case `b₂ < γ₂`): project along
`X - S₂` with `X` close to `S₃` on the face. -/
theorem isRupert_cappedSquarePyramid_lateral (A B C T : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : b₂ - γ₂ + t₂ = 1)
    (hconv : β₁ * γ₂ < c₁ * b₂) (hlt : b₂ < γ₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T, b₂ • B - γ₂ • C + t₂ • T} := by
  classical
  set S := b₂ • B - γ₂ • C + t₂ • T with hS
  set K := a₁ • A - β₁ • B + c₁ • C + t₁ • T with hK
  have hnc := not_coplanar_of_affineIndependent hind
  have hdet0 : det4 A B T C ≠ 0 := fun h0 => hnc ((coplanar_of_det4_eq_zero h0).subset
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  set N := cross (B - A) (S - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hNC : ⟪N, C - A⟫ = t₂ * det4 A B T C := by
    have ht : t₂ = 1 - b₂ + γ₂ := by linarith
    simp only [hNdef, hS, det4, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial, ht]
    simp
    ring
  have hNC0 : ⟪N, C - A⟫ ≠ 0 := by rw [hNC]; exact mul_ne_zero ht₂.ne' hdet0
  have hN : N ≠ 0 := fun h0 => hNC0 (by rw [h0, inner_zero_left])
  have hindW : AffineIndependent ℝ ![A, B, S] := affineIndependent_of_cross_ne_zero hN
  have hAB : A ≠ B := fun h => hN (by rw [hNdef, h, sub_self]; ext i; fin_cases i <;> simp [cross])
  have hAS : A ≠ S := fun h => hN (by
    rw [hNdef, ← h, sub_self]
    ext i
    fin_cases i <;> simp [cross])
  have hBS : B ≠ S := fun h => hN (by rw [hNdef, ← h, cross_self])
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) (S - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hNS : ⟪N, S⟫ = c := by
    have := inner_cross_right (B - A) (S - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({A, B, S} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNB
    · exact hNS
  -- the crossing point `X = ξA A + ξB B + ξS S`, with `ξB` close to `1`
  have hβc : β₁ < c₁ := by
    have h1 : c₁ * b₂ < c₁ * γ₂ := mul_lt_mul_of_pos_left hlt hc₁
    have h2 : β₁ * γ₂ < c₁ * γ₂ := hconv.trans h1
    exact lt_of_mul_lt_mul_right h2 hγ₂.le
  set φK := t₂ * c₁ + γ₂ * t₁
  have hφK : 0 < φK := by positivity
  set D1 := γ₂ - b₂
  set D2 := t₂ * (c₁ - β₁) + t₁ * (γ₂ - b₂)
  have hD1 : 0 < D1 := by simp only [D1]; linarith
  have hD2 : 0 < D2 := by
    simp only [D2]
    have := mul_pos ht₂ (sub_pos.mpr hβc)
    have := mul_pos ht₁ (sub_pos.mpr hlt)
    linarith
  have hD1γ : D1 < γ₂ := by simp only [D1]; linarith
  have hD2φ : D2 < φK := by
    simp only [D2, φK]; nlinarith [mul_pos ht₂ hβ₁, mul_pos ht₁ hb₂]
  set ε := D1 * D2 / (2 * γ₂ * φK)
  have hε : 0 < ε := by positivity
  have hεγ : γ₂ * ε < D1 := by
    simp only [ε]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith [mul_lt_mul_of_pos_left hD2φ (mul_pos hγ₂ hD1), mul_pos (mul_pos hγ₂ hD1) hφK]
  have hεφ : φK * ε < D2 := by
    simp only [ε]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith [mul_lt_mul_of_pos_left hD1γ (mul_pos hφK hD2), mul_pos (mul_pos hφK hD2) hγ₂]
  have hε1 : ε < 1 := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hγ₂.le
    linarith
  set ξA := ε / 2
  set ξB := 1 - ε
  set ξS := ε / 2
  have hξ : ξA + ξB + ξS = 1 := by simp only [ξA, ξB, ξS]; ring
  set X := ξA • A + ξB • B + ξS • S
  have hNX : ⟪N, X⟫ = c := by
    simp only [X, inner_add_right, real_inner_smul_right, hNB, hNS, ← hc]
    linear_combination c * hξ
  have hu₀ : ⟪N, X - C⟫ ≠ 0 := by
    rw [inner_sub_right, hNX]
    intro h0; apply hNC0
    rw [inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, S} (by intro x hx; simp at hx ⊢; tauto) N c hWN
    (by simp) (by simp) (by simp) hindW (X - C) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  have ht₂0 : t₂ ≠ 0 := ht₂.ne'
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact exists_weights3 hAB hAS hBS (t := 1) (by positivity) (by simp only [ξB]; linarith)
      (by positivity) hξ (by simp only [X]; module)
  · -- `S₁ = T`
    refine exists_weights3 hAB hAS hBS (t := γ₂ / t₂) (α := γ₂ * ξA / t₂)
      (β := (γ₂ * ξB - b₂) / t₂) (γ := (1 + γ₂ * ξS) / t₂) (by positivity) ?_ (by positivity)
      ?_ ?_
    · apply div_pos _ ht₂
      simp only [ξB]; nlinarith
    · rw [← add_div, ← add_div, div_eq_one_iff_eq ht₂0]
      linear_combination γ₂ * hξ - hsum₂
    · simp only [X, hS]
      match_scalars <;> field_simp <;> ring
  · -- the cap `K`
    refine exists_weights3 hAB hAS hBS (t := φK / t₂) (α := a₁ + φK / t₂ * ξA)
      (β := (φK * ξB - β₁ * t₂ - t₁ * b₂) / t₂) (γ := t₁ / t₂ + φK / t₂ * ξS)
      (by positivity) ?_ (by positivity) ?_ ?_
    · apply div_pos _ ht₂
      have : φK * ξB = φK - φK * ε := by simp only [ξB]; ring
      have h3 : φK - D2 = β₁ * t₂ + t₁ * b₂ := by simp only [φK, D2]; ring
      linarith
    · field_simp
      simp only [φK, ξA, ξB, ξS]
      linear_combination t₂ * hsum₁ - t₁ * hsum₂
    · simp only [X, hS, hK, φK]
      match_scalars <;> field_simp <;> ring
  · exact absurd rfl hvW.2.2

/-- **T5 in normal form.**  `(A, B, C, T) = (E, S₃, S₂, S₁)`, the cap
`K = (a₁, -β₁, c₁, t₁)` and `S₄ = (0, b₂, -γ₂, t₂)` in barycentrics, convexity
at `ES₁`: `β₁ γ₂ < c₁ b₂`.  If `γ₂ ≠ b₂` (i.e. `S₁S₄ ∦ S₂S₃`), the view
through `ES₁S₂` (`γ₂ < b₂`) or through `ES₃S₄` (`γ₂ > b₂`) is admissible. -/
theorem isRupert_cappedSquarePyramid_normalForm (A B C T : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : b₂ - γ₂ + t₂ = 1)
    (hconv : β₁ * γ₂ < c₁ * b₂) (hpar : γ₂ ≠ b₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T, b₂ • B - γ₂ • C + t₂ • T} := by
  rcases lt_or_gt_of_ne hpar with h | h
  · have := isRupert_bicap_case A B C T hind a₁ β₁ c₁ t₁ 0 b₂ γ₂ t₂ ha₁ hβ₁ hc₁ ht₁ le_rfl hb₂
      hγ₂ ht₂ hsum₁ (by linarith) hconv h
    simpa using this
  · exact isRupert_cappedSquarePyramid_lateral A B C T hind a₁ β₁ c₁ t₁ b₂ γ₂ t₂ ha₁ hβ₁ hc₁ ht₁
      hb₂ hγ₂ ht₂ hsum₁ hsum₂ hconv h

/-- `F ⊆ V` spans a facet of `conv V`: an affine functional vanishes on `F` and
is negative on the other points of `V`. -/
def IsFacet (V F : Finset ℝ³) : Prop :=
  ∃ f : ℝ³ →ᵃ[ℝ] ℝ, (∀ x ∈ F, f x = 0) ∧ ∀ x ∈ V, x ∉ F → f x < 0

/-- **T5, combinatorial form.**  A square pyramid with apex `E` and base
`S₁S₂S₃S₄` (cyclic order, a planar quadrilateral facet), capped by `K` over the
lateral face `ES₁S₂`: the facets are the base, `ES₂S₃`, `ES₃S₄`, `ES₄S₁`,
`KES₁`, `KS₁S₂`, `KS₂E`. -/
structure IsCappedSquarePyramid (E S₁ S₂ S₃ S₄ K : ℝ³) : Prop where
  nodup : [E, S₁, S₂, S₃, S₄, K].Nodup
  affineIndependent : AffineIndependent ℝ ![E, S₃, S₂, S₁]
  base : IsFacet {E, S₁, S₂, S₃, S₄, K} {S₁, S₂, S₃, S₄}
  facet_ES₂S₃ : IsFacetTriangle {E, S₁, S₂, S₃, S₄, K} E S₂ S₃
  facet_ES₃S₄ : IsFacetTriangle {E, S₁, S₂, S₃, S₄, K} E S₃ S₄
  facet_ES₄S₁ : IsFacetTriangle {E, S₁, S₂, S₃, S₄, K} E S₄ S₁
  facet_KES₁ : IsFacetTriangle {E, S₁, S₂, S₃, S₄, K} K E S₁
  facet_KS₁S₂ : IsFacetTriangle {E, S₁, S₂, S₃, S₄, K} K S₁ S₂
  facet_KS₂E : IsFacetTriangle {E, S₁, S₂, S₃, S₄, K} K S₂ E

/-- The facet conditions put a capped square pyramid in normal form with
respect to `(A, B, C, T) = (E, S₃, S₂, S₁)`. -/
theorem IsCappedSquarePyramid.exists_normalForm {E S₁ S₂ S₃ S₄ K : ℝ³}
    (h : IsCappedSquarePyramid E S₁ S₂ S₃ S₄ K) :
    ∃ a₁ β₁ c₁ t₁ b₂ γ₂ t₂ : ℝ, 0 < a₁ ∧ 0 < β₁ ∧ 0 < c₁ ∧ 0 < t₁ ∧
      0 < b₂ ∧ 0 < γ₂ ∧ 0 < t₂ ∧
      a₁ - β₁ + c₁ + t₁ = 1 ∧ b₂ - γ₂ + t₂ = 1 ∧ β₁ * γ₂ < c₁ * b₂ ∧
      K = a₁ • E - β₁ • S₃ + c₁ • S₂ + t₁ • S₁ ∧ S₄ = b₂ • S₃ - γ₂ • S₂ + t₂ • S₁ := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hE1, hE2, hE3, hE4, hEK⟩, ⟨h12, h13, h14, h1K⟩, ⟨h23, h24, h2K⟩,
    ⟨h34, h3K⟩, h4K, -⟩ := hnd
  have h1E := Ne.symm hE1; have h2E := Ne.symm hE2; have h3E := Ne.symm hE3
  have h4E := Ne.symm hE4; have hKE := Ne.symm hEK; have h21 := Ne.symm h12
  have h31 := Ne.symm h13; have h41 := Ne.symm h14; have hK1 := Ne.symm h1K
  have h32 := Ne.symm h23; have h42 := Ne.symm h24; have hK2 := Ne.symm h2K
  have h43 := Ne.symm h34; have hK3 := Ne.symm h3K; have hK4 := Ne.symm h4K
  obtain ⟨l1A, l1B, l1C, l1T, hs1, hK⟩ := exists_bary h.affineIndependent K
  obtain ⟨l2A, l2B, l2C, l2T, hs2, hS⟩ := exists_bary h.affineIndependent S₄
  have ev1 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK ▸ affine_apply_comb4 f hs1 :
    f K = l1A * f E + l1B * f S₃ + l1C * f S₂ + l1T * f S₁)
  have ev2 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hS ▸ affine_apply_comb4 f hs2 :
    f S₄ = l2A * f E + l2B * f S₃ + l2C * f S₂ + l2T * f S₁)
  -- the base: `S₄` has no `E`-coordinate, `K` a positive one
  obtain ⟨f, hf0, hf⟩ := h.base
  have f1 := hf0 S₁ (by simp); have f2 := hf0 S₂ (by simp)
  have f3 := hf0 S₃ (by simp); have f4 := hf0 S₄ (by simp)
  have fE := hf E (by simp) (by simp [hE1, hE2, hE3, hE4])
  have fK := hf K (by simp) (by simp [Ne.symm h1K, Ne.symm h2K, Ne.symm h3K, Ne.symm h4K])
  have e0 := ev2 f
  rw [f4, f3, f2, f1] at e0
  simp only [mul_zero, add_zero] at e0
  have h2A : l2A = 0 := (mul_eq_zero.mp e0.symm).resolve_right fE.ne
  rw [ev1, f3, f2, f1] at fK
  simp only [mul_zero, add_zero] at fK
  have h1A : 0 < l1A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fE.le]
  -- face `ES₂S₃`: positive `S₁`-coordinates
  obtain ⟨g, gE, g2, g3, hg⟩ := h.facet_ES₂S₃
  have g1 := hg S₁ (by simp) (by assumption) (by assumption) (by assumption)
  have gK := hg K (by simp) (by assumption) (by assumption) (by assumption)
  have g4 := hg S₄ (by simp) (by assumption) (by assumption) (by assumption)
  rw [ev1, gE, g2, g3] at gK
  rw [ev2, gE, g2, g3] at g4
  simp only [mul_zero, zero_add] at gK g4
  have h1T : 0 < l1T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc g1.le]
  have h2T : 0 < l2T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc g1.le]
  -- face `ES₃S₄`: negative `S₂`-coordinate of `S₄`
  obtain ⟨k, kE, k3, k4, hk⟩ := h.facet_ES₃S₄
  have k2 := hk S₂ (by simp) (by assumption) (by assumption) (by assumption)
  have k1 := hk S₁ (by simp) (by assumption) (by assumption) (by assumption)
  have ek := ev2 k
  rw [k4, kE, k3] at ek
  simp only [mul_zero, zero_add] at ek
  have h2C : l2C < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc k2.le, mul_neg_of_pos_of_neg h2T k1]
  -- face `ES₄S₁`: positive `S₃`-coordinate of `S₄`
  obtain ⟨m, mE, m4, m1, hm⟩ := h.facet_ES₄S₁
  have m3 := hm S₃ (by simp) (by assumption) (by assumption) (by assumption)
  have m2 := hm S₂ (by simp) (by assumption) (by assumption) (by assumption)
  have em := ev2 m
  rw [m4, mE, m1] at em
  simp only [mul_zero, zero_add, add_zero] at em
  have h2B : 0 < l2B := by
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos hc m3.le, mul_pos_of_neg_of_neg h2C m2]
  -- face `KS₂E`: negative `S₃`-coordinate of `K`
  obtain ⟨n, nK, n2, nE, hn⟩ := h.facet_KS₂E
  have n3 := hn S₃ (by simp) (by assumption) (by assumption) (by assumption)
  have n1 := hn S₁ (by simp) (by assumption) (by assumption) (by assumption)
  have en := ev1 n
  rw [nK, nE, n2] at en
  simp only [mul_zero, zero_add, add_zero] at en
  have h1B : l1B < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc n3.le, mul_neg_of_pos_of_neg h1T n1]
  -- face `KES₁`: positive `S₂`-coordinate of `K`, and convexity at `ES₁`
  obtain ⟨q, qK, qE, q1, hq⟩ := h.facet_KES₁
  have q3 := hq S₃ (by simp) (by assumption) (by assumption) (by assumption)
  have q2 := hq S₂ (by simp) (by assumption) (by assumption) (by assumption)
  have q4 := hq S₄ (by simp) (by assumption) (by assumption) (by assumption)
  have eq1 := ev1 q
  rw [qK, qE, q1] at eq1
  rw [ev2, qE, q1] at q4
  simp only [mul_zero, zero_add, add_zero] at eq1 q4
  have h1C : 0 < l1C := by
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos hc q2.le, mul_pos_of_neg_of_neg h1B q3]
  have hconv : l1B * l2C < l1C * l2B := by
    have hid : q S₃ * (l1C * l2B - l1B * l2C) = l1C * (l2B * q S₃ + l2C * q S₂) := by
      linear_combination l2C * eq1
    have hneg : q S₃ * (l1C * l2B - l1B * l2C) < 0 := by
      rw [hid]; exact mul_neg_of_pos_of_neg h1C (by linarith)
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos q3.le (show l1C * l2B - l1B * l2C ≤ 0 by linarith)]
  refine ⟨l1A, -l1B, l1C, l1T, l2B, -l2C, l2T, h1A, by linarith, h1C, h1T, h2B,
    by linarith, h2T, by linarith, by linarith,
    by linarith [show (-l1B) * (-l2C) = l1B * l2C by ring], ?_, ?_⟩
  · rw [hK]; module
  · rw [hS, h2A]; module

/-- **T5, combinatorial form.**  A capped square pyramid is Rupert unless the two
base edges `S₁S₄` and `S₂S₃` next to the capped base edge `S₁S₂` are parallel. -/
theorem isRupert_cappedSquarePyramid {E S₁ S₂ S₃ S₄ K : ℝ³}
    (h : IsCappedSquarePyramid E S₁ S₂ S₃ S₄ K)
    (hpar : ∀ k : ℝ, S₄ - S₁ ≠ k • (S₃ - S₂)) : IsRupert {E, S₁, S₂, S₃, S₄, K} := by
  obtain ⟨a₁, β₁, c₁, t₁, b₂, γ₂, t₂, ha₁, hβ₁, hc₁, ht₁, hb₂, hγ₂, ht₂, hs₁, hs₂, hconv,
    hK, hS⟩ := h.exists_normalForm
  have hne : γ₂ ≠ b₂ := by
    intro he
    apply hpar b₂
    have ht : t₂ = 1 := by linarith
    rw [hS, he, ht]; module
  have := isRupert_cappedSquarePyramid_normalForm E S₃ S₂ S₁ h.affineIndependent a₁ β₁ c₁ t₁
    b₂ γ₂ t₂ ha₁ hβ₁ hc₁ ht₁ hb₂ hγ₂ ht₂ hs₁ hs₂ hconv hne
  rw [← hK, ← hS] at this
  convert this using 1
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

end Minimality

end RupertMinimality
