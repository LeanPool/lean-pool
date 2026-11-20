/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.FewVertices

/-! # Bicapped Tetrahedron -/

@[expose] public section

namespace RupertMinimality

/-!
# Corollary 5.7: every bicapped tetrahedron is Rupert

`isRupert_bicap_normalForm` is the computational core: in barycentric
coordinates with respect to the tetrahedron `(A, B, C, T)`,
`K₁ = (a₁, -β₁, c₁, t₁)` and `K₂ = (a₂, b₂, -γ₂, t₂)` with all eight letters
positive, and convexity at the edge `AT` reads `β₁ γ₂ < c₁ b₂`.  Then
`U_ACT ≠ ∅` when `γ₂ < b₂` and `U_ABT ≠ ∅` otherwise (by the convexity
inequality, `γ₂ ≥ b₂` forces `β₁ < c₁`).

`isRupert_bicappedTetrahedron` is the combinatorial statement: the six points
have the eight facets `K₁AC, K₁CT, K₁TA, K₂AB, K₂BT, K₂TA, ABC, BCT`
(`IsFacetTriangle`: a supporting plane through the three points with the
other points strictly on one side).  It reduces to the normal form by
reading the barycentric signs off the facet inequalities.  Numerically, 49/49
random normal-form samples satisfy all eight facet conditions, and 300 samples
agree with the `U_ACT`/`U_ABT` criterion.
-/

namespace Minimality

/-- `P Q R` lies on a facet of `conv V`: an affine functional vanishes at
`P`, `Q`, `R` and is negative at every other point of `V`. -/
def IsFacetTriangle (V : Finset ℝ³) (P Q R : ℝ³) : Prop :=
  ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f P = 0 ∧ f Q = 0 ∧ f R = 0 ∧
    ∀ x ∈ V, x ≠ P → x ≠ Q → x ≠ R → f x < 0

/-- The six points form a bicapped tetrahedron with caps `K₁` (over the
face `ACT` of `ABCT`) and `K₂` (over `ABT`). -/
structure IsBicappedTetrahedron (A B C T K₁ K₂ : ℝ³) : Prop where
  nodup : [A, B, C, T, K₁, K₂].Nodup
  affineIndependent : AffineIndependent ℝ ![A, B, C, T]
  facet_K₁AC : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ A C
  facet_K₁CT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ C T
  facet_K₁TA : IsFacetTriangle {A, B, C, T, K₁, K₂} K₁ T A
  facet_K₂AB : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ A B
  facet_K₂BT : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ B T
  facet_K₂TA : IsFacetTriangle {A, B, C, T, K₁, K₂} K₂ T A
  facet_ABC : IsFacetTriangle {A, B, C, T, K₁, K₂} A B C
  facet_BCT : IsFacetTriangle {A, B, C, T, K₁, K₂} B C T


open scoped RealInnerProductSpace

/-- Four affinely independent points are not coplanar. -/
theorem not_coplanar_of_affineIndependent {a b c d : ℝ³}
    (h : AffineIndependent ℝ ![a, b, c, d]) : ¬ Coplanar ℝ ({a, b, c, d} : Set ℝ³) := by
  intro hc
  have h3 := h.finrank_vectorSpan (n := 3) (by simp)
  have hr : Set.range ![a, b, c, d] = ({a, b, c, d} : Set ℝ³) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rw [hr] at h3
  have := hc
  unfold Coplanar at this
  rw [← Module.finrank_eq_rank, h3] at this
  norm_num at this

/-- Weights on a three-point `Finset`. -/
theorem exists_weights3 {A Q T v u : ℝ³} (hAQ : A ≠ Q) (hAT : A ≠ T) (hQT : Q ≠ T)
    {t α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (h1 : α + β + γ = 1)
    (h : v + t • u = α • A + β • Q + γ • T) :
    ∃ t' : ℝ, ∃ μ : ℝ³ → ℝ, (∀ w ∈ ({A, Q, T} : Finset ℝ³), 0 < μ w) ∧
      ∑ w ∈ ({A, Q, T} : Finset ℝ³), μ w = 1 ∧
      v + t' • u = ∑ w ∈ ({A, Q, T} : Finset ℝ³), μ w • w := by
  classical
  refine ⟨t, fun w => if w = A then α else if w = Q then β else γ, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [hAQ.symm, hAT.symm, hQT.symm, *]
  · rw [Finset.sum_insert (by simp [hAQ, hAT]), Finset.sum_insert (by simp [hQT]),
      Finset.sum_singleton]
    simp [hAQ.symm, hAT.symm, hQT.symm, ← h1, add_assoc]
  · rw [Finset.sum_insert (by simp [hAQ, hAT]), Finset.sum_insert (by simp [hQT]),
      Finset.sum_singleton, h]
    simp [hAQ.symm, hAT.symm, hQT.symm, add_assoc]

/-- **Cor. 5.7, one admissible plane.**  `W = {A, Q, T}`, apex `P`,
`K = (a, -β, q, t)` and `L = (a', p', -γ', t')` in barycentrics with respect
to `(A, P, Q, T)`; if `βγ' < qp'` and `γ' < p'`, the plane `AQT` has an
admissible view `X - P`. -/
theorem isRupert_bicap_case (A P Q T : ℝ³) (hind : AffineIndependent ℝ ![A, P, Q, T])
    (a β q t a' p' γ' t' : ℝ) (ha : 0 < a) (hβ : 0 < β) (_hq : 0 < q) (ht : 0 < t)
    (ha' : 0 ≤ a') (hp' : 0 < p') (hγ' : 0 < γ') (ht' : 0 < t')
    (hs : a - β + q + t = 1) (hs' : a' + p' - γ' + t' = 1)
    (hconv : β * γ' < q * p') (hcase : γ' < p') :
    IsRupert {A, P, Q, T, a • A - β • P + q • Q + t • T, a' • A + p' • P - γ' • Q + t' • T} := by
  classical
  have hinj := hind.injective
  have hAQ : A ≠ Q := fun h => by have := @hinj 0 2 (by simp [h]); exact absurd this (by decide)
  have hAT : A ≠ T := fun h => by have := @hinj 0 3 (by simp [h]); exact absurd this (by decide)
  have hQT : Q ≠ T := fun h => by have := @hinj 2 3 (by simp [h]); exact absurd this (by decide)
  have hnc := not_coplanar_of_affineIndependent hind
  have hdet : det4 A Q T P ≠ 0 := fun h0 => hnc ((coplanar_of_det4_eq_zero h0).subset
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  set N := cross (Q - A) (T - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hdet (by simp [det4, ← hNdef, h0])
  have hindW : AffineIndependent ℝ ![A, Q, T] := affineIndependent_of_cross_ne_zero hN
  have hNQ : ⟪N, Q⟫ = c := by
    have := inner_cross_left (Q - A) (T - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hNT : ⟪N, T⟫ = c := by
    have := inner_cross_right (Q - A) (T - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({A, Q, T} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNQ
    · exact hNT
  -- choice of the crossing point `X = xA A + xQ Q + xT T`
  set Lo := max (γ' / p') ((q - 1) / β)
  set Up := min (q / β) 1
  have hLU : Lo < Up := by
    refine max_lt (lt_min ?_ ?_) (lt_min ?_ ?_)
    · rw [div_lt_div_iff₀ hp' hβ]; linarith
    · rw [div_lt_one hp']; exact hcase
    · rw [div_lt_div_iff_of_pos_right hβ]; linarith
    · rw [div_lt_one hβ]; linarith
  set xQ := (Lo + Up) / 2
  have hxQ1 : Lo < xQ := by simp only [xQ]; linarith
  have hxQ2 : xQ < Up := by simp only [xQ]; linarith
  have hi : γ' < p' * xQ := by
    have := (le_max_left _ _).trans_lt hxQ1; rw [div_lt_iff₀ hp'] at this; linarith
  have hii : β * xQ < q := by
    have := hxQ2.trans_le (min_le_left _ _); rw [lt_div_iff₀ hβ] at this; linarith
  have hiii : xQ < 1 := hxQ2.trans_le (min_le_right _ _)
  have hiv : q - 1 < β * xQ := by
    have := (le_max_right _ _).trans_lt hxQ1; rw [div_lt_iff₀ hβ] at this; linarith
  have hxQpos : 0 < xQ := by
    have : 0 < γ' / p' := by positivity
    exact this.trans_le (le_max_left _ _) |>.trans hxQ1
  set r := 1 - xQ
  have hr : 0 < r := by simp only [r]; linarith
  have hat : 0 < a + t := by positivity
  have hβr : β * r < a + t := by simp only [r]; linarith
  set xA := r * a / (a + t)
  set xT := r * t / (a + t)
  have hxA : 0 < xA := by positivity
  have hxT : 0 < xT := by positivity
  have hsumx : xA + xQ + xT = 1 := by
    simp only [xA, xT, r]; field_simp; ring
  have hβxA : β * xA < a := by
    simp only [xA]; rw [mul_div_assoc', div_lt_iff₀ hat]; nlinarith
  have hβxT : β * xT < t := by
    simp only [xT]; rw [mul_div_assoc', div_lt_iff₀ hat]; nlinarith
  set X := xA • A + xQ • Q + xT • T
  have hNX : ⟪N, X⟫ = c := by
    simp only [X, inner_add_right, real_inner_smul_right, hNQ, hNT, ← hc]
    linear_combination c * hsumx
  have hu₀ : ⟪N, X - P⟫ ≠ 0 := by
    rw [inner_sub_right, hNX]
    intro h0
    apply hdet
    simp only [det4, ← hNdef, inner_sub_right]
    linarith
  refine isRupert_of_crossing _ {A, Q, T} (by intro x hx; simp at hx ⊢; tauto) N c hWN
    (by simp) (by simp) (by simp) hindW (X - P) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact exists_weights3 hAQ hAT hQT hxA hxQpos hxT hsumx (t := 1) (by simp [X])
  · exact absurd rfl hvW.2.1
  · exact absurd rfl hvW.2.2
  · refine exists_weights3 hAQ hAT hQT (t := -β) (α := a - β * xA) (β := q - β * xQ)
      (γ := t - β * xT) (by linarith) (by linarith) (by linarith)
      (by linear_combination hs - β * hsumx) ?_
    simp only [X]; module
  · refine exists_weights3 hAQ hAT hQT (t := p') (α := a' + p' * xA) (β := p' * xQ - γ')
      (γ := t' + p' * xT) (by positivity) (by linarith) (by positivity)
      (by linear_combination hs' + p' * hsumx) ?_
    simp only [X]; module

/-- Barycentric coordinates with respect to four affinely independent points. -/
theorem exists_bary {A B C T : ℝ³} (hind : AffineIndependent ℝ ![A, B, C, T]) (K : ℝ³) :
    ∃ lA lB lC lT : ℝ, lA + lB + lC + lT = 1 ∧ K = lA • A + lB • B + lC • C + lT • T := by
  have hspan : affineSpan ℝ (Set.range ![A, B, C, T]) = ⊤ :=
    (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp)
  obtain ⟨w, hw, hK⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    (show K ∈ affineSpan ℝ (Set.range ![A, B, C, T]) by rw [hspan]; trivial)
  rw [Finset.univ.affineCombination_eq_linear_combination _ _ hw, Fin.sum_univ_four] at hK
  rw [Fin.sum_univ_four] at hw
  exact ⟨w 0, w 1, w 2, w 3, hw, by simpa using hK⟩

/-- An affine functional on an affine combination of four points. -/
theorem affine_apply_comb4 (f : ℝ³ →ᵃ[ℝ] ℝ) {A B C T : ℝ³} {lA lB lC lT : ℝ}
    (h1 : lA + lB + lC + lT = 1) :
    f (lA • A + lB • B + lC • C + lT • T) = lA * f A + lB * f B + lC * f C + lT * f T := by
  have hf : ∀ x, f x = f.linear x + f 0 := fun x => by
    have := f.map_vadd 0 x
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  rw [hf, hf A, hf B, hf C, hf T]
  simp only [map_add, map_smul, smul_eq_mul]
  linear_combination (-(f 0)) * h1

/-- **Corollary 5.7, normal form.** -/
theorem isRupert_bicap_normalForm (A B C T : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (ha₂ : 0 < a₂) (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : a₂ + b₂ - γ₂ + t₂ = 1)
    (hAT : β₁ * γ₂ < c₁ * b₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T,
      a₂ • A + b₂ • B - γ₂ • C + t₂ • T} := by
  by_cases hy : γ₂ < b₂
  · exact isRupert_bicap_case A B C T hind a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ ha₁ hβ₁ hc₁ ht₁ ha₂.le hb₂
      hγ₂ ht₂ hsum₁ hsum₂ hAT hy
  · push Not at hy
    have hx : β₁ < c₁ := by
      by_contra hx; push Not at hx
      have := mul_le_mul hx hy hb₂.le hβ₁.le
      linarith
    have hind' : AffineIndependent ℝ ![A, C, B, T] := by
      have := hind.comp_embedding (Equiv.swap (1 : Fin 4) 2).toEmbedding
      convert this using 1
      funext i; fin_cases i <;> rfl
    have h := isRupert_bicap_case A C B T hind' a₂ γ₂ b₂ t₂ a₁ c₁ β₁ t₁ ha₂ hγ₂ hb₂ ht₂ ha₁.le hc₁
      hβ₁ ht₁ (by linarith) (by linarith) (by linarith) hx
    have e1 : a₂ • A - γ₂ • C + b₂ • B + t₂ • T = a₂ • A + b₂ • B - γ₂ • C + t₂ • T := by module
    have e2 : a₁ • A + c₁ • C - β₁ • B + t₁ • T = a₁ • A - β₁ • B + c₁ • C + t₁ • T := by module
    rw [e1, e2] at h
    convert h using 1
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- The facet conditions put a bicapped tetrahedron in normal form. -/
theorem IsBicappedTetrahedron.exists_normalForm {A B C T K₁ K₂ : ℝ³}
    (h : IsBicappedTetrahedron A B C T K₁ K₂) :
    ∃ a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂ : ℝ, 0 < a₁ ∧ 0 < β₁ ∧ 0 < c₁ ∧ 0 < t₁ ∧
      0 < a₂ ∧ 0 < b₂ ∧ 0 < γ₂ ∧ 0 < t₂ ∧
      a₁ - β₁ + c₁ + t₁ = 1 ∧ a₂ + b₂ - γ₂ + t₂ = 1 ∧ β₁ * γ₂ < c₁ * b₂ ∧
      K₁ = a₁ • A - β₁ • B + c₁ • C + t₁ • T ∧ K₂ = a₂ • A + b₂ • B - γ₂ • C + t₂ • T := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hAB, hAC, hAT, hAK₁, hAK₂⟩, ⟨hBC, hBT, hBK₁, hBK₂⟩, ⟨hCT, hCK₁, hCK₂⟩,
    ⟨hTK₁, hTK₂⟩, hK₁K₂, -⟩ := hnd
  obtain ⟨l1A, l1B, l1C, l1T, hs1, hK₁⟩ := exists_bary h.affineIndependent K₁
  obtain ⟨l2A, l2B, l2C, l2T, hs2, hK₂⟩ := exists_bary h.affineIndependent K₂
  have ev1 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK₁ ▸ affine_apply_comb4 f hs1 :
    f K₁ = l1A * f A + l1B * f B + l1C * f C + l1T * f T)
  have ev2 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hK₂ ▸ affine_apply_comb4 f hs2 :
    f K₂ = l2A * f A + l2B * f B + l2C * f C + l2T * f T)
  -- face BCT: positive `A`-coordinates
  obtain ⟨f, fB, fC, fT, hf⟩ := h.facet_BCT
  have fA := hf A (by simp) hAB hAC hAT
  have fK₁ := hf K₁ (by simp) (Ne.symm hBK₁) (Ne.symm hCK₁) (Ne.symm hTK₁)
  have fK₂ := hf K₂ (by simp) (Ne.symm hBK₂) (Ne.symm hCK₂) (Ne.symm hTK₂)
  rw [ev1, fB, fC, fT] at fK₁
  rw [ev2, fB, fC, fT] at fK₂
  simp only [mul_zero, add_zero] at fK₁ fK₂
  have h1A : 0 < l1A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fA.le]
  have h2A : 0 < l2A := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc fA.le]
  -- face ABC: positive `T`-coordinates
  obtain ⟨g, gA, gB, gC, hg⟩ := h.facet_ABC
  have gT := hg T (by simp) (Ne.symm hAT) (Ne.symm hBT) (Ne.symm hCT)
  have gK₁ := hg K₁ (by simp) (Ne.symm hAK₁) (Ne.symm hBK₁) (Ne.symm hCK₁)
  have gK₂ := hg K₂ (by simp) (Ne.symm hAK₂) (Ne.symm hBK₂) (Ne.symm hCK₂)
  rw [ev1, gA, gB, gC] at gK₁
  rw [ev2, gA, gB, gC] at gK₂
  simp only [mul_zero, zero_add] at gK₁ gK₂
  have h1T : 0 < l1T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc gT.le]
  have h2T : 0 < l2T := by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc gT.le]
  -- face K₁AC: negative `B`-coordinate of `K₁`
  obtain ⟨hh, hhK, hhA, hhC, hhx⟩ := h.facet_K₁AC
  have hhB := hhx B (by simp) hBK₁ (Ne.symm hAB) hBC
  have hhT := hhx T (by simp) hTK₁ (Ne.symm hAT) (Ne.symm hCT)
  have e := ev1 hh
  rw [hhK, hhA, hhC] at e
  simp only [mul_zero, zero_add, add_zero] at e
  have h1B : l1B < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc hhB.le, mul_neg_of_pos_of_neg h1T hhT]
  -- face K₁TA: positive `C`-coordinate of `K₁`, and convexity at `AT`
  obtain ⟨k, kK, kT, kA, hk⟩ := h.facet_K₁TA
  have kB := hk B (by simp) hBK₁ hBT (Ne.symm hAB)
  have kC := hk C (by simp) hCK₁ hCT (Ne.symm hAC)
  have kK₂ := hk K₂ (by simp) (Ne.symm hK₁K₂) (Ne.symm hTK₂) (Ne.symm hAK₂)
  have e1 := ev1 k
  rw [kK, kT, kA] at e1
  rw [ev2, kT, kA] at kK₂
  simp only [mul_zero, zero_add, add_zero] at e1 kK₂
  have h1C : 0 < l1C := by
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos hc kC.le, mul_pos_of_neg_of_neg h1B kB]
  -- face K₂AB: negative `C`-coordinate of `K₂`
  obtain ⟨m, mK, mA, mB, hm⟩ := h.facet_K₂AB
  have mC := hm C (by simp) hCK₂ (Ne.symm hAC) (Ne.symm hBC)
  have mT := hm T (by simp) hTK₂ (Ne.symm hAT) (Ne.symm hBT)
  have e2 := ev2 m
  rw [mK, mA, mB] at e2
  simp only [mul_zero, zero_add, add_zero] at e2
  have h2C : l2C < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc mC.le, mul_neg_of_pos_of_neg h2T mT]
  -- face K₂TA: positive `B`-coordinate of `K₂`
  obtain ⟨n, nK, nT, nA, hn⟩ := h.facet_K₂TA
  have nB := hn B (by simp) hBK₂ hBT (Ne.symm hAB)
  have nC := hn C (by simp) hCK₂ hCT (Ne.symm hAC)
  have e3 := ev2 n
  rw [nK, nT, nA] at e3
  simp only [mul_zero, zero_add, add_zero] at e3
  have h2B : 0 < l2B := by
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos hc nB.le, mul_pos_of_neg_of_neg h2C nC]
  have hconv : l1B * l2C < l1C * l2B := by
    have hid : k B * (l1C * l2B - l1B * l2C) = l1C * (l2B * k B + l2C * k C) := by
      linear_combination l2C * e1
    have hneg : k B * (l1C * l2B - l1B * l2C) < 0 := by
      rw [hid]; exact mul_neg_of_pos_of_neg h1C (by linarith)
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos kB.le (show l1C * l2B - l1B * l2C ≤ 0 by linarith)]
  refine ⟨l1A, -l1B, l1C, l1T, l2A, l2B, -l2C, l2T, h1A, by linarith, h1C, h1T, h2A, h2B,
    by linarith, h2T, by linarith, by linarith,
    by linarith [show (-l1B) * (-l2C) = l1B * l2C by ring], ?_, ?_⟩
  · rw [hK₁]; module
  · rw [hK₂]; module

/-- **Corollary 5.7.** Every bicapped tetrahedron is Rupert. -/
theorem isRupert_bicappedTetrahedron {A B C T K₁ K₂ : ℝ³}
    (h : IsBicappedTetrahedron A B C T K₁ K₂) : IsRupert {A, B, C, T, K₁, K₂} := by
  obtain ⟨a₁, β₁, c₁, t₁, a₂, b₂, γ₂, t₂, ha₁, hβ₁, hc₁, ht₁, ha₂, hb₂, hγ₂, ht₂,
    hs₁, hs₂, hAT, rfl, rfl⟩ := h.exists_normalForm
  exact isRupert_bicap_normalForm A B C T h.affineIndependent a₁ β₁ c₁ t₁ a₂ b₂ γ₂ t₂
    ha₁ hβ₁ hc₁ ht₁ ha₂ hb₂ hγ₂ ht₂ hs₁ hs₂ hAT

end Minimality

end RupertMinimality
