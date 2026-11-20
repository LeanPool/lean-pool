/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Oct9Gale

/-! # Oct9 Weak -/

@[expose] public section

namespace RupertMinimality

/-!
# Weak quad edges (§9.6 of L9: Lemma 9.11)

When `f = 0`, the edge views chosen in §9.5 are *weak* quad edges: the face
`x' y' p'` at the antipodal edge contains the view direction `u = y - x`.
This file proves Lemma 9.11 for such an edge: it gives a passage unless it is
touching or its lateral edge `p y'` is parallel to the normal of the two
parallel faces.

Tools: Lemma 8.0 / Corollary 8.0′ with either orientation of the shadow
(`isRupert_of_tilted_unimodal_σ`, by reversing the cycle), the unimodality of
the two 5-cycles of Lemma 9.11, and a four-vector identity for the tilt tests.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `TiltSign` for the orientation `σ` (`σ = 1`: counterclockwise). -/
def TiltSignS (σ : ℝ) (a b u₀ v : ℝ³) : Prop :=
  0 < σ * det3 a b u₀ ∨ (det3 a b u₀ = 0 ∧ 0 < σ * det3 a b v)

theorem det3_rev_edge (A B W u : ℝ³) :
    det3 (A - B) (W - B) u = -det3 (B - A) (W - A) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem IsCyclicUnimodal.of_neg {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (h : IsCyclicUnimodal fun i => z (-i)) : IsCyclicUnimodal z := by
  classical
  obtain ⟨hinj, hcard⟩ := h
  refine ⟨fun i j hij => ?_, ?_⟩
  · have := @hinj (-i) (-j) (by simp only [neg_neg]; exact hij)
    simpa using this
  · rw [← hcard]
    refine Finset.card_bij (fun i _ => -i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      refine ⟨?_, ?_⟩
      · have e : -(-i - 1) = i + 1 := by ring
        rw [e, neg_neg]; exact hi.2
      · have e : -(-i + 1) = i - 1 := by ring
        rw [e, neg_neg]; exact hi.1
    · intro i _ j _ hij; simpa using hij
    · intro j hj
      refine ⟨-j, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨?_, ?_⟩
      · have e : -j - 1 = -(j + 1) := by ring
        rw [e]; exact hj.2
      · have e : -j + 1 = -(j - 1) := by ring
        rw [e]; exact hj.1

/-- **Corollary 8.0′ in either orientation** (with eventual `Q`). -/
theorem isRupert_of_tilted_unimodal_σ (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSignS σ (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → Q z → Q (fun i => c * z i))
    (hQe : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q fun i => ⟪x i, u₀ + ε • v⟫)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) : IsRupert V := by
  rcases hσ with rfl | rfl
  · refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk x hxV ?_ ?_ Q hQo hQs hQe hQu
    · intro i j hi hj; simpa [TiltSignS, TiltSign] using hcyc i j hi hj
    · intro y hy hyx i; simpa [TiltSignS, TiltSign] using hrest y hy hyx i
  · have key : ∀ i : ZMod k, ∀ w : ℝ³, ∀ u : ℝ³,
        det3 (x (-(i + 1)) - x (-i)) (w - x (-i)) u =
          -det3 (x (-(i + 1) + 1) - x (-(i + 1))) (w - x (-(i + 1))) u := by
      intro i w u
      have e : -(i + 1) + 1 = -i := by ring
      rw [e, det3_rev_edge]
    refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk (fun i => x (-i)) (fun i => hxV _) ?_ ?_
      (fun z => Q fun i => z (-i)) ?_ ?_ ?_ ?_
    · intro i j hi hj
      have h1 : -j ≠ -(i + 1) := by intro h; apply hj; simpa using congrArg Neg.neg h
      have h2 : -j ≠ -(i + 1) + 1 := by
        intro h; apply hi
        have : -(i + 1) + 1 = -i := by ring
        rw [this] at h; simpa using congrArg Neg.neg h
      have t := hcyc (-(i + 1)) (-j) h1 h2
      simp only [TiltSignS, neg_one_mul, neg_pos] at t
      simp only [TiltSign]
      rw [show i + 1 = i + 1 from rfl, key i (x (-j)) u₀, key i (x (-j)) v]
      rcases t with t | ⟨t0, t1⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [t0, neg_zero], by linarith⟩
    · intro y hy hyx i
      have t := hrest y hy (fun j h => hyx (-j) (by simpa using h)) (-(i + 1))
      simp only [TiltSignS, neg_one_mul, neg_pos] at t
      simp only [TiltSign]
      rw [key i y u₀, key i y v]
      rcases t with t | ⟨t0, t1⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [t0, neg_zero], by linarith⟩
    · have hc : Continuous fun z : ZMod k → ℝ => fun i => z (-i) := by fun_prop
      exact hQo.preimage hc
    · intro z c hc hz; exact hQs _ c hc hz
    · simpa using hQe
    · intro z hz hQ
      have hinj : Function.Injective fun i => z (-i) := fun i j hij => by
        simpa using hz hij
      exact IsCyclicUnimodal.of_neg (hQu _ hinj hQ)

theorem isCyclicUnimodal_of_unique {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (m : ZMod k) (hm : z (m - 1) < z m ∧ z (m + 1) < z m)
    (ho : ∀ i, i ≠ m → ¬(z (i - 1) < z i ∧ z (i + 1) < z i)) : IsCyclicUnimodal z := by
  classical
  refine ⟨hinj, Finset.card_eq_one.mpr ⟨m, ?_⟩⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi; by_contra hne; exact ho i hne hi
  · rintro rfl; exact hm

theorem zmod5_table (i : ZMod 5) :
    (i = 0 ∧ i - 1 = 4 ∧ i + 1 = 1) ∨ (i = 1 ∧ i - 1 = 0 ∧ i + 1 = 2) ∨
    (i = 2 ∧ i - 1 = 1 ∧ i + 1 = 3) ∨ (i = 3 ∧ i - 1 = 2 ∧ i + 1 = 4) ∨
    (i = 4 ∧ i - 1 = 3 ∧ i + 1 = 0) := by
  revert i; decide

/-- The 5-cycle `(x, p, y', x', p')` of Lemma 9.11 (`b < c`, `e < d`, `a < max(b, e)`). -/
def WQ5a (z : ZMod 5 → ℝ) : Prop := z 1 < z 2 ∧ z 4 < z 3 ∧ (z 0 < z 1 ∨ z 0 < z 4)

/-- The 5-cycle `(x, y, p, y', p')` of Lemma 9.11 (the tie with `ω < t₂`). -/
def WQ5b (z : ZMod 5 → ℝ) : Prop := z 0 < z 1 ∧ z 2 < z 1 ∧ z 3 < z 2 ∧ z 4 < z 3

theorem isOpen_WQ5a : IsOpen {z : ZMod 5 → ℝ | WQ5a z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [WQ5a, Set.ofPred_and, Set.ofPred_or]
  exact (hlt 1 2).inter ((hlt 4 3).inter ((hlt 0 1).union (hlt 0 4)))

theorem isOpen_WQ5b : IsOpen {z : ZMod 5 → ℝ | WQ5b z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [WQ5b, Set.ofPred_and]
  exact (hlt 0 1).inter ((hlt 2 1).inter ((hlt 3 2).inter (hlt 4 3)))

theorem WQ5a.mul {z : ZMod 5 → ℝ} (h : WQ5a z) {c : ℝ} (hc : 0 < c) : WQ5a fun i => c * z i := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp only; nlinarith, by simp only; nlinarith, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl (by simp only; nlinarith)
  · exact Or.inr (by simp only; nlinarith)

theorem WQ5b.mul {z : ZMod 5 → ℝ} (h : WQ5b z) {c : ℝ} (hc : 0 < c) : WQ5b fun i => c * z i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simp only; nlinarith, by simp only; nlinarith, by simp only; nlinarith,
    by simp only; nlinarith⟩

theorem WQ5a.unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : WQ5a z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3⟩ := h
  have h23 : z 2 ≠ z 3 := hinj.ne (by decide)
  rcases lt_or_gt_of_ne h23 with h23 | h23
  · refine isCyclicUnimodal_of_unique hinj 3 ⟨?_, ?_⟩ ?_
    · rw [show (3 - 1 : ZMod 5) = 2 from by decide]
      exact h23
    · rw [show (3 + 1 : ZMod 5) = 4 from by decide]
      exact h2
    intro i hi hc
    rcases zmod5_table i with ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ |
      ⟨rfl, e1, e2⟩ <;> rw [e1, e2] at hc
    · rcases h3 with h3 | h3 <;> linarith [hc.1, hc.2]
    · linarith [hc.2]
    · linarith [hc.2]
    · exact hi rfl
    · linarith [hc.1]
  · refine isCyclicUnimodal_of_unique hinj 2 ⟨?_, ?_⟩ ?_
    · rw [show (2 - 1 : ZMod 5) = 1 from by decide]
      exact h1
    · rw [show (2 + 1 : ZMod 5) = 3 from by decide]
      exact h23
    intro i hi hc
    rcases zmod5_table i with ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ |
      ⟨rfl, e1, e2⟩ <;> rw [e1, e2] at hc
    · rcases h3 with h3 | h3 <;> linarith [hc.1, hc.2]
    · linarith [hc.2]
    · exact hi rfl
    · linarith [hc.1]
    · linarith [hc.1]

theorem WQ5b.unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : WQ5b z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine isCyclicUnimodal_of_unique hinj 1 ⟨?_, ?_⟩ ?_
  · rw [show (1 - 1 : ZMod 5) = 0 from by decide]
    exact h1
  · rw [show (1 + 1 : ZMod 5) = 2 from by decide]
    exact h2
  intro i hi hc
  rcases zmod5_table i with ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ |
    ⟨rfl, e1, e2⟩ <;> rw [e1, e2] at hc
  · linarith [hc.2]
  · exact hi rfl
  · linarith [hc.1]
  · linarith [hc.1]
  · linarith [hc.1]

/-- **The four-vector identity** behind the tilt tests in a face: if `e`, `w`
and `u` are coplanar and `⟪N, e⟫ = 0`, then
`⟪N, u⟫ * det3 e w v = ⟪N, w⟫ * det3 e u v`. -/
theorem det3_four (N e w u v : ℝ³) :
    ⟪N, u⟫ * det3 e w v = ⟪N, w⟫ * det3 e u v + det3 e w u * ⟪N, v⟫ - det3 w u v * ⟪N, e⟫ := by
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]; ring

/-- `det3_pos_of_combo` with an orientation factor `σ`. -/
theorem det3_pos_of_combo_σ {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³} {σ : ℝ}
    (hr : 0 < σ * det3 (Q - P) (r - P) u) (hgr : α * f₁ r + β * f₂ r < 0)
    (hgw : α * f₁ w + β * f₂ w < 0) : 0 < σ * det3 (Q - P) (w - P) u := by
  set N := α • N₁ + β • N₂
  have hg : ∀ z, ⟪N, z - P⟫ = α * f₁ z + β * f₂ z := by
    intro z
    simp only [N, inner_add_left, real_inner_smul_left, ← h₁, ← h₂, h1P, h2P, sub_zero]
  have hNe : ⟪N, Q - P⟫ = 0 := by rw [hg, h1Q, h2Q]; ring
  have hNu : ⟪N, u⟫ = 0 := by
    simp only [N, inner_add_left, real_inner_smul_left]; linarith
  have key := det3_mul_inner_eq (w := w - P) (w' := r - P) hNe hNu
  rw [hg, hg] at key
  have key' : (σ * det3 (Q - P) (w - P) u) * (α * f₁ r + β * f₂ r) =
      (σ * det3 (Q - P) (r - P) u) * (α * f₁ w + β * f₂ w) := by
    rw [mul_assoc, key]; ring
  nlinarith

/-- A facet `G` through `P`, `Q`, `R` containing the view direction `u`. -/
theorem vert_face_pos_σ {V : Finset ℝ³} {P Q R : ℝ³} (G : FacetFn V P Q R) {u : ℝ³}
    (hu : ⟪G.N, u⟫ = 0) {σ : ℝ} {r w : ℝ³}
    (hr : r ∈ V) (hrP : r ≠ P) (hrQ : r ≠ Q) (hrR : r ≠ R) (hw : w ∈ V) (hwP : w ≠ P)
    (hwQ : w ≠ Q) (hwR : w ≠ R) (href : 0 < σ * det3 (Q - P) (r - P) u) :
    0 < σ * det3 (Q - P) (w - P) u :=
  det3_pos_of_combo_σ G.hN G.hN G.hP G.hQ G.hP G.hQ (α := 1) (β := 0) (by rw [hu]; ring) href
    (by have := G.neg r hr hrP hrQ hrR; linarith) (by have := G.neg w hw hwP hwQ hwR; linarith)

/-- A far edge `PQ` between a lower facet `x Q P` and an upper facet `x' Q P`. -/
theorem far_edge_pos_σ {V : Finset ℝ³} {x x' y P Q : ℝ³} (G : FacetFn V x Q P)
    (H : FacetFn V x' Q P) (hx : x ∈ V) (hx' : x' ∈ V) (hxx' : x ≠ x') (hxP : x ≠ P)
    (hxQ : x ≠ Q) (hx'P : x' ≠ P) (hx'Q : x' ≠ Q) (hGy : G.f y < 0) (hq : H.f x < H.f y)
    {σ : ℝ} {r w : ℝ³} (hr : r ∈ V) (hrP : r ≠ P) (hrQ : r ≠ Q) (hw : w ∈ V) (hwP : w ≠ P)
    (hwQ : w ≠ Q) (href : 0 < σ * det3 (Q - P) (r - P) (y - x)) :
    0 < σ * det3 (Q - P) (w - P) (y - x) := by
  have key : ∀ z ∈ V, z ≠ P → z ≠ Q →
      (H.f y - H.f x) * G.f z + (-(G.f y - G.f x)) * H.f z < 0 := by
    intro z hz hzP hzQ
    have hα : 0 < H.f y - H.f x := by linarith
    have hβ : 0 < -(G.f y - G.f x) := by rw [G.hP]; linarith
    by_cases hzx : z = x
    · subst hzx; rw [G.hP]; nlinarith [H.neg z hz hxx' hzQ hzP]
    by_cases hzx' : z = x'
    · subst hzx'; rw [H.hP]; nlinarith [G.neg z hz (Ne.symm hxx') hzQ hzP]
    nlinarith [G.neg z hz hzx hzQ hzP, H.neg z hz hzx' hzQ hzP]
  refine det3_pos_of_combo_σ G.hN H.hN G.hR G.hQ H.hR H.hQ ?_ href (key r hr hrP hrQ)
    (key w hw hwP hwQ)
  rw [← G.hN, ← H.hN]; ring

/-- The determinant tests at the edge view of a *weak* quad edge `x → y`
(the face `x' y' p'` contains `u = y - x`), with orientation `σ`. -/
theorem weak_edge_tests {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y) {σ : ℝ}
    (hor : 0 < σ * det3 (p - y) (p' - y) (y - x)) :
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y → w ≠ p → w ≠ x →
      0 < σ * det3 (p - y) (w - y) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p → w ≠ y' →
      0 < σ * det3 (y' - p) (w - p) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y' → w ≠ p' → w ≠ x' →
      0 < σ * det3 (p' - y') (w - y') (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p' → w ≠ y → w ≠ x →
      0 < σ * det3 (y - p') (w - p') (y - x)) := by
  set V : Finset ℝ³ := {x, x', y, y', p, p'}
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have hBu : ⟪F.abc.N, y - x⟫ = 0 := by rw [← F.abc.hN, F.abc.hP, F.abc.hQ]; ring
  have hB'u : ⟪F.abc'.N, y - x⟫ = 0 := by rw [← F.abc'.hN, F.abc'.hP, F.abc'.hQ]; ring
  have hTu : ⟪F.a'b'c'.N, y - x⟫ = 0 := by rw [← F.a'b'c'.hN, hT]; ring
  have E1 : ∀ w ∈ V, w ≠ y → w ≠ p → w ≠ x → 0 < σ * det3 (p - y) (w - y) (y - x) :=
    fun w hw hwy hwp hwx => vert_face_pos_σ F.abc.p12.p23 hBu mp' (Ne.symm hyp')
      (Ne.symm hpp') (Ne.symm hxp') hw hwy hwp hwx hor
  have E2 : ∀ w ∈ V, w ≠ p → w ≠ y' → 0 < σ * det3 (y' - p) (w - p) (y - x) :=
    fun w hw hwp hwy' => far_edge_pos_σ F.ab'c F.a'b'c mx mx' hxx' hxp hxy' hx'p hx'y'
      (F.ab'c.neg y my (Ne.symm hxy) hyy' hyp) hq₁ my hyp hyy' hw hwp hwy'
      (by rw [det3_cyc y p y']; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy'))
  have E3 : ∀ w ∈ V, w ≠ y' → w ≠ p' → w ≠ x' → 0 < σ * det3 (p' - y') (w - y') (y - x) :=
    fun w hw hwy' hwp' hwx' => vert_face_pos_σ F.a'b'c'.p12.p23 hTu mp (Ne.symm hy'p) hpp'
      (Ne.symm hx'p) hw hwy' hwp' hwx'
      (by rw [det3_cyc p y' p']; exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p'))
  have E4 : ∀ w ∈ V, w ≠ p' → w ≠ y → w ≠ x → 0 < σ * det3 (y - p') (w - p') (y - x) :=
    fun w hw hwp' hwy hwx => vert_face_pos_σ F.abc'.p23.p12.p23 hB'u mp hpp' (Ne.symm hyp)
      (Ne.symm hxp) hw hwp' hwy hwx (by rw [← det3_cyc p' y p]; exact hor)
  exact ⟨E1, E2, E3, E4⟩

theorem inner_four {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (A B C D : ℝ³) (c₁ c₂ c₃ c₄ : ℝ) (hs : c₁ - c₂ + c₃ - c₄ = 0) :
    ⟪N, c₁ • A - c₂ • B + c₃ • C - c₄ • D⟫ = c₁ * f A - c₂ * f B + c₃ * f C - c₄ * f D := by
  have e : ∀ t, ⟪N, t⟫ = f t - f A + ⟪N, A⟫ := fun t => by rw [hf, inner_sub_right]; ring
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
  rw [e B, e C, e D]
  linear_combination (⟪N, A⟫ - f A) * hs

/-- **The top face of a weak quad edge** (the face `x' y' p'` containing
`u = y - x`): four-point identities for an arbitrary point `w`. -/
theorem weak_top_face {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hT : F.a'b'c'.f x = F.a'b'c'.f y) (w : ℝ³) :
    det3 (x' - y') (w - y') (y - x) * (F.a'b'c.f p' * F.ab'c'.f y) =
      det3 (p' - y') (w - y') (y - x) * (-F.ab'c'.f x' * (F.a'b'c.f y - F.a'b'c.f x)) ∧
    det3 (p' - x') (w - x') (y - x) * (F.a'bc'.f y' * F.ab'c'.f y) =
      det3 (p' - y') (w - y') (y - x) * (F.ab'c'.f x' * F.a'bc'.f x) ∧
    F.ab'c'.f y * (det3 (p' - x') (w - x') (y - x) * ⟪y', y - x⟫ -
      det3 (p' - y') (w - y') (y - x) * ⟪x', y - x⟫ +
      det3 (x' - y') (w - y') (y - x) * ⟪p', y - x⟫) =
      -det3 (p' - y') (w - y') (y - x) * F.ab'c'.f x' * ⟪y - x, y - x⟫ ∧
    det3 (p' - x') (w - x') (y - x) - det3 (p' - y') (w - y') (y - x) +
      det3 (x' - y') (w - y') (y - x) = 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set u := y - x with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  set T := F.a'b'c'
  have hTx : T.f x < 0 := T.neg x (by simp) hxx' hxy' hxp'
  have hTN : T.N ≠ 0 := by
    intro h0
    have := T.hN x x'
    rw [h0, inner_zero_left, T.hP] at this
    linarith
  have hS0 : det3 (x' - y') (p' - y') u = 0 := by
    refine det3_eq_zero_of_perp hTN ?_ ?_ ?_ <;> rw [real_inner_comm, ← T.hN]
    · rw [T.hP, T.hQ]; ring
    · rw [T.hR, T.hQ]; ring
    · rw [hT]; ring
  have hpar := four_point_parallel y' x' p' w u hu
  have hsum := four_point_sum y' x' p' w u
  rw [hS0] at hpar hsum
  set S1 := det3 (p' - x') (w - x') u
  set S2 := det3 (p' - y') (w - y') u
  set S3 := det3 (x' - y') (w - y') u
  set Vv := S1 • y' - S2 • x' + S3 • p' - (0 : ℝ) • w
  set μ := ⟪Vv, u⟫ / ⟪u, u⟫
  have hs : S1 - S2 + S3 - 0 = 0 := hsum
  have app : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) →
      S1 * f y' - S2 * f x' + S3 * f p' - 0 * f w = μ * (f y - f x) := by
    intro f N hf
    rw [← inner_four hf y' x' p' w S1 S2 S3 0 hs, hf]
    change ⟪N, Vv⟫ = μ * ⟪N, u⟫
    rw [hpar, real_inner_smul_right]
  have hL := app F.ab'c'.hN
  rw [F.ab'c'.hQ, F.ab'c'.hR, F.ab'c'.hP] at hL
  have hU := app F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ] at hU
  have hH := app F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR] at hH
  have hVu : S1 * ⟪y', u⟫ - S2 * ⟪x', u⟫ + S3 * ⟪p', u⟫ = μ * ⟪u, u⟫ := by
    have := congrArg (fun z => ⟪z, u⟫) hpar
    simp only [Vv, inner_sub_left, inner_add_left, real_inner_smul_left, zero_mul,
      sub_zero] at this
    rw [this]
  refine ⟨?_, ?_, ?_, by linarith⟩
  · linear_combination F.ab'c'.f y * hU - (F.a'b'c.f y - F.a'b'c.f x) * hL
  · linear_combination F.ab'c'.f y * hH + F.a'bc'.f x * hL
  · linear_combination F.ab'c'.f y * hVu - ⟪u, u⟫ * hL

/-- Signs on the top face: the tests of the edges `y' → x'` and `x' → p'` have
the sign of the test of `y' → p'`. -/
theorem weak_top_signs {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y) {σ : ℝ} {w : ℝ³}
    (hw : 0 < σ * det3 (p' - y') (w - y') (y - x)) :
    0 < σ * det3 (x' - y') (w - y') (y - x) ∧ 0 < σ * det3 (p' - x') (w - x') (y - x) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  obtain ⟨i1, i2, -, -⟩ := weak_top_face F hT w
  have hUp' := F.a'b'c.neg p' (by simp) (Ne.symm hx'p') (Ne.symm hy'p') (Ne.symm hpp')
  have hLy := F.ab'c'.neg y (by simp) (Ne.symm hxy) hyy' hyp'
  have hLx' := F.ab'c'.neg x' (by simp) (Ne.symm hxx') hx'y' hx'p'
  have hHy' := F.a'bc'.neg y' (by simp) (Ne.symm hx'y') (Ne.symm hyy') hy'p'
  have hHx := F.a'bc'.neg x (by simp) hxx' hxy hxp'
  have p1 : 0 < F.a'b'c.f p' * F.ab'c'.f y := mul_pos_of_neg_of_neg hUp' hLy
  have p2 : 0 < -F.ab'c'.f x' * (F.a'b'c.f y - F.a'b'c.f x) := by
    apply mul_pos <;> linarith
  have p3 : 0 < F.a'bc'.f y' * F.ab'c'.f y := mul_pos_of_neg_of_neg hHy' hLy
  have p4 : 0 < F.ab'c'.f x' * F.a'bc'.f x := mul_pos_of_neg_of_neg hLx' hHx
  constructor
  · have e : (σ * det3 (x' - y') (w - y') (y - x)) * (F.a'b'c.f p' * F.ab'c'.f y) =
        (σ * det3 (p' - y') (w - y') (y - x)) * (-F.ab'c'.f x' * (F.a'b'c.f y - F.a'b'c.f x)) := by
      rw [mul_assoc, i1]; ring
    exact pos_of_mul_pos_pos (by rw [mul_comm, e]; exact mul_pos hw p2) p1 |> fun h => by
      nlinarith
  · have e : (σ * det3 (p' - x') (w - x') (y - x)) * (F.a'bc'.f y' * F.ab'c'.f y) =
        (σ * det3 (p' - y') (w - y') (y - x)) * (F.ab'c'.f x' * F.a'bc'.f x) := by
      rw [mul_assoc, i2]; ring
    nlinarith [mul_pos hw p4]

/-- Vectors parallel to the top face `x' y' p'` (which contains `u = y - x`). -/
theorem weak_top_perp {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hT : F.a'b'c'.f x = F.a'b'c'.f y) {a b : ℝ³} (ha : ⟪F.a'b'c'.N, a⟫ = 0)
    (hb : ⟪F.a'b'c'.N, b⟫ = 0) : det3 a b (y - x) = 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, -, -, -, -, -⟩ := hnd
  set T := F.a'b'c'
  have hTx : T.f x < 0 := T.neg x (by simp) hxx' hxy' hxp'
  have hTN : T.N ≠ 0 := by
    intro h0
    have := T.hN x x'
    rw [h0, inner_zero_left, T.hP] at this
    linarith
  refine det3_eq_zero_of_perp hTN ?_ ?_ ?_ <;> rw [real_inner_comm]
  · exact ha
  · exact hb
  · rw [← T.hN, hT]; ring

theorem weak_top_N {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p') :
    ⟪F.a'b'c'.N, p' - y'⟫ = 0 ∧ ⟪F.a'b'c'.N, x' - y'⟫ = 0 := by
  constructor <;> rw [← F.a'b'c'.hN]
  · rw [F.a'b'c'.hR, F.a'b'c'.hQ]; ring
  · rw [F.a'b'c'.hP, F.a'b'c'.hQ]; ring

/-- The tilt test on the top face, through the lower face `x y' p'`. -/
theorem weak_tau3 {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hT : F.a'b'c'.f x = F.a'b'c'.f y) (v : ℝ³) :
    F.ab'c'.f y * det3 (p' - y') (x' - y') v = F.ab'c'.f x' * det3 (p' - y') (y - x) v := by
  have h4 := det3_four F.ab'c'.N (p' - y') (x' - y') (y - x) v
  have e1 : ⟪F.ab'c'.N, y - x⟫ = F.ab'c'.f y := by rw [← F.ab'c'.hN, F.ab'c'.hP, sub_zero]
  have e2 : ⟪F.ab'c'.N, x' - y'⟫ = F.ab'c'.f x' := by rw [← F.ab'c'.hN, F.ab'c'.hQ, sub_zero]
  have e3 : ⟪F.ab'c'.N, p' - y'⟫ = 0 := by rw [← F.ab'c'.hN, F.ab'c'.hQ, F.ab'c'.hR, sub_zero]
  have e4 : det3 (p' - y') (x' - y') (y - x) = 0 :=
    weak_top_perp F hT (weak_top_N F).1 (weak_top_N F).2
  rw [e1, e2, e3, e4] at h4
  linarith

theorem det3_neg_mid (a b c : ℝ³) : det3 a (-b) c = -det3 a b c := by
  simp only [det3_expand, PiLp.neg_apply]; ring

theorem det3_sub_mid (a b c : ℝ³) : det3 a (a - b) c = -det3 a b c := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **Lemma 9.11, the 4-cycle `(y, p, y', p')`** (closing by `y`, lower chain on
the top face), for a tilt `v` with the three sign conditions. -/
theorem isRupert_weak_cycle4 {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hor : 0 < σ * det3 (p - y) (p' - y) (y - x)) (v : ℝ³)
    (t1 : 0 < σ * det3 (p - y) (x - y) v) (t2 : 0 < σ * det3 (y - p') (x - p') v)
    (t3 : 0 < σ * det3 (p' - y') (y - x) v)
    (hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NWS4 fun i => ⟪quad y p y' p' i, (y - x) + ε • v⟫) :
    IsRupert {x, x', y, y', p, p'} := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := weak_edge_tests F hq₁ hT hor
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set V : Finset ℝ³ := {x, x', y, y', p, p'} with hV
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have hmemV : ∀ z ∈ V, z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have t3' : 0 < σ * det3 (p' - y') (x' - y') v := by
    have e := weak_tau3 F hT v
    have hLy := F.ab'c'.neg y my (Ne.symm hxy) hyy' hyp'
    have hLx' := F.ab'c'.neg x' mx' (Ne.symm hxx') hx'y' hx'p'
    have : (σ * det3 (p' - y') (x' - y') v) * F.ab'c'.f y =
        (σ * det3 (p' - y') (y - x) v) * F.ab'c'.f x' := by
      rw [mul_assoc, mul_comm (det3 _ _ _), e]; ring
    nlinarith [mul_neg_of_pos_of_neg t3 hLx']
  have z3 : det3 (p' - y') (x' - y') (y - x) = 0 :=
    weak_top_perp F hT (weak_top_N F).1 (weak_top_N F).2
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_tilted_unimodal_σ V (y - x) v hu (by norm_num) (quad y p y' p') ?_ σ hσ
    ?_ ?_ NWS4 isOpen_NWS4 (fun z c hc hz => hz.mul hc.ne') hQ
    (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [V, quad_0, quad_1, quad_2, quad_3]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> refine Or.inl ?_
    · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
    · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    · exact E2 y my hyp hyy'
    · exact E3 y my hyy' hyp' (Ne.symm hx'y)
    · exact E3 p mp (Ne.symm hy'p) hpp' (Ne.symm hx'p)
    · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
    · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
  · intro z hz hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
    simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
    rcases hmemV z hz with h | h | h | h | h | h
    · rw [h]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact Or.inr ⟨det3_xy_zero p x y, t1⟩
      · exact Or.inl (E2 x mx hxp hxy')
      · exact Or.inl (E3 x mx hxy' hxp' hxx')
      · exact Or.inr ⟨det3_xy_zero' p' x y, t2⟩
    · rw [h]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact Or.inl (E1 x' mx' hx'y hx'p (Ne.symm hxx'))
      · exact Or.inl (E2 x' mx' hx'p hx'y')
      · exact Or.inr ⟨z3, t3'⟩
      · exact Or.inl (E4 x' mx' hx'p' hx'y (Ne.symm hxx'))
    · exact absurd h h0
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h3

theorem weak_zmod5_pairs : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
    (i = 0 ∧ (j = 2 ∨ j = 3 ∨ j = 4)) ∨ (i = 1 ∧ (j = 3 ∨ j = 4 ∨ j = 0)) ∨
    (i = 2 ∧ (j = 4 ∨ j = 0 ∨ j = 1)) ∨ (i = 3 ∧ (j = 0 ∨ j = 1 ∨ j = 2)) ∨
    (i = 4 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) := by decide

theorem det3_self_left' (a b : ℝ³) : det3 a a b = 0 := by
  simp only [det3_expand]; ring

/-- **Lemma 9.11, the 5-cycle `(x, p, y', x', p')`** (closing by `x`, upper chain
on the top face). -/
theorem isRupert_weak_cycle5a {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hor : 0 < σ * det3 (p - y) (p' - y) (y - x)) (v : ℝ³)
    (t1 : 0 < σ * det3 (p - x) (y - x) v) (t2 : 0 < σ * det3 (x - p') (y - p') v)
    (t3 : 0 < σ * det3 (x' - y') (p' - y') v)
    (hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), WQ5a fun i => ⟪quint x p y' x' p' i, (y - x) + ε • v⟫) :
    IsRupert {x, x', y, y', p, p'} := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := weak_edge_tests F hq₁ hT hor
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set V : Finset ℝ³ := {x, x', y, y', p, p'} with hV
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have hmemV : ∀ z ∈ V, z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have z3 : det3 (x' - y') (p' - y') (y - x) = 0 := by
    rw [← neg_eq_zero, ← det3_swap12]
    exact weak_top_perp F hT (weak_top_N F).1 (weak_top_N F).2
  have cyc' : ∀ w : ℝ³, det3 (p' - x') (y' - x') w = det3 (x' - y') (p' - y') w :=
    fun w => det3_cyc y' x' p' w
  have TSx := weak_top_signs F hq₁ hT (E3 x mx hxy' hxp' hxx')
  have TSp := weak_top_signs F hq₁ hT (E3 p mp (Ne.symm hy'p) hpp' (Ne.symm hx'p))
  have TSy := weak_top_signs F hq₁ hT (E3 y my hyy' hyp' (Ne.symm hx'y))
  have S1 : ∀ w ∈ V, w ≠ y → w ≠ p → w ≠ x → 0 < σ * det3 (p - x) (w - x) (y - x) :=
    fun w hw h1 h2 h3 => by rw [det3_shift_xy]; exact E1 w hw h1 h2 h3
  have S4 : ∀ w ∈ V, w ≠ p' → w ≠ y → w ≠ x → 0 < σ * det3 (x - p') (w - p') (y - x) :=
    fun w hw h1 h2 h3 => by rw [det3_shift_p']; exact E4 w hw h1 h2 h3
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  refine isRupert_of_tilted_unimodal_σ V (y - x) v hu (by norm_num) (quint x p y' x' p') ?_ σ
    hσ ?_ ?_ WQ5a isOpen_WQ5a (fun z c hc hz => hz.mul hc) hQ
    (fun z hz hQ => hQ.unimodal hz)
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i j hi hj
    rcases weak_zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
    · exact Or.inl (S1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy'))
    · exact Or.inl (S1 x' mx' hx'y hx'p (Ne.symm hxx'))
    · exact Or.inl (S1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp'))
    · exact Or.inl (E2 x' mx' hx'p hx'y')
    · exact Or.inl (E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p'))
    · exact Or.inl (E2 x mx hxp hxy')
    · exact Or.inr ⟨z3, t3⟩
    · exact Or.inl TSx.1
    · exact Or.inl TSp.1
    · exact Or.inl TSx.2
    · exact Or.inl TSp.2
    · exact Or.inr ⟨by rw [cyc']; exact z3, by rw [cyc']; exact t3⟩
    · exact Or.inl (S4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp))
    · exact Or.inl (S4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy'))
    · exact Or.inl (S4 x' mx' hx'p' hx'y (Ne.symm hxx'))
  · intro z hz hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    rcases hmemV z hz with h | h | h | h | h | h
    · exact absurd h h0
    · exact absurd h h3
    · rw [h]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
      · exact Or.inr ⟨det3_self_u _ x y, t1⟩
      · exact Or.inl (E2 y my hyp hyy')
      · exact Or.inl TSy.1
      · exact Or.inl TSy.2
      · exact Or.inr ⟨by rw [det3_shift_p', det3_self_left'], t2⟩
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h4

/-- **Lemma 9.11, the 5-cycle `(x, y, p, y', p')`** (the vertices over `q`
in the order `x, y`; lower chain on the top face). -/
theorem isRupert_weak_cycle5b {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hor : 0 < σ * det3 (p - y) (p' - y) (y - x)) (v : ℝ³)
    (t0p : 0 < σ * det3 (y - x) (p - x) v) (t0y' : 0 < σ * det3 (y - x) (y' - x) v)
    (t0p' : 0 < σ * det3 (y - x) (p' - x) v) (t0x' : 0 < σ * det3 (y - x) (x' - x) v)
    (t1 : 0 < σ * det3 (p - y) (x - y) v) (t2 : 0 < σ * det3 (x - p') (y - p') v)
    (t3 : 0 < σ * det3 (p' - y') (y - x) v)
    (hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), WQ5b fun i => ⟪quint x y p y' p' i, (y - x) + ε • v⟫) :
    IsRupert {x, x', y, y', p, p'} := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := weak_edge_tests F hq₁ hT hor
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set V : Finset ℝ³ := {x, x', y, y', p, p'} with hV
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have hmemV : ∀ z ∈ V, z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have t3' : 0 < σ * det3 (p' - y') (x' - y') v := by
    have e := weak_tau3 F hT v
    have hLy := F.ab'c'.neg y my (Ne.symm hxy) hyy' hyp'
    have hLx' := F.ab'c'.neg x' mx' (Ne.symm hxx') hx'y' hx'p'
    have : (σ * det3 (p' - y') (x' - y') v) * F.ab'c'.f y =
        (σ * det3 (p' - y') (y - x) v) * F.ab'c'.f x' := by
      rw [mul_assoc, mul_comm (det3 _ _ _), e]; ring
    nlinarith [mul_neg_of_pos_of_neg t3 hLx']
  have z3 : det3 (p' - y') (x' - y') (y - x) = 0 :=
    weak_top_perp F hT (weak_top_N F).1 (weak_top_N F).2
  have z0 : ∀ w : ℝ³, det3 (y - x) (w - x) (y - x) = 0 := fun w => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have S4 : ∀ w ∈ V, w ≠ p' → w ≠ y → w ≠ x → 0 < σ * det3 (x - p') (w - p') (y - x) :=
    fun w hw h1 h2 h3 => by rw [det3_shift_p']; exact E4 w hw h1 h2 h3
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  refine isRupert_of_tilted_unimodal_σ V (y - x) v hu (by norm_num) (quint x y p y' p') ?_ σ
    hσ ?_ ?_ WQ5b isOpen_WQ5b (fun z c hc hz => hz.mul hc) hQ
    (fun z hz hQ => hQ.unimodal hz)
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i j hi hj
    rcases weak_zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
    · exact Or.inr ⟨z0 p, t0p⟩
    · exact Or.inr ⟨z0 y', t0y'⟩
    · exact Or.inr ⟨z0 p', t0p'⟩
    · exact Or.inl (E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy'))
    · exact Or.inl (E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp'))
    · exact Or.inr ⟨det3_xy_zero p x y, t1⟩
    · exact Or.inl (E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p'))
    · exact Or.inl (E2 x mx hxp hxy')
    · exact Or.inl (E2 y my hyp hyy')
    · exact Or.inl (E3 x mx hxy' hxp' hxx')
    · exact Or.inl (E3 y my hyy' hyp' (Ne.symm hx'y))
    · exact Or.inl (E3 p mp (Ne.symm hy'p) hpp' (Ne.symm hx'p))
    · exact Or.inr ⟨by rw [det3_shift_p', det3_self_left'], t2⟩
    · exact Or.inl (S4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp))
    · exact Or.inl (S4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy'))
  · intro z hz hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    rcases hmemV z hz with h | h | h | h | h | h
    · exact absurd h h0
    · rw [h]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
      · exact Or.inr ⟨z0 x', t0x'⟩
      · exact Or.inl (E1 x' mx' hx'y hx'p (Ne.symm hxx'))
      · exact Or.inl (E2 x' mx' hx'p hx'y')
      · exact Or.inr ⟨z3, t3'⟩
      · exact Or.inl (S4 x' mx' hx'p' hx'y (Ne.symm hxx'))
    · exact absurd h h1
    · exact absurd h h3
    · exact absurd h h2
    · exact absurd h h4

/-- `quad_edge_lower` with an orientation factor `σ`. -/
theorem quad_edge_lower_σ {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p') {σ : ℝ}
    (_ : 0 < σ * det3 (y' - p) (p' - p) (y - x)) (_ : 0 < σ * det3 (y' - x) (p' - x) (y - x))
    (_ : 0 < σ * det3 (p - x) (p' - x) (y - x)) (hS₄ : 0 < σ * det3 (p - x) (y' - x) (y - x)) :
    σ * (det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ +
      det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫) <
    σ * (det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ +
      det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set u := y - x
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  set S₁ := det3 (y' - p) (p' - p) u
  set S₂ := det3 (y' - x) (p' - x) u
  set S₃ := det3 (p - x) (p' - x) u
  set S₄ := det3 (p - x) (y' - x) u
  have hpar := four_point_parallel x p y' p' u hu
  have hsum := four_point_sum x p y' p' u
  set L := S₁ • x - S₂ • p + S₃ • y' - S₄ • p'
  set lam := ⟪L, u⟫ / ⟪u, u⟫
  have hL : L = -S₂ • (p - x) + S₃ • (y' - x) - S₄ • (p' - x) := by
    have : S₁ = S₂ - S₃ + S₄ := by linarith
    simp only [L, this]; module
  have hGL : ⟪F.ab'c.N, L⟫ = -S₄ * F.ab'c.f p' := by
    rw [hL, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ← F.ab'c.hN, ← F.ab'c.hN, ← F.ab'c.hN, F.ab'c.hP, F.ab'c.hQ,
      F.ab'c.hR]
    ring
  have hGp' := F.ab'c.neg p' (by simp) (Ne.symm hxp') (Ne.symm hy'p') (Ne.symm hpp')
  have hGy := F.ab'c.neg y (by simp) (Ne.symm hxy) hyy' hyp
  have hGu : ⟪F.ab'c.N, u⟫ = F.ab'c.f y := by rw [← F.ab'c.hN, F.ab'c.hP, sub_zero]
  have e : ⟪F.ab'c.N, L⟫ = lam * F.ab'c.f y := by
    rw [← hGu, ← real_inner_smul_right, ← hpar]
  rw [hGL] at e
  have hlam : σ * lam < 0 := by
    have h1 : 0 < (σ * S₄) * (-F.ab'c.f p') := mul_pos hS₄ (by linarith)
    have h2 : (σ * lam) * F.ab'c.f y = (σ * S₄) * (-F.ab'c.f p') := by
      rw [mul_assoc, ← e]; ring
    nlinarith
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hLu : σ * ⟪L, u⟫ < 0 := by
    have : ⟪L, u⟫ = lam * ⟪u, u⟫ := by
      conv_lhs => rw [hpar]
      rw [real_inner_smul_left]
    rw [this, ← mul_assoc]; nlinarith
  simp only [L, inner_sub_left, inner_add_left, real_inner_smul_left] at hLu
  nlinarith

/-- An open condition on the limit depths holds at all small tilts. -/
theorem eventually_of_isOpen {k : ℕ} {Q : (ZMod k → ℝ) → Prop} (hQo : IsOpen {z | Q z})
    (x : ZMod k → ℝ³) (u v : ℝ³) (h0 : Q fun i => ⟪x i, u⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q fun i => ⟪x i, u + ε • v⟫ := by
  have hc : Continuous fun ε : ℝ => fun i => ⟪x i, u + ε • v⟫ := by fun_prop
  have : ∀ᶠ ε in 𝓝 (0 : ℝ), Q fun i => ⟪x i, u + ε • v⟫ :=
    hc.continuousAt.eventually (hQo.mem_nhds (by simpa using h0))
  exact this.filter_mono nhdsWithin_le_nhds

/-- A strict comparison of tilted depths, with a lexicographic tie-break. -/
theorem eventually_depth_lt {a b v u : ℝ³}
    (h : ⟪a, u⟫ < ⟪b, u⟫ ∨ (⟪a, u⟫ = ⟪b, u⟫ ∧ ⟪a, v⟫ < ⟪b, v⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪a, u + ε • v⟫ < ⟪b, u + ε • v⟫ := by
  have := eventually_pos_affine (A := ⟪b, u⟫ - ⟪a, u⟫) (B := ⟪b, v⟫ - ⟪a, v⟫)
    (by rcases h with h | ⟨h1, h2⟩; exacts [Or.inl (by linarith), Or.inr ⟨by linarith,
      by linarith⟩])
  filter_upwards [this] with ε hε
  simp only [inner_add_right, real_inner_smul_right]; linarith

/-- An affine test `σ * (A + η * B)` that is eventually positive in `η`. -/
theorem eventually_test {σ A B : ℝ} (h : 0 < σ * A ∨ (A = 0 ∧ 0 < σ * B)) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < σ * (A + η * B) := by
  have := eventually_pos_affine (A := σ * A) (B := σ * B)
    (by rcases h with h | ⟨h1, h2⟩; exacts [Or.inl h, Or.inr ⟨by rw [h1, mul_zero], h2⟩])
  filter_upwards [this] with η hη; linarith [hη]

/-- When the middle depths tie and the lateral inner product is negative,
a perturbed five-cycle gives a passage. -/
private theorem isRupert_weak_tie_neg {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y)
    (hTp : F.a'b'c'.f p = F.a'b'c'.f y) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hor : 0 < σ * det3 (p - y) (p' - y) (y - x))
    (e1y' : 0 < σ * det3 (p - y) (y' - y) (y - x))
    (e1x' : 0 < σ * det3 (p - y) (x' - y) (y - x))
    (e3x : 0 < σ * det3 (p' - y') (x - y') (y - x)) (hyp : y ≠ p)
    (hab : ⟪x, y - x⟫ < ⟪p, y - x⟫) (hY1 : ⟪p, y - x⟫ ≤ ⟪y, y - x⟫)
    (hbc : ⟪p, y - x⟫ = ⟪y', y - x⟫) (heb' : ⟪p', y - x⟫ < ⟪p, y - x⟫)
    (hneg : ⟪p - y', p - y⟫ < 0) :
    IsRupert {x, x', y, y', p, p'} := by
  classical
  have hTN := weak_top_N F
  have hyN : ⟪F.a'b'c'.N, y - p⟫ = 0 := by rw [← F.a'b'c'.hN, hTp, sub_self]
  have i0p : ∀ η : ℝ, det3 (y - x) (p - x) ((y - p) + η • (y' - y)) =
      0 + η * det3 (p - y) (y' - y) (y - x) := fun η => by
    rw [det3_add_smul]; congr 1 <;> [skip; congr 1] <;>
      simp only [det3_expand, PiLp.sub_apply] <;> ring
  have i0y' : ∀ η : ℝ, det3 (y - x) (y' - x) ((y - p) + η • (y' - y)) =
      det3 (p - y) (y' - y) (y - x) + η * det3 (y - x) (y' - x) (y' - y) := fun η => by
    rw [det3_add_smul]; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
  have i0p' : ∀ η : ℝ, det3 (y - x) (p' - x) ((y - p) + η • (y' - y)) =
      det3 (p - y) (p' - y) (y - x) + η * det3 (y - x) (p' - x) (y' - y) := fun η => by
    rw [det3_add_smul]; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
  have i0x' : ∀ η : ℝ, det3 (y - x) (x' - x) ((y - p) + η • (y' - y)) =
      det3 (p - y) (x' - y) (y - x) + η * det3 (y - x) (x' - x) (y' - y) := fun η => by
    rw [det3_add_smul]; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
  have i1 : ∀ η : ℝ, det3 (p - y) (x - y) ((y - p) + η • (y' - y)) =
      0 + η * det3 (p - y) (y' - y) (y - x) := fun η => by
    rw [det3_add_smul]; congr 1 <;> [skip; congr 1] <;>
      simp only [det3_expand, PiLp.sub_apply] <;> ring
  have i2 : ∀ η : ℝ, det3 (x - p') (y - p') ((y - p) + η • (y' - y)) =
      det3 (p - y) (p' - y) (y - x) + η * det3 (x - p') (y - p') (y' - y) := fun η => by
    rw [det3_add_smul]; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
  have z3 : det3 (p' - y') (y - x) (y - p) = 0 := by
    have := weak_top_perp F hT hTN.1 hyN
    have e : det3 (p' - y') (y - x) (y - p) = -det3 (p' - y') (y - p) (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, this, neg_zero]
  have i3 : ∀ η : ℝ, det3 (p' - y') (y - x) ((y - p) + η • (y' - y)) =
      0 + η * det3 (p' - y') (x - y') (y - x) := fun η => by
    rw [det3_add_smul, z3]; congr 1; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
  have iq1 : ∀ η : ℝ, ⟪y - p, (y - p) + η • (y' - y)⟫ =
      ⟪y - p, y - p⟫ + η * ⟪y - p, y' - y⟫ := fun η => by
    rw [inner_add_right, real_inner_smul_right]
  have iq2 : ∀ η : ℝ, ⟪p - y', (y - p) + η • (y' - y)⟫ =
      -⟪p - y', p - y⟫ + η * ⟪p - y', y' - y⟫ := fun η => by
    rw [inner_add_right, real_inner_smul_right, ← neg_sub p y, inner_neg_right]
  have hpy0 : 0 < ⟪y - p, y - p⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hyp)
  obtain ⟨η, c1, c2, c3, c4, c5, c6, c7, c8, -⟩ :=
    ((eventually_test (σ := σ) (A := 0) (B := det3 (p - y) (y' - y) (y - x))
      (Or.inr ⟨rfl, e1y'⟩)).and
    ((eventually_test (σ := σ) (B := det3 (y - x) (y' - x) (y' - y)) (Or.inl e1y')).and
    ((eventually_test (σ := σ) (B := det3 (y - x) (p' - x) (y' - y)) (Or.inl hor)).and
    ((eventually_test (σ := σ) (B := det3 (y - x) (x' - x) (y' - y)) (Or.inl e1x')).and
    ((eventually_test (σ := σ) (B := det3 (x - p') (y - p') (y' - y)) (Or.inl hor)).and
    ((eventually_test (σ := σ) (A := 0) (B := det3 (p' - y') (x - y') (y - x))
      (Or.inr ⟨rfl, e3x⟩)).and
    ((eventually_test (σ := 1) (A := ⟪y - p, y - p⟫) (B := ⟪y - p, y' - y⟫)
      (Or.inl (by linarith))).and
    ((eventually_test (σ := 1) (A := -⟪p - y', p - y⟫) (B := ⟪p - y', y' - y⟫)
      (Or.inl (by linarith))).and
    (self_mem_nhdsWithin : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioi 0))))))))).exists
  refine isRupert_weak_cycle5b F hq₁ hT hσ hor ((y - p) + η • (y' - y))
    (by rw [i0p]; exact c1) (by rw [i0y']; exact c2) (by rw [i0p']; exact c3)
    (by rw [i0x']; exact c4) (by rw [i1]; exact c1) (by rw [i2]; exact c5)
    (by rw [i3]; exact c6) ?_
  rw [one_mul] at c7 c8
  rw [← iq1] at c7
  rw [← iq2] at c8
  filter_upwards [eventually_depth_lt (a := x) (b := y) (v := (y - p) + η • (y' - y))
      (u := y - x) (Or.inl (by linarith)),
    eventually_depth_lt (a := p) (b := y) (v := (y - p) + η • (y' - y)) (u := y - x)
      (by rcases lt_or_eq_of_le hY1 with h | h
          · exact Or.inl h
          · refine Or.inr ⟨h, ?_⟩; rw [inner_sub_left] at c7; linarith),
    eventually_depth_lt (a := y') (b := p) (v := (y - p) + η • (y' - y)) (u := y - x)
      (Or.inr ⟨hbc.symm, by rw [inner_sub_left] at c8; linarith⟩),
    eventually_depth_lt (a := p') (b := y') (v := (y - p) + η • (y' - y)) (u := y - x)
      (Or.inl (by linarith))] with ε h1 h2 h3 h4
  simp only [WQ5b, quint_0, quint_1, quint_2, quint_3, quint_4]
  exact ⟨h1, h2, h3, h4⟩

/-- **Lemma 9.11** for a weak quad edge `x → y` (orientation `σ`): a passage,
or the edge is touching, or its lateral edge `p y'` is orthogonal to `y - x`
and to `p - y` (parallel to the normal of the faces `x y p ∥ x' y' p'`). -/
theorem isRupert_weak_edge_σ {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y)
    (hTp : F.a'b'c'.f p = F.a'b'c'.f y) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hor : 0 < σ * det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫) :
    IsRupert {x, x', y, y', p, p'} ∨
      (⟪p, y - x⟫ = ⟪p', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫ ∧ ⟪y', y - x⟫ < ⟪y, y - x⟫) ∨
      (⟪p - y', y - x⟫ = 0 ∧ ⟪p - y', p - y⟫ = 0) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := weak_edge_tests F hq₁ hT hor
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have mx : x ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have e1y' := E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
  have e1x' := E1 x' mx' hx'y hx'p (Ne.symm hxx')
  have e4y' := E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
  have e3x := E3 x mx hxy' hxp' hxx'
  have e2p' := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
  have hTN := weak_top_N F
  have hpy : ⟪F.a'b'c'.N, p - y⟫ = 0 := by rw [← F.a'b'c'.hN, hTp, sub_self]
  have hLy := F.ab'c'.neg y my (Ne.symm hxy) hyy' hyp'
  have hLx' := F.ab'c'.neg x' mx' (Ne.symm hxx') hx'y' hx'p'
  -- the depths
  set Y := ⟪y, y - x⟫
  set a := ⟪x, y - x⟫
  set b := ⟪p, y - x⟫
  set c := ⟪y', y - x⟫
  set d := ⟪x', y - x⟫
  set e := ⟪p', y - x⟫
  by_cases hN : NWS4 (quad Y b c e)
  · -- Mixed: the 4-cycle `(y, p, y', p')`, tilt `y' - x`
    left
    refine isRupert_weak_cycle4 F hq₁ hT hσ hor (y' - x) (by rw [det3_tilt_y]; exact e1y')
      (by rw [det3_tilt_p']; exact e4y') ?_ ?_
    · have : det3 (p' - y') (y - x) (y' - x) = det3 (p' - y') (x - y') (y - x) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; exact e3x
    · refine eventually_of_isOpen isOpen_NWS4 (quad y p y' p') (y - x) (y' - x) ?_
      convert hN using 1; funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  -- separated: `min(Y, c) ≥ max(b, e)`
  have hY : b ≤ Y ∧ e ≤ Y ∧ b ≤ c ∧ e ≤ c := by
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hN
    simp only [max_le_iff, le_min_iff, not_and_or, not_le] at hgood
    by_contra hc
    apply hN
    constructor
    · simp only [not_and_or, not_le] at hc; exact hc
    · rcases hgood with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  -- the lower boundary: `a < max(b, e)`
  have hS₂ : 0 < σ * det3 (y' - x) (p' - x) (y - x) := by rw [← det3_cyc x y' p']; exact e3x
  have hS₃ : 0 < σ * det3 (p - x) (p' - x) (y - x) := by rw [det3_shift_xy]; exact hor
  have hS₄ : 0 < σ * det3 (p - x) (y' - x) (y - x) := by rw [det3_shift_xy]; exact e1y'
  have hlow := quad_edge_lower_σ F e2p' hS₂ hS₃ hS₄
  have hsum := four_point_sum x p y' p' (y - x)
  have hx_lt : a < b ∨ a < e := by
    by_contra hc; push Not at hc
    obtain ⟨c1, c2⟩ := hc
    rcases le_total b e with hpp | hpp
    · nlinarith only [hlow, mul_le_mul_of_nonneg_left c2 e2p'.le,
        mul_le_mul_of_nonneg_left hY4 hS₃.le, mul_le_mul_of_nonneg_left hpp hS₂.le,
        mul_eq_zero_of_left hsum (σ * e)]
    · nlinarith only [hlow, mul_le_mul_of_nonneg_left c1 e2p'.le,
        mul_le_mul_of_nonneg_left hY3 hS₃.le, mul_le_mul_of_nonneg_left hpp hS₄.le,
        mul_eq_zero_of_left hsum (σ * b)]
  rcases lt_or_eq_of_le hY3 with hbc | hbc
  · -- the 5-cycle `(x, p, y', x', p')`, tilt `x - y'`
    left
    -- `x'` lies above the chord `y' p'`: `e < d`
    have hed : e < d := by
      obtain ⟨-, -, i3, i4⟩ := weak_top_face F hT x
      obtain ⟨s3, s1⟩ := weak_top_signs F hq₁ hT e3x
      have huu : 0 < ⟪y - x, y - x⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
      by_contra hde; push Not at hde
      have k1 : 0 < (σ * det3 (p' - y') (x - y') (y - x)) * (-F.ab'c'.f x') * ⟪y - x, y - x⟫ :=
        mul_pos (mul_pos e3x (by linarith)) huu
      have k2 : σ * (det3 (p' - x') (x - x') (y - x) * c - det3 (p' - y') (x - y') (y - x) * d +
          det3 (x' - y') (x - y') (y - x) * e) < 0 := by
        have : F.ab'c'.f y * (σ * (det3 (p' - x') (x - x') (y - x) * c -
            det3 (p' - y') (x - y') (y - x) * d + det3 (x' - y') (x - y') (y - x) * e)) =
            (σ * det3 (p' - y') (x - y') (y - x)) * (-F.ab'c'.f x') * ⟪y - x, y - x⟫ := by
          rw [← mul_assoc, mul_comm (F.ab'c'.f y) σ, mul_assoc, i3]; ring
        exact neg_of_mul_pos_right (by rw [this]; exact k1) hLy.le
      have k3 : σ * det3 (p' - y') (x - y') (y - x) = σ * det3 (p' - x') (x - x') (y - x) +
          σ * det3 (x' - y') (x - y') (y - x) := by linear_combination -σ * i4
      have k4 : σ * det3 (p' - y') (x - y') (y - x) * d = σ * det3 (p' - x') (x - x') (y - x) * d +
          σ * det3 (x' - y') (x - y') (y - x) * d := by rw [k3]; ring
      have k5 := mul_le_mul_of_nonneg_left (show d ≤ c by linarith) s1.le
      have k6 := mul_le_mul_of_nonneg_left hde s3.le
      have k7 : σ * (det3 (p' - x') (x - x') (y - x) * c - det3 (p' - y') (x - y') (y - x) * d +
          det3 (x' - y') (x - y') (y - x) * e) = σ * det3 (p' - x') (x - x') (y - x) * c -
          σ * det3 (p' - y') (x - y') (y - x) * d + σ * det3 (x' - y') (x - y') (y - x) * e := by
        ring
      linarith only [k2, k4, k5, k6, k7]
    refine isRupert_weak_cycle5a F hq₁ hT hσ hor (x - y') (by rw [det3_tilt_x]; exact e1y')
      (by rw [det3_tilt_x']; exact e4y') ?_ ?_
    · have e0 := weak_tau3 F hT (x - y')
      have i1 : det3 (p' - y') (y - x) (x - y') = -det3 (p' - y') (x - y') (y - x) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [i1] at e0
      rw [det3_swap12]
      have k : F.ab'c'.f y * (σ * det3 (p' - y') (x' - y') (x - y')) =
          (-F.ab'c'.f x') * (σ * det3 (p' - y') (x - y') (y - x)) := by
        linear_combination σ * e0
      have kp : 0 < (-F.ab'c'.f x') * (σ * det3 (p' - y') (x - y') (y - x)) :=
        mul_pos (neg_pos.mpr hLx') e3x
      have hneg : σ * det3 (p' - y') (x' - y') (x - y') < 0 :=
        neg_of_mul_pos_right (by rw [k]; exact kp) hLy.le
      linarith only [hneg]
    · refine eventually_of_isOpen isOpen_WQ5a (quint x p y' x' p') (y - x) (x - y') ?_
      simp only [WQ5a, quint_0, quint_1, quint_2, quint_3, quint_4]
      exact ⟨hbc, hed, hx_lt⟩
  -- `b = c`
  by_cases heb : e = b
  · right; left
    simp only [max_le_iff, le_min_iff, not_and_or, not_le] at hgood
    refine ⟨heb.symm, by rw [heb, hbc], ?_⟩
    rcases hgood with (h | h) | (h | h) <;> linarith
  have heb' : e < b := lt_of_le_of_ne (hbc ▸ hY4) heb
  rcases lt_trichotomy ⟪p - y', p - y⟫ 0 with hneg | hzero | hpos
  · left
    have hab : a < b := by rcases hx_lt with h | h; exacts [h, by linarith]
    exact isRupert_weak_tie_neg F hq₁ hT hTp hσ hor e1y' e1x' e3x hyp
      hab hY1 hbc heb' hneg
  · -- the lateral edge `p y'` is parallel to the normal
    right; right
    exact ⟨by rw [inner_sub_left]; linarith, hzero⟩
  · -- the tie with `ω > t₂`: the 4-cycle `(y, p, y', p')`, tilt `(p - y) + η (y' - y)`
    left
    have i1 : ∀ η : ℝ, det3 (p - y) (x - y) ((p - y) + η • (y' - y)) =
        0 + η * det3 (p - y) (y' - y) (y - x) := fun η => by
      rw [det3_add_smul]; congr 1 <;> [skip; congr 1] <;>
        simp only [det3_expand, PiLp.sub_apply] <;> ring
    have i2 : ∀ η : ℝ, det3 (y - p') (x - p') ((p - y) + η • (y' - y)) =
        det3 (p - y) (p' - y) (y - x) + η * det3 (y - p') (x - p') (y' - y) := fun η => by
      rw [det3_add_smul]; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
    have z3 : det3 (p' - y') (y - x) (p - y) = 0 := by
      have := weak_top_perp F hT hTN.1 hpy
      have e : det3 (p' - y') (y - x) (p - y) = -det3 (p' - y') (p - y) (y - x) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e, this, neg_zero]
    have i3 : ∀ η : ℝ, det3 (p' - y') (y - x) ((p - y) + η • (y' - y)) =
        0 + η * det3 (p' - y') (x - y') (y - x) := fun η => by
      rw [det3_add_smul, z3]; congr 1; congr 1; simp only [det3_expand, PiLp.sub_apply]; ring
    have iq : ∀ η : ℝ, ⟪p - y', (p - y) + η • (y' - y)⟫ =
        ⟪p - y', p - y⟫ + η * ⟪p - y', y' - y⟫ := fun η => by
      rw [inner_add_right, real_inner_smul_right]
    obtain ⟨η, c1, c2, c3, c4, -⟩ :=
      ((eventually_test (σ := σ) (A := 0) (B := det3 (p - y) (y' - y) (y - x))
        (Or.inr ⟨rfl, e1y'⟩)).and
      ((eventually_test (σ := σ) (B := det3 (y - p') (x - p') (y' - y)) (Or.inl hor)).and
      ((eventually_test (σ := σ) (A := 0) (B := det3 (p' - y') (x - y') (y - x))
        (Or.inr ⟨rfl, e3x⟩)).and
      ((eventually_test (σ := 1) (A := ⟪p - y', p - y⟫) (B := ⟪p - y', y' - y⟫)
        (Or.inl (by linarith))).and
      (self_mem_nhdsWithin : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioi 0))))).exists
    refine isRupert_weak_cycle4 F hq₁ hT hσ hor ((p - y) + η • (y' - y))
      (by rw [i1]; exact c1) (by rw [i2]; exact c2) (by rw [i3]; exact c3) ?_
    rw [one_mul, ← iq] at c4
    filter_upwards [eventually_depth_lt (a := y') (b := p) (v := (p - y) + η • (y' - y))
        (u := y - x) (Or.inr ⟨hbc.symm, by rw [inner_sub_left] at c4; linarith⟩),
      eventually_depth_lt (a := p') (b := y) (v := (p - y) + η • (y' - y)) (u := y - x)
        (Or.inl (by linarith))] with ε h1 h2
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
    exact ⟨Or.inr (Or.inr (Or.inl h1)), Or.inr (Or.inl h2)⟩

/-- **Lemma 9.11** for a weak quad edge `x → y`: a passage, or the edge is
touching, or its lateral edge `p y'` is orthogonal to `y - x` and `p - y`. -/
theorem isRupert_weak_edge {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y)
    (hTp : F.a'b'c'.f p = F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫) :
    IsRupert {x, x', y, y', p, p'} ∨
      (⟪p, y - x⟫ = ⟪p', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫ ∧ ⟪y', y - x⟫ < ⟪y, y - x⟫) ∨
      (⟪p - y', y - x⟫ = 0 ∧ ⟪p - y', p - y⟫ = 0) := by
  rcases lt_or_gt_of_ne (quad_orient_ne F) with h | h
  · exact isRupert_weak_edge_σ F hq₁ hT hTp (σ := -1) (Or.inr rfl) (by linarith) hgood
  · exact isRupert_weak_edge_σ F hq₁ hT hTp (σ := 1) (Or.inl rfl) (by linarith) hgood

end Minimality

end RupertMinimality
