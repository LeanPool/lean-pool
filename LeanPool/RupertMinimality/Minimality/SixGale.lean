/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.OctahedronAll
public import LeanPool.RupertMinimality.Minimality.L8T3
public import LeanPool.RupertMinimality.Minimality.L8T4
public import LeanPool.RupertMinimality.Minimality.RightPrism

/-! # Six Gale -/

@[expose] public section

namespace RupertMinimality

/-!
# Six points in convex position: dependencies, Gale signs, splits, prisms (L10)

Part of step 5 of `minimality.md`.  Setting (S) (`Six V`): six points, none in
the hull of the others,
not coplanar, no five coplanar.  Affine dependencies are functions
`ℝ³ → ℝ` (`IsDepOn V l`); two of them, `l` and `m`, give the Gale vectors
`(l t, m t)` and the determinants `galeD l m s t`.

* §10.1: the vertex lemma, no three collinear points, no three parallel Gale
  vectors, and facets (triangles, quadrilaterals) and independent tetrahedra
  from signs of `galeD`;
* Lemma 10.1 (`exists_split_of_no_partner`): a point without an O-partner
  gives a 2+4 split (a dependency positive at exactly two points);
* Proposition 10.2 (`isRupert_of_all_partners`): three O-pairs form a prism
  (frustum, parallel or translation prism).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Four points with nonzero orientation determinant are affinely independent. -/
theorem affineIndependent_of_det3 {a b c d : ℝ³} (h : det3 (b - a) (c - a) (d - a) ≠ 0) :
    AffineIndependent ℝ ![a, b, c, d] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w _ hw a,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_four] at hs
  have hc : cmb (b - a) (c - a) (d - a) (w 1) (w 2) (w 3) = 0 := by
    simpa [cmb] using hs
  obtain ⟨h₁, h₂, h₃⟩ := cmb_eq_zero h hc
  rw [Fin.sum_univ_four] at hw
  intro i
  fin_cases i <;> simp <;> linarith

/-- `l` is an affine dependency of the points of `V`. -/
def IsDepOn (V : Finset ℝ³) (l : ℝ³ → ℝ) : Prop :=
  ∑ t ∈ V, l t = 0 ∧ ∑ t ∈ V, l t • t = 0

/-- Setting (S): six points, none in the hull of the others, not coplanar, no
five coplanar. -/
structure Six (V : Finset ℝ³) : Prop where
  card : V.card = 6
  vert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)
  noncop : ¬ Coplanar ℝ (V : Set ℝ³)
  no5 : ∀ v ∈ V, ¬ Coplanar ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)

/-! ### Sums over six listed points -/

theorem sum_six {M : Type*} [AddCommMonoid M] {a b c d e f : ℝ³}
    (hnd : [a, b, c, d, e, f].Nodup) (g : ℝ³ → M) :
    ∑ t ∈ ({a, b, c, d, e, f} : Finset ℝ³), g t = g a + g b + g c + g d + g e + g f := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef, -⟩ :=
    hnd
  rw [Finset.sum_insert (by simp [hab, hac, had, hae, haf]),
    Finset.sum_insert (by simp [hbc, hbd, hbe, hbf]), Finset.sum_insert (by simp [hcd, hce, hcf]),
    Finset.sum_insert (by simp [hde, hdf]), Finset.sum_pair hef]
  simp only [add_assoc]

/-! ### Dependencies -/

theorem IsDepOn.comb {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (α β : ℝ) : IsDepOn V (fun t => α * l t + β * m t) := by
  constructor
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hl.1, hm.1]; ring
  · calc ∑ t ∈ V, (α * l t + β * m t) • t = ∑ t ∈ V, (α • (l t • t) + β • (m t • t)) :=
          Finset.sum_congr rfl (fun t _ => by rw [add_smul, mul_smul, mul_smul])
      _ = α • ∑ t ∈ V, l t • t + β • ∑ t ∈ V, m t • t := by
          rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = 0 := by rw [hl.2, hm.2, smul_zero, smul_zero, add_zero]

theorem IsDepOn.neg {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) :
    IsDepOn V (fun t => -l t) := by
  constructor
  · rw [Finset.sum_neg_distrib, hl.1, neg_zero]
  · simp only [neg_smul, Finset.sum_neg_distrib, hl.2, neg_zero]

/-- A dependency applied to an affine function. -/
theorem IsDepOn.apply {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) (f : ℝ³ →ᵃ[ℝ] ℝ) :
    ∑ t ∈ V, l t * f t = 0 := by
  have hf : ∀ x, f x = f.linear x + f 0 := fun x => by
    have := f.map_vadd 0 x
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  calc ∑ t ∈ V, l t * f t = ∑ t ∈ V, (l t * f.linear t + l t * f 0) :=
        Finset.sum_congr rfl (fun t _ => by rw [hf t, mul_add])
    _ = f.linear (∑ t ∈ V, l t • t) + (∑ t ∈ V, l t) * f 0 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, map_sum]
        simp only [map_smul, smul_eq_mul]
    _ = 0 := by rw [hl.1, hl.2, map_zero, zero_mul, add_zero]

theorem IsDepOn.galeD {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (s : ℝ³) : IsDepOn V (galeD l m s) := by
  have := hl.comb hm (-m s) (l s)
  convert this using 2 with t
  simp only [Minimality.galeD]; ring

/-- The dependency `t ↦ -⟨g_s, g_t⟩`. -/
theorem IsDepOn.nu {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (s : ℝ³) : IsDepOn V (fun t => -(l s * l t + m s * m t)) := by
  have := hl.comb hm (-l s) (-m s)
  convert this using 2 with t
  ring

/-! ### §10.1 (a)–(d) -/

/-- **(a) Vertex lemma.**  No dependency is negative at exactly one point and
nonnegative elsewhere. -/
theorem Six.not_single_neg {V : Finset ℝ³} (hS : Six V) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    {v : ℝ³} (hv : v ∈ V) (hneg : μ v < 0) (hrest : ∀ t ∈ V, t ≠ v → 0 ≤ μ t) : False := by
  classical
  apply hS.vert v hv
  have hsplit := Finset.add_sum_erase V μ hv
  have hsplit' := Finset.add_sum_erase V (fun t => μ t • t) hv
  rw [hμ.1] at hsplit
  rw [hμ.2] at hsplit'
  rw [Finset.mem_convexHull']
  refine ⟨fun t => μ t / (-μ v), fun t ht => ?_, ?_, ?_⟩
  · exact div_nonneg (hrest t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht))
      (by linarith)
  · rw [← Finset.sum_div, div_eq_one_iff_eq (by linarith)]; linarith
  · simp only [div_eq_mul_inv, mul_comm _ (-μ v)⁻¹, ← smul_smul, ← Finset.smul_sum]
    have h2 : ∑ x ∈ V.erase v, μ x • x = -(μ v • v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsplit'
    rw [h2, ← neg_smul, smul_smul, inv_mul_cancel₀ (by linarith : -μ v ≠ 0), one_smul]

/-- A dependency that is nonnegative (or nonpositive) everywhere vanishes. -/
theorem IsDepOn.eq_zero_of_nonpos {V : Finset ℝ³} {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    (h : ∀ t ∈ V, μ t ≤ 0) : ∀ t ∈ V, μ t = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonpos h).mp hμ.1

/-- **(b)** No three points of `V` are collinear. -/
theorem Six.cross_ne_zero {V : Finset ℝ³} (hS : Six V) {P Q R : ℝ³} (hP : P ∈ V) (hQ : Q ∈ V)
    (hR : R ∈ V) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : cross (Q - P) (R - P) ≠ 0 := by
  intro h0
  have ha : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have haa : 0 < ⟪Q - P, Q - P⟫ := real_inner_self_pos.mpr ha
  have key : ⟪Q - P, Q - P⟫ • (R - P) = ⟪Q - P, R - P⟫ • (Q - P) := by
    have c0 := congrArg (fun v : ℝ³ => v 0) h0
    have c1 := congrArg (fun v : ℝ³ => v 1) h0
    have c2 := congrArg (fun v : ℝ³ => v 2) h0
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.zero_apply] at c0 c1 c2
    ext i; fin_cases i <;>
      simp only [PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      simp only [PiLp.sub_apply] at c0 c1 c2 ⊢
    · linear_combination (-(Q 1 - P 1)) * c2 + (Q 2 - P 2) * c1
    · linear_combination (Q 0 - P 0) * c2 - (Q 2 - P 2) * c0
    · linear_combination (-(Q 0 - P 0)) * c1 + (Q 1 - P 1) * c0
  set t := ⟪Q - P, R - P⟫ / ⟪Q - P, Q - P⟫ with ht
  have hR' : R = P + t • (Q - P) := by
    have : R - P = t • (Q - P) := by
      rw [ht, div_eq_inv_mul, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ haa.ne', one_smul]
    rw [← this]; abel
  rcases lt_or_ge t 0 with h | h
  · apply hS.vert P hP
    have hs : segment ℝ Q R ⊆ convexHull ℝ ((V.erase P : Finset ℝ³) : Set ℝ³) :=
      segment_subset_convexHull (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPQ.symm, hQ⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPR.symm, hR⟩))
    have h1 : (1 - t) ≠ 0 := by linarith
    refine hs ⟨-t / (1 - t), 1 / (1 - t), by
      apply div_nonneg <;> linarith, by apply div_nonneg <;> linarith, by
      rw [← add_div, div_eq_one_iff_eq h1]; ring, ?_⟩
    rw [hR', show -t / (1 - t) = (1 / (1 - t)) * (-t) by ring, ← smul_smul, ← smul_add]
    have : (-t) • Q + (P + t • (Q - P)) = (1 - t) • P := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ h1, one_smul]
  rcases le_or_gt t 1 with h' | h'
  · apply hS.vert R hR
    have hs : segment ℝ P Q ⊆ convexHull ℝ ((V.erase R : Finset ℝ³) : Set ℝ³) :=
      segment_subset_convexHull (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPR, hP⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hQR, hQ⟩))
    exact hs ⟨1 - t, t, by linarith, h, by ring, by rw [hR']; module⟩
  · apply hS.vert Q hQ
    have hs : segment ℝ P R ⊆ convexHull ℝ ((V.erase Q : Finset ℝ³) : Set ℝ³) :=
      segment_subset_convexHull (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPQ, hP⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hQR.symm, hR⟩))
    have ht0 : t ≠ 0 := by linarith
    refine hs ⟨1 - 1 / t, 1 / t, by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith, by positivity, by ring, ?_⟩
    rw [hR', smul_add, smul_smul, one_div, inv_mul_cancel₀ ht0, one_smul]
    module

/-- A nonzero dependency vanishes at no three points (support at least 4). -/
theorem Six.no_three_zeros {V : Finset ℝ³} (hS : Six V) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    (hne : ∃ t ∈ V, μ t ≠ 0) {a b c : ℝ³} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h0a : μ a = 0) (h0b : μ b = 0) (h0c : μ c = 0) : False := by
  classical
  have hc3 : (((V.erase a).erase b).erase c).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm,
      hc⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩), Finset.card_erase_of_mem ha,
      hS.card]
  obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.mp hc3
  have hmemx : ∀ w, w ∈ ({x, y, z} : Finset ℝ³) ↔ w ≠ c ∧ w ≠ b ∧ w ≠ a ∧ w ∈ V := by
    intro w; rw [← hxyz, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
  have hx := (hmemx x).mp (by simp)
  have hy := (hmemx y).mp (by simp)
  have hz := (hmemx z).mp (by simp)
  have mem : ∀ t ∈ V, t = a ∨ t = b ∨ t = c ∨ t = x ∨ t = y ∨ t = z := by
    intro t ht
    by_cases h1 : t = a; · exact Or.inl h1
    by_cases h2 : t = b; · exact Or.inr (Or.inl h2)
    by_cases h3 : t = c; · exact Or.inr (Or.inr (Or.inl h3))
    have := (hmemx t).mpr ⟨h3, h2, h1, ht⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  -- the sum over the remaining three points
  have hsum : μ x + μ y + μ z = 0 := by
    have e1 := Finset.add_sum_erase V μ ha
    have e2 := Finset.add_sum_erase (V.erase a) μ (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
    have e3 := Finset.add_sum_erase ((V.erase a).erase b) μ
      (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, hc⟩⟩)
    rw [hxyz, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz] at e3
    rw [hμ.1] at e1
    linarith
  have hne' : μ x ≠ 0 ∨ μ y ≠ 0 ∨ μ z ≠ 0 := by
    obtain ⟨t, ht, htne⟩ := hne
    rcases mem t ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd h0a htne
    · exact absurd h0b htne
    · exact absurd h0c htne
    · exact Or.inl htne
    · exact Or.inr (Or.inl htne)
    · exact Or.inr (Or.inr htne)
  -- a dependency negative at exactly one of `x, y, z` and nonnegative at the others
  have lone : ∀ ν : ℝ³ → ℝ, IsDepOn V ν → ν a = 0 → ν b = 0 → ν c = 0 →
      ∀ v, (v = x ∨ v = y ∨ v = z) → ν v < 0 → (x ≠ v → 0 ≤ ν x) → (y ≠ v → 0 ≤ ν y) →
        (z ≠ v → 0 ≤ ν z) → False := by
    intro ν hν na nb nc v hv hneg h1 h2 h3
    have hvV : v ∈ V := by rcases hv with rfl | rfl | rfl <;> simp_all
    refine hS.not_single_neg hν hvV hneg (fun t ht htv => ?_)
    rcases mem t ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [na]
    · rw [nb]
    · rw [nc]
    · exact h1 htv
    · exact h2 htv
    · exact h3 htv
  have hn := hμ.neg
  rcases lt_or_ge (μ x) 0 with hx0 | hx0 <;> rcases lt_or_ge (μ y) 0 with hy0 | hy0 <;>
    rcases lt_or_ge (μ z) 0 with hz0 | hz0
  · linarith
  · exact lone (fun t => -μ t) hn (by simp [h0a]) (by simp [h0b]) (by simp [h0c]) z (by simp)
      (by linarith) (fun _ => by linarith) (fun _ => by linarith) (fun h => absurd rfl h)
  · exact lone (fun t => -μ t) hn (by simp [h0a]) (by simp [h0b]) (by simp [h0c]) y (by simp)
      (by linarith) (fun _ => by linarith) (fun h => absurd rfl h) (fun _ => by linarith)
  · exact lone μ hμ h0a h0b h0c x (by simp) hx0 (fun h => absurd rfl h) (fun _ => hy0)
      (fun _ => hz0)
  · exact lone (fun t => -μ t) hn (by simp [h0a]) (by simp [h0b]) (by simp [h0c]) x (by simp)
      (by linarith) (fun h => absurd rfl h) (fun _ => by linarith) (fun _ => by linarith)
  · exact lone μ hμ h0a h0b h0c y (by simp) hy0 (fun _ => hx0) (fun h => absurd rfl h)
      (fun _ => hz0)
  · exact lone μ hμ h0a h0b h0c z (by simp) hz0 (fun _ => hx0) (fun _ => hy0)
      (fun h => absurd rfl h)
  · rcases hne' with h | h | h <;> apply h <;> linarith

/-- A Gale frame: two dependencies, with nonzero Gale vectors, and two points
where they take the values of barycentric dependencies. -/
structure GaleFrame (V : Finset ℝ³) (l m : ℝ³ → ℝ) : Prop where
  hl : IsDepOn V l
  hm : IsDepOn V m
  ne : ∀ t ∈ V, l t ≠ 0 ∨ m t ≠ 0
  base : ∃ D₀ ∈ V, ∃ E₀ ∈ V, l D₀ = -1 ∧ m D₀ = 0 ∧ l E₀ = 0 ∧ m E₀ = -1

/-- Six distinct listed points. -/
theorem exists_six_of_card {V : Finset ℝ³} (h : V.card = 6) :
    ∃ a b c d e f : ℝ³, [a, b, c, d, e, f].Nodup ∧ V = {a, b, c, d, e, f} := by
  classical
  obtain ⟨a, V₁, ha, rfl, h₁⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, V₂, hb, rfl, h₂⟩ := Finset.card_eq_succ.mp h₁
  obtain ⟨c, V₃, hc, rfl, h₃⟩ := Finset.card_eq_succ.mp h₂
  obtain ⟨d, e, f, hde, hdf, hef, rfl⟩ := Finset.card_eq_three.mp h₃
  refine ⟨a, b, c, d, e, f, ?_, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  tauto

/-- An affine functional constant on three of four frame points, with zero
weight on the fourth. -/
theorem inner_bary_eq {N A B C T X : ℝ³} {a b c d k : ℝ}
    (hX : X = a • A + b • B + c • C + d • T) (hs : a + b + c + d = 1)
    (hA : a = 0 ∨ ⟪N, A⟫ = k) (hB : b = 0 ∨ ⟪N, B⟫ = k) (hC : c = 0 ∨ ⟪N, C⟫ = k)
    (hT : d = 0 ∨ ⟪N, T⟫ = k) : ⟪N, X⟫ = k := by
  rw [hX]
  simp only [inner_add_right, real_inner_smul_right]
  have eA : a * (⟪N, A⟫ - k) = 0 := by rcases hA with h | h <;> simp [h]
  have eB : b * (⟪N, B⟫ - k) = 0 := by rcases hB with h | h <;> simp [h]
  have eC : c * (⟪N, C⟫ - k) = 0 := by rcases hC with h | h <;> simp [h]
  have eT : d * (⟪N, T⟫ - k) = 0 := by rcases hT with h | h <;> simp [h]
  linear_combination eA + eB + eC + eT + k * hs

/-- A Gale frame from an independent tetrahedron `ABCT` and the two other points. -/
theorem galeFrame_of_det4 {V : Finset ℝ³} (hS : Six V) {A B C T D₀ E₀ : ℝ³}
    (hV : V = {A, B, C, T, D₀, E₀}) (hnd : [A, B, C, T, D₀, E₀].Nodup)
    (hdet : det4 A B C T ≠ 0) : ∃ l m, GaleFrame V l m := by
  classical
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hAB, hAC, hAT, hAD, hAE⟩, ⟨hBC, hBT, hBD, hBE⟩, ⟨hCT, hCD, hCE⟩, ⟨hTD, hTE⟩, hDE, -⟩ :=
    hnd'
  have hind : AffineIndependent ℝ ![A, B, C, T] := affineIndependent_of_det3 hdet
  obtain ⟨bA, bB, bC, bT, hbs, hbD⟩ := exists_bary hind D₀
  obtain ⟨cA, cB, cC, cT, hcs, hcE⟩ := exists_bary hind E₀
  set l : ℝ³ → ℝ := fun t => if t = A then bA else if t = B then bB else if t = C then bC
    else if t = T then bT else if t = D₀ then -1 else 0 with hl
  set m : ℝ³ → ℝ := fun t => if t = A then cA else if t = B then cB else if t = C then cC
    else if t = T then cT else if t = D₀ then 0 else -1 with hm
  have lA : l A = bA := by simp [hl]
  have lB : l B = bB := by simp [hl, (Ne.symm hAB)]
  have lC : l C = bC := by simp [hl, (Ne.symm hAC), (Ne.symm hBC)]
  have lT : l T = bT := by simp [hl, (Ne.symm hAT), (Ne.symm hBT), (Ne.symm hCT)]
  have lD : l D₀ = -1 := by simp [hl, (Ne.symm hAD), (Ne.symm hBD), (Ne.symm hCD), (Ne.symm hTD)]
  have lE : l E₀ = 0 := by simp [hl, (Ne.symm hAE), (Ne.symm hBE), (Ne.symm hCE), (Ne.symm hTE),
    (Ne.symm hDE)]
  have mA : m A = cA := by simp [hm]
  have mB : m B = cB := by simp [hm, (Ne.symm hAB)]
  have mC : m C = cC := by simp [hm, (Ne.symm hAC), (Ne.symm hBC)]
  have mT : m T = cT := by simp [hm, (Ne.symm hAT), (Ne.symm hBT), (Ne.symm hCT)]
  have mD : m D₀ = 0 := by simp [hm, (Ne.symm hAD), (Ne.symm hBD), (Ne.symm hCD), (Ne.symm hTD)]
  have mE : m E₀ = -1 := by simp [hm, (Ne.symm hAE), (Ne.symm hBE), (Ne.symm hCE), (Ne.symm hTE),
    (Ne.symm hDE)]
  have hsl : ∀ g : ℝ³ → ℝ³, ∑ t ∈ V, g t = g A + g B + g C + g T + g D₀ + g E₀ := fun g => by
    rw [hV]; exact sum_six hnd g
  have hsr : ∀ g : ℝ³ → ℝ, ∑ t ∈ V, g t = g A + g B + g C + g T + g D₀ + g E₀ := fun g => by
    rw [hV]; exact sum_six hnd g
  have hmemV : ∀ x ∈ V, x = A ∨ x = B ∨ x = C ∨ x = T ∨ x = D₀ ∨ x = E₀ := by
    intro x hx; rw [hV] at hx; simpa using hx
  -- a frame point with vanishing Gale vector makes the other five coplanar
  have plane : ∀ X Y Z W : ℝ³, X ∈ V → Y ∈ V → Z ∈ V → X ≠ Y → X ≠ Z → Y ≠ Z →
      (∀ x ∈ V, x ≠ W → x = X ∨ x = Y ∨ x = Z ∨ x = D₀ ∨ x = E₀) → W ∈ V →
      ⟪cross (Y - X) (Z - X), D₀⟫ = ⟪cross (Y - X) (Z - X), X⟫ →
      ⟪cross (Y - X) (Z - X), E₀⟫ = ⟪cross (Y - X) (Z - X), X⟫ → False := by
    intro X Y Z W hX hY hZ hXY hXZ hYZ hsub hW hD hE
    have hN := hS.cross_ne_zero hX hY hZ hXY hXZ hYZ
    apply hS.no5 W hW
    refine coplanar_of_plane hN (c := ⟪cross (Y - X) (Z - X), X⟫) (fun x hx => ?_)
    have hx' := Finset.mem_erase.mp hx
    rcases hsub x hx'.2 hx'.1 with rfl | rfl | rfl | rfl | rfl
    · rfl
    · have := inner_cross_left (x - X) (Z - X); rw [inner_sub_right] at this; linarith
    · have := inner_cross_right (Y - X) (x - X); rw [inner_sub_right] at this; linarith
    · exact hD
    · exact hE
  have hAV : A ∈ V := by rw [hV]; simp
  have hBV : B ∈ V := by rw [hV]; simp
  have hCV : C ∈ V := by rw [hV]; simp
  have hTV : T ∈ V := by rw [hV]; simp
  have hDV : D₀ ∈ V := by rw [hV]; simp
  have hEV : E₀ ∈ V := by rw [hV]; simp
  have kB : ∀ N : ℝ³, ⟪cross (C - B) (T - B), N⟫ = ⟪cross (C - B) (T - B), N⟫ := fun _ => rfl
  refine ⟨l, m, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, D₀, hDV, E₀, hEV, lD, mD, lE, mE⟩
  · rw [hsr, lA, lB, lC, lT, lD, lE]; linarith
  · rw [hsl, lA, lB, lC, lT, lD, lE, hbD]; module
  · rw [hsr, mA, mB, mC, mT, mD, mE]; linarith
  · rw [hsl, mA, mB, mC, mT, mD, mE, hcE]; module
  · intro t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases hmemV t ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lA] at h1; rw [mA] at h2
      have iC := inner_cross_left (C - B) (T - B)
      have iT := inner_cross_right (C - B) (T - B)
      simp only [inner_sub_right] at iC iT
      refine plane B C T t hBV hCV hTV hBC hBT hCT (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inl h1) (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by
          linarith)))
        (inner_bary_eq hcE hcs (Or.inl h2) (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by
          linarith)))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lB] at h1; rw [mB] at h2
      have iC := inner_cross_left (C - A) (T - A)
      have iT := inner_cross_right (C - A) (T - A)
      simp only [inner_sub_right] at iC iT
      refine plane A C T t hAV hCV hTV hAC hAT hCT (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inr rfl) (Or.inl h1) (Or.inr (by linarith)) (Or.inr (by
          linarith)))
        (inner_bary_eq hcE hcs (Or.inr rfl) (Or.inl h2) (Or.inr (by linarith)) (Or.inr (by
          linarith)))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lC] at h1; rw [mC] at h2
      have iB := inner_cross_left (B - A) (T - A)
      have iT := inner_cross_right (B - A) (T - A)
      simp only [inner_sub_right] at iB iT
      refine plane A B T t hAV hBV hTV hAB hAT hBT (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inr rfl) (Or.inr (by linarith)) (Or.inl h1) (Or.inr (by
          linarith)))
        (inner_bary_eq hcE hcs (Or.inr rfl) (Or.inr (by linarith)) (Or.inl h2) (Or.inr (by
          linarith)))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lT] at h1; rw [mT] at h2
      have iB := inner_cross_left (B - A) (C - A)
      have iC := inner_cross_right (B - A) (C - A)
      simp only [inner_sub_right] at iB iC
      refine plane A B C t hAV hBV hCV hAB hAC hBC (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by linarith)) (Or.inl
          h1))
        (inner_bary_eq hcE hcs (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by linarith)) (Or.inl
          h2))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lD] at h1; norm_num at h1
    · rw [mE] at h2; norm_num at h2

/-- Every six-point set in setting (S) has a Gale frame. -/
theorem Six.exists_galeFrame {V : Finset ℝ³} (hS : Six V) : ∃ l m, GaleFrame V l m := by
  obtain ⟨a, b, c, d, e, f, hnd, hV⟩ := exists_six_of_card hS.card
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef, -⟩ :=
    hnd'
  have hN := hS.cross_ne_zero (P := a) (Q := b) (R := c) (by rw [hV]; simp) (by rw [hV]; simp)
    (by rw [hV]; simp) hab hac hbc
  by_cases h4 : det4 a b c d ≠ 0
  · exact galeFrame_of_det4 hS hV hnd h4
  by_cases h5 : det4 a b c e ≠ 0
  · refine galeFrame_of_det4 hS (A := a) (B := b) (C := c) (T := e) (D₀ := d) (E₀ := f)
      (by rw [hV]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) ?_ h5
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    tauto
  by_cases h6 : det4 a b c f ≠ 0
  · refine galeFrame_of_det4 hS (A := a) (B := b) (C := c) (T := f) (D₀ := d) (E₀ := e)
      (by rw [hV]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) ?_ h6
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    tauto
  push Not at h4 h5 h6
  exfalso
  apply hS.noncop
  refine coplanar_of_plane hN (c := ⟪cross (b - a) (c - a), a⟫) (fun x hx => ?_)
  rw [hV] at hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  have ib := inner_cross_left (b - a) (c - a)
  have ic := inner_cross_right (b - a) (c - a)
  simp only [det4] at h4 h5 h6
  simp only [inner_sub_right] at ib ic h4 h5 h6
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

/-- `galeD l m s ·` is nonzero somewhere. -/
theorem GaleFrame.exists_galeD_ne {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hF : GaleFrame V l m)
    {s : ℝ³} (hs : s ∈ V) : ∃ t ∈ V, galeD l m s t ≠ 0 := by
  obtain ⟨D₀, hD, E₀, hE, lD, mD, lE, mE⟩ := hF.base
  rcases hF.ne s hs with h | h
  · exact ⟨E₀, hE, by simp only [galeD, lE, mE]; intro h0; apply h; linarith⟩
  · exact ⟨D₀, hD, by simp only [galeD, lD, mD]; intro h0; apply h; linarith⟩

/-- **(d)** No three Gale vectors are pairwise parallel. -/
theorem GaleFrame.no_three_parallel {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hS : Six V)
    (hF : GaleFrame V l m) {s t u : ℝ³} (hs : s ∈ V) (ht : t ∈ V) (hu : u ∈ V) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u) (h1 : galeD l m s t = 0) (h2 : galeD l m s u = 0) : False := by
  exact hS.no_three_zeros (hF.hl.galeD hF.hm s) (hF.exists_galeD_ne hs) hs ht hu hst hsu htu
    (galeD_self l m s) h1 h2

/-! ### §10.1 (e): facets from Gale signs -/

/-- The affine functional with normal `n` and constant term `c`. -/
private noncomputable def normalAffineFunctional (n : ℝ³) (c : ℝ) : ℝ³ →ᵃ[ℝ] ℝ :=
  (innerₛₗ ℝ n).toAffineMap + AffineMap.const ℝ ℝ³ c

private theorem normalAffineFunctional_apply (n x : ℝ³) (c : ℝ) :
    normalAffineFunctional n c x = ⟪n, x⟫ + c := rfl

/-- A dependency applied to `x ↦ ⟪N, x⟫ - k`. -/
theorem IsDepOn.apply_inner {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) (N : ℝ³) (k : ℝ) :
    ∑ t ∈ V, l t * (⟪N, t⟫ - k) = 0 := by
  have := hl.apply (normalAffineFunctional N (-k))
  simpa only [normalAffineFunctional_apply, ← sub_eq_add_neg] using this

/-- The six-term relation of a Gale dependency `galeD l m s` and a plane function. -/
theorem gale_rel {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    {a b c d e f : ℝ³} (hV : V = {a, b, c, d, e, f}) (hnd : [a, b, c, d, e, f].Nodup)
    (N : ℝ³) (k : ℝ) (s : ℝ³) :
    galeD l m s a * (⟪N, a⟫ - k) + galeD l m s b * (⟪N, b⟫ - k) +
      galeD l m s c * (⟪N, c⟫ - k) + galeD l m s d * (⟪N, d⟫ - k) +
      galeD l m s e * (⟪N, e⟫ - k) + galeD l m s f * (⟪N, f⟫ - k) = 0 := by
  have := (hl.galeD hm s).apply_inner N k
  rwa [hV, sum_six hnd] at this

/-- The plane of three non-collinear points `P Q R`, as `⟪N, x⟫ = ⟪N, P⟫`. -/
theorem plane_three (P Q R : ℝ³) :
    ⟪cross (Q - P) (R - P), Q⟫ - ⟪cross (Q - P) (R - P), P⟫ = 0 ∧
      ⟪cross (Q - P) (R - P), R⟫ - ⟪cross (Q - P) (R - P), P⟫ = 0 := by
  have h1 := inner_cross_left (Q - P) (R - P)
  have h2 := inner_cross_right (Q - P) (R - P)
  rw [inner_sub_right] at h1 h2
  exact ⟨h1, h2⟩

/-- If a plane function vanishes on all six points, `V` is coplanar. -/
theorem Six.plane_contra {V : Finset ℝ³} (hS : Six V) {a b c d e f : ℝ³}
    (hV : V = {a, b, c, d, e, f}) {N : ℝ³} (hN : N ≠ 0) {k : ℝ} (ha : ⟪N, a⟫ - k = 0)
    (hb : ⟪N, b⟫ - k = 0) (hc : ⟪N, c⟫ - k = 0) (hd : ⟪N, d⟫ - k = 0) (he : ⟪N, e⟫ - k = 0)
    (hf : ⟪N, f⟫ - k = 0) : False := by
  apply hS.noncop
  refine coplanar_of_plane hN (c := k) (fun x hx => ?_)
  rw [hV] at hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

/-- A triangle facet from three negative Gale determinants of its complement. -/
theorem isFacetTriangle_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {P Q R X Y Z : ℝ³} (hV : V = {P, Q, R, X, Y, Z})
    (hnd : [P, Q, R, X, Y, Z].Nodup) (h₁ : galeD l m X Y < 0) (h₂ : galeD l m Y Z < 0)
    (h₃ : galeD l m Z X < 0) : IsFacetTriangle V P Q R := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hPQ, hPR, hPX, hPY, hPZ⟩, ⟨hQR, hQX, hQY, hQZ⟩, ⟨hRX, hRY, hRZ⟩, ⟨hXY, hXZ⟩, hYZ, -⟩ :=
    hnd'
  have hN := hS.cross_ne_zero (P := P) (Q := Q) (R := R) (by rw [hV]; simp) (by rw [hV]; simp)
    (by rw [hV]; simp) hPQ hPR hQR
  set N := cross (Q - P) (R - P) with hNdef
  set k := ⟪N, P⟫ with hk
  obtain ⟨gQ, gR⟩ := plane_three P Q R
  rw [← hNdef, ← hk] at gQ gR
  have gP : ⟪N, P⟫ - k = 0 := sub_self _
  have e1 := gale_rel hl hm hV hnd N k X
  have e2 := gale_rel hl hm hV hnd N k Y
  rw [gP, gQ, gR, galeD_self] at e1
  rw [gP, gQ, gR, galeD_self] at e2
  rw [galeD_anti l m Z X] at e1
  rw [galeD_anti l m X Y] at e2
  set p := galeD l m X Y
  set q := galeD l m Y Z
  set r := galeD l m Z X
  set fX := ⟪N, X⟫ - k
  set fY := ⟪N, Y⟫ - k
  set fZ := ⟪N, Z⟫ - k
  -- `p fY = r fZ` and `p fX = q fZ`
  have r1 : p * fY = r * fZ := by linarith
  have r2 : p * fX = q * fZ := by linarith
  have hmem : ∀ x ∈ V, x ≠ P → x ≠ Q → x ≠ R → x = X ∨ x = Y ∨ x = Z := by
    intro x hx h1 h2 h3
    rw [hV] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  rcases lt_trichotomy fZ 0 with hZ | hZ | hZ
  · have hY : fY < 0 := by nlinarith
    have hX : fX < 0 := by nlinarith
    refine ⟨normalAffineFunctional N (-k),
      by simp only [normalAffineFunctional_apply]; linarith,
      by simp only [normalAffineFunctional_apply]; linarith,
      by simp only [normalAffineFunctional_apply]; linarith, ?_⟩
    intro x hx h1 h2 h3
    simp only [normalAffineFunctional_apply]
    rcases hmem x hx h1 h2 h3 with rfl | rfl | rfl <;> linarith
  · exfalso
    have hY : fY = 0 := by
      rw [hZ, mul_zero] at r1; exact (mul_eq_zero.mp r1).resolve_left h₁.ne
    have hX : fX = 0 := by
      rw [hZ, mul_zero] at r2; exact (mul_eq_zero.mp r2).resolve_left h₁.ne
    exact hS.plane_contra hV hN gP gQ gR hX hY hZ
  · have hY : 0 < fY := by nlinarith
    have hX : 0 < fX := by nlinarith
    refine ⟨normalAffineFunctional (-N) k,
      by simp only [normalAffineFunctional_apply, inner_neg_left]; linarith,
      by simp only [normalAffineFunctional_apply, inner_neg_left]; linarith,
      by simp only [normalAffineFunctional_apply, inner_neg_left]; linarith, ?_⟩
    intro x hx h1 h2 h3
    simp only [normalAffineFunctional_apply, inner_neg_left]
    rcases hmem x hx h1 h2 h3 with rfl | rfl | rfl <;> linarith

/-- A quadrilateral facet from a parallel opposite complementary pair. -/
theorem isFacet_quad_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {P Q R Z X Y : ℝ³} (hV : V = {P, Q, R, Z, X, Y})
    (hnd : [P, Q, R, Z, X, Y].Nodup) (h₀ : galeD l m X Y = 0)
    (h₁ : galeD l m X Z * galeD l m Y Z < 0) : IsFacet V {P, Q, R, Z} := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hPQ, hPR, hPZ, hPX, hPY⟩, ⟨hQR, hQZ, hQX, hQY⟩, ⟨hRZ, hRX, hRY⟩, ⟨hZX, hZY⟩, hXY, -⟩ :=
    hnd'
  have hN := hS.cross_ne_zero (P := P) (Q := Q) (R := R) (by rw [hV]; simp) (by rw [hV]; simp)
    (by rw [hV]; simp) hPQ hPR hQR
  set N := cross (Q - P) (R - P) with hNdef
  set k := ⟪N, P⟫ with hk
  obtain ⟨gQ, gR⟩ := plane_three P Q R
  rw [← hNdef, ← hk] at gQ gR
  have gP : ⟪N, P⟫ - k = 0 := sub_self _
  have e1 := gale_rel hl hm hV hnd N k X
  have e2 := gale_rel hl hm hV hnd N k Z
  rw [gP, gQ, gR, galeD_self, h₀] at e1
  rw [gP, gQ, gR, galeD_self, galeD_anti l m X Z, galeD_anti l m Y Z] at e2
  have hXZ : galeD l m X Z ≠ 0 := by intro h0; rw [h0, zero_mul] at h₁; exact lt_irrefl 0 h₁
  have gZ : ⟪N, Z⟫ - k = 0 := by
    have : galeD l m X Z * (⟪N, Z⟫ - k) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hXZ
  rw [gZ, mul_zero] at e2
  set a := galeD l m X Z
  set b := galeD l m Y Z
  set fX := ⟪N, X⟫ - k
  set fY := ⟪N, Y⟫ - k
  have r : a * fX + b * fY = 0 := by linarith
  have hmem : ∀ x ∈ V, x ∉ ({P, Q, R, Z} : Finset ℝ³) → x = X ∨ x = Y := by
    intro x hx hxF
    rw [hV] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hxF
    tauto
  have hF : ∀ x ∈ ({P, Q, R, Z} : Finset ℝ³), ⟪N, x⟫ - k = 0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have key : (a * b) * fY = -(a * a) * fX := by linear_combination a * r
  have ha2 : 0 < a * a := mul_self_pos.mpr hXZ
  rcases lt_trichotomy fX 0 with hX | hX | hX
  · have hY : fY < 0 := by
      by_contra hc; push Not at hc
      have h1 : (a * b) * fY ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h₁.le hc
      have h2 : 0 < -(a * a) * fX := by nlinarith
      linarith
    refine ⟨normalAffineFunctional N (-k), fun x hx => ?_, fun x hx hxF => ?_⟩
    · simp only [normalAffineFunctional_apply]; linarith [hF x hx]
    · simp only [normalAffineFunctional_apply]
      rcases hmem x hx hxF with rfl | rfl <;> linarith
  · exfalso
    have hY : fY = 0 := by
      rw [hX, mul_zero, zero_add] at r
      exact (mul_eq_zero.mp r).resolve_left (by intro h0; rw [h0, mul_zero] at h₁; linarith)
    exact hS.plane_contra hV hN gP gQ gR gZ hX hY
  · have hY : 0 < fY := by
      by_contra hc; push Not at hc
      have h1 : 0 ≤ (a * b) * fY := mul_nonneg_of_nonpos_of_nonpos h₁.le hc
      have h2 : -(a * a) * fX < 0 := by nlinarith
      linarith
    refine ⟨normalAffineFunctional (-N) k, fun x hx => ?_, fun x hx hxF => ?_⟩
    · simp only [normalAffineFunctional_apply, inner_neg_left]; linarith [hF x hx]
    · simp only [normalAffineFunctional_apply, inner_neg_left]
      rcases hmem x hx hxF with rfl | rfl <;> linarith

/-- The complement of a non-parallel pair is an independent tetrahedron. -/
theorem affineIndependent_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {A B C T X Y : ℝ³} (hV : V = {A, B, C, T, X, Y})
    (hnd : [A, B, C, T, X, Y].Nodup) (h : galeD l m X Y ≠ 0) :
    AffineIndependent ℝ ![A, B, C, T] := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hAB, hAC, hAT, hAX, hAY⟩, ⟨hBC, hBT, hBX, hBY⟩, ⟨hCT, hCX, hCY⟩, ⟨hTX, hTY⟩, hXY, -⟩ :=
    hnd'
  have hN := hS.cross_ne_zero (P := A) (Q := B) (R := C) (by rw [hV]; simp) (by rw [hV]; simp)
    (by rw [hV]; simp) hAB hAC hBC
  apply affineIndependent_of_det3
  intro hdet
  set N := cross (B - A) (C - A) with hNdef
  set k := ⟪N, A⟫ with hk
  obtain ⟨gB, gC⟩ := plane_three A B C
  rw [← hNdef, ← hk] at gB gC
  have gA : ⟪N, A⟫ - k = 0 := sub_self _
  have gT : ⟪N, T⟫ - k = 0 := by
    have : det3 (B - A) (C - A) (T - A) = ⟪N, T⟫ - k := by
      simp only [det3, hNdef, hk, inner_sub_right]
    rw [← this, hdet]
  have e1 := gale_rel hl hm hV hnd N k X
  have e2 := gale_rel hl hm hV hnd N k Y
  rw [gA, gB, gC, gT, galeD_self] at e1
  rw [gA, gB, gC, gT, galeD_self] at e2
  have gY : ⟪N, Y⟫ - k = 0 := by
    have : galeD l m X Y * (⟪N, Y⟫ - k) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left h
  rw [gY] at e2
  have gX : ⟪N, X⟫ - k = 0 := by
    have : galeD l m Y X * (⟪N, X⟫ - k) = 0 := by linarith
    refine (mul_eq_zero.mp this).resolve_left ?_
    rw [galeD_anti]; exact neg_ne_zero.mpr h
  exact hS.plane_contra hV hN gA gB gC gT gX gY

/-! ### Lemma 10.1: a 2+4 split -/

/-- `s, t` are an O-pair: antiparallel Gale vectors. -/
def IsOPair (l m : ℝ³ → ℝ) (s t : ℝ³) : Prop :=
  s ≠ t ∧ galeD l m s t = 0 ∧ l s * l t + m s * m t < 0

/-- Perturbing a dependency `M` by `δ ν` (`ν < 0` where `M` vanishes): if `M`
is positive at exactly two points, this is a 2+4 split. -/
theorem exists_split_of_perturb {V : Finset ℝ³} {M ν : ℝ³ → ℝ} (hM : IsDepOn V M)
    (hν : IsDepOn V ν) (hνZ : ∀ t ∈ V, M t = 0 → ν t < 0)
    (h2 : (V.filter (fun t => 0 < M t)).card = 2) :
    ∃ D ∈ V, ∃ E ∈ V, D ≠ E ∧ ∃ μ : ℝ³ → ℝ, IsDepOn V μ ∧ 0 < μ D ∧ 0 < μ E ∧
      ∀ x ∈ V, x ≠ D → x ≠ E → μ x < 0 := by
  classical
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t ∈ V,
      (0 < M t → 0 < M t + δ * ν t) ∧ (M t < 0 → M t + δ * ν t < 0) := by
    rw [Filter.eventually_all_finset]
    intro t _
    have hc : Tendsto (fun δ : ℝ => M t + δ * ν t) (𝓝[>] 0) (𝓝 (M t)) := by
      have hcont : Continuous (fun δ : ℝ => M t + δ * ν t) := by fun_prop
      have := hcont.tendsto 0
      simp only [zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    rcases lt_trichotomy (M t) 0 with h | h | h
    · exact (hc.eventually (Iio_mem_nhds h)).mono fun δ hδ =>
        ⟨fun h' => absurd h' (not_lt.mpr h.le), fun _ => hδ⟩
    · exact Filter.Eventually.of_forall fun δ =>
        ⟨fun h' => absurd h' (by rw [h]; exact lt_irrefl 0),
          fun h' => absurd h' (by rw [h]; exact lt_irrefl 0)⟩
    · exact (hc.eventually (Ioi_mem_nhds h)).mono fun δ hδ =>
        ⟨fun _ => hδ, fun h' => absurd h' (not_lt.mpr h.le)⟩
  obtain ⟨δ, hδ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0 : 0 < δ := hδpos
  obtain ⟨D, E, hDE, hPE⟩ := Finset.card_eq_two.mp h2
  have hD : D ∈ V.filter (fun t => 0 < M t) := by rw [hPE]; simp
  have hE : E ∈ V.filter (fun t => 0 < M t) := by rw [hPE]; simp
  rw [Finset.mem_filter] at hD hE
  have hμ : IsDepOn V (fun t => 1 * M t + δ * ν t) := hM.comb hν 1 δ
  refine ⟨D, hD.1, E, hE.1, hDE, fun t => 1 * M t + δ * ν t, hμ, ?_, ?_, ?_⟩
  · simp only [one_mul]; exact ((hδ D hD.1).1 hD.2)
  · simp only [one_mul]; exact ((hδ E hE.1).1 hE.2)
  · intro x hx hxD hxE
    simp only [one_mul]
    have hxP : x ∉ V.filter (fun t => 0 < M t) := by rw [hPE]; simp [hxD, hxE]
    rw [Finset.mem_filter] at hxP
    have hMx : M x ≤ 0 := not_lt.mp (fun h => hxP ⟨hx, h⟩)
    rcases hMx.lt_or_eq with h | h
    · exact (hδ x hx).2 h
    · rw [h, zero_add]; exact mul_neg_of_pos_of_neg hδ0 (hνZ x hx h)

/-- **Lemma 10.1.** A point without an O-partner gives a 2+4 split. -/
theorem exists_split_of_no_partner {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) {i : ℝ³} (hi : i ∈ V) (hno : ∀ j ∈ V, ¬ IsOPair l m i j) :
    ∃ D ∈ V, ∃ E ∈ V, D ≠ E ∧ ∃ μ : ℝ³ → ℝ, IsDepOn V μ ∧ 0 < μ D ∧ 0 < μ E ∧
      ∀ x ∈ V, x ≠ D → x ≠ E → μ x < 0 := by
  classical
  have hl := hF.hl
  have hm := hF.hm
  set L : ℝ³ → ℝ := galeD l m i with hLdef
  set ν : ℝ³ → ℝ := fun t => -(l i * l t + m i * m t) with hνdef
  have hL : IsDepOn V L := hl.galeD hm i
  have hν : IsDepOn V ν := hl.nu hm i
  have hgi2 : 0 < l i * l i + m i * m i := by
    rcases hF.ne i hi with h | h
    · have := mul_self_pos.mpr h; nlinarith [mul_self_nonneg (m i)]
    · have := mul_self_pos.mpr h; nlinarith [mul_self_nonneg (l i)]
  have hνZ : ∀ t ∈ V, L t = 0 → ν t < 0 := by
    intro t ht hLt
    by_cases hti : t = i
    · rw [hti]; simp only [hνdef]; linarith
    · have hge : 0 ≤ l i * l t + m i * m t := by
        by_contra hc; push Not at hc; exact hno t ht ⟨Ne.symm hti, hLt, hc⟩
      have hne : l i * l t + m i * m t ≠ 0 := by
        intro h0
        have hLt' : l i * m t - m i * l t = 0 := hLt
        have e1 : (l i * l i + m i * m i) * l t = 0 := by
          linear_combination l i * h0 - m i * hLt'
        have e2 : (l i * l i + m i * m i) * m t = 0 := by
          linear_combination m i * h0 + l i * hLt'
        rcases hF.ne t ht with h | h
        · exact h ((mul_eq_zero.mp e1).resolve_left hgi2.ne')
        · exact h ((mul_eq_zero.mp e2).resolve_left hgi2.ne')
      simp only [hνdef]; linarith [lt_of_le_of_ne hge (Ne.symm hne)]
  have hLne : ∃ t ∈ V, L t ≠ 0 := hF.exists_galeD_ne hi
  -- the three sign classes of `L`
  have hcard : (V.filter (fun t => 0 < L t)).card + (V.filter (fun t => L t < 0)).card +
      (V.filter (fun t => L t = 0)).card = 6 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := V) (fun t => 0 < L t)
    have h2 := Finset.card_filter_add_card_filter_not (s := V.filter (fun t => ¬ 0 < L t))
      (fun t => L t < 0)
    have e1 : (V.filter (fun t => ¬ 0 < L t)).filter (fun t => L t < 0) =
        V.filter (fun t => L t < 0) := by
      ext t; simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, not_lt.mpr h.2.le⟩, h.2⟩⟩
    have e2 : (V.filter (fun t => ¬ 0 < L t)).filter (fun t => ¬ L t < 0) =
        V.filter (fun t => L t = 0) := by
      ext t; simp only [Finset.mem_filter, not_lt]
      exact ⟨fun h => ⟨h.1.1, le_antisymm h.1.2 h.2⟩,
        fun h => ⟨⟨h.1, h.2.le⟩, h.2.ge⟩⟩
    rw [e1, e2] at h2
    rw [← hS.card]; omega
  have hZ : (V.filter (fun t => L t = 0)).card ≤ 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hc
    rw [Finset.mem_filter] at ha hb hc'
    exact hS.no_three_zeros hL hLne ha.1 hb.1 hc'.1 hab hac hbc ha.2 hb.2 hc'.2
  have hiZ : 1 ≤ (V.filter (fun t => L t = 0)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, galeD_self l m i⟩⟩
  have hP : 2 ≤ (V.filter (fun t => 0 < L t)).card := by
    by_contra hc
    push Not at hc
    have h1 := Finset.card_le_one.mp (Nat.lt_succ_iff.mp hc)
    by_cases hv : ∃ v ∈ V, 0 < L v
    · obtain ⟨v, hv, hLv⟩ := hv
      refine hS.not_single_neg hL.neg hv (by linarith) (fun t ht htv => ?_)
      have : ¬ 0 < L t := fun h => htv (h1 t (Finset.mem_filter.mpr ⟨ht, h⟩) v
        (Finset.mem_filter.mpr ⟨hv, hLv⟩))
      linarith [not_lt.mp this]
    · push Not at hv
      obtain ⟨t, ht, hLt⟩ := hLne
      exact hLt (hL.eq_zero_of_nonpos hv t ht)
  have hN : 2 ≤ (V.filter (fun t => L t < 0)).card := by
    by_contra hc
    push Not at hc
    have h1 := Finset.card_le_one.mp (Nat.lt_succ_iff.mp hc)
    by_cases hv : ∃ v ∈ V, L v < 0
    · obtain ⟨v, hv, hLv⟩ := hv
      refine hS.not_single_neg hL hv hLv (fun t ht htv => ?_)
      exact not_lt.mp fun h => htv (h1 t (Finset.mem_filter.mpr ⟨ht, h⟩) v
        (Finset.mem_filter.mpr ⟨hv, hLv⟩))
    · push Not at hv
      obtain ⟨t, ht, hLt⟩ := hLne
      have := hL.neg.eq_zero_of_nonpos (fun t ht => by linarith [hv t ht]) t ht
      exact hLt (by linarith)
  rcases (show (V.filter (fun t => 0 < L t)).card = 2 ∨ (V.filter (fun t => L t < 0)).card = 2
    by omega) with h2 | h2
  · exact exists_split_of_perturb hL hν hνZ h2
  · refine exists_split_of_perturb hL.neg hν (fun t ht h0 => hνZ t ht (by linarith)) ?_
    have : V.filter (fun t => 0 < -L t) = V.filter (fun t => L t < 0) := by
      ext t; simp only [Finset.mem_filter, neg_pos]
    rw [this]; exact h2

/-! ### Proposition 10.2: prisms -/

theorem IsOPair.symm {l m : ℝ³ → ℝ} {s t : ℝ³} (h : IsOPair l m s t) : IsOPair l m t s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, ?_, by linarith [mul_comm (l s) (l t), mul_comm (m s) (m t)]⟩
  rw [galeD_anti, h2, neg_zero]

/-- The Gale vector of an O-partner is a negative multiple. -/
theorem IsOPair.coeff {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hF : GaleFrame V l m) {s t : ℝ³}
    (hs : s ∈ V) (h : IsOPair l m s t) : ∃ a, 0 < a ∧ l t = -a * l s ∧ m t = -a * m s := by
  obtain ⟨-, h2, h3⟩ := h
  have hn : 0 < l s * l s + m s * m s := by
    rcases hF.ne s hs with h | h
    · have := mul_self_pos.mpr h; nlinarith [mul_self_nonneg (m s)]
    · have := mul_self_pos.mpr h; nlinarith [mul_self_nonneg (l s)]
  have h2' : l s * m t - m s * l t = 0 := h2
  refine ⟨-(l s * l t + m s * m t) / (l s * l s + m s * m s), div_pos (by linarith) hn, ?_, ?_⟩
  · rw [neg_div, neg_neg, div_mul_eq_mul_div, eq_div_iff hn.ne']
    linear_combination (-(m s)) * h2'
  · rw [neg_div, neg_neg, div_mul_eq_mul_div, eq_div_iff hn.ne']
    linear_combination l s * h2'

/-- O-partners are unique. -/
theorem partner_unique {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ} (hF : GaleFrame V l m)
    {s t u : ℝ³} (hs : s ∈ V) (ht : t ∈ V) (hu : u ∈ V) (h1 : IsOPair l m s t)
    (h2 : IsOPair l m s u) : t = u := by
  by_contra htu
  exact hF.no_three_parallel hS hs ht hu h1.1 h2.1 htu h1.2.1 h2.2.1

theorem galeD_pair {l m : ℝ³ → ℝ} {X X' : ℝ³} {a : ℝ} (hl : l X' = -a * l X)
    (hm : m X' = -a * m X) (s : ℝ³) : galeD l m s X' = -a * galeD l m s X := by
  simp only [galeD, hl, hm]; ring

/-- If every point has an O-partner, the six points split into three O-pairs. -/
theorem exists_three_pairs {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ} (hF : GaleFrame V l m)
    (hall : ∀ i ∈ V, ∃ j ∈ V, IsOPair l m i j) :
    ∃ A A' B B' C C' : ℝ³, V = {A, A', B, B', C, C'} ∧ [A, A', B, B', C, C'].Nodup ∧
      IsOPair l m A A' ∧ IsOPair l m B B' ∧ IsOPair l m C C' := by
  classical
  obtain ⟨A, hA⟩ : V.Nonempty := Finset.card_pos.mp (by rw [hS.card]; norm_num)
  obtain ⟨A', hA', hAA'⟩ := hall A hA
  -- `t` has at most one partner, seen from either side
  have uniq : ∀ s ∈ V, ∀ t ∈ V, ∀ u ∈ V, IsOPair l m s t → IsOPair l m u t → s = u :=
    fun s hs t ht u hu h1 h2 => partner_unique hS hF ht hs hu h1.symm h2.symm
  have hAA'ne := hAA'.1
  have hV₁ : ((V.erase A).erase A').card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hAA'ne.symm, hA'⟩),
      Finset.card_erase_of_mem hA, hS.card]
  obtain ⟨B, hB₁⟩ : ((V.erase A).erase A').Nonempty :=
    Finset.card_pos.mp (by rw [hV₁]; norm_num)
  obtain ⟨hBA', hBA, hB⟩ : B ≠ A' ∧ B ≠ A ∧ B ∈ V := by
    simpa only [Finset.mem_erase] using hB₁
  obtain ⟨B', hB', hBB'⟩ := hall B hB
  have hB'A : B' ≠ A := fun h => hBA' (partner_unique hS hF hA hB hA' (h ▸ hBB'.symm) hAA')
  have hB'A' : B' ≠ A' := fun h => hBA (uniq B hB A' hA' A hA (h ▸ hBB') hAA')
  have hBB'ne := hBB'.1
  have hV₂ : ((((V.erase A).erase A').erase B).erase B').card = 2 := by
    rw [Finset.card_erase_of_mem (by
          simp only [Finset.mem_erase]
          exact ⟨hBB'ne.symm, hB'A', hB'A, hB'⟩),
      Finset.card_erase_of_mem hB₁, hV₁]
  obtain ⟨C, C₂, hCC₂, hV₂eq⟩ := Finset.card_eq_two.mp hV₂
  have hmem₂ : ∀ x, x ∈ ({C, C₂} : Finset ℝ³) ↔ x ≠ B' ∧ x ≠ B ∧ x ≠ A' ∧ x ≠ A ∧ x ∈ V := by
    intro x; rw [← hV₂eq]; simp only [Finset.mem_erase]
  obtain ⟨hCB', hCB, hCA', hCA, hC⟩ := (hmem₂ C).mp (by simp)
  obtain ⟨hC₂B', hC₂B, hC₂A', hC₂A, hC₂⟩ := (hmem₂ C₂).mp (by simp)
  obtain ⟨C', hC', hCC'⟩ := hall C hC
  have hC'A : C' ≠ A := fun h => hCA' (partner_unique hS hF hA hC hA' (h ▸ hCC'.symm) hAA')
  have hC'A' : C' ≠ A' := fun h => hCA (uniq C hC A' hA' A hA (h ▸ hCC') hAA')
  have hC'B : C' ≠ B := fun h => hCB' (partner_unique hS hF hB hC hB' (h ▸ hCC'.symm) hBB')
  have hC'B' : C' ≠ B' := fun h => hCB (uniq C hC B' hB' B hB (h ▸ hCC') hBB')
  have hC'C₂ : C' = C₂ := by
    have := (hmem₂ C').mpr ⟨hC'B', hC'B, hC'A', hC'A, hC'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hCC'.1.symm
    · exact h
  subst hC'C₂
  refine ⟨A, A', B, B', C, C', ?_, ?_, hAA', hBB', hCC'⟩
  · ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases h1 : x = A; · exact Or.inl h1
      by_cases h2 : x = A'; · exact Or.inr (Or.inl h2)
      by_cases h3 : x = B; · exact Or.inr (Or.inr (Or.inl h3))
      by_cases h4 : x = B'; · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      have := (hmem₂ x).mpr ⟨h4, h3, h2, h1, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨hAA'ne, Ne.symm hBA, Ne.symm hB'A, Ne.symm hCA, Ne.symm hC'A⟩,
      ⟨Ne.symm hBA', Ne.symm hB'A', Ne.symm hCA', Ne.symm hC'A'⟩,
      ⟨hBB'ne, Ne.symm hCB, Ne.symm hC'B⟩, ⟨Ne.symm hCB', Ne.symm hC'B'⟩, hCC'.1⟩

/-- A frustum pair `X' = O + r (X - O)` with the far point first. -/
theorem pair_frustum {O X X' : ℝ³} {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (h : X' = O + r • (X - O)) : ∃ F N : ℝ³, ∃ α : ℝ, (∀ x, (x = X ∨ x = X') ↔ (x = F ∨ x = N)) ∧
      0 < α ∧ α < 1 ∧ N = O + α • (F - O) := by
  rcases lt_or_gt_of_ne hr1 with h1 | h1
  · exact ⟨X, X', r, fun x => Iff.rfl, hr, h1, h⟩
  · refine ⟨X', X, r⁻¹, fun x => or_comm, inv_pos.mpr hr, inv_lt_one_of_one_lt₀ h1, ?_⟩
    rw [h, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, add_sub_cancel]

/-- A parallel pair `X' = X + s w` with the positive shift. -/
theorem pair_parallel {X X' w : ℝ³} {s : ℝ} (hs : s ≠ 0) (h : X' = X + s • w) :
    ∃ F N : ℝ³, ∃ σ : ℝ, (∀ x, (x = X ∨ x = X') ↔ (x = F ∨ x = N)) ∧ 0 < σ ∧
      N = F + σ • w := by
  rcases lt_or_gt_of_ne hs with h1 | h1
  · refine ⟨X', X, -s, fun x => or_comm, by linarith, ?_⟩
    rw [h, neg_smul, add_neg_cancel_right]
  · exact ⟨X, X', s, fun x => Iff.rfl, h1, h⟩

theorem finset_of_pairs {A A' B B' C C' F₁ N₁ F₂ N₂ F₃ N₃ : ℝ³}
    (h₁ : ∀ x, (x = A ∨ x = A') ↔ (x = F₁ ∨ x = N₁))
    (h₂ : ∀ x, (x = B ∨ x = B') ↔ (x = F₂ ∨ x = N₂))
    (h₃ : ∀ x, (x = C ∨ x = C') ↔ (x = F₃ ∨ x = N₃)) :
    ({A, A', B, B', C, C'} : Finset ℝ³) = {F₁, F₂, F₃, N₁, N₂, N₃} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  calc (x = A ∨ x = A' ∨ x = B ∨ x = B' ∨ x = C ∨ x = C') ↔
        ((x = A ∨ x = A') ∨ (x = B ∨ x = B') ∨ (x = C ∨ x = C')) := by simp only [or_assoc]
    _ ↔ ((x = F₁ ∨ x = N₁) ∨ (x = F₂ ∨ x = N₂) ∨ (x = F₃ ∨ x = N₃)) := by rw [h₁, h₂, h₃]
    _ ↔ (x = F₁ ∨ x = F₂ ∨ x = F₃ ∨ x = N₁ ∨ x = N₂ ∨ x = N₃) := by
        constructor
        · rintro ((h | h) | (h | h) | (h | h)) <;> simp only [h, true_or, or_true]
        · rintro (h | h | h | h | h | h) <;> simp only [h, true_or, or_true]

/-- Pair memberships and distinctness of the representatives. -/
theorem pair_mem {A A' F N : ℝ³} (h : ∀ x, (x = A ∨ x = A') ↔ (x = F ∨ x = N)) :
    (F = A ∨ F = A') ∧ (N = A ∨ N = A') :=
  ⟨(h F).mpr (Or.inl rfl), (h N).mpr (Or.inr rfl)⟩

/-- **Parallel prisms**: lateral edges `A' - A = w`, `B' - B = s_B w`, `C' - C = s_C w`. -/
theorem isRupert_parallel_of_shifts {V : Finset ℝ³} (hS : Six V) {A A' B B' C C' w : ℝ³}
    (hV : V = {A, A', B, B', C, C'}) (hnd : [A, A', B, B', C, C'].Nodup) {sB sC : ℝ}
    (hsB : sB ≠ 0) (hsC : sC ≠ 0) (hA' : A' = A + w) (hB' : B' = B + sB • w)
    (hC' : C' = C + sC • w) : IsRupert V := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ :=
    hnd'
  obtain ⟨FB, NB, σB, hpB, hσB, hNB⟩ := pair_parallel hsB hB'
  obtain ⟨FC, NC, σC, hpC, hσC, hNC⟩ := pair_parallel hsC hC'
  have hV' : V = {A, FB, FC, A', NB, NC} := by
    rw [hV]; exact finset_of_pairs (fun x => Iff.rfl) hpB hpC
  obtain ⟨hFB, -⟩ := pair_mem hpB
  obtain ⟨hFC, -⟩ := pair_mem hpC
  have hAFB : A ≠ FB := by rcases hFB with h | h <;> rw [h] <;> assumption
  have hAFC : A ≠ FC := by rcases hFC with h | h <;> rw [h] <;> assumption
  have hFBFC : FB ≠ FC := by
    rcases hFB with h | h <;> rcases hFC with h' | h' <;> rw [h, h'] <;> assumption
  have memV : ∀ x, (x = A ∨ x = A' ∨ x = B ∨ x = B' ∨ x = C ∨ x = C') → x ∈ V := by
    intro x hx; rw [hV]; simpa using hx
  have hN := hS.cross_ne_zero (memV A (by simp)) (memV FB (by tauto)) (memV FC (by tauto))
    hAFB hAFC hFBFC
  have hind : AffineIndependent ℝ ![A, FB, FC, A + w] := by
    apply affineIndependent_of_det3
    rw [add_sub_cancel_left]
    intro hdet
    set N := cross (FB - A) (FC - A) with hNdef
    set k := ⟪N, A⟫
    obtain ⟨g2, g3⟩ := plane_three A FB FC
    rw [← hNdef] at g2 g3
    have hw : ⟪N, w⟫ = 0 := hdet
    have g1 : ⟪N, A⟫ - k = 0 := sub_self _
    refine hS.plane_contra hV' hN g1 g2 g3 ?_ ?_ ?_
    · rw [hA', inner_add_right, hw]; linarith
    · rw [hNB, inner_add_right, real_inner_smul_right, hw]; linarith
    · rw [hNC, inner_add_right, real_inner_smul_right, hw]; linarith
  by_cases htr : σB = 1 ∧ σC = 1
  · obtain ⟨rfl, rfl⟩ := htr
    rw [one_smul] at hNB hNC
    rw [hV', hA', hNB, hNC]
    exact isRupert_translationPrism_all A FB FC w hind
  · have := isRupert_parallelPrism A FB FC w hind 1 σB σC one_pos hσB hσC
      (fun h => htr ⟨h.1.symm, h.2 ▸ h.1.symm⟩)
    rwa [one_smul, ← hA', ← hNB, ← hNC, ← hV'] at this

/-- **Frustums**: three lateral lines through `O`, `X' = O + r_X (X - O)`. -/
theorem isRupert_frustum_of_ratios {V : Finset ℝ³} (hS : Six V) {A A' B B' C C' O : ℝ³}
    (hV : V = {A, A', B, B', C, C'}) (hnd : [A, A', B, B', C, C'].Nodup) {rA rB rC : ℝ}
    (hrA : 0 < rA) (hrB : 0 < rB) (hrC : 0 < rC) (hrA1 : rA ≠ 1) (hrB1 : rB ≠ 1) (hrC1 : rC ≠ 1)
    (hA' : A' = O + rA • (A - O)) (hB' : B' = O + rB • (B - O)) (hC' : C' = O + rC • (C - O)) :
    IsRupert V := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ :=
    hnd'
  obtain ⟨FA, NA, α, hpA, hα, hα1, hNA⟩ := pair_frustum hrA hrA1 hA'
  obtain ⟨FB, NB, β, hpB, hβ, hβ1, hNB⟩ := pair_frustum hrB hrB1 hB'
  obtain ⟨FC, NC, γ, hpC, hγ, hγ1, hNC⟩ := pair_frustum hrC hrC1 hC'
  have hV' : V = {FA, FB, FC, NA, NB, NC} := by rw [hV]; exact finset_of_pairs hpA hpB hpC
  obtain ⟨hFA, -⟩ := pair_mem hpA
  obtain ⟨hFB, -⟩ := pair_mem hpB
  obtain ⟨hFC, -⟩ := pair_mem hpC
  have hAB : FA ≠ FB := by
    rcases hFA with h | h <;> rcases hFB with h' | h' <;> rw [h, h'] <;> assumption
  have hAC : FA ≠ FC := by
    rcases hFA with h | h <;> rcases hFC with h' | h' <;> rw [h, h'] <;> assumption
  have hBC : FB ≠ FC := by
    rcases hFB with h | h <;> rcases hFC with h' | h' <;> rw [h, h'] <;> assumption
  have memV : ∀ x, (x = A ∨ x = A' ∨ x = B ∨ x = B' ∨ x = C ∨ x = C') → x ∈ V := by
    intro x hx; rw [hV]; simpa using hx
  have hN := hS.cross_ne_zero (memV FA (by tauto)) (memV FB (by tauto)) (memV FC (by tauto))
    hAB hAC hBC
  have hind : AffineIndependent ℝ ![FA, FB, FC, O] := by
    apply affineIndependent_of_det3
    intro hdet
    set N := cross (FB - FA) (FC - FA) with hNdef
    set k := ⟪N, FA⟫
    obtain ⟨g2, g3⟩ := plane_three FA FB FC
    rw [← hNdef] at g2 g3
    have g1 : ⟪N, FA⟫ - k = 0 := sub_self _
    have gO : ⟪N, O⟫ - k = 0 := by
      have : det3 (FB - FA) (FC - FA) (O - FA) = ⟪N, O⟫ - k := by
        simp only [det3, hNdef, inner_sub_right]; rfl
      rw [← this, hdet]
    have near : ∀ (F : ℝ³) (t : ℝ), ⟪N, F⟫ - k = 0 → ⟪N, O + t • (F - O)⟫ - k = 0 := by
      intro F t hF
      rw [inner_add_right, real_inner_smul_right, inner_sub_right]
      linear_combination (1 - t) * gO + t * hF
    refine hS.plane_contra hV' hN g1 g2 g3 ?_ ?_ ?_
    · rw [hNA]; exact near FA α g1
    · rw [hNB]; exact near FB β g2
    · rw [hNC]; exact near FC γ g3
  rw [hV', hNA, hNB, hNC]
  exact isRupert_frustum FA FB FC O hind α β γ ⟨hα, hα1⟩ ⟨hβ, hβ1⟩ ⟨hγ, hγ1⟩

/-- Parallel lateral edges from one Gale dependency. -/
theorem parallel_rel {X X' Y Y' : ℝ³} {LX LY : ℝ}
    (hv : LX • (X - X') + LY • (Y - Y') = 0) (hLY : LY ≠ 0) :
    Y' = Y + (-(LX / LY)) • (X' - X) := by
  have e : LY * (LX / LY) = LX := mul_div_cancel₀ LX hLY
  have h0 : LY • (Y' - (Y + (-(LX / LY)) • (X' - X))) = 0 := by
    linear_combination (norm := module) -hv + e • (X' - X)
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd h hLY
  · exact sub_eq_zero.mp h

theorem frustum_of_rel {O Y Y' : ℝ³} {y : ℝ} (h2 : (1 - y) • O = Y - y • Y') (hy : y ≠ 0) :
    Y' = O + y⁻¹ • (Y - O) := by
  calc Y' = y⁻¹ • (y • Y') := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
    _ = y⁻¹ • ((Y - O) + y • O) := by congr 1; linear_combination (norm := module) h2
    _ = O + y⁻¹ • (Y - O) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hy, one_smul, add_comm]

/-- Concurrent lateral lines from one Gale dependency. -/
theorem frustum_rel {O X X' Y Y' : ℝ³} {x y LX LY : ℝ} (hO : (1 - x) • O = X - x • X')
    (hs : LX * (1 - x) + LY * (1 - y) = 0) (hv : LX • (X - x • X') + LY • (Y - y • Y') = 0)
    (hLY : LY ≠ 0) (hy : y ≠ 0) : Y' = O + y⁻¹ • (Y - O) := by
  have h1 : (LY * (1 - y)) • O = LY • (Y - y • Y') := by
    linear_combination (norm := module) hs • O - LX • hO - hv
  have h2 : (1 - y) • O = Y - y • Y' := by
    rw [← smul_smul] at h1
    exact smul_right_injective _ hLY h1
  exact frustum_of_rel h2 hy

/-- **Proposition 10.2** for named O-pairs. -/
theorem isRupert_prism_of_pairs {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) {A A' B B' C C' : ℝ³} (hV : V = {A, A', B, B', C, C'})
    (hnd : [A, A', B, B', C, C'].Nodup) (hA : IsOPair l m A A') (hB : IsOPair l m B B')
    (hC : IsOPair l m C C') : IsRupert V := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ :=
    hnd'
  have mA : A ∈ V := by rw [hV]; simp
  have mA' : A' ∈ V := by rw [hV]; simp
  have mB : B ∈ V := by rw [hV]; simp
  have mB' : B' ∈ V := by rw [hV]; simp
  have mC : C ∈ V := by rw [hV]; simp
  have mC' : C' ∈ V := by rw [hV]; simp
  obtain ⟨a, ha, laA, maA⟩ := hA.coeff hF mA
  obtain ⟨b, hb, lbB, mbB⟩ := hB.coeff hF mB
  obtain ⟨c, hc, lcC, mcC⟩ := hC.coeff hF mC
  have gA' := galeD_pair laA maA
  have gB' := galeD_pair lbB mbB
  have gC' := galeD_pair lcC mcC
  -- nonvanishing Gale determinants across pairs
  have npar : ∀ {s s' t : ℝ³}, s ∈ V → s' ∈ V → t ∈ V → s ≠ s' → s ≠ t → s' ≠ t →
      galeD l m s s' = 0 → galeD l m s t ≠ 0 :=
    fun hs hs' ht h1 h2 h3 h0 h => hF.no_three_parallel hS hs hs' ht h1 h2 h3 h0 h
  have LA : galeD l m C A ≠ 0 := npar mC mC' mA h56 (Ne.symm h15) (Ne.symm h16) hC.2.1
  have LB : galeD l m C B ≠ 0 := npar mC mC' mB h56 (Ne.symm h35) (Ne.symm h36) hC.2.1
  have KC : galeD l m A C ≠ 0 := npar mA mA' mC h12 h15 h25 hA.2.1
  have JA : galeD l m B A ≠ 0 := npar mB mB' mA h34 (Ne.symm h13) (Ne.symm h14) hB.2.1
  have JC : galeD l m B C ≠ 0 := npar mB mB' mC h34 h35 h45 hB.2.1
  -- the relations of the dependencies `galeD C`, `galeD A`, `galeD B`
  have dep := fun s => hF.hl.galeD hF.hm s
  have sC := (dep C).1
  have vC := (dep C).2
  have sA := (dep A).1
  have sB := (dep B).1
  have vB := (dep B).2
  rw [hV, sum_six hnd] at sC vC sA sB vB
  rw [gA', gB', galeD_self, hC.2.1] at sC vC
  rw [galeD_self, hA.2.1, gB', gC'] at sA
  rw [gA', galeD_self, hB.2.1, gC'] at sB vB
  set PA := galeD l m C A
  set PB := galeD l m C B
  set QB := galeD l m A B
  set QC := galeD l m A C
  set RA := galeD l m B A
  set RC := galeD l m B C
  have sC' : PA * (1 - a) + PB * (1 - b) = 0 := by linarith
  have sA' : QB * (1 - b) + QC * (1 - c) = 0 := by linarith
  have sB' : RA * (1 - a) + RC * (1 - c) = 0 := by linarith
  have vC' : PA • (A - a • A') + PB • (B - b • B') = 0 := by
    rw [← vC]; module
  have vB' : RA • (A - a • A') + RC • (C - c • C') = 0 := by
    rw [← vB]; module
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b = 1 := by
      have : PB * (1 - b) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h LB
      · linarith
    subst hb1
    have hc1 : c = 1 := by
      have : QC * (1 - c) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h KC
      · linarith
    subst hc1
    simp only [one_smul] at vC' vB'
    refine isRupert_parallel_of_shifts hS hV hnd (w := A' - A)
      (neg_ne_zero.mpr (div_ne_zero LA LB)) (neg_ne_zero.mpr (div_ne_zero JA JC))
      (by abel) (parallel_rel vC' LB) (parallel_rel vB' JC)
  · have ha1' : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    have hb1 : 1 - b ≠ 0 := by
      intro h; rw [h, mul_zero, add_zero] at sC'
      rcases mul_eq_zero.mp sC' with h' | h'
      · exact LA h'
      · exact ha1' h'
    have hc1 : 1 - c ≠ 0 := by
      intro h; rw [h, mul_zero, add_zero] at sB'
      rcases mul_eq_zero.mp sB' with h' | h'
      · exact JA h'
      · exact ha1' h'
    set O := (1 - a)⁻¹ • (A - a • A') with hOdef
    have hO : (1 - a) • O = A - a • A' := by
      rw [hOdef, smul_smul, mul_inv_cancel₀ ha1', one_smul]
    have hA'' : A' = O + a⁻¹ • (A - O) := frustum_of_rel hO ha.ne'
    have hB'' : B' = O + b⁻¹ • (B - O) := frustum_rel hO sC' vC' LB hb.ne'
    have hC'' : C' = O + c⁻¹ • (C - O) := frustum_rel hO sB' vB' JC hc.ne'
    refine isRupert_frustum_of_ratios hS hV hnd (inv_pos.mpr ha) (inv_pos.mpr hb)
      (inv_pos.mpr hc) ?_ ?_ ?_ hA'' hB'' hC''
    · intro h; apply ha1; rw [← inv_inv a, h, inv_one]
    · intro h; apply hb1; rw [← inv_inv b, h, inv_one, sub_self]
    · intro h; apply hc1; rw [← inv_inv c, h, inv_one, sub_self]

/-- **Proposition 10.2.** If every point has an O-partner, `V` is a prism and
Rupert. -/
theorem isRupert_of_all_partners {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) (hall : ∀ i ∈ V, ∃ j ∈ V, IsOPair l m i j) : IsRupert V := by
  obtain ⟨A, A', B, B', C, C', hV, hnd, hA, hB, hC⟩ := exists_three_pairs hS hF hall
  exact isRupert_prism_of_pairs hS hF hV hnd hA hB hC

end Minimality

end RupertMinimality
