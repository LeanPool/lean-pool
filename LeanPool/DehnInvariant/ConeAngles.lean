/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.SectorArea
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Dihedral angles of cones of half-spaces
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type}

/-- Sign pattern of a relation `a X + b Y + c Z = 0` with `X, Y, Z < 0`: one coefficient is not
zero and the
other two have the opposite sign (or vanish). -/
lemma sign3 {a b c X Y Z : ℝ} (hX : X < 0) (hY : Y < 0) (hZ : Z < 0) (h : a * X + b * Y + c * Z = 0)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (c ≠ 0 ∧ a * c ≤ 0 ∧ b * c ≤ 0) ∨ (a ≠ 0 ∧ b * a ≤ 0 ∧ c * a ≤ 0) ∨
      (b ≠ 0 ∧ a * b ≤ 0 ∧ c * b ≤ 0) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;> rcases lt_trichotomy b 0 with hb | rfl | hb <;>
    rcases lt_trichotomy c 0 with hc | rfl | hc <;>
    first
    | (exfalso; simp at hne; done)
    | (exfalso; nlinarith)
    | (left; exact ⟨by intro h0; linarith, by nlinarith, by nlinarith⟩)
    | (right; left; exact ⟨by intro h0; linarith, by nlinarith, by nlinarith⟩)
    | (right; right; exact ⟨by intro h0; linarith, by nlinarith, by nlinarith⟩)

/-- If `c r = -(a p + b q)` with `p, q ≤ 0`, `c ≠ 0` and `a c ≤ 0`, `b c ≤ 0`, then `r ≤ 0`. -/
lemma nonpos_of_comb {a b c p q r : ℝ} (hc : c ≠ 0) (hac : a * c ≤ 0) (hbc : b * c ≤ 0) (hp : p ≤ 0)
    (hq : q ≤ 0) (h : a * p + b * q + c * r = 0) : r ≤ 0 := by
  by_contra hr
  have hr' : 0 < r := not_le.1 hr
  have e : c * (a * p + b * q + c * r) = 0 := by rw [h, mul_zero]
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hac hp, mul_nonneg_of_nonpos_of_nonpos hbc hq,
    mul_pos (sq_pos_of_ne_zero hc) hr']

/-- Three vectors of a plane on one side of a line: one of the three half-planes contains the
intersection of the other two. -/
lemma three_in_plane {W : Submodule ℝ E} (hW : finrank ℝ W = 2) {x y z v0 : E} (hx : x ∈ W)
    (hy : y ∈ W) (hz : z ∈ W) (cx : ⟪x, v0⟫ < 0) (cy : ⟪y, v0⟫ < 0) (cz : ⟪z, v0⟫ < 0) :
    (∀ v, ⟪x, v⟫ ≤ 0 → ⟪y, v⟫ ≤ 0 → ⟪z, v⟫ ≤ 0) ∨ (∀ v, ⟪y, v⟫ ≤ 0 → ⟪z, v⟫ ≤ 0 → ⟪x, v⟫ ≤ 0) ∨
      (∀ v, ⟪x, v⟫ ≤ 0 → ⟪z, v⟫ ≤ 0 → ⟪y, v⟫ ≤ 0) := by
  have hdep : ¬ LinearIndependent ℝ ![(⟨x, hx⟩ : W), ⟨y, hy⟩, ⟨z, hz⟩] := by
    intro hli
    have : Module.Finite ℝ W := Module.finite_of_finrank_pos (by rw [hW]; norm_num)
    have h1 := hli.fintype_card_le_finrank
    rw [hW] at h1
    simp at h1
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hrel : g 0 • x + g 1 • y + g 2 • z = 0 := by
    have h1 := congrArg Subtype.val hg
    simpa [Fin.sum_univ_three] using h1
  have hv : ∀ v, g 0 * ⟪x, v⟫ + g 1 * ⟪y, v⟫ + g 2 * ⟪z, v⟫ = 0 := by
    intro v
    have h1 := congrArg (fun u => ⟪u, v⟫) hrel
    simpa [inner_add_left, inner_smul_left] using h1
  have hne : g 0 ≠ 0 ∨ g 1 ≠ 0 ∨ g 2 ≠ 0 := by
    fin_cases i0
    · exact Or.inl hi0
    · exact Or.inr (Or.inl hi0)
    · exact Or.inr (Or.inr hi0)
  rcases sign3 cx cy cz (hv v0) hne with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inl fun v hp hq => nonpos_of_comb h0 h1 h2 hp hq (hv v)
  · exact Or.inr (Or.inl fun v hp hq => nonpos_of_comb h0 h1 h2 hp hq (by linarith [hv v]))
  · exact Or.inr (Or.inr fun v hp hq => nonpos_of_comb h0 h1 h2 hp hq (by linarith [hv v]))

/-- Finitely many vectors of a plane, all on one side of a line: the intersection of their
half-planes is
the intersection of two of them. -/
lemma two_extreme {W : Submodule ℝ E} (hW : finrank ℝ W = 2) (a : ι → E) (v0 : E) (s : Finset ι) :
    s.Nonempty → (∀ i ∈ s, a i ∈ W) → (∀ i ∈ s, ⟪a i, v0⟫ < 0) →
      ∃ p ∈ s, ∃ q ∈ s, ∀ v, ⟪a p, v⟫ ≤ 0 → ⟪a q, v⟫ ≤ 0 → ∀ i ∈ s, ⟪a i, v⟫ ≤ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | insert k s hk ih =>
    intro _ hmem hneg
    rcases s.eq_empty_or_nonempty with he | hs
    · subst he
      refine ⟨k, Finset.mem_insert_self _ _, k, Finset.mem_insert_self _ _, fun v h _ i hi => ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact h
      · exact absurd hi (Finset.notMem_empty _)
    · obtain ⟨p, hp, q, hq, hpq⟩ := ih hs (fun i hi => hmem i (Finset.mem_insert_of_mem hi))
        (fun i hi => hneg i (Finset.mem_insert_of_mem hi))
      have hp' : p ∈ insert k s := Finset.mem_insert_of_mem hp
      have hq' : q ∈ insert k s := Finset.mem_insert_of_mem hq
      have hk' := Finset.mem_insert_self k s
      rcases three_in_plane hW (hmem p hp') (hmem q hq') (hmem k hk') (hneg p hp') (hneg q hq')
        (hneg k hk') with h | h | h
      · refine ⟨p, hp', q, hq', fun v h1 h2 i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h v h1 h2
        · exact hpq v h1 h2 i hi
      · refine ⟨q, hq', k, hk', fun v h1 h2 i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h2
        · exact hpq v (h v h1 h2) h1 i hi
      · refine ⟨p, hp', k, hk', fun v h1 h2 i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h2
        · exact hpq v h1 (h v h1 h2) i hi

/-- Two vectors whose Gram determinant is not zero are linearly independent. -/
lemma linIndep_pair_of_gram {x y : E} (h : ⟪x, x⟫ * ⟪y, y⟫ ≠ ⟪x, y⟫ ^ 2) :
    LinearIndependent ℝ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : s * ⟪x, x⟫ + t * ⟪x, y⟫ = 0 := by
    have := congrArg (fun v => ⟪x, v⟫) hst
    simpa [inner_add_right, inner_smul_right] using this
  have h2 : s * ⟪x, y⟫ + t * ⟪y, y⟫ = 0 := by
    have := congrArg (fun v => ⟪y, v⟫) hst
    have e : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
    simpa [inner_add_right, inner_smul_right, e] using this
  have hd : ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ ^ 2 ≠ 0 := sub_ne_zero.2 h
  have hs : s * (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ ^ 2) = 0 := by
    linear_combination ⟪y, y⟫ * h1 - ⟪x, y⟫ * h2
  have ht : t * (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ ^ 2) = 0 := by
    linear_combination ⟪x, x⟫ * h2 - ⟪x, y⟫ * h1
  exact ⟨(mul_eq_zero.1 hs).resolve_right hd, (mul_eq_zero.1 ht).resolve_right hd⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fact (finrank ℝ E = 3)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A direction space that contains a whole plane is not a line. -/
lemma finrank_linCone_ne_one_of_perp (a : ι → E) {A : Set ι} {u : E}
    (hle : (ℝ ∙ u)ᗮ ≤ linCone a A) : finrank ℝ (linCone a A) ≠ 1 := by
  have hE : finrank ℝ E = 3 := Fact.out
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
  have h2 : finrank ℝ (ℝ ∙ u) ≤ 1 := (finrank_span_le_card ({u} : Set E)).trans (by simp)
  have h3 := Submodule.finrank_mono hle
  omega

/-- **The angle class where exactly two faces meet**: π minus the angle between the two outward
normals. -/
theorem theta_pair (a : ι → E) {A : Set ι} {i j : ι} (hA : A = {i, j})
    (h : LinearIndependent ℝ ![a i, a j]) :
    theta (cone a A) =
      Submodule.Quotient.mk (Real.pi - InnerProductGeometry.angle (a i) (a j)) := by
  have hc : cone a A = cone ![a i, a j] Set.univ := by
    ext v; rw [mem_cone_pair, hA]; simp [cone]
  have hl : linCone a A = linCone ![a i, a j] Set.univ := by
    ext v; rw [mem_linCone_pair, mem_linCone, hA]; simp
  unfold theta
  rw [linSpace_cone, hl, ite_eq_left (finrank_linCone_pair h), hc, wedgeAngle_two_planes _ _ h]

omit [MeasurableSpace E] [BorelSpace E] in
/-- At most one tight constraint: the common direction space has dimension at least 2. -/
lemma finrank_linCone_ne_one_of_subsingleton (a : ι → E) {A : Set ι} {i : ι} (hA : A ⊆ {i}) :
    finrank ℝ (linCone a A) ≠ 1 := by
  have hle : (ℝ ∙ a i)ᗮ ≤ linCone a A := by
    intro v hv
    rw [mem_linCone]
    intro m hm
    have hmi : m = i := hA hm
    rw [hmi]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hv
  exact finrank_linCone_ne_one_of_perp a hle

omit [MeasurableSpace E] [BorelSpace E] in
/-- If the common direction space of the tight constraints is a line, and any three of the tight
normals have
no common perpendicular direction, then exactly two constraints are tight. -/
lemma pair_of_finrank_one (a : ι → E) {A : Set ι}
    (hfin : finrank ℝ (linCone a A) = 1)
    (hind : ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A, i ≠ j → i ≠ k → j ≠ k →
      ∀ v : E, ⟪a i, v⟫ = 0 → ⟪a j, v⟫ = 0 → ⟪a k, v⟫ = 0 → v = 0) :
    ∃ i j, i ≠ j ∧ A = {i, j} := by
  have h2 : ∃ i ∈ A, ∃ j ∈ A, i ≠ j := by
    by_contra hno
    push Not at hno
    rcases A.eq_empty_or_nonempty with he | ⟨i, hi⟩
    · have top_eq : linCone a A = ⊤ := by
        ext v
        simp [mem_linCone, he]
      rw [top_eq, finrank_top, Fact.out (p := finrank ℝ E = 3)] at hfin
      omega
    · exact finrank_linCone_ne_one_of_subsingleton a (i := i)
        (fun j hj => (hno i hi j hj).symm) hfin
  obtain ⟨i, hi, j, hj, hij⟩ := h2
  refine ⟨i, j, hij, ?_⟩
  ext k; constructor
  · intro hk
    by_contra hno
    have hki : i ≠ k := fun h => hno (Or.inl h.symm)
    have hkj : j ≠ k := fun h => hno (Or.inr h.symm)
    have hbot : ∀ v ∈ linCone a A, v = 0 := fun v hv =>
      hind i hi j hj k hk hij hki hkj v (hv i hi) (hv j hj) (hv k hk)
    have hb : linCone a A = ⊥ := (Submodule.eq_bot_iff _).2 hbot
    rw [hb, finrank_bot] at hfin
    exact zero_ne_one hfin
  · rintro (rfl | rfl)
    · exact hi
    · exact hj

omit [Fact (finrank ℝ E = 3)] in
/-- If the angle class takes only one value `τ` besides 0, the Dehn invariant is (length of the
set where it
is `τ`) ⊗ `τ`. -/
lemma dehnSet_eq_single (P : Set E) (τ : Angle) (h : ∀ x, edgeAngle P x = τ ∨ edgeAngle P x = 0) :
    dehnSet P = (μH[1] {x | edgeAngle P x = τ}).toReal ⊗ₜ[ℚ] τ := by
  unfold dehnSet tsum1
  apply finsum_eq_single _ τ
  intro θ hθ
  by_cases h0 : θ = 0
  · rw [h0, TensorProduct.tmul_zero]
  · have he : {x | edgeAngle P x = θ} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx' : edgeAngle P x = θ := hx
      rcases h x with h1 | h1
      · exact hθ (hx'.symm.trans h1)
      · exact h0 (hx'.symm.trans h1)
    rw [he, measure_empty, ENNReal.toReal_zero, TensorProduct.zero_tmul]

/-- **The angle class of two faces from the Gram numbers of their normals.** If `⟪aᵢ, aᵢ⟫ = X`,
`⟪aⱼ, aⱼ⟫ = Y` and `⟪aᵢ, aⱼ⟫ = -d`, the interior angle where the two faces meet is `arccos (d /
√(X Y))`. -/
theorem theta_pair_of_gram {ι : Type} (a : ι → E) {A : Set ι} {i j : ι}
    (hA : A = {i, j}) {X Y d : ℝ} (hX : 0 < X) (hxx : ⟪a i, a i⟫ = X)
    (hyy : ⟪a j, a j⟫ = Y) (hxy : ⟪a i, a j⟫ = -d) (hne : X * Y ≠ d ^ 2) :
    theta (cone a A) = (Submodule.Quotient.mk (Real.arccos (d / √(X * Y))) : Angle) := by
  have hli : LinearIndependent ℝ ![a i, a j] :=
    linIndep_pair_of_gram (by rw [hxx, hyy, hxy, neg_sq]; exact hne)
  rw [theta_pair a hA hli]
  congr 1
  unfold InnerProductGeometry.angle
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hxx, hyy, hxy, ← Real.sqrt_mul hX.le,
    neg_div, Real.arccos_neg]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- A cone with a line of common directions and a strictly inward direction is the intersection of
two of its half-spaces. The selected normals are linearly independent. -/
lemma cone_eq_pair_of_strict [Finite ι] (a : ι → E) {A : Set ι} {v₀ : E}
    (hfin : finrank ℝ (linCone a A) = 1) (hv0 : ∀ i ∈ A, a i ≠ 0 → ⟪a i, v₀⟫ < 0) :
    ∃ p ∈ A, ∃ q ∈ A, LinearIndependent ℝ ![a p, a q] ∧ cone a A = cone a {p, q} := by
  classical
  let := Fintype.ofFinite ι
  have hE : finrank ℝ E = 3 := Fact.out
  have hW : finrank ℝ (linCone a A)ᗮ = 2 := by
    have := Submodule.finrank_add_finrank_orthogonal (linCone a A)
    omega
  have hmem : ∀ i ∈ A, a i ∈ (linCone a A)ᗮ := by
    intro i hi
    rw [Submodule.mem_orthogonal']
    intro u hu
    exact hu i hi
  let s : Finset ι := Finset.univ.filter fun i => i ∈ A ∧ a i ≠ 0
  have hs : ∀ i, i ∈ s ↔ i ∈ A ∧ a i ≠ 0 := by intro i; simp [s]
  have hsne : s.Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty] at hno
    have htop : linCone a A = ⊤ := by
      rw [eq_top_iff]; intro w _ i hi
      have h0 : a i = 0 := by
        by_contra h
        have h1 : i ∈ s := (hs i).2 ⟨hi, h⟩
        rw [hno] at h1
        exact absurd h1 (Finset.notMem_empty _)
      rw [h0, inner_zero_left]
    rw [htop, finrank_top] at hfin
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := two_extreme hW a v₀ s hsne
    (fun i hi => hmem i ((hs i).1 hi).1) (fun i hi => hv0 i ((hs i).1 hi).1 ((hs i).1 hi).2)
  have hpA : p ∈ A := ((hs p).1 hp).1
  have hqA : q ∈ A := ((hs q).1 hq).1
  have hcone : cone a A = cone a {p, q} := by
    ext w; constructor
    · intro h i hi
      rcases hi with rfl | rfl
      · exact h _ hpA
      · exact h _ hqA
    · intro h i hi
      by_cases h0 : a i = 0
      · rw [h0, inner_zero_left]
      · exact hpq w (h p (mem_insert _ _)) (h q (mem_insert_of_mem _ rfl)) i ((hs i).2 ⟨hi, h0⟩)
  refine ⟨p, hpA, q, hqA, ?_, hcone⟩
  by_contra hli
  rw [LinearIndependent.pair_iff' ((hs p).1 hp).2] at hli
  push Not at hli
  obtain ⟨c, hc⟩ := hli
  have hlin : linCone a A = linCone a {p, q} := by
    ext w; rw [← cone_lin a A w, ← cone_lin a {p, q} w, hcone]
  have hle : (ℝ ∙ a p)ᗮ ≤ linCone a {p, q} := by
    intro w hw
    have h0 : ⟪a p, w⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw
    rw [mem_linCone]
    intro i hi
    rcases hi with rfl | rfl
    · exact h0
    · rw [← hc, inner_smul_left, h0, mul_zero]
  exact finrank_linCone_ne_one_of_perp a hle (hlin ▸ hfin)

end DehnCanon.Library
