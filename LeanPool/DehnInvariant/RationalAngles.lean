/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.Similarity
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
Lean study 4 of the shape-language canon (DICTO, 19 Nov 2026), part L: the zero words.

`dehnSet_sol_eq_zero_of_rational`: a solid cut out by finitely many half-spaces whose normals
make, two by two,
angles that are rational multiples of π has Dehn invariant zero, whatever the offsets of the
half-spaces
(the solid may have any number of faces through an edge or a corner; no list of edges is needed).

`dehnSet_cubeRD`: every cube ∩ rhombic dodecahedron solid `|x i| ≤ s`, `|x i ± x j| ≤ c` has Dehn
invariant
zero, for all `s`, `c`; the fair 18-face die is the member `s = 1`, `c = μ√2`, μ = 1.03125… .
(The face normals make angles 45°, 60°, 90°, 120°, 135° and 180°, so the dihedral angles are 90°,
120°, 135°.)

Method. At a point of the solid the angle class is that of the cone of the tight constraints
(study 2).
If that cone has interior, it is the cone of two of the constraints (`two_extreme`: in the plane
across the
edge every normal is a combination, with coefficients ≥ 0, of two extreme ones), and the angle of
two
half-spaces is π minus the angle of the normals (`theta_pair`, study 3). If it has no interior its
angle is 0.

Credits: Mathlib `InnerProductGeometry.cos_angle_mul_norm_mul_norm`, `Real.cos_three_mul`,
`Real.sin_eq_zero_iff`, `Fintype.not_linearIndependent_iff`,
`LinearIndependent.fintype_card_le_finrank`,
`LinearIndependent.pair_iff'`, `MeasureTheory.Measure.addHaar_submodule`.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-! ### Angles whose squared cosine is 0, 1/4, 1/2, 3/4 or 1 -/

lemma mem_ratPi_of_sin_nat_mul {x : ℝ} (N : ℕ) (hN : N ≠ 0) (h : Real.sin (N * x) = 0) :
    x ∈ ratPi := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
  rw [mem_ratPi_iff]
  refine ⟨(n : ℚ) / N, ?_⟩
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : x = n * Real.pi / N := by rw [eq_div_iff hN']; linarith
  rw [hx]; push_cast; ring

lemma pi_mem_ratPi : Real.pi ∈ ratPi := (mem_ratPi_iff _).2 ⟨1, by simp⟩

/-- If 4 cos² θ is 0, 1, 2, 3 or 4, then θ is a rational multiple of π. -/
lemma mem_ratPi_of_four_cos_sq {θ : ℝ} {k : ℕ} (hk : k ≤ 4) (h : 4 * Real.cos θ ^ 2 = k) :
    θ ∈ ratPi := by
  have sq0 : ∀ y : ℝ, y ^ 2 = 0 → y = 0 := fun y hy => (pow_eq_zero_iff two_ne_zero).1 hy
  have h2 := Real.cos_two_mul θ
  have hs := Real.sin_sq_add_cos_sq θ
  have key : ∀ c : ℝ, Real.cos (2 * θ) = c → 4 * c ^ 3 - 3 * c = 1 ∨ 4 * c ^ 3 - 3 * c = -1 →
      θ ∈ ratPi := by
    intro c hc h3
    have h6 : Real.cos (3 * (2 * θ)) = 4 * c ^ 3 - 3 * c := by rw [Real.cos_three_mul, hc]
    have hs6 := Real.sin_sq_add_cos_sq (3 * (2 * θ))
    have h0 : Real.sin (3 * (2 * θ)) = 0 := by
      apply sq0
      rcases h3 with e | e <;> rw [h6, e] at hs6 <;> linarith
    apply mem_ratPi_of_sin_nat_mul 6 (by norm_num)
    rw [show ((6 : ℕ) : ℝ) * θ = 3 * (2 * θ) by push_cast; ring]; exact h0
  interval_cases k
  · have hc : Real.cos θ = 0 := sq0 _ (by push_cast at h; linarith)
    apply mem_ratPi_of_sin_nat_mul 2 (by norm_num)
    rw [show ((2 : ℕ) : ℝ) * θ = 2 * θ by push_cast; ring, Real.sin_two_mul, hc, mul_zero]
  · exact key (-1 / 2) (by rw [h2]; push_cast at h; linarith) (Or.inl (by norm_num))
  · have hc : Real.cos (2 * θ) = 0 := by rw [h2]; push_cast at h; linarith
    apply mem_ratPi_of_sin_nat_mul 4 (by norm_num)
    rw [show ((4 : ℕ) : ℝ) * θ = 2 * (2 * θ) by push_cast; ring, Real.sin_two_mul, hc, mul_zero]
  · exact key (1 / 2) (by rw [h2]; push_cast at h; linarith) (Or.inr (by norm_num))
  · have hc : Real.sin θ = 0 := sq0 _ (by push_cast at h; linarith)
    apply mem_ratPi_of_sin_nat_mul 1 (by norm_num)
    rw [show ((1 : ℕ) : ℝ) * θ = θ by push_cast; ring]; exact hc

section general

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type}

/-- Two vectors with 4⟪x, y⟫² = k ⟪x, x⟫ ⟪y, y⟫, k = 0, 1, 2, 3 or 4, make an angle that is a
rational
multiple of π (90°; 60° or 120°; 45° or 135°; 30° or 150°; 0° or 180°). -/
lemma angle_mem_ratPi_of_gram {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) {k : ℕ} (hk : k ≤ 4)
    (h : 4 * ⟪x, y⟫ ^ 2 = k * (⟪x, x⟫ * ⟪y, y⟫)) : InnerProductGeometry.angle x y ∈ ratPi := by
  apply mem_ratPi_of_four_cos_sq hk
  have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm x y
  have hxx : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hyy : ⟪y, y⟫ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hpos : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have := norm_pos_iff.2 hx; have := norm_pos_iff.2 hy; positivity
  rw [← h1, hxx, hyy] at h
  have h0 : (4 * Real.cos (InnerProductGeometry.angle x y) ^ 2 - k) * (‖x‖ ^ 2 * ‖y‖ ^ 2) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h0 with e | e
  · linarith
  · exact absurd e hpos.ne'

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

/-- **The angle class of a cone of constraints whose normals make rational angles is zero**, for any
number of constraints. -/
theorem theta_cone_eq_zero_of_rational [Finite ι] (a : ι → E) (A : Set ι) (hne : ∀ i, a i ≠ 0)
    (hang : ∀ i j, InnerProductGeometry.angle (a i) (a j) ∈ ratPi) : theta (cone a A) = 0 := by
  classical
  by_cases hfin : finrank ℝ (linCone a A) = 1
  swap
  · unfold theta; rw [linSpace_cone, ite_eq_right hfin]
  have hE : finrank ℝ E = 3 := Fact.out
  have hW : finrank ℝ (linCone a A)ᗮ = 2 := by
    have := Submodule.finrank_add_finrank_orthogonal (linCone a A)
    omega
  have hmem : ∀ i ∈ A, a i ∈ (linCone a A)ᗮ := by
    intro i hi
    rw [Submodule.mem_orthogonal']
    intro u hu
    exact hu i hi
  by_cases hv0 : ∃ v0, ∀ i ∈ A, ⟪a i, v0⟫ < 0
  · obtain ⟨v0, hv0⟩ := hv0
    have hAne : A.Nonempty := by
      by_contra hno
      rw [Set.not_nonempty_iff_eq_empty] at hno
      have htop : linCone a A = ⊤ := by
        rw [eq_top_iff]; intro v _
        rw [mem_linCone, hno]; intro i hi; exact absurd hi (Set.notMem_empty i)
      rw [htop, finrank_top] at hfin
      omega
    have hAfin : A.Finite := Set.toFinite A
    obtain ⟨p, hp, q, hq, hpq⟩ := two_extreme hW a v0 hAfin.toFinset
      ((Set.Finite.toFinset_nonempty hAfin).2 hAne)
      (fun i hi => hmem i ((Set.Finite.mem_toFinset hAfin).1 hi))
      (fun i hi => hv0 i ((Set.Finite.mem_toFinset hAfin).1 hi))
    have hpA : p ∈ A := (Set.Finite.mem_toFinset hAfin).1 hp
    have hqA : q ∈ A := (Set.Finite.mem_toFinset hAfin).1 hq
    have hcone : cone a A = cone a {p, q} := by
      ext v; constructor
      · intro h i hi
        rcases hi with rfl | rfl
        · exact h _ hpA
        · exact h _ hqA
      · intro h i hi
        exact hpq v (h p (mem_insert _ _)) (h q (mem_insert_of_mem _ rfl)) i
          ((Set.Finite.mem_toFinset hAfin).2 hi)
    rw [hcone]
    by_cases hli : LinearIndependent ℝ ![a p, a q]
    · rw [theta_pair a rfl hli, Submodule.Quotient.mk_eq_zero]
      exact ratPi.sub_mem pi_mem_ratPi (hang p q)
    · rw [LinearIndependent.pair_iff' (hne p)] at hli
      push Not at hli
      obtain ⟨c, hc⟩ := hli
      have hle : (ℝ ∙ a p)ᗮ ≤ linCone a {p, q} := by
        intro v hv
        have h0 : ⟪a p, v⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hv
        rw [mem_linCone]
        intro i hi
        rcases hi with rfl | rfl
        · exact h0
        · rw [← hc, inner_smul_left, h0, mul_zero]
      unfold theta
      rw [linSpace_cone, ite_eq_right (finrank_linCone_ne_one_of_perp a hle)]
  · push Not at hv0
    unfold theta
    rw [linSpace_cone, ite_eq_left hfin, Submodule.Quotient.mk_eq_zero]
    have hnull : volume (wedgeSet (cone a A) (linCone a A)) = 0 := by
      have hsub : wedgeSet (cone a A) (linCone a A) ⊆
          ⋃ i ∈ A, {w : (linCone a A)ᗮ | ⟪a i, (w : E)⟫ = 0} := by
        intro w hw
        obtain ⟨i, hi, h0⟩ := hv0 (w : E)
        exact mem_iUnion₂.2 ⟨i, hi, le_antisymm (hw.1 i hi) h0⟩
      apply measure_mono_null hsub
      rw [measure_biUnion_null_iff (Set.to_countable A)]
      intro i hi
      let N : Submodule ℝ (linCone a A)ᗮ := (ℝ ∙ (⟨a i, hmem i hi⟩ : (linCone a A)ᗮ))ᗮ
      have hN : N ≠ ⊤ := by
        intro h
        have h1 : (⟨a i, hmem i hi⟩ : (linCone a A)ᗮ) ∈ N := by rw [h]; trivial
        have h2 : ⟪(⟨a i, hmem i hi⟩ : (linCone a A)ᗮ), (⟨a i, hmem i hi⟩ : (linCone a A)ᗮ)⟫ = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.1 h1
        have h3 : (⟨a i, hmem i hi⟩ : (linCone a A)ᗮ) = 0 := inner_self_eq_zero.1 h2
        exact hne i (congrArg Subtype.val h3)
      have hset : {w : (linCone a A)ᗮ | ⟪a i, (w : E)⟫ = 0} = (N : Set (linCone a A)ᗮ) := by
        ext w
        exact (Submodule.mem_orthogonal_singleton_iff_inner_right
          (u := (⟨a i, hmem i hi⟩ : (linCone a A)ᗮ)) (v := w)).symm
      rw [hset]
      exact Measure.addHaar_submodule volume N hN
    unfold wedgeAngle
    rw [hnull]
    simp

/-- **Rational normals, zero invariant.** A solid cut out by finitely many half-spaces whose
normals make,
two by two, angles that are rational multiples of π has Dehn invariant zero, for all offsets `b`. -/
theorem dehnSet_sol_eq_zero_of_rational [Finite ι] (a : ι → E) (b : ι → ℝ) (hne : ∀ i, a i ≠ 0)
    (hang : ∀ i j, InnerProductGeometry.angle (a i) (a j) ∈ ratPi) : dehnSet (sol a b) = 0 := by
  have h0 : ∀ x, edgeAngle (sol a b) x = 0 := by
    intro x
    by_cases hx : x ∈ sol a b
    · rw [edgeAngle_sol a b hx]; exact theta_cone_eq_zero_of_rational a _ hne hang
    · exact edgeAngle_of_notMem hx
  rw [dehnSet_eq_single (sol a b) 0 (fun x => Or.inl (h0 x)), TensorProduct.tmul_zero]

end general

/-! ### The cube ∩ rhombic dodecahedron line -/

/-- The 18 face normals of the cube ∩ rhombic dodecahedron solids, in whole numbers: ± the three
coordinate
directions (cube), then the twelve vectors ±eᵢ ± eⱼ (rhombic dodecahedron). -/
def crZ : Fin 18 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1],
    ![1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 0],
    ![1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, -1],
    ![0, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, -1]]

/-- Dot products of the normals. -/
def crDot (i j : Fin 18) : ℤ := crZ i 0 * crZ j 0 + crZ i 1 * crZ j 1 + crZ i 2 * crZ j 2

/-- The normals as vectors of ℝ³. -/
noncomputable def crN (i : Fin 18) : R3 := !₂[(crZ i 0 : ℝ), (crZ i 1 : ℝ), (crZ i 2 : ℝ)]

/-- Offsets: `s` for the six cube faces, `c` for the twelve rhombic dodecahedron faces. -/
def crB (s c : ℝ) : Fin 18 → ℝ := fun i => if (i : ℕ) < 6 then s else c

/-- **The cube ∩ rhombic dodecahedron solids**: the points with `|x i| ≤ s` (cube) and `|x i ± x
j| ≤ c`
(rhombic dodecahedron). For `s < c < 2 s` the solid has 18 faces; `s = 1`, `c = μ√2` with μ =
1.03125… is
the fair 18-face die. -/
noncomputable def cubeRDSet (s c : ℝ) : Set R3 := sol crN (crB s c)

lemma crN_inner (i j : Fin 18) : ⟪crN i, crN j⟫ = (crDot i j : ℝ) := by
  unfold crN crDot
  rw [inner3]
  push_cast
  rfl

private def angleIndex (i j : Fin 18) : Fin 5 :=
  Fin.ofNat 5 ((4 * crDot i j ^ 2 / (crDot i i * crDot j j)).toNat)

private lemma angleIndex_spec : ∀ i j : Fin 18,
    4 * crDot i j ^ 2 = (angleIndex i j : ℤ) * (crDot i i * crDot j j) := by
  -- The kernel checks the computed index for each pair of normals.
  decide +kernel

/-- The squared cosine of each of the 18 normals with each other is a multiple of one fourth. -/
lemma crDot_table (i j : Fin 18) :
    ∃ k : Fin 5, 4 * crDot i j ^ 2 = (k : ℤ) * (crDot i i * crDot j j) :=
  ⟨angleIndex i j, angleIndex_spec i j⟩

lemma crDot_self_ne : ∀ i : Fin 18, crDot i i ≠ 0 := by decide +kernel

lemma crN_ne_zero (i : Fin 18) : crN i ≠ 0 := by
  intro h
  have h1 := crN_inner i i
  rw [h, inner_zero_left] at h1
  exact crDot_self_ne i (by exact_mod_cast h1.symm)

/-- Any two of the 18 normals make an angle that is a rational multiple of π. -/
lemma crN_angle (i j : Fin 18) : InnerProductGeometry.angle (crN i) (crN j) ∈ ratPi := by
  obtain ⟨k, hk⟩ := crDot_table i j
  apply angle_mem_ratPi_of_gram (crN_ne_zero i) (crN_ne_zero j) (k := (k : ℕ)) (by omega)
  rw [crN_inner, crN_inner, crN_inner]
  exact_mod_cast hk

lemma fin3_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

/-- The definition spelled out: `|x i| ≤ s` for the three coordinates and `|x i ± x j| ≤ c` for
the three
pairs of coordinates. -/
lemma mem_cubeRDSet {s c : ℝ} {x : R3} :
    x ∈ cubeRDSet s c ↔ (∀ i, |x i| ≤ s) ∧ ∀ i j, i ≠ j → |x i + x j| ≤ c ∧ |x i - x j| ≤ c := by
  have e : ∀ i : Fin 18, ⟪crN i, x⟫ = crZ i 0 * x 0 + crZ i 1 * x 1 + crZ i 2 * x 2 := fun i => by
    unfold crN; rw [inner3]
  constructor
  · intro hx
    have H : ∀ i : Fin 18, (crZ i 0 : ℝ) * x 0 + crZ i 1 * x 1 + crZ i 2 * x 2
        ≤ crB s c i := fun i => by
      rw [← e]; exact hx i
    have h0 := H 0; have h1 := H 1; have h2 := H 2; have h3 := H 3; have h4 := H 4; have h5 := H 5
    have h6 := H 6; have h7 := H 7; have h8 := H 8; have h9 := H 9; have h10 := H 10; have h11 :=
        H 11
    have h12 := H 12; have h13 := H 13; have h14 := H 14; have h15 := H 15; have h16 := H 16
    have h17 := H 17
    simp [crZ, crB] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rcases fin3_cases i with rfl | rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
    · rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hij
        | (rw [abs_le, abs_le]; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith)
  · rintro ⟨h1, h2⟩ i
    change ⟪crN i, x⟫ ≤ crB s c i
    rw [e]
    have a0 := abs_le.1 (h1 0); have a1 := abs_le.1 (h1 1); have a2 := abs_le.1 (h1 2)
    have b01 := abs_le.1 (h2 0 1 (by decide)).1; have c01 := abs_le.1 (h2 0 1 (by decide)).2
    have b02 := abs_le.1 (h2 0 2 (by decide)).1; have c02 := abs_le.1 (h2 0 2 (by decide)).2
    have b12 := abs_le.1 (h2 1 2 (by decide)).1; have c12 := abs_le.1 (h2 1 2 (by decide)).2
    fin_cases i <;> simp [crZ, crB] <;> linarith

/-- The cube ∩ rhombic dodecahedron solids are convex polytopes. -/
theorem isPoly_cubeRD (s c : ℝ) : IsPoly (cubeRDSet s c) :=
  ⟨bounded_of_coords s (fun _ hx i => (mem_cubeRDSet.1 hx).1 i), Fin 18, inferInstance, crN, _, rfl⟩

/-- **The zero word.** Every cube ∩ rhombic dodecahedron solid has Dehn invariant zero: all
offsets `s`, `c`,
so the whole line of cuts, the fair 18-face die among them. -/
theorem dehnSet_cubeRD (s c : ℝ) : dehnSet (cubeRDSet s c) = 0 :=
  dehnSet_sol_eq_zero_of_rational crN (crB s c) crN_ne_zero crN_angle

/-- The fair 18-face die is the member `s = 1`, `c = μ√2` with μ = 1.03125… (the fair cut, known
numerically
and as a root of a polynomial of degree 6; study of 18 November 2026). The statement holds for
every μ. -/
theorem dehnSet_fairDie18 (μ : ℝ) : dehnSet (cubeRDSet 1 (μ * √2)) = 0 := dehnSet_cubeRD 1 _

/-- The same invariant as every cube. -/
theorem dehnSet_cubeRD_eq_cube (s c t : ℝ) (ht : 0 < t) :
    dehnSet (cubeRDSet s c) = dehnSet (cubeSet t) := by
  rw [dehnSet_cubeRD, dehnSet_cube t ht]

end DehnCanon.Library
