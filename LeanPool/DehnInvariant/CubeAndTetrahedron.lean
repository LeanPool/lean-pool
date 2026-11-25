/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.SectorArea
public import LeanPool.DehnInvariant.TetrahedronData
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
Lean study 3 of the shape-language canon (DICTO, 19 Nov 2026), part J: the cube and the regular
tetrahedron.

With the angle evaluation of part I (`wedgeAngle_two_planes`) this file evaluates the set
invariant `dehnSet`
of study 2 on the two solids of Dehn's theorem, closing gaps 2 and 3 of study 2:

* `dehnSet_cube`: the Dehn invariant of the cube `[-s, s]³` is zero (every edge angle is π/2).
* `dehnSet_tetra`: the Dehn invariant of the regular tetrahedron with corners (−1,−1,−1),
  (1,1,−1), (1,−1,1),
  (−1,1,1) is study 1's value for six edges of length 2√2 at arccos(1/3).
* `tetra_not_scissorsCongruent_cube` (**Dehn's theorem**): the regular tetrahedron is not scissors
  congruent to
  any cube.

Method. At a point of a polytope the angle class is read off from the constraints that hold with
equality
there (`edgeAngle_sol`, study 2). If their common direction space is a line, then in both solids
exactly two
constraints are tight (`pair_of_finrank_one`), and the angle is π minus the angle between the two
normals
(`theta_pair`, from part I). For the tetrahedron the points with two tight constraints are the six
open
segments between the corners (`tet_openSegment_iff`); their length is Mathlib's
`MeasureTheory.hausdorffMeasure_segment`.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-! ### General lemmas -/

section general

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type}

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
  have hE : finrank ℝ E = 3 := Fact.out
  have hle : (ℝ ∙ a i)ᗮ ≤ linCone a A := by
    intro v hv
    rw [mem_linCone]
    intro m hm
    have hmi : m = i := hA hm
    rw [hmi]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hv
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ a i)
  have h2 : finrank ℝ (ℝ ∙ a i) ≤ 1 := (finrank_span_le_card ({a i} : Set E)).trans (by simp)
  have h3 := Submodule.finrank_mono hle
  omega

omit [MeasurableSpace E] [BorelSpace E] in
/-- If the common direction space of the tight constraints is a line, and any three of the tight
normals have
no common perpendicular direction, then exactly two constraints are tight. -/
lemma pair_of_finrank_one [Nonempty ι] (a : ι → E) {A : Set ι}
    (hfin : finrank ℝ (linCone a A) = 1)
    (hind : ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A, i ≠ j → i ≠ k → j ≠ k →
      ∀ v : E, ⟪a i, v⟫ = 0 → ⟪a j, v⟫ = 0 → ⟪a k, v⟫ = 0 → v = 0) :
    ∃ i j, i ≠ j ∧ A = {i, j} := by
  have h2 : ∃ i ∈ A, ∃ j ∈ A, i ≠ j := by
    by_contra hno
    push Not at hno
    rcases A.eq_empty_or_nonempty with he | ⟨i, hi⟩
    · exact finrank_linCone_ne_one_of_subsingleton a (i := Classical.arbitrary ι)
        (by rw [he]; exact empty_subset _) hfin
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
  unfold dehnSet
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

end general

/-! ### The cube -/

lemma cubeN_apply (p : Fin 3 × Bool) (m : Fin 3) :
    cubeN p m = if m = p.1 then (if p.2 then 1 else -1) else 0 := by
  unfold cubeN
  by_cases hb : p.2 = true <;> by_cases hm : m = p.1 <;> simp [hb, hm]

lemma inner_cubeN (p : Fin 3 × Bool) (v : R3) :
    ⟪cubeN p, v⟫ = if p.2 then v p.1 else -v p.1 := by
  unfold cubeN
  by_cases hb : p.2 = true
  · rw [ite_eq_left hb, ite_eq_left hb, EuclideanSpace.inner_single_left]; simp
  · rw [ite_eq_right hb, ite_eq_right hb, inner_neg_left, EuclideanSpace.inner_single_left]; simp

lemma inner_cubeN_eq_zero {p : Fin 3 × Bool} {v : R3} (h : ⟪cubeN p, v⟫ = 0) : v p.1 = 0 := by
  rw [inner_cubeN] at h
  by_cases hb : p.2 = true
  · rwa [ite_eq_left hb] at h
  · rw [ite_eq_right hb] at h; linarith

lemma fin3_cover : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → ∀ m, m = a ∨ m = b ∨ m = c := by decide

/-- Every point of the cube has angle class 0: where two faces meet, the angle is π/2. -/
lemma edgeAngle_cube (s : ℝ) (hs : 0 < s) (x : R3) : edgeAngle (cubeSet s) x = 0 := by
  by_cases hx : x ∈ cubeSet s
  swap
  · exact edgeAngle_of_notMem hx
  change edgeAngle (sol cubeN fun _ => s) x = 0
  rw [edgeAngle_sol _ _ hx]
  set A := act cubeN (fun _ => s) x with hAdef
  by_cases hfin : finrank ℝ (linCone cubeN A) = 1
  swap
  · unfold theta; rw [linSpace_cone, ite_eq_right hfin]
  -- two tight constraints on one axis would be the two opposite faces
  have hcons : ∀ p ∈ A, ∀ q ∈ A, p.1 = q.1 → p = q := by
    rintro ⟨i, b⟩ hp ⟨j, c⟩ hq hij
    have hij' : i = j := hij
    subst hij'
    have hp' : ⟪cubeN (i, b), x⟫ = s := hp
    have hq' : ⟪cubeN (i, c), x⟫ = s := hq
    rw [inner_cubeN] at hp' hq'
    cases b <;> cases c <;> simp at hp' hq' ⊢ <;> linarith
  have hind : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, p ≠ q → p ≠ r → q ≠ r →
      ∀ v : R3, ⟪cubeN p, v⟫ = 0 → ⟪cubeN q, v⟫ = 0 → ⟪cubeN r, v⟫ = 0 → v = 0 := by
    intro p hp q hq r hr hpq hpr hqr v h1 h2 h3
    have e1 := inner_cubeN_eq_zero h1
    have e2 := inner_cubeN_eq_zero h2
    have e3 := inner_cubeN_eq_zero h3
    ext m
    change v m = 0
    rcases fin3_cover p.1 q.1 r.1 (fun h => hpq (hcons p hp q hq h)) (fun h => hpr (hcons p hp r
        hr h))
      (fun h => hqr (hcons q hq r hr h)) m with rfl | rfl | rfl
    · exact e1
    · exact e2
    · exact e3
  obtain ⟨p, q, hpq, hA⟩ := pair_of_finrank_one cubeN hfin hind
  have hpA : p ∈ A := by rw [hA]; exact mem_insert _ _
  have hqA : q ∈ A := by rw [hA]; exact mem_insert_of_mem _ rfl
  have hax : p.1 ≠ q.1 := fun h => hpq (hcons p hpA q hqA h)
  have i12 : ⟪cubeN p, cubeN q⟫ = 0 := by
    rw [inner_cubeN, cubeN_apply, ite_eq_right hax]; simp
  have i11 : ⟪cubeN p, cubeN p⟫ = 1 := by
    rw [inner_cubeN, cubeN_apply, ite_eq_left rfl]
    by_cases hb : p.2 = true <;> simp [hb]
  have i22 : ⟪cubeN q, cubeN q⟫ = 1 := by
    rw [inner_cubeN, cubeN_apply, ite_eq_left rfl]
    by_cases hb : q.2 = true <;> simp [hb]
  have hli : LinearIndependent ℝ ![cubeN p, cubeN q] :=
    linIndep_pair_of_gram (by rw [i11, i22, i12]; norm_num)
  rw [theta_pair cubeN hA hli, (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).1
      i12,
    Submodule.Quotient.mk_eq_zero, mem_ratPi_iff]
  exact ⟨1 / 2, by push_cast; ring⟩

/-- **Gap 2 of study 2, closed (cube).** The Dehn invariant of the cube `[-s, s]³`, as a set, is
zero. -/
theorem dehnSet_cube (s : ℝ) (hs : 0 < s) : dehnSet (cubeSet s) = 0 := by
  rw [dehnSet_eq_single (cubeSet s) 0 (fun x => Or.inl (edgeAngle_cube s hs x)),
      TensorProduct.tmul_zero]

/-! ### The regular tetrahedron -/

/-- The Gram matrix of the four outward normals. -/
lemma tetN_inner (k l : Fin 4) : ⟪tetN k, tetN l⟫ = if k = l then 3 else -1 := by
  fin_cases k <;> fin_cases l <;>
    norm_num [tetN, inner3, EuclideanSpace.norm_eq, Real.sq_sqrt, Fin.sum_univ_three]

lemma tet_sum (v : R3) : ⟪tetN 0, v⟫ + ⟪tetN 1, v⟫ + ⟪tetN 2, v⟫ + ⟪tetN 3, v⟫ = 0 := by
  simp [tetN, inner3]; ring

lemma tet_inj {v : R3} (h : ∀ m, ⟪tetN m, v⟫ = 0) : v = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [tetN, inner3] at h0 h1 h2
  ext m
  change v m = 0
  fin_cases m
  · change v 0 = 0; linarith
  · change v 1 = 0; linarith
  · change v 2 = 0; linarith

lemma fin4_pair_compl : ∀ i j : Fin 4, i ≠ j →
    ∃ k l, k < l ∧ ∀ m, (m = i ∨ m = j) ↔ (m ≠ k ∧ m ≠ l) := by decide

lemma fin4_compl_pair : ∀ k l : Fin 4, k ≠ l →
    ∃ i j, i ≠ j ∧ ∀ m, (m ≠ k ∧ m ≠ l) ↔ (m = i ∨ m = j) := by decide

lemma fin4_pair_unique : ∀ k l k' l' : Fin 4, k < l → k' < l' →
    (∀ m, (m ≠ k ∧ m ≠ l) ↔ (m ≠ k' ∧ m ≠ l')) → k = k' ∧ l = l' := by decide

/-- The face functionals of the regular tetrahedron give its barycentric coordinates. -/
theorem regularTetrahedronData :
    IsTetraData tetN (fun m => -tetN m) (fun _ => 1) (fun _ => 1 / 4) where
  w_pos _ := by norm_num
  delta m k := by
    rw [inner_neg_right, tetN_inner]
    split_ifs <;> norm_num
  sum_one x := by
    simp only [Fin.sum_univ_four]
    linarith [tet_sum x]
  rebuild x := by
    apply sub_eq_zero.mp
    apply tet_inj
    intro m
    rw [inner_sub_right, inner_sum]
    fin_cases m <;>
      norm_num [Fin.sum_univ_four, inner_smul_right, inner_neg_right, tetN_inner] <;>
      linarith [tet_sum x]

/-- Three distinct face normals have no common perpendicular direction. -/
lemma tet_three {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {v : R3}
    (hi : ⟪tetN i, v⟫ = 0) (hj : ⟪tetN j, v⟫ = 0) (hk : ⟪tetN k, v⟫ = 0) : v = 0 :=
  regularTetrahedronData.three hij hik hjk hi hj hk

/-- Two tight faces describe the open segment joining the opposite corners. -/
lemma tet_openSegment_iff {k l : Fin 4} (hkl : k ≠ l) (x : R3) :
    x ∈ openSegment ℝ (-tetN k) (-tetN l) ↔
      x ∈ tetraSet ∧ act tetN (fun _ => 1) x = ({k, l}ᶜ : Set (Fin 4)) :=
  regularTetrahedronData.openSegment_iff hkl x

/-- The angle class where two faces of the tetrahedron meet: arccos(1/3). -/
lemma tet_theta {A : Set (Fin 4)} {i j : Fin 4} (hij : i ≠ j) (hA : A = {i, j}) :
    theta (cone tetN A) = (Submodule.Quotient.mk tetDihedral : Angle) := by
  have hli : LinearIndependent ℝ ![tetN i, tetN j] :=
    linIndep_pair_of_gram (by
      rw [tetN_inner, tetN_inner, tetN_inner, ite_eq_left rfl, ite_eq_left rfl,
          ite_eq_right hij]; norm_num)
  rw [theta_pair tetN hA hli]
  congr 1
  unfold InnerProductGeometry.angle tetDihedral
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, tetN_inner, tetN_inner, tetN_inner,
      ite_eq_left rfl,
    ite_eq_left rfl, ite_eq_right hij, Real.mul_self_sqrt (by norm_num),
    show (-1 : ℝ) / 3 = -(1 / 3) by norm_num, Real.arccos_neg]
  ring

lemma tet_nonempty_fin4 : Nonempty (Fin 4) := ⟨0⟩

/-- At a point of the tetrahedron whose tight faces have a line as common direction space, exactly
two faces
are tight. -/
lemma tet_pair {x : R3} (hfin : finrank ℝ (linCone tetN (act tetN (fun _ => 1) x)) = 1) :
    ∃ i j, i ≠ j ∧ act tetN (fun _ => 1) x = {i, j} :=
  pair_of_finrank_one tetN hfin
    (fun _ _ _ _ _ _ hij hik hjk _ hi hj hk => tet_three hij hik hjk hi hj hk)

/-- The angle class of the tetrahedron is arccos(1/3) or 0 at every point. -/
lemma edgeAngle_tetra_cases (x : R3) :
    edgeAngle tetraSet x = (Submodule.Quotient.mk tetDihedral : Angle) ∨ edgeAngle tetraSet x
        = 0 := by
  by_cases hx : x ∈ tetraSet
  swap
  · exact Or.inr (edgeAngle_of_notMem hx)
  have he : edgeAngle tetraSet x = theta (cone tetN (act tetN (fun _ => 1) x))
      := edgeAngle_sol _ _ hx
  rw [he]
  by_cases hfin : finrank ℝ (linCone tetN (act tetN (fun _ => 1) x)) = 1
  · obtain ⟨i, j, hij, hA⟩ := tet_pair hfin
    exact Or.inl (tet_theta hij hA)
  · right; unfold theta; rw [linSpace_cone, ite_eq_right hfin]

lemma tetDihedral_class_ne_zero : (Submodule.Quotient.mk tetDihedral : Angle) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]; exact tetDihedral_not_ratPi

/-- The pairs of corners, each once. -/
def tetPairs : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun p => p.1 < p.2

lemma tetPairs_card : tetPairs.card = 6 := by decide

/-- The points of the tetrahedron with angle class arccos(1/3) are the six open edges. -/
lemma tetra_edge_set :
    {x | edgeAngle tetraSet x = (Submodule.Quotient.mk tetDihedral : Angle)} =
      ⋃ p ∈ tetPairs, openSegment ℝ (-tetN p.1) (-tetN p.2) := by
  ext x
  rw [mem_iUnion₂]
  constructor
  · intro hx
    have hx' : edgeAngle tetraSet x = (Submodule.Quotient.mk tetDihedral : Angle) := hx
    have hxs : x ∈ tetraSet := by
      by_contra hno
      rw [edgeAngle_of_notMem hno] at hx'
      exact tetDihedral_class_ne_zero hx'.symm
    have he : edgeAngle tetraSet x = theta (cone tetN (act tetN (fun _ => 1) x)) :=
      edgeAngle_sol _ _ hxs
    have hfin : finrank ℝ (linCone tetN (act tetN (fun _ => 1) x)) = 1 := by
      by_contra hno
      rw [he] at hx'
      unfold theta at hx'
      rw [linSpace_cone, ite_eq_right hno] at hx'
      exact tetDihedral_class_ne_zero hx'.symm
    obtain ⟨i, j, hij, hA⟩ := tet_pair hfin
    obtain ⟨k, l, hkl, hm⟩ := fin4_pair_compl i j hij
    refine ⟨(k, l), Finset.mem_filter.2 ⟨Finset.mem_univ _, hkl⟩, ?_⟩
    rw [tet_openSegment_iff hkl.ne]
    refine ⟨hxs, ?_⟩
    rw [hA]
    ext m
    rw [mem_insert_iff, mem_singleton_iff, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact hm m
  · rintro ⟨⟨k, l⟩, hp, hx⟩
    have hkl : k < l := (Finset.mem_filter.1 hp).2
    obtain ⟨hxs, hA⟩ := (tet_openSegment_iff hkl.ne x).1 hx
    obtain ⟨i, j, hij, hm⟩ := fin4_compl_pair k l hkl.ne
    have hA' : act tetN (fun _ => 1) x = {i, j} := by
      rw [hA]
      ext m
      rw [mem_insert_iff, mem_singleton_iff, mem_compl_iff, mem_insert_iff, mem_singleton_iff,
          not_or]
      exact hm m
    change edgeAngle tetraSet x = _
    have he : edgeAngle tetraSet x = theta (cone tetN (act tetN (fun _ => 1) x)) :=
      edgeAngle_sol _ _ hxs
    rw [he]
    exact tet_theta hij hA'

lemma hausdorff_pair_null (x y : R3) : μH[1] ({x, y} : Set R3) = 0 := by
  have := nullSingletonClass_hausdorff R3 (d := 1) one_pos
  rw [Set.insert_eq]
  exact measure_union_null (measure_singleton x) (measure_singleton y)

lemma tet_corner_ne {k l : Fin 4} (hkl : k ≠ l) : -tetN k ≠ -tetN l := by
  intro h
  have h1 : ⟪tetN k, tetN k⟫ = ⟪tetN k, tetN l⟫ := by rw [neg_injective h]
  rw [tetN_inner, tetN_inner, ite_eq_left rfl, ite_eq_right hkl] at h1
  norm_num at h1

/-- The length of an open edge: 2√2. -/
lemma tet_edge_length {k l : Fin 4} (hkl : k ≠ l) :
    μH[1] (openSegment ℝ (-tetN k) (-tetN l)) = ENNReal.ofReal (2 * √2) := by
  rw [openSegment_eq_diff (tet_corner_ne hkl), measure_sdiff_null (hausdorff_pair_null _ _),
    hausdorffMeasure_segment, edist_dist, dist_eq_norm]
  congr 1
  rw [norm_eq_sqrt_real_inner]
  have h8 : ⟪-tetN k - -tetN l, -tetN k - -tetN l⟫ = 8 := by
    simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, tetN_inner,
      ite_eq_right hkl, ite_eq_right hkl.symm, ite_true]
    norm_num
  rw [h8, show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- The total length of the six edges. -/
lemma tetra_edge_measure :
    (μH[1] {x | edgeAngle tetraSet x = (Submodule.Quotient.mk tetDihedral : Angle)}).toReal =
      6 * (2 * √2) := by
  have hdisj : (↑tetPairs : Set (Fin 4 × Fin 4)).PairwiseDisjoint
      (fun p => openSegment ℝ (-tetN p.1) (-tetN p.2)) := by
    rintro ⟨k, l⟩ hp ⟨k', l'⟩ hq hne
    have hkl : k < l := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    have hkl' : k' < l' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hA⟩ := (tet_openSegment_iff hkl.ne x).1 hx
    obtain ⟨-, hA'⟩ := (tet_openSegment_iff hkl'.ne x).1 hx'
    apply hne
    have hm : ∀ m, (m ≠ k ∧ m ≠ l) ↔ (m ≠ k' ∧ m ≠ l') := by
      intro m
      have h1 : m ∈ ({k, l}ᶜ : Set (Fin 4)) ↔ m ∈ ({k', l'}ᶜ : Set (Fin 4)) := by
        rw [← hA, ← hA']
      rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_compl_iff, mem_insert_iff,
        mem_singleton_iff, not_or] at h1
      exact h1
    obtain ⟨e1, e2⟩ := fin4_pair_unique k l k' l' hkl hkl' hm
    rw [e1, e2]
  have hmeas : ∀ p ∈ tetPairs, MeasurableSet (openSegment ℝ (-tetN p.1) (-tetN p.2)) := by
    rintro ⟨k, l⟩ hp
    have hkl : k < l := (Finset.mem_filter.1 hp).2
    rw [openSegment_eq_diff (tet_corner_ne hkl.ne)]
    have hcl : IsClosed (segment ℝ (-tetN k) (-tetN l)) := by
      rw [segment_eq_image]
      exact (isCompact_Icc.image (by fun_prop)).isClosed
    exact hcl.measurableSet.diff
      ((measurableSet_singleton _).insert _)
  rw [tetra_edge_set, measure_biUnion_finset hdisj hmeas,
    Finset.sum_congr rfl (fun p hp => tet_edge_length (Finset.mem_filter.1 hp).2.ne),
    Finset.sum_const, tetPairs_card, nsmul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num

/-- **Gap 3 of study 2, closed (tetrahedron).** The Dehn invariant of the regular tetrahedron with
corners
(−1,−1,−1), (1,1,−1), (1,−1,1), (−1,1,1), as a set, is study 1's edge-list value for six edges of
length 2√2
at arccos(1/3). -/
theorem dehnSet_tetra : dehnSet tetraSet = dehn (tetrahedron (2 * √2)) := by
  rw [dehnSet_eq_single tetraSet _ edgeAngle_tetra_cases, tetra_edge_measure]
  unfold tetrahedron
  rw [dehn_const, List.sum_replicate, nsmul_eq_mul]
  unfold edgeTerm
  norm_num

/-- **Dehn's theorem.** The regular tetrahedron is not scissors congruent to any cube: it cannot
be cut into
finitely many convex polytopes that, moved rigidly, fill a cube. -/
theorem tetra_not_scissorsCongruent_cube (s : ℝ) (hs : 0 < s) :
    ¬ ScissorsCongruent tetraSet (cubeSet s) := by
  apply not_scissorsCongruent_of_dehnSet_ne isPoly_tetra (isPoly_cube s)
  rw [dehnSet_tetra, dehnSet_cube s hs]
  exact dehn_tetrahedron_ne_zero (by positivity)

end DehnCanon.Library
