/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.RationalAngles
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
Lean study 4 of the shape-language canon (DICTO, 19 Nov 2026), part M: the Dehn invariant of a
tetrahedron
given by its four corners and four face normals, and a test for "not zero".

`IsTetraData n p b w`: `p k` are the corners, `n m` the outward normal of the face opposite the
corner `m`,
`⟪n m, x⟫ ≤ b m` the half-space of that face, and `w m (b m - ⟪n m, x⟫)` the barycentric coordinates
(1 at the corner `m`, 0 at the three others; they sum to 1 and rebuild `x`). These are finitely many
identities, checked by arithmetic for a concrete solid.

* `IsTetraData.eq_convexHull`: the solid `sol n b` is the convex hull of the four corners.
* `IsTetraData.openSegment_iff`: the points where exactly the two faces other than `k`, `l` are
  tight are the
  points of the open segment between the corners `k` and `l` (as in study 3 for the regular
  tetrahedron).
* `IsTetraData.dehnSet_eq`: `dehnSet (sol n b)` = Σ over the six edges of (distance of the two
  corners) ⊗
  (angle class of the two faces through the edge).
* `tmul_add_tmul_ne_zero`: `L₁ ⊗ θ₁ + L₂ ⊗ θ₂ ≠ 0` when `L₁` is not a rational multiple of `L₂`
  and `θ₁` is not
  a rational multiple of π.

Credits: Mathlib `MeasureTheory.hausdorffMeasure_segment`, `Convex.sum_mem`, `convexHull_min`,
`Submodule.exists_dual_map_eq_bot_of_notMem`, `Module.forall_dual_apply_eq_zero_iff`; study 2's
`dehnSet_eq_dehn_edgeList`; study 3's `pair_of_finrank_one` and the finite facts about four corners.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-- **A test for "not zero".** If the length `L₁` is not a rational multiple of the length `L₂`,
and the angle
class `θ₁` is not zero (the angle is not a rational multiple of π), then `L₁ ⊗ θ₁ + L₂ ⊗ θ₂ ≠ 0`,
whatever
`θ₂` is. -/
theorem tmul_add_tmul_ne_zero {L₁ L₂ : ℝ} {θ₁ θ₂ : Angle} (hL : L₁ ∉ Submodule.span ℚ {L₂})
    (hθ : θ₁ ≠ 0) : L₁ ⊗ₜ[ℚ] θ₁ + L₂ ⊗ₜ[ℚ] θ₂ ≠ (0 : DehnSpace) := by
  intro h
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hL inferInstance
  have hf2 : f L₂ = 0 := by
    have h1 : f L₂ ∈ (Submodule.span ℚ {L₂}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rw [hf0] at h1
    exact (Submodule.mem_bot ℚ).1 h1
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℚ Angle, g θ₁ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hθ ((Module.forall_dual_apply_eq_zero_iff ℚ _).1 hc)
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℚ ℚ).compl₁₂ f g)) h
  rw [map_add, TensorProduct.lift.tmul, TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.mul_apply', hf2, zero_mul,
        add_zero] at h2
  exact mul_ne_zero hf hg h2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The data of a tetrahedron: corners `p`, outward face normals `n` (face `m` is opposite the
corner `m`),
face offsets `b`, and positive weights `w` that turn the face functionals into barycentric
coordinates. -/
structure IsTetraData (n p : Fin 4 → E) (b w : Fin 4 → ℝ) : Prop where
  w_pos : ∀ m, 0 < w m
  delta : ∀ m k, w m * (b m - ⟪n m, p k⟫) = if m = k then 1 else 0
  sum_one : ∀ x, ∑ m, w m * (b m - ⟪n m, x⟫) = 1
  rebuild : ∀ x, ∑ m, (w m * (b m - ⟪n m, x⟫)) • p m = x

namespace IsTetraData

variable {n p : Fin 4 → E} {b w : Fin 4 → ℝ}

lemma mem_sol_iff (h : IsTetraData n p b w) (x : E) :
    x ∈ sol n b ↔ ∀ m, 0 ≤ w m * (b m - ⟪n m, x⟫) := by
  constructor
  · intro hx m
    exact mul_nonneg (h.w_pos m).le (sub_nonneg.2 (hx m))
  · intro hx m
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_right (hx m) (h.w_pos m))

lemma mem_act_iff (h : IsTetraData n p b w) (x : E) (m : Fin 4) :
    m ∈ act n b x ↔ w m * (b m - ⟪n m, x⟫) = 0 := by
  change ⟪n m, x⟫ = b m ↔ _
  rw [mul_eq_zero, sub_eq_zero]
  constructor
  · intro h1; exact Or.inr h1.symm
  · rintro (h1 | h1)
    · exact absurd h1 (h.w_pos m).ne'
    · exact h1.symm

lemma bary_comb (n : Fin 4 → E) (b w : Fin 4 → ℝ) (m : Fin 4) {α β : ℝ} (hab : α + β = 1)
    (u v : E) :
    w m * (b m - ⟪n m, α • u + β • v⟫) =
      α * (w m * (b m - ⟪n m, u⟫)) + β * (w m * (b m - ⟪n m, v⟫)) := by
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  linear_combination (-(w m * b m)) * hab

/-- The four normals have no common perpendicular direction. -/
lemma inj (h : IsTetraData n p b w) {v : E} (hv : ∀ m, ⟪n m, v⟫ = 0) : v = 0 := by
  calc v = ∑ m, (w m * (b m - ⟪n m, v⟫)) • p m := (h.rebuild v).symm
    _ = ∑ m, (w m * (b m - ⟪n m, (0 : E)⟫)) • p m := by
        apply Finset.sum_congr rfl; intro m _; rw [hv m, inner_zero_right]
    _ = 0 := h.rebuild 0

/-- Three of the four normals have no common perpendicular direction. -/
lemma three (h : IsTetraData n p b w) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {v : E} (hi : ⟪n i, v⟫ = 0) (hj : ⟪n j, v⟫ = 0) (hk : ⟪n k, v⟫ = 0) : v = 0 := by
  have hs : ∑ m, w m * ⟪n m, v⟫ = 0 := by
    have h1 := h.sum_one v
    have h2 := h.sum_one 0
    simp only [inner_zero_right, sub_zero] at h2
    have h3 : ∑ m, w m * (b m - ⟪n m, v⟫) = ∑ m, w m * b m - ∑ m, w m * ⟪n m, v⟫ := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro m _; ring
    linarith
  apply h.inj
  intro m
  rcases fin4_cover i j k hij hik hjk m with rfl | rfl | rfl | hc
  · exact hi
  · exact hj
  · exact hk
  · have hsum : ∑ l, w l * ⟪n l, v⟫ = w m * ⟪n m, v⟫ :=
      Finset.sum_eq_single m (fun l _ hlm => by
        rcases hc l with rfl | rfl | rfl | rfl
        · rw [hi, mul_zero]
        · rw [hj, mul_zero]
        · rw [hk, mul_zero]
        · exact absurd rfl hlm) (fun h' => absurd (Finset.mem_univ m) h')
    rw [hs] at hsum
    exact (mul_eq_zero.1 hsum.symm).resolve_left (h.w_pos m).ne'

lemma corner_ne (h : IsTetraData n p b w) {k l : Fin 4} (hkl : k ≠ l) : p k ≠ p l := by
  intro he
  have h1 := h.delta k k
  have h2 := h.delta k l
  rw [he, h2, ite_eq_left rfl, ite_eq_right hkl] at h1
  exact zero_ne_one h1

/-- **The edges**: the points of the solid where exactly the two faces other than `k`, `l` are
tight are the
points of the open segment between the corners `k` and `l`. -/
lemma openSegment_iff (h : IsTetraData n p b w) {k l : Fin 4} (hkl : k ≠ l) (x : E) :
    x ∈ openSegment ℝ (p k) (p l) ↔ x ∈ sol n b ∧ act n b x = ({k, l}ᶜ : Set (Fin 4)) := by
  constructor
  · rintro ⟨α, β, hα, hβ, hab, rfl⟩
    have hb : ∀ m, w m * (b m - ⟪n m, α • p k + β • p l⟫) =
        α * (if m = k then 1 else 0) + β * (if m = l then 1 else 0) := by
      intro m; rw [bary_comb n b w m hab, h.delta, h.delta]
    refine ⟨(h.mem_sol_iff _).2 fun m => ?_, ?_⟩
    · rw [hb]; split_ifs <;> linarith
    · ext m
      rw [h.mem_act_iff, hb, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      by_cases hmk : m = k
      · rw [ite_eq_left hmk, ite_eq_right (fun h' => hkl (hmk.symm.trans h'))]
        constructor
        · intro h'; exfalso; linarith
        · intro h'; exact absurd hmk h'.1
      · by_cases hml : m = l
        · rw [ite_eq_right hmk, ite_eq_left hml]
          constructor
          · intro h'; exfalso; linarith
          · intro h'; exact absurd hml h'.2
        · rw [ite_eq_right hmk, ite_eq_right hml]
          constructor
          · intro _; exact ⟨hmk, hml⟩
          · intro _; ring
  · rintro ⟨hx, hA⟩
    have hmem : ∀ m, w m * (b m - ⟪n m, x⟫) = 0 ↔ (m ≠ k ∧ m ≠ l) := by
      intro m
      rw [← h.mem_act_iff, hA, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    have hnn := (h.mem_sol_iff x).1 hx
    have hk1 : 0 < w k * (b k - ⟪n k, x⟫) :=
      lt_of_le_of_ne (hnn k) (fun h' => ((hmem k).1 h'.symm).1 rfl)
    have hl1 : 0 < w l * (b l - ⟪n l, x⟫) :=
      lt_of_le_of_ne (hnn l) (fun h' => ((hmem l).1 h'.symm).2 rfl)
    have hsum : w k * (b k - ⟪n k, x⟫) + w l * (b l - ⟪n l, x⟫) = 1 := by
      rw [← h.sum_one x]
      exact (Fintype.sum_eq_add k l hkl (fun m hm => (hmem m).2 hm)).symm
    have hreb : (w k * (b k - ⟪n k, x⟫)) • p k + (w l * (b l - ⟪n l, x⟫)) • p l = x := by
      have h1 := Fintype.sum_eq_add (f := fun m => (w m * (b m - ⟪n m, x⟫)) • p m) k l hkl
        (fun m hm => by change (w m * (b m - ⟪n m, x⟫)) • p m = 0; rw [(hmem m).2 hm, zero_smul])
      rw [← h1]; exact h.rebuild x
    exact ⟨_, _, hk1, hl1, hsum, hreb⟩

/-- The solid is bounded. -/
lemma bounded (h : IsTetraData n p b w) : Bornology.IsBounded (sol n b) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∑ m, ‖p m‖, fun x hx => ?_⟩
  have hnn := (h.mem_sol_iff x).1 hx
  have hle : ∀ m, w m * (b m - ⟪n m, x⟫) ≤ 1 := by
    intro m
    rw [← h.sum_one x]
    exact Finset.single_le_sum (f := fun m => w m * (b m - ⟪n m, x⟫)) (fun i _ => hnn i)
      (Finset.mem_univ m)
  calc ‖x‖ = ‖∑ m, (w m * (b m - ⟪n m, x⟫)) • p m‖ := by rw [h.rebuild x]
    _ ≤ ∑ m, ‖(w m * (b m - ⟪n m, x⟫)) • p m‖ := norm_sum_le _ _
    _ ≤ ∑ m, ‖p m‖ := by
        apply Finset.sum_le_sum; intro m _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn m)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hle m)

/-- The solid is a convex polytope. -/
lemma isPoly (h : IsTetraData n p b w) : IsPoly (sol n b) :=
  ⟨h.bounded, Fin 4, inferInstance, n, b, rfl⟩

/-- **The solid is the convex hull of its four corners.** -/
theorem eq_convexHull (h : IsTetraData n p b w) : sol n b = convexHull ℝ (Set.range p) := by
  apply Subset.antisymm
  · intro x hx
    rw [← h.rebuild x]
    exact (convex_convexHull ℝ _).sum_mem (fun m _ => (h.mem_sol_iff x).1 hx m) (h.sum_one x)
      (fun m _ => subset_convexHull ℝ _ (mem_range_self m))
  · apply convexHull_min _ (convex_sol n b)
    rintro _ ⟨k, rfl⟩
    rw [h.mem_sol_iff]
    intro m
    rw [h.delta]; split_ifs <;> norm_num

end IsTetraData

lemma openSegment_eq_diff' {x y : E} (hxy : x ≠ y) :
    openSegment ℝ x y = segment ℝ x y \ {x, y} := by
  ext z; constructor
  · intro hz
    refine ⟨openSegment_subset_segment ℝ x y hz, ?_⟩
    rintro (rfl | rfl)
    · exact hxy (left_mem_openSegment_iff.1 hz)
    · exact hxy (right_mem_openSegment_iff.1 hz)
  · rintro ⟨hz, hne⟩
    exact mem_openSegment_of_ne_left_right (fun h => hne (Or.inl h.symm))
      (fun h => hne (Or.inr h.symm)) hz

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- The length of an open segment is the distance of its ends. -/
lemma hausdorff_openSegment {x y : E} (hxy : x ≠ y) :
    (μH[1] (openSegment ℝ x y)).toReal = dist x y := by
  have hnull : μH[1] ({x, y} : Set E) = 0 := by
    have := nullSingletonClass_hausdorff E (d := 1) one_pos
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton x) (measure_singleton y)
  rw [openSegment_eq_diff' hxy, measure_sdiff_null hnull, hausdorffMeasure_segment, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

/-- The six pairs of corners, written out. -/
lemma tetPairs_eq : tetPairs = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide

lemma sum_tetPairs {M : Type*} [AddCommMonoid M] (f : Fin 4 × Fin 4 → M) :
    ∑ q ∈ tetPairs, f q = f (0, 1) + f (0, 2) + f (0, 3) + f (1, 2) + f (1, 3) + f (2, 3) := by
  rw [tetPairs_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

/-- The two faces through the edge between the corners `k`, `l` are the two other ones, `i`, `j`. -/
lemma compl_pair_eq {k l i j : Fin 4} (h : ∀ m : Fin 4, (m ≠ k ∧ m ≠ l) ↔ (m = i ∨ m = j)) :
    ({k, l}ᶜ : Set (Fin 4)) = {i, j} := by
  ext m
  rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_insert_iff, mem_singleton_iff]
  exact h m

/-- **The angle class of two faces from the Gram numbers of their normals.** If `⟪aᵢ, aᵢ⟫ = X`,
`⟪aⱼ, aⱼ⟫ = Y` and `⟪aᵢ, aⱼ⟫ = -d`, the interior angle where the two faces meet is `arccos (d /
√(X Y))`. -/
theorem theta_pair_of_gram [Fact (finrank ℝ E = 3)] {ι : Type} (a : ι → E) {A : Set ι} {i j : ι}
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

/-- Squared length in coordinates. -/
lemma norm3_sq (p q r : ℝ) : ‖(!₂[p, q, r] : R3)‖ ^ 2 = p ^ 2 + q ^ 2 + r ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Distance in coordinates. -/
lemma dist3 (x y : R3) {d : ℝ} (hd : 0 ≤ d)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = d ^ 2) : dist x y = d := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]
  rw [h, Real.sqrt_sq hd]

/-- The Dehn invariant of a bounded solid given by half-spaces, as a sum over the sets `A` of
constraints:
(length of the set of points where exactly the constraints of `A` are tight) ⊗ (angle class of
their cone). -/
lemma dehnSet_eq_sum_faceSet {ι : Type} [Fintype ι] (a : ι → E) (b : ι → ℝ)
    (hb : Bornology.IsBounded (sol a b)) :
    dehnSet (sol a b) = ∑ A : Set ι, (μH[1] (faceSet a b A)).toReal ⊗ₜ[ℚ] theta (cone a A) := by
  rw [dehnSet_eq_dehn_edgeList a b hb]
  unfold dehn edgeList
  rw [List.map_map, Finset.sum_map_toList, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro A _
  unfold theta
  rw [linSpace_cone]
  by_cases h : finrank ℝ (linCone a A) = 1
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h, TensorProduct.tmul_zero]

/-- **The Dehn invariant of a tetrahedron**: the sum over its six edges of
(distance of the two corners of the edge) ⊗ (angle class of the cone of the two faces through the
edge;
the edge between the corners `k`, `l` lies on the two faces other than `k`, `l`). -/
theorem IsTetraData.dehnSet_eq [Fact (finrank ℝ E = 3)] {n p : Fin 4 → E} {b w : Fin 4 → ℝ}
    (h : IsTetraData n p b w) :
    dehnSet (sol n b) =
      ∑ q ∈ tetPairs, dist (p q.1) (p q.2) ⊗ₜ[ℚ] theta (cone n ({q.1, q.2}ᶜ : Set (Fin 4))) := by
  classical
  let F : Fin 4 × Fin 4 → Set (Fin 4) := fun q => {q.1, q.2}ᶜ
  have hzero : ∀ A : Set (Fin 4), A ∉ tetPairs.image F →
      (μH[1] (faceSet n b A)).toReal ⊗ₜ[ℚ] theta (cone n A) = 0 := by
    intro A hA
    by_cases hfin : finrank ℝ (linCone n A) = 1
    · exfalso
      obtain ⟨i, j, hij, rfl⟩ := pair_of_finrank_one n hfin
        (fun _ _ _ _ _ _ hij hik hjk _ hi hj hk => h.three hij hik hjk hi hj hk)
      obtain ⟨k, l, hkl, hm⟩ := fin4_pair_compl i j hij
      apply hA
      rw [Finset.mem_image]
      refine ⟨(k, l), Finset.mem_filter.2 ⟨Finset.mem_univ _, hkl⟩, ?_⟩
      ext m
      change m ∈ ({k, l}ᶜ : Set (Fin 4)) ↔ m ∈ ({i, j} : Set (Fin 4))
      rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_insert_iff,
          mem_singleton_iff]
      exact (hm m).symm
    · unfold theta; rw [linSpace_cone, ite_eq_right hfin, TensorProduct.tmul_zero]
  have hinj : Set.InjOn F (tetPairs : Set (Fin 4 × Fin 4)) := by
    rintro ⟨k, l⟩ hq ⟨k', l'⟩ hq' hF
    have hkl : k < l := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
    have hkl' : k' < l' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq')).2
    have hm : ∀ m, (m ≠ k ∧ m ≠ l) ↔ (m ≠ k' ∧ m ≠ l') := by
      intro m
      have h1 : m ∈ ({k, l}ᶜ : Set (Fin 4)) ↔ m ∈ ({k', l'}ᶜ : Set (Fin 4)) := by
        change m ∈ F (k, l) ↔ m ∈ F (k', l')
        rw [hF]
      rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_compl_iff, mem_insert_iff,
        mem_singleton_iff, not_or] at h1
      exact h1
    obtain ⟨e1, e2⟩ := fin4_pair_unique k l k' l' hkl hkl' hm
    rw [e1, e2]
  rw [dehnSet_eq_sum_faceSet n b h.bounded,
    ← Finset.sum_subset (Finset.subset_univ (tetPairs.image F)) (fun A _ hA => hzero A hA),
    Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  rintro ⟨k, l⟩ hq
  have hkl : k < l := (Finset.mem_filter.1 hq).2
  have hface : faceSet n b (F (k, l)) = openSegment ℝ (p k) (p l) := by
    ext x; exact (h.openSegment_iff hkl.ne x).symm
  rw [hface, hausdorff_openSegment (h.corner_ne hkl.ne)]

end DehnCanon.Library
