/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.Definitions
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.VectorSpace

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Constraint polytopes and finite convex decompositions
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators MatrixOrder

namespace OlevskiiGram

/-- The constraint polytope cut out by the inequalities `|⟪x,a_j⟫| ≤ 1`. -/
def constraintPolytope {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) : Set (n → ℝ) :=
  {x | ∀ j, |realDot x (a j)| ≤ 1}

/-- The vectors whose constraints are active at `x`. -/
def activeConstraintVectors {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (x : n → ℝ) : Set (n → ℝ) :=
  {v | ∃ j, v = a j ∧ |realDot x (a j)| = 1}

/-- The span of the active constraint vectors at `x`. -/
def activeConstraintSpan {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (x : n → ℝ) : Submodule ℝ (n → ℝ) :=
  Submodule.span ℝ (activeConstraintVectors a x)

/-- The finite set of indices whose constraints are active at `x`. -/
def activeConstraintIndexSet {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (x : n → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun j => |realDot x (a j)| = 1

/-- The number of active constraints at `x`. -/
def activeConstraintCount {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (x : n → ℝ) : ℕ :=
  (activeConstraintIndexSet a x).card

/-- Membership in the finite active-index set is exactly activity of the constraint. -/
theorem mem_activeConstraintIndexSet_iff
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (x : n → ℝ) (j : ι) :
    j ∈ activeConstraintIndexSet a x ↔ |realDot x (a j)| = 1 := by
  classical
  simp [activeConstraintIndexSet]

/-- Adding one genuinely new active index strictly increases the active count. -/
theorem activeConstraintCount_lt_of_subset_and_new
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (x y : n → ℝ)
    (hsubset : activeConstraintIndexSet a x ⊆ activeConstraintIndexSet a y)
    {jNew : ι}
    (hjOld : jNew ∉ activeConstraintIndexSet a x)
    (hjNew : jNew ∈ activeConstraintIndexSet a y) :
    activeConstraintCount a x < activeConstraintCount a y := by
  classical
  have hne : activeConstraintIndexSet a x ≠ activeConstraintIndexSet a y := by
    intro hxy
    exact hjOld (by simpa [hxy] using hjNew)
  have hssub :
      activeConstraintIndexSet a x ⊂ activeConstraintIndexSet a y :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
  simpa [activeConstraintCount] using Finset.card_lt_card hssub

/--
If all old active constraints remain active and one inactive constraint becomes
active, then the active count strictly increases.
-/
theorem activeConstraintCount_lt_of_old_active_and_new
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (x y : n → ℝ) {jNew : ι}
    (hold : ∀ j, |realDot x (a j)| = 1 → |realDot y (a j)| = 1)
    (hjOldInactive : |realDot x (a jNew)| ≠ 1)
    (hjNewActive : |realDot y (a jNew)| = 1) :
    activeConstraintCount a x < activeConstraintCount a y := by
  classical
  apply activeConstraintCount_lt_of_subset_and_new a x y
  · intro j hj
    rw [mem_activeConstraintIndexSet_iff] at hj ⊢
    exact hold j hj
  · rw [mem_activeConstraintIndexSet_iff]
    exact hjOldInactive
  · rw [mem_activeConstraintIndexSet_iff]
    exact hjNewActive

/-- Predicate for a point maximizing `Φ` on the constraint polytope. -/
def IsConstraintPolytopeMaximizer {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ) (x : n → ℝ) : Prop :=
  x ∈ constraintPolytope a ∧
    ∀ y : n → ℝ, y ∈ constraintPolytope a → Φ y ≤ Φ x

/-- Linearity of the finite real dot product in its first argument. -/
theorem realDot_add {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    realDot (x + y) z = realDot x z + realDot y z := by
  simp [realDot, add_mul, Finset.sum_add_distrib]

/-- Homogeneity of the finite real dot product in its first argument. -/
theorem realDot_smul {ι : Type*} [Fintype ι] (c : ℝ) (x y : ι → ℝ) :
    realDot (c • x) y = c * realDot x y := by
  simp [realDot, Finset.mul_sum, mul_assoc]

/-- Linearity of the finite real dot product in its second argument. -/
theorem realDot_add_right {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    realDot x (y + z) = realDot x y + realDot x z := by
  simp [realDot, mul_add, Finset.sum_add_distrib]

/-- Homogeneity of the finite real dot product in its second argument. -/
theorem realDot_smul_right {ι : Type*} [Fintype ι] (c : ℝ) (x y : ι → ℝ) :
    realDot x (c • y) = c * realDot x y := by
  simp [realDot, Finset.mul_sum, mul_left_comm]

/-- The dot product with a fixed first argument, as a linear functional. -/
def realDotLinearFunctional {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun y := realDot x y
  map_add' y z := realDot_add_right x y z
  map_smul' c y := realDot_smul_right c x y

/-- A vector with zero dot product against itself is zero. -/
theorem realDot_self_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℝ} :
    realDot x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    exact (Finset.sum_mul_self_eq_zero_iff Finset.univ x).mp
      (by simpa [realDot] using hx) i (Finset.mem_univ i)
  · intro hx
    simp [hx, realDot]

/-- The coordinate vector representing a linear functional via `realDot`. -/
def dualRepresenter {ι : Type*}
    (φ : (ι → ℝ) →ₗ[ℝ] ℝ) : ι → ℝ := by
  classical
  exact fun i => φ (Pi.single i (1 : ℝ))

/-- Every linear functional on a finite coordinate space is represented by `realDot`. -/
theorem realDot_dualRepresenter {ι : Type*} [Fintype ι]
    (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    realDot (dualRepresenter φ) x = φ x := by
  classical
  calc
    realDot (dualRepresenter φ) x
        = ∑ i, x i * φ (Pi.single i (1 : ℝ)) := by
          simp [realDot, dualRepresenter, mul_comm]
    _ = φ (∑ i, x i • Pi.single (M := fun _ => ℝ) i (1 : ℝ)) := by
          simp [map_sum]
    _ = φ x := by
          rw [← pi_eq_sum_univ' x]

/-- A nonzero functional has a nonzero `realDot` representer. -/
theorem dualRepresenter_ne_zero {ι : Type*} [Finite ι]
    {φ : (ι → ℝ) →ₗ[ℝ] ℝ} :
    φ ≠ 0 → dualRepresenter φ ≠ 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  intro hφ hrep
  apply hφ
  ext x
  have hx := (realDot_dualRepresenter φ x).symm
  simpa [hrep, realDot] using hx

/-- Continuity of the finite real dot product as a function of its first argument. -/
theorem continuous_realDot_left {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    Continuous fun x : ι → ℝ => realDot x y := by
  unfold realDot
  fun_prop

/-- The linear map collecting all constraint functionals. -/
def constraintLinearMap {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) : (n → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x j := realDot x (a j)
  map_add' x y := by
    ext j
    exact realDot_add x y (a j)
  map_smul' c x := by
    ext j
    exact realDot_smul c x (a j)

/-- If the constraint vectors span, then the constraint map is injective. -/
theorem constraintLinearMap_injective_of_span
    {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤) :
    Function.Injective (constraintLinearMap a) := by
  intro x y hxy
  suffices x - y = 0 by
    exact sub_eq_zero.mp this
  apply realDot_self_eq_zero.mp
  let φ : (n → ℝ) →ₗ[ℝ] ℝ := realDotLinearFunctional (x - y)
  have hmap : constraintLinearMap a (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hrange : Set.range a ⊆ φ.ker := by
    rintro v ⟨j, rfl⟩
    have hcoord := congrFun hmap j
    change realDot (x - y) (a j) = 0
    simpa [constraintLinearMap] using hcoord
  have hspan_le : Submodule.span ℝ (Set.range a) ≤ φ.ker :=
    (Submodule.span_le).2 hrange
  have hxmem : x - y ∈ φ.ker := by
    have htop_le : (⊤ : Submodule ℝ (n → ℝ)) ≤ φ.ker := by
      simpa [hspan] using hspan_le
    exact htop_le trivial
  exact hxmem

/--
If the active span is proper, there is a nonzero direction annihilating every
active constraint vector under `realDot`.
-/
theorem exists_nonzero_annihilating_activeSpan
    {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (x : n → ℝ)
    (hproper : activeConstraintSpan a x ≠ ⊤) :
    ∃ h : n → ℝ,
      h ≠ 0 ∧ ∀ j, |realDot x (a j)| = 1 → realDot h (a j) = 0 := by
  classical
  have hlt : activeConstraintSpan a x < ⊤ := lt_top_iff_ne_top.mpr hproper
  rcases Submodule.exists_le_ker_of_lt_top (activeConstraintSpan a x) hlt with
    ⟨φ, hφne, hleker⟩
  refine ⟨dualRepresenter φ, dualRepresenter_ne_zero hφne, ?_⟩
  intro j hj
  have haj_mem : a j ∈ activeConstraintSpan a x := by
    exact Submodule.subset_span ⟨j, rfl, hj⟩
  have hφaj : φ (a j) = 0 := hleker haj_mem
  simpa [hφaj] using realDot_dualRepresenter φ (a j)

/-- Active constraints remain active along a direction annihilating them. -/
theorem activeConstraint_stays_active_along_annihilating_direction
    {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (x h : n → ℝ)
    (hh : ∀ j, |realDot x (a j)| = 1 → realDot h (a j) = 0)
    {j : ι} (hj : |realDot x (a j)| = 1) (t : ℝ) :
    |realDot (x + t • h) (a j)| = 1 := by
  have hdot : realDot (x + t • h) (a j) = realDot x (a j) := by
    rw [realDot_add, realDot_smul, hh j hj]
    ring
  rw [hdot, hj]

/-- A strict scalar inequality has a positive interval of perturbative room. -/
theorem abs_add_mul_le_one_of_abs_lt_one {u v : ℝ} (hu : |u| < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ → |u + t * v| ≤ 1 := by
  let δ : ℝ := (1 - |u|) / (|v| + 1)
  have hnum : 0 < 1 - |u| := by linarith
  have hden : 0 < |v| + 1 := by positivity
  refine ⟨δ, div_pos hnum hden, ?_⟩
  intro t ht
  have hvfrac : δ * |v| ≤ 1 - |u| := by
    dsimp [δ]
    have hle : |v| / (|v| + 1) ≤ 1 := by
      rw [div_le_one hden]
      linarith [abs_nonneg v]
    have hnum_nonneg : 0 ≤ 1 - |u| := le_of_lt hnum
    calc
      (1 - |u|) / (|v| + 1) * |v|
          = (1 - |u|) * (|v| / (|v| + 1)) := by ring
      _ ≤ (1 - |u|) * 1 := by
          exact mul_le_mul_of_nonneg_left hle hnum_nonneg
      _ = 1 - |u| := by ring
  calc
    |u + t * v| ≤ |u| + |t * v| := abs_add_le _ _
    _ = |u| + |t| * |v| := by rw [abs_mul]
    _ ≤ |u| + δ * |v| := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (abs_nonneg v))
    _ ≤ |u| + (1 - |u|) := by
        exact add_le_add le_rfl hvfrac
    _ = 1 := by ring

/-- A single inactive constraint has a positive interval of allowed motion. -/
theorem inactiveConstraint_has_room
    {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (x h : n → ℝ) {j : ι}
    (hj : |realDot x (a j)| < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| ≤ δ → |realDot (x + t • h) (a j)| ≤ 1 := by
  rcases abs_add_mul_le_one_of_abs_lt_one
      (u := realDot x (a j)) (v := realDot h (a j)) hj with
    ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht
  have hdot :
      realDot (x + t • h) (a j) =
        realDot x (a j) + t * realDot h (a j) := by
    rw [realDot_add, realDot_smul]
  rw [hdot]
  exact hδ t ht

/--
If a direction annihilates every active constraint, then a small whole segment
around the base point remains in the constraint polytope.
-/
theorem constraintPolytope_has_local_line_segment
    {n ι : Type*} [Fintype n] [Finite ι]
    (a : ι → n → ℝ) (x h : n → ℝ)
    (hx : x ∈ constraintPolytope a)
    (hh : ∀ j, |realDot x (a j)| = 1 → realDot h (a j) = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| ≤ δ → x + t • h ∈ constraintPolytope a := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have room :
      ∀ j : ι, ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, |t| ≤ δ → |realDot (x + t • h) (a j)| ≤ 1 := by
    intro j
    by_cases hactive : |realDot x (a j)| = 1
    · refine ⟨1, zero_lt_one, ?_⟩
      intro t _ht
      exact le_of_eq
        (activeConstraint_stays_active_along_annihilating_direction a x h hh hactive t)
    · have hinactive : |realDot x (a j)| < 1 :=
        lt_of_le_of_ne (hx j) hactive
      exact inactiveConstraint_has_room a x h (j := j) hinactive
  by_cases huniv : (Finset.univ : Finset ι).Nonempty
  · let δOf : ι → ℝ := fun j => Classical.choose (room j)
    obtain ⟨j₀, _hj₀mem, hj₀min⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) δOf huniv
    refine ⟨δOf j₀, ?_, ?_⟩
    · exact (Classical.choose_spec (room j₀)).1
    · intro t ht j
      have hle : |t| ≤ δOf j := by
        exact ht.trans (hj₀min j (Finset.mem_univ j))
      exact (Classical.choose_spec (room j)).2 t hle
  · refine ⟨1, zero_lt_one, ?_⟩
    intro _t _ht j
    exact False.elim (huniv ⟨j, Finset.mem_univ j⟩)

/-- The constraint polytope always contains the origin. -/
theorem constraintPolytope_zero_mem {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) :
    (0 : n → ℝ) ∈ constraintPolytope a := by
  intro j
  simp [realDot]

/-- The constraint polytope is closed. -/
theorem constraintPolytope_isClosed {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) :
    IsClosed (constraintPolytope a) := by
  rw [constraintPolytope, Set.ofPred_forall]
  exact isClosed_iInter fun j =>
    isClosed_le ((continuous_realDot_left (a j)).abs)
      (continuous_const : Continuous fun _ : n → ℝ => (1 : ℝ))

/-- Under the spanning hypothesis, the constraint polytope is bounded. -/
theorem constraintPolytope_isBounded
    {n ι : Type*} [Fintype n] [Finite ι]
    (a : ι → n → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤) :
    Bornology.IsBounded (constraintPolytope a) := by
  let : Fintype ι := Fintype.ofFinite ι
  rcases (constraintLinearMap a).injective_iff_antilipschitz.mp
      (constraintLinearMap_injective_of_span a hspan) with
    ⟨K, _hKpos, hanti⟩
  refine isBounded_iff_forall_norm_le.2 ⟨(K : ℝ), ?_⟩
  intro x hx
  have hMx : ‖constraintLinearMap a x‖ ≤ (1 : ℝ) := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    simpa [constraintLinearMap, Real.norm_eq_abs] using hx j
  calc
    ‖x‖ ≤ (K : ℝ) * ‖constraintLinearMap a x‖ := by
      simpa using hanti.le_mul_norm (map_zero (constraintLinearMap a)) x
    _ ≤ (K : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left hMx K.coe_nonneg
    _ = (K : ℝ) := by
      rw [mul_one]

/-- Under the spanning hypothesis, the constraint polytope is compact. -/
theorem constraintPolytope_isCompact
    {n ι : Type*} [Fintype n] [Finite ι]
    (a : ι → n → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤) :
    IsCompact (constraintPolytope a) :=
  Metric.isCompact_of_isClosed_isBounded
    (constraintPolytope_isClosed a)
    (constraintPolytope_isBounded a hspan)

/-- A continuous function on the constraint polytope attains its maximum. -/
theorem exists_constraintPolytope_maximizer
    {n ι : Type*} [Fintype n] [Finite ι]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (hcont : Continuous Φ) :
    ∃ x₀ : n → ℝ,
      x₀ ∈ constraintPolytope a ∧
      ∀ x : n → ℝ, x ∈ constraintPolytope a → Φ x ≤ Φ x₀ := by
  rcases (constraintPolytope_isCompact a hspan).exists_isMaxOn
      ⟨0, constraintPolytope_zero_mem a⟩ hcont.continuousOn with
    ⟨x₀, hx₀, hmax⟩
  exact ⟨x₀, hx₀, fun x hx => hmax hx⟩

/-- The number of active constraints is bounded by the total number of constraints. -/
theorem activeConstraintCount_le_card
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (x : n → ℝ) :
    activeConstraintCount a x ≤ Fintype.card ι := by
  classical
  calc
    activeConstraintCount a x
        = ((Finset.univ : Finset ι).filter
            (fun j => |realDot x (a j)| = 1)).card := by
          simp [activeConstraintCount, activeConstraintIndexSet]
    _ ≤ (Finset.univ : Finset ι).card := Finset.card_filter_le _ _
    _ = Fintype.card ι := Finset.card_univ

/-- There is a maximizer whose number of active constraints is maximal. -/
theorem exists_constraintPolytope_maximizer_max_active
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (hcont : Continuous Φ) :
    ∃ x₀ : n → ℝ,
      IsConstraintPolytopeMaximizer a Φ x₀ ∧
      ∀ x : n → ℝ,
        IsConstraintPolytopeMaximizer a Φ x →
          activeConstraintCount a x ≤ activeConstraintCount a x₀ := by
  classical
  rcases exists_constraintPolytope_maximizer a Φ hspan hcont with
    ⟨x, hxmem, hxmax⟩
  let P : ℕ → Prop := fun k =>
    ∃ x : n → ℝ, IsConstraintPolytopeMaximizer a Φ x ∧ activeConstraintCount a x = k
  have hP : P (activeConstraintCount a x) :=
    ⟨x, ⟨hxmem, hxmax⟩, rfl⟩
  have hbound : activeConstraintCount a x ≤ Fintype.card ι :=
    activeConstraintCount_le_card a x
  let k₀ := Nat.findGreatest P (Fintype.card ι)
  have hk₀P : P k₀ := Nat.findGreatest_spec (P := P) hbound hP
  rcases hk₀P with ⟨x₀, hx₀max, hx₀card⟩
  refine ⟨x₀, hx₀max, ?_⟩
  intro y hymax
  have hyP : P (activeConstraintCount a y) := ⟨y, hymax, rfl⟩
  have hybound : activeConstraintCount a y ≤ Fintype.card ι :=
    activeConstraintCount_le_card a y
  have hle : activeConstraintCount a y ≤ k₀ :=
    Nat.le_findGreatest (P := P) hybound hyP
  rwa [hx₀card]

/-- The constraint polytope is convex. -/
theorem constraintPolytope_convex {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) :
    Convex ℝ (constraintPolytope a) := by
  rw [convex_iff_add_mem]
  intro x hx y hy c d hc hd hcd j
  have hxj : |realDot x (a j)| ≤ 1 := hx j
  have hyj : |realDot y (a j)| ≤ 1 := hy j
  have hlin :
      realDot (c • x + d • y) (a j) =
        c * realDot x (a j) + d * realDot y (a j) := by
    rw [realDot_add, realDot_smul, realDot_smul]
  calc
    |realDot (c • x + d • y) (a j)|
        = |c * realDot x (a j) + d * realDot y (a j)| := by rw [hlin]
    _ ≤ |c * realDot x (a j)| + |d * realDot y (a j)| := abs_add_le _ _
    _ = c * |realDot x (a j)| + d * |realDot y (a j)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hd]
    _ ≤ c * 1 + d * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hxj hc)
          (mul_le_mul_of_nonneg_left hyj hd)
    _ = 1 := by
        nlinarith

/--
If a maximizer is a genuine convex combination of two feasible endpoints, then
both endpoints are maximizers.
-/
theorem endpoints_are_maximizers_of_convex_combination
    {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    {x₀ xPlus xMinus : n → ℝ} {c d : ℝ}
    (hconv : ConvexOn ℝ (constraintPolytope a) Φ)
    (hx₀max : IsConstraintPolytopeMaximizer a Φ x₀)
    (hxPlus : xPlus ∈ constraintPolytope a)
    (hxMinus : xMinus ∈ constraintPolytope a)
    (hc : 0 < c) (hd : 0 < d) (hcd : c + d = 1)
    (hcomb : x₀ = c • xPlus + d • xMinus) :
    IsConstraintPolytopeMaximizer a Φ xPlus ∧
      IsConstraintPolytopeMaximizer a Φ xMinus := by
  have hxMinus_le_combo : Φ xMinus ≤ Φ (c • xPlus + d • xMinus) := by
    rw [← hcomb]
    exact hx₀max.2 xMinus hxMinus
  have hx₀_le_xPlus : Φ x₀ ≤ Φ xPlus := by
    rw [hcomb]
    exact hconv.le_left_of_right_le' hxPlus hxMinus hc hd.le hcd hxMinus_le_combo
  have hxPlus_le_combo : Φ xPlus ≤ Φ (c • xPlus + d • xMinus) := by
    rw [← hcomb]
    exact hx₀max.2 xPlus hxPlus
  have hx₀_le_xMinus : Φ x₀ ≤ Φ xMinus := by
    rw [hcomb]
    exact hconv.le_right_of_left_le' hxPlus hxMinus hc.le hd hcd hxPlus_le_combo
  constructor
  · exact ⟨hxPlus, fun y hy => (hx₀max.2 y hy).trans hx₀_le_xPlus⟩
  · exact ⟨hxMinus, fun y hy => (hx₀max.2 y hy).trans hx₀_le_xMinus⟩

/-- Some spanning constraint has nonzero pairing with every nonzero direction. -/
theorem exists_constraint_not_annihilated_of_span
    {n ι : Type*} [Fintype n]
    (a : ι → n → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    {h : n → ℝ} (hhne : h ≠ 0) :
    ∃ j : ι, realDot h (a j) ≠ 0 := by
  by_contra hnone
  have hall : ∀ j : ι, realDot h (a j) = 0 := by
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  let φ : (n → ℝ) →ₗ[ℝ] ℝ := realDotLinearFunctional h
  have hrange : Set.range a ⊆ φ.ker := by
    rintro v ⟨j, rfl⟩
    exact hall j
  have hspan_le : Submodule.span ℝ (Set.range a) ≤ φ.ker :=
    (Submodule.span_le).2 hrange
  have hhker : h ∈ φ.ker := by
    have htop_le : (⊤ : Submodule ℝ (n → ℝ)) ≤ φ.ker := by
      simpa [hspan] using hspan_le
    exact htop_le trivial
  have hself : realDot h h = 0 := by
    simpa [φ, realDotLinearFunctional] using hhker
  exact hhne (realDot_self_eq_zero.mp hself)

/-- The positive endpoint time for the scalar inequality `|u + t v| ≤ 1`. -/
def endpointTimeBound (u v : ℝ) : ℝ :=
  if 0 < v then (1 - u) / v else (-1 - u) / v

/--
For a strictly inactive scalar constraint with nonzero derivative, the endpoint
time is positive.
-/
theorem endpointTimeBound_pos {u v : ℝ}
    (hu : |u| < 1) (hv : v ≠ 0) :
    0 < endpointTimeBound u v := by
  by_cases hvpos : 0 < v
  · have hnum : 0 < 1 - u := by
      have hright := (abs_lt.mp hu).2
      linarith
    simp [endpointTimeBound, hvpos, div_pos hnum hvpos]
  · have hvneg : v < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hv
    have hnum : -1 - u < 0 := by
      have hleft := (abs_lt.mp hu).1
      linarith
    simp [endpointTimeBound, hvpos, div_pos_of_neg_of_neg hnum hvneg]

/--
If `0 ≤ t` is below the scalar endpoint time, then the corresponding scalar
constraint remains feasible.
-/
theorem abs_add_mul_le_one_of_le_endpointTimeBound {u v t : ℝ}
    (hu : |u| ≤ 1) (htnonneg : 0 ≤ t)
    (htle : t ≤ endpointTimeBound u v) :
    |u + t * v| ≤ 1 := by
  have hu_bounds := abs_le.mp hu
  by_cases hvpos : 0 < v
  · have hvnonneg : 0 ≤ v := le_of_lt hvpos
    have ht_v_le : t * v ≤ 1 - u := by
      have hmul := mul_le_mul_of_nonneg_right htle hvnonneg
      have hvne : v ≠ 0 := ne_of_gt hvpos
      simpa [endpointTimeBound, hvpos, div_mul_cancel₀ (1 - u) hvne] using hmul
    have hlower : -1 ≤ u + t * v := by
      have htv_nonneg : 0 ≤ t * v := mul_nonneg htnonneg hvnonneg
      linarith
    have hupper : u + t * v ≤ 1 := by
      linarith
    exact abs_le.mpr ⟨hlower, hupper⟩
  · by_cases hvzero : v = 0
    · simpa [hvzero] using hu
    · have hvneg : v < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hvzero
      have hvnonpos : v ≤ 0 := le_of_lt hvneg
      have hbound_v_le : -1 - u ≤ t * v := by
        have hmul := mul_le_mul_of_nonpos_right htle hvnonpos
        rw [endpointTimeBound, ite_eq_right hvpos] at hmul
        rw [div_mul_cancel₀ (-1 - u) hvzero] at hmul
        exact hmul
      have hlower : -1 ≤ u + t * v := by
        linarith
      have htv_nonpos : t * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htnonneg hvnonpos
      have hupper : u + t * v ≤ 1 := by
        linarith
      exact abs_le.mpr ⟨hlower, hupper⟩

/-- At the scalar endpoint time, the scalar constraint is active. -/
theorem abs_add_endpointTimeBound_mul_eq_one {u v : ℝ} (hv : v ≠ 0) :
    |u + endpointTimeBound u v * v| = 1 := by
  by_cases hvpos : 0 < v
  · have hvne : v ≠ 0 := ne_of_gt hvpos
    simp [endpointTimeBound, hvpos, div_mul_cancel₀ (1 - u) hvne]
  · have hvneg : v < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hv
    have hvne : v ≠ 0 := ne_of_lt hvneg
    simp [endpointTimeBound, hvpos, div_mul_cancel₀ (-1 - u) hvne]

/--
Endpoint construction in the active-constraint
maximizer lemma.

All compactness, local-motion, and convexity/maximizer consequences have been
separated out. This lemma proves the remaining endpoint/geometric part: from
a nonzero feasible perturbation direction, one can find feasible
endpoints whose convex combination is the base point, all old active
constraints remain active at one endpoint, and one genuinely new constraint
becomes active there.
-/
theorem activeEndpointWithNewActiveConstraint
    {n ι : Type*} [Fintype n] [Finite ι]
    (a : ι → n → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (x₀ : n → ℝ) :
    activeConstraintSpan a x₀ ≠ ⊤ →
    (h : n → ℝ) →
    h ≠ 0 →
    (∀ j, |realDot x₀ (a j)| = 1 → realDot h (a j) = 0) →
    (δ : ℝ) →
    0 < δ →
    (∀ t : ℝ, |t| ≤ δ → x₀ + t • h ∈ constraintPolytope a) →
    ∃ (xPlus xMinus : n → ℝ) (c d : ℝ) (jNew : ι),
      xPlus ∈ constraintPolytope a ∧
      xMinus ∈ constraintPolytope a ∧
      0 < c ∧
      0 < d ∧
      c + d = 1 ∧
      x₀ = c • xPlus + d • xMinus ∧
      (∀ j, |realDot x₀ (a j)| = 1 → |realDot xPlus (a j)| = 1) ∧
      |realDot x₀ (a jNew)| ≠ 1 ∧
      |realDot xPlus (a jNew)| = 1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro hproper h hhne hhortho δ hδpos hlocal
  have hx₀ : x₀ ∈ constraintPolytope a := by
    simpa using hlocal 0 (by simpa using le_of_lt hδpos)
  let activeDerivativeSet : Finset ι :=
    (Finset.univ : Finset ι).filter fun j => realDot h (a j) ≠ 0
  have hactiveDerivativeSet_nonempty : activeDerivativeSet.Nonempty := by
    rcases exists_constraint_not_annihilated_of_span a hspan hhne with ⟨j, hj⟩
    exact ⟨j, by simp [activeDerivativeSet, hj]⟩
  let u : ι → ℝ := fun j => realDot x₀ (a j)
  let v : ι → ℝ := fun j => realDot h (a j)
  let scalarBound : ι → ℝ := fun j => endpointTimeBound (u j) (v j)
  rcases Finset.exists_min_image activeDerivativeSet scalarBound
      hactiveDerivativeSet_nonempty with
    ⟨jNew, hjNew_mem, hjNew_min⟩
  have hjNew_v_ne : v jNew ≠ 0 := by
    simpa [activeDerivativeSet, v] using hjNew_mem
  have inactive_of_mem_activeDerivativeSet :
      ∀ {j : ι}, j ∈ activeDerivativeSet → |realDot x₀ (a j)| ≠ 1 := by
    intro j hjmem hjactive
    have hvne : realDot h (a j) ≠ 0 := by
      simpa [activeDerivativeSet] using hjmem
    exact hvne (hhortho j hjactive)
  have hjNew_inactive : |realDot x₀ (a jNew)| ≠ 1 :=
    inactive_of_mem_activeDerivativeSet hjNew_mem
  have strict_of_mem_activeDerivativeSet :
      ∀ {j : ι}, j ∈ activeDerivativeSet → |u j| < 1 := by
    intro j hjmem
    exact lt_of_le_of_ne (by simpa [u] using hx₀ j)
      (by simpa [u] using inactive_of_mem_activeDerivativeSet hjmem)
  let τ : ℝ := scalarBound jNew
  have hτpos : 0 < τ := by
    exact endpointTimeBound_pos
      (strict_of_mem_activeDerivativeSet hjNew_mem) hjNew_v_ne
  let σ : ℝ := δ / 2
  have hσpos : 0 < σ := by
    positivity
  let xPlus : n → ℝ := x₀ + τ • h
  let xMinus : n → ℝ := x₀ + (-σ) • h
  have hxPlus : xPlus ∈ constraintPolytope a := by
    intro j
    by_cases hvj : v j = 0
    · have hdot : realDot xPlus (a j) = realDot x₀ (a j) := by
        simp [xPlus, v, realDot_add, realDot_smul, hvj]
      simpa [hdot] using hx₀ j
    · have hjmem : j ∈ activeDerivativeSet := by
        simp [activeDerivativeSet, v, hvj]
      have hτle : τ ≤ scalarBound j := hjNew_min j hjmem
      have huj : |u j| ≤ 1 := by
        simpa [u] using hx₀ j
      have hscalar :
          |u j + τ * v j| ≤ 1 :=
        abs_add_mul_le_one_of_le_endpointTimeBound huj hτpos.le hτle
      have hdot :
          realDot xPlus (a j) = u j + τ * v j := by
        simp [xPlus, u, v, realDot_add, realDot_smul]
      simpa [hdot] using hscalar
  have hσ_le : |-σ| ≤ δ := by
    have hσnonneg : 0 ≤ σ := le_of_lt hσpos
    rw [abs_of_nonpos (neg_nonpos.mpr hσnonneg)]
    dsimp [σ]
    linarith
  have hxMinus : xMinus ∈ constraintPolytope a := by
    simpa [xMinus, σ] using hlocal (-σ) hσ_le
  let c : ℝ := σ / (τ + σ)
  let d : ℝ := τ / (τ + σ)
  have hsumpos : 0 < τ + σ := add_pos hτpos hσpos
  have hcpos : 0 < c := div_pos hσpos hsumpos
  have hdpos : 0 < d := div_pos hτpos hsumpos
  have hcd : c + d = 1 := by
    change σ / (τ + σ) + τ / (τ + σ) = 1
    field_simp [ne_of_gt hsumpos]
    ring
  have hcomb : x₀ = c • xPlus + d • xMinus := by
    ext i
    change x₀ i =
      σ / (τ + σ) * (x₀ i + τ * h i) +
        τ / (τ + σ) * (x₀ i + -σ * h i)
    field_simp [ne_of_gt hsumpos]
    ring
  have hold : ∀ j, |realDot x₀ (a j)| = 1 → |realDot xPlus (a j)| = 1 := by
    intro j hj
    simpa [xPlus] using
      activeConstraint_stays_active_along_annihilating_direction a x₀ h hhortho hj τ
  have hjNew_active : |realDot xPlus (a jNew)| = 1 := by
    have hdot :
        realDot xPlus (a jNew) = u jNew + τ * v jNew := by
      simp [xPlus, u, v, realDot_add, realDot_smul]
    simpa [hdot, τ, scalarBound] using
      abs_add_endpointTimeBound_mul_eq_one hjNew_v_ne
  exact ⟨xPlus, xMinus, c, d, jNew, hxPlus, hxMinus, hcpos, hdpos, hcd,
    hcomb, hold, hjNew_inactive, hjNew_active⟩

/-- The endpoint construction implies the active-count increase used downstream. -/
theorem activeEndpointWithMoreActiveConstraints
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (x₀ : n → ℝ) :
    activeConstraintSpan a x₀ ≠ ⊤ →
    (h : n → ℝ) →
    h ≠ 0 →
    (∀ j, |realDot x₀ (a j)| = 1 → realDot h (a j) = 0) →
    (δ : ℝ) →
    0 < δ →
    (∀ t : ℝ, |t| ≤ δ → x₀ + t • h ∈ constraintPolytope a) →
    ∃ (xPlus xMinus : n → ℝ) (c d : ℝ),
      xPlus ∈ constraintPolytope a ∧
      xMinus ∈ constraintPolytope a ∧
      0 < c ∧
      0 < d ∧
      c + d = 1 ∧
      x₀ = c • xPlus + d • xMinus ∧
      activeConstraintCount a x₀ < activeConstraintCount a xPlus := by
  intro hproper h hhne hhortho δ hδpos hlocal
  rcases activeEndpointWithNewActiveConstraint a hspan x₀
      hproper h hhne hhortho δ hδpos hlocal with
    ⟨xPlus, xMinus, c, d, jNew, hxPlus, hxMinus, hc, hd, hcd, hcomb,
      hold, hjOldInactive, hjNewActive⟩
  exact ⟨xPlus, xMinus, c, d, hxPlus, hxMinus, hc, hd, hcd, hcomb,
    activeConstraintCount_lt_of_old_active_and_new a x₀ xPlus
      hold hjOldInactive hjNewActive⟩

/--
Endpoint contradiction after proving the endpoint maximizer fact from convexity.
-/
theorem activeEndpointContradiction
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (hconv : ConvexOn ℝ (constraintPolytope a) Φ)
    (x₀ : n → ℝ) :
    IsConstraintPolytopeMaximizer a Φ x₀ →
    (∀ x : n → ℝ,
      IsConstraintPolytopeMaximizer a Φ x →
        activeConstraintCount a x ≤ activeConstraintCount a x₀) →
    activeConstraintSpan a x₀ ≠ ⊤ →
    (h : n → ℝ) →
    h ≠ 0 →
    (∀ j, |realDot x₀ (a j)| = 1 → realDot h (a j) = 0) →
    (δ : ℝ) →
    0 < δ →
    (∀ t : ℝ, |t| ≤ δ → x₀ + t • h ∈ constraintPolytope a) →
    False := by
  intro hx₀max hx₀card hproper h hhne hhortho δ hδpos hlocal
  rcases activeEndpointWithMoreActiveConstraints a hspan x₀
      hproper h hhne hhortho δ hδpos hlocal with
    ⟨xPlus, xMinus, c, d, hxPlus, hxMinus, hc, hd, hcd, hcomb, hcount_lt⟩
  have hxPlusMax :
      IsConstraintPolytopeMaximizer a Φ xPlus :=
    (endpoints_are_maximizers_of_convex_combination a Φ hconv hx₀max
      hxPlus hxMinus hc hd hcd hcomb).1
  exact (not_lt_of_ge (hx₀card xPlus hxPlusMax)) hcount_lt

/--
The perturbation contradiction, reduced to the endpoint part after proving
there is positive room to move inside the polytope.
-/
theorem activePerturbationContradiction
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (hconv : ConvexOn ℝ (constraintPolytope a) Φ)
    (x₀ : n → ℝ) :
    IsConstraintPolytopeMaximizer a Φ x₀ →
    (∀ x : n → ℝ,
      IsConstraintPolytopeMaximizer a Φ x →
        activeConstraintCount a x ≤ activeConstraintCount a x₀) →
    activeConstraintSpan a x₀ ≠ ⊤ →
    (h : n → ℝ) →
    h ≠ 0 →
    (∀ j, |realDot x₀ (a j)| = 1 → realDot h (a j) = 0) →
    False := by
  intro hx₀max hx₀card hproper h hhne hhortho
  rcases constraintPolytope_has_local_line_segment a x₀ h hx₀max.1 hhortho with
    ⟨δ, hδpos, hlocal⟩
  exact activeEndpointContradiction a Φ hspan hconv x₀
    hx₀max hx₀card hproper h hhne hhortho δ hδpos hlocal

/--
A maximal-active-cardinality maximizer has full active span via the endpoint
perturbation argument.
-/
theorem activeSpanTopOfMaximalActiveMaximizer
    {n ι : Type*} [Fintype n] [Fintype ι]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (hconv : ConvexOn ℝ (constraintPolytope a) Φ)
    (x₀ : n → ℝ) :
    IsConstraintPolytopeMaximizer a Φ x₀ →
    (∀ x : n → ℝ,
      IsConstraintPolytopeMaximizer a Φ x →
        activeConstraintCount a x ≤ activeConstraintCount a x₀) →
    activeConstraintSpan a x₀ = ⊤ := by
  intro hx₀max hx₀card
  by_contra hproper
  rcases exists_nonzero_annihilating_activeSpan a x₀ hproper with
    ⟨h, hhne, hhortho⟩
  exact activePerturbationContradiction a Φ hspan hconv x₀
    hx₀max hx₀card hproper h hhne hhortho

/--
The active-constraint maximizer lemma, proved using the perturbation argument.
-/
theorem activeConstraintMaximizer
    {n ι : Type*} [Fintype n] [Finite ι]
    (a : ι → n → ℝ) (Φ : (n → ℝ) → ℝ)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (hcont : Continuous Φ)
    (hconv : ConvexOn ℝ (constraintPolytope a) Φ) :
    ∃ x₀ : n → ℝ,
      x₀ ∈ constraintPolytope a ∧
      (∀ x : n → ℝ, x ∈ constraintPolytope a → Φ x ≤ Φ x₀) ∧
      activeConstraintSpan a x₀ = ⊤ := by
  let : Fintype ι := Fintype.ofFinite ι
  rcases exists_constraintPolytope_maximizer_max_active a Φ hspan hcont with
    ⟨x₀, hx₀max, hx₀card⟩
  exact ⟨x₀, hx₀max.1, hx₀max.2,
    activeSpanTopOfMaximalActiveMaximizer a Φ hspan hconv x₀ hx₀max hx₀card⟩

/-- A compact set lies in a nonempty compact convex set when its support function
is smaller. -/
theorem supportFunctionSeparation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K L : Set V)
    (hKcpt : IsCompact K) (hLcpt : IsCompact L)
    (hLconv : Convex ℝ L) (hLnonempty : L.Nonempty)
    (hsupport :
      ∀ a : V,
        sSup ((fun x : V => inner ℝ a x) '' K) ≤
          sSup ((fun y : V => inner ℝ a y) '' L)) :
    K ⊆ L := by
  intro x hxK
  by_contra hxL
  rcases exists_norm_eq_iInf_of_complete_convex hLnonempty hLcpt.isComplete hLconv x with
    ⟨y₀, hy₀L, hy₀min⟩
  let a : V := x - y₀
  have hvariational : ∀ y ∈ L, inner ℝ a (y - y₀) ≤ 0 := by
    simpa [a] using (norm_eq_iInf_iff_real_inner_le_zero hLconv hy₀L).mp hy₀min
  have hLupper :
      ∀ b ∈ ((fun y : V => inner ℝ a y) '' L), b ≤ inner ℝ a y₀ := by
    rintro b ⟨y, hyL, rfl⟩
    have hy := hvariational y hyL
    have hy' : inner ℝ a y - inner ℝ a y₀ ≤ 0 := by
      simpa [inner_sub_right] using hy
    linarith
  have hLsup_le :
      sSup ((fun y : V => inner ℝ a y) '' L) ≤ inner ℝ a y₀ := by
    exact csSup_le ⟨inner ℝ a y₀, ⟨y₀, hy₀L, rfl⟩⟩ hLupper
  have hKbdd : BddAbove ((fun x : V => inner ℝ a x) '' K) := by
    exact hKcpt.bddAbove_image (by fun_prop)
  have hx_le_Ksup : inner ℝ a x ≤ sSup ((fun x : V => inner ℝ a x) '' K) := by
    exact le_csSup hKbdd ⟨x, hxK, rfl⟩
  have hx_le_y₀ : inner ℝ a x ≤ inner ℝ a y₀ :=
    hx_le_Ksup.trans ((hsupport a).trans hLsup_le)
  have hx_ne_y₀ : x ≠ y₀ := by
    intro hxy
    apply hxL
    simpa [hxy] using hy₀L
  have hstrict : inner ℝ a y₀ < inner ℝ a x := by
    have hpos : 0 < inner ℝ a x - inner ℝ a y₀ := by
      have hdiff : inner ℝ a x - inner ℝ a y₀ = inner ℝ a a := by
        rw [← inner_sub_right]
      rw [hdiff, real_inner_self_eq_norm_sq]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_y₀))
    linarith
  linarith

/-- Over the real numbers, matrix star is just transpose. -/
theorem realMatrix_star_eq_transpose
    {n : Type*} (A : Matrix n n ℝ) :
    star A = A.transpose := by
  ext i j
  simp [Matrix.star_apply]

/--
For the matrix inner product induced by the identity positive matrix, the
Frobenius pairing is the trace pairing against the transpose.
-/
theorem matrixInner_eq_trace_transpose_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A G : Matrix n n ℝ) :
    letI := Matrix.toMatrixInnerProductSpace
      (1 : Matrix n n ℝ) Matrix.PosSemidef.one
    inner ℝ A G = (A.transpose * G).trace := by
  change (G * (1 : Matrix n n ℝ) * star A).trace = (A.transpose * G).trace
  rw [realMatrix_star_eq_transpose A]
  rw [Matrix.trace_mul_cycle]
  simp

/--
The Frobenius support value of a rank-one cube matrix is the associated
quadratic form.
-/
theorem matrixInner_realRankOne_eq_realQuadraticForm
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (q : n → ℝ) :
    letI := Matrix.toMatrixInnerProductSpace
      (1 : Matrix n n ℝ) Matrix.PosSemidef.one
    inner ℝ A (realRankOne q) = realQuadraticForm A q := by
  change (realRankOne q * (1 : Matrix n n ℝ) * star A).trace =
    realQuadraticForm A q
  rw [realMatrix_star_eq_transpose A]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.trace, mul_one, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    realRankOne,
    realQuadraticForm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The symmetric part of a real square matrix. -/
def realSymmPart {d : Type*} (A : Matrix d d ℝ) : Matrix d d ℝ :=
  fun i j => (A i j + A j i) / 2

/-- Rank-one cube matrices, as a subset of the ambient real matrix space. -/
def realRankOneCubeSet (d : Type*) : Set (Matrix d d ℝ) :=
  {R | ∃ q : d → ℝ, InRealUnitCube q ∧ R = realRankOne q}

/-- Flatten a matrix into the Euclidean coordinate space indexed by pairs. -/
def matrixToEuclidean {d : Type*} (A : Matrix d d ℝ) :
    EuclideanSpace ℝ (d × d) :=
  WithLp.toLp 2 (fun ij : d × d => A (Prod.fst ij) (Prod.snd ij))

/-- Unflatten a Euclidean vector indexed by pairs into a matrix. -/
def euclideanToMatrix {d : Type*} (v : EuclideanSpace ℝ (d × d)) :
    Matrix d d ℝ :=
  fun i j => v (i, j)

/-- Rank-one cube matrices, flattened into Euclidean space. -/
def realRankOneCubeEuclideanSet (d : Type*) :
    Set (EuclideanSpace ℝ (d × d)) :=
  Set.image (fun A : Matrix d d ℝ => matrixToEuclidean A)
    (realRankOneCubeSet d)

/-- The coordinate cube `[-1,1]^d` is compact. -/
theorem isCompact_realUnitCube
    {d : Type*} :
    IsCompact {q : d → ℝ | InRealUnitCube q} := by
  have h : IsCompact {q : d → ℝ | ∀ i, q i ∈ Set.Icc (-1 : ℝ) 1} := by
    exact isCompact_pi_infinite (fun _ => isCompact_Icc)
  convert h using 1
  ext q
  simp [InRealUnitCube, abs_le]

/-- The rank-one flattening map is continuous on the real cube ambient space. -/
theorem continuous_matrixToEuclidean_realRankOne
    {d : Type*} :
    Continuous (fun q : d → ℝ => matrixToEuclidean (realRankOne q)) := by
  unfold matrixToEuclidean realRankOne
  apply (PiLp.continuous_toLp 2 (fun _ : d × d => ℝ)).comp
  apply continuous_pi
  intro ij
  exact (continuous_apply (Prod.fst ij)).mul
    (continuous_apply (Prod.snd ij))

/-- The flattened rank-one cube image is compact. -/
theorem isCompact_realRankOneCubeEuclideanSet
    {d : Type*} :
    IsCompact (realRankOneCubeEuclideanSet d) := by
  have himage :
      Set.image (fun q : d → ℝ => matrixToEuclidean (realRankOne q))
          {q : d → ℝ | InRealUnitCube q} =
        realRankOneCubeEuclideanSet d := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨realRankOne q, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨R, ⟨q, hq, hR⟩, hv⟩
      refine ⟨q, hq, ?_⟩
      rw [← hv, hR]
  rw [← himage]
  exact isCompact_realUnitCube.image continuous_matrixToEuclidean_realRankOne

/--
The set of barycentres of `k` points of `s`, with weights in the standard
simplex.
-/
def barycentricImageSet {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Set E) (k : ℕ) : Set E :=
  {x | ∃ (w : Fin k → ℝ) (z : Fin k → E),
    w ∈ Set.range (fun t : Convexity.StdSimplex ℝ (Fin k) =>
      (t.weights : Fin k → ℝ)) ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x}

/--
A finite-dimensional Caratheodory-sized union of barycentric images.
-/
def finiteBarycentricHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Set E) : Set E :=
  ⋃ k : Fin (Module.finrank ℝ E + 2), barycentricImageSet s k.1

/-- Barycentric images of compact sets are compact. -/
theorem isCompact_barycentricImageSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : IsCompact s) (k : ℕ) :
    IsCompact (barycentricImageSet s k) := by
  let D : Set ((Fin k → ℝ) × (Fin k → E)) :=
    {x | x.1 ∈ Set.range (fun t : Convexity.StdSimplex ℝ (Fin k) =>
      (t.weights : Fin k → ℝ)) ∧ ∀ i, x.2 i ∈ s}
  have hD : IsCompact D := by
    have hw : IsCompact (Set.range (fun t : Convexity.StdSimplex ℝ (Fin k) =>
        (t.weights : Fin k → ℝ))) :=
      isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin k)).continuous
    have hz : IsCompact {z : Fin k → E | ∀ i, z i ∈ s} :=
      isCompact_pi_infinite (fun _ => hs)
    have hprod := hw.prod hz
    convert hprod using 1
    ext x
    rfl
  let F : ((Fin k → ℝ) × (Fin k → E)) → E := fun x => ∑ i, x.1 i • x.2 i
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have himage : F '' D = barycentricImageSet s k := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, y.2, hy.1, hy.2, rfl⟩
    · rintro ⟨w, z, hw, hz, hx⟩
      exact ⟨(w, z), ⟨hw, hz⟩, hx⟩
  rw [← himage]
  exact hD.image hF

/--
Membership in the convex hull of a finite subset gives an explicit barycentric
image point.
-/
theorem mem_barycentricImageSet_of_finset_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {t : Finset E} {x : E}
    (hts : (t : Set E) ⊆ s) (hx : x ∈ convexHull ℝ (t : Set E)) :
    x ∈ barycentricImageSet s (Fintype.card t) := by
  classical
  rw [Finset.convexHull_eq] at hx
  rcases hx with ⟨w, hw_nonneg, hsum, hcenter⟩
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨fun r => w ((e.symm r : t) : E), fun r => ((e.symm r : t) : E), ?_, ?_, ?_⟩
  · simp only [Convexity.StdSimplex.range_toFun_comp_weights, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_ofPred_eq]
    have hsum_subtype : ∑ y : t, w (y : E) = 1 := by
      rw [← Finset.sum_attach t w] at hsum
      simpa using hsum
    constructor
    · intro r
      exact hw_nonneg ((e.symm r : t) : E) (e.symm r).property
    · rw [← hsum_subtype]
      symm
      simpa using Equiv.sum_comp e
        (fun r : Fin (Fintype.card t) => w ((e.symm r : t) : E))
  · intro r
    exact hts (e.symm r).property
  · have hcenter_sum : ∑ y : t, w (y : E) • (y : E) = x := by
      rw [Finset.centerMass_eq_of_sum_1 t id hsum] at hcenter
      rw [← Finset.sum_attach t (fun y => w y • id y)] at hcenter
      simpa using hcenter
    rw [← hcenter_sum]
    symm
    simpa using Equiv.sum_comp e
      (fun r : Fin (Fintype.card t) => w ((e.symm r : t) : E) • ((e.symm r : t) : E))

/-- In finite dimension, the convex hull is the Caratheodory-sized barycentric union. -/
theorem convexHull_eq_finiteBarycentricHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Set E) :
    convexHull ℝ s = finiteBarycentricHull s := by
  classical
  ext x
  constructor
  · intro hx
    rw [convexHull_eq_union] at hx
    simp only [exists_prop, Set.mem_iUnion] at hx
    rcases hx with ⟨t, hts, hAI, hxt⟩
    have hcard : Fintype.card t ≤ Module.finrank ℝ E + 1 :=
      (hAI.card_le_finrank_succ).trans
        (Nat.succ_le_succ (Submodule.finrank_le _))
    refine Set.mem_iUnion.mpr ⟨⟨Fintype.card t, Nat.lt_succ_iff.mpr hcard⟩, ?_⟩
    exact mem_barycentricImageSet_of_finset_convexHull hts hxt
  · intro hx
    rw [finiteBarycentricHull] at hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    rcases hk with ⟨w, z, hw, hz, hsum⟩
    have hw' : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
      simpa only [Convexity.StdSimplex.range_toFun_comp_weights, Set.mem_inter_iff,
        Set.mem_iInter, Set.mem_ofPred_eq] using hw
    exact mem_convexHull_of_exists_fintype w z hw'.1 hw'.2 hz hsum

/-- The convex hull of a compact set in finite-dimensional real space is compact. -/
theorem isCompact_convexHull_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rw [convexHull_eq_finiteBarycentricHull]
  rw [finiteBarycentricHull]
  exact isCompact_iUnion fun k => isCompact_barycentricImageSet hs k.1

/-- The convex hull of a compact set in finite-dimensional real space is closed. -/
theorem isClosed_convexHull_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    IsClosed (convexHull ℝ s) :=
  (isCompact_convexHull_of_isCompact hs).isClosed

/-- For compact sets in finite dimension, closed convex hull equals convex hull. -/
theorem closedConvexHull_eq_convexHull_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    closedConvexHull ℝ s = convexHull ℝ s := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact closure_eq_iff_isClosed.mpr (isClosed_convexHull_of_isCompact hs)

/-- Flattening and then unflattening a matrix gives the original matrix. -/
theorem euclideanToMatrix_matrixToEuclidean
    {d : Type*} (A : Matrix d d ℝ) :
    euclideanToMatrix (matrixToEuclidean A) = A := by
  ext i j
  simp [euclideanToMatrix, matrixToEuclidean]

/-- Unflattening and then flattening a Euclidean matrix-vector gives the original vector. -/
theorem matrixToEuclidean_euclideanToMatrix
    {d : Type*} (v : EuclideanSpace ℝ (d × d)) :
    matrixToEuclidean (euclideanToMatrix v) = v := by
  ext ij
  simp [euclideanToMatrix, matrixToEuclidean]

/-- The symmetric part is symmetric. -/
theorem realSymmetric_realSymmPart
    {d : Type*} (A : Matrix d d ℝ) :
    RealSymmetric (realSymmPart A) := by
  intro i j
  simp [realSymmPart, add_comm]

/-- Rank-one real matrices are symmetric. -/
theorem realSymmetric_realRankOne
    {d : Type*} (q : d → ℝ) :
    RealSymmetric (realRankOne q) := by
  intro i j
  simp [realRankOne, mul_comm]

/-- Against a symmetric right factor, `A` and `Aᵀ` have the same trace pairing. -/
theorem trace_mul_eq_trace_transpose_mul_of_realSymmetric_right
    {d : Type*} [Fintype d]
    (A T : Matrix d d ℝ) (hT : RealSymmetric T) :
    (A * T).trace = (A.transpose * T).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hT j i]

/-- The trace pairing with the symmetric part is the average of the two trace pairings. -/
theorem trace_realSymmPart_mul_eq_average
    {d : Type*} [Fintype d]
    (A T : Matrix d d ℝ) :
    (realSymmPart A * T).trace =
      ((A * T).trace + (A.transpose * T).trace) / 2 := by
  simp [Matrix.trace, Matrix.mul_apply, realSymmPart, add_mul, div_eq_mul_inv,
    Finset.sum_add_distrib, Finset.sum_mul]
  ring_nf

/-- A symmetric right factor only sees the symmetric part of the left factor. -/
theorem trace_transpose_mul_eq_trace_realSymmPart_mul_of_realSymmetric
    {d : Type*} [Fintype d]
    (A T : Matrix d d ℝ) (hT : RealSymmetric T) :
    (A.transpose * T).trace = (realSymmPart A * T).trace := by
  rw [trace_realSymmPart_mul_eq_average]
  rw [trace_mul_eq_trace_transpose_mul_of_realSymmetric_right A T hT]
  ring

/-- The quadratic form of a transpose agrees with the original quadratic form. -/
theorem realQuadraticForm_transpose
    {d : Type*} [Fintype d]
    (A : Matrix d d ℝ) (q : d → ℝ) :
    realQuadraticForm A.transpose q = realQuadraticForm A q := by
  simp only [realQuadraticForm, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The quadratic form of the symmetric part is the average of the two transpose forms. -/
theorem realQuadraticForm_realSymmPart_eq_average
    {d : Type*} [Fintype d]
    (A : Matrix d d ℝ) (q : d → ℝ) :
    realQuadraticForm (realSymmPart A) q =
      (realQuadraticForm A q + realQuadraticForm A.transpose q) / 2 := by
  simp [realQuadraticForm, realSymmPart, add_mul, mul_add, div_eq_mul_inv,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  ring_nf

/-- Quadratic forms only see the symmetric part of a real matrix. -/
theorem realQuadraticForm_realSymmPart
    {d : Type*} [Fintype d]
    (A : Matrix d d ℝ) (q : d → ℝ) :
    realQuadraticForm (realSymmPart A) q = realQuadraticForm A q := by
  rw [realQuadraticForm_realSymmPart_eq_average]
  rw [realQuadraticForm_transpose]
  ring

/-- The Euclidean inner product of flattened matrices is the trace pairing. -/
theorem inner_matrixToEuclidean_eq_trace_transpose_mul
    {d : Type*} [Fintype d]
    (A T : Matrix d d ℝ) :
    inner ℝ (matrixToEuclidean A) (matrixToEuclidean T) =
      (A.transpose * T).trace := by
  classical
  simp only [matrixToEuclidean, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The flattened support value of a rank-one matrix is the quadratic form. -/
theorem inner_matrixToEuclidean_realRankOne_eq_realQuadraticForm
    {d : Type*} [Fintype d]
    (A : Matrix d d ℝ) (q : d → ℝ) :
    inner ℝ (matrixToEuclidean A) (matrixToEuclidean (realRankOne q)) =
      realQuadraticForm A q := by
  classical
  rw [inner_matrixToEuclidean_eq_trace_transpose_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    realRankOne,
    realQuadraticForm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- A real symmetric matrix is Hermitian in Mathlib's matrix sense. -/
theorem realSymmetric_isHermitian
    {n : Type*} (A : Matrix n n ℝ) :
    RealSymmetric A → A.IsHermitian := by
  intro hA
  rw [Matrix.IsHermitian]
  ext i j
  exact hA j i

/-- A real Hermitian matrix is symmetric in entrywise real coordinates. -/
theorem realSymmetric_of_isHermitian
    {n : Type*} (A : Matrix n n ℝ) :
    A.IsHermitian → RealSymmetric A := by
  intro hA i j
  rw [Matrix.IsHermitian] at hA
  have hij := congrFun (congrFun hA i) j
  simpa using hij.symm

/-- The explicit Hermitian matrix functional calculus preserves real symmetry. -/
theorem realSymmetric_cfc
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hSym : RealSymmetric A) (f : ℝ → ℝ) :
    RealSymmetric ((realSymmetric_isHermitian A hSym).cfc f) := by
  apply realSymmetric_of_isHermitian
  rw [← Matrix.IsHermitian.cfc_eq]
  exact cfc_predicate f A

/-- The real quadratic-form PSD predicate implies Mathlib's matrix PSD predicate. -/
theorem realPSD_posSemidef
    {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) :
    RealSymmetric A → RealPSD A → A.PosSemidef := by
  intro hSym hPSD
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realSymmetric_isHermitian A hSym) ?_
  intro x
  have hx := hPSD x
  simpa [realQuadraticForm, dotProduct, Matrix.vecMul, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm] using hx

/-- Mathlib's matrix PSD predicate implies nonnegativity of the real quadratic form. -/
theorem realPSD_of_posSemidef
    {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) :
    A.PosSemidef → RealPSD A := by
  intro hA x
  have hx := hA.dotProduct_mulVec_nonneg x
  simpa [realQuadraticForm, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm] using hx

/--
If a real function is nonnegative on the spectrum, its Hermitian matrix
functional calculus is positive semidefinite in the project's quadratic-form
sense.
-/
theorem realPSD_cfc_of_nonneg_spectrum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hSym : RealSymmetric A) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ A, 0 ≤ f x) :
    RealPSD ((realSymmetric_isHermitian A hSym).cfc f) := by
  rw [← Matrix.IsHermitian.cfc_eq]
  exact realPSD_of_posSemidef (cfc f A)
    (Matrix.nonneg_iff_posSemidef.mp
      (cfc_nonneg (A := Matrix n n ℝ) hf))

/-- Trace of the explicit Hermitian matrix functional calculus. -/
theorem trace_cfc_eq_sum_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal]

/-- Mathlib's CFC positive part agrees with the explicit Hermitian matrix `cfc`. -/
theorem posPart_eq_cfc_posPart
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A⁺ = hA.cfc (fun x : ℝ => x⁺) := by
  rw [CFC.posPart_def]
  rw [cfcₙ_eq_cfc]
  rw [Matrix.IsHermitian.cfc_eq]

/-- Trace of the CFC positive part as the sum of positive eigenvalue parts. -/
theorem trace_posPart_eq_sum_posPart_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (A⁺).trace = ∑ i, (hA.eigenvalues i)⁺ := by
  rw [posPart_eq_cfc_posPart A hA]
  exact trace_cfc_eq_sum_eigenvalues A hA (fun x : ℝ => x⁺)

/--
Trace of the CFC positive part, indexed by Mathlib's canonical sorted
eigenvalue list.
-/
theorem trace_posPart_eq_sum_eigenvalues₀
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hSym : RealSymmetric A) :
    (A⁺).trace =
      ∑ i : Fin (Fintype.card n),
        ((realSymmetric_isHermitian A hSym).eigenvalues₀ i)⁺ := by
  have hHerm : A.IsHermitian := realSymmetric_isHermitian A hSym
  calc
    (A⁺).trace = ∑ i : n, (hHerm.eigenvalues i)⁺ :=
      trace_posPart_eq_sum_posPart_eigenvalues A hHerm
    _ = ∑ i : Fin (Fintype.card n), (hHerm.eigenvalues₀ i)⁺ := by
      unfold Matrix.IsHermitian.eigenvalues
      exact Equiv.sum_comp
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm)
        (fun i : Fin (Fintype.card n) => (hHerm.eigenvalues₀ i)⁺)

/-- The identity matrix is real symmetric. -/
theorem realSymmetric_one
    {n : Type*} [DecidableEq n] :
    RealSymmetric (1 : Matrix n n ℝ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

/-- Symmetry is preserved by subtracting from the identity. -/
theorem realSymmetric_one_sub
    {n : Type*} [DecidableEq n] (G : Matrix n n ℝ) :
    RealSymmetric G → RealSymmetric (1 - G) := by
  intro hG i j
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji, hG i j]

/-- The zero matrix is real positive semidefinite. -/
theorem realPSD_zero
    {n : Type*} [Fintype n] :
    RealPSD (0 : Matrix n n ℝ) := by
  intro x
  simp [realQuadraticForm]

/-- The identity matrix is real positive semidefinite. -/
theorem realPSD_one
    {n : Type*} [Fintype n] [DecidableEq n] :
    RealPSD (1 : Matrix n n ℝ) := by
  intro x
  calc
    0 ≤ ∑ i, x i * x i := by
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    _ = realQuadraticForm (1 : Matrix n n ℝ) x := by
      unfold realQuadraticForm
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show (∑ j, (1 : Matrix n n ℝ) i j * x j) = x i by
        simp [Matrix.one_apply]]

/-- The identity matrix satisfies `0 ≤ I ≤ I`. -/
theorem realLoewnerBetweenZeroAndOne_one
    {n : Type*} [Fintype n] [DecidableEq n] :
    RealLoewnerBetweenZeroAndOne (1 : Matrix n n ℝ) := by
  exact ⟨realPSD_one, by
    simpa [RealLoewnerLE] using (realPSD_zero : RealPSD (0 : Matrix n n ℝ))⟩

/-- The trace of a product of two real PSD matrices is nonnegative. -/
theorem positiveSemidefinite_trace_mul_nonneg
    {n : Type*} [Fintype n]
    (B C : Matrix n n ℝ) :
    RealSymmetric B → RealSymmetric C → RealPSD B → RealPSD C →
      0 ≤ (B * C).trace := by
  classical
  intro hBsym hCsym hBpsd hCpsd
  have hBpos : B.PosSemidef := realPSD_posSemidef B hBsym hBpsd
  have hCpos : C.PosSemidef := realPSD_posSemidef C hCsym hCpsd
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hCpos.nonneg
  rw [hS]
  calc
    0 ≤ (S * B * star S).trace := (hBpos.mul_mul_conjTranspose_same S).trace_nonneg
    _ = (B * (star S * S)).trace := by
      rw [← Matrix.trace_mul_cycle B (star S) S]
      rw [Matrix.mul_assoc]

/-- Trace pairing with a finite convex combination of rank-one matrices. -/
theorem trace_mul_realConvexCombination
    {n : Type*} [Fintype n]
    {m : ℕ} (A G : Matrix n n ℝ) (p : Fin m → ℝ) (q : Fin m → n → ℝ)
    (hentry : ∀ a b, G a b = ∑ r, p r * q r a * q r b) :
    (A * G).trace = ∑ r, p r * realQuadraticForm A (q r) := by
  calc
    (A * G).trace = ∑ i, ∑ j, A i j * G j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    _ = ∑ i, ∑ j, A i j * (∑ r, p r * q r j * q r i) := by
      simp [hentry]
    _ = ∑ i, ∑ j, ∑ r, A i j * (p r * q r j * q r i) := by
      simp [Finset.mul_sum]
    _ = ∑ r, ∑ i, ∑ j, A i j * (p r * q r j * q r i) := by
      rw [show (∑ i, ∑ j, ∑ r, A i j * (p r * q r j * q r i)) =
          ∑ i, ∑ r, ∑ j, A i j * (p r * q r j * q r i) by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.sum_comm]]
      rw [Finset.sum_comm]
    _ = ∑ r, p r * realQuadraticForm A (q r) := by
      simp [realQuadraticForm, Finset.mul_sum, mul_comm, mul_left_comm]

/--
The support-function property expected from the positive spectral part of `A`.

For the paper proof, `Apos` is instantiated as the positive spectral part of
`A`; this predicate packages the required support-function property.
-/
def HasPositivePartSupportFunction
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Apos : Matrix n n ℝ) : Prop :=
  (∀ G : Matrix n n ℝ,
    RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
      (A * G).trace ≤ Apos.trace) ∧
  ∃ G : Matrix n n ℝ,
    RealSymmetric G ∧ RealLoewnerBetweenZeroAndOne G ∧
      (A * G).trace = Apos.trace

/--
For a positive semidefinite test matrix, the support function over `0 ≤ G ≤ I`
is attained at `G = I`.
-/
theorem hasPositivePartSupportFunction_of_realPSD
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    RealSymmetric A → RealPSD A → HasPositivePartSupportFunction A A := by
  intro hAsym hApsd
  constructor
  · intro G hGsym hGbetween
    have hnonneg := positiveSemidefinite_trace_mul_nonneg A (1 - G)
      hAsym (realSymmetric_one_sub G hGsym) hApsd hGbetween.2
    have htrace : 0 ≤ A.trace - (A * G).trace := by
      simpa [Matrix.mul_sub] using hnonneg
    linarith
  · exact ⟨1, realSymmetric_one, realLoewnerBetweenZeroAndOne_one, by simp⟩

/--
Upper-bound half of the positive/negative spectral-part support-function
argument.  This is enough for the convex-hull separation proof once
Ball--Prodromou supplies a cube vector with quadratic value at least
`Apos.trace`.
-/
theorem supportUpperBound_of_posNegDecomposition
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Apos Aneg : Matrix n n ℝ)
    (hAeq : A = Apos - Aneg)
    (hAposSym : RealSymmetric Apos) (hAnegSym : RealSymmetric Aneg)
    (hAposPSD : RealPSD Apos) (hAnegPSD : RealPSD Aneg) :
    ∀ G : Matrix n n ℝ,
      RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
        (A * G).trace ≤ Apos.trace := by
  intro G hGsym hGbetween
  have hposUpper : (Apos * G).trace ≤ Apos.trace :=
    (hasPositivePartSupportFunction_of_realPSD Apos hAposSym hAposPSD).1
      G hGsym hGbetween
  have hnegNonneg : 0 ≤ (Aneg * G).trace :=
    positiveSemidefinite_trace_mul_nonneg Aneg G
      hAnegSym hGsym hAnegPSD hGbetween.1
  have hsplit : (A * G).trace = (Apos * G).trace - (Aneg * G).trace := by
    rw [hAeq]
    simp [Matrix.sub_mul]
  rw [hsplit]
  linarith

/--
For a real symmetric matrix, Mathlib's CFC positive part gives the support
upper bound over the Loewner interval `0 ≤ G ≤ I`.
-/
theorem supportUpperBound_cfc_posPart
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hSym : RealSymmetric A) :
    ∀ G : Matrix n n ℝ,
      RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
        (A * G).trace ≤ (A⁺).trace :=
  supportUpperBound_of_posNegDecomposition A A⁺ A⁻
    (by simpa using (CFC.posPart_sub_negPart A
      (realSymmetric_isHermitian A hSym)).symm)
    (by
      apply realSymmetric_of_isHermitian
      exact (CFC.posPart_nonneg A).isSelfAdjoint)
    (by
      apply realSymmetric_of_isHermitian
      exact (CFC.negPart_nonneg A).isSelfAdjoint)
    (realPSD_of_posSemidef A⁺
      (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)))
    (realPSD_of_posSemidef A⁻
      (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)))

/--
Abstract positive/negative spectral-part criterion for the support-function
property.  The remaining spectral task is to provide `Apos`, `Aneg`, and
`Ppos` satisfying these hypotheses for a real symmetric matrix `A`.
-/
theorem hasPositivePartSupportFunction_of_posNegProjection
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Apos Aneg Ppos : Matrix n n ℝ)
    (hAeq : A = Apos - Aneg)
    (hAposSym : RealSymmetric Apos) (hAnegSym : RealSymmetric Aneg)
    (hAposPSD : RealPSD Apos) (hAnegPSD : RealPSD Aneg)
    (hPposSym : RealSymmetric Ppos)
    (hPposBetween : RealLoewnerBetweenZeroAndOne Ppos)
    (hApos_mul_Ppos : Apos * Ppos = Apos)
    (hAneg_mul_Ppos : Aneg * Ppos = 0) :
    HasPositivePartSupportFunction A Apos := by
  constructor
  · intro G hGsym hGbetween
    have hposUpper : (Apos * G).trace ≤ Apos.trace :=
      (hasPositivePartSupportFunction_of_realPSD Apos hAposSym hAposPSD).1
        G hGsym hGbetween
    have hnegNonneg : 0 ≤ (Aneg * G).trace :=
      positiveSemidefinite_trace_mul_nonneg Aneg G
        hAnegSym hGsym hAnegPSD hGbetween.1
    have hsplit :
        (A * G).trace = (Apos * G).trace - (Aneg * G).trace := by
      rw [hAeq]
      simp [Matrix.sub_mul]
    rw [hsplit]
    linarith
  · refine ⟨Ppos, hPposSym, hPposBetween, ?_⟩
    rw [hAeq]
    simp [Matrix.sub_mul, hApos_mul_Ppos, hAneg_mul_Ppos]

/--
The real convex-decomposition theorem as an explicit property.

This packages the substantial mathematical statement that every real
symmetric matrix with `0 ≤ T ≤ I` should be a finite convex combination of
rank-one matrices `q qᵀ` with `q ∈ [-1,1]^d`. It is established below by
`hasRealConvexDecomposition`.
-/
def HasRealConvexDecomposition
    (d : Type*) [Fintype d] [DecidableEq d] : Prop :=
  ∀ T : Matrix d d ℝ,
    RealSymmetric T → RealLoewnerBetweenZeroAndOne T →
      ∃ (m : ℕ) (_hm : 0 < m) (p : Fin m → ℝ) (q : Fin m → d → ℝ),
        (∀ r, 0 ≤ p r) ∧
        (∑ r, p r = 1) ∧
        (∀ r, InRealUnitCube (q r)) ∧
        ∀ a b, T a b = ∑ r, p r * q r a * q r b

/--
The cube quadratic maximum follows from the support-function maximizer and the
real convex decomposition.
-/
theorem cubeQuadraticMaximum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Apos : Matrix n n ℝ) :
    HasRealConvexDecomposition n →
    HasPositivePartSupportFunction A Apos →
      ∃ x : n → ℝ,
        InRealUnitCube x ∧ Apos.trace ≤ realQuadraticForm A x := by
  classical
  intro hdecomp hsupport
  rcases hsupport with ⟨_, hmax⟩
  rcases hmax with ⟨G, hGsym, hGbetween, htrace⟩
  rcases hdecomp G hGsym hGbetween with
    ⟨m, hm, p, q, hp, hpsum, hcube, hentry⟩
  have htrace_sum : Apos.trace = ∑ r, p r * realQuadraticForm A (q r) := by
    rw [← htrace]
    exact trace_mul_realConvexCombination A G p q hentry
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
  rcases Finset.exists_max_image (Finset.univ : Finset (Fin m))
      (fun r => realQuadraticForm A (q r)) hnonempty with
    ⟨r₀, _hr₀mem, hr₀max⟩
  refine ⟨q r₀, hcube r₀, ?_⟩
  rw [htrace_sum]
  calc
    ∑ r, p r * realQuadraticForm A (q r)
        ≤ ∑ r, p r * realQuadraticForm A (q r₀) := by
          exact Finset.sum_le_sum fun r _hr =>
            mul_le_mul_of_nonneg_left (hr₀max r (Finset.mem_univ r)) (hp r)
    _ = (∑ r, p r) * realQuadraticForm A (q r₀) := by
          rw [Finset.sum_mul]
    _ = realQuadraticForm A (q r₀) := by
          rw [hpsum, one_mul]

end OlevskiiGram
