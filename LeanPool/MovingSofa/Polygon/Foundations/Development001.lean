/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development001

public import LeanPool.MovingSofa.Classical.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Algebra.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development001





public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
/-!
# Moving sofa: related mathematical developments

* `Polygon.AngleSet`.
* `Polygon.BooleanFunctions`.
* `Polygon.Height.Space`.
* `Polygon.Height.Bounds`.
* `Polygon.Height.RaisedSupport`.
* `Polygon.Nef.Basic`.
* `Polygon.Nef.CapConstruction`.
* `Polygon.Nef.Cells`.
* `Polygon.Nef.Height`.
* `Polygon.PerturbationBounds`.
* `Polygon.Polyline.Basic`.
* `Polygon.Polyline.Displacement`.
* `Polygon.Polyline.Graph`.
* `Polygon.Polyline.Measure`.
* `Polygon.Polyline.Projection`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Angle Set
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The interior points of the uniform angular grid. -/
def uniformAngleSet (ω : ℝ) (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2)
    (n : ℕ) (hn : 2 ≤ n) : AngleSet where
  angle := ω
  angle_pos := hω
  angle_le := hω'
  directions := (Finset.Ioo 0 n).image (fun i : ℕ ↦ (i : ℝ) / n * ω)
  nonempty := by
    apply Finset.Nonempty.image
    exact ⟨1, by simp; omega⟩
  interior := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hi, hin⟩ := Finset.mem_Ioo.mp hi
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have hin' : (i : ℝ) < n := by exact_mod_cast hin
    refine ⟨mul_pos (div_pos hi' hn') hω, ?_⟩
    exact (mul_lt_mul_of_pos_right ((div_lt_one hn').2 hin') hω).trans_eq (one_mul ω)

/-- A divisible grid refines the original grid. -/
theorem uniformAngleSet_directions_mono_of_dvd (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hmn : m ∣ n) :
    (uniformAngleSet ω hω hω' m hm).directions ⊆
      (uniformAngleSet ω hω hω' n hn).directions := by
  obtain ⟨k, rfl⟩ := hmn
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hj0, hjm⟩ := Finset.mem_Ioo.mp hj
  have hk : 0 < k := by nlinarith
  apply Finset.mem_image.mpr
  refine ⟨j * k, Finset.mem_Ioo.mpr ⟨Nat.mul_pos hj0 hk,
    Nat.mul_lt_mul_of_pos_right hjm hk⟩, ?_⟩
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  rw [mul_div_mul_right _ _ hk']

/-- Monotone dyadic grids have nested directions. -/
theorem uniformAngleSet_directions_mono_of_dyadic (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : Monotone n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    {i j : ℕ} (hij : i ≤ j) :
    (uniformAngleSet ω hω hω' (n i) (hn i)).directions ⊆
      (uniformAngleSet ω hω hω' (n j) (hn j)).directions := by
  apply uniformAngleSet_directions_mono_of_dvd
  obtain ⟨a, ha⟩ := hdyadic i
  obtain ⟨b, hb⟩ := hdyadic j
  have hab : a ≤ b := by
    apply (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp
    simpa only [← ha, ← hb] using hmono hij
  rw [ha, hb]
  exact pow_dvd_pow 2 hab

/-- An interval longer than the mesh contains a grid direction. -/
theorem exists_uniformAngleSet_mem_Ioo (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ) (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ ω) (hmesh : ω / n < b - a) :
    ∃ t ∈ (uniformAngleSet ω hω hω' n hn).directions, t ∈ Set.Ioo a b := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let j := ⌊a * n / ω⌋₊ + 1
  have hjpos : 0 < j := by dsimp [j]; omega
  have hfloor := Nat.floor_le (show 0 ≤ a * n / ω by positivity)
  have hfloor' := Nat.lt_floor_add_one (a * n / ω)
  have hjlo : a < (j : ℝ) / n * ω := by
    have h : a * n < (j : ℝ) * ω := by
      apply (div_lt_iff₀ hω).mp
      simpa only [j, Nat.cast_add, Nat.cast_one] using hfloor'
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hnpos).mpr h
  have hjhi : (j : ℝ) / n * ω ≤ a + ω / n := by
    have h : ((j : ℝ) - 1) * ω ≤ a * n := by
      apply (le_div_iff₀ hω).mp
      simpa only [j, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hfloor
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hnpos.ne']
    nlinarith
  have hjb : (j : ℝ) / n * ω < b := hjhi.trans_lt (by linarith)
  have hjn : j < n := by
    have h : (j : ℝ) / n < 1 := (mul_lt_mul_iff_left₀ hω).mp (by simpa using hjb.trans_le hb)
    exact_mod_cast (div_lt_one hnpos).mp h
  refine ⟨(j : ℝ) / n * ω, Finset.mem_image.mpr ⟨j, Finset.mem_Ioo.mpr ⟨hjpos, hjn⟩, rfl⟩,
    hjlo, hjb⟩

/-- An increasing sequence of grids eventually meets each interior open interval. -/
theorem eventually_exists_uniformAngleSet_mem_Ioo (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ ω) :
    ∀ᶠ i in atTop, ∃ t ∈ (uniformAngleSet ω hω hω' (n i) (hn i)).directions,
      t ∈ Set.Ioo a b := by
  have hlim : Tendsto (fun i ↦ ω / (n i : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ω).comp hmono.tendsto_atTop
  filter_upwards [hlim.eventually_lt_const (sub_pos.mpr hab)] with i hi
  exact exists_uniformAngleSet_mem_Ioo ω hω hω' (n i) (hn i) ha hb hi

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Boolean Functions
-/

@[expose] public section

namespace MovingSofa

/-- Boolean functions of finitely many Boolean variables. -/
abbrev BooleanFunction (n : ℕ) := (Fin n → Bool) → Bool

/-- Changing inputs from false to true cannot change a true output to false. -/
def IsMonotoneBooleanFunction {n : ℕ} (E : BooleanFunction n) : Prop :=
  ∀ P Q, (∀ i, P i = true → Q i = true) → E P = true → E Q = true

/-- Formulas built from variables using only conjunction and disjunction. -/
inductive PositiveBooleanFormula (n : ℕ) where
  | variable (i : Fin n)
  | conjunction (left right : PositiveBooleanFormula n)
  | disjunction (left right : PositiveBooleanFormula n)

/-- Evaluate a positive formula under a Boolean assignment. -/
def PositiveBooleanFormula.eval {n : ℕ} : PositiveBooleanFormula n → BooleanFunction n
  | .variable i => fun P ↦ P i
  | .conjunction left right => fun P ↦ left.eval P && right.eval P
  | .disjunction left right => fun P ↦ left.eval P || right.eval P

theorem positiveBooleanFormula_monotone {n : ℕ} (E : PositiveBooleanFormula n) :
    IsMonotoneBooleanFunction E.eval := by
  induction E <;>
    simp_all [IsMonotoneBooleanFunction, PositiveBooleanFormula.eval,
      Bool.and_eq_true, Bool.or_eq_true] <;>
    aesop

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Height / Space
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Point sets obtained by translating a polygonal cap with the fixed angle data. -/
def PolygonCapTranslateSpace (Θ : AngleSet) :=
  {S : Set Point // ∃ (K : PolygonCapSpace Θ) (q : Point),
    S = (fun p ↦ p + q) '' (K.val.val : Set Point)}

/-- Real wall heights indexed by the finite angle domain. -/
def PolygonHeightSpace (Θ : AngleSet) := angleDomain Θ → ℝ

/-- Extend a wall-height function by zero outside its angle domain. -/
def polygonHeightValue {Θ : AngleSet} (h : PolygonHeightSpace Θ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ angleDomain Θ then h ⟨t, ht⟩ else 0

/-- Intersect the two endpoint strips of unit width determined by the height data. -/
def polygonHeightParallelogram {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false ∩
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) true false

/-- Cut the endpoint parallelogram by all upper wall half-planes. -/
def polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  polygonHeightParallelogram h ∩
    ⋂ t ∈ (Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions),
      normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false

/-- Intersect the lower half-planes at the two endpoint directions. -/
def polygonHeightFan {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) true false

/-- Intersect the endpoint fan with the union of forbidden inner corners. -/
def polygonHeightNiche {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  polygonHeightFan h ∩ ⋃ t ∈ Θ.directions,
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (polygonHeightValue h (t + Real.pi / 2) - 1) false true

/-- The real area of the cap minus the real area of its niche. -/
def polygonHeightArea {Θ : AngleSet} (h : PolygonHeightSpace Θ) : ℝ :=
  ClassicalResults.area (polygonHeightCap h) - ClassicalResults.area (polygonHeightNiche h)

/-- Bundle the parallelogram, cap, fan, niche and area constructed from wall heights. -/
def polygonHeightExtensions {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Set Point × Set Point × Set Point × Set Point × ℝ :=
  (polygonHeightParallelogram h, polygonHeightCap h, polygonHeightFan h,
    polygonHeightNiche h, polygonHeightArea h)

/-- Take support values of a translated cap in the prescribed directions. -/
def polygonTranslateHeight {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    PolygonHeightSpace Θ := fun t ↦ supportValue K.val (t.val : Real.Angle)

/-- The niche and area functional associated with a translated cap. -/
def polygonTranslateExtensions {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    Set Point × ℝ :=
  (polygonHeightNiche (polygonTranslateHeight K), polygonHeightArea (polygonTranslateHeight K))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Height / Bounds
-/

@[expose] public section

namespace MovingSofa

/-- A height cap satisfies each selected upper half-plane constraint. -/
theorem polygonHeightCap_subset_normalHalfPlane {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    polygonHeightCap h ⊆ normalHalfPlane (t : Real.Angle)
      (polygonHeightValue h t) false false := by
  intro p hp
  rcases ht with ht | ht
  · exact Set.mem_iInter₂.mp hp.2 t ht
  · exact (Set.mem_iInter₂.mp hp.1 t ht).1

/-- The support of a reconstructed height cap is bounded by each defining height. -/
theorem supportValue_le_polygonHeightValue {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (K : ConvexBody Point) (hK : polygonHeightCap h = (K : Set Point))
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    supportValue K (t : Real.Angle) ≤ polygonHeightValue h t := by
  apply supportValue_le_of_subset_normalHalfPlane
  rw [← hK]
  exact polygonHeightCap_subset_normalHalfPlane h ht

/-- Unit width forces equality with the height of a distinguished strip. -/
theorem supportValue_eq_polygonHeightValue_of_width_one {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (K : ConvexBody Point)
    (hK : polygonHeightCap h = (K : Set Point)) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hw : supportValue K (t : Real.Angle) +
      supportValue K ((t + Real.pi : ℝ) : Real.Angle) = 1) :
    supportValue K (t : Real.Angle) = polygonHeightValue h t := by
  apply le_antisymm (supportValue_le_polygonHeightValue h K hK (Or.inr ht))
  have hopp : supportValue K ((t + Real.pi : ℝ) : Real.Angle) ≤
      1 - polygonHeightValue h t := by
    apply supportValue_le_of_subset_normalHalfPlane
    intro p hp
    have hp' : p ∈ polygonHeightCap h := hK.symm ▸ hp
    have hl := (Set.mem_iInter₂.mp hp'.1 t ht).2
    change polygonHeightValue h t - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) at hl
    change inner ℝ p (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤ _
    rw [normalVector_add_pi, inner_neg_right]
    linarith
  linarith

/-- Niches grow with their heights when the fan remains fixed. -/
theorem polygonHeightNiche_mono_of_eq_endpoints {Θ : AngleSet}
    {h g : PolygonHeightSpace Θ} (hle : ∀ t, h t ≤ g t)
    (heq : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      polygonHeightValue h t = polygonHeightValue g t) :
    polygonHeightNiche h ⊆ polygonHeightNiche g := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue h t ≤ polygonHeightValue g t := by
    simpa only [polygonHeightValue, dite_eq_left ht] using hle ⟨t, ht⟩
  rintro p ⟨hpF, hpN⟩
  constructor
  · apply Set.mem_iInter₂.mpr
    intro t ht
    have hp := Set.mem_iInter₂.mp hpF t ht
    rwa [heq t ht] at hp
  · obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_, ?_⟩
    · change inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue g t - 1
      have hp₁ : inner ℝ p (normalVector (t : Real.Angle)) <
          polygonHeightValue h t - 1 := hp.1
      exact hp₁.trans_le (sub_le_sub_right (hval t (Or.inl (Or.inl ht))) 1)
    · change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        polygonHeightValue g (t + Real.pi / 2) - 1
      have hp₂ : inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
          polygonHeightValue h (t + Real.pi / 2) - 1 := hp.2
      exact hp₂.trans_le (sub_le_sub_right
        (hval (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))) 1)

/-- Every polygon height niche is bounded. -/
theorem isBounded_polygonHeightNiche {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Bornology.IsBounded (polygonHeightNiche h) := by
  let a := polygonHeightValue h (Real.pi / 2) - 1
  let Q (t : ℝ) : Set Point := {p | a ≤ p 1 ∧
    inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue h t - 1 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      polygonHeightValue h (t + Real.pi / 2) - 1}
  have hQ : Bornology.IsBounded (⋃ t ∈ Θ.directions, Q t) := by
    apply (Bornology.isBounded_biUnion_finset Θ.directions).2
    intro t ht
    exact isBounded_setOf_le_snd_and_inner_lt _ _ _ t
      ⟨(Θ.interior t ht).1, (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  apply hQ.subset
  rintro p ⟨hpF, hpN⟩
  obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
  apply Set.mem_iUnion₂.mpr
  refine ⟨t, ht, ?_, hp⟩
  have hpT := Set.mem_iInter₂.mp hpF (Real.pi / 2) (by simp)
  change a ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
  simpa [normalVector, frame, PiLp.inner_apply] using hpT

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Height / Raised Support
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Increase one selected support height by the prescribed amount. -/
def raisedPolygonSupport {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (ε : ℝ) : PolygonHeightSpace Θ := by
  classical
  exact fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle) +
    if s = t then ε else 0

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Basic
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Normal direction, height and boundary conventions specifying a planar half-plane. -/
structure PlanarHalfPlaneData where
  /-- The angle of the half-plane’s normal vector. -/
  angle : Real.Angle
  /-- The scalar-product threshold defining the boundary line. -/
  height : ℝ
  /-- Select the side above the threshold when true, or below it when false. -/
  upper : Bool
  /-- Exclude the boundary line when true. -/
  strict : Bool

/-- The half-plane defined by the recorded normal, threshold and conventions. -/
def PlanarHalfPlaneData.carrier (H : PlanarHalfPlaneData) : Set Point :=
  normalHalfPlane H.angle H.height H.upper H.strict

/-- The line where the normal scalar product equals the recorded height. -/
def PlanarHalfPlaneData.boundaryLine (H : PlanarHalfPlaneData) : Set Point :=
  normalLine H.angle H.height

/-- Evaluate a Boolean function on the point’s memberships in a finite family of sets. -/
def booleanSet {n : ℕ} (E : BooleanFunction n) (H : Fin n → Set Point) : Set Point := by
  classical
  exact {p | E (fun i ↦ decide (p ∈ H i)) = true}

/-- The set is a finite Boolean combination of planar half-planes. -/
def IsNefPolygon (X : Set Point) : Prop :=
  ∃ (n : ℕ) (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData),
    X = booleanSet E (fun i ↦ (H i).carrier)

/-- A monotone Boolean representation uses the supplied walls with distinct boundary lines. -/
def IsSimpleNefPolygonWith {n : ℕ} (X : Set Point)
    (H : Fin n → PlanarHalfPlaneData) : Prop :=
  Function.Injective (fun i ↦ (H i).boundaryLine) ∧
    ∃ E : BooleanFunction n, IsMonotoneBooleanFunction E ∧
      X = booleanSet E (fun i ↦ (H i).carrier)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Cap Construction
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The upper walls and two lower endpoint walls defining the polygonal cap. -/
def polygonCapWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set PlanarHalfPlaneData :=
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩ :
    PlanarHalfPlaneData)) '' angleDomain Θ ∪
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ :
    PlanarHalfPlaneData)) '' {Θ.angle, Real.pi / 2}

/-- The strict inner walls and two lower endpoint walls defining the polygonal niche. -/
def polygonNicheWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set PlanarHalfPlaneData :=
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, false, true⟩ :
    PlanarHalfPlaneData)) ''
      ((Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)) ∪
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ :
    PlanarHalfPlaneData)) '' {Θ.angle, Real.pi / 2}

private theorem angleDomain_finite (Θ : AngleSet) : (angleDomain Θ).Finite := by
  unfold angleDomain
  exact (Θ.directions.finite_toSet.union
    (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
      (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)

private theorem polygonInnerAngles_finite (Θ : AngleSet) :
    ((Θ.directions : Set ℝ) ∪
      ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)).Finite :=
  Θ.directions.finite_toSet.union
    (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))

private theorem polygonInnerAngles_subset_angleDomain (Θ : AngleSet) :
    (Θ.directions : Set ℝ) ∪
      ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions) ⊆ angleDomain Θ := by
  intro t ht
  exact Or.inl ht

private theorem polygonInnerAngle_ne_endpoint {Θ : AngleSet} {s t : ℝ}
    (hs : s ∈ (Θ.directions : Set ℝ) ∪
      ((fun r : ℝ ↦ r + Real.pi / 2) '' Θ.directions))
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) : s ≠ t := by
  rcases hs with hs | ⟨r, hr, rfl⟩
  · have hsI := Θ.interior s hs
    rcases ht with ht | ht
    · intro hst
      exact hsI.2.ne (hst.trans ht)
    · have ht' : t = Real.pi / 2 := by simpa using ht
      intro hst
      exact (ne_of_lt (hsI.2.trans_le Θ.angle_le)) (hst.trans ht')
  · have hrI := Θ.interior r hr
    rcases ht with ht | ht
    · intro hst
      have hgt : Θ.angle < r + Real.pi / 2 := by
        linarith [Θ.angle_le, hrI.1, Real.pi_pos]
      exact hgt.ne' (hst.trans ht)
    · have ht' : t = Real.pi / 2 := by simpa using ht
      intro hst
      have hgt : Real.pi / 2 < r + Real.pi / 2 := by linarith [hrI.1]
      exact hgt.ne' (hst.trans ht')

private theorem polygonCapWalls_finite {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    (polygonCapWalls h).Finite := by
  unfold polygonCapWalls
  exact ((angleDomain_finite Θ).image _).union
    ((Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle).image _)

private theorem polygonNicheWalls_finite {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    (polygonNicheWalls h).Finite := by
  unfold polygonNicheWalls
  exact ((polygonInnerAngles_finite Θ).image _).union
    ((Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle).image _)

private def polygonUpperWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩

private def polygonLowerWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩

private def polygonInnerWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t - 1, false, true⟩

private theorem polygonCapWalls_eq {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    polygonCapWalls h =
      polygonUpperWall h '' angleDomain Θ ∪
        polygonLowerWall h '' ({Θ.angle, Real.pi / 2} : Set ℝ) := by
  rfl

private theorem polygonNicheWalls_eq {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    polygonNicheWalls h =
      polygonInnerWall h ''
          ((Θ.directions : Set ℝ) ∪
            ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)) ∪
        polygonLowerWall h '' ({Θ.angle, Real.pi / 2} : Set ℝ) := by
  rfl

private theorem boundaryLine_injOn_polygonCapWalls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    Set.InjOn PlanarHalfPlaneData.boundaryLine (polygonCapWalls h) := by
  intro A hA B hB hline
  rw [polygonCapWalls_eq] at hA hB
  rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ ht)).mp hline
    simp [hst.1]
  · have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ htD)).mp hline
    have hfalse := hst.2
    simp [polygonUpperWall, polygonLowerWall, hst.1] at hfalse
    exfalso
    linarith
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ ht)).mp hline
    have hfalse := hst.2
    simp [polygonUpperWall, polygonLowerWall, hst.1] at hfalse
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]

private theorem boundaryLine_injOn_polygonNicheWalls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    Set.InjOn PlanarHalfPlaneData.boundaryLine (polygonNicheWalls h) := by
  intro A hA B hB hline
  rw [polygonNicheWalls_eq] at hA hB
  rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hsD := polygonInnerAngles_subset_angleDomain Θ hs
    have htD := polygonInnerAngles_subset_angleDomain Θ ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]
  · have hsD := polygonInnerAngles_subset_angleDomain Θ hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    exact (polygonInnerAngle_ne_endpoint hs ht hst.1).elim
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD := polygonInnerAngles_subset_angleDomain Θ ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    exact (polygonInnerAngle_ne_endpoint ht hs hst.1.symm).elim
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]

private def PositiveBooleanFormula.conjunctions {n : ℕ}
    (default : PositiveBooleanFormula n) :
    List (PositiveBooleanFormula n) → PositiveBooleanFormula n
  | [] => default
  | E :: Es => .conjunction E (conjunctions default Es)

private def PositiveBooleanFormula.disjunctions {n : ℕ}
    (default : PositiveBooleanFormula n) :
    List (PositiveBooleanFormula n) → PositiveBooleanFormula n
  | [] => default
  | E :: Es => .disjunction E (disjunctions default Es)

private theorem PositiveBooleanFormula.conjunctions_eval_eq_true {n : ℕ}
    (default : PositiveBooleanFormula n) (Es : List (PositiveBooleanFormula n))
    (P : Fin n → Bool) :
    (default.conjunctions Es).eval P = true ↔
      default.eval P = true ∧ ∀ E ∈ Es, E.eval P = true := by
  induction Es with
  | nil => simp [PositiveBooleanFormula.conjunctions]
  | cons E Es ih =>
      simp [PositiveBooleanFormula.conjunctions, PositiveBooleanFormula.eval, ih,
        and_left_comm]

private theorem PositiveBooleanFormula.disjunctions_eval_eq_true {n : ℕ}
    (default : PositiveBooleanFormula n) (Es : List (PositiveBooleanFormula n))
    (P : Fin n → Bool) :
    (default.disjunctions Es).eval P = true ↔
      default.eval P = true ∨ ∃ E ∈ Es, E.eval P = true := by
  induction Es with
  | nil => simp [PositiveBooleanFormula.disjunctions]
  | cons E Es ih =>
      simp [PositiveBooleanFormula.disjunctions, PositiveBooleanFormula.eval, ih,
        or_left_comm]

private theorem mem_polygonHeightCap_iff_walls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (p : Point) :
    p ∈ polygonHeightCap h ↔
      ∀ W ∈ polygonCapWalls h, p ∈ W.carrier := by
  simp only [polygonHeightCap, polygonHeightParallelogram, polygonCapWalls,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨hendpoint, hinner⟩ W
    rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · change p ∈ normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false
      rcases ht with ht | ht
      · exact hinner t ht
      · exact (hendpoint t ht).1
    · change p ∈ normalHalfPlane (t : Real.Angle)
          (polygonHeightValue h t - 1) true false
      exact (hendpoint t ht).2
  · intro hall
    refine ⟨?_, ?_⟩
    · intro t ht
      constructor
      · exact hall (polygonUpperWall h t) (Or.inl ⟨t, Or.inr ht, rfl⟩)
      · exact hall (polygonLowerWall h t) (Or.inr ⟨t, ht, rfl⟩)
    · intro t ht
      exact hall (polygonUpperWall h t) (Or.inl ⟨t, Or.inl ht, rfl⟩)

private theorem mem_polygonHeightNiche_iff_walls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (p : Point) :
    p ∈ polygonHeightNiche h ↔
      (∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        p ∈ (polygonLowerWall h t).carrier) ∧
      ∃ t ∈ Θ.directions,
        p ∈ (polygonInnerWall h t).carrier ∧
        p ∈ (polygonInnerWall h (t + Real.pi / 2)).carrier := by
  unfold polygonHeightNiche polygonHeightFan
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hfan, hniche⟩
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hfan t ht
    · obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hniche
      exact ⟨t, ht, hp⟩
  · rintro ⟨hfan, t, ht, hp⟩
    refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    exact hp

private theorem exists_polygonHeightCap_simpleNef (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonCapWalls h ∧
        IsSimpleNefPolygonWith (polygonHeightCap h) H := by
  classical
  let S : Set PlanarHalfPlaneData := polygonCapWalls h
  have hSfinite : S.Finite := polygonCapWalls_finite h
  let _ : Fintype S := hSfinite.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let H : Fin n → PlanarHalfPlaneData := fun i ↦ (e i).1
  have hrange : Set.range H = polygonCapWalls h := by
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hW
      obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hHinj : Function.Injective (fun i ↦ (H i).boundaryLine) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact boundaryLine_injOn_polygonCapWalls h (e i).2 (e j).2 hij
  have hupperω : polygonUpperWall h Θ.angle ∈ S := by
    exact Or.inl ⟨Θ.angle, by simp [angleDomain], rfl⟩
  let i₀ : Fin n := e.symm ⟨polygonUpperWall h Θ.angle, hupperω⟩
  let varList : List (PositiveBooleanFormula n) :=
    List.ofFn fun i : Fin n ↦ PositiveBooleanFormula.variable i
  let formula : PositiveBooleanFormula n :=
    (PositiveBooleanFormula.variable i₀).conjunctions varList
  refine ⟨n, H, hrange, hHinj, formula.eval,
    positiveBooleanFormula_monotone formula, ?_⟩
  ext p
  rw [mem_polygonHeightCap_iff_walls]
  change (∀ W ∈ polygonCapWalls h, p ∈ W.carrier) ↔
    formula.eval (fun i ↦ decide (p ∈ (H i).carrier)) = true
  have hformula (P : Fin n → Bool) :
      formula.eval P = true ↔ ∀ i, P i = true := by
    rw [show formula = (PositiveBooleanFormula.variable i₀).conjunctions varList by rfl,
      PositiveBooleanFormula.conjunctions_eval_eq_true]
    simp [varList, PositiveBooleanFormula.eval]
    aesop
  rw [hformula]
  constructor
  · intro hall i
    apply decide_eq_true
    exact hall (H i) (e i).2
  · intro hall W hW
    obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
    have hi' : H i = W := congrArg Subtype.val hi
    subst W
    exact of_decide_eq_true (hall i)

private theorem exists_polygonHeightNiche_simpleNef (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonNicheWalls h ∧
        IsSimpleNefPolygonWith (polygonHeightNiche h) H := by
  classical
  let S : Set PlanarHalfPlaneData := polygonNicheWalls h
  have hSfinite : S.Finite := polygonNicheWalls_finite h
  let _ : Fintype S := hSfinite.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let H : Fin n → PlanarHalfPlaneData := fun i ↦ (e i).1
  have hrange : Set.range H = polygonNicheWalls h := by
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hW
      obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hHinj : Function.Injective (fun i ↦ (H i).boundaryLine) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact boundaryLine_injOn_polygonNicheWalls h (e i).2 (e j).2 hij
  have hlowerω : polygonLowerWall h Θ.angle ∈ S := by
    exact Or.inr ⟨Θ.angle, by simp, rfl⟩
  have hlowerT : polygonLowerWall h (Real.pi / 2) ∈ S := by
    exact Or.inr ⟨Real.pi / 2, by simp, rfl⟩
  have hinner (t : ℝ) (ht : t ∈ Θ.directions) :
      polygonInnerWall h t ∈ S := by
    exact Or.inl ⟨t, Or.inl ht, rfl⟩
  have hinnerShift (t : ℝ) (ht : t ∈ Θ.directions) :
      polygonInnerWall h (t + Real.pi / 2) ∈ S := by
    exact Or.inl ⟨t + Real.pi / 2, Or.inr ⟨t, ht, rfl⟩, rfl⟩
  let iω : Fin n := e.symm ⟨polygonLowerWall h Θ.angle, hlowerω⟩
  let iT : Fin n := e.symm ⟨polygonLowerWall h (Real.pi / 2), hlowerT⟩
  let innerIndex : Θ.directions → Fin n :=
    fun t ↦ e.symm ⟨polygonInnerWall h t, hinner t t.property⟩
  let shiftedIndex : Θ.directions → Fin n :=
    fun t ↦ e.symm ⟨polygonInnerWall h (t + Real.pi / 2), hinnerShift t t.property⟩
  let pairFormula : Θ.directions → PositiveBooleanFormula n :=
    fun t ↦ .conjunction (.variable (innerIndex t)) (.variable (shiftedIndex t))
  let t₀ : Θ.directions := ⟨Θ.nonempty.choose, Θ.nonempty.choose_spec⟩
  let pairList : List (PositiveBooleanFormula n) :=
    Θ.directions.attach.toList.map pairFormula
  let endpointFormula : PositiveBooleanFormula n :=
    .conjunction (.variable iω) (.variable iT)
  let interiorFormula : PositiveBooleanFormula n :=
    (pairFormula t₀).disjunctions pairList
  let formula : PositiveBooleanFormula n :=
    .conjunction endpointFormula interiorFormula
  have hHiω : H iω = polygonLowerWall h Θ.angle := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonLowerWall h Θ.angle, hlowerω⟩)
  have hHiT : H iT = polygonLowerWall h (Real.pi / 2) := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonLowerWall h (Real.pi / 2), hlowerT⟩)
  have hHinner (t : Θ.directions) :
      H (innerIndex t) = polygonInnerWall h t := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonInnerWall h t, hinner t t.property⟩)
  have hHshift (t : Θ.directions) :
      H (shiftedIndex t) = polygonInnerWall h (t + Real.pi / 2) := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonInnerWall h (t + Real.pi / 2), hinnerShift t t.property⟩)
  refine ⟨n, H, hrange, hHinj, formula.eval,
    positiveBooleanFormula_monotone formula, ?_⟩
  ext p
  rw [mem_polygonHeightNiche_iff_walls]
  change ((∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      p ∈ (polygonLowerWall h t).carrier) ∧
    ∃ t ∈ Θ.directions,
      p ∈ (polygonInnerWall h t).carrier ∧
      p ∈ (polygonInnerWall h (t + Real.pi / 2)).carrier) ↔
    formula.eval (fun i ↦ decide (p ∈ (H i).carrier)) = true
  have hpair (t : Θ.directions) (P : Fin n → Bool) :
      (pairFormula t).eval P = true ↔
        P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    simp [pairFormula, PositiveBooleanFormula.eval]
  have hinterior (P : Fin n → Bool) :
      interiorFormula.eval P = true ↔
        ∃ t : Θ.directions,
          P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    rw [show interiorFormula = (pairFormula t₀).disjunctions pairList by rfl,
      PositiveBooleanFormula.disjunctions_eval_eq_true]
    simp only [hpair]
    constructor
    · rintro (ht₀ | ⟨E, hE, hEval⟩)
      · exact ⟨t₀, ht₀⟩
      · rw [show pairList = Θ.directions.attach.toList.map pairFormula by rfl] at hE
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hE
        exact ⟨t, (hpair t P).mp hEval⟩
    · rintro ⟨t, hEval⟩
      right
      refine ⟨pairFormula t, ?_, (hpair t P).mpr hEval⟩
      rw [show pairList = Θ.directions.attach.toList.map pairFormula by rfl]
      exact List.mem_map.mpr ⟨t, by simp, rfl⟩
  have hformula (P : Fin n → Bool) :
      formula.eval P = true ↔
        (P iω = true ∧ P iT = true) ∧
          ∃ t : Θ.directions,
            P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    rw [show formula = .conjunction endpointFormula interiorFormula by rfl]
    simp only [PositiveBooleanFormula.eval, Bool.and_eq_true, hinterior]
    simp [endpointFormula, PositiveBooleanFormula.eval]
  rw [hformula]
  constructor
  · rintro ⟨hendpoint, t, ht, htinner, htshift⟩
    let ts : Θ.directions := ⟨t, ht⟩
    refine ⟨⟨?_, ?_⟩, ts, ?_, ?_⟩
    · apply decide_eq_true
      rw [hHiω]
      exact hendpoint Θ.angle (by simp)
    · apply decide_eq_true
      rw [hHiT]
      exact hendpoint (Real.pi / 2) (by simp)
    · apply decide_eq_true
      rw [hHinner ts]
      exact htinner
    · apply decide_eq_true
      rw [hHshift ts]
      exact htshift
  · rintro ⟨⟨hω, hT⟩, t, htinner, htshift⟩
    refine ⟨?_, t, t.property, ?_, ?_⟩
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        rw [← hHiω]
        exact of_decide_eq_true hω
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        rw [← hHiT]
        exact of_decide_eq_true hT
    · rw [← hHinner t]
      exact of_decide_eq_true htinner
    · rw [← hHshift t]
      exact of_decide_eq_true htshift

theorem polygonCap_niche_simpleNef (Θ : AngleSet) (h : PolygonHeightSpace Θ) :
    (∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonCapWalls h ∧ IsSimpleNefPolygonWith (polygonHeightCap h) H) ∧
    (∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonNicheWalls h ∧ IsSimpleNefPolygonWith (polygonHeightNiche h) H) := by
  exact ⟨exists_polygonHeightCap_simpleNef Θ h, exists_polygonHeightNiche_simpleNef Θ h⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Cells
-/

@[expose] public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma monotoneBoolean_update_false {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E (Function.update P i false) = true → E P = true := by
  apply hE
  intro j hj
  by_cases hji : j = i
  · subst j
    simp at hj
  · simpa [Function.update_of_ne hji] using hj

lemma monotoneBoolean_update_true {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E P = true → E (Function.update P i true) = true := by
  apply hE
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma monotoneBoolean_eval_iff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E P = true ↔ E (Function.update P i false) = true ∨
      (P i = true ∧ E (Function.update P i true) = true) := by
  constructor
  · intro h
    cases hp : P i
    · left
      rwa [← hp, Function.update_eq_self]
    · exact Or.inr ⟨rfl, monotoneBoolean_update_true hE P i h⟩
  · rintro (h | ⟨hp, h⟩)
    · exact monotoneBoolean_update_false hE P i h
    · rwa [(Function.update_eq_self_iff).mpr hp.symm] at h

lemma booleanSet_update_eq {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → Set Point) (i : Fin n)
    (S : Set Point) :
    booleanSet E (Function.update H i S) =
      booleanSet E (Function.update H i ∅) ∪
        (S ∩ booleanSet E (Function.update H i Set.univ)) := by
  classical
  ext p
  have hfun (T : Set Point) :
      (fun j ↦ decide (p ∈ Function.update H i T j)) =
        Function.update (fun j ↦ decide (p ∈ H j)) i (decide (p ∈ T)) := by
    funext j
    by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
  simp only [booleanSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, hfun]
  simp only [Set.mem_empty_iff_false, decide_false, Set.mem_univ, decide_true]
  have h := monotoneBoolean_eval_iff hE
    (Function.update (fun j ↦ decide (p ∈ H j)) i (decide (p ∈ S))) i
  simpa only [Function.update_idem, Function.update_self, decide_eq_true_eq] using h

lemma booleanSet_update_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → Set Point) (i : Fin n)
    (S T : Set Point) :
    booleanSet E (Function.update H i S) \ booleanSet E (Function.update H i T) =
      (S \ T) ∩ (booleanSet E (Function.update H i Set.univ) \
        booleanSet E (Function.update H i ∅)) := by
  rw [booleanSet_update_eq hE H i S, booleanSet_update_eq hE H i T]
  ext p
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
  tauto

lemma booleanSet_mono {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) {H G : Fin n → Set Point}
    (hHG : ∀ i, H i ⊆ G i) : booleanSet E H ⊆ booleanSet E G := by
  classical
  intro p hp
  apply hE _ _ ?_ hp
  intro i hi
  simp only [decide_eq_true_eq] at hi ⊢
  exact hHG i hi

/-- The points realizing exactly the specified Boolean membership pattern. -/
def booleanCell {n : ℕ} (H : Fin n → Set Point) (P : Fin n → Bool) : Set Point :=
  ⋂ j, if P j then H j else (H j)ᶜ

/-- The vector of membership decisions for a point in a finite set family. -/
def setMembershipPattern {n : ℕ} (H : Fin n → Set Point) (p : Point) : Fin n → Bool := by
  classical
  exact fun j ↦ decide (p ∈ H j)

lemma mem_booleanCell_iff {n : ℕ} (H : Fin n → Set Point) (P : Fin n → Bool)
    (p : Point) :
    p ∈ booleanCell H P ↔ setMembershipPattern H p = P := by
  classical
  simp only [booleanCell, Set.mem_iInter]
  constructor
  · intro hp
    funext j
    have hj := hp j
    cases hP : P j <;> simp only [hP, Bool.false_eq_true, ↓reduceIte, Set.mem_compl_iff,
      setMembershipPattern,
      decide_eq_false_iff_not, decide_eq_true_eq] at hj ⊢ <;> exact hj
  · intro hp j
    have hj := congrFun hp j
    cases hP : P j <;> simp only [setMembershipPattern, hP, decide_eq_false_iff_not,
      Bool.false_eq_true, ↓reduceIte,
      Set.mem_compl_iff, decide_eq_true_eq] at hj ⊢ <;> exact hj

lemma booleanSet_eq_iUnion_booleanCell {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → Set Point) :
    booleanSet E H = ⋃ P : Fin n → Bool, if E P = true then booleanCell H P else ∅ := by
  classical
  ext p
  simp only [booleanSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_ite_empty_right]
  constructor
  · intro hp
    change E (setMembershipPattern H p) = true at hp
    refine ⟨setMembershipPattern H p, ?_, (mem_booleanCell_iff H _ p).mpr rfl⟩
    exact hp
  · rintro ⟨P, hEP, hp⟩
    have hpat := (mem_booleanCell_iff H P p).mp hp
    calc
      E (fun j ↦ decide (p ∈ H j)) = E (setMembershipPattern H p) := by
        congr 1
      _ = E P := congrArg E hpat
      _ = true := hEP

/-- Intersect the closed sides of each wall selected by the Boolean pattern. -/
def closedBooleanCell {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) : Set Point :=
  ⋂ j, normalHalfPlane (H j).angle (H j).height
    (if P j then (H j).upper else !(H j).upper) false

lemma mem_booleanCell_iff_mem_closedBooleanCell_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (p : Point)
    (hp : ∀ j, inner ℝ p (normalVector (H j).angle) ≠ (H j).height) :
    p ∈ booleanCell (fun j ↦ (H j).carrier) P ↔ p ∈ closedBooleanCell H P := by
  simp only [booleanCell, closedBooleanCell, Set.mem_iInter]
  constructor <;> intro h j
  · have hj := h j
    have hne := hp j
    rcases lt_or_gt_of_ne hne with hlt | hgt <;>
      cases hP : P j <;> cases hu : (H j).upper <;> cases hs : (H j).strict <;>
      simp only [hP, hu, hs, PlanarHalfPlaneData.carrier, normalHalfPlane,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢ <;> linarith
  · have hj := h j
    have hne := hp j
    rcases lt_or_gt_of_ne hne with hlt | hgt <;>
      cases hP : P j <;> cases hu : (H j).upper <;> cases hs : (H j).strict <;>
      simp only [hP, hu, hs, PlanarHalfPlaneData.carrier, normalHalfPlane,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢ <;> linarith

/-- Switching the selected input from false to true switches the output to true. -/
def IsActiveBooleanPattern {n : ℕ} (E : BooleanFunction n) (i : Fin n)
    (P : Fin n → Bool) : Prop :=
  E (Function.update P i false) = false ∧
    E (Function.update P i true) = true

/-- All input patterns for which the selected Boolean variable is active. -/
def activeBooleanPatterns {n : ℕ} (E : BooleanFunction n) (i : Fin n) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (IsActiveBooleanPattern E i)

/-- The set gained by making the selected wall universally true rather than false. -/
def activeBooleanRegion {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) : Set Point :=
  booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
    booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)

lemma mem_activeBooleanRegion_iff {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (p : Point) :
    p ∈ activeBooleanRegion E H i ↔
      IsActiveBooleanPattern E i (setMembershipPattern (fun j ↦ (H j).carrier) p) := by
  classical
  unfold activeBooleanRegion IsActiveBooleanPattern
  simp only [Set.mem_sdiff, booleanSet, Set.mem_ofPred_eq]
  have huniv : (fun j ↦ decide (p ∈ Function.update
      (fun j ↦ (H j).carrier) i Set.univ j)) =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i true := by
    funext j
    by_cases hji : j = i <;>
      simp [hji, Function.update_of_ne, setMembershipPattern]
  have hempty : (fun j ↦ decide (p ∈ Function.update
      (fun j ↦ (H j).carrier) i ∅ j)) =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i false := by
    funext j
    by_cases hji : j = i <;>
      simp [hji, Function.update_of_ne, setMembershipPattern]
  rw [huniv, hempty]
  cases hfalse : E (Function.update (setMembershipPattern
      (fun j ↦ (H j).carrier) p) i false) <;> simp

lemma measurableSet_planarHalfPlane_carrier (H : PlanarHalfPlaneData) :
    MeasurableSet H.carrier := by
  cases hu : H.upper <;> cases hs : H.strict <;>
    simp only [PlanarHalfPlaneData.carrier, normalHalfPlane, hu, hs,
      Bool.false_eq_true, ↓reduceIte] <;> measurability

lemma eventually_mem_carrier_iff_of_not_mem_boundaryLine (H : PlanarHalfPlaneData)
    (p : Point) (hp : p ∉ H.boundaryLine) :
    ∀ᶠ q in 𝓝 p, (q ∈ H.carrier ↔ p ∈ H.carrier) := by
  have hpne : inner ℝ p (normalVector H.angle) ≠ H.height := hp
  have hcont : Continuous (fun q : Point ↦ inner ℝ q (normalVector H.angle)) := by
    fun_prop
  rcases lt_or_gt_of_ne hpne with hplt | hpgt
  · have hev : ∀ᶠ q in 𝓝 p, inner ℝ q (normalVector H.angle) < H.height :=
      hcont.continuousAt.eventually_lt continuousAt_const hplt
    filter_upwards [hev] with q hq
    change (q ∈ normalHalfPlane H.angle H.height H.upper H.strict ↔
      p ∈ normalHalfPlane H.angle H.height H.upper H.strict)
    simp only [normalHalfPlane, Set.mem_ofPred_eq]
    cases H.upper <;> cases H.strict <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> intro hm <;> linarith
  · have hev : ∀ᶠ q in 𝓝 p, H.height < inner ℝ q (normalVector H.angle) :=
      continuousAt_const.eventually_lt hcont.continuousAt hpgt
    filter_upwards [hev] with q hq
    change (q ∈ normalHalfPlane H.angle H.height H.upper H.strict ↔
      p ∈ normalHalfPlane H.angle H.height H.upper H.strict)
    simp only [normalHalfPlane, Set.mem_ofPred_eq]
    cases H.upper <;> cases H.strict <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> intro hm <;> linarith

lemma eventually_setMembershipPattern_eq_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (p : Point)
    (hp : ∀ j, j ≠ i → p ∉ (H j).boundaryLine) :
    ∀ᶠ q in 𝓝 p, ∀ j, j ≠ i →
      setMembershipPattern (fun k ↦ (H k).carrier) q j =
        setMembershipPattern (fun k ↦ (H k).carrier) p j := by
  suffices ∀ᶠ q in 𝓝 p, ∀ j ∈ (Set.univ : Set (Fin n)), j ≠ i →
      setMembershipPattern (fun k ↦ (H k).carrier) q j =
        setMembershipPattern (fun k ↦ (H k).carrier) p j by
    exact this.mono fun q hq j ↦ hq j (Set.mem_univ j)
  apply (Filter.eventually_all_finite Set.finite_univ).2
  intro j _
  by_cases hji : j = i
  · exact Filter.Eventually.of_forall fun _ hj ↦ (hj hji).elim
  · filter_upwards [eventually_mem_carrier_iff_of_not_mem_boundaryLine (H j) p
      (hp j hji)] with q hq
    intro _
    simp only [setMembershipPattern]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hq

lemma measurableSet_booleanCell {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) :
    MeasurableSet (booleanCell (fun j ↦ (H j).carrier) P) := by
  apply MeasurableSet.iInter
  intro j
  cases hP : P j
  · simpa [booleanCell, hP] using (measurableSet_planarHalfPlane_carrier (H j)).compl
  · simpa [booleanCell, hP] using measurableSet_planarHalfPlane_carrier (H j)

lemma measurableSet_booleanSet {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) :
    MeasurableSet (booleanSet E (fun j ↦ (H j).carrier)) := by
  rw [booleanSet_eq_iUnion_booleanCell]
  apply MeasurableSet.iUnion
  intro P
  by_cases hP : E P = true
  · simpa [hP] using measurableSet_booleanCell H P
  · simp [hP]

lemma monotoneBoolean_update_false_true {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (i : Fin n) (P : Fin n → Bool) :
    E (Function.update P i false) = true →
      E (Function.update P i true) = true := by
  intro htrue
  apply hE _ _ _ htrue
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma not_isActiveBooleanPattern_iff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (i : Fin n) (P : Fin n → Bool) :
    ¬IsActiveBooleanPattern E i P ↔
      E (Function.update P i false) = E (Function.update P i true) := by
  unfold IsActiveBooleanPattern
  constructor
  · intro hnot
    cases hf : E (Function.update P i false) <;>
      cases ht : E (Function.update P i true)
    · rfl
    · exact (hnot ⟨hf, ht⟩).elim
    · have hcontra := monotoneBoolean_update_false_true hE i P hf
      rw [ht] at hcontra
      exact (Bool.false_ne_true hcontra).elim
    · rfl
  · intro heq hactive
    rw [hactive.1, hactive.2] at heq
    exact Bool.false_ne_true heq

end MovingSofa.Nef

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Height
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Change one wall’s height by `δ` in a Boolean half-plane representation. -/
def perturbNefHeight {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) : Set Point :=
  booleanSet E (fun j ↦
    (if j = i then { H j with height := (H j).height + δ } else H j).carrier)

end MovingSofa

namespace MovingSofa.Nef

open Filter Topology

lemma perturbNefHeight_eq_update {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E H i δ = booleanSet E
      (Function.update (fun j ↦ (H j).carrier) i
        ({ H i with height := (H i).height + δ }).carrier) := by
  unfold perturbNefHeight
  congr 1
  funext j
  by_cases hji : j = i <;> simp [hji, Function.update_of_ne]

lemma perturbNefHeight_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (δ ε : ℝ) :
    perturbNefHeight E H i δ \ perturbNefHeight E H i ε =
      (({ H i with height := (H i).height + δ }).carrier \
        ({ H i with height := (H i).height + ε }).carrier) ∩
        (booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
          booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)) := by
  rw [perturbNefHeight_eq_update, perturbNefHeight_eq_update]
  exact booleanSet_update_sdiff hE _ _ _ _

/-- The half-open strip-height interval matching the wall’s strictness convention. -/
def heightInterval (strict : Bool) (h δ ε : ℝ) : Set ℝ :=
  if strict then Set.Ico (h + ε) (h + δ) else Set.Ioc (h + ε) (h + δ)

lemma measurableSet_heightInterval (strict : Bool) (h δ ε : ℝ) :
    MeasurableSet (heightInterval strict h δ ε) := by
  cases strict <;> simp [heightInterval]

lemma integral_heightInterval_eq_intervalIntegral (strict : Bool)
    (h δ ε : ℝ) (f : ℝ → ℝ) (hεδ : ε ≤ δ) :
    (∫ x in heightInterval strict h δ ε, f x) =
      ∫ x in h + ε..h + δ, f x := by
  have hle : h + ε ≤ h + δ := by linarith
  cases strict
  · simp only [heightInterval, Bool.false_eq_true, ↓reduceIte]
    exact (intervalIntegral.integral_of_le hle).symm
  · simp only [heightInterval, ↓reduceIte]
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le hle).symm

lemma mem_heightInterval_bounds {strict : Bool} {h δ ε x : ℝ}
    (hx : x ∈ heightInterval strict h δ ε) :
    h + ε ≤ x ∧ x ≤ h + δ := by
  cases strict <;> simp [heightInterval] at hx <;>
    constructor <;> linarith [hx.1, hx.2]

lemma carrier_sdiff_carrier_eq_heightInterval (H : PlanarHalfPlaneData)
    (hSide : H.upper = false) (δ ε : ℝ) :
    ({ H with height := H.height + δ }).carrier \
        ({ H with height := H.height + ε }).carrier =
      {p | inner ℝ p (normalVector H.angle) ∈
        heightInterval H.strict H.height δ ε} := by
  ext p
  cases hs : H.strict <;>
    simp [PlanarHalfPlaneData.carrier, normalHalfPlane, hSide,
      heightInterval] <;> tauto

lemma perturbNefHeight_sdiff_eq_heightInterval {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (δ ε : ℝ) :
    perturbNefHeight E H i δ \ perturbNefHeight E H i ε =
      {p | inner ℝ p (normalVector (H i).angle) ∈
        heightInterval (H i).strict (H i).height δ ε} ∩
        (booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
          booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)) := by
  rw [perturbNefHeight_sdiff hE H i δ ε,
    carrier_sdiff_carrier_eq_heightInterval (H i) hSide]

lemma perturbNefHeight_mono {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) :
    Monotone (perturbNefHeight E H i) := by
  intro δ ε hδε
  apply booleanSet_mono hE
  intro j p hp
  by_cases hji : j = i
  · subst j
    simp only at hp ⊢
    change p ∈ normalHalfPlane (H i).angle ((H i).height + δ) (H i).upper
      (H i).strict at hp
    change p ∈ normalHalfPlane (H i).angle ((H i).height + ε) (H i).upper
      (H i).strict
    cases hstrict : (H i).strict <;>
      simp only [normalHalfPlane, hSide, hstrict, Bool.false_eq_true, ite_false,
        ite_true, Set.mem_ofPred_eq] at hp ⊢
    · exact hp.trans (add_le_add_right hδε _)
    · exact hp.trans_le (add_le_add_right hδε _)
  · simpa only [ite_eq_right hji] using hp

lemma measurableSet_perturbNefHeight {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    MeasurableSet (perturbNefHeight E H i δ) := by
  unfold perturbNefHeight
  apply measurableSet_booleanSet

lemma area_perturb_sub_eq_volume_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ δ ε : ℝ)
    (hεδ : ε ≤ δ) (hδ : |δ| ≤ ε₀) (hε : |ε| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    ClassicalResults.area (perturbNefHeight E H i δ) -
        ClassicalResults.area (perturbNefHeight E H i ε) =
      (MeasureTheory.volume
        (perturbNefHeight E H i δ \ perturbNefHeight E H i ε)).toReal := by
  have hmono := perturbNefHeight_mono hE H i hSide hεδ
  have hfiniteδ : MeasureTheory.volume (perturbNefHeight E H i δ) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono (hBound δ hδ))
      MeasureTheory.measure_closedBall_lt_top
  have hfiniteε : MeasureTheory.volume (perturbNefHeight E H i ε) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono (hBound ε hε))
      MeasureTheory.measure_closedBall_lt_top
  rw [ClassicalResults.area, ClassicalResults.area,
    ← ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hmono) hfiniteδ,
    ← MeasureTheory.measure_sdiff hmono
      (measurableSet_perturbNefHeight E H i ε).nullMeasurableSet hfiniteε]

lemma perturbNefHeight_zero {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) :
    perturbNefHeight E H i 0 = booleanSet E (fun j ↦ (H j).carrier) := by
  ext p
  simp [perturbNefHeight, PlanarHalfPlaneData.carrier]

end MovingSofa.Nef

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Perturbation Bounds
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The polygonal cap with independently specified upper and lower wall heights. -/
def independentWallCap {Θ : AngleSet} (upper lower : PolygonHeightSpace Θ) : Set Point :=
  (⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false ∩
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) ∩
  ⋂ t ∈ (Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false

/-- The polygonal niche determined by independently specified lower wall heights. -/
def independentWallNiche {Θ : AngleSet} (lower : PolygonHeightSpace Θ) : Set Point :=
  (⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) ∩
  ⋃ t ∈ Θ.directions,
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (polygonHeightValue lower (t + Real.pi / 2)) false true

theorem polygonPerturbation_uniform_bounds (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ R ε₀ : ℝ, 0 < R ∧ 0 < ε₀ ∧
      ∀ upper lower : PolygonHeightSpace Θ,
        (∀ t, |upper t - h t| ≤ ε₀) →
        (∀ t, |lower t - (h t - 1)| ≤ ε₀) →
        independentWallCap upper lower ⊆ Metric.closedBall 0 R ∧
        independentWallNiche lower ⊆ Metric.closedBall 0 R := by
  let a := polygonHeightValue h (Real.pi / 2) - 2
  let Q (t : ℝ) : Set Point := {p | a ≤ p 1 ∧
    inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue h t + 2 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      polygonHeightValue h (t + Real.pi / 2) + 2}
  have hQ : Bornology.IsBounded (⋃ t ∈ Θ.directions, Q t) := by
    apply (Bornology.isBounded_biUnion_finset Θ.directions).2
    intro t ht
    exact isBounded_setOf_le_snd_and_inner_lt _ _ _ t
      ⟨(Θ.interior t ht).1, (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  obtain ⟨R, hR, hbound⟩ := hQ.exists_pos_norm_le
  refine ⟨R, 1, hR, zero_lt_one, ?_⟩
  intro upper lower hu hl
  have huv (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue upper t ≤ polygonHeightValue h t + 1 := by
    have hh := (abs_le.mp (hu ⟨t, ht⟩)).2
    simp only [polygonHeightValue, dite_eq_left ht]
    linarith
  have hlv (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue h t - 2 ≤ polygonHeightValue lower t ∧
      polygonHeightValue lower t ≤ polygonHeightValue h t := by
    have hh := abs_le.mp (hl ⟨t, ht⟩)
    simp only [polygonHeightValue, dite_eq_left ht]
    constructor <;> linarith [hh.1, hh.2]
  have hy {p : Point}
      (hp : p ∈ ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) :
      a ≤ p 1 := by
    have hp' := Set.mem_iInter₂.mp hp (Real.pi / 2) (by simp)
    have hb := (hlv (Real.pi / 2) (Or.inr (by simp))).1
    have hp'' : polygonHeightValue lower (Real.pi / 2) ≤ p 1 := by
      simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hp'
    exact hb.trans hp''
  have hball {p : Point} (hp : p ∈ ⋃ t ∈ Θ.directions, Q t) :
      p ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound p hp
  constructor
  · intro p hp
    apply hball
    obtain ⟨t, ht⟩ := Θ.nonempty
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · apply hy
      exact Set.mem_iInter₂.mpr fun s hs ↦ (Set.mem_iInter₂.mp hp.1 s hs).2
    · have hb := Set.mem_iInter₂.mp hp.2 t (Or.inl ht)
      change inner ℝ p (normalVector (t : Real.Angle)) ≤ polygonHeightValue upper t at hb
      have hu' := huv t (Or.inl (Or.inl ht))
      linarith
    · have hb := Set.mem_iInter₂.mp hp.2 (t + Real.pi / 2) (Or.inr ⟨t, ht, rfl⟩)
      change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
        polygonHeightValue upper (t + Real.pi / 2) at hb
      have hu' := huv (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))
      linarith
  · rintro p ⟨hpF, hpN⟩
    apply hball
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, hy hpF, ?_, ?_⟩
    · have hb := (hlv t (Or.inl (Or.inl ht))).2
      have hp₁ : inner ℝ p (normalVector (t : Real.Angle)) <
          polygonHeightValue lower t := hp.1
      exact hp₁.trans_le (by linarith)
    · have hb := (hlv (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))).2
      exact hp.2.trans_le (by linarith)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Basic
-/

@[expose] public section

namespace MovingSofa

/-- A finite vertex sequence whose horizontal coordinates strictly increase. -/
structure XMonotonePolylineData where
  /-- The number of consecutive line segments in the polyline. -/
  edges : ℕ
  /-- The ordered sequence of polyline vertices. -/
  vertices : Fin (edges + 1) → Point
  increasing : StrictMono (fun i ↦ vertices i 0)

/-- The union of the segments between consecutive vertices. -/
def XMonotonePolylineData.carrier (p : XMonotonePolylineData) : Set Point :=
  ⋃ i : Fin p.edges, segment ℝ (p.vertices i.castSucc) (p.vertices i.succ)

/-- The set is the carrier of a polyline with strictly increasing horizontal coordinates. -/
def IsXMonotonePolyline (S : Set Point) : Prop :=
  ∃ p : XMonotonePolylineData, S = p.carrier

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Displacement
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The horizontal displacement of a rightward edge is its length times the sine of its normal. -/
lemma dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero {a b : Point} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a 0 < b 0)
    (horth : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) :
    dist a b * Real.sin t = b 0 - a 0 := by
  let r := inner ℝ (b - a) (tangentVector (t : Real.Angle))
  have hvec : r • tangentVector (t : Real.Angle) = b - a := by
    simpa only [horth, zero_smul, zero_add] using
      inner_normalVector_smul_add_inner_tangentVector_smul (b - a) (t : Real.Angle)
  have hcoord : -(r * Real.sin t) = b 0 - a 0 := by
    have h := congrArg (fun p : Point ↦ p 0) hvec
    simpa [tangentVector, frame] using h
  have hsin := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hr : r < 0 := by nlinarith
  have hn : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [EuclideanSpace.norm_sq_eq]
    simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hdist : dist a b = -r := by
    rw [dist_comm, dist_eq_norm, ← hvec, norm_smul, hn, mul_one,
      Real.norm_eq_abs, abs_of_neg hr]
  rw [hdist]
  linarith

/-- The sine-weighted edge lengths telescope to the horizontal endpoint displacement. -/
lemma XMonotonePolylineData.sum_dist_mul_sin
    (p : XMonotonePolylineData) (t : Fin p.edges → ℝ)
    (ht : ∀ i, t i ∈ Set.Ioo 0 Real.pi)
    (horth : ∀ i, inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t i : Real.Angle)) = 0) :
    ∑ i : Fin p.edges,
      dist (p.vertices i.castSucc) (p.vertices i.succ) * Real.sin (t i) =
        p.vertices (Fin.last p.edges) 0 - p.vertices 0 0 := by
  have hedge (i : Fin p.edges) := dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero
    (ht i) (p.increasing i.castSucc_lt_succ) (horth i)
  simp_rw [hedge]
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ (fun i : Fin (p.edges + 1) ↦ p.vertices i 0)
  have hlast := Fin.sum_univ_castSucc (fun i : Fin (p.edges + 1) ↦ p.vertices i 0)
  linarith

/-- A nonvertical segment has at most one normal angle strictly between zero and pi. -/
lemma eq_of_inner_sub_normalVector_eq_zero {a b : Point} {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hab : a 0 < b 0)
    (horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0)
    (hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) : s = t := by
  have hs' : (b 0 - a 0) * Real.cos s + (b 1 - a 1) * Real.sin s = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using horths
  have ht' : (b 0 - a 0) * Real.cos t + (b 1 - a 1) * Real.sin t = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using hortht
  have hprod : (b 0 - a 0) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin s * ht' - Real.sin t * hs'
  have hz : Real.sin (s - t) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_pos.mpr hab).ne'
  have := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])).mp hz
  linarith

/-- Grouping edge lengths by normal preserves the horizontal displacement identity. -/
lemma XMonotonePolylineData.sum_normal_lengths_mul_sin
    (p : XMonotonePolylineData) (D : Finset ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (hlabels : ∀ i : Fin p.edges, ∃ t ∈ D,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0) :
    ∑ t ∈ D, (∑ i : Fin p.edges,
      if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0 then
        dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t =
      p.vertices (Fin.last p.edges) 0 - p.vertices 0 0 := by
  classical
  choose t ht horth using hlabels
  calc
    _ = ∑ i : Fin p.edges, ∑ u ∈ D,
        (if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (u : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin u := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin p.edges,
        dist (p.vertices i.castSucc) (p.vertices i.succ) * Real.sin (t i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (t i)]
      · rw [ite_eq_left (horth i)]
      · intro u hu hut
        have hne : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
            (normalVector (u : Real.Angle)) ≠ 0 := by
          intro hzero
          exact hut (eq_of_inner_sub_normalVector_eq_zero (hD u hu) (hD _ (ht i))
            (p.increasing i.castSucc_lt_succ) hzero (horth i))
        simp [hne]
      · exact fun hnot ↦ (hnot (ht i)).elim
    _ = _ := p.sum_dist_mul_sin t (fun i ↦ hD _ (ht i)) horth

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Graph
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The point on the graph of a real-valued function above a given abscissa. -/
def pointOnGraph (f : ℝ → ℝ) (x : ℝ) : Point := !₂[x, f x]

/-- Evaluation of the affine function with slope-intercept pair `c`. -/
def affineValue (c : ℝ × ℝ) (x : ℝ) : ℝ := c.1 * x + c.2

/-- An affine real-valued function is continuous. -/
theorem continuous_affineValue (c : ℝ × ℝ) : Continuous (affineValue c) := by
  unfold affineValue
  fun_prop

private def affineCrossings (L : Finset (ℝ × ℝ)) : Set ℝ :=
  ⋃ c ∈ L, ⋃ d ∈ L.erase c, {x | affineValue c x = affineValue d x}

private theorem finite_affineValue_eq_of_ne {c d : ℝ × ℝ} (hcd : c ≠ d) :
    {x | affineValue c x = affineValue d x}.Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, affineValue] at hx hy
  by_cases hm : c.1 = d.1
  · rw [hm] at hx
    have hb : c.2 = d.2 := by linarith
    exact (hcd (Prod.ext hm hb)).elim
  · have hs : c.1 - d.1 ≠ 0 := sub_ne_zero.mpr hm
    have hprod : (c.1 - d.1) * (x - y) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hs)

private theorem finite_affineCrossings (L : Finset (ℝ × ℝ)) :
    (affineCrossings L).Finite := by
  apply L.finite_toSet.biUnion
  intro c hc
  apply (L.erase c).finite_toSet.biUnion
  intro d hd
  exact finite_affineValue_eq_of_ne (Finset.ne_of_mem_erase hd).symm

@[simp] theorem pointOnGraph_apply_zero (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x 0 = x := by
  rfl

@[simp] theorem pointOnGraph_apply_one (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x 1 = f x := by
  rfl

/-- The closed vertical epigraph of a real-valued function. -/
def verticalEpigraph (f : ℝ → ℝ) : Set Point :=
  {p | f (p 0) ≤ p 1}

/-- A continuous function has a closed vertical epigraph. -/
theorem isClosed_verticalEpigraph {f : ℝ → ℝ} (hf : Continuous f) :
    IsClosed (verticalEpigraph f) := by
  exact isClosed_le
    (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0))
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)

private theorem pointOnGraph_not_mem_interior_verticalEpigraph
    (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x ∉ interior (verticalEpigraph f) := by
  intro hx
  let q : ℕ → Point := fun n ↦ !₂[x, f x - (1 : ℝ) / (n + 1)]
  have hq : Filter.Tendsto q Filter.atTop (nhds (pointOnGraph f x)) := by
    apply (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Filter.Tendsto (fun _ : ℕ ↦ x) Filter.atTop (nhds x)
      exact tendsto_const_nhds
    · change Filter.Tendsto (fun n : ℕ ↦ f x - (1 : ℝ) / (n + 1))
        Filter.atTop (nhds (f x))
      simpa using (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hev : ∀ᶠ n in Filter.atTop, q n ∈ interior (verticalEpigraph f) :=
    hq (isOpen_interior.mem_nhds hx)
  obtain ⟨n, hn⟩ := hev.exists
  have hn' := interior_subset hn
  change f x ≤ f x - (1 : ℝ) / (n + 1) at hn'
  have : 0 < (1 : ℝ) / (n + 1) := by positivity
  linarith

/-- The frontier of a continuous vertical epigraph is its graph. -/
theorem frontier_verticalEpigraph {f : ℝ → ℝ} (hf : Continuous f) :
    frontier (verticalEpigraph f) = Set.range (pointOnGraph f) := by
  have hclosed := isClosed_verticalEpigraph hf
  ext p
  constructor
  · intro hp
    have hpE : p ∈ verticalEpigraph f := by
      exact hclosed.closure_eq ▸ frontier_subset_closure hp
    have hpNotInt : p ∉ interior (verticalEpigraph f) :=
      (mem_frontier_iff_notMem_interior hpE).mp hp
    have heq : f (p 0) = p 1 := by
      apply le_antisymm hpE
      apply le_of_not_gt
      intro hlt
      apply hpNotInt
      have hopen : IsOpen {q : Point | f (q 0) < q 1} :=
        isOpen_lt
          (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0))
          (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)
      exact interior_maximal (fun q hq ↦ by
        change f (q 0) ≤ q 1
        exact hq.le) hopen hlt
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp [pointOnGraph]
    · simpa [pointOnGraph] using heq
  · rintro ⟨x, rfl⟩
    apply (mem_frontier_iff_notMem_interior (s := verticalEpigraph f)
      (x := pointOnGraph f x) (by
        change f x ≤ f x
        exact le_rfl)).mpr
    exact pointOnGraph_not_mem_interior_verticalEpigraph f x

private def graphPolyline (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (f : ℝ → ℝ) : XMonotonePolylineData where
  edges := n
  vertices i := pointOnGraph f (x i)
  increasing := by
    simpa only [pointOnGraph_apply_zero] using hx

@[simp] private theorem graphPolyline_vertices (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (f : ℝ → ℝ) (i : Fin (n + 1)) :
    (graphPolyline n x hx f).vertices i = pointOnGraph f (x i) := by
  rfl

private theorem segment_pointOnGraph_affine {f : ℝ → ℝ} {m c a b : ℝ}
    (hab : a ≤ b) (hf : ∀ z ∈ Set.Icc a b, f z = m * z + c) :
    segment ℝ (pointOnGraph f a) (pointOnGraph f b) =
      pointOnGraph f '' Set.Icc a b := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    let z := u * a + v * b
    have hz : z ∈ Set.Icc a b := by
      constructor
      · calc
          a = (u + v) * a := by rw [huv]; ring
          _ = u * a + v * a := by ring
          _ ≤ u * a + v * b := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hab hv)
      · calc
          u * a + v * b ≤ u * b + v * b :=
            add_le_add (mul_le_mul_of_nonneg_left hab hu) (le_refl _)
          _ = (u + v) * b := by ring
          _ = b := by rw [huv]; ring
    refine ⟨z, hz, ?_⟩
    have hfa := hf a ⟨le_rfl, hab⟩
    have hfb := hf b ⟨hab, le_rfl⟩
    have hfz := hf z hz
    ext i
    fin_cases i
    · simp [pointOnGraph, z]
    · simp only [pointOnGraph, hfz, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hfa, hfb, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, z]
      calc
        m * (u * a + v * b) + c =
            u * (m * a) + v * (m * b) + (u + v) * c := by rw [huv]; ring
        _ = u * (m * a + c) + v * (m * b + c) := by ring
  · rintro ⟨z, hz, rfl⟩
    by_cases hab' : a = b
    · subst b
      have : z = a := by exact le_antisymm hz.2 hz.1
      subst z
      simp
    · have hlt : a < b := lt_of_le_of_ne hab hab'
      let u := (b - z) / (b - a)
      let v := (z - a) / (b - a)
      have hden : 0 < b - a := sub_pos.mpr hlt
      have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hz.2) hden.le
      have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hz.1) hden.le
      have huv : u + v = 1 := by
        dsimp [u, v]
        field_simp
        ring
      refine ⟨u, v, hu, hv, huv, ?_⟩
      have hfa := hf a ⟨le_rfl, hab⟩
      have hfb := hf b ⟨hab, le_rfl⟩
      have hfz := hf z hz
      ext i
      fin_cases i
      · simp [pointOnGraph]
        dsimp [u, v]
        field_simp
        ring
      · simp [pointOnGraph, hfz, hfa, hfb]
        dsimp [u, v]
        field_simp
        ring

/-- A graph segment of slope `m` is orthogonal to each normal annihilating `(1,m)`. -/
theorem inner_pointOnGraph_sub_normalVector_eq_zero {f : ℝ → ℝ}
    {m c a b t : ℝ}
    (hf : Set.EqOn f (fun x ↦ m * x + c) (Set.Icc a b))
    (hab : a ≤ b) (horth : Real.cos t + m * Real.sin t = 0) :
    inner ℝ (pointOnGraph f b - pointOnGraph f a)
      (normalVector (t : Real.Angle)) = 0 := by
  have hfa := hf ⟨le_rfl, hab⟩
  have hfb := hf ⟨hab, le_rfl⟩
  simp [pointOnGraph, normalVector, frame, PiLp.inner_apply, hfa, hfb]
  nlinarith

private theorem graphPolyline_carrier_eq_image_Icc {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) {f : ℝ → ℝ}
    (hpiece : ∀ i : Fin n, ∃ m c : ℝ, ∀ z ∈ Set.Icc (x i.castSucc) (x i.succ),
      f z = m * z + c)
    (hcover : Set.Icc (x 0) (x (Fin.last n)) =
      ⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ)) :
    (graphPolyline n x hx f).carrier =
      pointOnGraph f '' Set.Icc (x 0) (x (Fin.last n)) := by
  rw [hcover, Set.image_iUnion]
  apply Set.iUnion_congr
  intro i
  obtain ⟨m, c, hi⟩ := hpiece i
  exact segment_pointOnGraph_affine (hx i.castSucc_lt_succ).le hi

private theorem iUnion_Icc_fin {n : ℕ} (hn : 0 < n) {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) :
    Set.Icc (x 0) (x (Fin.last n)) =
      ⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        ext z
        constructor
        · intro hz
          exact Set.mem_iUnion.mpr ⟨0, by simpa using hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          fin_cases i
          simpa using hi
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let y : Fin (n + 1) → ℝ := fun i ↦ x i.castSucc
        have hy : StrictMono y := hx.comp Fin.strictMono_castSucc
        have hprefix := ih hnpos hy
        have hprefix' : Set.Icc (x 0) (x (Fin.last n).castSucc) =
            ⋃ i : Fin n, Set.Icc (x i.castSucc.castSucc) (x i.succ.castSucc) := by
          simpa [y] using hprefix
        have hprefix'' : Set.Icc (x 0) (x (Fin.last n).castSucc) =
            Set.iUnion ((fun i : Fin (n + 1) ↦
              Set.Icc (x i.castSucc) (x i.succ)) ∘ Fin.castSucc) := by
          rw [hprefix']
          apply Set.iUnion_congr
          intro i
          congr 2
        rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
        rw [← hprefix'']
        exact (Set.Icc_union_Icc_eq_Icc
          (hx.monotone (Fin.zero_le _))
          (hx (Fin.last n).castSucc_lt_succ).le).symm

private theorem exists_affineValue_eqOn_of_finite_selector {I : Set ℝ}
    (hI : IsPreconnected I) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f I)
    (hsel : ∀ x ∈ I, ∃ c ∈ L, f x = affineValue c x)
    (hsep : ∀ c ∈ L, ∀ d ∈ L, c ≠ d →
      ∀ x ∈ I, affineValue c x ≠ affineValue d x)
    (hIne : I.Nonempty) :
    ∃ c ∈ L, Set.EqOn f (affineValue c) I := by
  classical
  let _ : PreconnectedSpace I := Subtype.preconnectedSpace hI
  obtain ⟨x₀, hx₀⟩ := hIne
  obtain ⟨c₀, hc₀L, hc₀⟩ := hsel x₀ hx₀
  let A : Set I := {x | f x = affineValue c₀ x}
  have hAclosed : IsClosed A := by
    apply isClosed_eq
    · change Continuous (I.domRestrict f)
      exact continuousOn_iff_continuous_domRestrict.mp hf
    · exact (continuous_affineValue c₀).comp continuous_subtype_val
  have hAc : Aᶜ = ⋃ d ∈ L.erase c₀,
      {x : I | f x = affineValue d x} := by
    ext x
    constructor
    · intro hx
      have hxne : f x ≠ affineValue c₀ x := by simpa [A] using hx
      obtain ⟨d, hdL, hd⟩ := hsel x x.2
      have hdc : d ≠ c₀ := by
        intro h
        subst d
        exact hxne hd
      exact Set.mem_iUnion₂.mpr ⟨d, Finset.mem_erase.mpr ⟨hdc, hdL⟩, hd⟩
    · intro hx
      obtain ⟨d, hdL, hd⟩ := Set.mem_iUnion₂.mp hx
      have hdc := (Finset.mem_erase.mp hdL).1
      intro hxc
      exact hsep d (Finset.mem_of_mem_erase hdL) c₀ hc₀L hdc x x.2 (hd.symm.trans hxc)
  have hAcclosed : IsClosed Aᶜ := by
    rw [hAc]
    apply isClosed_biUnion_finset
    intro d hd
    apply isClosed_eq
    · change Continuous (I.domRestrict f)
      exact continuousOn_iff_continuous_domRestrict.mp hf
    · exact (continuous_affineValue d).comp continuous_subtype_val
  have hAclopen : IsClopen A := ⟨hAclosed, isClosed_compl_iff.mp hAcclosed⟩
  have hAnonempty : A.Nonempty := ⟨⟨x₀, hx₀⟩, hc₀⟩
  have hAuniv : A = Set.univ := hAclopen.eq_univ hAnonempty
  refine ⟨c₀, hc₀L, ?_⟩
  intro x hx
  have : (⟨x, hx⟩ : I) ∈ A := hAuniv.symm ▸ Set.mem_univ _
  exact this

private theorem exists_affineValue_eqOn_Icc_of_avoids_crossings {a b : ℝ}
    (hab : a < b) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hsel : ∀ x ∈ Set.Icc a b, ∃ c ∈ L, f x = affineValue c x)
    (hcross : Set.Ioo a b ∩ affineCrossings L = ∅) :
    ∃ c ∈ L, Set.EqOn f (affineValue c) (Set.Icc a b) := by
  classical
  have hf' : ContinuousOn f (Set.Ioo a b) :=
    hf.mono (Set.Ioo_subset_Icc_self)
  have hsel' : ∀ x ∈ Set.Ioo a b, ∃ c ∈ L, f x = affineValue c x :=
    fun x hx ↦ hsel x (Set.Ioo_subset_Icc_self hx)
  have hsep : ∀ c ∈ L, ∀ d ∈ L, c ≠ d →
      ∀ x ∈ Set.Ioo a b, affineValue c x ≠ affineValue d x := by
    intro c hc d hd hcd x hx hEq
    have hxCross : x ∈ affineCrossings L := by
      exact Set.mem_iUnion₂.mpr ⟨c, hc, Set.mem_iUnion₂.mpr
        ⟨d, Finset.mem_erase.mpr ⟨hcd.symm, hd⟩, hEq⟩⟩
    have : x ∈ Set.Ioo a b ∩ affineCrossings L := ⟨hx, hxCross⟩
    simp [hcross] at this
  obtain ⟨c, hcL, hc⟩ := exists_affineValue_eqOn_of_finite_selector
    isPreconnected_Ioo L hf' hsel' hsep (Set.nonempty_Ioo.mpr hab)
  refine ⟨c, hcL, ?_⟩
  exact hc.of_subset_closure hf (continuous_affineValue c).continuousOn
    Set.Ioo_subset_Icc_self (by simp [closure_Ioo hab.ne])

/-- A continuous finite selector of affine functions on a compact interval is a polyline. -/
theorem exists_graphPolyline_of_finite_affine_selector {a b : ℝ}
    (hab : a < b) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hsel : ∀ x ∈ Set.Icc a b, ∃ c ∈ L, f x = affineValue c x) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph f a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph f b ∧
      p.carrier = pointOnGraph f '' Set.Icc a b ∧
      (∀ i : Fin (p.edges + 1),
        p.vertices i = pointOnGraph f (p.vertices i 0)) ∧
      ∀ i : Fin p.edges, ∃ c ∈ L,
        Set.EqOn f (affineValue c)
          (Set.Icc (p.vertices i.castSucc 0) (p.vertices i.succ 0)) := by
  classical
  let C := (finite_affineCrossings L).toFinset.filter (· ∈ Set.Icc a b)
  let B := insert a (insert b C)
  have haB : a ∈ B := by simp [B]
  have hbB : b ∈ B := by simp [B]
  have hBsub : ∀ z ∈ B, z ∈ Set.Icc a b := by
    intro z hz
    simp only [B, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact (Finset.mem_filter.mp hz).2
  have hcard2 : 2 ≤ B.card := by
    have hsub : ({a, b} : Finset ℝ) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haB
      · exact hbB
    have hcard := Finset.card_le_card hsub
    simpa [hab.ne] using hcard
  let n := B.card - 1
  have hnpos : 0 < n := by dsimp [n]; omega
  have hcard : B.card = n + 1 := by dsimp [n]; omega
  let x : Fin (n + 1) → ℝ := B.orderEmbOfFin hcard
  have hx : StrictMono x := (B.orderEmbOfFin hcard).strictMono
  have hxmem (i : Fin (n + 1)) : x i ∈ B := by
    exact B.orderEmbOfFin_mem hcard i
  have hxrange : Set.range x = B := by
    exact B.range_orderEmbOfFin hcard
  have hxzero : x 0 = a := by
    apply le_antisymm
    · have haRange : a ∈ Set.range x := by simpa [hxrange] using haB
      obtain ⟨i, hi⟩ := haRange
      rw [← hi]
      exact hx.monotone (Fin.zero_le i)
    · exact (hBsub _ (hxmem 0)).1
  have hxlast : x (Fin.last n) = b := by
    apply le_antisymm
    · exact (hBsub _ (hxmem (Fin.last n))).2
    · have hbRange : b ∈ Set.range x := by simpa [hxrange] using hbB
      obtain ⟨i, hi⟩ := hbRange
      rw [← hi]
      exact hx.monotone (Fin.le_last i)
  have hnocross (i : Fin n) :
      Set.Ioo (x i.castSucc) (x i.succ) ∩ affineCrossings L = ∅ := by
    ext z
    constructor
    · intro hz
      have hzab : z ∈ Set.Icc a b := by
        rw [← hxzero, ← hxlast]
        exact ⟨(hx.monotone (Fin.zero_le i.castSucc)).trans hz.1.1.le,
          hz.1.2.le.trans (hx.monotone (Fin.le_last i.succ))⟩
      have hzB : z ∈ B := by
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_filter.mpr
        exact ⟨(finite_affineCrossings L).mem_toFinset.mpr hz.2, hzab⟩
      have hzRange : z ∈ Set.range x := by simpa [hxrange] using hzB
      obtain ⟨j, hj⟩ := hzRange
      rw [← hj] at hz
      have hij : i.castSucc < j := hx.lt_iff_lt.mp hz.1.1
      have hji : j < i.succ := hx.lt_iff_lt.mp hz.1.2
      change i.val < j.val at hij
      change j.val < i.val + 1 at hji
      omega
    · intro hz
      exact hz.elim
  have hpiece : ∀ i : Fin n, ∃ c ∈ L,
      Set.EqOn f (affineValue c) (Set.Icc (x i.castSucc) (x i.succ)) := by
    intro i
    exact exists_affineValue_eqOn_Icc_of_avoids_crossings
      (hx i.castSucc_lt_succ) L
      (hf.mono (Set.Icc_subset_Icc
        (by rw [← hxzero]; exact hx.monotone (Fin.zero_le _))
        (by rw [← hxlast]; exact hx.monotone (Fin.le_last _))))
      (fun z hz ↦ hsel z (Set.Icc_subset_Icc
        (by rw [← hxzero]; exact hx.monotone (Fin.zero_le _))
        (by rw [← hxlast]; exact hx.monotone (Fin.le_last _)) hz))
      (hnocross i)
  let p := graphPolyline n x hx f
  refine ⟨p, hnpos, ?_, ?_, ?_, ?_, ?_⟩
  · change pointOnGraph f (x 0) = pointOnGraph f a
    rw [hxzero]
  · change pointOnGraph f (x (Fin.last n)) = pointOnGraph f b
    rw [hxlast]
  · rw [graphPolyline_carrier_eq_image_Icc hx]
    · simp [hxzero, hxlast]
    · intro i
      obtain ⟨c, -, hc⟩ := hpiece i
      exact ⟨c.1, c.2, hc⟩
    · exact iUnion_Icc_fin hnpos hx
  · intro i
    rfl
  · intro i
    change ∃ c ∈ L, Set.EqOn f (affineValue c)
      (Set.Icc (x i.castSucc) (x i.succ))
    exact hpiece i

/-- Injective graph parametrizations preserve disjointness of parameter sets. -/
theorem pointOnGraph_image_disjoint
    (f : ℝ → ℝ) {s t : Set ℝ} (hst : Disjoint s t) :
    Disjoint (pointOnGraph f '' s) (pointOnGraph f '' t) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have heq : x = y := by
    have := congrArg (fun p : Point ↦ p 0) hxy
    simpa [pointOnGraph] using this.symm
  exact Set.disjoint_left.mp hst hx (heq ▸ hy)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Measure
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private lemma fst_mem_Icc_of_mem_segment_mbe8a367 {a b q : Point}
    (hab : a 0 ≤ b 0) (hq : q ∈ segment ℝ a b) : q 0 ∈ Set.Icc (a 0) (b 0) := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  change a 0 + r * (b 0 - a 0) ∈ Set.Icc (a 0) (b 0)
  constructor <;> nlinarith [hr.1, hr.2]

private lemma eq_right_of_mem_segment_of_fst_eq {a b q : Point}
    (hab : a 0 < b 0) (hq : q ∈ segment ℝ a b) (heq : q 0 = b 0) : q = b := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  have hcoord : a 0 + r * (b 0 - a 0) = b 0 := heq
  have hrone : r = 1 := by nlinarith
  simp [hrone]

/-- Distinct increasing polyline segments meet only at a possible common endpoint. -/
lemma XMonotonePolylineData.segment_inter_subset_singleton
    (p : XMonotonePolylineData) {i j : Fin p.edges} (hij : i < j) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ∩
        segment ℝ (p.vertices j.castSucc) (p.vertices j.succ) ⊆
      {p.vertices i.succ} := by
  intro q hq
  have hi := fst_mem_Icc_of_mem_segment_mbe8a367 (p.increasing i.castSucc_lt_succ).le hq.1
  have hj := fst_mem_Icc_of_mem_segment_mbe8a367 (p.increasing j.castSucc_lt_succ).le hq.2
  have hindex : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact hij
  have horder := p.increasing.monotone hindex
  apply Set.mem_singleton_iff.mpr
  exact eq_right_of_mem_segment_of_fst_eq (p.increasing i.castSucc_lt_succ) hq.1
    (le_antisymm hi.2 (horder.trans hj.1))

open MeasureTheory

/-- The segments of an increasing polyline are almost disjoint for length measure. -/
lemma XMonotonePolylineData.pairwise_aedisjoint_segments
    (p : XMonotonePolylineData) :
    Pairwise (fun i j : Fin p.edges ↦ AEDisjoint (Measure.hausdorffMeasure 1)
      (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ))
      (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ))) := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  have hlt (i j : Fin p.edges) (hij : i < j) :
      AEDisjoint (Measure.hausdorffMeasure 1)
        (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ))
        (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ)) := by
    exact measure_mono_null (p.segment_inter_subset_singleton hij) (measure_singleton _)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

/-- A supporting-line slice has the sum of the lengths of its parallel segments. -/
lemma XMonotonePolylineData.hausdorffMeasure_carrier_inter_hyperplane
    (p : XMonotonePolylineData) (n : Point) (c : ℝ)
    (hparallel : ∀ i : Fin p.edges,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 →
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        {q | inner ℝ q n = c}) :
    Measure.hausdorffMeasure 1 (p.carrier ∩ {q | inner ℝ q n = c}) =
      ∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 then
          ENNReal.ofReal (dist (p.vertices i.castSucc) (p.vertices i.succ)) else 0 := by
  classical
  have hd : Pairwise (fun i j : Fin p.edges ↦ AEDisjoint (Measure.hausdorffMeasure 1)
      (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ∩ {q | inner ℝ q n = c})
      (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ) ∩ {q | inner ℝ q n = c})) := by
    intro i j hij
    exact (p.pairwise_aedisjoint_segments hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [XMonotonePolylineData.carrier, Set.iUnion_inter, measure_iUnion₀ hd, tsum_fintype]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0
    · rw [ite_eq_left hi, Set.inter_eq_left.mpr (hparallel i hi), hausdorffMeasure_segment,
        edist_dist]
    · rw [ite_eq_right hi]
      exact EuclideanGeometry.hausdorffMeasure_segment_inter_hyperplane_eq_zero hi
  · intro i
    have hc : IsCompact (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ)) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    exact (hc.isClosed.measurableSet.inter
      (isClosed_eq (by fun_prop) continuous_const).measurableSet).nullMeasurableSet

/-- The real length of a supporting-line slice is the sum of its parallel segment lengths. -/
lemma XMonotonePolylineData.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (p : XMonotonePolylineData) (n : Point) (c : ℝ)
    (hparallel : ∀ i : Fin p.edges,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 →
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        {q | inner ℝ q n = c}) :
    (Measure.hausdorffMeasure 1 (p.carrier ∩ {q | inner ℝ q n = c})).toReal =
      ∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0 := by
  classical
  rw [p.hausdorffMeasure_carrier_inter_hyperplane n c hparallel,
    ENNReal.toReal_sum (by intro i _; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [dist_nonneg]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Projection
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A leftward edge displacement is its length times its oriented tangent. -/
theorem sub_eq_dist_smul_tangentVector {a b : Point} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a 0 < b 0)
    (horth : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) :
    a - b = dist a b • tangentVector (t : Real.Angle) := by
  let r := inner ℝ (b - a) (tangentVector (t : Real.Angle))
  have hvec : r • tangentVector (t : Real.Angle) = b - a := by
    simpa only [horth, zero_smul, zero_add] using
      inner_normalVector_smul_add_inner_tangentVector_smul (b - a) (t : Real.Angle)
  have hcoord : -(r * Real.sin t) = b 0 - a 0 := by
    have h := congrArg (fun p : Point ↦ p 0) hvec
    simpa [tangentVector, frame] using h
  have hdist := dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero ht hab horth
  have hr : r = -dist a b := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    nlinarith
  rw [hr, neg_smul] at hvec
  simpa only [neg_neg, neg_sub] using (congrArg Neg.neg hvec).symm

/-- Every point of a polyline satisfies the bound by positive projected edge increments. -/
theorem XMonotonePolylineData.inner_le_endpoint_add_sum_pos
    (p : XMonotonePolylineData) (u : Point) {q : Point} (hq : q ∈ p.carrier) :
    inner ℝ q u ≤ inner ℝ (p.vertices (Fin.last p.edges)) u +
      ∑ i : Fin p.edges, max (inner ℝ (p.vertices i.castSucc - p.vertices i.succ) u) 0 := by
  have hvertex (i : Fin (p.edges + 1)) :=
    Fin.apply_le_last_add_sum_max_sub (fun i ↦ inner ℝ (p.vertices i) u) i
  simp only [← inner_sub_left] at hvertex
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hqi
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h₁ := mul_le_mul_of_nonneg_left (hvertex i.castSucc) ha
  have h₂ := mul_le_mul_of_nonneg_left (hvertex i.succ) hb
  have h := add_le_add h₁ h₂
  rwa [← add_mul, hab, one_mul] at h

/-- Grouping edge lengths by their unique normal preserves every weighted sum. -/
theorem XMonotonePolylineData.sum_normal_lengths_mul
    (p : XMonotonePolylineData) (D : Finset ℝ) (g : ℝ → ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (t : Fin p.edges → ℝ) (ht : ∀ i, t i ∈ D)
    (horth : ∀ i, inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t i : Real.Angle)) = 0) :
    ∑ u ∈ D, (∑ i : Fin p.edges,
      if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (u : Real.Angle)) = 0 then
        dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * g u =
      ∑ i : Fin p.edges, dist (p.vertices i.castSucc) (p.vertices i.succ) * g (t i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (t i)]
  · rw [ite_eq_left (horth i)]
  · intro u hu hut
    have hne : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (u : Real.Angle)) ≠ 0 := by
      intro hzero
      exact hut (eq_of_inner_sub_normalVector_eq_zero (hD u hu) (hD _ (ht i))
        (p.increasing i.castSucc_lt_succ) hzero (horth i))
    simp [hne]
  · exact fun hnot ↦ (hnot (ht i)).elim

/-- Positive normal projections bound every point of a polyline by its right endpoint. -/
theorem XMonotonePolylineData.inner_le_endpoint_add_sum_normal_lengths
    (p : XMonotonePolylineData) (D : Finset ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (hlabels : ∀ i : Fin p.edges, ∃ t ∈ D,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0)
    (s : ℝ) {q : Point} (hq : q ∈ p.carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ (p.vertices (Fin.last p.edges)) (normalVector (s : Real.Angle)) +
      ∑ u ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (u : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) *
        max (Real.sin (s - u)) 0 := by
  classical
  choose t ht horth using hlabels
  rw [p.sum_normal_lengths_mul D (fun u ↦ max (Real.sin (s - u)) 0) hD t ht horth]
  have h := p.inner_le_endpoint_add_sum_pos (normalVector (s : Real.Angle)) hq
  convert h using 2
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_eq_dist_smul_tangentVector (hD _ (ht i))
    (p.increasing i.castSucc_lt_succ) (horth i), real_inner_smul_left,
    inner_tangentVector_normalVector_real, mul_max_of_nonneg _ _ dist_nonneg, mul_zero]

end MovingSofa

end

end

end
