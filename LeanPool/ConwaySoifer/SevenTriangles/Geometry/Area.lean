/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Support
public import LeanPool.ConwaySoifer.SevenTriangles.Geometry.Diameter
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Areas in skew coordinates

`Point = ℝ × ℝ` carries the product Lebesgue measure `volume`.  Because `(x, z)` denotes the
Euclidean point `(x, (√3/2) z)`, the physical area of a set is `(√3/2) · volume`.  Hence a filled
equilateral triangle of side `s` has `volume = s ^ 2 / 2` and the unit hexagon has `volume = 3`.

The area budget is the only place where measure theory enters the proof.

Implementation notes.
* `volume` on `ℝ × ℝ` is the product measure `volume.prod volume`, which is an additive Haar
  measure; we register that instance for `Point` explicitly.
* A triangle `convexHull {p, q, r}` is the image of the standard triangle
  `stdTriangle = {(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}` under the affine map
  `(s, t) ↦ p + s • (q - p) + t • (r - p)`; the linear part has determinant
  `coordDet (q - p) (r - p)` and `stdTriangle` has volume `1/2` (Fubini).
* The hexagon volume is computed by Fubini in the second coordinate: the horizontal section at
  height `z ∈ [-1, 1]` is the interval `[-1 + |z|/2, 1 - |z|/2]` of length `2 - |z|`.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace ConwaySoifer.SevenTriangles

/-- The product Lebesgue measure on skew coordinates is an additive Haar measure. -/
instance instIsAddHaarMeasure_volume_point : (volume : Measure Point).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem isCompact_carrier (T : EquilateralTriangle) : IsCompact T.carrier :=
  (Set.finite_range T.vertices).isCompact_convexHull ℝ

theorem isClosed_carrier (T : EquilateralTriangle) : IsClosed T.carrier :=
  (isCompact_carrier T).isClosed

theorem measurableSet_carrier (T : EquilateralTriangle) : MeasurableSet T.carrier :=
  (isClosed_carrier T).measurableSet

theorem isClosed_unitHexagon : IsClosed unitHexagon := by
  simp only [unitHexagon, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem measurableSet_unitHexagon : MeasurableSet unitHexagon :=
  isClosed_unitHexagon.measurableSet

/-! ### The standard triangle and its volume -/

/-- The standard triangle `{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`. -/
def stdTriangle : Set Point := {st | 0 ≤ st.1 ∧ 0 ≤ st.2 ∧ st.1 + st.2 ≤ 1}

theorem isClosed_stdTriangle : IsClosed stdTriangle := by
  simp only [stdTriangle, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem convex_stdTriangle : Convex ℝ stdTriangle := by
  intro x hx y hy a b ha hb hab
  simp only [stdTriangle, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem stdTriangle_eq_convexHull :
    stdTriangle = convexHull ℝ {((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} := by
  apply Set.Subset.antisymm
  · intro st hst
    obtain ⟨h1, h2, h3⟩ := hst
    have hconv := convex_convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set Point)
    have := hconv.sum_mem (t := Finset.univ) (w := ![1 - st.1 - st.2, st.1, st.2])
      (z := ![(0, 0), (1, 0), (0, 1)]) ?_ ?_ ?_
    · convert this using 1
      simp [Fin.sum_univ_three]
    · intro i _
      fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_three]; ring
    · intro i _
      fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
      · exact subset_convexHull ℝ _ (by simp)
      · exact subset_convexHull ℝ _ (by simp)
      · exact subset_convexHull ℝ _ (by simp)
  · apply convexHull_min _ convex_stdTriangle
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> simp [stdTriangle]

theorem stdTriangle_section (x : ℝ) :
    volume (Prod.mk x ⁻¹' stdTriangle) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun x => ENNReal.ofReal (1 - x)) x := by
  by_cases hx : 0 ≤ x
  · have : Prod.mk x ⁻¹' stdTriangle = Set.Icc 0 (1 - x) := by
      ext y
      simp only [Set.mem_preimage, stdTriangle, Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · rintro ⟨_, h2, h3⟩; exact ⟨h2, by linarith⟩
      · rintro ⟨h2, h3⟩; exact ⟨hx, h2, by linarith⟩
    rw [this, Real.volume_Icc]
    by_cases hx1 : x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ Set.Icc (0 : ℝ) 1 from ⟨hx, hx1⟩)]; ring_nf
    · rw [Set.indicator_of_notMem (fun h => hx1 h.2), ENNReal.ofReal_of_nonpos (by linarith)]
  · have : Prod.mk x ⁻¹' stdTriangle = ∅ := by
      ext y
      simp only [Set.mem_preimage, stdTriangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, _, _⟩; exact hx h1
    rw [this, measure_empty, Set.indicator_of_notMem (fun h => hx h.1)]

theorem volume_stdTriangle : volume stdTriangle = ENNReal.ofReal (1 / 2) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply isClosed_stdTriangle.measurableSet]
  simp_rw [stdTriangle_section]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => by
        simp only [Pi.zero_apply]; linarith [hx.2])),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_id]
  congr 1
  norm_num

/-! ### Linear and affine images -/

/-- The linear map `(s, t) ↦ s • u + t • v`. -/
def linMap (u v : Point) : Point →ₗ[ℝ] Point :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight v

theorem linMap_apply (u v : Point) (st : Point) : linMap u v st = st.1 • u + st.2 • v := by
  simp [linMap]

/-- The determinant of `linMap u v` is the coordinate determinant `coordDet u v`. -/
theorem det_linMap (u v : Point) : LinearMap.det (linMap u v) = coordDet u v := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, linMap_apply, coordDet]
  ring

theorem volume_image_linMap (u v : Point) (s : Set Point) :
    volume (linMap u v '' s) = ENNReal.ofReal |coordDet u v| * volume s := by
  rw [Measure.addHaar_image_linearMap, det_linMap]

theorem volume_image_add_left (p : Point) (s : Set Point) :
    volume ((fun x => p + x) '' s) = volume s := by
  rw [Set.image_add_left, measure_preimage_add]

/-- The affine map `(s, t) ↦ p + s • u + t • v`. -/
def triMap (p u v : Point) : Point →ᵃ[ℝ] Point where
  toFun st := p + linMap u v st
  linear := linMap u v
  map_vadd' := by
    intro a b
    simp only [vadd_eq_add, map_add]
    abel

theorem triMap_apply (p u v st : Point) : triMap p u v st = p + linMap u v st := rfl

theorem triMap_image (p u v : Point) (s : Set Point) :
    triMap p u v '' s = (fun x => p + x) '' (linMap u v '' s) := by
  rw [Set.image_image]
  rfl

theorem convexHull_triple_eq_image (p q r : Point) :
    convexHull ℝ {p, q, r} = triMap p (q - p) (r - p) '' stdTriangle := by
  rw [stdTriangle_eq_convexHull, AffineMap.image_convexHull]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton, triMap_apply, linMap_apply]
  simp

/-- Area of a (possibly degenerate) triangle given by three vertices, in skew coordinates. -/
theorem volume_triangle (p q r : Point) :
    volume (convexHull ℝ {p, q, r}) = ENNReal.ofReal (|coordDet (q - p) (r - p)| / 2) := by
  rw [convexHull_triple_eq_image, triMap_image, volume_image_add_left, volume_image_linMap,
    volume_stdTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-! ### Equilateral triangles -/

theorem sqDist_sub_zero (a b : Point) : sqDist (a - b) (0, 0) = sqDist a b := by
  simp [sqDist]

theorem EquilateralTriangle.range_vertices (T : EquilateralTriangle) :
    Set.range T.vertices = {T.vertices 0, T.vertices 1, T.vertices 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem EquilateralTriangle.abs_coordDet (T : EquilateralTriangle) :
    |coordDet (T.vertices 1 - T.vertices 0) (T.vertices 2 - T.vertices 0)| = T.side ^ 2 := by
  have h10 : sqDist (T.vertices 1 - T.vertices 0) (0, 0) = T.side ^ 2 := by
    rw [sqDist_sub_zero]
    exact T.equilateral 1 0 (by decide)
  rcases T.thirdVertex_orientation with h | h
  · rw [h, coordDet_rotate60, h10, abs_of_nonneg (sq_nonneg _)]
  · rw [h, coordDet_rotateNeg60, h10, abs_neg, abs_of_nonneg (sq_nonneg _)]

theorem EquilateralTriangle.volume_carrier (T : EquilateralTriangle) :
    volume T.carrier = ENNReal.ofReal (T.side ^ 2 / 2) := by
  rw [EquilateralTriangle.carrier, T.range_vertices, volume_triangle, T.abs_coordDet]

theorem EquilateralTriangle.volume_carrier_lt_top (T : EquilateralTriangle) :
    volume T.carrier < ⊤ := by
  rw [T.volume_carrier]
  exact ENNReal.ofReal_lt_top

/-! ### The unit hexagon -/

theorem unitHexagon_section (z : ℝ) :
    volume ((fun x => (x, z)) ⁻¹' unitHexagon) =
      Set.indicator (Set.Icc (-1 : ℝ) 1) (fun z => ENNReal.ofReal (2 - |z|)) z := by
  by_cases hz : |z| ≤ 1
  · have : (fun x => (x, z)) ⁻¹' unitHexagon = Set.Icc (-1 + |z| / 2) (1 - |z| / 2) := by
      ext x
      simp only [Set.mem_preimage, unitHexagon, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
      rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        constructor
      · rintro ⟨_, ⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a, b⟩; exact ⟨abs_le.1 hz, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨_, ⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a, b⟩; exact ⟨abs_le.1 hz, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [this, Real.volume_Icc, Set.indicator_of_mem (show z ∈ Set.Icc (-1 : ℝ) 1 from abs_le.1 hz)]
    ring_nf
  · have : (fun x => (x, z)) ⁻¹' unitHexagon = ∅ := by
      ext x
      simp only [Set.mem_preimage, unitHexagon, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, _, _⟩; exact hz h1
    rw [this, measure_empty, Set.indicator_of_notMem (fun h : z ∈ Set.Icc (-1 : ℝ) 1 => hz (abs_le.2
        h))]

theorem integral_two_sub_abs : ∫ z in (-1 : ℝ)..1, (2 - |z|) = 3 := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun z : ℝ => 2 - |z|) volume a b :=
    fun a b => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-1) 0) (hI 0 1)]
  have h1 : ∫ z in (-1 : ℝ)..0, (2 - |z|) = ∫ z in (-1 : ℝ)..0, (2 - (-z)) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp [abs_of_nonpos hz.2]
  have h2 : ∫ z in (0 : ℝ)..1, (2 - |z|) = ∫ z in (0 : ℝ)..1, (2 - z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp [abs_of_nonneg hz.1]
  rw [h1, h2, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_neg, integral_id,
    integral_id]
  simp
  norm_num

theorem volume_unitHexagon : volume unitHexagon = 3 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm measurableSet_unitHexagon]
  simp_rw [unitHexagon_section]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun z hz => by
        simp only [Pi.zero_apply]; linarith [abs_le.2 hz])),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_two_sub_abs]
  norm_num

/-! ### The area budget -/

/-- The area budget: the parts of the seven triangles outside the hexagon cannot exceed the total
area surplus `7 r ^ 2 / 2 - 3` (skew units; multiply by `√3/2` for physical area). -/
theorem area_budget (r : ℝ) (T : Configuration) (hs : ∀ i, (T i).side ≤ r)
    (hc : CoversUnitHexagon T) :
    ∑ j : Fin 7, (volume ((T j).carrier \ unitHexagon)).toReal ≤ 7 * r ^ 2 / 2 - 3 := by
  -- the hexagon is covered by the pieces `carrier ∩ hexagon`
  have hsub : unitHexagon ⊆ ⋃ j, ((T j).carrier ∩ unitHexagon) := by
    intro p hp
    obtain ⟨i, hi⟩ := hc p hp
    exact Set.mem_iUnion.2 ⟨i, hi, hp⟩
  have h3 : (3 : ENNReal) ≤ ∑ j, volume ((T j).carrier ∩ unitHexagon) :=
    volume_unitHexagon ▸ (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
  -- finiteness of all the pieces
  have hfinA : ∀ j, volume ((T j).carrier ∩ unitHexagon) ≠ ⊤ := fun j =>
    ((measure_mono Set.inter_subset_left).trans_lt (T j).volume_carrier_lt_top).ne
  have hfinB : ∀ j, volume ((T j).carrier \ unitHexagon) ≠ ⊤ := fun j =>
    ((measure_mono Set.sdiff_subset).trans_lt (T j).volume_carrier_lt_top).ne
  -- the real-valued pieces
  have hsplit : ∀ j, (volume ((T j).carrier ∩ unitHexagon)).toReal +
      (volume ((T j).carrier \ unitHexagon)).toReal ≤ r ^ 2 / 2 := by
    intro j
    rw [← ENNReal.toReal_add (hfinA j) (hfinB j),
      measure_inter_add_sdiff _ measurableSet_unitHexagon, (T j).volume_carrier,
      ENNReal.toReal_ofReal (by positivity)]
    have := (T j).side_pos
    have := hs j
    nlinarith
  have h3' : (3 : ℝ) ≤ ∑ j, (volume ((T j).carrier ∩ unitHexagon)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => hfinA j) h3
    rw [ENNReal.toReal_sum fun j _ => hfinA j] at this
    simpa using this
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hsplit j
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

end ConwaySoifer.SevenTriangles
