/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Owners
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic

/-!
Lebesgue area in triangular coordinates. Physical area is sqrt(3)/2 times
this measure, so dividing physical area by sqrt(3)/4 amounts to multiplying
`volume.toReal` by two. The standard-simplex integration and affine image
argument are adapted from SevenTriangles/Geometry/Area.lean, pinned commit
b17ca52a395519f43fc15f83fb49a5dd69996225. The ten-owner budget explicitly keeps
the corner triangles' contributions inside H.
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
namespace ConwaySoifer

instance instIsAddHaarMeasure_volume_point : (volume : Measure Point).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem EquilateralTriangle.measurableSet_carrier (T : EquilateralTriangle) :
    MeasurableSet T.carrier := T.isClosed_carrier.measurableSet

theorem isClosed_hexagon : IsClosed hexagon := by
  simp only [hexagon, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem measurableSet_hexagon : MeasurableSet hexagon := isClosed_hexagon.measurableSet

/-- The filled standard simplex with nonnegative coordinates summing to at most one. -/
def stdTriangle : Set Point := {st | 0 ≤ st.1 ∧ 0 ≤ st.2 ∧ st.1+st.2 ≤ 1}

theorem isClosed_stdTriangle : IsClosed stdTriangle := by
  simp only [stdTriangle, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem convex_stdTriangle : Convex ℝ stdTriangle := by
  intro x hx y hy a b ha hb hab
  simp only [stdTriangle, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem stdTriangle_eq_convexHull :
    stdTriangle = convexHull ℝ ({(0, 0), (1, 0), (0, 1)} : Set Point) := by
  apply Set.Subset.antisymm
  · intro st hst
    obtain ⟨h1, h2, h3⟩ := hst
    have hconv := convex_convexHull ℝ ({(0, 0), (1, 0), (0, 1)} : Set Point)
    have h := convex_three_mem hconv
      (subset_convexHull ℝ _ (by simp : (0, 0) ∈ ({(0, 0), (1, 0), (0, 1)} : Set Point)))
      (subset_convexHull ℝ _ (by simp : (1, 0) ∈ ({(0, 0), (1, 0), (0, 1)} : Set Point)))
      (subset_convexHull ℝ _ (by simp : (0, 1) ∈ ({(0, 0), (1, 0), (0, 1)} : Set Point))) h1 h2 h3
    simpa using h
  · apply convexHull_min _ convex_stdTriangle
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> simp [stdTriangle]

theorem stdTriangle_section (x : ℝ) :
    volume (Prod.mk x ⁻¹' stdTriangle) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun x => ENNReal.ofReal (1-x)) x := by
  by_cases hx : 0 ≤ x
  · have he : Prod.mk x ⁻¹' stdTriangle = Set.Icc 0 (1-x) := by
      ext y
      simp only [Set.mem_preimage, stdTriangle, Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · rintro ⟨_, h2, h3⟩; exact ⟨h2, by linarith⟩
      · rintro ⟨h2, h3⟩; exact ⟨hx, h2, by linarith⟩
    rw [he, Real.volume_Icc]
    by_cases hx1 : x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ Set.Icc (0 : ℝ) 1 from ⟨hx, hx1⟩)]; ring_nf
    · rw [Set.indicator_of_notMem (fun h => hx1 h.2), ENNReal.ofReal_of_nonpos (by linarith)]
  · have he : Prod.mk x ⁻¹' stdTriangle = ∅ := by
      ext y
      simp only [Set.mem_preimage, stdTriangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
      rintro ⟨h1, _, _⟩; exact hx h1
    rw [he, measure_empty, Set.indicator_of_notMem (fun h => hx h.1)]

theorem volume_stdTriangle : volume stdTriangle = ENNReal.ofReal (1/2) := by
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

/-- The linear map with specified edge vectors as its columns. -/
def areaLinMap (u v : Point) : Point →ₗ[ℝ] Point :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight v

theorem areaLinMap_apply (u v st : Point) : areaLinMap u v st = st.1 • u + st.2 • v := by
  simp [areaLinMap]

theorem det_areaLinMap (u v : Point) : LinearMap.det (areaLinMap u v) = cross u v := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, areaLinMap_apply, cross]
  ring

theorem volume_image_areaLinMap (u v : Point) (s : Set Point) :
    volume (areaLinMap u v '' s) = ENNReal.ofReal |cross u v| * volume s := by
  rw [Measure.addHaar_image_linearMap, det_areaLinMap]

theorem volume_image_add_left (p : Point) (s : Set Point) :
    volume ((fun x => p+x) '' s) = volume s := by
  rw [Set.image_add_left, measure_preimage_add]

/-- The affine map from the standard simplex to a triangle with specified base and edges. -/
def areaTriMap (p u v : Point) : Point →ᵃ[ℝ] Point where
  toFun st := p + areaLinMap u v st
  linear := areaLinMap u v
  map_vadd' := by
    intro a b
    simp only [vadd_eq_add, map_add]
    abel

theorem areaTriMap_apply (p u v st : Point) : areaTriMap p u v st = p + areaLinMap u v st := rfl

theorem areaTriMap_image (p u v : Point) (s : Set Point) :
    areaTriMap p u v '' s = (fun x => p+x) '' (areaLinMap u v '' s) := by
  rw [Set.image_image]
  rfl

theorem convexHull_triple_eq_image (p q r : Point) :
    convexHull ℝ {p, q, r} = areaTriMap p (q-p) (r-p) '' stdTriangle := by
  rw [stdTriangle_eq_convexHull, AffineMap.image_convexHull]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton, areaTriMap_apply, areaLinMap_apply]
  simp

theorem volume_triangle (p q r : Point) :
    volume (convexHull ℝ {p, q, r}) = ENNReal.ofReal (|cross (q-p) (r-p)|/2) := by
  rw [convexHull_triple_eq_image, areaTriMap_image, volume_image_add_left,
    volume_image_areaLinMap, volume_stdTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

theorem EquilateralTriangle.range_vertices (T : EquilateralTriangle) :
    Set.range T.vertices = {T.vertices 0, T.vertices 1, T.vertices 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem EquilateralTriangle.abs_det (T : EquilateralTriangle) :
    |cross (T.vertices 1-T.vertices 0) (T.vertices 2-T.vertices 0)| = T.side ^ 2 := by
  have h := T.det_sq
  dsimp [triangleDet] at h
  nlinarith [sq_abs (cross (T.vertices 1-T.vertices 0) (T.vertices 2-T.vertices 0)),
    abs_nonneg (cross (T.vertices 1-T.vertices 0) (T.vertices 2-T.vertices 0)), sq_nonneg T.side]

theorem EquilateralTriangle.volume_carrier (T : EquilateralTriangle) :
    volume T.carrier = ENNReal.ofReal (T.side ^ 2/2) := by
  rw [EquilateralTriangle.carrier, T.range_vertices, volume_triangle, T.abs_det]

theorem EquilateralTriangle.volume_carrier_lt_top (T : EquilateralTriangle) :
    volume T.carrier < ⊤ := by
  rw [T.volume_carrier]
  exact ENNReal.ofReal_lt_top

theorem hexagon_section (b : ℝ) :
    volume ((fun a => (a, b)) ⁻¹' hexagon) =
      Set.indicator (Set.Icc (-1 : ℝ) 1) (fun b => ENNReal.ofReal (2-|b|)) b := by
  by_cases hb : |b| ≤ 1
  · have he : (fun a => (a, b)) ⁻¹' hexagon =
        Set.Icc (-1-b/2+|b|/2) (1-b/2-|b|/2) := by
      ext a
      simp only [Set.mem_preimage, hexagon, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
      rcases abs_cases b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> constructor
      · rintro ⟨⟨a1, a2⟩, _, ⟨c1, c2⟩⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a1, a2⟩; exact ⟨⟨by linarith, by linarith⟩, abs_le.mp hb, ⟨by linarith, by
          linarith⟩⟩
      · rintro ⟨⟨a1, a2⟩, _, ⟨c1, c2⟩⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a1, a2⟩; exact ⟨⟨by linarith, by linarith⟩, abs_le.mp hb, ⟨by linarith, by
          linarith⟩⟩
    rw [he, Real.volume_Icc, Set.indicator_of_mem (show b ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hb)]
    ring_nf
  · have he : (fun a => (a, b)) ⁻¹' hexagon = ∅ := by
      ext a
      simp only [Set.mem_preimage, hexagon, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, h2, _⟩; exact hb h2
    rw [he, measure_empty, Set.indicator_of_notMem (fun h : b ∈ Set.Icc (-1 : ℝ) 1 => hb (abs_le.mpr
        h))]

theorem integral_two_sub_abs : ∫ z in (-1 : ℝ)..1, (2-|z|) = 3 := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun z : ℝ => 2-|z|) volume a b :=
    fun a b => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-1) 0) (hI 0 1)]
  have h1 : ∫ z in (-1 : ℝ)..0, (2-|z|) = ∫ z in (-1 : ℝ)..0, (2-(-z)) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp [abs_of_nonpos hz.2]
  have h2 : ∫ z in (0 : ℝ)..1, (2-|z|) = ∫ z in (0 : ℝ)..1, (2-z) := by
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

theorem volume_hexagon : volume hexagon = 3 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm measurableSet_hexagon]
  simp_rw [hexagon_section]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun z hz => by
        simp only [Pi.zero_apply]; linarith [abs_le.mpr hz])),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_two_sub_abs]
  norm_num

theorem sum_ten_decompose (f : Fin 10 → ℝ) :
    ∑ i, f i = f 0 + (∑ i : Fin 6, f (sideIndex i)) + ∑ j : Fin 3, f (cornerIndex j) := by
  simp [Fin.sum_univ_succ, sideIndex, cornerIndex]; ring

namespace AnchoredCover
variable {r : ℝ}

/-- Twice the area of a side owner outside the central hexagon. -/
def outside (C : AnchoredCover r) (i : Fin 6) : ℝ :=
  2 * (volume ((C.sideOwner i).carrier \ hexagon)).toReal

/-- Twice the area of a corner owner inside the central hexagon. -/
def cornerHelp (C : AnchoredCover r) (j : Fin 3) : ℝ :=
  2 * (volume ((C.cornerOwner j).carrier ∩ hexagon)).toReal

/-- This inequality follows from actual Lebesgue measure of the full cover.
The corner contribution is retained; no non-overlap assumption is made. -/
theorem area_budget (C : AnchoredCover r) :
    ∑ i : Fin 6, C.outside i ≤ 7*r ^ 2-6 + ∑ j : Fin 3, C.cornerHelp j := by
  let I : Fin 10 → ℝ := fun i => (volume ((C.triangles i).carrier ∩ hexagon)).toReal
  let O : Fin 10 → ℝ := fun i => (volume ((C.triangles i).carrier \ hexagon)).toReal
  have hfinI : ∀ i, volume ((C.triangles i).carrier ∩ hexagon) ≠ ⊤ := fun i =>
    ((measure_mono Set.inter_subset_left).trans_lt (C.triangles i).volume_carrier_lt_top).ne
  have hfinO : ∀ i, volume ((C.triangles i).carrier \ hexagon) ≠ ⊤ := fun i =>
    ((measure_mono Set.sdiff_subset).trans_lt (C.triangles i).volume_carrier_lt_top).ne
  have hsub : hexagon ⊆ ⋃ i, ((C.triangles i).carrier ∩ hexagon) := by
    intro p hp
    obtain ⟨i, hi⟩ := C.covers p (hexagon_subset_target hp)
    exact Set.mem_iUnion.mpr ⟨i, hi, hp⟩
  have h3 : (3:ENNReal) ≤ ∑ i, volume ((C.triangles i).carrier ∩ hexagon) :=
    volume_hexagon ▸ (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
  have h3r : (3 : ℝ) ≤ ∑ i, I i := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => hfinI i) h3
    rw [ENNReal.toReal_sum fun i _ => hfinI i] at h
    simpa [I] using h
  have hsplit : ∀ i, I i + O i = r ^ 2/2 := by
    intro i
    dsimp [I, O]
    rw [← ENNReal.toReal_add (hfinI i) (hfinO i),
      measure_inter_add_sdiff _ measurableSet_hexagon, (C.triangles i).volume_carrier, C.side_eq,
      ENNReal.toReal_ofReal (by positivity)]
  have hcentre : I 0 ≤ r ^ 2/2 := by
    have h0 := hsplit 0
    have hn : 0 ≤ O 0 := ENNReal.toReal_nonneg
    linarith
  have hsides := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hsplit
      (sideIndex i))
  rw [Finset.sum_add_distrib] at hsides
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsides
  rw [sum_ten_decompose] at h3r
  have hbudget : (∑ i : Fin 6, O (sideIndex i)) ≤
      7*r ^ 2/2-3 + ∑ j : Fin 3, I (cornerIndex j) := by
    norm_num at hsides
    linarith
  change (∑ i : Fin 6, 2 * O (sideIndex i)) ≤
    7*r ^ 2-6 + ∑ j : Fin 3, 2 * I (cornerIndex j)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  linarith

end AnchoredCover
end ConwaySoifer
