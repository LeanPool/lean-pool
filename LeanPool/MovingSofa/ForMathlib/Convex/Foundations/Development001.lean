/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Sequences

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Convex.Body.BoundaryMeasure`.
* `ForMathlib.Convex.Body.Hausdorff`.
* `ForMathlib.Convex.Collinear`.
* `ForMathlib.Convex.Body.Segment`.
* `ForMathlib.Convex.Function`.
* `ForMathlib.Convex.Hausdorff`.
* `ForMathlib.Convex.Support`.
* `ForMathlib.Convex.Translation`.
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
# For Mathlib / Convex / Body / Boundary Measure
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Topology

namespace ConvexBody

private abbrev Plane_m58ecd66 := EuclideanSpace ℝ (Fin 2)

private def unitCircleParam (t : ℝ) : Plane_m58ecd66 :=
  WithLp.toLp 2 (![Real.cos t, Real.sin t] : Fin 2 → ℝ)

private theorem lipschitzWith_unitCircleParam :
    LipschitzWith 2 unitCircleParam := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [dist_eq_norm]
  rw [Real.dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [unitCircleParam, PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : |Real.cos x - Real.cos y| ≤ |x - y| := by
    exact Real.abs_cos_sub_cos_le x y
  have hs : |Real.sin x - Real.sin y| ≤ |x - y| := by
    exact Real.abs_sin_sub_sin_le x y
  have hxy : 0 ≤ |x - y| := abs_nonneg _
  have hc_sq := sq_le_sq₀ (abs_nonneg _) hxy |>.mpr hc
  have hs_sq := sq_le_sq₀ (abs_nonneg _) hxy |>.mpr hs
  norm_num
  nlinarith [sq_abs (Real.cos x - Real.cos y), sq_abs (Real.sin x - Real.sin y)]

private theorem hausdorffMeasure_one_sphere_lt_top :
    Measure.hausdorffMeasure 1 (Metric.sphere (0 : Plane_m58ecd66) 1) < ⊤ := by
  have hsphere : Metric.sphere (0 : Plane_m58ecd66) 1 ⊆
      unitCircleParam '' Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    have hnorm : ‖p‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hp
    let z : ℂ := ⟨p 0, p 1⟩
    have hzNorm : ‖z‖ = 1 := by
      rw [Complex.norm_def, show Complex.normSq z = ‖p‖ ^ 2 by
        rw [EuclideanSpace.norm_sq_eq]
        simp [z, Complex.normSq_apply, Fin.sum_univ_two, pow_two, Real.norm_eq_abs]]
      simp [hnorm]
    have hz : z ≠ 0 := by
      intro hz
      simp [hz] at hzNorm
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    ext i
    fin_cases i
    · simpa [unitCircleParam, z, hzNorm] using Complex.cos_arg hz
    · simpa [unitCircleParam, z, hzNorm] using Complex.sin_arg z
  calc
    Measure.hausdorffMeasure 1 (Metric.sphere (0 : Plane_m58ecd66) 1) ≤
        Measure.hausdorffMeasure 1 (unitCircleParam '' Set.Icc (-Real.pi) Real.pi) :=
      measure_mono hsphere
    _ ≤ ((2 : NNReal) : ENNReal) ^ (1 : ℝ) *
        Measure.hausdorffMeasure 1 (Set.Icc (-Real.pi) Real.pi) :=
      lipschitzWith_unitCircleParam.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      finiteness

private theorem image_gaugeRescale_unitSphere_eq_frontier {s : Set Plane_m58ecd66}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane_m58ecd66)) (hbounded : Bornology.IsBounded s)
    (hclosed : IsClosed s) :
    gaugeRescale (Metric.ball 0 1) s '' Metric.sphere 0 1 = frontier s := by
  have hvnb : Bornology.IsVonNBounded ℝ s :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hbounded
  let h := gaugeRescaleHomeomorph (Metric.ball (0 : Plane_m58ecd66) 1) s
    (convex_ball 0 1) (Metric.ball_mem_nhds 0 zero_lt_one)
    (NormedSpace.isVonNBounded_ball ℝ Plane_m58ecd66 1) hconv h₀ hvnb
  change h '' Metric.sphere 0 1 = frontier s
  rw [← frontier_ball, ← closure_sdiff_interior, Set.image_sdiff h.injective]
  · rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
    rw [hclosed.closure_eq]
    simpa [hclosed.closure_eq] using closure_sdiff_interior s
  · norm_num

private theorem exists_lipschitzOnWith_gaugeRescale_unitSphere {s : Set Plane_m58ecd66}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane_m58ecd66)) (hbounded : Bornology.IsBounded s) :
    ∃ C, LipschitzOnWith C (gaugeRescale (Metric.ball 0 1) s) (Metric.sphere 0 1) := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp h₀
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  let R : ℝ := |B| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hsR : s ⊆ Metric.closedBall (0 : Plane_m58ecd66) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hB x hx).trans (by dsimp [R]; linarith [le_abs_self B])
  have habs : Absorbent ℝ s := absorbent_nhds_zero h₀
  let rn : NNReal := ⟨r, hr.le⟩
  have hg : LipschitzWith rn⁻¹ (gauge s) := hconv.lipschitzWith_gauge hr hrs
  let C : NNReal := ⟨R + (rn⁻¹ : ℝ) * R ^ 2, by positivity⟩
  refine ⟨C, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hnx : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hny : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  have hgx : 1 / R ≤ gauge s x := by
    simpa [hnx] using (le_gauge_of_subset_closedBall habs hR.le hsR : ‖x‖ / R ≤ gauge s x)
  have hgy : 1 / R ≤ gauge s y := by
    simpa [hny] using (le_gauge_of_subset_closedBall habs hR.le hsR : ‖y‖ / R ≤ gauge s y)
  have hgxpos : 0 < gauge s x := (div_pos one_pos hR).trans_le hgx
  have hgypos : 0 < gauge s y := (div_pos one_pos hR).trans_le hgy
  have hinvx : (gauge s x)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hgxpos hR]
    simpa [div_eq_inv_mul] using hgx
  have hinvy : (gauge s y)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hgypos hR]
    simpa [div_eq_inv_mul] using hgy
  have hginv : dist (gauge s x)⁻¹ (gauge s y)⁻¹ ≤
      (rn⁻¹ : ℝ) * R ^ 2 * dist x y := by
    rw [dist_inv_inv₀ hgxpos.ne' hgypos.ne']
    have hdist := hg.dist_le_mul x y
    have hprod : 1 / R ^ 2 ≤ ‖gauge s x‖ * ‖gauge s y‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgxpos, abs_of_pos hgypos]
      calc
        1 / R ^ 2 = (1 / R) * (1 / R) := by ring_nf
        _ ≤ gauge s x * gauge s y :=
          mul_le_mul hgx hgy (div_nonneg one_pos.le hR.le) hgxpos.le
    calc
      dist (gauge s x) (gauge s y) / (‖gauge s x‖ * ‖gauge s y‖) ≤
          dist (gauge s x) (gauge s y) / (1 / R ^ 2) := by
        exact div_le_div_of_nonneg_left (dist_nonneg) (by positivity) hprod
      _ ≤ ((rn⁻¹ : ℝ) * dist x y) / (1 / R ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa [NNReal.coe_inv] using hdist
      _ = (rn⁻¹ : ℝ) * R ^ 2 * dist x y := by field_simp
  change dist ((gauge (Metric.ball 0 1) x / gauge s x) • x)
      ((gauge (Metric.ball 0 1) y / gauge s y) • y) ≤ (C : ℝ) * dist x y
  simp_rw [gauge_ball (by positivity : (0 : ℝ) ≤ 1)]
  rw [hnx, hny]
  simp only [inv_one, one_div]
  rw [dist_eq_norm]
  calc
    ‖(gauge s x)⁻¹ • x - (gauge s y)⁻¹ • y‖ ≤
        ‖(gauge s x)⁻¹ • (x - y)‖ +
          ‖((gauge s x)⁻¹ - (gauge s y)⁻¹) • y‖ := by
      have heq : (gauge s x)⁻¹ • x - (gauge s y)⁻¹ • y =
          (gauge s x)⁻¹ • (x - y) +
            ((gauge s x)⁻¹ - (gauge s y)⁻¹) • y := by module
      rw [heq]
      exact norm_add_le _ _
    _ ≤ R * dist x y + ((rn⁻¹ : ℝ) * R ^ 2 * dist x y) := by
      simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
      have hix : |(gauge s x)⁻¹| ≤ R := by rw [abs_of_pos (inv_pos.mpr hgxpos)]; exact hinvx
      have hid : |(gauge s x)⁻¹ - (gauge s y)⁻¹| ≤
          (rn⁻¹ : ℝ) * R ^ 2 * ‖x - y‖ := by simpa [dist_eq_norm] using hginv
      rw [hny, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_right hix (norm_nonneg _)) hid
    _ = (C : ℝ) * dist x y := by
      change _ = (R + (rn⁻¹ : ℝ) * R ^ 2) * dist x y
      ring

private theorem hausdorffMeasure_frontier_lt_top_of_mem_nhds_zero {s : Set Plane_m58ecd66}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane_m58ecd66)) (hcompact : IsCompact s) :
    Measure.hausdorffMeasure 1 (frontier s) < ⊤ := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzOnWith_gaugeRescale_unitSphere hconv h₀ hcompact.isBounded
  rw [← image_gaugeRescale_unitSphere_eq_frontier hconv h₀ hcompact.isBounded hcompact.isClosed]
  refine (hC.hausdorffMeasure_image_le (by positivity)).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
    hausdorffMeasure_one_sphere_lt_top

/-- The frontier of a planar convex body with nonempty interior has finite
one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_frontier_lt_top
    (K : ConvexBody (EuclideanSpace ℝ (Fin 2)))
    (hint : (interior (K : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) :
    Measure.hausdorffMeasure 1
      (frontier (K : Set (EuclideanSpace ℝ (Fin 2)))) < ⊤ := by
  obtain ⟨c, hc⟩ := hint
  let s : Set Plane_m58ecd66 := -c +ᵥ (K : Set Plane_m58ecd66)
  have hsconv : Convex ℝ s := K.convex.vadd (-c)
  have hscompact : IsCompact s := by
    change IsCompact ((fun x : Plane_m58ecd66 ↦ -c + x) '' (K : Set Plane_m58ecd66))
    exact K.isCompact.image (continuous_const.add continuous_id)
  have hs₀ : s ∈ nhds (0 : Plane_m58ecd66) := by
    rw [← mem_interior_iff_mem_nhds]
    change (0 : Plane_m58ecd66) ∈ interior (-c +ᵥ (K : Set Plane_m58ecd66))
    rw [interior_vadd]
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hc
  have hsfinite := hausdorffMeasure_frontier_lt_top_of_mem_nhds_zero hsconv hs₀ hscompact
  have himage : (fun z : Plane_m58ecd66 ↦ c + z) '' frontier s = frontier (K : Set Plane_m58ecd66)
    := by
    calc
      (fun z : Plane_m58ecd66 ↦ c + z) '' frontier s =
          frontier ((fun z : Plane_m58ecd66 ↦ c + z) '' s) :=
        (Homeomorph.addLeft c).image_frontier s
      _ = frontier (K : Set Plane_m58ecd66) := by
        congr 1
        ext x
        simp [s, Set.mem_vadd_set_iff_neg_vadd_mem]
  have hisom : Isometry (fun z : Plane_m58ecd66 ↦ c + z) := by
    intro x y
    simp
  rw [← himage, hisom.hausdorffMeasure_image (Or.inl zero_le_one)]
  exact hsfinite

end ConvexBody

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
# For Mathlib / Convex / Body / Hausdorff
-/

@[expose] public section

open Filter
open scoped Topology

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Eventual membership persists in a Hausdorff limit of convex bodies. -/
theorem mem_of_tendsto_hausdorffDist (q : E) (K : ℕ → ConvexBody E) (L : ConvexBody E)
    (hev : ∀ᶠ n in atTop, q ∈ (K n : Set E))
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E))
      atTop (𝓝 0)) : q ∈ (L : Set E) := by
  have hle : (fun _ : ℕ ↦ Metric.infDist q (L : Set E)) ≤ᶠ[atTop]
      (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E)) := by
    filter_upwards [hev] with n hn
    exact Metric.infDist_le_hausdorffDist_of_mem hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
  have hz : Metric.infDist q (L : Set E) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact (IsClosed.mem_iff_infDist_zero L.isClosed L.nonempty).mpr
    (le_antisymm hz Metric.infDist_nonneg)

end ConvexBody

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Collinear
-/

@[expose] public section

open Module

/-- A convex set with empty interior in dimension at most two is collinear. -/
theorem Convex.collinear_of_interior_eq_empty {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hdim : finrank ℝ E ≤ 2)
    (hint : interior s = ∅) : Collinear ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact collinear_empty ℝ E
  have hspan : vectorSpan ℝ s ≠ ⊤ := by
    intro h
    have ha : affineSpan ℝ s = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty
        (hne.mono (subset_affineSpan ℝ s))).mp (by simpa only [direction_affineSpan] using h)
    have hi := hs.interior_nonempty_iff_affineSpan_eq_top.mpr ha
    simp [hint] at hi
  apply collinear_iff_finrank_le_one.mpr
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hspan)
  simp only [finrank_top] at hlt
  omega

/-- A separating linear functional orders points on a line into a segment. -/
theorem Collinear.mem_segment_of_apply_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Collinear ℝ s) {a p x : E}
    (ha : a ∈ s) (hp : p ∈ s) (hx : x ∈ s) (f : E →ₗ[ℝ] ℝ)
    (hpos : 0 < f (p - a)) (hle : f p ≤ f x) : p ∈ segment ℝ a x := by
  have hne : a ≠ p := by
    intro h
    simp [h] at hpos
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hs.mem_affineSpan_of_mem_of_ne ha hp hx hne)
  have hrle : 1 ≤ r := by
    rw [← hr, AffineMap.lineMap_apply_module', map_add, map_smul] at hle
    have hsub := f.map_sub p a
    change f p ≤ r * f (p - a) + f a at hle
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrle
  have hinv : r⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hrpos.le, inv_le_one_of_one_le₀ hrle⟩
  have hmem := lineMap_mem_segment ℝ a x hinv
  rw [← hr, AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hrpos.ne',
    AffineMap.lineMap_apply_one] at hmem
  simpa only [hr] using hmem

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Body / Segment
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace ConvexBody

private abbrev Plane_mea511e5 := EuclideanSpace ℝ (Fin 2)

/-- A nonsingleton planar convex body with empty interior is a nontrivial segment. -/
theorem exists_eq_segment_of_interior_empty
    (K : ConvexBody (EuclideanSpace ℝ (Fin 2)))
    (hsub : ¬(K : Set (EuclideanSpace ℝ (Fin 2))).Subsingleton)
    (hint : interior (K : Set (EuclideanSpace ℝ (Fin 2))) = ∅) :
    ∃ a b, a ≠ b ∧
      (K : Set (EuclideanSpace ℝ (Fin 2))) = segment ℝ a b := by
  have hcol : Collinear ℝ (K : Set Plane_mea511e5) :=
    K.convex.collinear_of_interior_eq_empty
      (by simp) hint
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd
    (k := ℝ) (K : Set Plane_mea511e5)).mp hcol
  have hv₀ : v ≠ 0 := by
    intro hz
    apply hsub
    intro p hp q hq
    obtain ⟨r, hr⟩ := hv p hp
    obtain ⟨s, hs⟩ := hv q hq
    simpa [hz] using hr.trans (by simpa [hz] using hs.symm)
  let f : Plane_mea511e5 → ℝ := fun p ↦ inner ℝ v (p - p₀) / inner ℝ v v
  have hvv : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hv₀
  have hrepr : ∀ p ∈ (K : Set Plane_mea511e5), p = f p • v + p₀ := by
    intro p hp
    obtain ⟨r, rfl⟩ := hv p hp
    have hf : f (r • v + p₀) = r := by
      dsimp [f]
      rw [add_sub_cancel_right, inner_smul_right]
      field_simp [hvv]
    change r • v + p₀ = f (r • v + p₀) • v + p₀
    rw [hf]
  have hfcont : Continuous f := by fun_prop
  obtain ⟨a, ha, hamin⟩ := K.isCompact.exists_isMinOn K.nonempty hfcont.continuousOn
  obtain ⟨b, hb, hbmax⟩ := K.isCompact.exists_isMaxOn K.nonempty hfcont.continuousOn
  have habf : f a < f b := by
    apply lt_of_le_of_ne (hamin hb)
    intro heq
    apply hsub
    intro p hp q hq
    rw [hrepr p hp, hrepr q hq]
    have hpfa : f p = f a :=
      le_antisymm ((hbmax hp).trans_eq heq.symm) (hamin hp)
    have hqfa : f q = f a :=
      le_antisymm ((hbmax hq).trans_eq heq.symm) (hamin hq)
    rw [hpfa, hqfa]
  refine ⟨a, b, ?_, Set.Subset.antisymm ?_ ?_⟩
  · intro hab
    rw [hab] at habf
    exact habf.false
  · intro p hp
    rw [segment_eq_image']
    let t := (f p - f a) / (f b - f a)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨
      div_nonneg (sub_nonneg.mpr (hamin hp)) (sub_nonneg.mpr habf.le),
      (div_le_one (sub_pos.mpr habf)).mpr (sub_le_sub_right (hbmax hp) _)⟩
    refine ⟨t, ht, ?_⟩
    rw [hrepr p hp, hrepr a ha, hrepr b hb]
    have hden : f b - f a ≠ 0 := sub_ne_zero.mpr habf.ne'
    have htalg : f a + t * (f b - f a) = f p := by
      dsimp [t]
      field_simp [hden]
      ring
    rw [← htalg]
    module
  · exact K.convex.segment_subset ha hb

end ConvexBody

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
# For Mathlib / Convex / Function
-/

@[expose] public section

/-- A convex function stays below a bound before the right endpoint if the left
endpoint is strictly below the bound and the right endpoint is at most the bound. -/
theorem ConvexOn.lt_on_Ico_of_lt_of_le {f : ℝ → ℝ} {a b t c : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (ha : f a < c) (hb : f b ≤ c)
    (hat : a ≤ t) (htb : t < b) : f t < c := by
  have hab : a < b := lt_of_le_of_lt hat htb
  let u := (b - t) / (b - a)
  let v := (t - a) / (b - a)
  have hu : 0 < u := div_pos (sub_pos.mpr htb) (sub_pos.mpr hab)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hab.le)
  have huv : u + v = 1 := by dsimp [u, v]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have ht : u * a + v * b = t := by dsimp [u, v]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have h := hf.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hu.le hv huv
  simp only [smul_eq_mul, ht] at h
  have hleft : u * f a < u * c := mul_lt_mul_of_pos_left ha hu
  have hright : v * f b ≤ v * c := mul_le_mul_of_nonneg_left hb hv
  calc
    f t ≤ u * f a + v * f b := h
    _ < u * c + v * c := add_lt_add_of_lt_of_le hleft hright
    _ = c := by rw [← add_mul, huv, one_mul]

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Hausdorff
-/

@[expose] public section

open Filter TopologicalSpace
open scoped Topology

/-- Hausdorff limits of nonempty compact convex sets are convex. -/
theorem TopologicalSpace.NonemptyCompacts.convex_of_tendsto {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} [l.NeBot] {K : ι → NonemptyCompacts E} {L : NonemptyCompacts E}
    (hK : ∀ n, Convex ℝ (K n : Set E)) (hlim : Tendsto K l (𝓝 L)) :
    Convex ℝ (L : Set E) := by
  have happrox : ∀ x ∈ (L : Set E), ∃ p : ι → E,
      (∀ n, p n ∈ (K n : Set E)) ∧ Tendsto p l (𝓝 x) := by
    intro x hx
    choose p hp hd using fun n ↦ (K n).isCompact.exists_infDist_eq_dist (K n).nonempty x
    refine ⟨p, hp, ?_⟩
    have hinf := (NonemptyCompacts.lipschitz_infDist_const x).continuous.tendsto L |>.comp hlim
    have hz : Metric.infDist x (L : Set E) = 0 := Metric.infDist_zero_of_mem hx
    rw [hz] at hinf
    change Tendsto (fun n ↦ Metric.infDist x (K n : Set E)) l (𝓝 0) at hinf
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Function.comp_apply, hd, dist_comm] using hinf
  intro x hx y hy a b ha hb hab
  obtain ⟨p, hp, hpx⟩ := happrox x hx
  obtain ⟨q, hq, hqy⟩ := happrox y hy
  have hz := (hpx.const_smul a).add (hqy.const_smul b)
  have hi := NonemptyCompacts.uniformContinuous_infDist.continuous.tendsto
    (a • x + b • y, L) |>.comp (hz.prodMk_nhds hlim)
  have hzero : (fun n ↦ Metric.infDist (a • p n + b • q n) (K n : Set E)) = fun _ ↦ 0 := by
    funext n
    exact Metric.infDist_zero_of_mem (hK n (hp n) (hq n) ha hb hab)
  change Tendsto (fun n ↦ Metric.infDist (a • p n + b • q n) (K n : Set E))
    l (𝓝 (Metric.infDist (a • x + b • y) (L : Set E))) at hi
  rw [hzero] at hi
  exact (L.isCompact.isClosed.mem_iff_infDist_zero L.nonempty).mpr
    (tendsto_nhds_unique hi tendsto_const_nhds)

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Support
-/

@[expose] public section

open scoped ENNReal

/-- Support values of compact sets differ by at most their Hausdorff distance times the norm of
the direction. -/
theorem IsCompact.abs_csSup_inner_sub_le_hausdorffDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S T : Set E} (hS : IsCompact S) (hneS : S.Nonempty)
    (hT : IsCompact T) (hneT : T.Nonempty) (u : E) :
    |sSup ((fun x ↦ inner ℝ x u) '' S) - sSup ((fun x ↦ inner ℝ x u) '' T)| ≤
      Metric.hausdorffDist S T * ‖u‖ := by
  obtain ⟨x, hxS, hx, hxmax⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y, hyT, hy⟩ := hT.exists_infDist_eq_dist hneT x
  obtain ⟨z, hzT, hz, hzmax⟩ := hT.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneT
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hfin : Metric.hausdorffEDist S T ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hneS hneT
      hS.isBounded hT.isBounded
  have hdist : ‖x - y‖ ≤ Metric.hausdorffDist S T := by
    calc
      ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
      _ = Metric.infDist x T := hy.symm
      _ ≤ Metric.hausdorffDist S T := Metric.infDist_le_hausdorffDist_of_mem hxS hfin
  have hupper : sSup ((fun x ↦ inner ℝ x u) '' S) -
      sSup ((fun x ↦ inner ℝ x u) '' T) ≤ Metric.hausdorffDist S T * ‖u‖ := by
    rw [hx, hz]
    calc
      inner ℝ x u - inner ℝ z u ≤ inner ℝ x u - inner ℝ y u :=
        sub_le_sub_left (hzmax y hyT) _
      _ = inner ℝ (x - y) u := by rw [inner_sub_left]
      _ ≤ |inner ℝ (x - y) u| := le_abs_self _
      _ ≤ ‖x - y‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (x - y) u
      _ ≤ Metric.hausdorffDist S T * ‖u‖ := by gcongr
  have hreverse : sSup ((fun x ↦ inner ℝ x u) '' T) -
      sSup ((fun x ↦ inner ℝ x u) '' S) ≤ Metric.hausdorffDist S T * ‖u‖ := by
    have hfin' : Metric.hausdorffEDist T S ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hneT hneS
        hT.isBounded hS.isBounded
    obtain ⟨x', hx'S, hx'⟩ := hS.exists_infDist_eq_dist hneS z
    have hdist' : ‖z - x'‖ ≤ Metric.hausdorffDist S T := by
      calc
        ‖z - x'‖ = dist z x' := (dist_eq_norm z x').symm
        _ = Metric.infDist z S := hx'.symm
        _ ≤ Metric.hausdorffDist T S :=
          Metric.infDist_le_hausdorffDist_of_mem hzT hfin'
        _ = Metric.hausdorffDist S T := Metric.hausdorffDist_comm
    rw [hz, hx]
    calc
      inner ℝ z u - inner ℝ x u ≤ inner ℝ z u - inner ℝ x' u :=
        sub_le_sub_left (hxmax x' hx'S) _
      _ = inner ℝ (z - x') u := by rw [inner_sub_left]
      _ ≤ |inner ℝ (z - x') u| := le_abs_self _
      _ ≤ ‖z - x'‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (z - x') u
      _ ≤ Metric.hausdorffDist S T * ‖u‖ := by gcongr
  rw [abs_le]
  constructor <;> linarith

/-- The support values of a compact set are Lipschitz in the direction, with constant equal to the
maximum norm of a point in the set. -/
theorem IsCompact.abs_csSup_inner_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} (hS : IsCompact S) (hneS : S.Nonempty) (u v : E) :
    |sSup ((fun x ↦ inner ℝ x u) '' S) - sSup ((fun x ↦ inner ℝ x v) '' S)| ≤
      sSup (norm '' S) * ‖u - v‖ := by
  obtain ⟨x, hxS, hxu, hxu'⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y, hyS, hyv, hyv'⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x v) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hbound (z : E) (hz : z ∈ S) (w : E) :
      |inner ℝ z w| ≤ sSup (norm '' S) * ‖w‖ := by
    calc
      |inner ℝ z w| ≤ ‖z‖ * ‖w‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) z w
      _ ≤ sSup (norm '' S) * ‖w‖ := by
        gcongr
        exact le_csSup (hS.bddAbove_image continuous_norm.continuousOn) ⟨z, hz, rfl⟩
  have huv : sSup ((fun x ↦ inner ℝ x u) '' S) -
      sSup ((fun x ↦ inner ℝ x v) '' S) ≤ sSup (norm '' S) * ‖u - v‖ := by
    rw [hxu, hyv]
    calc
      inner ℝ x u - inner ℝ y v ≤ inner ℝ x u - inner ℝ x v :=
        sub_le_sub_left (hyv' x hxS) _
      _ = inner ℝ x (u - v) := by rw [inner_sub_right]
      _ ≤ |inner ℝ x (u - v)| := le_abs_self _
      _ ≤ sSup (norm '' S) * ‖u - v‖ := hbound x hxS (u - v)
  have hvu : sSup ((fun x ↦ inner ℝ x v) '' S) -
      sSup ((fun x ↦ inner ℝ x u) '' S) ≤ sSup (norm '' S) * ‖u - v‖ := by
    rw [hyv, hxu]
    calc
      inner ℝ y v - inner ℝ x u ≤ inner ℝ y v - inner ℝ y u :=
        sub_le_sub_left (hxu' y hyS) _
      _ = inner ℝ y (v - u) := by rw [inner_sub_right]
      _ ≤ |inner ℝ y (v - u)| := le_abs_self _
      _ ≤ sSup (norm '' S) * ‖v - u‖ := hbound y hyS (v - u)
      _ = sSup (norm '' S) * ‖u - v‖ := by rw [norm_sub_rev]
  rw [abs_le]
  constructor <;> linarith

/-- A convex body in a real inner product space is the intersection of its supporting
half-spaces. -/
theorem ConvexBody.eq_iInter_halfSpaces
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : ConvexBody E) :
    (K : Set E) = ⋂ u ∈ {u : E | ‖u‖ = 1},
      {p : E | inner ℝ p u ≤ sSup ((fun x ↦ inner ℝ x u) '' (K : Set E))} := by
  apply Set.Subset.antisymm
  · intro p hp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro u _
    obtain ⟨x, hx, hxmax, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : E ↦ inner ℝ x u) K.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    rw [hxmax]
    exact hmax p hp
  · intro p hp
    by_contra hpK
    obtain ⟨q, hq, hqmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex p
    have hpq : p - q ≠ 0 := sub_ne_zero.mpr (fun h ↦ hpK (h ▸ hq))
    let u : E := ‖p - q‖⁻¹ • (p - q)
    have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hpq
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hnorm.ne']
    have hproj : ∀ y ∈ (K : Set E), inner ℝ (p - q) (y - q) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero K.convex hq).mp hqmin
    have hqmax : sSup ((fun x ↦ inner ℝ x u) '' (K : Set E)) = inner ℝ q u := by
      obtain ⟨x, hx, hxmax, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge
        (f := fun x : E ↦ inner ℝ x u) K.nonempty
        (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
      rw [hxmax]
      apply le_antisymm
      · dsimp [u]
        rw [inner_smul_right, inner_smul_right]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnorm.le)
        have h := hproj x hx
        have h' : inner ℝ (x - q) (p - q) ≤ 0 := by rwa [real_inner_comm]
        rw [inner_sub_left] at h'
        linarith
      · exact hmax q hq
    have hpu := Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
    rw [hqmax] at hpu
    have hstrict : inner ℝ q u < inner ℝ p u := by
      dsimp [u]
      rw [inner_smul_right, inner_smul_right]
      have hself : 0 < inner ℝ (p - q) (p - q) := by
        rw [real_inner_self_eq_norm_sq]
        positivity
      rw [← sub_pos, ← mul_sub, ← inner_sub_left]
      exact mul_pos (inv_pos.mpr hnorm) hself
    exact (not_lt_of_ge hpu) hstrict

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Translation
-/

@[expose] public section

/-- Translation of a convex body by a vector. -/
def ConvexBody.translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (v : E) : ConvexBody E where
  carrier := (fun p ↦ p + v) '' (K : Set E)
  convex' := by simpa only [add_comm] using K.convex.translate v
  isCompact' := K.isCompact.image (continuous_id.add continuous_const)
  nonempty' := K.nonempty.image _

end

end
