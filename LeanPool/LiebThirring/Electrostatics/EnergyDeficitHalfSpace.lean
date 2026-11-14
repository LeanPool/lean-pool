/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitHalfSpaceRadial
public import LeanPool.LiebThirring.Electrostatics.PlanePolar
public import LeanPool.LiebThirring.Electrostatics.SphereCap

/-!
# Exact inverse-fourth mass of an exterior half-space

The inverse-fourth planar slice has mass `π/s²` at positive normal height.

In the volume-preserving height coordinates the inverse-fourth kernel has its literal radial
denominator.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LiebThirring

/-- The inverse-fourth planar slice has mass `π/s²` at positive normal height. -/
theorem lintegral_planar_inverse_fourth (s : ℝ) (hs : 0 < s) :
    (∫⁻ q : Planar, ENNReal.ofReal ((s ^ 2 + ‖q‖ ^ 2) ^ 2)⁻¹) =
      ENNReal.ofReal (Real.pi / s ^ 2) := by
  have hg : Measurable (fun r : ℝ => ENNReal.ofReal ((s ^ 2 + r ^ 2) ^ 2)⁻¹) :=
    (((measurable_const.add (measurable_id.pow_const 2)).pow_const 2).inv).ennreal_ofReal
  rw [lintegral_planar_norm _ hg]
  have heq : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
      ENNReal.ofReal ((s ^ 2 + r ^ 2) ^ 2)⁻¹) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r / (s ^ 2 + r ^ 2) ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [← ENNReal.ofReal_mul hr.le, div_eq_mul_inv]
  rw [heq, lintegral_inverse_fourth_radial s hs,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  field_simp

/-- In the volume-preserving height coordinates the inverse-fourth kernel has
its literal radial denominator. -/
lemma inverse_fourth_sphereHeightSplit (p : ℝ × Planar) :
    ‖sphereHeightSplit.symm p‖ ^ 4 = (p.1 ^ 2 + ‖p.2‖ ^ 2) ^ 2 := by
  have h := sphereHeightSplit_norm (sphereHeightSplit.symm p)
  rw [sphereHeightSplit.apply_symm_apply] at h
  calc
    _ = (‖sphereHeightSplit.symm p‖ ^ 2) ^ 2 := by ring
    _ = _ := congrArg (fun t : ℝ => t ^ 2) h

/-- Exact inverse-fourth volume integral in the canonical coordinate half-space. -/
theorem lintegral_inverse_fourth_coordinate_halfSpace {a : ℝ} (ha : 0 < a) :
    (∫⁻ x : Position in {x | a ≤ x 2}, ENNReal.ofReal (‖x‖ ^ 4)⁻¹) =
      ENNReal.ofReal (Real.pi / a) := by
  classical
  have hset : MeasurableSet {x : Position | a ≤ x 2} :=
    isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2) |>.measurableSet
  have hprod : Measurable (fun p : ℝ × Planar =>
      (Ici a).indicator (fun s : ℝ => ENNReal.ofReal ((s ^ 2 + ‖p.2‖ ^ 2) ^ 2)⁻¹) p.1) := by
    have hm : Measurable (fun p : ℝ × Planar =>
        ENNReal.ofReal ((p.1 ^ 2 + ‖p.2‖ ^ 2) ^ 2)⁻¹) :=
      (((measurable_fst.pow_const 2).add (measurable_snd.norm.pow_const 2)).pow_const
        2).inv.ennreal_ofReal
    exact hm.ite ((measurable_fst measurableSet_Ici)) measurable_const
  calc
    _ = ∫⁻ p : ℝ × Planar, (Ici a).indicator
        (fun s : ℝ => ENNReal.ofReal ((s ^ 2 + ‖p.2‖ ^ 2) ^ 2)⁻¹) p.1 := by
      rw [← lintegral_indicator hset,
        ← sphereHeightSplit_preserving.symm.lintegral_comp_emb
          sphereHeightSplit.symm.measurableEmbedding]
      apply lintegral_congr
      intro p
      have hh : (sphereHeightSplit.symm p) 2 = p.1 := by
        rw [← sphereHeightSplit_fst, sphereHeightSplit.apply_symm_apply]
      by_cases hp : a ≤ p.1
      · rw [Set.indicator_of_mem (show sphereHeightSplit.symm p ∈ {x : Position | a ≤ x 2}
          from by simpa only [mem_ofPred_eq, hh] using hp), Set.indicator_of_mem (show p.1 ∈ Ici a
            from hp),
          inverse_fourth_sphereHeightSplit]
      · rw [Set.indicator_of_notMem (show sphereHeightSplit.symm p ∉ {x : Position | a ≤ x 2}
          from fun h => hp (by simpa only [mem_ofPred_eq, hh] using h)), Set.indicator_of_notMem
            (show p.1 ∉ Ici a from hp)]
    _ = ∫⁻ s in Ici a, ∫⁻ q : Planar, ENNReal.ofReal ((s ^ 2 + ‖q‖ ^ 2) ^ 2)⁻¹ := by
      rw [Measure.volume_eq_prod, lintegral_prod _ hprod.aemeasurable]
      rw [← lintegral_indicator measurableSet_Ici]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ Ici a
      · simp only [Set.indicator_of_mem hs]
      · simp only [Set.indicator_of_notMem hs, lintegral_zero]
    _ = ∫⁻ s in Ici a, ENNReal.ofReal (Real.pi / s ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ici (fun s hs => ?_)
      exact lintegral_planar_inverse_fourth s (ha.trans_le hs)
    _ = _ := lintegral_inverse_square_height a ha

/-- Exact inverse-fourth volume mass of an exterior half-space with arbitrary
unit normal and arbitrary centre. This is the energy deficit, equation. -/
theorem lintegral_inverse_fourth_halfSpace (n c : Position) (hn : ‖n‖ = 1)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ x : Position in {x | a ≤ inner ℝ n (x - c)},
      ENNReal.ofReal ((‖x - c‖ ^ 4)⁻¹)) = ENNReal.ofReal (Real.pi / a) := by
  classical
  let v : Position := EuclideanSpace.single 2 1
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.single, PiLp.norm_single]
  let Q : Position ≃ₗᵢ[ℝ] Position := (Submodule.span ℝ {v - n})ᗮ.reflection
  have hQ : Q v = n := Submodule.reflection_sub (hv.trans hn.symm)
  have hinner (z : Position) : inner ℝ n (Q z) = z 2 := by
    rw [← hQ, Q.inner_map_map]
    simp only [v, EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
  let e : Position ≃ᵃⁱ[ℝ] Position :=
    Q.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ c)
  have hsub (z : Position) : e z - c = Q z := by
    change Q z + c - c = Q z
    rw [add_sub_cancel_right]
  have hmp : MeasurePreserving e (volume : Measure Position) volume := by
    change MeasurePreserving (fun z : Position => Q z + c) volume volume
    exact (measurePreserving_add_right (volume : Measure Position) c).comp Q.measurePreserving
  have hset : MeasurableSet {x : Position | a ≤ inner ℝ n (x - c)} :=
    isClosed_le continuous_const (continuous_const.inner (continuous_id.sub continuous_const))
      |>.measurableSet
  calc
    _ = ∫⁻ z : Position, {z : Position | a ≤ z 2}.indicator
        (fun z : Position => ENNReal.ofReal ((‖z‖ ^ 4)⁻¹)) z := by
      rw [← lintegral_indicator hset, ← hmp.lintegral_comp_emb e.toHomeomorph.measurableEmbedding]
      apply lintegral_congr
      intro z
      simp only [Set.indicator, mem_ofPred_eq, hsub, hinner, Q.norm_map]
    _ = _ := by
      rw [lintegral_indicator
        (isClosed_le continuous_const
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2)).measurableSet]
      exact lintegral_inverse_fourth_coordinate_halfSpace ha

/-- The exact mass supplies the lower bound used by the nearest-nucleus argument. -/
theorem lintegral_inverse_fourth_halfSpace_le_of_subset (n c : Position) (hn : ‖n‖ = 1)
    {a : ℝ} (ha : 0 < a) (E : Set Position)
    (hE : {x : Position | a ≤ inner ℝ n (x - c)} ⊆ E) :
    ENNReal.ofReal (Real.pi / a) ≤
      ∫⁻ x in E, ENNReal.ofReal ((‖x - c‖ ^ 4)⁻¹) := by
  rw [← lintegral_inverse_fourth_halfSpace n c hn ha]
  exact lintegral_mono' (Measure.restrict_mono hE le_rfl) le_rfl

end LiebThirring

end
