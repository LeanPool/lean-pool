/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessProductSlices
public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls

/-!
# Compactness Limit Slices

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- A space-time `L²` vector field belongs to spatial `L²` on almost every
time slice of a rectangle. -/
theorem ae_memLp_slice_of_memLp_product_vec3
    {K : Set Vec3} {J : Set ℝ}
    (g : Vec3 × ℝ → L2Vec3)
    (hg : MemLp g 2 ((volume.restrict K).prod (volume.restrict J))) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x : Vec3 => g (x,t)) 2 (volume.restrict K) := by
  let μ : Measure Vec3 := volume.restrict K
  let ν : Measure ℝ := volume.restrict J
  let ρ : Measure (Vec3 × ℝ) := μ.prod ν
  let g₀ : Vec3 × ℝ → L2Vec3 := hg.aestronglyMeasurable.mk g
  have hg₀Meas : Measurable g₀ :=
    hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgEq : g =ᵐ[ρ] g₀ := hg.aestronglyMeasurable.ae_eq_mk
  have hg₀ : MemLp g₀ 2 ρ := (memLp_congr_ae hgEq).1 hg
  let G : Vec3 × ℝ → Vec3 := fun z => WithLp.ofLp (p := 2) (g₀ z)
  have hG : Measurable G := by
    exact (PiLp.continuous_ofLp 2 _).measurable.comp hg₀Meas
  have hfinite : (∫⁻ z : Vec3 × ℝ, ‖g₀ z‖ₑ ^ (2 : ℝ) ∂ρ) < ⊤ := by
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num) hg₀.aestronglyMeasurable).mp
        hg₀.eLpNorm_lt_top
  have hiter : (∫⁻ t in J, ∫⁻ x in K,
      ENNReal.ofReal (vec3EuclideanNorm (G (x,t))) ^ (2 : ℝ)
        ∂volume ∂volume) < ⊤ := by
    have hF : Measurable (fun z : Vec3 × ℝ => ‖g₀ z‖ₑ ^ (2 : ℝ)) := by
      fun_prop
    have hprod := lintegral_prod_symm (μ := μ) (ν := ν)
      (fun z : Vec3 × ℝ => ‖g₀ z‖ₑ ^ (2 : ℝ))
      (hF.aemeasurable)
    have hpoint (z : Vec3 × ℝ) :
        ‖g₀ z‖ₑ = ENNReal.ofReal (vec3EuclideanNorm (G z)) := by
      rw [← ofReal_norm, vec3EuclideanNorm_eq_l2]
    rw [hprod] at hfinite
    simpa only [ρ, μ, ν, hpoint] using hfinite
  have hslice₀ := CKN.Foundation.ae_memLp_two_vec3_slice_of_lintegral_sq_lt_top
    G hG hiter
  have hEqSwap : (fun z : ℝ × Vec3 => g z.swap) =ᵐ[
      ν.prod μ] (fun z : ℝ × Vec3 => g₀ z.swap) :=
    hgEq.comp_tendsto
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.tendsto_ae
  have hEqSlice := Measure.ae_ae_eq_curry_of_prod hEqSwap
  filter_upwards [hslice₀, hEqSlice] with t ht heq
  have ht₀ : MemLp (fun x : Vec3 => g₀ (x,t)) 2 μ := by
    simpa only [G, WithLp.toLp_ofLp] using ht
  exact (memLp_congr_ae heq).2 ht₀

end CKN.Leray
