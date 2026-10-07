/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessBallPairing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionTransport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientBumps
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Compactness Mollifier Test

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Topology
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- A reflected mollifier in one coordinate is a compactly supported `L²`
test for weak convergence of vector-valued spatial slices. -/
theorem memLp_reflected_mollifier_coordinate
    (m : ℕ) (x : Vec3) (i : Fin 3) :
    MemLp (fun y : Vec3 =>
      (WithLp.toLp 2 (Pi.single i
        (CKN.mollifier (d := 3) (CKN.sliceRadius m)
          (CKN.sliceRadius_pos m) (x - y))) : L2Vec3))
      2 (volume : Measure Vec3) := by
  let κ : Vec3 → ℝ := fun y =>
    CKN.mollifier (d := 3) (CKN.sliceRadius m)
      (CKN.sliceRadius_pos m) (x - y)
  let ψ : Vec3 → L2Vec3 := fun y =>
    WithLp.toLp 2 (Pi.single i (κ y))
  have hκcont : Continuous κ := by
    unfold κ
    exact (CKN.mollifier_contDiff (d := 3) (n := 0)
      (CKN.sliceRadius_pos m)).continuous.comp
        (continuous_const.sub continuous_id)
  have hκcompact : HasCompactSupport κ := by
    convert (CKN.mollifier_hasCompactSupport (d := 3)
      (CKN.sliceRadius_pos m)).comp_homeomorph
        (Homeomorph.subLeft x) using 1
    funext y
    simp [κ]
  have hψcont : Continuous ψ := by
    unfold ψ
    exact (PiLp.continuous_toLp 2 _).comp
      ((by simpa only [Pi.single] using
        (continuous_const.update i (continuous_id : Continuous (id : ℝ → ℝ))) :
        Continuous (fun a : ℝ => (Pi.single i a : Vec3))).comp hκcont)
  have hsupport : tsupport ψ ⊆ tsupport κ := by
    apply closure_mono
    intro y hy hκzero
    apply hy
    simp [ψ, hκzero]
  have hψcompact : HasCompactSupport ψ :=
    hκcompact.of_isClosed_subset (isClosed_tsupport ψ) hsupport
  exact hψcont.memLp_of_hasCompactSupport hψcompact

/-- On the support of a reflected mollifier, a cutoff equal to one leaves the
spatial Hilbert pairing equal to mollification. -/
theorem mollify_component_eq_cutoff_inner
    (f : Vec3 → Vec3) (χ : Vec3 → ℝ)
    (hf : MemLp (fun y => χ y • WithLp.toLp 2 (f y)) 2
      (volume : Measure Vec3))
    (m : ℕ) (x : Vec3) (i : Fin 3)
    (hχ : ∀ y, CKN.mollifier (d := 3) (CKN.sliceRadius m)
      (CKN.sliceRadius_pos m) (x - y) ≠ 0 → χ y = 1) :
    CKN.mollify (fun y => f y i)
      (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x =
    inner ℝ (hf.toLp (fun y => χ y • WithLp.toLp 2 (f y)))
      ((memLp_reflected_mollifier_coordinate m x i).toLp
        (fun y : Vec3 =>
          (WithLp.toLp 2 (Pi.single i
            (CKN.mollifier (d := 3) (CKN.sliceRadius m)
              (CKN.sliceRadius_pos m) (x - y))) : L2Vec3))) := by
  let κ : Vec3 → ℝ := fun y =>
    CKN.mollifier (d := 3) (CKN.sliceRadius m)
      (CKN.sliceRadius_pos m) (x - y)
  let ψ : Vec3 → L2Vec3 := fun y => WithLp.toLp 2 (Pi.single i (κ y))
  let hψ : MemLp ψ 2 (volume : Measure Vec3) :=
    memLp_reflected_mollifier_coordinate m x i
  have hsum (y : Vec3) :
      (∑ j : Fin 3, f y j * (χ y • ψ y) j) =
        f y i * χ y * κ y := by
    simp [ψ, Finset.sum_ite_eq', mul_assoc]
  calc
    CKN.mollify (fun y => f y i)
        (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x =
      ∫ y, f y i * κ y ∂volume := by
        simpa only [κ] using
          (CKN.integral_mul_mollifier_sub (fun y => f y i)
            (CKN.sliceRadius_pos m) x).symm
    _ = ∫ y, ∑ j : Fin 3, f y j * (χ y • ψ y) j ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hsum]
      by_cases hκ : κ y = 0
      · simp [hκ]
      · rw [hχ y (by simpa only [κ] using hκ)]
        ring
    _ = inner ℝ (hf.toLp (fun y => χ y • WithLp.toLp 2 (f y)))
        (hψ.toLp ψ) :=
      (inner_cutoff_vec3_eq_integral_dot f χ ψ hf hψ).symm

end CKN.Leray
