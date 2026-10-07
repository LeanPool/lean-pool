/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitWeakLower
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessProductSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLimitSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropClass
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Leray Hopf Limit Prop Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Space-time `L²` membership gives spatial `L²` membership on almost every
time slice of a finite slab. -/
theorem lerayHopfLimit_ae_slice_memLp_of_spaceTime_memLp
    (T : ℝ) (u : ParabolicPoint → Vec3)
    (hu : MemLp u 2
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T)))) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)),
      MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x,t))) 2 volume := by
  let μt : Measure ℝ := volume.restrict (Set.Ioo 0 T)
  have hMeasure :
      volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T)) =
        (volume : Measure Vec3).prod μt := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Set.Ioo 0 T) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Set.Ioo 0 T)]
    simp [μt, Measure.restrict_univ]
  have huProd : MemLp u 2 ((volume : Measure Vec3).prod μt) := by
    rw [← hMeasure]
    exact hu
  have hconverted : MemLp
      (fun z : ParabolicPoint => WithLp.toLp 2 (u z)) 2
      ((volume : Measure Vec3).prod μt) := by
    exact huProd.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hconverted' : MemLp
      (fun z : ParabolicPoint => WithLp.toLp 2 (u z)) 2
      ((volume.restrict (Set.univ : Set Vec3)).prod μt) := by
    simpa [Measure.restrict_univ] using hconverted
  have hslice := ae_memLp_slice_of_memLp_product_vec3
    (g := fun z : ParabolicPoint => WithLp.toLp 2 (u z)) hconverted'
  filter_upwards [hslice] with t ht
  simpa [μt, Measure.restrict_univ] using ht

/-- The exact regularized energy identity and convolution contraction give a
uniform spatial `L²` bound for every regularized slice. -/
theorem lerayHopfLimit_regSlice_uniformBound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (U : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3)
    (ha : MemLp (regUniformSpatialField a) 2 volume)
    (hUslice : ∀ t, 0 ≤ t →
      MemLp (regUniformVelocitySlice U t) 2 volume)
    (hR5 : ∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice U t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation U D t =
        eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
          2 volume ^ (2 : ℕ))
    (t : ℝ) (ht : 0 ≤ t) :
    eLpNorm (fun x : Vec3 => WithLp.toLp 2 (U (x,t))) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume := by
  have hmoll := regMollifyVector_eLpNorm_two_le ρ ε hε ha
  have henergy := hR5 t ht
  have hsq : eLpNorm (regUniformVelocitySlice U t) 2 volume ^ (2 : ℕ) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    calc
      eLpNorm (regUniformVelocitySlice U t) 2 volume ^ (2 : ℕ) ≤
          eLpNorm (regUniformVelocitySlice U t) 2 volume ^ (2 : ℕ) +
            2 * regUniformDissipation U D t := le_add_right le_rfl
      _ = eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ) := henergy
      _ ≤ eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) :=
        pow_le_pow_left' hmoll 2
  have hsliceBound : eLpNorm (regUniformVelocitySlice U t) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume :=
    (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hchange := eLpNorm_comp_measurePreserving
      (p := (2 : ℝ≥0∞))
      (f := (WithLp.toLp 2 : Vec3 → L2Vec3))
      (hUslice t ht).aestronglyMeasurable vec3ToL2Vec3_measurePreserving
  have hchange' :
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (U (x,t))) 2 volume =
        eLpNorm (regUniformVelocitySlice U t) 2 volume := by
    have hfun : (fun x : Vec3 => WithLp.toLp 2 (U (x,t))) =
        fun x : Vec3 => regUniformVelocitySlice U t (WithLp.toLp 2 x) := by
      funext x
      simp [regUniformVelocitySlice]
    rw [hfun]
    exact hchange
  rw [hchange']
  exact hsliceBound

/-- The coordinate `L²` datum has the Hilbert-carrier representative used by
the regularized mollifier. -/
theorem lerayHopfLimit_initialField_memLp
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume) :
    MemLp (regUniformSpatialField a) 2 volume := by
  have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) 2 volume :=
    ha.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  exact hcoord.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

/-- Uniform spatial `L²` bounds pass through weak convergence of every time
slice, giving the essential supremum bound in (LH1). -/
theorem lerayHopfLimit_slice_energy_essSup
    (T : ℝ) (u : ParabolicPoint → Vec3)
    (U : ℕ → ParabolicPoint → Vec3) (B : ℝ≥0∞) (hB : B < ⊤)
    (hslice : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)),
      MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x,t))) 2 volume)
    (hU : ∀ n t, t ∈ Set.Ioo 0 T →
      MemLp (fun x : Vec3 => WithLp.toLp 2 (U n (x,t))) 2 volume)
    (hUbound : ∀ n t, t ∈ Set.Ioo 0 T →
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (U n (x,t))) 2 volume ≤ B)
    (hweak : ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
      MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n (x,t) i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x,t) i * w x i))) :
    essSup (fun t : ℝ => ∫⁻ x : Vec3, ‖u (x,t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Set.Ioo 0 T)) < ⊤ := by
  let Bsq : ℝ≥0∞ := B ^ (2 : ℝ)
  have hBsq : Bsq < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)),
      (∫⁻ x : Vec3, ‖u (x,t)‖ₑ ^ (2 : ℝ)) ≤ Bsq := by
    filter_upwards [hslice, ae_restrict_mem measurableSet_Ioo]
      with t hsliceT htmem
    have ht : 0 < t := htmem.1
    let fU : ℕ → Vec3 → L2Vec3 := fun n x => WithLp.toLp 2 (U n (x,t))
    let fu : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (u (x,t))
    let hU' : ∀ n, MemLp (fU n) 2 volume := fun n => hU n t htmem
    let vu : Lp L2Vec3 2 volume := (hsliceT).toLp fu
    have hw : MemLp (fun x : Vec3 => u (x,t)) 2 volume := by
      have hcomp := hsliceT.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
      simpa [fu, PiLp.continuousLinearEquiv, WithLp.linearEquiv] using hcomp
    have hpairU (n : ℕ) :
        inner ℝ ((hU' n).toLp (fU n)) vu =
          ∫ x : Vec3, ∑ i : Fin 3, U n (x,t) i * u (x,t) i := by
      simpa [vu, fu, fU] using
        (inner_toLp_vec3_eq_integral_dot_measure volume (fU n) fu
          (hU' n) hsliceT)
    have hpairLimit :
        inner ℝ vu vu = ∫ x : Vec3, ∑ i : Fin 3, u (x,t) i * u (x,t) i := by
      simpa [vu, fu] using
        (inner_toLp_vec3_eq_integral_dot_measure volume fu fu hsliceT hsliceT)
    have hseqEq :
        (fun n => inner ℝ ((hU' n).toLp (fU n)) vu) =
          fun n => ∫ x : Vec3, ∑ i : Fin 3, U n (x,t) i * u (x,t) i :=
      funext hpairU
    have hnormEq :
      ‖vu‖ ^ 2 = ∫ x : Vec3,
          ∑ i : Fin 3, u (x,t) i * u (x,t) i := by
      calc
        ‖vu‖ ^ 2 = inner ℝ vu vu := (real_inner_self_eq_norm_sq vu).symm
        _ = _ := hpairLimit
    have hweakInner : Tendsto
        (fun n => inner ℝ ((hU' n).toLp (fU n)) vu) atTop
        (nhds (‖vu‖ ^ 2)) := by
      rw [hseqEq, hnormEq]
      exact hweak t ht (fun x => u (x,t)) hw
    have huniform (n : ℕ) :
        ‖(hU' n).toLp (fU n)‖ ≤ B.toReal := by
      rw [Lp.norm_toLp]
      exact ENNReal.toReal_mono
        hB.ne (hUbound n t htmem)
    have hnormBound : ‖vu‖ ≤ B.toReal :=
      norm_le_of_tendsto_inner_and_uniform_bound ENNReal.toReal_nonneg
        (Filter.Eventually.of_forall huniform) hweakInner
    have hnormEqLp : ‖vu‖ = (eLpNorm fu 2 volume).toReal := by
      change ‖(hsliceT).toLp fu‖ = _
      rw [Lp.norm_toLp]
    have hrealBound : (eLpNorm fu 2 volume).toReal ≤ B.toReal := by
      rw [← hnormEqLp]
      exact hnormBound
    have hLpBound : eLpNorm fu 2 volume ≤ B :=
      (ENNReal.toReal_le_toReal hsliceT.eLpNorm_ne_top hB.ne).mp hrealBound
    have hL2id : eLpNorm fu 2 volume ^ (2 : ℝ) =
        ∫⁻ x : Vec3, ‖fu x‖ₑ ^ (2 : ℝ) :=
      by convert (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
        hsliceT.aestronglyMeasurable) using 1 <;> norm_num [fu]
    have hpoint (x : Vec3) :
        ‖u (x,t)‖ₑ ^ (2 : ℝ) ≤ ‖fu x‖ₑ ^ (2 : ℝ) := by
      have hnorm : ‖u (x,t)‖ ≤ ‖fu x‖ := by
        calc
          ‖u (x,t)‖ ≤ vec3EuclideanNorm (u (x,t)) :=
            norm_le_vec3EuclideanNorm _
          _ = ‖WithLp.toLp 2 (u (x,t))‖ := vec3EuclideanNorm_eq_l2 _
          _ = ‖fu x‖ := rfl
      have henorm : ‖u (x,t)‖ₑ ≤ ‖fu x‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hnorm
      exact ENNReal.rpow_le_rpow henorm (by norm_num)
    calc
      (∫⁻ x : Vec3, ‖u (x,t)‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x : Vec3, ‖fu x‖ₑ ^ (2 : ℝ) :=
        lintegral_mono fun x => hpoint x
      _ = eLpNorm fu 2 volume ^ (2 : ℝ) := hL2id.symm
      _ ≤ B ^ (2 : ℝ) := ENNReal.rpow_le_rpow hLpBound (by norm_num)
  exact (essSup_le_of_ae_le Bsq hbound).trans_lt hBsq

end CKN.Leray

end
