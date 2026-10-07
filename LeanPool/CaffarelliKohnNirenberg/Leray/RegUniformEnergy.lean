/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierContraction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Uniform energy bounds for regularized solutions

The energy equality in `thm:regularised` controls every time slice and the
full positive-time dissipation, uniformly in the regularization parameter.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial `L²` field represented by a CKN vector-valued function. -/
@[expose]
def regUniformSpatialField (f : Vec3 → Vec3) : L2Vec3 → L2Vec3 :=
  fun x => WithLp.toLp 2 (f (WithLp.ofLp x))

/-- A time slice of the velocity, represented on the Euclidean spatial carrier. -/
@[expose]
def regUniformVelocitySlice (u : ParabolicPoint → Vec3) (t : ℝ) :
    L2Vec3 → L2Vec3 :=
  fun x => WithLp.toLp 2 (u (WithLp.ofLp x, t))

/-- The mollified initial velocity as a pointwise CKN vector field. -/
@[expose]
def regUniformMollifiedInitial (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (a : Vec3 → Vec3) : Vec3 → Vec3 :=
  fun x => WithLp.ofLp
    (regMollifyVector ρ ε hε (regUniformSpatialField a) (WithLp.toLp 2 x))

/-- The regularized transport velocity `J_ε u` on positive-time slices. -/
@[expose]
def regUniformMollifiedVelocity (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => WithLp.ofLp (regMollifyVector ρ ε hε
    (regUniformVelocitySlice u z.2) (WithLp.toLp 2 z.1))

/-- Lebesgue measure on all positive space-time, used for global energy bounds. -/
@[expose]
def regUniformPositiveTimeMeasure : Measure ParabolicPoint :=
  volume.restrict (CKN.spaceTimeSet Set.univ (Ioi 0))

/-- Dissipation up to time `T`, measured on the positive-time carrier. -/
@[expose]
def regUniformDissipation (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, (if z.2 < T then ENNReal.ofReal (CKN.spatialGradientSq u Du z) else 0)
    ∂regUniformPositiveTimeMeasure

/-- The energy equality in `thm:regularised` implies the uniform slice-energy
bound and the full positive-time dissipation bound. -/
theorem regUniform_energy_bounds
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (ha : MemLp (regUniformSpatialField a) (2 : ℝ≥0∞) volume)
    (hR5 : ∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation u Du t =
        eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
          2 volume ^ (2 : ℕ))
    (hDuMeasurable : Measurable Du) :
    (∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ)) ∧
          2 * (∫⁻ z, ENNReal.ofReal (CKN.spatialGradientSq u Du z)
        ∂regUniformPositiveTimeMeasure) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
  have hDissipationMeasurable : AEMeasurable
      (fun z : ParabolicPoint =>
        ENNReal.ofReal (CKN.spatialGradientSq u Du z))
      regUniformPositiveTimeMeasure := by
    have hmeas : Measurable
        (fun z : ParabolicPoint =>
          ENNReal.ofReal (CKN.spatialGradientSq u Du z)) := by
      apply ENNReal.measurable_ofReal.comp
      unfold CKN.spatialGradientSq
      fun_prop
    exact hmeas.aemeasurable
  have hMoll := regMollifyVector_eLpNorm_two_le ρ ε hε ha
  have hMollSq :
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
          2 volume ^ (2 : ℕ) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hMoll (2 : ℕ)
  have hFinite (T : ℝ) (hT : 0 ≤ T) :
      eLpNorm (regUniformVelocitySlice u T) 2 volume ^ (2 : ℕ) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) ∧
      2 * regUniformDissipation u Du T ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    have hEnergy := hR5 T hT
    constructor
    · calc
        eLpNorm (regUniformVelocitySlice u T) 2 volume ^ (2 : ℕ) ≤
            eLpNorm (regUniformVelocitySlice u T) 2 volume ^ (2 : ℕ) +
              2 * regUniformDissipation u Du T := le_add_right le_rfl
        _ = eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
              2 volume ^ (2 : ℕ) := hEnergy
        _ ≤ eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := hMollSq
    · calc
        2 * regUniformDissipation u Du T ≤
            eLpNorm (regUniformVelocitySlice u T) 2 volume ^ (2 : ℕ) +
              2 * regUniformDissipation u Du T := le_add_left le_rfl
        _ = eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
              2 volume ^ (2 : ℕ) := hEnergy
        _ ≤ eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := hMollSq
  constructor
  · intro t ht
    exact (hFinite t ht).1
  · let g : ParabolicPoint → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (CKN.spatialGradientSq u Du z)
    let f : ℕ → ParabolicPoint → ℝ≥0∞ := fun n z =>
      g z * (if z.2 < (n : ℝ) + 1 then 1 else 0)
    have hmono : Monotone f := by
      intro m n hmn z
      by_cases hm : z.2 < (m : ℝ) + 1
      · have hn : z.2 < (n : ℝ) + 1 := by
          exact hm.trans_le (by exact_mod_cast Nat.add_le_add_right hmn 1)
        simp [f, hm, hn]
      · simp [f, hm]
    have hmeas (n : ℕ) : AEMeasurable (f n) regUniformPositiveTimeMeasure := by
      apply hDissipationMeasurable.mul
      have hset : MeasurableSet {z : ParabolicPoint | z.2 < (n : ℝ) + 1} := by
        exact measurableSet_lt (by fun_prop) measurable_const
      exact (measurable_const.piecewise hset measurable_const).aemeasurable
    have hlin := lintegral_iSup' hmeas (by
      filter_upwards [] with z
      intro m n hmn
      exact hmono hmn z)
    have hcover : (fun z : ParabolicPoint => ⨆ n, f n z) =ᵐ[
        regUniformPositiveTimeMeasure] g := by
      filter_upwards [ae_restrict_mem
        (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)] with z hz
      have hzpos : 0 < z.2 := hz.2
      apply le_antisymm
      · apply iSup_le
        intro n
        by_cases hn : z.2 < (n : ℝ) + 1
        · simp [f, hn, g]
        · simp [f, hn, g]
      · obtain ⟨n, hn⟩ := exists_nat_gt z.2
        have hn' : z.2 < (n : ℝ) + 1 := by
          exact hn.trans_le (by exact_mod_cast Nat.le_add_right n 1)
        exact le_iSup_of_le n (by simp [f, hn'])
    have hglobal :
        (∫⁻ z, g z ∂regUniformPositiveTimeMeasure) =
          ⨆ n : ℕ, regUniformDissipation u Du ((n : ℝ) + 1) := by
      calc
        (∫⁻ z, g z ∂regUniformPositiveTimeMeasure) =
            ∫⁻ z, ⨆ n, f n z ∂regUniformPositiveTimeMeasure :=
          lintegral_congr_ae hcover.symm
        _ = ⨆ n, ∫⁻ z, f n z ∂regUniformPositiveTimeMeasure := hlin
        _ = ⨆ n : ℕ, regUniformDissipation u Du ((n : ℝ) + 1) := by
          apply iSup_congr
          intro n
          simp [regUniformDissipation, f, g, regUniformPositiveTimeMeasure]
    rw [hglobal, ENNReal.mul_iSup]
    apply iSup_le
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    exact (hFinite ((n : ℝ) + 1) hn).2

/-- The regularized transport field has no larger slice `L²` norm than the
velocity, by the convolution contraction in `lem:reg-mollifier-bounds`. -/
theorem regUniform_mollified_velocity_L2_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (regUniformVelocitySlice u t) (2 : ℝ≥0∞) volume) :
    eLpNorm (regMollifyVector ρ ε hε (regUniformVelocitySlice u t))
        2 volume ≤ eLpNorm (regUniformVelocitySlice u t) 2 volume :=
  regMollifyVector_eLpNorm_two_le ρ ε hε hu

end CKN.Leray

end
