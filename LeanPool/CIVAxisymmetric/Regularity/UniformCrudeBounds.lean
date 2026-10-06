/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CaffarelliKohnNirenberg.Statements.Alpha
public import LeanPool.CaffarelliKohnNirenberg.Statements.Beta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Delta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Lambda
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Uniform Crude Bounds

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CIV

variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- A cylinder based at an interior point `(x, s)` with `s` before the top time slice, whose
backward parabolic scale `r` keeps `s - r ^ 2` inside `(-1, 0)` and whose spatial ball sits
inside the unit ball, is itself contained in the unit cylinder. -/
theorem parabolicCylinder_subset_unitCylinder {x : Vec3} {s r : ℝ} (hs : s < 0)
    (hlow : -1 < s - r ^ 2) (hball : vec3Ball x r ⊆ vec3Ball 0 1) :
    parabolicCylinder x s r ⊆ unitCylinder := by
  have hIoc : Ioc (s - r ^ 2) s ⊆ Ioo (-1 : ℝ) 0 :=
    fun τ hτ => ⟨hlow.trans hτ.1, hτ.2.trans_lt hs⟩
  show vec3Ball x r ×ˢ Ioc (s - r ^ 2) s ⊆ vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0
  exact Set.prod_mono hball hIoc

/-- The Euclidean-norm-squared density of a `Vec3`-valued function is dominated by three
times its `enorm`-squared density, the two norms on `Vec3` being equivalent up to `√3`. -/
private lemma vec3EuclideanNorm_sq_le_three_mul_enorm_sq (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤ 3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have h1 : vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := vec3EuclideanNorm_le_sqrt_three_mul_norm v
  have h2 : (vec3EuclideanNorm v) ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) h1 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hp
  have hcast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hL : ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) =
      ENNReal.ofReal ((vec3EuclideanNorm v) ^ 2) := by
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg v), hcast, ENNReal.rpow_natCast]
  have hR : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg v), hcast, ENNReal.rpow_natCast]
  rw [hL, hR, ← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  exact ENNReal.ofReal_le_ofReal h2

/-- The energy scale-quantity `α` at an off-centre cylinder based at `(x, s)`, `s < 0`, is
bounded by the same quantity computed from the global `enorm`-based energy essential supremum
over the whole unit cylinder, uniformly in `s`, up to the factor `3` from the equivalence between
`vec3EuclideanNorm` and the entrywise sup-norm `enorm` on `Vec3`. -/
theorem alpha_le_of_globalEnergyClass (henergy : GlobalEnergyClass u Du p) {x : Vec3} {s r : ℝ}
    (hr : 0 < r) (hs : s < 0) (hlow : -1 < s - r ^ 2) (hball : vec3Ball x r ⊆ vec3Ball 0 1) :
    alpha u (x, s) r ≤ (r⁻¹ * (3 * essSup (fun τ => ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0))).toReal) ^ (1 / 2 : ℝ) := by
  have hpoint : ∀ τ : ℝ, timeSliceBallEnergy x r τ (fun w => vec3EuclideanNorm (u w)) ≤
      3 * ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ) := by
    intro τ
    calc timeSliceBallEnergy x r τ (fun w => vec3EuclideanNorm (u w))
        = ∫⁻ y in vec3Ball x r, ENNReal.ofReal (vec3EuclideanNorm (u (y, τ))) ^ (2 : ℝ) := by
          unfold timeSliceBallEnergy
          refine lintegral_congr (fun y => ?_)
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      _ ≤ ∫⁻ y in vec3Ball x r, 3 * ‖u (y, τ)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (fun y => vec3EuclideanNorm_sq_le_three_mul_enorm_sq (u (y, τ)))
      _ = 3 * ∫⁻ y in vec3Ball x r, ‖u (y, τ)‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' 3 _ (by norm_num)
      _ ≤ 3 * ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hball) (by positivity)
  have htimesub : Ioc (s - r ^ 2) s ⊆ Ioo (-1 : ℝ) 0 :=
    fun τ hτ => ⟨hlow.trans hτ.1, hτ.2.trans_lt hs⟩
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Ioc (s - r ^ 2) s))
    (ν := volume.restrict (Ioo (-1 : ℝ) 0))
    (Measure.restrict_mono htimesub le_rfl) (Filter.Eventually.of_forall hpoint)
  rw [ENNReal.essSup_const_mul] at hmono
  have hE1fin : essSup (fun τ => ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1 : ℝ) 0)) ≠ ⊤ := henergy.1.ne
  have h3E1fin : (3 : ℝ≥0∞) * essSup (fun τ => ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1 : ℝ) 0)) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hE1fin
  have hfin : timeSliceEnergyEssSup x s r (fun w => vec3EuclideanNorm (u w)) ≠ ⊤ :=
    ne_top_of_le_ne_top h3E1fin hmono
  have htoReal : (timeSliceEnergyEssSup x s r (fun w => vec3EuclideanNorm (u w))).toReal ≤
      (3 * essSup (fun τ => ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1 : ℝ) 0))).toReal :=
    ENNReal.toReal_mono h3E1fin hmono
  have hrinv : (0 : ℝ) ≤ r⁻¹ := inv_nonneg.mpr hr.le
  show (r⁻¹ * (timeSliceEnergyEssSup x s r (fun w => vec3EuclideanNorm (u w))).toReal) ^
      (1 / 2 : ℝ) ≤ _
  exact Real.rpow_le_rpow (mul_nonneg hrinv ENNReal.toReal_nonneg)
    (mul_le_mul_of_nonneg_left htoReal hrinv) (by norm_num)

/-- The gradient scale-quantity `β` at an off-centre cylinder based at `(x, s)`, `s < 0`, is
bounded by the same quantity computed from the global spatial-gradient integral over the whole
unit cylinder, uniformly in `s`. -/
theorem beta_le_of_globalEnergyClass {x : Vec3} {s r : ℝ} (hr : 0 < r) (hs : s < 0)
    (hlow : -1 < s - r ^ 2) (hball : vec3Ball x r ⊆ vec3Ball 0 1)
    (hfin : (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤) :
    beta u Du (x, s) r ≤
      (r⁻¹ * (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^ (1/2 :
        ℝ) := by
  have hsub : parabolicCylinder x s r ⊆ unitCylinder :=
    parabolicCylinder_subset_unitCylinder hs hlow hball
  have hle : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      ∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w) :=
    lintegral_mono_set hsub
  have htoReal : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal (spatialGradientSq u Du
    w)).toReal ≤
      (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)).toReal :=
    ENNReal.toReal_mono hfin hle
  have hrinv : (0 : ℝ) ≤ r⁻¹ := inv_nonneg.mpr hr.le
  show (r⁻¹ * (∫⁻ w in parabolicCylinder x s r,
      ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^ (1/2 : ℝ) ≤ _
  exact Real.rpow_le_rpow (mul_nonneg hrinv ENNReal.toReal_nonneg)
    (mul_le_mul_of_nonneg_left htoReal hrinv) (by norm_num)

/-- The pressure scale-quantity `δ` at an off-centre cylinder based at `(x, s)`, `s < 0`, is
bounded by the same quantity computed from the global `L^{3/2}` pressure integral over the whole
unit cylinder, uniformly in `s`. -/
theorem delta_le_of_globalEnergyClass {x : Vec3} {s r : ℝ} (hr : 0 < r) (hs : s < 0)
    (hlow : -1 < s - r ^ 2) (hball : vec3Ball x r ⊆ vec3Ball 0 1)
    (hfin : (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤) :
    delta p (x, s) r ≤
      (r ^ (-2 : ℝ) * (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3/2 : ℝ)).toReal) ^ (1/3 :
        ℝ) := by
  have hsub : parabolicCylinder x s r ⊆ unitCylinder :=
    parabolicCylinder_subset_unitCylinder hs hlow hball
  have hle : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
      ∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
    lintegral_mono_set hsub
  have htoReal : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal ≤
      (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal :=
    ENNReal.toReal_mono hfin hle
  have hrpow : (0 : ℝ) ≤ r ^ (-2 : ℝ) := Real.rpow_nonneg hr.le _
  show (r ^ (-2 : ℝ) * (∫⁻ w in parabolicCylinder x s r,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^ (1/3 : ℝ) ≤ _
  exact Real.rpow_le_rpow (mul_nonneg hrpow ENNReal.toReal_nonneg)
    (mul_le_mul_of_nonneg_left htoReal hrpow) (by norm_num)

/-- The force scale-quantity `λ` at every off-centre cylinder based at `(x, s)`, `s < 0`, inside
the unit ball is bounded by a constant multiple of `r ^ 3`, with the constant depending only on
the `ForceC2Bounded` data, uniformly in `x`, `s` and `r`. -/
theorem lambda_le_of_forceC2Bounded (q : ℝ) (hq : 5 / 2 < q) (hMf : ForceC2Bounded f) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (x : Vec3) (s r : ℝ), 0 < r → s < 0 → -1 < s - r ^ 2 →
      vec3Ball x r ⊆ vec3Ball 0 1 → lambda q f (x, s) r ≤ Cf * r ^ 3 := by
  obtain ⟨M, hM⟩ := hMf
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hbound : ∀ z ∈ unitCylinder, vec3EuclideanNorm (f z) ≤ Real.sqrt 3 * M' := by
    intro z hz
    have hcomp : ∀ i : Fin 3, |f z i| ≤ M' := by
      intro i
      have hzero : (0 : Fin 3 → ℕ) 0 + (0 : Fin 3 → ℕ) 1 + (0 : Fin 3 → ℕ) 2 ≤ 2 := by norm_num
      have := hM z hz i (0 : Fin 3 → ℕ) hzero
      simp only [multiPartial] at this
      exact this.trans (le_max_left _ _)
    have hnorm : ‖f z‖ ≤ M' := (pi_norm_le_iff_of_nonneg hM'0).2 hcomp
    calc vec3EuclideanNorm (f z) ≤ Real.sqrt 3 * ‖f z‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm (f z)
      _ ≤ Real.sqrt 3 * M' := by gcongr
  set Cf : ℝ := Real.sqrt 3 * M' * (4 * Real.pi / 3) ^ (1 / q : ℝ) with hCfdef
  have hCf0 : 0 ≤ Cf := by
    rw [hCfdef]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  refine ⟨Cf, hCf0, ?_⟩
  intro x s r hr hs hlow hball
  have hsub : parabolicCylinder x s r ⊆ unitCylinder :=
    parabolicCylinder_subset_unitCylinder hs hlow hball
  have hmeas : MeasurableSet (parabolicCylinder x s r) := measurableSet_parabolicCylinder x s r
  have hintbound : (∫⁻ w in parabolicCylinder x s r,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤
      ENNReal.ofReal (Real.sqrt 3 * M') ^ q * volume (parabolicCylinder x s r) := by
    calc (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q)
        ≤ ∫⁻ _w in parabolicCylinder x s r, ENNReal.ofReal (Real.sqrt 3 * M') ^ q := by
          apply setLIntegral_mono' hmeas
          intro z hz'
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hbound z (hsub hz'))) hqpos.le
      _ = ENNReal.ofReal (Real.sqrt 3 * M') ^ q * volume (parabolicCylinder x s r) :=
          setLIntegral_const _ _
  have hvol : volume (parabolicCylinder x s r) = ENNReal.ofReal (4 * Real.pi / 3 * r ^ 5) := by
    rw [volume_parabolicCylinder, volume_vec3Ball_eq, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hintbound2 : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^
    q) ≤
      ENNReal.ofReal (Real.sqrt 3 * M') ^ q * ENNReal.ofReal (4 * Real.pi / 3 * r ^ 5) := by
    rw [← hvol]; exact hintbound
  have hCombine : ENNReal.ofReal (Real.sqrt 3 * M') ^ q * ENNReal.ofReal (4 * Real.pi / 3 * r ^ 5) =
      ENNReal.ofReal ((Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5)) := by
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Real.sqrt 3 * M') ^ q by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hqpos.le]
  have hintbound3 : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^
    q) ≤
      ENNReal.ofReal ((Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5)) := hCombine ▸ hintbound2
  have hintReal : (∫⁻ w in parabolicCylinder x s r, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^
    q).toReal ≤
      (Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hintbound3
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hrpowbound : (∫⁻ w in parabolicCylinder x s r,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1/q : ℝ) ≤
      ((Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5)) ^ (1/q : ℝ) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hintReal (by positivity)
  have hRHSeq : ((Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5)) ^ (1/q : ℝ) =
      Real.sqrt 3 * M' * (4 * Real.pi / 3) ^ (1/q : ℝ) * r ^ (5/q : ℝ) := by
    have ha : (0 : ℝ) ≤ Real.sqrt 3 * M' := by positivity
    have hb : (0 : ℝ) ≤ (4 * Real.pi / 3 : ℝ) := by positivity
    have hr5 : (0 : ℝ) ≤ r ^ 5 := by positivity
    have hstep1 : ((Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5)) ^ (1/q : ℝ)
        = ((Real.sqrt 3 * M') ^ q) ^ (1/q : ℝ) * (4 * Real.pi / 3 * r ^ 5) ^ (1/q : ℝ) :=
      Real.mul_rpow (by positivity) (by positivity)
    have hstep2 : ((Real.sqrt 3 * M') ^ q) ^ (1/q : ℝ) = Real.sqrt 3 * M' := by
      rw [← Real.rpow_mul ha, mul_one_div, div_self hqpos.ne', Real.rpow_one]
    have hstep3 : (4 * Real.pi / 3 * r ^ 5 : ℝ) ^ (1/q : ℝ)
        = (4 * Real.pi / 3 : ℝ) ^ (1/q : ℝ) * (r ^ 5 : ℝ) ^ (1/q : ℝ) :=
      Real.mul_rpow hb hr5
    have hstep4 : (r ^ 5 : ℝ) ^ (1/q : ℝ) = r ^ (5/q : ℝ) := by
      rw [show (r : ℝ) ^ (5 : ℕ) = r ^ ((5 : ℕ) : ℝ) from (Real.rpow_natCast r 5).symm,
        ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    rw [hstep1, hstep2, hstep3, hstep4]
    ring
  show r ^ (3 - 5 / q : ℝ) * (∫⁻ w in parabolicCylinder x s r,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1/q : ℝ) ≤ _
  calc r ^ (3 - 5 / q : ℝ) * (∫⁻ w in parabolicCylinder x s r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1/q : ℝ)
      ≤ r ^ (3 - 5 / q : ℝ) *
          ((Real.sqrt 3 * M') ^ q * (4 * Real.pi / 3 * r ^ 5)) ^ (1/q : ℝ) :=
        mul_le_mul_of_nonneg_left hrpowbound (Real.rpow_nonneg hr.le _)
    _ = r ^ (3 - 5 / q : ℝ) * (Real.sqrt 3 * M' * (4 * Real.pi / 3) ^ (1/q : ℝ) * r ^ (5/q : ℝ))
      := by
        rw [hRHSeq]
    _ = Cf * (r ^ (3 - 5 / q : ℝ) * r ^ (5/q : ℝ)) := by rw [hCfdef]; ring
    _ = Cf * r ^ 3 := by
        rw [← Real.rpow_add hr, show (3 - 5/q : ℝ) + 5/q = 3 by ring,
          show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end CIV
