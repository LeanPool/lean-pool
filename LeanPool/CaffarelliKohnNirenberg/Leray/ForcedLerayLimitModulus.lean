/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitFlux
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPressureBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPressureFiveThirds

/-!
# The forced time modulus

`lem:forced-equicontinuity`: for a smooth compactly supported spatial test
field `w`, the pairings `t ↦ ∫ u_ε(t)·w` of the forced regularized solutions
have a common Hölder modulus on `[0,T]`, independent of `ε`. The increment of
a pairing between two times is the space-time integral of the momentum flux
with the pressure term (the weak momentum identity `eq:reg-momentum-forced`
tested with `η(t) w(x)`), and Hölder's inequality with the uniform energy,
dissipation, `L³` and `L^{5/3}` quadratic-pressure bounds of
`lem:forced-energy-bounds` and the force-pressure bound of `lem:force-pressure`
bounds it by a constant times `|t - s|^{2/5}`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A power `x^r` with `r ≥ 2/5` of a quantity bounded by `c` is at most
`c^{r - 2/5} x^{2/5}`. -/
private theorem forcedLerayLimit_rpow_le_twoFifths {x c : ℝ≥0∞} (hxc : x ≤ c) {r : ℝ}
    (hr : 2 / 5 ≤ r) : x ^ r ≤ c ^ (r - 2 / 5) * x ^ (2 / 5 : ℝ) := by
  have hsplit : x ^ r = x ^ (r - 2 / 5) * x ^ (2 / 5 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith only [hr]) (by norm_num)]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul' (ENNReal.rpow_le_rpow hxc (by linarith only [hr])) le_rfl

/-- For a jointly measurable field whose kinetic energy is at most `E` on the
times of `I`, the square of each component integrates over `ℝ³ × I` to at most
`E |I|`. -/
private theorem forcedLerayLimit_lintegral_sq_slab_le {U : ParabolicPoint → Vec3}
    (hU : Measurable U) {I : Set ℝ} (hI : MeasurableSet I) {E : ℝ}
    (hslice : ∀ τ ∈ I, MemLp (fun x : Vec3 => U (x, τ)) 2 volume)
    (hbound : ∀ τ ∈ I, ∑ j : Fin 3, ∫ x : Vec3, U (x, τ) j ^ 2 ≤ E) (i : Fin 3) :
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I, ‖U z i‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal E * volume I := by
  have hmeas : Measurable fun z : Vec3 × ℝ => ‖U z i‖ₑ ^ (2 : ℝ) :=
    ((measurable_pi_apply i).comp hU).enorm.pow_const _
  have hsl : ∀ τ ∈ I, ∫⁻ x : Vec3, ‖U (x, τ) i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal E := by
    intro τ hτ
    have hmem := (hslice τ hτ).eval i
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.toReal_ofNat 2,
      ← eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmem.aestronglyMeasurable,
      vorticity_eLpNorm_two_eq_sqrt hmem, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    refine le_trans ?_ (hbound τ hτ)
    exact Finset.single_le_sum (f := fun j : Fin 3 => ∫ x : Vec3, U (x, τ) j ^ 2)
      (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
  calc ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I, ‖U z i‖ₑ ^ (2 : ℝ)
      = ∫⁻ τ in I, ∫⁻ x : Vec3, ‖U (x, τ) i‖ₑ ^ (2 : ℝ) :=
        (lintegral_slab_eq_prod _ I).trans (lintegral_prod_symm _ hmeas.aemeasurable)
    _ ≤ ∫⁻ _τ in I, ENNReal.ofReal E := setLIntegral_mono' hI hsl
    _ = ENNReal.ofReal E * volume I := setLIntegral_const _ _

/-- The kinetic-energy bound on time slices gives the local space-time
coordinate estimate used for the compact test region. -/
private theorem forcedLerayLimit_velocity_coordinate_sq_slab_le
    {U : ParabolicPoint → Vec3} (hU : Measurable U)
    (hSlice : ∀ τ : ℝ, MemLp (fun x : Vec3 => U (x, τ)) 2 volume)
    {I : Set ℝ} (hI : MeasurableSet I) {E : ℝ} {x : ℝ≥0∞}
    (hIvolume : volume I = x)
    (hkin : ∀ τ ∈ I, ∑ j : Fin 3, ∫ x : Vec3, U (x, τ) j ^ 2 ≤ E) :
    ∀ i, ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I, ‖U z i‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal E * x := by
  intro i
  rw [← hIvolume]
  exact forcedLerayLimit_lintegral_sq_slab_le hU hI (fun τ _ => hSlice τ) hkin i

/-- The pairing of a velocity with continuous `L²` slices against a fixed
square-integrable field is continuous in time. -/
private theorem forcedLerayLimit_pairing_continuousOn {U : ParabolicPoint → Vec3}
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => U (x, t)) 2 volume)
    (hcont : Continuous (fun t : Set.Ici (0 : ℝ) =>
      realVectorL2OfCoordinateFunction (fun x : Vec3 => U (x, t.1)) (hSlice t.1 t.2)))
    {w : Vec3 → Vec3} (hw : MemLp w 2 volume) :
    ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, U (x, t) i * w x i) (Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Ici (0 : ℝ)).domRestrict (fun t => ∫ x, ∑ i : Fin 3, U (x, t) i * w x i) =
      fun t : Set.Ici (0 : ℝ) => inner ℝ
        (realVectorL2OfCoordinateFunction (fun x : Vec3 => U (x, t.1)) (hSlice t.1 t.2))
        (realVectorL2OfCoordinateFunction w hw) := by
    funext t
    rw [inner_realVectorL2OfCoordinateFunction
      (realVectorL2OfCoordinateFunction_rep _ (hSlice t.1 t.2)).symm w hw]
    change ∫ x, ∑ i : Fin 3, U (x, t.1) i * w x i = _
    exact integral_congr_ae (Eventually.of_forall fun x =>
      Finset.sum_congr rfl fun i _ => mul_comm _ _)
  rw [heq]
  exact hcont.inner continuous_const

private theorem forcedLerayLimit_toReal_coefficient_le
    {Cenn coefficient : ℝ≥0∞} {M0 M1 : ℝ}
    (hM0nn : 0 ≤ M0) (hM1nn : 0 ≤ M1) (hfinite : coefficient ≠ ⊤)
    (hbound : Cenn ≤ ENNReal.ofReal (M0 + M1) * coefficient) :
    Cenn.toReal ≤ coefficient.toReal * (M0 + M1) := by
  rw [mul_comm, ← ENNReal.toReal_ofReal (add_nonneg hM0nn hM1nn), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hbound

private theorem forcedLerayLimit_weighted_coefficient_le
    {a1 a2 a3 a4 a5 : ℝ≥0∞} {M0 M1 : ℝ}
    (hM0nn : 0 ≤ M0) (hM1nn : 0 ≤ M1) :
    ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
        ENNReal.ofReal (3 * M1) * a4 + ENNReal.ofReal (3 * M1) * a5 ≤
      ENNReal.ofReal (M0 + M1) * (a1 + a2 + a3 + 3 * a4 + 3 * a5) := by
  have h3 : ENNReal.ofReal (3 * M1) = 3 * ENNReal.ofReal M1 := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hsum : ENNReal.ofReal (M0 + M1) = ENNReal.ofReal M0 + ENNReal.ofReal M1 :=
    ENNReal.ofReal_add hM0nn hM1nn
  rw [h3, hsum]
  calc ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
        3 * ENNReal.ofReal M1 * a4 + 3 * ENNReal.ofReal M1 * a5
      ≤ ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
        3 * ENNReal.ofReal M1 * a4 + 3 * ENNReal.ofReal M1 * a5 +
        (ENNReal.ofReal M0 * (a1 + a2 + 3 * a4 + 3 * a5) + ENNReal.ofReal M1 * a3) :=
          le_self_add
    _ = (ENNReal.ofReal M0 + ENNReal.ofReal M1) * (a1 + a2 + a3 + 3 * a4 + 3 * a5) := by
      ring

/-- Hölder's inequality on a finite slab controls the bounded-divergence
pairing with the uniformly bounded quadratic-pressure remainder. -/
private theorem forcedLerayLimit_pressure_remainder_lintegral_le
    {S : Set ParabolicPoint} {PN div : ParabolicPoint → ℝ}
    {MP5 vK y : ℝ≥0∞} {M1 : ℝ}
    (hPNae : AEStronglyMeasurable PN (volume.restrict S))
    (hnorm : eLpNorm PN (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict S) ≤ MP5)
    (hvol : volume S ^ (1 / (5 / 2 : ℝ)) = vK ^ (2 / 5 : ℝ) * y)
    (hdiv : ∀ z, |div z| ≤ 3 * M1) :
    ∫⁻ z in S, ‖PN z * div z‖ₑ ≤
      ENNReal.ofReal (3 * M1) * (MP5 * vK ^ (2 / 5 : ℝ)) * y := by
  have h53 : (5 / 3 : ℝ).HolderConjugate (5 / 2) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) h53
    hPNae.aemeasurable.enorm (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at hhold
  have h53ne : ENNReal.ofReal (5 / 3 : ℝ) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num
  have hnorm' : (∫⁻ z in S, ‖PN z‖ₑ ^ (5 / 3 : ℝ)) ^ (1 / (5 / 3 : ℝ)) ≤ MP5 := by
    have he : (∫⁻ z in S, ‖PN z‖ₑ ^ (5 / 3 : ℝ)) ^ (1 / (5 / 3 : ℝ)) =
        eLpNorm PN (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict S) := by
      rw [eLpNorm_eq_eLpNorm' h53ne ENNReal.ofReal_ne_top hPNae,
        ENNReal.toReal_ofReal (by norm_num), eLpNorm'_eq_lintegral_enorm]
    rw [he]
    exact hnorm
  have hpt : ∀ z, ‖PN z * div z‖ₑ ≤ ENNReal.ofReal (3 * M1) * ‖PN z‖ₑ := by
    intro z
    rw [enorm_mul, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hdiv z)
  calc ∫⁻ z in S, ‖PN z * div z‖ₑ
      ≤ ∫⁻ z in S, ENNReal.ofReal (3 * M1) * ‖PN z‖ₑ := lintegral_mono hpt
    _ = ENNReal.ofReal (3 * M1) * ∫⁻ z in S, ‖PN z‖ₑ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (3 * M1) *
        ((∫⁻ z in S, ‖PN z‖ₑ ^ (5 / 3 : ℝ)) ^ (1 / (5 / 3 : ℝ)) *
          volume S ^ (1 / (5 / 2 : ℝ))) := mul_le_mul' le_rfl hhold
    _ ≤ ENNReal.ofReal (3 * M1) * (MP5 * (vK ^ (2 / 5 : ℝ) * y)) := by
      rw [hvol]
      exact mul_le_mul' le_rfl (mul_le_mul' hnorm' le_rfl)
    _ = _ := by ring

/-- Turn a space-time flux estimate into the corresponding scalar time
modulus after identifying its integral with the pairing increment. -/
private theorem forcedLerayLimit_scalar_interval_modulus
    {H : ParabolicPoint → ℝ} {g : ℝ → ℝ}
    {S : Set ParabolicPoint} {s t : ℝ}
    (hHS : Integrable H (volume.restrict S))
    (hinc : g t - g s = ∫ z in S, H z) :
    |g t - g s| ≤ (∫⁻ z in S, ‖H z‖ₑ).toReal := by
  rw [hinc, ← Real.norm_eq_abs,
    ← integral_norm_eq_lintegral_enorm hHS.aestronglyMeasurable]
  exact norm_integral_le_integral_norm _

/-- Local L² estimates for the mollified and unmollified velocities give the
uniform convection contribution on a time slab. -/
private theorem forcedLerayLimit_convection_coordinate_estimate
    {S : Set ParabolicPoint} {J U : ParabolicPoint → Vec3} {i j : Fin 3}
    {E : ℝ} {x c y : ℝ≥0∞}
    (hJ : ∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ) ≤ 9 * ENNReal.ofReal E * x)
    (hU : ∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal E * x)
    (hx : x ≤ c ^ ((1 : ℝ) - 2 / 5) * y) :
    (∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
        c ^ ((1 : ℝ) - 2 / 5) * y := by
  calc _ ≤ (9 * ENNReal.ofReal E * x) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal E * x) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hJ (by norm_num))
        (ENNReal.rpow_le_rpow hU (by norm_num))
    _ = (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
        (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg (9 * ENNReal.ofReal E) x (by norm_num),
        ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal E) x (by norm_num)]
      ring
    _ = (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) * x := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    _ ≤ _ := by
      rw [mul_assoc _ (c ^ _) y]
      exact mul_le_mul' le_rfl hx

/-- The uniform dissipation estimate controls the gradient contribution on
the same slab. -/
private theorem forcedLerayLimit_diffusion_coordinate_estimate
    {S : Set ParabolicPoint} {D : ParabolicPoint → Fin 3 → Vec3} {i j : Fin 3}
    {G : ℝ} {vK x c y : ℝ≥0∞}
    (hD : ∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal G)
    (hvolume : volume S = vK * x)
    (hx : x ^ (1 / 2 : ℝ) ≤ c ^ ((1 / 2 : ℝ) - 2 / 5) * y) :
    (∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      volume S ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal G ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) *
        c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
  rw [hvolume, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc _ ≤ ENNReal.ofReal G ^ (1 / 2 : ℝ) * (vK ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hD (by norm_num)) le_rfl
    _ ≤ ENNReal.ofReal G ^ (1 / 2 : ℝ) *
        (vK ^ (1 / 2 : ℝ) * (c ^ ((1 / 2 : ℝ) - 2 / 5) * y)) := by gcongr
    _ = _ := by ring

/-- Cauchy--Schwarz turns the local force energy into its contribution to the
weak momentum flux. -/
private theorem forcedLerayLimit_force_coordinate_estimate
    {S : Set ParabolicPoint} {f : ParabolicPoint → Vec3} {i : Fin 3}
    {F vK x c y : ℝ≥0∞}
    (hF : ∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ) ≤ F)
    (hvolume : volume S = vK * x)
    (hx : x ^ (1 / 2 : ℝ) ≤ c ^ ((1 / 2 : ℝ) - 2 / 5) * y) :
    (∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * volume S ^ (1 / 2 : ℝ) ≤
      F ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
  rw [hvolume, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc _ ≤ F ^ (1 / 2 : ℝ) * (vK ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hF (by norm_num)) le_rfl
    _ ≤ F ^ (1 / 2 : ℝ) * (vK ^ (1 / 2 : ℝ) * (c ^ ((1 / 2 : ℝ) - 2 / 5) * y)) := by gcongr
    _ = _ := by ring

/-- The force-pressure estimate and the volume of the local slab give the
uniform pressure contribution with its time exponent. -/
private theorem forcedLerayLimit_force_pressure_coordinate_estimate
    {S : Set ParabolicPoint} {p : ParabolicPoint → ℝ}
    {vK x c Q y : ℝ≥0∞}
    (hp : (∫⁻ z in S, ‖p z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) ≤
      vK ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) * Q ^ (1 / 2 : ℝ))
    (hvolume : volume S = vK * x)
    (hx : x ^ (1 / 2 : ℝ) ≤ c ^ ((1 / 2 : ℝ) - 2 / 5) * y) :
    (∫⁻ z in S, ‖p z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) *
      volume S ^ (1 / 3 : ℝ) ≤
      vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
        c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
  rw [hvolume, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hx16 : x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc _ ≤ (vK ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) * Q ^ (1 / 2 : ℝ)) *
        (vK ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ)) := mul_le_mul' hp le_rfl
    _ = vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
        (x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ)) := by ring
    _ = vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [hx16]
    _ ≤ vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
        (c ^ ((1 / 2 : ℝ) - 2 / 5) * y) := by gcongr
    _ = _ := by ring

/-- Mollification preserves the local space-time L² coordinate bound, with
the dimension factor made explicit for the convection estimate. -/
private theorem forcedLerayLimit_transport_coordinate_sq_slab_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ParabolicPoint → Vec3} (hUs : StronglyMeasurable U)
    (hSlice : ∀ τ : ℝ, MemLp (fun x : Vec3 => U (x, τ)) 2 volume)
    {I : Set ℝ} {x : ℝ≥0∞}
    (hU : ∀ k : Fin 3,
      ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I, ‖U z k‖ₑ ^ (2 : ℝ) ≤ x) :
    ∀ j : Fin 3,
      ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I,
        ‖regUniformMollifiedVelocity ρ ε hε U z j‖ₑ ^ (2 : ℝ) ≤ 9 * x := by
  intro j
  have htr := forcedLerayLimit_transport_eLpNorm_le ρ ε hε U hUs hSlice
    (p := 2) (by norm_num) (by norm_num) I j
  simp only [ENNReal.toReal_ofNat] at htr
  have hl2 : ∀ (φ : ParabolicPoint → ℝ), AEStronglyMeasurable φ
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I) ) →
      eLpNorm φ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) ^ (2 : ℝ) =
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I, ‖φ z‖ₑ ^ (2 : ℝ) := by
    intro φ hφ
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hφ, ENNReal.toReal_ofNat,
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]
  have hJmeas : Measurable (regUniformMollifiedVelocity ρ ε hε U) :=
    forcedLerayLimit_transport_measurable ρ ε hε U hUs hSlice
  rw [hl2 (fun z => regUniformMollifiedVelocity ρ ε hε U z j)
    ((measurable_pi_apply j).comp hJmeas).aestronglyMeasurable] at htr
  have hsum : ∑ k : Fin 3, eLpNorm (fun z : ParabolicPoint => U z k) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) ^ (2 : ℝ) ≤ 3 * x := by
    calc ∑ k : Fin 3, eLpNorm (fun z : ParabolicPoint => U z k) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) ^ (2 : ℝ)
        ≤ ∑ _k : Fin 3, x := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [hl2 (fun z => U z k)
            ((measurable_pi_apply k).comp hUs.measurable).aestronglyMeasurable]
          exact hU k
      _ = 3 * x := by simp
  have h3 : (3 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 3 := by norm_num
  rw [h3] at htr
  calc ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I,
        ‖regUniformMollifiedVelocity ρ ε hε U z j‖ₑ ^ (2 : ℝ)
      ≤ 3 * ∑ k : Fin 3, eLpNorm (fun z : ParabolicPoint => U z k) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) ^ (2 : ℝ) := htr
    _ ≤ 3 * (3 * x) := by gcongr
    _ = 9 * x := by ring

/-- The weak momentum pairing identity integrates the flux over the
space-time slab between the two times. -/
private theorem forcedLerayLimit_pairing_increment_eq_slab_flux
    {H : ParabolicPoint → ℝ} {g h' : ℝ → ℝ} {K : Set Vec3}
    {T T1 s t : ℝ}
    (hHint : Integrable H
      (volume.restrict (spaceTimeSet K (Ioo 0 T1))))
    (hpair : ∀ τ ∈ Ioo 0 T1,
      g τ - g 0 = ∫ z in spaceTimeSet K (Ioo 0 τ), H z)
    (hh' : Integrable h')
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hTT1 : T < T1) (hst : s ≤ t)
    (hindicator : h' = (Ioo 0 T1).indicator (fun τ => ∫ x in K, H (x, τ))) :
    g t - g s = ∫ z in spaceTimeSet K (Ioc s t), H z := by
  have hkey : ∀ τ ∈ Icc 0 T, g τ - g 0 = ∫ τ' in (0 : ℝ)..τ, h' τ' := by
    intro τ hτ
    rcases hτ.1.eq_or_lt with hzero | hpositive
    · subst τ
      simp
    · rw [hpair τ ⟨hpositive, hτ.2.trans_lt hTT1⟩]
      rw [hindicator]
      exact forcedHopf_setIntegral_slab_eq_intervalIntegral K T1 H hHint τ
        ⟨hpositive.le, hτ.2.trans hTT1.le⟩
  have hdiff : g t - g s = ∫ τ in s..t, h' τ := by
    have hsub := intervalIntegral.integral_interval_sub_left
      (hh'.intervalIntegrable (a := 0) (b := t)) (hh'.intervalIntegrable (a := 0) (b := s))
    calc g t - g s = (g t - g 0) - (g s - g 0) := by ring
      _ = _ := by rw [hkey t ht, hkey s hs, hsub]
  let S := spaceTimeSet K (Ioc s t)
  have hSsub : Ioc s t ⊆ Ioo 0 T1 := fun τ hτ =>
    ⟨hs.1.trans_lt hτ.1, hτ.2.trans_lt (ht.2.trans_lt hTT1)⟩
  have hSle : volume.restrict S ≤ volume.restrict (spaceTimeSet K (Ioo 0 T1)) :=
    Measure.restrict_mono_set volume (Set.prod_mono subset_rfl hSsub)
  have hHS : Integrable H (volume.restrict S) := hHint.mono_measure hSle
  have hspace : ∫ τ in s..t, h' τ = ∫ z in S, H z := by
    rw [intervalIntegral.integral_of_le hst, hindicator]
    have hHS' : Integrable (fun q : Vec3 × ℝ => H q)
        (((volume : Measure Vec3).restrict K).prod ((volume : Measure ℝ).restrict (Ioc s t))) := by
      rw [← forcedHopf_slab_measure_eq_prod]
      exact hHS
    have hprod : ∫ z in S, H z = ∫ τ in Ioc s t, ∫ x in K, H (x, τ) := by
      change ∫ q, H q ∂((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet K (Ioc s t)) : Measure (Vec3 × ℝ)) = _
      rw [forcedHopf_slab_measure_eq_prod]
      exact integral_prod_symm _ hHS'
    rw [hprod]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    exact indicator_of_mem (hSsub hτ) _
  rw [hdiff, hspace]

/-- A global dissipation bound controls every gradient coordinate on a
smaller compact space-time slab. -/
private theorem forcedLerayLimit_gradient_coordinate_sq_local_le
    {D : ParabolicPoint → Fin 3 → Vec3}
    {S full : Set ParabolicPoint} {i j : Fin 3} {G : ℝ}
    (hD : MemLp D 2 (volume.restrict full)) (hS : S ⊆ full)
    (hsum : ∑ k : Fin 3, ∑ l : Fin 3, ∫ z in full, D z k l ^ 2 ≤ G) :
    ∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal G := by
  have hsq : ∀ y : ℝ, ‖y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (y ^ 2) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  refine (lintegral_mono_set hS).trans ?_
  have hint := ((hD.eval i).eval j).integrable_sq
  simp only [hsq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun z => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ hsum)
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ l : Fin 3,
    ∫ z in full, D z k l ^ 2) (fun k _ =>
      Finset.sum_nonneg fun l _ => integral_nonneg fun z => sq_nonneg _)
      (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun l => ∫ z in full, D z i l ^ 2)
    (fun l _ => integral_nonneg fun z => sq_nonneg _) (Finset.mem_univ j)

/-- A square-integrable vector field has finite total coordinate energy. -/
private theorem forcedLerayLimit_coordinate_energy_ne_top
    {f : ParabolicPoint → Vec3} {μ : Measure ParabolicPoint} (hf : MemLp f 2 μ) :
    (∑ i : Fin 3, ∫⁻ z, ‖f z i‖ₑ ^ (2 : ℝ) ∂μ) ≠ ⊤ := by
  refine ENNReal.sum_ne_top.2 fun i _ => ?_
  have hmem := hf.eval i
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num),
    ← ENNReal.toReal_ofNat 2,
    ← eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmem.aestronglyMeasurable]
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hmem.eLpNorm_ne_top

/-- Finite energy, dissipation, force and pressure bounds produce a finite
uniform Hölder coefficient on a compact spatial region. -/
private theorem forcedLerayLimit_modulus_coefficient_ne_top
    (E G : ℝ) (F Q MP c vK : ℝ≥0∞)
    (hF : F ≠ ⊤) (hQ : Q ≠ ⊤) (hMP : MP ≠ ⊤)
    (hcne : c ≠ ⊤) (hvK : vK ≠ ⊤) :
    let a1 : ℝ≥0∞ := ∑ _i : Fin 3, ∑ _j : Fin 3,
      (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
        c ^ ((1 : ℝ) - 2 / 5)
    let a2 : ℝ≥0∞ := ∑ _i : Fin 3, ∑ _j : Fin 3,
      ENNReal.ofReal G ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5)
    let a3 : ℝ≥0∞ := ∑ _i : Fin 3,
      F ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5)
    let a4 : ℝ≥0∞ := vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
      c ^ ((1 / 2 : ℝ) - 2 / 5)
    let a5 : ℝ≥0∞ := MP * vK ^ (2 / 5 : ℝ)
    a1 + a2 + a3 + 3 * a4 + 3 * a5 ≠ ⊤ := by
  have hrp : ∀ (z : ℝ≥0∞) (r : ℝ), 0 ≤ r → z ≠ ⊤ → z ^ r ≠ ⊤ := fun z r hr hz =>
    ENNReal.rpow_ne_top_of_nonneg hr hz
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => ?_
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))
      (hrp _ _ (by norm_num) ENNReal.ofReal_ne_top)) (hrp _ _ (by norm_num) hcne)
  · refine ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => ?_
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num) ENNReal.ofReal_ne_top)
      (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne)
  · refine ENNReal.sum_ne_top.2 fun _ _ => ?_
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num) hF)
      (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne)
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (hrp _ _ (by norm_num) hvK) (hrp _ _ (by norm_num) hQ))
      (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne))
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top hMP (hrp _ _ (by norm_num) hvK))

/-- Local coordinate energy bounds and the two pressure estimates assemble
into a uniform Hölder estimate for the full momentum flux. -/
private theorem forcedLerayLimit_flux_twoFifths_le
    {S : Set ParabolicPoint} {U J f : ParabolicPoint → Vec3}
    {D : ParabolicPoint → Fin 3 → Vec3} {P pF : ParabolicPoint → ℝ}
    {wc : Fin 3 → Vec3 → ℝ} {E G M0 M1 : ℝ} {F Q MP vK x c : ℝ≥0∞}
    (hM0 : ∀ i x, |wc i x| ≤ M0) (hM1 : ∀ i j x, |spatialDeriv (wc i) j x| ≤ M1)
    (hM2 : ∀ x, |∑ i : Fin 3, spatialDeriv (wc i) i x| ≤ 3 * M1)
    (hU : AEMeasurable U (volume.restrict S)) (hJ : AEMeasurable J (volume.restrict S))
    (hD : AEMeasurable D (volume.restrict S)) (hf : AEMeasurable f (volume.restrict S))
    (hpFae : AEStronglyMeasurable pF (volume.restrict S))
    (hPNae : AEStronglyMeasurable (fun z => P z - pF z) (volume.restrict S))
    (hdivS : AEMeasurable (fun z : ParabolicPoint => ∑ i : Fin 3, spatialDeriv (wc i) i z.1)
      (volume.restrict S))
    (hUS : ∀ i, ∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal E * x)
    (hJS : ∀ j, ∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ) ≤ 9 * ENNReal.ofReal E * x)
    (hDS : ∀ i j, ∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal G)
    (hfS : ∀ i, ∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ) ≤ F)
    (hPS : (∫⁻ z in S, ‖pF z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) ≤
      vK ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) * Q ^ (1 / 2 : ℝ))
    (hPNnorm : eLpNorm (fun z => P z - pF z) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict S) ≤ MP)
    (hvS : volume S = vK * x) (hxc : x ≤ c) :
    ∫⁻ z in S, ‖forcedHopfPairingFlux J U f D wc z +
      P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ ≤
      (ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
          (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
            c ^ ((1 : ℝ) - 2 / 5) +
        ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
          ENNReal.ofReal G ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) +
        ENNReal.ofReal M0 * ∑ _i : Fin 3,
          F ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) +
        ENNReal.ofReal (3 * M1) *
          (vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
            c ^ ((1 / 2 : ℝ) - 2 / 5)) +
        ENNReal.ofReal (3 * M1) * (MP * vK ^ (2 / 5 : ℝ))) * x ^ (2 / 5 : ℝ) := by
  let y : ℝ≥0∞ := x ^ (2 / 5 : ℝ)
  let PN : ParabolicPoint → ℝ := fun z => P z - pF z
  let H : ParabolicPoint → ℝ := fun z =>
    forcedHopfPairingFlux J U f D wc z + P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1
  let Cenn : ℝ≥0∞ :=
    ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
        (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
          c ^ ((1 : ℝ) - 2 / 5) +
      ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
        ENNReal.ofReal G ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) +
      ENNReal.ofReal M0 * ∑ _i : Fin 3,
        F ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) +
      ENNReal.ofReal (3 * M1) *
        (vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
          c ^ ((1 / 2 : ℝ) - 2 / 5)) +
      ENNReal.ofReal (3 * M1) * (MP * vK ^ (2 / 5 : ℝ))
  have hvolPN : volume S ^ (1 / (5 / 2 : ℝ)) = vK ^ (2 / 5 : ℝ) * y := by
    rw [hvS, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    norm_num
    rfl
  have hPN := forcedLerayLimit_pressure_remainder_lintegral_le hPNae hPNnorm hvolPN
    (fun z => hM2 z.1)
  have hflux := forcedLerayLimit_flux_lintegral_le (S := S) (U := U) (J := J) (f := f) (D := D)
    (P := pF) (wc := wc) hM0 hM1 hM2 hU hJ hD hf hpFae.aemeasurable
  have hx12 : x ^ (1 / 2 : ℝ) ≤ c ^ ((1 / 2 : ℝ) - 2 / 5) * y :=
    forcedLerayLimit_rpow_le_twoFifths hxc (by norm_num)
  have hx1 : x ≤ c ^ ((1 : ℝ) - 2 / 5) * y := by
    have h := forcedLerayLimit_rpow_le_twoFifths hxc (r := 1) (by norm_num)
    rwa [ENNReal.rpow_one] at h
  have hT1b : ∀ i j : Fin 3, (∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
        c ^ ((1 : ℝ) - 2 / 5) * y := by
    intro i j
    exact forcedLerayLimit_convection_coordinate_estimate (hJS j) (hUS i) hx1
  have hT2b : ∀ i j : Fin 3, (∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      volume S ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal G ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
    intro i j
    exact forcedLerayLimit_diffusion_coordinate_estimate (hDS i j) hvS hx12
  have hT3b : ∀ i : Fin 3, (∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      volume S ^ (1 / 2 : ℝ) ≤
      F ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
    intro i
    exact forcedLerayLimit_force_coordinate_estimate (hfS i) hvS hx12
  have hT4b : (∫⁻ z in S, ‖pF z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) * volume S ^ (1 / 3 : ℝ) ≤
      vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
    exact forcedLerayLimit_force_pressure_coordinate_estimate hPS hvS hx12
  have hsplitH : ∀ z, H z = (forcedHopfPairingFlux J U f D wc z +
      pF z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1) +
      PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1 := by
    intro z
    simp only [H, PN]
    ring
  have hH2meas : AEMeasurable (fun z => ‖PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ)
      (volume.restrict S) := (hPNae.aemeasurable.mul hdivS).enorm
  have hlint : ∫⁻ z in S, ‖H z‖ₑ ≤ Cenn * y := by
    calc ∫⁻ z in S, ‖H z‖ₑ
        ≤ ∫⁻ z in S, (‖forcedHopfPairingFlux J U f D wc z +
            pF z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ +
            ‖PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ) :=
          lintegral_mono fun z => by rw [hsplitH z]; exact enorm_add_le _ _
      _ = (∫⁻ z in S, ‖forcedHopfPairingFlux J U f D wc z +
            pF z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ) +
            ∫⁻ z in S, ‖PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ :=
          lintegral_add_right' _ hH2meas
      _ ≤ (ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
            (9 * ENNReal.ofReal E) ^ (1 / 2 : ℝ) * ENNReal.ofReal E ^ (1 / 2 : ℝ) *
              c ^ ((1 : ℝ) - 2 / 5) * y +
          ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
            ENNReal.ofReal G ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y +
          ENNReal.ofReal M0 * ∑ _i : Fin 3,
            F ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y +
          ENNReal.ofReal (3 * M1) * (vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
              c ^ ((1 / 2 : ℝ) - 2 / 5) * y)) +
          ENNReal.ofReal (3 * M1) * (MP * vK ^ (2 / 5 : ℝ)) * y := by
          refine add_le_add (hflux.trans ?_) hPN
          refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
          · exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ => hT1b i j)
          · exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ => hT2b i j)
          · exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hT3b i)
          · exact mul_le_mul' le_rfl hT4b
      _ = Cenn * y := by
          simp only [Cenn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  exact hlint

/-- The local force-pressure norm bound also bounds its integral power. -/
private theorem forcedLerayLimit_force_pressure_integral_power_le
    {p : ParabolicPoint → ℝ} {μ : Measure ParabolicPoint} {B : ℝ≥0∞}
    (hp : AEStronglyMeasurable p μ)
    (hbound : eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ B) :
    (∫⁻ z, ‖p z‖ₑ ^ (3 / 2 : ℝ) ∂μ) ^ (1 / (3 / 2 : ℝ)) ≤ B := by
  have h32 : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0 := by norm_num
  rwa [eLpNorm_eq_eLpNorm' h32 ENNReal.ofReal_ne_top hp,
    ENNReal.toReal_ofReal (by norm_num), eLpNorm'_eq_lintegral_enorm] at hbound

/-- Restricting the slice-energy estimate to a compact test region gives
the local velocity-coordinate bound. -/
private theorem forcedLerayLimit_velocity_coordinate_sq_local_le
    {U : ParabolicPoint → Vec3} (hU : Measurable U)
    (hSlice : ∀ τ : ℝ, MemLp (fun x : Vec3 => U (x, τ)) 2 volume)
    {I : Set ℝ} (hI : MeasurableSet I) {E : ℝ} {x : ℝ≥0∞}
    (hIvolume : volume I = x)
    (hkin : ∀ τ ∈ I, ∑ j : Fin 3, ∫ x : Vec3, U (x, τ) j ^ 2 ≤ E)
    {S : Set ParabolicPoint} (hS : S ⊆ spaceTimeSet (Set.univ : Set Vec3) I) :
    ∀ i, ∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal E * x := by
  intro i
  exact (lintegral_mono_set hS).trans
    (forcedLerayLimit_velocity_coordinate_sq_slab_le hU hSlice hI hIvolume hkin i)

/-- The mollified velocity satisfies the same compact-region estimate with
the dimension factor required by convection. -/
private theorem forcedLerayLimit_transport_coordinate_sq_local_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ParabolicPoint → Vec3} (hUs : StronglyMeasurable U)
    (hSlice : ∀ τ : ℝ, MemLp (fun x : Vec3 => U (x, τ)) 2 volume)
    {I : Set ℝ} (hI : MeasurableSet I) {E : ℝ} {x : ℝ≥0∞}
    (hIvolume : volume I = x)
    (hkin : ∀ τ ∈ I, ∑ j : Fin 3, ∫ x : Vec3, U (x, τ) j ^ 2 ≤ E)
    {S : Set ParabolicPoint} (hS : S ⊆ spaceTimeSet (Set.univ : Set Vec3) I) :
    ∀ j, ∫⁻ z in S, ‖regUniformMollifiedVelocity ρ ε hε U z j‖ₑ ^ (2 : ℝ) ≤
      9 * ENNReal.ofReal E * x := by
  have hU := forcedLerayLimit_velocity_coordinate_sq_slab_le hUs.measurable hSlice
    hI hIvolume hkin
  have hJ := forcedLerayLimit_transport_coordinate_sq_slab_le ρ ε hε hUs hSlice hU
  intro j
  simpa [mul_assoc] using (lintegral_mono_set hS).trans (hJ j)

/-- Integrability of the force pressure and the quadratic-pressure
remainder gives integrability of the total pressure on a compact slab. -/
private theorem forcedLerayLimit_pressure_integrable_of_remainder
    {μ : Measure ParabolicPoint} [IsFiniteMeasure μ] {P pF : ParabolicPoint → ℝ}
    (hrem : MemLp (fun z => P z - pF z) 2 μ)
    (hpF : MemLp pF (ENNReal.ofReal (3 / 2 : ℝ)) μ) : Integrable P μ := by
  have hexponent : 1 ≤ ENNReal.ofReal (3 / 2 : ℝ) := by norm_num
  refine ((hrem.integrable (by norm_num)).add (hpF.integrable hexponent)).congr
    (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, sub_add_cancel]

/-- A slab flux bound yields the scalar Hölder modulus, including the
initial time and the terminal endpoint of the closed interval. -/
private theorem forcedLerayLimit_scalar_twoFifths_modulus
    {H : ParabolicPoint → ℝ} {g : ℝ → ℝ} {K : Set Vec3} {T T1 s t : ℝ} {C : ℝ≥0∞}
    (hHint : Integrable H (volume.restrict (spaceTimeSet K (Ioo 0 T1))))
    (hpair : ∀ τ ∈ Ioo 0 T1, g τ - g 0 = ∫ z in spaceTimeSet K (Ioo 0 τ), H z)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hTT1 : T < T1) (hst : s ≤ t)
    (hflux : ∫⁻ z in spaceTimeSet K (Ioc s t), ‖H z‖ₑ ≤
      C * ENNReal.ofReal (t - s) ^ (2 / 5 : ℝ)) (hC : C ≠ ⊤) :
    |g t - g s| ≤ C.toReal * |t - s| ^ (2 / 5 : ℝ) := by
  let h' : ℝ → ℝ := (Ioo 0 T1).indicator (fun τ => ∫ x in K, H (x, τ))
  have hh' : Integrable h' := forcedHopf_integrable_timeDensity K T1 H hHint
  have hinc := forcedLerayLimit_pairing_increment_eq_slab_flux (h' := h') hHint hpair hh'
    hs ht hTT1 hst rfl
  have hsub : Ioc s t ⊆ Ioo 0 T1 := fun τ hτ =>
    ⟨hs.1.trans_lt hτ.1, hτ.2.trans_lt (ht.2.trans_lt hTT1)⟩
  have hHS := hHint.mono_measure (Measure.restrict_mono_set volume
    (Set.prod_mono subset_rfl hsub))
  calc |g t - g s| ≤ (∫⁻ z in spaceTimeSet K (Ioc s t), ‖H z‖ₑ).toReal :=
      forcedLerayLimit_scalar_interval_modulus hHS hinc
    _ ≤ (C * ENNReal.ofReal (t - s) ^ (2 / 5 : ℝ)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hC
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)) hflux
    _ = C.toReal * |t - s| ^ (2 / 5 : ℝ) := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal (sub_nonneg.2 hst), abs_of_nonneg (sub_nonneg.2 hst)]

/-- Bounds on test-coordinate derivatives bound the scalar divergence. -/
private theorem forcedLerayLimit_test_divergence_le
    {wc : Fin 3 → Vec3 → ℝ} {M1 : ℝ}
    (hM1 : ∀ i j x, |spatialDeriv (wc i) j x| ≤ M1) :
    ∀ x, |∑ i : Fin 3, spatialDeriv (wc i) i x| ≤ 3 * M1 := by
  intro x
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin 3, |spatialDeriv (wc i) i x| ≤ ∑ _i : Fin 3, M1 :=
        Finset.sum_le_sum fun i _ => hM1 i i x
    _ = 3 * M1 := by simp

/-- Restriction to the test region bounds each force coordinate by the
total force energy on the full slab. -/
private theorem forcedLerayLimit_force_coordinate_sq_local_le
    {f : ParabolicPoint → Vec3} {S full : Set ParabolicPoint} (hS : S ⊆ full) :
    ∀ i, ∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ) ≤
      ∑ j : Fin 3, ∫⁻ z in full, ‖f z j‖ₑ ^ (2 : ℝ) := by
  intro i
  exact (lintegral_mono_set hS).trans (Finset.single_le_sum
    (f := fun j => ∫⁻ z in full, ‖f z j‖ₑ ^ (2 : ℝ))
    (fun _ _ => bot_le) (Finset.mem_univ i))

/-- The divergence of a smooth spatial test field is jointly measurable
when viewed as a time-independent space-time scalar. -/
private theorem forcedLerayLimit_test_divergence_measurable
    {wc : Fin 3 → Vec3 → ℝ} (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i)) :
    Measurable fun z : ParabolicPoint => ∑ i : Fin 3, spatialDeriv (wc i) i z.1 := by
  have hdivx : Continuous fun x : Vec3 => ∑ i : Fin 3, spatialDeriv (wc i) i x :=
    continuous_finsetSum _ fun i _ =>
      ((hw i).continuous_fderiv (by simp)).clm_apply continuous_const
  exact hdivx.measurable.comp measurable_fst

/-- `lem:forced-equicontinuity` with a constant independent of the test
field: given the weak momentum identity `eq:reg-momentum-forced` of the
forced regularized solutions, there is `C`, depending only on `T`, `K`, the
datum and the force, such that for every smooth test field `w` supported in
`K` with `|w| ≤ M₀` and `|∂_j w_i| ≤ M₁` the pairings `t ↦ ∫ u_ε(t)·w` satisfy
`|∫ (u_ε(t) - u_ε(s))·w| ≤ C (M₀ + M₁) |t - s|^{2/5}` on `[0,T]`, for every
`ε`. -/
theorem forcedLerayLimit_time_modulus_uniform
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (hmom : ∀ (ε : ℝ) (hε : 0 < ε) (φ : ParabolicPoint → Vec3),
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε z i *
            timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε) z j *
                forcedRegVelocity ρ a ha f hf ε z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              forcedRegGradient ρ a ha f hf ε z i j * spatialPartial (fun y => φ y i) j z
          - forcedRegPressure ρ a ha f hf ε z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0)
    (T : ℝ) (hT : 0 < T) {K : Set Vec3} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (wc : Fin 3 → Vec3 → ℝ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i)) →
      (∀ i, tsupport (wc i) ⊆ K) → ∀ M0 M1 : ℝ, 0 ≤ M0 → 0 ≤ M1 →
      (∀ i x, |wc i x| ≤ M0) → (∀ i j x, |spatialDeriv (wc i) j x| ≤ M1) →
      ∀ (ε : ℝ), 0 < ε → ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        |(∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, t) i * wc i x) -
          ∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, s) i * wc i x| ≤
          C * (M0 + M1) * |t - s| ^ (2 / 5 : ℝ) := by
  classical
  set T1 : ℝ := T + 1 with hT1def
  have hT1 : 0 < T1 := add_pos hT one_pos
  have hTT1 : T < T1 := lt_add_one T
  -- uniform bounds on the slab of height T1
  obtain ⟨M3, MJ, MP, -, hMJ, -, hunif⟩ := forcedLerayLimit_uniform_slab_bounds ρ a ha f hf T1 hT1
  obtain ⟨M5, MJ5, MP5, -, -, hMP5, hunif5⟩ := forcedLerayLimit_fiveThirds_bounds ρ a ha f hf T1 hT1
  let A0 : ℝ := ∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2
  let F1 : ℝ := ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), f z i ^ 2
  let E1 : ℝ := Real.exp T1 * (A0 + F1)
  let G1 : ℝ := (A0 + F1 + T1 * E1) / 2
  let Ff : ℝ≥0∞ := ∑ i : Fin 3,
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), ‖f z i‖ₑ ^ (2 : ℝ)
  obtain ⟨-, hQfin, -, hpFloc⟩ := forcePressure_spec f hf T1 hT1
  let Q : ℝ≥0∞ := ∫⁻ t in Ioo 0 T1,
    eLpNorm (fun x : Vec3 => forcePressure f hf (x, t)) (ENNReal.ofReal (6 : ℝ))
      (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)
  let c : ℝ≥0∞ := ENNReal.ofReal T
  let vK : ℝ≥0∞ := volume K
  let a1 : ℝ≥0∞ := ∑ _i : Fin 3, ∑ _j : Fin 3,
      (9 * ENNReal.ofReal E1) ^ (1 / 2 : ℝ) * ENNReal.ofReal E1 ^ (1 / 2 : ℝ) *
        c ^ ((1 : ℝ) - 2 / 5)
  let a2 : ℝ≥0∞ := ∑ _i : Fin 3, ∑ _j : Fin 3,
      ENNReal.ofReal G1 ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5)
  let a3 : ℝ≥0∞ := ∑ _i : Fin 3,
      Ff ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5)
  let a4 : ℝ≥0∞ := vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
      c ^ ((1 / 2 : ℝ) - 2 / 5)
  let a5 : ℝ≥0∞ := MP5 * vK ^ (2 / 5 : ℝ)
  refine ⟨(a1 + a2 + a3 + 3 * a4 + 3 * a5).toReal, ENNReal.toReal_nonneg,
    fun wc hw hwK M0 M1 hM0nn hM1nn hM0 hM1 ε hε => ?_⟩
  have hwc : ∀ i, HasCompactSupport (wc i) := fun i =>
    IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (hwK i)
  have hM2 := forcedLerayLimit_test_divergence_le hM1
  let Cenn : ℝ≥0∞ :=
    ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
        (9 * ENNReal.ofReal E1) ^ (1 / 2 : ℝ) * ENNReal.ofReal E1 ^ (1 / 2 : ℝ) *
          c ^ ((1 : ℝ) - 2 / 5) +
      ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
        ENNReal.ofReal G1 ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) +
      ENNReal.ofReal M0 * ∑ _i : Fin 3,
        Ff ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) +
      ENNReal.ofReal (3 * M1) *
        (vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
          c ^ ((1 / 2 : ℝ) - 2 / 5)) +
      ENNReal.ofReal (3 * M1) * (MP5 * vK ^ (2 / 5 : ℝ))
  have hCenn_le : Cenn ≤ ENNReal.ofReal (M0 + M1) * (a1 + a2 + a3 + 3 * a4 + 3 * a5) := by
    change ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
        ENNReal.ofReal (3 * M1) * a4 + ENNReal.ofReal (3 * M1) * a5 ≤ _
    exact forcedLerayLimit_weighted_coefficient_le hM0nn hM1nn
  have hfin : a1 + a2 + a3 + 3 * a4 + 3 * a5 ≠ ⊤ :=
    forcedLerayLimit_modulus_coefficient_ne_top E1 G1 Ff Q MP5 c vK
      (forcedLerayLimit_coordinate_energy_ne_top (hf T1 hT1)) hQfin.ne hMP5.ne
      ENNReal.ofReal_ne_top hK.measure_lt_top.ne
  have hCle := forcedLerayLimit_toReal_coefficient_le hM0nn hM1nn hfin hCenn_le
  intro s hs t ht
  suffices hmain : |(∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, t) i * wc i x) -
      ∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, s) i * wc i x| ≤
      Cenn.toReal * |t - s| ^ (2 / 5 : ℝ) by
    exact hmain.trans (mul_le_mul_of_nonneg_right hCle (by positivity))
  wlog hst : s ≤ t generalizing s t with H
  · have h := H t ht s hs (le_of_not_ge hst)
    rw [abs_sub_comm, abs_sub_comm t s]
    exact h
  let U := forcedRegVelocity ρ a ha f hf ε
  let J := regUniformMollifiedVelocity ρ ε hε U
  let D := forcedRegGradient ρ a ha f hf ε
  let P := forcedRegPressure ρ a ha f hf ε
  let pF := forcePressure f hf
  obtain ⟨-, hJ3i, -⟩ := hunif ε hε
  have hc := forcedRegularised ρ a ha f hf ε hε
  obtain ⟨⟨hSlice, hcont, -, -⟩, -, hR2, -, hE⟩ := hc
  have hUs : StronglyMeasurable U := by
    change StronglyMeasurable (forcedRegVelocity ρ a ha f hf ε)
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact forcedRegRep_stronglyMeasurable ρ ε hε ha hf
  have hSliceAll : ∀ τ : ℝ, MemLp (fun x : Vec3 => U (x, τ)) 2 volume := by
    intro τ
    change MemLp (fun x : Vec3 => forcedRegVelocity ρ a ha f hf ε (x, τ)) 2 volume
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact forcedRegRep_memLp ρ ε hε ha hf τ
  have hJm : Measurable J := forcedLerayLimit_transport_measurable ρ ε hε U hUs hSliceAll
  have hDm : Measurable D := by
    change Measurable (forcedMollifiedGrad (forcedRegVelocity ρ a ha f hf ε))
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact measurable_forcedMollifiedGrad (forcedRegRep_stronglyMeasurable ρ ε hε ha hf)
      (fun t i => forcedRegRep_locallyIntegrable ρ ε hε ha hf t i)
  let μ1 : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1))
  have hU3 : MemLp U 3 μ1 := (forcedRegVelocity_memLp_slab ρ a ha f hf ε hε T1 hT1).2.2.1
  have hJ3 : MemLp J 3 μ1 := memLp_pi_iff.2 fun i => (hJ3i i).trans_lt hMJ
  have hD2 : MemLp D 2 μ1 := (hR2 T1 hT1).1
  have hf2 : MemLp f 2 μ1 := hf T1 hT1
  have hu2 : ∀ S : ℝ, 0 < S →
      MemLp U 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 S))) := fun S hS =>
    (forcedRegVelocity_memLp_slab ρ a ha f hf ε hε S hS).1
  obtain ⟨hkin, hgrad⟩ := forcedLerayLimit_energy_bounds ρ ε hε a ha.1 f hf U D hSlice hcont
    hu2 (fun S hS => (hR2 S hS).1) (fun t ht => (hE t ht).2) T1 hT1
  -- the pressure on the slab over `K`
  let νK : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 T1))
  have : IsFiniteMeasure νK := forcedHopf_slab_isFiniteMeasure hK T1
  have hνK : νK ≤ μ1 := Measure.restrict_mono_set volume
    (Set.prod_mono (subset_univ K) subset_rfl)
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hvK : vK ≠ ⊤ := hK.measure_lt_top.ne
  have hpFK : MemLp pF (ENNReal.ofReal (3 / 2 : ℝ)) νK :=
    (hpFloc K (Ioo 0 T1) hKmeas measurableSet_Ioo subset_rfl).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvK)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) measure_Ioo_lt_top.ne))
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hQfin.ne))
  have hPK : Integrable P νK := forcedLerayLimit_pressure_integrable_of_remainder
    ((hR2 T1 hT1).2.mono_measure hνK) hpFK
  have hwvec : MemLp (fun x : Vec3 => fun i : Fin 3 => wc i x) 2 volume :=
    memLp_pi_iff.2 fun i => (hw i).continuous.memLp_of_hasCompactSupport (hwc i)
  have hcontPair := forcedLerayLimit_pairing_continuousOn hSlice hcont hwvec
  have hpair := forcedLerayLimit_regPairing_sub_eq hT1 hw hK hwK hU3 hJ3 hD2 hf2 hPK hcontPair
    (hmom ε hε)
  let H : ParabolicPoint → ℝ := fun z =>
    forcedHopfPairingFlux J U f D wc z + P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1
  have hdivc := forcedLerayLimit_test_divergence_measurable hw
  have hHint : Integrable H νK :=
    (forcedHopf_pairingFlux_integrable hw hK hwK hJ3 hU3 hD2 hf2).add
      (hPK.mul_bdd hdivc.aestronglyMeasurable (c := 3 * M1)
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hM2 z.1))
  let S : Set ParabolicPoint := spaceTimeSet K (Ioc s t)
  have hSsub : Ioc s t ⊆ Ioo 0 T1 := fun τ hτ =>
    ⟨hs.1.trans_lt hτ.1, hτ.2.trans_lt (ht.2.trans_lt hTT1)⟩
  have hSle : volume.restrict S ≤ νK :=
    Measure.restrict_mono_set volume (Set.prod_mono subset_rfl hSsub)
  -- the bounds on the pieces of the flux
  let x : ℝ≥0∞ := ENNReal.ofReal (t - s)
  have hIoc : volume (Ioc s t) = x := by rw [Real.volume_Ioc]
  have hvS : volume S = vK * x := by
    change (volume : Measure (Vec3 × ℝ)) (K ×ˢ Ioc s t) = _
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc]
  have hxc : x ≤ c := ENNReal.ofReal_le_ofReal (by linarith only [hs.1, ht.2])
  have hSleμ1 : volume.restrict S ≤ μ1 := hSle.trans hνK
  have hSsubU : S ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioc s t) :=
    Set.prod_mono (subset_univ K) subset_rfl
  have hSsub1 : S ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1) :=
    Set.prod_mono (subset_univ K) hSsub
  have hkinI : ∀ τ ∈ Ioc s t, ∑ j : Fin 3, ∫ x : Vec3, U (x, τ) j ^ 2 ≤ E1 :=
    fun τ hτ => hkin τ ⟨hs.1.trans hτ.1.le, hτ.2.trans (ht.2.trans hTT1.le)⟩
  have hUS := forcedLerayLimit_velocity_coordinate_sq_local_le hUs.measurable hSliceAll
    measurableSet_Ioc hIoc hkinI hSsubU
  have hJS := forcedLerayLimit_transport_coordinate_sq_local_le ρ ε hε hUs hSliceAll
    measurableSet_Ioc hIoc hkinI hSsubU
  have hG1 : ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), D z i j ^ 2 ≤ G1 := by
    change _ ≤ (A0 + F1 + T1 * E1) / 2
    linarith only [hgrad]
  have hDS : ∀ i j, ∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal G1 := by
    intro i j
    exact forcedLerayLimit_gradient_coordinate_sq_local_le hD2 hSsub1 hG1
  have hfS := forcedLerayLimit_force_coordinate_sq_local_le (f := f) hSsub1
  -- the pressure piece
  have hpFae : AEStronglyMeasurable pF (volume.restrict S) :=
    hpFK.aestronglyMeasurable.mono_measure hSle
  have hPS : (∫⁻ z in S, ‖pF z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) ≤
      vK ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) * Q ^ (1 / 2 : ℝ) := by
    apply forcedLerayLimit_force_pressure_integral_power_le hpFae
    rw [← hIoc]
    exact hpFloc K (Ioc s t) hKmeas measurableSet_Ioc hSsub
  -- the quadratic pressure piece, in `L^{5/3}`
  let y : ℝ≥0∞ := x ^ (2 / 5 : ℝ)
  let PN : ParabolicPoint → ℝ := fun z => P z - pF z
  have hPNae : AEStronglyMeasurable PN (volume.restrict S) :=
    (hR2 T1 hT1).2.aestronglyMeasurable.mono_measure hSleμ1
  have hPNnorm : eLpNorm PN (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict S) ≤ MP5 :=
    (eLpNorm_mono_measure _ hSleμ1).trans (hunif5 ε hε).2.2
  have hlint : ∫⁻ z in S, ‖H z‖ₑ ≤ Cenn * y :=
    forcedLerayLimit_flux_twoFifths_le hM0 hM1 hM2 hUs.measurable.aemeasurable
      hJm.aemeasurable hDm.aemeasurable
      (hf2.aestronglyMeasurable.mono_measure hSleμ1).aemeasurable hpFae hPNae
      hdivc.aemeasurable hUS hJS hDS hfS hPS hPNnorm hvS hxc
  have hCenn : Cenn ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hCenn_le
  exact forcedLerayLimit_scalar_twoFifths_modulus hHint hpair hs ht hTT1 hst hlint hCenn

/-- `lem:forced-equicontinuity`: given the weak momentum identity
`eq:reg-momentum-forced` of the forced regularized solutions, for every
smooth test field `w` supported in a compact set `K` the pairings
`t ↦ ∫ u_ε(t)·w` have a common modulus `B |t - s|^{2/5}` on `[0,T]`, with `B`
independent of `ε`. -/
theorem forcedLerayLimit_time_modulus
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (hmom : ∀ (ε : ℝ) (hε : 0 < ε) (φ : ParabolicPoint → Vec3),
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε z i *
            timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε) z j *
                forcedRegVelocity ρ a ha f hf ε z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              forcedRegGradient ρ a ha f hf ε z i j * spatialPartial (fun y => φ y i) j z
          - forcedRegPressure ρ a ha f hf ε z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0)
    (T : ℝ) (hT : 0 < T) {K : Set Vec3} (hK : IsCompact K)
    {wc : Fin 3 → Vec3 → ℝ} (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i))
    (hwK : ∀ i, tsupport (wc i) ⊆ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ε : ℝ), 0 < ε → ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      |(∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, t) i * wc i x) -
        ∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, s) i * wc i x| ≤
        B * |t - s| ^ (2 / 5 : ℝ) := by
  have hwc : ∀ i, HasCompactSupport (wc i) := fun i =>
    IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (hwK i)
  -- bounds for the test field
  choose C0 hC0 using fun i => (hw i).continuous.bounded_above_of_compact_support (hwc i)
  choose C1 hC1 using fun i j =>
    (((hw i).continuous_fderiv
      (by simp)).clm_apply continuous_const).bounded_above_of_compact_support
      ((hwc i).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j))
  let M0 : ℝ := ∑ i : Fin 3, C0 i
  let M1 : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, C1 i j
  have hC0nn : ∀ i, 0 ≤ C0 i := fun i => (norm_nonneg _).trans (hC0 i 0)
  have hC1nn : ∀ i j, 0 ≤ C1 i j := fun i j => (norm_nonneg _).trans (hC1 i j 0)
  have hM0 : ∀ i x, |wc i x| ≤ M0 := fun i x => by
    rw [← Real.norm_eq_abs]
    exact (hC0 i x).trans (Finset.single_le_sum (f := C0) (fun j _ => hC0nn j)
      (Finset.mem_univ i))
  have hM1 : ∀ i j x, |spatialDeriv (wc i) j x| ≤ M1 := fun i j x => by
    rw [← Real.norm_eq_abs]
    refine (hC1 i j x).trans ?_
    refine (Finset.single_le_sum (f := fun j => C1 i j) (fun j _ => hC1nn i j)
      (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum (f := fun i => ∑ j : Fin 3, C1 i j)
      (fun i _ => Finset.sum_nonneg fun j _ => hC1nn i j) (Finset.mem_univ i)
  obtain ⟨C, hC, hmod⟩ := forcedLerayLimit_time_modulus_uniform ρ a ha f hf hmom T hT hK
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg fun i _ => hC0nn i
  have hM1nn : 0 ≤ M1 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC1nn i j
  exact ⟨C * (M0 + M1), mul_nonneg hC (add_nonneg hM0nn hM1nn),
    hmod wc hw hwK M0 M1 hM0nn hM1nn hM0 hM1⟩

/-- The time modulus of `lem:forced-equicontinuity` in the form of the
time-pairing hypothesis of `lem:compactness`, for the forced regularized
solutions along any sequence of positive regularization parameters, on the
time interval `(0,T)` and for test fields with values in L2Vec3. -/
theorem forcedLerayLimit_compactness_modulus
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (hmom : ∀ (ε : ℝ) (hε : 0 < ε) (φ : ParabolicPoint → Vec3),
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε z i *
            timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε) z j *
                forcedRegVelocity ρ a ha f hf ε z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              forcedRegGradient ρ a ha f hf ε z i j * spatialPartial (fun y => φ y i) j z
          - forcedRegPressure ρ a ha f hf ε z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n) (T : ℝ) (hT : 0 < T) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ a' b : ℝ, Icc a' b ⊆ Ioo 0 T →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc a' b → t ∈ Icc a' b →
          |(∫ x : Vec3, ∑ i : Fin 3,
              forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3,
              forcedRegVelocity ρ a ha f hf (εseq n) (x, s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ := by
  intro C hC _ a' b hab w hw _ hwC
  let wc : Fin 3 → Vec3 → ℝ := fun i => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i ∘ w
  have hwc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i) := fun i =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp hw
  have hwcK : ∀ i, tsupport (wc i) ⊆ C := fun i =>
    (tsupport_comp_subset (map_zero (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) w).trans hwC
  obtain ⟨B, hB, hmod⟩ := forcedLerayLimit_time_modulus ρ a ha f hf hmom T hT hC hwc hwcK
  refine ⟨0, B, 2 / 5, le_rfl, hB, by norm_num, fun n s t hs ht => ?_⟩
  have hs' : s ∈ Icc 0 T := Ioo_subset_Icc_self (hab hs)
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self (hab ht)
  rw [zero_mul, zero_add, Real.dist_eq]
  exact hmod (εseq n) (hseq n) s hs' t ht'

end CKN.Leray

end
