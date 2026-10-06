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
  have hM2 : ∀ x, |∑ i : Fin 3, spatialDeriv (wc i) i x| ≤ 3 * M1 := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin 3, |spatialDeriv (wc i) i x| ≤ ∑ _i : Fin 3, M1 :=
          Finset.sum_le_sum fun i _ => hM1 i i x
      _ = 3 * M1 := by simp
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
    have h3 : ENNReal.ofReal (3 * M1) = 3 * ENNReal.ofReal M1 := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    have hsum : ENNReal.ofReal (M0 + M1) = ENNReal.ofReal M0 + ENNReal.ofReal M1 :=
      ENNReal.ofReal_add hM0nn hM1nn
    change ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
        ENNReal.ofReal (3 * M1) * a4 + ENNReal.ofReal (3 * M1) * a5 ≤ _
    rw [h3, hsum]
    calc ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
          3 * ENNReal.ofReal M1 * a4 + 3 * ENNReal.ofReal M1 * a5
        ≤ ENNReal.ofReal M1 * a1 + ENNReal.ofReal M1 * a2 + ENNReal.ofReal M0 * a3 +
          3 * ENNReal.ofReal M1 * a4 + 3 * ENNReal.ofReal M1 * a5 +
          (ENNReal.ofReal M0 * (a1 + a2 + 3 * a4 + 3 * a5) + ENNReal.ofReal M1 * a3) :=
          le_self_add
      _ = (ENNReal.ofReal M0 + ENNReal.ofReal M1) * (a1 + a2 + a3 + 3 * a4 + 3 * a5) := by
          ring
  have hfin : a1 + a2 + a3 + 3 * a4 + 3 * a5 ≠ ⊤ := by
    have hrp : ∀ (z : ℝ≥0∞) (r : ℝ), 0 ≤ r → z ≠ ⊤ → z ^ r ≠ ⊤ := fun z r hr hz =>
      ENNReal.rpow_ne_top_of_nonneg hr hz
    have hcne : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hvK : vK ≠ ⊤ := hK.measure_lt_top.ne
    have hFf : Ff ≠ ⊤ := by
      refine ENNReal.sum_ne_top.2 fun i _ => ?_
      have hmem := (hf T1 hT1).eval i
      have hl2 : eLpNorm (fun z => f z i) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1))) ^ (2 : ℝ) =
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), ‖f z i‖ₑ ^ (2 : ℝ) := by
        rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmem.aestronglyMeasurable,
          ENNReal.toReal_ofNat, lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]
      rw [← hl2]
      exact hrp _ _ (by norm_num) hmem.eLpNorm_ne_top
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
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num) hFf)
        (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne)
    · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (hrp _ _ (by norm_num) hvK) (hrp _ _ (by norm_num) hQfin.ne))
        (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne))
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top hMP5.ne (hrp _ _ (by norm_num) hvK))
  have hCle : Cenn.toReal ≤ (a1 + a2 + a3 + 3 * a4 + 3 * a5).toReal * (M0 + M1) := by
    rw [mul_comm, ← ENNReal.toReal_ofReal (add_nonneg hM0nn hM1nn), ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hCenn_le
  intro s hs t ht
  suffices hmain : |(∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, t) i * wc i x) -
      ∫ x, ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf ε (x, s) i * wc i x| ≤
      Cenn.toReal * |t - s| ^ (2 / 5 : ℝ) by
    exact hmain.trans (mul_le_mul_of_nonneg_right hCle (by positivity))
  wlog hst : s ≤ t generalizing s t with H
  · have h := H t ht s hs (le_of_not_ge hst)
    rw [abs_sub_comm, abs_sub_comm t s]
    exact h
  have hst' : 0 ≤ t - s := sub_nonneg.2 hst
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
  have hPK : Integrable P νK := by
    have h1 : Integrable (fun z => P z - pF z) νK :=
      ((hR2 T1 hT1).2.mono_measure hνK).integrable (by norm_num)
    have h2 : Integrable pF νK := hpFK.integrable (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num))
    refine (h1.add h2).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  have hwvec : MemLp (fun x : Vec3 => fun i : Fin 3 => wc i x) 2 volume :=
    memLp_pi_iff.2 fun i => (hw i).continuous.memLp_of_hasCompactSupport (hwc i)
  have hcontPair := forcedLerayLimit_pairing_continuousOn hSlice hcont hwvec
  have hpair := forcedLerayLimit_regPairing_sub_eq hT1 hw hK hwK hU3 hJ3 hD2 hf2 hPK hcontPair
    (hmom ε hε)
  let H : ParabolicPoint → ℝ := fun z =>
    forcedHopfPairingFlux J U f D wc z + P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1
  have hdivx : Continuous fun x : Vec3 => ∑ i : Fin 3, spatialDeriv (wc i) i x :=
    continuous_finsetSum _ fun i _ =>
      ((hw i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdivc : Measurable fun z : ParabolicPoint => ∑ i : Fin 3, spatialDeriv (wc i) i z.1 :=
    hdivx.measurable.comp measurable_fst
  have hHint : Integrable H νK :=
    (forcedHopf_pairingFlux_integrable hw hK hwK hJ3 hU3 hD2 hf2).add
      (hPK.mul_bdd hdivc.aestronglyMeasurable (c := 3 * M1)
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hM2 z.1))
  let g : ℝ → ℝ := fun τ => ∫ x, ∑ i : Fin 3, U (x, τ) i * wc i x
  let h' : ℝ → ℝ := (Ioo 0 T1).indicator (fun τ => ∫ x in K, H (x, τ))
  have hh' : Integrable h' := forcedHopf_integrable_timeDensity K T1 H hHint
  have hkey : ∀ τ ∈ Icc 0 T, g τ - g 0 = ∫ τ' in (0 : ℝ)..τ, h' τ' := by
    intro τ hτ
    rcases hτ.1.eq_or_lt with h0 | hpos
    · subst h0
      simp
    · rw [hpair τ ⟨hpos, hτ.2.trans_lt hTT1⟩]
      exact forcedHopf_setIntegral_slab_eq_intervalIntegral K T1 H hHint τ
        ⟨hpos.le, hτ.2.trans hTT1.le⟩
  have hdiff : g t - g s = ∫ τ in s..t, h' τ := by
    have hsub := intervalIntegral.integral_interval_sub_left
      (hh'.intervalIntegrable (a := 0) (b := t)) (hh'.intervalIntegrable (a := 0) (b := s))
    calc g t - g s = (g t - g 0) - (g s - g 0) := by ring
      _ = _ := by rw [hkey t ht, hkey s hs, hsub]
  let S : Set ParabolicPoint := spaceTimeSet K (Ioc s t)
  have hSsub : Ioc s t ⊆ Ioo 0 T1 := fun τ hτ =>
    ⟨hs.1.trans_lt hτ.1, hτ.2.trans_lt (ht.2.trans_lt hTT1)⟩
  have hSle : volume.restrict S ≤ νK :=
    Measure.restrict_mono_set volume (Set.prod_mono subset_rfl hSsub)
  have hHS : Integrable H (volume.restrict S) := hHint.mono_measure hSle
  have hspace : ∫ τ in s..t, h' τ = ∫ z in S, H z := by
    rw [intervalIntegral.integral_of_le hst]
    have hHS' : Integrable (fun q : Vec3 × ℝ => H q)
        ((volume.restrict K).prod (volume.restrict (Ioc s t))) := by
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
  have hfinal : |g t - g s| ≤ (∫⁻ z in S, ‖H z‖ₑ).toReal := by
    rw [hdiff, hspace, ← Real.norm_eq_abs,
      ← integral_norm_eq_lintegral_enorm hHS.aestronglyMeasurable]
    exact norm_integral_le_integral_norm _
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
  have hsq : ∀ y : ℝ, ‖y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (y ^ 2) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hl2 : ∀ (μ : Measure ParabolicPoint) (φ : ParabolicPoint → ℝ),
      AEStronglyMeasurable φ μ → eLpNorm φ 2 μ ^ (2 : ℝ) = ∫⁻ z, ‖φ z‖ₑ ^ (2 : ℝ) ∂μ := by
    intro μ φ hφ
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hφ, ENNReal.toReal_ofNat,
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]
  have hUsl : ∀ i, ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioc s t), ‖U z i‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal E1 * x := by
    intro i
    rw [← hIoc]
    exact forcedLerayLimit_lintegral_sq_slab_le hUs.measurable measurableSet_Ioc
      (fun τ _ => hSliceAll τ)
      (fun τ hτ => hkin τ ⟨hs.1.trans hτ.1.le, hτ.2.trans (ht.2.trans hTT1.le)⟩) i
  have hUS : ∀ i, ∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal E1 * x := fun i =>
    (lintegral_mono_set hSsubU).trans (hUsl i)
  have hJS : ∀ j, ∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ) ≤ 9 * ENNReal.ofReal E1 * x := by
    intro j
    refine (lintegral_mono_set hSsubU).trans ?_
    have htr := forcedLerayLimit_transport_eLpNorm_le ρ ε hε U hUs hSliceAll (p := 2)
      (by norm_num) (by norm_num) (Ioc s t) j
    simp only [ENNReal.toReal_ofNat] at htr
    rw [hl2 _ (fun z => regUniformMollifiedVelocity ρ ε hε U z j)
      ((measurable_pi_apply j).comp hJm).aestronglyMeasurable] at htr
    refine htr.trans ?_
    have hsum : ∑ k : Fin 3, eLpNorm (fun z : ParabolicPoint => U z k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioc s t))) ^ (2 : ℝ) ≤
        3 * (ENNReal.ofReal E1 * x) := by
      calc ∑ k : Fin 3, eLpNorm (fun z : ParabolicPoint => U z k) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioc s t))) ^ (2 : ℝ)
          ≤ ∑ _k : Fin 3, ENNReal.ofReal E1 * x := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [hl2 _ (fun z => U z k)
              ((measurable_pi_apply k).comp hUs.measurable).aestronglyMeasurable]
            exact hUsl k
        _ = 3 * (ENNReal.ofReal E1 * x) := by simp
    have h3 : (3 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 3 := by norm_num
    rw [h3]
    calc 3 * ∑ k : Fin 3, eLpNorm (fun z : ParabolicPoint => U z k) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioc s t))) ^ (2 : ℝ)
        ≤ 3 * (3 * (ENNReal.ofReal E1 * x)) := by gcongr
      _ = 9 * ENNReal.ofReal E1 * x := by ring
  have hG1 : ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), D z i j ^ 2 ≤ G1 := by
    change _ ≤ (A0 + F1 + T1 * E1) / 2
    linarith only [hgrad]
  have hDS : ∀ i j, ∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal G1 := by
    intro i j
    refine (lintegral_mono_set hSsub1).trans ?_
    have hint := ((hD2.eval i).eval j).integrable_sq
    simp only [hsq]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hG1)
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin 3,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), D z i j ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => integral_nonneg fun z => sq_nonneg _)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∫ z in spaceTimeSet (Set.univ : Set Vec3)
      (Ioo 0 T1), D z i j ^ 2) (fun j _ => integral_nonneg fun z => sq_nonneg _)
      (Finset.mem_univ j)
  have hfS : ∀ i, ∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ) ≤ Ff := fun i =>
    (lintegral_mono_set hSsub1).trans (Finset.single_le_sum (f := fun i =>
      ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T1), ‖f z i‖ₑ ^ (2 : ℝ))
      (fun _ _ => bot_le) (Finset.mem_univ i))
  -- the pressure piece
  have h32 : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num
  have hpFae : AEStronglyMeasurable pF (volume.restrict S) :=
    hpFK.aestronglyMeasurable.mono_measure hSle
  have hPS : (∫⁻ z in S, ‖pF z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) ≤
      vK ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) * Q ^ (1 / 2 : ℝ) := by
    have hPe : (∫⁻ z in S, ‖pF z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) =
        eLpNorm pF (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S) := by
      rw [eLpNorm_eq_eLpNorm' h32 ENNReal.ofReal_ne_top hpFae,
        ENNReal.toReal_ofReal (by norm_num), eLpNorm'_eq_lintegral_enorm]
    rw [hPe, ← hIoc]
    exact hpFloc K (Ioc s t) hKmeas measurableSet_Ioc hSsub
  -- the quadratic pressure piece, in `L^{5/3}`
  let y : ℝ≥0∞ := x ^ (2 / 5 : ℝ)
  let PN : ParabolicPoint → ℝ := fun z => P z - pF z
  have hPNae : AEStronglyMeasurable PN (volume.restrict S) :=
    (hR2 T1 hT1).2.aestronglyMeasurable.mono_measure hSleμ1
  have hdivS : AEMeasurable (fun z : ParabolicPoint => ∑ i : Fin 3, spatialDeriv (wc i) i z.1)
      (volume.restrict S) := hdivc.aemeasurable
  have hPN : ∫⁻ z in S, ‖PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ ≤
      ENNReal.ofReal (3 * M1) * (MP5 * vK ^ (2 / 5 : ℝ)) * y := by
    have hpt : ∀ z, ‖PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ ≤
        ENNReal.ofReal (3 * M1) * ‖PN z‖ₑ := by
      intro z
      rw [enorm_mul, mul_comm]
      refine mul_le_mul' ?_ le_rfl
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hM2 z.1)
    have h53 : (5 / 3 : ℝ).HolderConjugate (5 / 2) := ⟨by norm_num, by norm_num, by norm_num⟩
    have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) h53
      hPNae.aemeasurable.enorm (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply_univ, one_mul] at hhold
    have h53ne : ENNReal.ofReal (5 / 3 : ℝ) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      norm_num
    have hnorm : (∫⁻ z in S, ‖PN z‖ₑ ^ (5 / 3 : ℝ)) ^ (1 / (5 / 3 : ℝ)) ≤ MP5 := by
      have he : (∫⁻ z in S, ‖PN z‖ₑ ^ (5 / 3 : ℝ)) ^ (1 / (5 / 3 : ℝ)) =
          eLpNorm PN (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict S) := by
        rw [eLpNorm_eq_eLpNorm' h53ne ENNReal.ofReal_ne_top hPNae,
          ENNReal.toReal_ofReal (by norm_num), eLpNorm'_eq_lintegral_enorm]
      rw [he]
      exact (eLpNorm_mono_measure _ hSleμ1).trans (hunif5 ε hε).2.2
    have hvol : volume S ^ (1 / (5 / 2 : ℝ)) = vK ^ (2 / 5 : ℝ) * y := by
      rw [hvS, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      norm_num
      rfl
    calc ∫⁻ z in S, ‖PN z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ
        ≤ ∫⁻ z in S, ENNReal.ofReal (3 * M1) * ‖PN z‖ₑ := lintegral_mono hpt
      _ = ENNReal.ofReal (3 * M1) * ∫⁻ z in S, ‖PN z‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3 * M1) * ((∫⁻ z in S, ‖PN z‖ₑ ^ (5 / 3 : ℝ)) ^ (1 / (5 / 3 : ℝ)) *
            volume S ^ (1 / (5 / 2 : ℝ))) := mul_le_mul' le_rfl hhold
      _ ≤ ENNReal.ofReal (3 * M1) * (MP5 * (vK ^ (2 / 5 : ℝ) * y)) := by
          rw [hvol]
          exact mul_le_mul' le_rfl (mul_le_mul' hnorm le_rfl)
      _ = _ := by ring
  -- combination
  have hflux := forcedLerayLimit_flux_lintegral_le (S := S) (U := U) (J := J) (f := f) (D := D)
    (P := pF) (wc := wc) hM0 hM1 hM2 hUs.measurable.aemeasurable hJm.aemeasurable
    hDm.aemeasurable (hf2.aestronglyMeasurable.mono_measure hSleμ1).aemeasurable
    hpFae.aemeasurable
  have hx12 : x ^ (1 / 2 : ℝ) ≤ c ^ ((1 / 2 : ℝ) - 2 / 5) * y :=
    forcedLerayLimit_rpow_le_twoFifths hxc (by norm_num)
  have hx1 : x ≤ c ^ ((1 : ℝ) - 2 / 5) * y := by
    have h := forcedLerayLimit_rpow_le_twoFifths hxc (r := 1) (by norm_num)
    rwa [ENNReal.rpow_one] at h
  have hx16 : x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hxx : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hT1b : ∀ i j : Fin 3, (∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (9 * ENNReal.ofReal E1) ^ (1 / 2 : ℝ) * ENNReal.ofReal E1 ^ (1 / 2 : ℝ) *
        c ^ ((1 : ℝ) - 2 / 5) * y := by
    intro i j
    calc _ ≤ (9 * ENNReal.ofReal E1 * x) ^ (1 / 2 : ℝ) * (ENNReal.ofReal E1 * x) ^ (1 / 2 : ℝ) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (hJS j) (by norm_num))
            (ENNReal.rpow_le_rpow (hUS i) (by norm_num))
      _ = (9 * ENNReal.ofReal E1) ^ (1 / 2 : ℝ) * ENNReal.ofReal E1 ^ (1 / 2 : ℝ) *
            (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg (9 * ENNReal.ofReal E1) x (by norm_num),
            ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal E1) x (by norm_num)]
          ring
      _ = (9 * ENNReal.ofReal E1) ^ (1 / 2 : ℝ) * ENNReal.ofReal E1 ^ (1 / 2 : ℝ) * x := by
          rw [hxx]
      _ ≤ _ := by
          rw [mul_assoc _ (c ^ _) y]
          exact mul_le_mul' le_rfl hx1
  have hT2b : ∀ i j : Fin 3, (∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      volume S ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal G1 ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
    intro i j
    rw [hvS, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc _ ≤ ENNReal.ofReal G1 ^ (1 / 2 : ℝ) * (vK ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (hDS i j) (by norm_num)) le_rfl
      _ ≤ ENNReal.ofReal G1 ^ (1 / 2 : ℝ) *
            (vK ^ (1 / 2 : ℝ) * (c ^ ((1 / 2 : ℝ) - 2 / 5) * y)) := by gcongr
      _ = _ := by ring
  have hT3b : ∀ i : Fin 3, (∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      volume S ^ (1 / 2 : ℝ) ≤
      Ff ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
    intro i
    rw [hvS, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc _ ≤ Ff ^ (1 / 2 : ℝ) * (vK ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (hfS i) (by norm_num)) le_rfl
      _ ≤ Ff ^ (1 / 2 : ℝ) * (vK ^ (1 / 2 : ℝ) * (c ^ ((1 / 2 : ℝ) - 2 / 5) * y)) := by gcongr
      _ = _ := by ring
  have hT4b : (∫⁻ z in S, ‖pF z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) * volume S ^ (1 / 3 : ℝ) ≤
      vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y := by
    rw [hvS, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc _ ≤ (vK ^ (1 / 2 : ℝ) * x ^ (1 / 6 : ℝ) * Q ^ (1 / 2 : ℝ)) *
            (vK ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ)) :=
          mul_le_mul' hPS le_rfl
      _ = vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
            (x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ)) := by ring
      _ = vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) * x ^ (1 / 2 : ℝ) := by
          rw [hx16]
      _ ≤ vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
            (c ^ ((1 / 2 : ℝ) - 2 / 5) * y) := by gcongr
      _ = _ := by ring
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
            (9 * ENNReal.ofReal E1) ^ (1 / 2 : ℝ) * ENNReal.ofReal E1 ^ (1 / 2 : ℝ) *
              c ^ ((1 : ℝ) - 2 / 5) * y +
          ENNReal.ofReal M1 * ∑ _i : Fin 3, ∑ _j : Fin 3,
            ENNReal.ofReal G1 ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y +
          ENNReal.ofReal M0 * ∑ _i : Fin 3,
            Ff ^ (1 / 2 : ℝ) * vK ^ (1 / 2 : ℝ) * c ^ ((1 / 2 : ℝ) - 2 / 5) * y +
          ENNReal.ofReal (3 * M1) * (vK ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * vK ^ (1 / 3 : ℝ) *
              c ^ ((1 / 2 : ℝ) - 2 / 5) * y)) +
          ENNReal.ofReal (3 * M1) * (MP5 * vK ^ (2 / 5 : ℝ)) * y := by
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
  have hrp : ∀ (z : ℝ≥0∞) (r : ℝ), 0 ≤ r → z ≠ ⊤ → z ^ r ≠ ⊤ := fun z r hr hz =>
    ENNReal.rpow_ne_top_of_nonneg hr hz
  have hcne : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hFf : Ff ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun i _ => ?_
    have hmem := (hf T1 hT1).eval i
    rw [← hl2 _ _ hmem.aestronglyMeasurable]
    exact hrp _ _ (by norm_num) hmem.eLpNorm_ne_top
  have hCenn : Cenn ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun _ _ =>
        ENNReal.sum_ne_top.2 fun _ _ => ?_)
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))
        (hrp _ _ (by norm_num) ENNReal.ofReal_ne_top)) (hrp _ _ (by norm_num) hcne)
    · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun _ _ =>
        ENNReal.sum_ne_top.2 fun _ _ => ?_)
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num) ENNReal.ofReal_ne_top)
        (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne)
    · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun _ _ => ?_)
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrp _ _ (by norm_num) hFf)
        (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne)
    · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
          (hrp _ _ (by norm_num) hvK) (hrp _ _ (by norm_num) hQfin.ne))
          (hrp _ _ (by norm_num) hvK)) (hrp _ _ (by norm_num) hcne)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hMP5.ne (hrp _ _ (by norm_num) hvK))
  change |g t - g s| ≤ Cenn.toReal * |t - s| ^ (2 / 5 : ℝ)
  calc |g t - g s| ≤ (∫⁻ z in S, ‖H z‖ₑ).toReal := hfinal
    _ ≤ (Cenn * y).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hCenn
        (hrp _ _ (by norm_num) ENNReal.ofReal_ne_top)) hlint
    _ = Cenn.toReal * |t - s| ^ (2 / 5 : ℝ) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hst',
          abs_of_nonneg hst']

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
    (((hw i).continuous_fderiv (by simp)).clm_apply continuous_const).bounded_above_of_compact_support
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
