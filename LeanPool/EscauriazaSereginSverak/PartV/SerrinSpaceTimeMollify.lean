/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution

/-!
# Slice-wise spatial mollification of space-time fields

Mollifying every time slice in space along the radii `1 / (n + 1)` converges in
every space-time `L^p`, `1 ≤ p < ∞`, on the slab. This removes the
mollification in the cross-testing identity of `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval Convolution
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The mollification radii `1 / (n + 1)`. -/
@[expose] def serrinRadius (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ)

theorem serrinRadius_pos (n : ℕ) : 0 < serrinRadius n := by
  unfold serrinRadius
  positivity

theorem serrinRadius_tendsto : Tendsto serrinRadius atTop (𝓝 0) := by
  unfold serrinRadius
  exact tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by push_cast; ring_nf

/-- The mollification kernel of radius `1 / (n + 1)`. -/
@[expose] def serrinKernel (n : ℕ) : Vec3 → ℝ :=
  CKN.mollifier (d := 3) (serrinRadius n) (serrinRadius_pos n)

/-- Mollification written as an integral against the translated kernel. -/
theorem serrin_mollify_eq_integral (g : Vec3 → ℝ) {ε : ℝ} (hε : 0 < ε) (y : Vec3) :
    CKN.mollify g ε hε y = ∫ x : Vec3, g x * CKN.mollifier (d := 3) ε hε (y - x) := by
  rw [CKN.mollify, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have h := integral_sub_left_eq_self
    (fun t : Vec3 => CKN.mollifier (d := 3) ε hε (y - t) * g (y - (y - t)))
    (μ := (volume : Measure Vec3)) y
  simp only [sub_sub_cancel] at h
  rw [h]
  congr 1
  funext x
  ring

/-- Slice-wise spatial mollification of a scalar space-time field. -/
@[expose] def serrinSM (f : ParabolicPoint → ℝ) (n : ℕ) : ParabolicPoint → ℝ :=
  fun z => CKN.mollify (fun x : Vec3 => f (x, z.2)) (serrinRadius n)
    (serrinRadius_pos n) z.1

theorem serrinSM_eq_integral (f : ParabolicPoint → ℝ) (n : ℕ) (y : Vec3) (τ : ℝ) :
    serrinSM f n (y, τ) = ∫ x : Vec3, f (x, τ) * serrinKernel n (y - x) :=
  serrin_mollify_eq_integral _ _ y

/-- The mollified component equals the slice-wise mollification of the component. -/
theorem serrinMol_kernel_eq (u : ParabolicPoint → Vec3) (n : ℕ) (k : Fin 3)
    (y : Vec3) (τ : ℝ) :
    serrinMol u (serrinKernel n) k y τ = serrinSM (fun z => u z k) n (y, τ) :=
  (serrinSM_eq_integral (fun z => u z k) n y τ).symm

/-- Slice-wise mollification preserves almost everywhere strong measurability on
the slab. -/
theorem serrinSM_aestronglyMeasurable {T : ℝ} {f : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (n : ℕ) :
    AEStronglyMeasurable (serrinSM f n)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  let u : ParabolicPoint → Vec3 := fun z _ => f z
  have hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (continuous_pi fun _ => continuous_id).comp_aestronglyMeasurable hf
  have hker : Continuous (serrinKernel n) :=
    (CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous
  have h := serrinMol_aestronglyMeasurable hu hker 0
  have hswap : AEStronglyMeasurable (fun z : Vec3 × ℝ => serrinMol u (serrinKernel n) 0 z.1 z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
    have hmp := (Measure.measurePreserving_swap (μ := (volume : Measure Vec3))
      (ν := volume.restrict (Ioo 0 T)))
    exact h.comp_measurePreserving hmp
  have hfun : (fun z : Vec3 × ℝ => serrinMol u (serrinKernel n) 0 z.1 z.2) =
      fun z => serrinSM f n z := by
    funext z
    exact serrinMol_kernel_eq u n 0 z.1 z.2
  rw [hfun] at hswap
  have h' : AEStronglyMeasurable (serrinSM f n)
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.restrict_univ]
    exact hswap
  rw [Measure.prod_restrict] at h'
  exact h'

private theorem serrin_eLpNorm_rpow_eq {g : Vec3 → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hptop : p ≠ ⊤) (hg : AEStronglyMeasurable g volume) :
    eLpNorm g p volume ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg, ← ENNReal.rpow_mul,
    one_div_mul_cancel hr.ne', ENNReal.rpow_one]

/-- Slice-wise spatial mollification converges in space-time `L^p` on the slab,
product-coordinate form. -/
theorem serrinSM_tendsto_prod {T : ℝ} {g : Vec3 × ℝ → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hg : MemLp g p ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hSM : ∀ n, AEStronglyMeasurable
      (fun z : Vec3 × ℝ => CKN.mollify (fun x : Vec3 => g (x, z.2)) (serrinRadius n)
        (serrinRadius_pos n) z.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))) :
    Tendsto (fun n => eLpNorm (fun z : Vec3 × ℝ =>
        CKN.mollify (fun x : Vec3 => g (x, z.2)) (serrinRadius n) (serrinRadius_pos n) z.1
          - g z) p ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
      atTop (𝓝 0) := by
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  set r : ℝ := p.toReal with hrdef
  have hr : 0 < r := ENNReal.toReal_pos hp0 hptop
  let h : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    CKN.mollify (fun x : Vec3 => g (x, z.2)) (serrinRadius n) (serrinRadius_pos n) z.1 - g z
  have hhm (n : ℕ) : AEStronglyMeasurable (h n) ν := (hSM n).sub hg.aestronglyMeasurable
  -- reduce to the integral of the `r`-th power
  have hpow : ∀ n, eLpNorm (h n) p ν = (∫⁻ z, ‖h n z‖ₑ ^ r ∂ν) ^ (1 / r) := fun n =>
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hhm n)
  simp_rw [show (fun n => eLpNorm (fun z : Vec3 × ℝ =>
      CKN.mollify (fun x : Vec3 => g (x, z.2)) (serrinRadius n) (serrinRadius_pos n) z.1
        - g z) p ν) = fun n => eLpNorm (h n) p ν from rfl, hpow]
  have hzero : (0 : ℝ≥0∞) = 0 ^ (1 / r) := (ENNReal.zero_rpow_of_pos (by positivity)).symm
  rw [hzero]
  refine (ENNReal.continuous_rpow_const.tendsto 0).comp ?_
  -- Tonelli in the time variable
  have hmeasPow (n : ℕ) : AEMeasurable (fun z => ‖h n z‖ₑ ^ r) ν :=
    (hhm n).enorm.pow_const r
  have hTon (n : ℕ) : (∫⁻ z, ‖h n z‖ₑ ^ r ∂ν) =
      ∫⁻ τ, ∫⁻ x, ‖h n (x, τ)‖ₑ ^ r ∂volume ∂(volume.restrict (Ioo 0 T)) :=
    lintegral_prod_symm _ (hmeasPow n)
  simp_rw [hTon]
  -- the slices of `g`
  have hgm : AEMeasurable (fun z => ‖g z‖ₑ ^ r) ν := hg.aestronglyMeasurable.enorm.pow_const r
  have hgfin : (∫⁻ z, ‖g z‖ₑ ^ r ∂ν) ≠ ⊤ := by
    have h1 := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg.aestronglyMeasurable] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).mp h1 |>.ne
  set G : ℝ → ℝ≥0∞ := fun τ => ∫⁻ x, ‖g (x, τ)‖ₑ ^ r ∂volume
  have hGm : AEMeasurable G (volume.restrict (Ioo 0 T)) := hgm.lintegral_prod_left'
  have hGfin : (∫⁻ τ, G τ ∂(volume.restrict (Ioo 0 T))) ≠ ⊤ := by
    rw [← lintegral_prod_symm _ hgm]
    exact hgfin
  have hslice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x => g (x, τ)) volume ∧ G τ < ⊤ := by
    filter_upwards [hg.aestronglyMeasurable.prodMk_right, ae_lt_top' hGm hGfin] with τ h1 h2
    exact ⟨h1, h2⟩
  have hsliceLp : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), MemLp (fun x => g (x, τ)) p volume := by
    filter_upwards [hslice] with τ ⟨hm, hG⟩
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hm]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hG.ne
  have hlim : Tendsto (fun n => ∫⁻ τ, ∫⁻ x, ‖h n (x, τ)‖ₑ ^ r ∂volume
      ∂(volume.restrict (Ioo 0 T))) atTop (𝓝 (∫⁻ _τ, (0 : ℝ≥0∞) ∂(volume.restrict (Ioo 0 T)))) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun τ => 2 ^ r * G τ)
      (fun n => (hmeasPow n).lintegral_prod_left') ?_ ?_ ?_
    · intro n
      filter_upwards [hsliceLp] with τ hτ
      have hmol := CKN.young_convolution_nonneg_integral_one_of_aemeasurable (d := 3)
        (p := p) hp hptop (CKN.mollifier_nonneg (serrinRadius_pos n))
        ((CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous
          |>.integrable_of_hasCompactSupport (CKN.mollifier_hasCompactSupport _))
        (CKN.mollifier_integral_one (serrinRadius_pos n))
        (CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n) (n := 0)).continuous.measurable
        hτ.aestronglyMeasurable.aemeasurable
      have hmolm : AEStronglyMeasurable (fun x => CKN.mollify (fun x : Vec3 => g (x, τ))
          (serrinRadius n) (serrinRadius_pos n) x) volume :=
        (CKN.mollify_continuous (serrinRadius_pos n)
          (hτ.locallyIntegrable hp)).aestronglyMeasurable
      have htri : eLpNorm (fun x => h n (x, τ)) p volume ≤
          2 * eLpNorm (fun x => g (x, τ)) p volume := by
        calc
          eLpNorm (fun x => h n (x, τ)) p volume ≤
              eLpNorm (fun x => CKN.mollify (fun x : Vec3 => g (x, τ)) (serrinRadius n)
                (serrinRadius_pos n) x) p volume +
                eLpNorm (fun x => g (x, τ)) p volume :=
            eLpNorm_sub_le hp
          _ ≤ eLpNorm (fun x => g (x, τ)) p volume + eLpNorm (fun x => g (x, τ)) p volume := by
            gcongr
            simpa [CKN.mollify, CKN.mollifier] using hmol
          _ = 2 * eLpNorm (fun x => g (x, τ)) p volume := by rw [two_mul]
      have hl := serrin_eLpNorm_rpow_eq hp0 hptop (hmolm.sub hτ.aestronglyMeasurable)
      have hr' := serrin_eLpNorm_rpow_eq hp0 hptop hτ.aestronglyMeasurable
      change (∫⁻ x, ‖h n (x, τ)‖ₑ ^ r) ≤ 2 ^ r * G τ
      calc
        (∫⁻ x, ‖h n (x, τ)‖ₑ ^ r) = eLpNorm (fun x => h n (x, τ)) p volume ^ r := hl.symm
        _ ≤ (2 * eLpNorm (fun x => g (x, τ)) p volume) ^ r := by gcongr
        _ = 2 ^ r * G τ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, hr']
    · rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le (by simp))]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr.le (by simp)) hGfin
    · filter_upwards [hsliceLp] with τ hτ
      have hc := CKN.tendsto_eLpNorm_sub_zero_mollify hp hptop hτ serrinRadius_tendsto
        serrinRadius_pos
      have hmolm (n : ℕ) : AEStronglyMeasurable (fun x => CKN.mollify (fun x : Vec3 => g (x, τ))
          (serrinRadius n) (serrinRadius_pos n) x) volume :=
        (CKN.mollify_continuous (serrinRadius_pos n)
          (hτ.locallyIntegrable hp)).aestronglyMeasurable
      have heq (n : ℕ) : (∫⁻ x, ‖h n (x, τ)‖ₑ ^ r) =
          eLpNorm (fun x => CKN.mollify (fun x : Vec3 => g (x, τ)) (serrinRadius n)
            (serrinRadius_pos n) x - g (x, τ)) p volume ^ r :=
        (serrin_eLpNorm_rpow_eq hp0 hptop ((hmolm n).sub hτ.aestronglyMeasurable)).symm
      simp_rw [heq]
      have h0 : (0 : ℝ≥0∞) = 0 ^ r := (ENNReal.zero_rpow_of_pos hr).symm
      rw [h0]
      exact (ENNReal.continuous_rpow_const.tendsto 0).comp hc
  simpa using hlim

/-- The parabolic slab measure is the product of Lebesgue measure in space with
Lebesgue measure on the time interval. -/
theorem serrin_slab_measure_eq (T : ℝ) :
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :
      Measure ParabolicPoint) =
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)) : Measure (Vec3 × ℝ)) := by
  show (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Slice-wise spatial mollification converges in space-time `L^p` on the slab. -/
theorem serrinSM_tendsto {T : ℝ} {f : ParabolicPoint → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    Tendsto (fun n => eLpNorm (fun z => serrinSM f n z - f z) p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (𝓝 0) := by
  have hSM (n : ℕ) := serrinSM_aestronglyMeasurable hf.aestronglyMeasurable n
  rw [serrin_slab_measure_eq] at hf hSM ⊢
  exact serrinSM_tendsto_prod (g := fun z : Vec3 × ℝ => f z) hp hptop hf hSM

end ESS
