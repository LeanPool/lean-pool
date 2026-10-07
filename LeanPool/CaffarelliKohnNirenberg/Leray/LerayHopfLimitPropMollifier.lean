/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropTransport
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# The mollified initial data converge in `L²`

The profile of `eq:reg-mollifier` is a nonnegative, normalized kernel
supported in the unit ball, so its dilates form an approximate identity in
`L²`. This is the convergence `J_ε a → a` used in the proof of
`prop:leray-hopf-limit`: it is first checked on continuous compactly supported
fields by uniform continuity, and then extended by density and the `L²`
contraction of the mollifier.
-/

public section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology Convolution
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem kernel_continuous (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    Continuous (regMollifierKernel ρ ε hε) := by
  unfold regMollifierKernel
  exact (contDiff_const.mul (ρ.smooth.comp (contDiff_const_smul _))).continuous

private theorem kernel_support (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    Function.support (regMollifierKernel ρ ε hε) ⊆ ball (0 : L2Vec3) ε := by
  intro x hx
  have hρ : ρ.rho (ε⁻¹ • x) ≠ 0 := by
    intro h
    apply hx
    simp only [regMollifierKernel, h, mul_zero]
  have hmem : ε⁻¹ • x ∈ ball (0 : L2Vec3) 1 :=
    ρ.support_unit (subset_tsupport _ hρ)
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε] at hmem
  rw [mem_ball_zero_iff]
  have h := (inv_mul_lt_iff₀ hε).mp hmem
  linarith only [h]

/-- The vector mollifier is the convolution with the dilated kernel acting by
scalar multiplication. -/
theorem lerayHopfLimit_regMollifyVector_eq_convolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (f : L2Vec3 → L2Vec3) :
    regMollifyVector ρ ε hε f =
      regMollifierKernel ρ ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext x
  rfl

private theorem regMollifyVector_dist_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {g : L2Vec3 → L2Vec3} (hg : AEStronglyMeasurable g volume)
    {x₀ z₀ : L2Vec3} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x ∈ ball x₀ ε, dist (g x) z₀ ≤ η) :
    dist (regMollifyVector ρ ε hε g x₀) z₀ ≤ η := by
  rw [lerayHopfLimit_regMollifyVector_eq_convolution]
  exact dist_convolution_le hη (kernel_support ρ ε hε)
    (regMollifierKernel_nonneg ρ ε hε) (regMollifierKernel_integral_eq_one ρ ε hε) hg h

/-- The mollifier converges in `L²` on continuous compactly supported fields. -/
theorem lerayHopfLimit_regMollifyVector_tendsto_of_compact
    (ρ : RegMollifierProfile) {g : L2Vec3 → L2Vec3}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (εs : ℕ → ℝ) (hpos : ∀ n, 0 < εs n) (hlim : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (regMollifyVector ρ (εs n) (hpos n) g - g) 2 volume)
      atTop (𝓝 0) := by
  let K : Set L2Vec3 := tsupport g
  let S : Set L2Vec3 := cthickening 1 K
  have hS : IsCompact S := hgc.isCompact.cthickening
  have hSfin : volume S < ⊤ := hS.measure_lt_top
  let A : ℝ≥0∞ := volume S ^ (2 : ℝ≥0∞).toReal⁻¹
  have hA : A < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSfin.ne
  have hgu : UniformContinuous g := hgc.uniformContinuous_of_continuous hg
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall (fun _ => le_top)
  have he' : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop
  let η : ℝ := e.toReal / (A.toReal + 1)
  have hη : 0 < η := div_pos he' (by positivity)
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hgu η hη
  have hev : ∀ᶠ n in atTop, εs n < min δ 1 :=
    (tendsto_order.1 hlim).2 _ (lt_min hδ one_pos)
  filter_upwards [hev] with n hn
  have hnδ : εs n < δ := lt_of_lt_of_le hn (min_le_left _ _)
  have hn1 : εs n < 1 := lt_of_lt_of_le hn (min_le_right _ _)
  set T := regMollifyVector ρ (εs n) (hpos n) g with hT
  have hTmeas : AEStronglyMeasurable (T - g) volume :=
    (regMollifyVector_aestronglyMeasurable ρ (εs n) (hpos n)
      (hg.memLp_of_hasCompactSupport hgc)).sub hg.aestronglyMeasurable
  have hpt : ∀ x₀, ‖(T - g) x₀‖ ≤ η := by
    intro x₀
    rw [Pi.sub_apply, ← dist_eq_norm]
    refine regMollifyVector_dist_le ρ (εs n) (hpos n) hg.aestronglyMeasurable hη.le ?_
    intro x hx
    exact (hδg (lt_trans (mem_ball.mp hx) hnδ)).le
  have hsupp : Function.support (T - g) ⊆ S := by
    intro x₀ hx₀
    by_contra hnot
    apply hx₀
    have hfar : ∀ x ∈ ball x₀ (εs n), g x = 0 := by
      intro x hx
      by_contra hgx
      apply hnot
      exact mem_cthickening_of_dist_le x₀ x 1 K (subset_tsupport _ hgx)
        (le_of_lt (lt_trans (by rw [dist_comm]; exact mem_ball.mp hx) hn1))
    have hg0 : g x₀ = 0 := hfar x₀ (mem_ball_self (hpos n))
    have hT0 : dist (T x₀) 0 ≤ 0 :=
      regMollifyVector_dist_le ρ (εs n) (hpos n) hg.aestronglyMeasurable le_rfl
        (fun x hx => by rw [hfar x hx, dist_self])
    rw [Pi.sub_apply, hg0, sub_zero]
    exact dist_le_zero.mp hT0
  rw [← eLpNorm_restrict_eq_of_support_subset hTmeas hsupp]
  have hbound := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) (μ := volume.restrict S)
    hTmeas.restrict (Filter.Eventually.of_forall hpt)
  refine hbound.trans ?_
  rw [Measure.restrict_apply_univ]
  change A * ENNReal.ofReal η ≤ e
  have hAeq : A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA.ne).symm
  rw [hAeq, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [← ENNReal.ofReal_toReal hetop]
  apply ENNReal.ofReal_le_ofReal
  have hA0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hkey : A.toReal * η ≤ (A.toReal + 1) * η :=
    mul_le_mul_of_nonneg_right (by linarith only) hη.le
  have hcalc : (A.toReal + 1) * η = e.toReal := by
    simp only [η]
    field_simp
  linarith only [hkey, hcalc]

/-- The mollifier converges in `L²` on every `L²` field. -/
theorem lerayHopfLimit_regMollifyVector_tendsto
    (ρ : RegMollifierProfile) {f : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume)
    (εs : ℕ → ℝ) (hpos : ∀ n, 0 < εs n) (hlim : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (regMollifyVector ρ (εs n) (hpos n) f - f) 2 volume)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall (fun _ => le_top)
  have he4 : e / 4 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, he.ne', ENNReal.ofNat_ne_top, or_self,
      not_false_eq_true]
  obtain ⟨g, hgc, hfg, hg, hgmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) he4
  have hconv := lerayHopfLimit_regMollifyVector_tendsto_of_compact ρ hg hgc εs hpos hlim
  have hev := (ENNReal.tendsto_nhds_zero.mp hconv) (e / 4)
    (ENNReal.div_pos he.ne' (by norm_num))
  filter_upwards [hev] with n hn
  set ε := εs n
  have hfgmem : MemLp (f - g) 2 volume := hf.sub hgmem
  have hlin : regMollifyVector ρ ε (hpos n) f =
      regMollifyVector ρ ε (hpos n) g + regMollifyVector ρ ε (hpos n) (f - g) := by
    have hkc : HasCompactSupport (regMollifierKernel ρ ε (hpos n)) := by
      unfold regMollifierKernel
      exact (ρ.compact.comp_smul (inv_ne_zero (hpos n).ne')).mul_left
    have hexg : ConvolutionExists (regMollifierKernel ρ ε (hpos n)) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hkc.convolutionExists_left _
        (kernel_continuous ρ ε (hpos n)) (hgmem.locallyIntegrable (by norm_num))
    have hexfg : ConvolutionExists (regMollifierKernel ρ ε (hpos n)) (f - g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hkc.convolutionExists_left _
        (kernel_continuous ρ ε (hpos n)) (hfgmem.locallyIntegrable (by norm_num))
    simp only [lerayHopfLimit_regMollifyVector_eq_convolution]
    rw [← hexg.distrib_add hexfg, add_sub_cancel]
  have hsplit : regMollifyVector ρ ε (hpos n) f - f =
      (regMollifyVector ρ ε (hpos n) (f - g) + (regMollifyVector ρ ε (hpos n) g - g)) +
        (g - f) := by
    rw [hlin]
    abel
  have hTfg := regMollifyVector_eLpNorm_two_le ρ ε (hpos n) hfgmem
  rw [hsplit]
  calc eLpNorm ((regMollifyVector ρ ε (hpos n) (f - g) +
          (regMollifyVector ρ ε (hpos n) g - g)) + (g - f)) 2 volume
      ≤ eLpNorm (regMollifyVector ρ ε (hpos n) (f - g) +
          (regMollifyVector ρ ε (hpos n) g - g)) 2 volume + eLpNorm (g - f) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (regMollifyVector ρ ε (hpos n) (f - g)) 2 volume +
          eLpNorm (regMollifyVector ρ ε (hpos n) g - g) 2 volume) +
          eLpNorm (g - f) 2 volume := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (e / 4 + e / 4) + e / 4 := by
        gcongr
        · exact hTfg.trans hfg
        · rw [eLpNorm_sub_comm]
          exact hfg
    _ ≤ e := by
        rw [← ENNReal.add_div, ← ENNReal.add_div]
        apply ENNReal.div_le_of_le_mul
        calc e + e + e ≤ e + e + e + e := le_add_right le_rfl
          _ = e * 4 := by ring

/-- The mollified initial fields converge weakly in `L²`: their pairings with
every `L²` field converge. -/
theorem lerayHopfLimit_mollifiedInitial_pairing_tendsto
    (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : MemLp a 2 volume)
    (εs : ℕ → ℝ) (hpos : ∀ n, 0 < εs n) (hlim : Tendsto εs atTop (𝓝 0))
    (w : Vec3 → Vec3) (hw : MemLp w 2 volume) :
    Tendsto (fun n => ∫ x, ∑ i : Fin 3,
        regUniformMollifiedInitial ρ (εs n) (hpos n) a x i * w x i)
      atTop (𝓝 (∫ x, ∑ i : Fin 3, a x i * w x i)) := by
  let f : L2Vec3 → L2Vec3 := regUniformSpatialField a
  have hf : MemLp f 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) 2 volume :=
      ha.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hJ : ∀ n, MemLp (regUniformMollifiedInitial ρ (εs n) (hpos n) a) 2 volume := by
    intro n
    refine MemLp.of_eval (fun i => ?_)
    exact (lerayHopfLimit_mollifiedInitial_component_sq_le ρ (εs n) (hpos n) ha i).1
  let E : ∀ g : Vec3 → Vec3, MemLp g 2 volume → Lp L2Vec3 2 (volume : Measure Vec3) :=
    fun g hg => (lerayHopfLimit_toLp_memLp hg).toLp (fun x => WithLp.toLp 2 (g x))
  have hinner : ∀ g (hg : MemLp g 2 volume),
      inner ℝ (E g hg) (E w hw) = ∫ x, ∑ i : Fin 3, g x i * w x i := by
    intro g hg
    simpa using inner_toLp_vec3_eq_integral_dot_measure volume
      (fun x => (WithLp.toLp 2 (g x) : L2Vec3)) (fun x => WithLp.toLp 2 (w x))
      (lerayHopfLimit_toLp_memLp hg) (lerayHopfLimit_toLp_memLp hw)
  have hconv : Tendsto (fun n => E _ (hJ n)) atTop (𝓝 (E a ha)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm : ∀ n, ‖E _ (hJ n) - E a ha‖ =
        (eLpNorm (regMollifyVector ρ (εs n) (hpos n) f - f) 2 volume).toReal := by
      intro n
      change ‖(lerayHopfLimit_toLp_memLp (hJ n)).toLp _ -
        (lerayHopfLimit_toLp_memLp ha).toLp _‖ = _
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      congr 1
      have hmeas : AEStronglyMeasurable
          (regMollifyVector ρ (εs n) (hpos n) f - f) volume :=
        (regMollifyVector_aestronglyMeasurable ρ (εs n) (hpos n) hf).sub
          hf.aestronglyMeasurable
      exact eLpNorm_comp_measurePreserving hmeas vec3ToL2Vec3_measurePreserving
    simp only [hnorm]
    have h := lerayHopfLimit_regMollifyVector_tendsto ρ hf εs hpos hlim
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    exact h'
  have hlimit := (hconv.inner (𝕜 := ℝ) (tendsto_const_nhds (x := E w hw)))
  rw [hinner a ha] at hlimit
  exact hlimit.congr (fun n => hinner _ (hJ n))

end CKN.Leray

end
