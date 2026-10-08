/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitJConvContraction
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Strong `L³` convergence of the regularized transport velocities

In `prop:leray-limit` the transport velocities J_{ε_n} u_{ε_n} converge to
the limit velocity strongly in `L³` on every finite slab. The argument
approximates the limit by a continuous compactly supported field, on which the
regularization converges uniformly with supports in a fixed compact set, and
controls the remaining terms by the space-time `L³` contraction and the strong
`L³` convergence of the velocities themselves.
-/

public section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology Convolution
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- For a continuous compactly supported space-time field, the regularized
transport velocities converge to the field in `L³` on a finite slab. -/
theorem lerayLimit_regUniformMollifiedVelocity_tendsto_of_compact
    (ρ : RegMollifierProfile) (T : ℝ)
    (g : Vec3 × ℝ → Vec3) (hg : Continuous g) (hgc : HasCompactSupport g)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (regUniformMollifiedVelocity ρ (ε n) (hε n)
          (fun z : ParabolicPoint => g (z.1, z.2)) -
        fun z : ParabolicPoint => g (z.1, z.2)) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
      atTop (𝓝 0) := by
  let gP : ParabolicPoint → Vec3 := fun z => g (z.1, z.2)
  have hgPm : Measurable gP := hg.measurable
  let S : Set (Vec3 × ℝ) := cthickening 1 (tsupport g)
  have hS : IsCompact S := hgc.isCompact.cthickening
  have hSmeas : MeasurableSet S := hS.isClosed.measurableSet
  have hSfin : (volume : Measure (Vec3 × ℝ)) S < ⊤ := hS.measure_lt_top
  let A : ℝ≥0∞ := (volume : Measure (Vec3 × ℝ)) S ^ (1 / (3 : ℝ≥0∞).toReal)
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
  have hev : ∀ᶠ n in atTop, ε n < min δ 1 :=
    (tendsto_order.1 hlim).2 _ (lt_min hδ one_pos)
  filter_upwards [hev] with n hn
  have hnδ : ε n < δ := lt_of_lt_of_le hn (min_le_left _ _)
  have hn1 : ε n < 1 := lt_of_lt_of_le hn (min_le_right _ _)
  obtain ⟨hκ0, -, -, hκ1, hκsupp, -⟩ :=
    lerayLimit_regMollifierKernel_vec3_props ρ (ε n) (hε n)
  have hslice (t : ℝ) : AEStronglyMeasurable (fun y : Vec3 => gP (y, t)) volume :=
    (hg.comp (Continuous.prodMk_left t)).aestronglyMeasurable
  have hpoint : ∀ z : ParabolicPoint,
      ‖(regUniformMollifiedVelocity ρ (ε n) (hε n) gP - gP) z‖ ≤
        (S : Set ParabolicPoint).indicator (fun _ => η) z := by
    suffices h : ∀ (x : Vec3) (t : ℝ),
        ‖regUniformMollifiedVelocity ρ (ε n) (hε n) gP (x, t) - g (x, t)‖ ≤
          S.indicator (fun _ => η) (x, t) from
      fun z => h z.1 z.2
    intro x t
    rw [← dist_eq_norm, lerayLimit_regUniformMollifiedVelocity_eq_convolution]
    by_cases hz : ((x, t) : Vec3 × ℝ) ∈ S
    · rw [indicator_of_mem hz]
      refine dist_convolution_le hη.le hκsupp hκ0 hκ1 (hslice t) ?_
      intro y hy
      have hdist : dist ((y, t) : Vec3 × ℝ) (x, t) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact lt_trans (mem_ball.mp hy) hnδ
      exact (hδg hdist).le
    · rw [indicator_of_notMem hz]
      have hgx : g (x, t) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hmem => hz (self_subset_cthickening _ hmem))
      have hfar : ∀ y ∈ ball x (ε n), dist (gP (y, t)) (0 : Vec3) ≤ 0 := by
        intro y hy
        have hgy : g (y, t) = 0 := by
          by_contra hne
          apply hz
          refine mem_cthickening_of_dist_le (x, t) (y, t) 1 (tsupport g)
            (subset_tsupport _ hne) ?_
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
          exact (lt_trans (by rw [dist_comm]; exact mem_ball.mp hy) hn1).le
        change dist (g (y, t)) 0 ≤ 0
        rw [hgy, dist_self]
      have hzero := dist_convolution_le le_rfl hκsupp hκ0 hκ1 (hslice t) hfar
      rw [hgx]
      exact hzero
  have hmeas : AEStronglyMeasurable
      (regUniformMollifiedVelocity ρ (ε n) (hε n) gP - gP)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    ((lerayLimit_regUniformMollifiedVelocity_stronglyMeasurable ρ (ε n) (hε n)
      hgPm).aestronglyMeasurable.sub hgPm.aestronglyMeasurable)
  calc
    eLpNorm (regUniformMollifiedVelocity ρ (ε n) (hε n) gP - gP) 3
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤
        eLpNorm ((S : Set ParabolicPoint).indicator (fun _ => η)) 3
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      eLpNorm_mono_real hmeas hpoint
    _ ≤ eLpNorm ((S : Set ParabolicPoint).indicator (fun _ => η)) 3
          (volume : Measure ParabolicPoint) :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (S.indicator (fun _ : Vec3 × ℝ => η)) 3
          (volume : Measure (Vec3 × ℝ)) := rfl
    _ = ‖η‖ₑ * A := by
      rw [eLpNorm_indicator_const hSmeas.nullMeasurableSet
        (by norm_num) (by norm_num)]
    _ ≤ e := by
      rw [Real.enorm_eq_ofReal hη.le]
      have hAeq : A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA.ne).symm
      rw [hAeq, ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_toReal hetop]
      apply ENNReal.ofReal_le_ofReal
      have hA0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
      have hkey : η * A.toReal ≤ η * (A.toReal + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) hη.le
      have hcalc : η * (A.toReal + 1) = e.toReal := by
        simp only [η]
        field_simp
      linarith only [hkey, hcalc]

/-- The `L³` assertion of `prop:leray-limit` for the transport velocities:
from the strong `L³` convergence of the regularized velocities on a finite
slab, the regularized transport velocities are cubically integrable there, the
limit is cubically integrable, and the transport velocities converge to the
limit in `L³`. -/
theorem lerayLimit_regUniformMollifiedVelocity_tendsto_three
    (ρ : RegMollifierProfile) (T : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (U : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (hUcont : ∀ n, ∀ i : Fin 3, ContinuousOn (fun z => U n z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUslice : ∀ n, ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => U n (x, t)) 2 volume)
    (hU3 : ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hconv : Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
      atTop (𝓝 0)) :
    (∀ n, MemLp (regUniformMollifiedVelocity ρ (ε n) (hε n) (U n)) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
    MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
    Tendsto (fun n => eLpNorm
      (regUniformMollifiedVelocity ρ (ε n) (hε n) (U n) - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
      atTop (𝓝 0) := by
  classical
  let slab : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.restrict slab
  let P : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  let V : ℕ → ParabolicPoint → Vec3 := fun n => P.piecewise (U n) 0
  let J : ℕ → (ParabolicPoint → Vec3) → ParabolicPoint → Vec3 := fun n f =>
    regUniformMollifiedVelocity ρ (ε n) (hε n) f
  have hslabMeas : MeasurableSet slab :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hPmeas : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Ioi
  have hVmeas (n : ℕ) : Measurable (V n) :=
    (continuousOn_pi.mpr (hUcont n)).measurable_piecewise continuousOn_const hPmeas
  have hpos : ∀ᵐ z ∂μ, 0 < z.2 := by
    filter_upwards [ae_restrict_mem hslabMeas] with z hz
    exact hz.2.1
  have hVeq (n : ℕ) (z : ParabolicPoint) (hz : 0 < z.2) : V n z = U n z :=
    piecewise_eq_of_mem _ _ _ (show z ∈ P from ⟨Set.mem_univ _, hz⟩)
  have hJeq (n : ℕ) (z : ParabolicPoint) (hz : 0 < z.2) :
      J n (U n) z = J n (V n) z := by
    change J n (U n) ((z.1, z.2) : ParabolicPoint) =
      J n (V n) ((z.1, z.2) : ParabolicPoint)
    simp only [J]
    rw [lerayLimit_regUniformMollifiedVelocity_eq_convolution,
      lerayLimit_regUniformMollifiedVelocity_eq_convolution]
    congr 1
    funext y
    exact (hVeq n (y, z.2) hz).symm
  have hUV (n : ℕ) : U n =ᵐ[μ] V n := by
    filter_upwards [hpos] with z hz
    exact (hVeq n z hz).symm
  have hJUV (n : ℕ) : J n (U n) =ᵐ[μ] J n (V n) := by
    filter_upwards [hpos] with z hz
    exact hJeq n z hz
  have hcontract (n : ℕ) (f : ParabolicPoint → Vec3) (hf : Measurable f) :
      eLpNorm (J n f) 3 μ ≤ eLpNorm f 3 μ :=
    lerayLimit_regUniformMollifiedVelocity_spaceTime_eLpNorm_le ρ (ε n) (hε n)
      hf T
  -- The transport velocities are cubically integrable.
  have hJ3 (n : ℕ) : MemLp (J n (U n)) 3 μ := by
    have hV3 : MemLp (V n) 3 μ := (hU3 n).ae_eq (hUV n)
    have hJV : MemLp (J n (V n)) 3 μ :=
      lt_of_le_of_lt (hcontract n (V n) (hVmeas n)) hV3
    exact hJV.ae_eq (hJUV n).symm
  -- The limit is cubically integrable.
  have hconv3 : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_ofNat] using hconv
  have hu3 : MemLp u 3 μ := by
    obtain ⟨n, hn⟩ := (hconv3.eventually (gt_mem_nhds zero_lt_one)).exists
    have hdiff : MemLp (U n - u) 3 μ := lt_trans hn ENNReal.one_lt_top
    have hsplit : u = U n - (U n - u) := by
      funext z
      simp
    rw [hsplit]
    exact (hU3 n).sub hdiff
  refine ⟨hJ3, hu3, ?_⟩
  -- Strong convergence.
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall (fun _ => le_top)
  let e4 : ℝ≥0∞ := e / 4
  have he4 : 0 < e4 := ENNReal.div_pos he.ne' (by norm_num)
  have hw : MemLp (fun q : Vec3 × ℝ => slab.indicator u ((q.1, q.2) : ParabolicPoint))
      3 (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hslabMeas).2 hu3
  obtain ⟨g, hgc, hgclose, hgcont, -⟩ :=
    hw.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) he4.ne'
  let gP : ParabolicPoint → Vec3 := fun z => g (z.1, z.2)
  have hgPm : Measurable gP := hgcont.measurable
  have hug : eLpNorm (u - gP) 3 μ ≤ e4 := by
    have hae : u - gP =ᵐ[μ] slab.indicator u - gP := by
      filter_upwards [ae_restrict_mem hslabMeas] with z hz
      simp [indicator_of_mem hz]
    rw [eLpNorm_congr_ae hae]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hgclose
  have hJg := (ENNReal.tendsto_nhds_zero.mp
    (lerayLimit_regUniformMollifiedVelocity_tendsto_of_compact ρ T g hgcont hgc
      ε hε hlim)) e4 he4
  have hUu := (ENNReal.tendsto_nhds_zero.mp hconv3) e4 he4
  filter_upwards [hJg, hUu] with n hJgn hUun
  have hsliceV (t : ℝ) (ht : 0 < t) :
      LocallyIntegrable (fun y : Vec3 => V n (y, t)) volume := by
    have hfun : (fun y : Vec3 => V n (y, t)) = fun y : Vec3 => U n (y, t) := by
      funext y
      exact hVeq n (y, t) ht
    rw [hfun]
    exact (hUslice n t ht.le).locallyIntegrable (by norm_num)
  obtain ⟨-, hκc, -, -, -, hκcs⟩ :=
    lerayLimit_regMollifierKernel_vec3_props ρ (ε n) (hε n)
  have hlin (z : ParabolicPoint) (hz : 0 < z.2) :
      J n (V n) z - J n gP z = J n (V n - gP) z := by
    change J n (V n) ((z.1, z.2) : ParabolicPoint) -
        J n gP ((z.1, z.2) : ParabolicPoint) =
      J n (V n - gP) ((z.1, z.2) : ParabolicPoint)
    set x := z.1
    set t := z.2 with ht_def
    simp only [J]
    rw [lerayLimit_regUniformMollifiedVelocity_eq_convolution,
      lerayLimit_regUniformMollifiedVelocity_eq_convolution,
      lerayLimit_regUniformMollifiedVelocity_eq_convolution]
    have hg1 : LocallyIntegrable (fun y : Vec3 => gP (y, t)) volume :=
      (hgcont.comp (Continuous.prodMk_left t)).locallyIntegrable
    have hd : LocallyIntegrable (fun y : Vec3 => (V n - gP) (y, t)) volume :=
      (hsliceV t hz).sub hg1
    have hsum : (fun y : Vec3 => V n (y, t)) =
        (fun y : Vec3 => (V n - gP) (y, t)) + fun y : Vec3 => gP (y, t) := by
      funext y
      exact (sub_add_cancel (V n (y, t)) (gP (y, t))).symm
    rw [hsum, ConvolutionExistsAt.distrib_add
      (hκcs.convolutionExists_left _ hκc hd x)
      (hκcs.convolutionExists_left _ hκc hg1 x), add_sub_cancel_right]
  have hdecomp : J n (U n) - u =ᵐ[μ]
      (J n (V n - gP) + (J n gP - gP)) + (gP - u) := by
    filter_upwards [hpos] with z hz
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← hlin z hz, hJeq n z hz]
    abel
  have hVg : eLpNorm (V n - gP) 3 μ ≤ e4 + e4 := by
    have hae : V n - gP =ᵐ[μ] (U n - u) + (u - gP) := by
      filter_upwards [hUV n] with z hz
      simp [hz]
    rw [eLpNorm_congr_ae hae]
    exact (eLpNorm_add_le (by norm_num)).trans (add_le_add hUun hug)
  have hgu' : eLpNorm (gP - u) 3 μ ≤ e4 := by
    rw [eLpNorm_sub_comm]
    exact hug
  have hfour : e4 + e4 + e4 + e4 = e := by
    have h4 : (4 : ℝ≥0∞) * (e / 4) = e :=
      ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    calc
      e4 + e4 + e4 + e4 = 4 * (e / 4) := by
        simp only [e4]
        ring
      _ = e := h4
  change eLpNorm (J n (U n) - u) 3 μ ≤ e
  rw [eLpNorm_congr_ae hdecomp]
  calc
    eLpNorm ((J n (V n - gP) + (J n gP - gP)) + (gP - u)) 3 μ ≤
        (eLpNorm (J n (V n - gP)) 3 μ + eLpNorm (J n gP - gP) 3 μ) +
          eLpNorm (gP - u) 3 μ :=
      (eLpNorm_add_le (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)
    _ ≤ ((e4 + e4) + e4) + e4 := by
      gcongr
      exact (hcontract n (V n - gP) ((hVmeas n).sub hgPm)).trans hVg
    _ = e := by rw [← hfour]

end CKN.Leray

end
