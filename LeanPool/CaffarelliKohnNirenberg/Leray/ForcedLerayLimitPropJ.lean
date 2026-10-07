/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitJConvLimit
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Forced Leray Limit Prop J

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Strong `L³` convergence of the regularized velocities implies strong
`L³` convergence of their spatially mollified transports. -/
theorem forcedLerayLimit_mollified_convergence_of_strong_three
    (ρ : RegMollifierProfile) (T : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (U : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (hUmeas : ∀ n, Measurable (U n))
    (hUslice : ∀ n, ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => U n (x,t)) 2 volume)
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
    Measurable.piecewise hPmeas (hUmeas n)
      (by fun_prop : Measurable (fun _ : ParabolicPoint => (0 : Vec3)))
  have hpos : ∀ᵐ z ∂μ, 0 < z.2 := by
    filter_upwards [ae_restrict_mem hslabMeas] with z hz
    exact hz.2.1
  have hVeq (n : ℕ) (z : ParabolicPoint) (hz : 0 < z.2) : V n z = U n z :=
    piecewise_eq_of_mem _ _ _ (show z ∈ P from ⟨Set.mem_univ _,hz⟩)
  have hJeq (n : ℕ) (z : ParabolicPoint) (hz : 0 < z.2) :
      J n (U n) z = J n (V n) z := by
    change J n (U n) ((z.1,z.2) : ParabolicPoint) =
      J n (V n) ((z.1,z.2) : ParabolicPoint)
    simp only [J]
    rw [lerayLimit_regUniformMollifiedVelocity_eq_convolution,
      lerayLimit_regUniformMollifiedVelocity_eq_convolution]
    congr 1
    funext y
    exact (hVeq n (y,z.2) hz).symm
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
  have hJ3 (n : ℕ) : MemLp (J n (U n)) 3 μ := by
    have hV3 : MemLp (V n) 3 μ := (hU3 n).ae_eq (hUV n)
    have hJV : MemLp (J n (V n)) 3 μ :=
      lt_of_le_of_lt (hcontract n (V n) (hVmeas n)) hV3
    exact hJV.ae_eq (hJUV n).symm
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
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall (fun _ => le_top)
  let e4 : ℝ≥0∞ := e / 4
  have he4 : 0 < e4 := ENNReal.div_pos he.ne' (by norm_num)
  have hw : MemLp (fun q : Vec3 × ℝ => slab.indicator u ((q.1,q.2) : ParabolicPoint))
      3 (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hslabMeas).2 hu3
  obtain ⟨g, hgc, hgclose, hgcont, -⟩ :=
    hw.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) he4.ne'
  let gP : ParabolicPoint → Vec3 := fun z => g (z.1,z.2)
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
      LocallyIntegrable (fun y : Vec3 => V n (y,t)) volume := by
    have hfun : (fun y : Vec3 => V n (y,t)) = fun y => U n (y,t) := by
      funext y
      exact hVeq n (y,t) ht
    rw [hfun]
    exact (hUslice n t ht.le).locallyIntegrable (by norm_num)
  obtain ⟨-, hκc, -, -, -, hκcs⟩ :=
    lerayLimit_regMollifierKernel_vec3_props ρ (ε n) (hε n)
  have hlin (z : ParabolicPoint) (hz : 0 < z.2) :
      J n (V n) z - J n gP z = J n (V n - gP) z := by
    change J n (V n) ((z.1,z.2) : ParabolicPoint) -
        J n gP ((z.1,z.2) : ParabolicPoint) =
      J n (V n - gP) ((z.1,z.2) : ParabolicPoint)
    set x := z.1
    set t := z.2 with ht_def
    simp only [J]
    rw [lerayLimit_regUniformMollifiedVelocity_eq_convolution,
      lerayLimit_regUniformMollifiedVelocity_eq_convolution,
      lerayLimit_regUniformMollifiedVelocity_eq_convolution]
    have hg1 : LocallyIntegrable (fun y : Vec3 => gP (y,t)) volume :=
      (hgcont.comp (Continuous.prodMk_left t)).locallyIntegrable
    have hd : LocallyIntegrable (fun y : Vec3 => (V n - gP) (y,t)) volume :=
      (hsliceV t hz).sub hg1
    have hsum : (fun y : Vec3 => V n (y,t)) =
        (fun y : Vec3 => (V n - gP) (y,t)) + fun y : Vec3 => gP (y,t) := by
      funext y
      exact (sub_add_cancel (V n (y,t)) (gP (y,t))).symm
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
