/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionDeriv

/-!
# Energy bounds for the heat orbit of an `L²` datum

The Gaussian convolution is an `L²` contraction, so the spatial `L²` norm of
the heat orbit is bounded by that of the datum at every positive time.  For
the gradient, the energy inequality `∫₀^τ ‖∇h‖₂² ≤ ½‖a‖₂²` holds for the smooth
compactly supported approximants of a datum in `J`, and passes to the heat
orbit of the datum by Fatou's lemma, since the gradients converge pointwise.
These are the energy clauses of the heat orbit in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem enorm_rpow_two_le_sum (v : Vec3) :
    ‖v‖ₑ ^ (2 : ℝ) ≤ ∑ i : Fin 3, ‖v i‖ₑ ^ (2 : ℝ) := by
  obtain ⟨k, hk⟩ := vec3_exists_enorm_eq_component v
  rw [hk]
  exact Finset.single_le_sum (f := fun i => ‖v i‖ₑ ^ (2 : ℝ)) (fun i _ => bot_le)
    (Finset.mem_univ k)

private theorem enorm_rpow_two_le_double_sum (M : Fin 3 → Fin 3 → ℝ) :
    ‖M‖ₑ ^ (2 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖M i j‖ₑ ^ (2 : ℝ) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => ‖M i‖₊)
  have hM : ‖M‖ₑ = ‖M k‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Pi.nnnorm_def, hk]
  rw [hM]
  exact (enorm_rpow_two_le_sum (M k)).trans
    (Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖M i j‖ₑ ^ (2 : ℝ))
      (fun i _ => bot_le) (Finset.mem_univ k))

/-- Convolution with a kernel derivative is continuous in the datum for the
`L²` norm, pointwise at each positive time. -/
theorem heatConvGrad_tendsto_of_eLpNorm {fs : ℕ → Vec3 → ℝ} {f : Vec3 → ℝ}
    (hfs : ∀ n, MemLp (fs n) 2 volume) (hf : MemLp f 2 volume)
    (hlim : Tendsto (fun n => eLpNorm (fs n - f) 2 volume) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (j : Fin 3) (x : Vec3) :
    Tendsto (fun n => heatConvGrad t (fs n) j x) atTop (𝓝 (heatConvGrad t f j x)) := by
  obtain ⟨-, hD⟩ := heatKernel_memLp_two ht
  have hbd : Tendsto (fun n => eLpNorm (fun y : Vec3 => heatKernelSpaceDerivative y t j) 2 volume *
      eLpNorm (fs n - f) 2 volume) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr (hD j).eLpNorm_ne_top)
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbd
    (fun _ => bot_le) fun n => ?_
  rw [edist_eq_enorm_sub]
  exact integral_mul_sub_sub_enorm_le (hD j) (hfs n) hf x

/-- The `L²` contraction of the heat flow on the heat orbit of an `L²` datum:
at every positive time the spatial square integral is bounded by the sum of
the squared `L²` norms of the components of the datum. -/
theorem heatOrbit_slice_lintegral_le {a : Vec3 → Vec3} (ha : MemLp a 2 volume) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ x, ‖heatOrbit a (x, s)‖ₑ ^ (2 : ℝ) ≤
      ∑ i : Fin 3, eLpNorm (fun y => a y i) 2 volume ^ (2 : ℝ) := by
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha i
  have hcont (i : Fin 3) : Continuous (heatConv s (fun y => a y i)) := by
    have hd : Differentiable ℝ (heatConv s (fun y => a y i)) := fun x =>
      (heatConv_hasFDerivAt_of_memLp (hai i) hs x).differentiableAt
    exact hd.continuous
  have hyoung (i : Fin 3) :
      eLpNorm (heatConv s (fun y => a y i)) 2 volume ≤ eLpNorm (fun y => a y i) 2 volume := by
    rw [heatConv]
    exact CKN.young_convolution_nonneg_integral_one_of_aemeasurable (d := 3) (by norm_num)
      (by norm_num) (fun x => heatKernel_nonneg x s) (heatKernel_integrable hs)
      (heatKernel_integral s hs)
      (heatKernel_vecTime_measurable.comp (measurable_id.prodMk measurable_const))
      (hai i).aestronglyMeasurable.aemeasurable
  calc
    ∫⁻ x, ‖heatOrbit a (x, s)‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ x, ∑ i : Fin 3, ‖heatConv s (fun y => a y i) x‖ₑ ^ (2 : ℝ) :=
      lintegral_mono fun x => enorm_rpow_two_le_sum (heatOrbit a (x, s))
    _ = ∑ i : Fin 3, ∫⁻ x, ‖heatConv s (fun y => a y i) x‖ₑ ^ (2 : ℝ) :=
      lintegral_finsetSum' _ fun i _ =>
        ((hcont i).aestronglyMeasurable.enorm.pow_const _)
    _ = ∑ i : Fin 3, eLpNorm (heatConv s (fun y => a y i)) 2 volume ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num) (hcont i).aestronglyMeasurable]
      norm_num
    _ ≤ ∑ i : Fin 3, eLpNorm (fun y => a y i) 2 volume ^ (2 : ℝ) := by
      gcongr with i
      exact hyoung i

/-- The time-integrated Dirichlet energy of the heat orbit of smooth compactly
supported data is bounded by the initial energy. -/
theorem heatConvVec3_grad_lintegral_le {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ t in Ioo 0 τ, ∫⁻ x, ∑ i : Fin 3, ∑ j : Fin 3,
        ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2) := by
  refine le_trans ?_ (heatConvVec3_energy_bound hb hbc hτ).2
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have htpos : 0 < t := ht.1
  have hmem (i j : Fin 3) :
      MemLp (fun x => spatialDeriv (fun y => heatConvVec3 t b y i) j x) 2 volume := by
    have hdS : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (fun y => b y i) j) :=
      contDiff_spatialDeriv_smooth (hb i) j
    have hdC : HasCompactSupport (spatialDeriv (fun y => b y i) j) := by
      change HasCompactSupport (fun z => (fderiv ℝ (fun y => b y i) z) (basisVec j))
      exact (hbc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
    have heq : (fun x => spatialDeriv (fun y => heatConvVec3 t b y i) j x) =
        heatConv t (spatialDeriv (fun y => b y i) j) := by
      funext x
      change fderiv ℝ (heatConv t (fun y => b y i)) x (basisVec j) = _
      exact heatConv_fderiv (hb i) (hbc i) htpos x (basisVec j)
    rw [heq]
    exact heatConv_memLp_two_smooth hdS hdC htpos
  have hterm (i j : Fin 3) :
      ∫⁻ x, ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (∫ x, (spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
    rw [lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num) (hmem i j).aestronglyMeasurable,
      ← eLpNorm_two_rpow_two_eq_ofReal_integral (hmem i j)]
    norm_num
  have hmeas (i j : Fin 3) : AEMeasurable
      (fun x => ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ)) volume :=
    ((hmem i j).aestronglyMeasurable.enorm.pow_const _)
  have hnn (i j : Fin 3) :
      0 ≤ ∫ x, (spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hS : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x, (spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j
  have hsplit : (∫⁻ x, ∑ i : Fin 3, ∑ j : Fin 3,
      ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫⁻ x, ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ) := by
    rw [lintegral_finsetSum' (f := fun i x => ∑ j : Fin 3,
      ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ)) Finset.univ
      fun i _ => Finset.aemeasurable_fun_sum Finset.univ fun j _ => hmeas i j]
    exact Finset.sum_congr rfl fun i _ => lintegral_finsetSum' Finset.univ fun j _ => hmeas i j
  calc
    (∫⁻ x, ∑ i : Fin 3, ∑ j : Fin 3,
        ‖spatialDeriv (fun y => heatConvVec3 t b y i) j x‖ₑ ^ (2 : ℝ)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ENNReal.ofReal (∫ x, (spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
      rw [hsplit]
      simp only [hterm]
    _ = ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x, (spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j]
      exact Finset.sum_congr rfl fun i _ =>
        (ENNReal.ofReal_sum_of_nonneg fun j _ => hnn i j).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith only [hS])

/-- (h3) The heat orbit of a datum in `J` has finite energy on every slab
`ℝ³ × (0, τ)`: the space-time integral of `|h|² + |∇h|²` is finite. -/
theorem heatOrbit_energy_lintegral_lt_top {a : Vec3 → Vec3} (ha : IsInJ a) {τ : ℝ}
    (hτ : 0 < τ) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ‖heatOrbit a z‖ₑ ^ (2 : ℝ) +
      ‖(fun i j => spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 :
        Fin 3 → Fin 3 → ℝ)‖ₑ ^ (2 : ℝ)) < ⊤ := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) with hQdef
  have hQ : MeasurableSet Q := MeasurableSet.univ.prod measurableSet_Ioo
  obtain ⟨hmh, -⟩ := heatOrbit_grad_aestronglyMeasurable ha τ
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  rw [lintegral_add_left' (hmh.enorm.pow_const _)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_spaceTimeSet_univ_eq (hmh.enorm.pow_const _)]
    have hfin : ∑ i : Fin 3, eLpNorm (fun y => a y i) 2 volume ^ (2 : ℝ) < ⊤ :=
      ENNReal.sum_lt_top.2 fun i _ => ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (hai i).eLpNorm_ne_top
    calc
      ∫⁻ t in Ioo 0 τ, ∫⁻ x, ‖heatOrbit a (x, t)‖ₑ ^ (2 : ℝ) ≤
          ∫⁻ _t in Ioo 0 τ, ∑ i : Fin 3, eLpNorm (fun y => a y i) 2 volume ^ (2 : ℝ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact heatOrbit_slice_lintegral_le ha.1 ht.1
      _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Ioo]
        exact ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top
  · obtain ⟨aSeq, hsm, hcs, -, hlim, hvlim⟩ := isInJ_component_approx ha
    have hmem (k : ℕ) (i : Fin 3) : MemLp (fun y => aSeq k y i) 2 volume :=
      (hsm k i).continuous.memLp_of_hasCompactSupport (hcs k i)
    have hmemV (k : ℕ) : MemLp (aSeq k) 2 volume := memLp_pi_iff.2 (hmem k)
    let G : ℕ → ParabolicPoint → Fin 3 → Fin 3 → ℝ := fun k z i j =>
      heatConvGrad z.2 (fun y => aSeq k y i) j z.1
    have hGij (k : ℕ) (i j : Fin 3) : Measurable (fun z => G k z i j) :=
      (stronglyMeasurable_integral_kernel_mul_sub (heatKernelSpaceDerivative_vecTime_measurable j)
        (hmem k i).aestronglyMeasurable).measurable
    have hGm (k : ℕ) : Measurable (G k) :=
      measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hGij k i j
    have hlimit : ∀ᵐ z ∂(volume.restrict Q), Tendsto (fun k => ‖G k z‖ₑ ^ (2 : ℝ)) atTop
        (𝓝 (‖(fun i j => spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 :
          Fin 3 → Fin 3 → ℝ)‖ₑ ^ (2 : ℝ))) := by
      filter_upwards [ae_restrict_mem hQ] with z hz
      have hz2 : 0 < z.2 := hz.2.1
      have hconv : Tendsto (fun k => G k z) atTop
          (𝓝 (fun i j => spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1)) := by
        refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
        rw [heatOrbit_spatialDeriv_eq ha.1 hz2 z.1 i j]
        exact heatConvGrad_tendsto_of_eLpNorm (fun k => hmem k i) (hai i) (hlim i) hz2 j z.1
      exact (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_enorm.tendsto _).comp hconv)
    have hbound (k : ℕ) : ∫⁻ z in Q, ‖G k z‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (∫ x : Vec3, ∑ i : Fin 3, (aSeq k x i) ^ 2) := by
      have hm : AEMeasurable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ‖G k z i j‖ₑ ^ (2 : ℝ))
          (volume.restrict Q) :=
        (Finset.measurable_fun_sum _ fun i _ => Finset.measurable_fun_sum _ fun j _ =>
          ((hGij k i j).enorm.pow_const _)).aemeasurable
      calc
        ∫⁻ z in Q, ‖G k z‖ₑ ^ (2 : ℝ) ≤
            ∫⁻ z in Q, ∑ i : Fin 3, ∑ j : Fin 3, ‖G k z i j‖ₑ ^ (2 : ℝ) :=
          lintegral_mono fun z => enorm_rpow_two_le_double_sum _
        _ = ∫⁻ t in Ioo 0 τ, ∫⁻ x, ∑ i : Fin 3, ∑ j : Fin 3, ‖G k (x, t) i j‖ₑ ^ (2 : ℝ) :=
          lintegral_spaceTimeSet_univ_eq hm
        _ = ∫⁻ t in Ioo 0 τ, ∫⁻ x, ∑ i : Fin 3, ∑ j : Fin 3,
              ‖spatialDeriv (fun y => heatConvVec3 t (aSeq k) y i) j x‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          refine lintegral_congr fun x => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          exact congrArg (fun r : ℝ => ‖r‖ₑ ^ (2 : ℝ))
            (heatOrbit_spatialDeriv_eq (hmemV k) ht.1 x i j).symm
        _ ≤ _ := heatConvVec3_grad_lintegral_le (hsm k) (hcs k) hτ
    have hev : ∀ᶠ k in atTop, ∫⁻ z in Q, ‖G k z‖ₑ ^ (2 : ℝ) ≤
        3 * (eLpNorm a 2 volume + 1) ^ (2 : ℝ) := by
      filter_upwards [(ENNReal.tendsto_nhds_zero.1 hvlim) 1 one_pos] with k hk
      refine (hbound k).trans ((ofReal_integral_sum_sq_le_eLpNorm_two (hsm k) (hcs k)).trans ?_)
      gcongr
      calc
        eLpNorm (aSeq k) 2 volume ≤
            eLpNorm a 2 volume + eLpNorm (fun x => aSeq k x - a x) 2 volume := by
          have hsplit : aSeq k = a + fun x => aSeq k x - a x := by
            funext x
            simp
          conv_lhs => rw [hsplit]
          exact eLpNorm_add_le (by norm_num)
        _ ≤ eLpNorm a 2 volume + 1 := by gcongr
    calc
      ∫⁻ z in Q, ‖(fun i j => spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 :
          Fin 3 → Fin 3 → ℝ)‖ₑ ^ (2 : ℝ) =
          ∫⁻ z in Q, Filter.liminf (fun k => ‖G k z‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_congr_ae (hlimit.mono fun z hz => hz.liminf_eq.symm)
      _ ≤ Filter.liminf (fun k => ∫⁻ z in Q, ‖G k z‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_liminf_le' fun k => ((hGm k).enorm.pow_const _).aemeasurable
      _ ≤ 3 * (eLpNorm a 2 volume + 1) ^ (2 : ℝ) := liminf_le_of_frequently_le' hev.frequently
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (ENNReal.add_lt_top.2 ⟨ha.1.eLpNorm_lt_top, ENNReal.one_lt_top⟩).ne)

end ESS

end
