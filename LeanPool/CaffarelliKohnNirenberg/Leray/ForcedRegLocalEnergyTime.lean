/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyNLimit

/-!
# The mollifier limit of the space-time energy identity

For each velocity component of the forced regularized solution, the space-time
energy identity of the mollified velocity passes to the limit as the mollifier
radius tends to zero: on almost every time slice the mollified pairing
converges to the unmollified pairing, dominated by an integrable product of
slice `L²` norms. The result is `∫∫ u_k² ∂ₜψ = 2 ∫ L_k`, where `L_k` is the
limiting slice pairing. This is the limit step of `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution Topology

noncomputable section

namespace CKN.Leray

theorem memLp_toReal_of_lintegral_sq {N : ℝ → ℝ≥0∞} (hm : Measurable N) {T : ℝ}
    (hfin : ∫⁻ t in Ioo 0 T, N t ^ (2 : ℝ) ≠ ⊤) :
    MemLp (fun t => (N t).toReal) 2 ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
  rw [memLp_two_iff_integrable_sq hm.ennreal_toReal.aestronglyMeasurable]
  refine (integrable_toReal_of_lintegral_ne_top (hm.pow_const _).aemeasurable hfin).congr
    (Eventually.of_forall fun t => ?_)
  simp only
  rw [← ENNReal.toReal_rpow, Real.rpow_two]

theorem memLp_eLpNorm_slice_two {X : Vec3 × ℝ → ℝ} (hX : StronglyMeasurable X) {T : ℝ}
    (h2 : MemLp X 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) :
    MemLp (fun t => (eLpNorm (fun x => X (x, t)) 2 volume).toReal) 2
      ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
  refine memLp_toReal_of_lintegral_sq
    (measurable_eLpNorm_slice hX (by norm_num) (by norm_num) volume) ?_
  rw [lintegral_eLpNorm_real_slice_sq hX]
  exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top).ne

theorem memLp_eLpNorm_vector_slice_two {X : Vec3 × ℝ → Vec3} (hX : StronglyMeasurable X)
    {T : ℝ}
    (h2 : MemLp X 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) :
    MemLp (fun t => (eLpNorm (fun x => X (x, t)) 2 volume).toReal) 2
      ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
  refine memLp_toReal_of_lintegral_sq (measurable_eLpNorm_two_slice hX) ?_
  rw [lintegral_eLpNorm_slice_sq_eq hX]
  exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top).ne

theorem fderiv_scalar_slice {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Vec3) (t : ℝ)
    (v : Vec3) : fderiv ℝ (fun y => ψ (y, t)) x v = fderiv ℝ ψ (x, t) (v, 0) := by
  have h : HasFDerivAt (fun y => ψ (y, t))
      ((fderiv ℝ ψ (x, t)).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) x :=
    ((hψ.differentiable (by simp)) (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)
  rw [h.fderiv]
  rfl

theorem fderiv_eq_zero_of_notMem_tsupport_scalar {ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : fderiv ℝ ψ z = 0 := by
  by_contra h
  exact hz (support_fderiv_subset ℝ h)

/-- A smooth compactly supported space-time weight and its spatial partial
derivatives are uniformly bounded. -/
theorem exists_weight_bound {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z, |ψ z| ≤ M) ∧
      ∀ (j : Fin 3) (x : Vec3) (t : ℝ), |fderiv ℝ (fun y => ψ (y, t)) x (CKN.basisVec j)| ≤ M := by
  obtain ⟨M0, hM0⟩ := Continuous.bounded_above_of_compact_support hψ.continuous hψc
  have hd : ∀ j : Fin 3, Continuous fun z => fderiv ℝ ψ z (CKN.basisVec j, 0) := fun j =>
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : ∀ j : Fin 3, HasCompactSupport fun z => fderiv ℝ ψ z (CKN.basisVec j, 0) := fun j =>
    (hψc.fderiv ℝ).comp_left (g := fun L : Vec3 × ℝ →L[ℝ] ℝ => L (CKN.basisVec j, 0)) (by simp)
  choose Mj hMj using fun j => Continuous.bounded_above_of_compact_support (hd j) (hdc j)
  refine ⟨max 0 (max M0 (∑ j, |Mj j|)), le_max_left _ _, fun z => ?_, fun j x t => ?_⟩
  · have h := hM0 z
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [fderiv_scalar_slice hψ]
    have h1 := hMj j (x, t)
    rw [Real.norm_eq_abs] at h1
    have h2 : Mj j ≤ ∑ i, |Mj i| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Mj i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))
    exact h1.trans (h2.trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem hasCompactSupport_scalar_slice {g : Vec3 × ℝ → ℝ} (hgc : HasCompactSupport g) (t : ℝ) :
    HasCompactSupport fun x => g (x, t) :=
  HasCompactSupport.intro (hgc.image continuous_fst) fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, t), h, rfl⟩

section Time

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The mollified energy pairing of one component on a time slice. -/
@[expose]
def leDeltaT (ψ : Vec3 × ℝ → ℝ) (n : ℕ) (k : Fin 3) (t : ℝ) : ℝ :=
  ∫ x, leW ρ ε hε ha hf (leMol n) x t k * leSF ρ ε hε ha hf (leMol n) x t k * ψ (x, t)

/-- The limiting energy pairing of one component on a time slice. -/
@[expose]
def leLimitT (ψ : Vec3 × ℝ → ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  limUnder atTop fun n => leDeltaT ρ ε hε ha hf ψ n k t

/-- The dominating function of the mollified energy pairings. -/
@[expose]
def leTimeBound (M : ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  M * ((∑ j : Fin 3, (eLpNorm (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume).toReal +
      (eLpNorm (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
        volume).toReal) *
    (∑ j : Fin 3, (eLpNorm (fun y => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (y, t) k j)
        2 volume).toReal +
      (eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume).toReal) +
    (eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume).toReal *
      (5 * (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal))

theorem integrableOn_leTimeBound (M : ℝ) (k : Fin 3) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (leTimeBound ρ ε hε ha hf M k) (Ioo 0 T) := by
  have mA : ∀ j, MemLp (fun t =>
      (eLpNorm (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume).toReal) 2
      ((volume : Measure ℝ).restrict (Ioo 0 T)) := fun j =>
    memLp_eLpNorm_slice_two (stronglyMeasurable_leTensor ρ ε hε ha hf j k)
      (memLp_leTensor_prod ρ ε hε ha hf j k hT.le)
  have mq := memLp_eLpNorm_slice_two
    (forcedQuadPressure_stronglyMeasurable ρ ε hε (continuous_forcedRegCurve ρ ε hε ha hf))
    (memLp_forcedQuadPressure_slab ρ ε hε (continuous_forcedRegCurve ρ ε hε ha hf) T)
  have mD : ∀ j, MemLp (fun t => (eLpNorm (fun y =>
      forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (y, t) k j) 2 volume).toReal) 2
      ((volume : Measure ℝ).restrict (Ioo 0 T)) := fun j =>
    memLp_eLpNorm_slice_two (forcedMollifiedGrad_stronglyMeasurable
      (forcedRegRep_stronglyMeasurable ρ ε hε ha hf) (forcedRegRep_locallyIntegrable ρ ε hε ha hf)
      k j) (((memLp_forcedRegGrad_prod ρ ε hε ha hf T hT.le).eval k).eval j)
  have mu : MemLp (fun t =>
      (eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume).toReal) 2
      ((volume : Measure ℝ).restrict (Ioo 0 T)) :=
    memLp_eLpNorm_slice_two (X := fun z => forcedRegRep ρ ε hε ha hf z k)
      ((measurable_pi_apply k).comp
        (forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable).stronglyMeasurable
      ((memLp_forcedRegRep_prod ρ ε hε ha hf T).eval k)
  have mF := memLp_eLpNorm_vector_slice_two (forcedForceMod_stronglyMeasurable f hf)
    (memLp_forcedForceMod_prod f hf hT)
  have ma := (memLp_finsetSum Finset.univ fun j _ => mA j).add mq
  have mb := (memLp_finsetSum Finset.univ fun j _ => mD j).add mu
  have h := ((ma.integrable_mul mb).add (mu.integrable_mul (mF.const_mul 5))).const_mul M
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [leTimeBound, Pi.add_apply, Pi.mul_apply]

theorem memLp_leTensor_slice {T t : ℝ} (ht : t ∈ Icc 0 T) (k : Fin 3)
    (hDu : ∀ i j, MemLp (fun x => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i j) 2
      volume) (j : Fin 3) :
    MemLp (fun y => leTensor ρ ε hε ha hf j k (y, t)) 2 volume := by
  obtain ⟨M, -, hM⟩ := forcedRegTransport_bound ρ ε hε ha hf T
  have hu := (forcedRegRep_memLp ρ ε hε ha hf t).eval k
  have hJu : MemLp (fun y => regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf)
      (y, t) j * forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume := by
    refine hu.of_le_mul (c := M) ?_ (Eventually.of_forall fun y => ?_)
    · exact (((measurable_forcedRegTransport ρ ε hε ha hf j).comp
        (measurable_id.prodMk measurable_const)).mul ((measurable_pi_apply k).comp
        ((forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable.comp
          (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · rw [norm_mul]
      have h := hM (y, t) ht j
      rw [← Real.norm_eq_abs] at h
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  exact hJu.sub (hDu k j)

/-- On almost every time slice the mollified energy pairings are bounded by the
dominating function and converge to the limiting pairing, which is the slice
pairing of the unmollified fields. -/
theorem ae_leDelta {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) {M : ℝ} (hMψ : ∀ z, |ψ z| ≤ M)
    (hMd : ∀ (j : Fin 3) (x : Vec3) (t : ℝ), |fderiv ℝ (fun y => ψ (y, t)) x (CKN.basisVec j)| ≤ M)
    (k : Fin 3) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      (∀ n, |leDeltaT ρ ε hε ha hf ψ n k t| ≤ leTimeBound ρ ε hε ha hf M k t) ∧
      Tendsto (fun n => leDeltaT ρ ε hε ha hf ψ n k t) atTop
        (𝓝 (leLimitT ρ ε hε ha hf ψ k t)) ∧
      ∀ hft : MemLp (fun x => f (x, t)) 2 volume,
        leLimitT ρ ε hε ha hf ψ k t =
          leLimit (fun y => forcedRegRep ρ ε hε ha hf (y, t) k)
            (fun j y => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (y, t) k j)
            (fun j y => leTensor ρ ε hε ha hf j k (y, t))
            (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t))
            (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k)
            (fun y => forcedForceMod f hf (y, t) k) (fun y => ψ (y, t)) k := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      (forcedRegRep_weakGradient ρ ε hε ha hf),
    ae_forcedRegGrad_slice ρ ε hε ha hf hT.le, ae_forcedForceMod_slice hf hT,
    ae_forcePressure_slice hf hT] with t ht hw hDu hFF hPF
  obtain ⟨hF2, hFf⟩ := hFF
  obtain ⟨hpfl, hft, hpf⟩ := hPF
  have hA := memLp_leTensor_slice ρ ε hε ha hf ⟨ht.1.le, ht.2.le⟩ k hDu
  have hψt : ContDiff ℝ (⊤ : ℕ∞) fun y => ψ (y, t) := hψ.comp (contDiff_id.prodMk contDiff_const)
  have hψtc := hasCompactSupport_scalar_slice hψc t
  have hq2 : MemLp (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
      volume :=
    (memLp_rieszPressureSliceRepresentative_two _).ae_eq
      (forcedQuadPressure_slice ρ ε hε (forcedRegCurve ρ ε hε ha hf) t).symm
  have hu := (forcedRegRep_memLp ρ ε hε ha hf t).eval k
  have hG2 : MemLp (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) 2
      volume := (forcePressureGradientFunction_memLp _ hft).eval k
  have hD : ∀ j, MemLp (fun y => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (y, t) k j) 2
      volume := fun j => hDu k j
  have hweak : ∀ j, CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j
      (fun y => forcedRegRep ρ ε hε ha hf (y, t) k)
      (fun y => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (y, t) k j) := fun j => hw k j
  have hEq : ∀ n, leDeltaT ρ ε hε ha hf ψ n k t =
      leDeltaRHS n (fun y => forcedRegRep ρ ε hε ha hf (y, t) k)
        (fun j y => leTensor ρ ε hε ha hf j k (y, t))
        (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t))
        (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k)
        (fun y => forcedForceMod f hf (y, t) k) (fun y => ψ (y, t)) k := fun n => by
    unfold leDeltaT
    rw [integral_leW_mul_leSF ρ ε hε ha hf (leMol_contDiff n) (leMol_hasCompactSupport n) k hA
      hF2 hft hpf hpfl hψt hψtc]
    rfl
  have hlim := (tendsto_leDeltaRHS hu hD hA hq2 hG2 (hF2.eval k) hweak hψt hψtc k).congr
    fun n => (hEq n).symm
  refine ⟨fun n => ?_, ?_, fun hft' => ?_⟩
  · have hb := abs_leDeltaRHS_le hu hD hA hq2 hG2 (hF2.eval k) hweak hψt hψtc
      (fun x => hMψ (x, t)) (fun j x => hMd j x t) n k
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMψ 0)
    have hGb : (eLpNorm (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k) 2
        volume).toReal ≤ 4 * (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal := by
      have h := eLpNorm_forcePressureGradient_le hft k
      rw [eLpNorm_congr_ae hFf.symm] at h
      exact h
    have hFb : (eLpNorm (fun y => forcedForceMod f hf (y, t) k) 2 volume).toReal ≤
        (eLpNorm (fun y => forcedForceMod f hf (y, t)) 2 volume).toReal :=
      ENNReal.toReal_mono hF2.eLpNorm_ne_top
        (eLpNorm_mono (hF2.eval k).aestronglyMeasurable fun y => norm_le_pi_norm _ k)
    have hc0 : 0 ≤ (eLpNorm (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2 volume).toReal :=
      ENNReal.toReal_nonneg
    rw [hEq n]
    refine hb.trans ?_
    unfold leTimeBound
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hc0)) hM0
    linarith only [hGb, hFb]
  · unfold leLimitT
    exact tendsto_nhds_limUnder ⟨_, hlim⟩
  · unfold leLimitT
    exact hlim.limUnder_eq

theorem aestronglyMeasurable_leDeltaSlice {ψ : Vec3 × ℝ → ℝ} (hψ : Continuous ψ) (n : ℕ)
    (k : Fin 3) (ν : Measure ℝ) [SFinite ν] :
    AEStronglyMeasurable (leDeltaT ρ ε hε ha hf ψ n k) ν := by
  have hm : StronglyMeasurable fun p : Vec3 × ℝ => leW ρ ε hε ha hf (leMol n) p.1 p.2 k *
      leSF ρ ε hε ha hf (leMol n) p.1 p.2 k * ψ p :=
    (((stronglyMeasurable_leW ρ ε hε ha hf (leMol_contDiff n).continuous k).measurable.mul
      (stronglyMeasurable_leSF ρ ε hε ha hf (leMol_contDiff n) k).measurable).mul
        hψ.measurable).stronglyMeasurable
  exact hm.integral_prod_left'.aestronglyMeasurable

theorem integrableOn_leLimitT {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (k : Fin 3) :
    IntegrableOn (leLimitT ρ ε hε ha hf ψ k) (Ioo 0 T) := by
  obtain ⟨M, -, hMψ, hMd⟩ := exists_weight_bound hψ hψc
  have hae := ae_leDelta ρ ε hε ha hf hT hψ hψc hMψ hMd k
  have hmeas : AEStronglyMeasurable (leLimitT ρ ε hε ha hf ψ k)
      ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_leDeltaSlice ρ ε hε ha hf hψ.continuous n k _) ?_
    filter_upwards [hae] with t ht
    exact ht.2.1
  refine Integrable.mono' (integrableOn_leTimeBound ρ ε hε ha hf M k hT) hmeas ?_
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs]
  exact le_of_tendsto' (continuous_abs.tendsto _ |>.comp ht.2.1) fun n => ht.1 n

/-- The mollifier limit of the space-time energy identity of one component. -/
theorem integral_sq_timePartial_eq (k : Fin 3) {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {c d : ℝ} (hc : 0 < c)
    (hcd : c < d) (hdT : d < T) (hψs : ∀ z ∈ tsupport ψ, z.2 ∈ Ioo c d) :
    ∫ t in Ioo 0 T, ∫ x, forcedRegRep ρ ε hε ha hf (x, t) k *
        (forcedRegRep ρ ε hε ha hf (x, t) k * CKN.timePartial ψ (x, t)) =
      2 * ∫ t in Ioo 0 T, leLimitT ρ ε hε ha hf ψ k t := by
  obtain ⟨M, -, hMψ, hMd⟩ := exists_weight_bound hψ hψc
  have hae := ae_leDelta ρ ε hε ha hf hT hψ hψc hMψ hMd k
  have hR : Tendsto (fun n => ∫ t in Ioo 0 T, leDeltaT ρ ε hε ha hf ψ n k t) atTop
      (𝓝 (∫ t in Ioo 0 T, leLimitT ρ ε hε ha hf ψ k t)) := by
    refine tendsto_integral_of_dominated_convergence (leTimeBound ρ ε hε ha hf M k)
      (fun n => aestronglyMeasurable_leDeltaSlice ρ ε hε ha hf hψ.continuous n k _)
      (integrableOn_leTimeBound ρ ε hε ha hf M k hT) (fun n => ?_) ?_
    · filter_upwards [hae] with t ht
      rw [Real.norm_eq_abs]
      exact ht.1 n
    · filter_upwards [hae] with t ht
      exact ht.2.1
  have hτ : Continuous fun z : Vec3 × ℝ => fderiv ℝ ψ z (0, 1) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hτc : HasCompactSupport fun z : Vec3 × ℝ => fderiv ℝ ψ z (0, 1) :=
    (hψc.fderiv ℝ).comp_left (g := fun L : Vec3 × ℝ →L[ℝ] ℝ => L (0, 1)) (by simp)
  obtain ⟨Mτ, hMτ⟩ := Continuous.bounded_above_of_compact_support hτ hτc
  have hτeq : ∀ t, (fun x => CKN.timePartial ψ (x, t)) = fun x => fderiv ℝ ψ (x, t) (0, 1) :=
    fun t => funext fun x => timePartial_eq_fderiv hψ (x, t)
  have hτt : ∀ t, Continuous fun x => CKN.timePartial ψ (x, t) := fun t => by
    rw [hτeq t]
    exact hτ.comp (continuous_id.prodMk continuous_const)
  have hτtc : ∀ t, HasCompactSupport fun x => CKN.timePartial ψ (x, t) := fun t => by
    rw [hτeq t]
    exact hasCompactSupport_scalar_slice hτc t
  have hτb : ∀ x t, |CKN.timePartial ψ (x, t)| ≤ Mτ := fun x t => by
    rw [timePartial_eq_fderiv hψ, ← Real.norm_eq_abs]
    exact hMτ (x, t)
  obtain ⟨Cu, hCu0, hCu⟩ := forcedRegRep_slice_bound ρ ε hε ha hf T
  have hJ : ∀ n t, ∫ x, leW ρ ε hε ha hf (leMol n) x t k ^ 2 * CKN.timePartial ψ (x, t) =
      ∫ x, leConv (leMol n) (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x *
        (leConv (leMol n) (fun y => forcedRegRep ρ ε hε ha hf (y, t) k) x *
          CKN.timePartial ψ (x, t)) := fun n t =>
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only
      rw [leW_eq_leConv]
      ring)
  have hL : Tendsto (fun n => ∫ t in Ioo 0 T, ∫ x, leW ρ ε hε ha hf (leMol n) x t k ^ 2 *
      CKN.timePartial ψ (x, t)) atTop
      (𝓝 (∫ t in Ioo 0 T, ∫ x, forcedRegRep ρ ε hε ha hf (x, t) k *
        (forcedRegRep ρ ε hε ha hf (x, t) k * CKN.timePartial ψ (x, t)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mτ * Cu ^ 2) (fun n => ?_)
      (integrableOn_const (by simp [Real.volume_Ioo])) (fun n => ?_) ?_
    · have hm : StronglyMeasurable fun p : Vec3 × ℝ =>
          leW ρ ε hε ha hf (leMol n) p.1 p.2 k ^ 2 * CKN.timePartial ψ p := by
        have h2 : Measurable fun p : Vec3 × ℝ => CKN.timePartial ψ p := by
          have e : (fun p : Vec3 × ℝ => CKN.timePartial ψ p) =
              fun z => fderiv ℝ ψ z (0, 1) := funext (timePartial_eq_fderiv hψ)
          rw [e]
          exact hτ.measurable
        exact (((stronglyMeasurable_leW ρ ε hε ha hf (leMol_contDiff n).continuous
          k).measurable.pow_const 2).mul h2).stronglyMeasurable
      exact hm.integral_prod_left'.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [hJ n t, Real.norm_eq_abs]
      have hu := (forcedRegRep_memLp ρ ε hε ha hf t).eval k
      have hC := hCu t ⟨ht.1.le, ht.2.le⟩ k
      have h1 := abs_integral_mul_le_eLpNorm_two (memLp_leConv_leMol hu n)
        (memLp_mul_compact (memLp_leConv_leMol hu n) (hτt t) (hτtc t))
      have h2 := toReal_eLpNorm_mul_le (memLp_leConv_leMol hu n) (hτt t).aestronglyMeasurable
        (fun x => hτb x t)
      have h3 := toReal_eLpNorm_leConv_leMol_le hu n
      have hMτ0 : 0 ≤ Mτ := (abs_nonneg _).trans (hτb 0 t)
      have hw0 : 0 ≤ (eLpNorm (leConv (leMol n) fun y => forcedRegRep ρ ε hε ha hf (y, t) k) 2
          volume).toReal := ENNReal.toReal_nonneg
      refine h1.trans ?_
      calc _ ≤ Cu * (Mτ * Cu) := mul_le_mul (h3.trans hC)
              (h2.trans (mul_le_mul_of_nonneg_left (h3.trans hC) hMτ0)) ENNReal.toReal_nonneg
              hCu0
        _ = Mτ * Cu ^ 2 := by ring
    · refine Eventually.of_forall fun t => ?_
      have hu := (forcedRegRep_memLp ρ ε hε ha hf t).eval k
      refine (tendsto_integral_leConv_mul hu
        (fun n => memLp_mul_compact (memLp_leConv_leMol hu n) (hτt t) (hτtc t))
        (memLp_mul_compact hu (hτt t) (hτtc t))
        (tendsto_mul_leConv_leMol hu (hτt t) (hτtc t))).congr fun n => (hJ n t).symm
  have hn : ∀ n, ∫ t in Ioo 0 T, ∫ x, leW ρ ε hε ha hf (leMol n) x t k ^ 2 *
      CKN.timePartial ψ (x, t) = 2 * ∫ t in Ioo 0 T, ∫ x, leW ρ ε hε ha hf (leMol n) x t k *
        leSF ρ ε hε ha hf (leMol n) x t k * ψ (x, t) := fun n =>
    integral_leW_sq_spaceTime ρ ε hε ha hf (leMol_contDiff n) (leMol_hasCompactSupport n) k hT hψ
      hψc hc hcd hdT hψs
  exact tendsto_nhds_unique hL ((hR.const_mul 2).congr fun n => (hn n).symm)

end Time

end CKN.Leray

end
