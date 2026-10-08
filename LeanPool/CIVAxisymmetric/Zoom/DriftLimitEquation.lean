/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Statements.IsDistributionalDriftDiffusion
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import LeanPool.CIVAxisymmetric.Comparison.IsDistributionalDriftDiffusionConst
public import LeanPool.CIVAxisymmetric.Comparison.MollifiedEquation

/-!
# Passing a drift-diffusion residual to the limit

Generic in the ambient dimension `m`, the truncation dimension `d`, and the time horizon `T`:
given a sequence of scalars `qn` converging to `q` in `L¹_{loc}` and a sequence of drifts
`(b n, divb n)` converging weak-* to an admissible drift `(B, divB)`, this file shows that if
the finite-`n` distributional pairing of `qn n` against the drift-diffusion residual built from
`(b n, divb n)` tends to zero for every test function, then the limit data `(B, divB, q)` solves
`eq:aniso:comparison:equation` exactly (`CIV.IsDistributionalDriftDiffusion`).

The four terms of the residual — the time derivative, the drift-gradient pairing, the
divergence pairing, and the truncated Laplacian — are passed to the limit by four different
mechanisms: the two terms free of the drift use only the strong `L¹_{loc}` convergence of `qn`
against a fixed weight, while the two drift terms split into a vanishing piece (handled the
same way, since the drift stays uniformly bounded) and a piece driven directly by the weak-*
hypothesis. A limit-uniqueness argument against the hypothesis that the finite-`n` residual
itself tends to zero then identifies the sum of the four limits as zero.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open CKN

noncomputable section

namespace CIV

/-! ### Elementary sequence lemmas -/

/-- A finite sum of a.e. strongly measurable functions is a.e. strongly measurable. -/
theorem aestronglyMeasurable_finsetSum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using aestronglyMeasurable_const
  | @insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s')).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- If `a n` is eventually within `b n` of `L` and `b n → 0`, then `a n → L`. -/
theorem tendsto_of_eventually_abs_sub_le {a : ℕ → ℝ} {L : ℝ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop (nhds 0)) (hbound : ∀ᶠ n in atTop, |a n - L| ≤ b n) :
    Tendsto a atTop (nhds L) := by
  have h1 : Tendsto (fun n => a n - L) atTop (nhds 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hbound) hb
  have h2 := h1.add_const L
  simpa using h2

/-- A product `f_n · g_n`, vanishing outside a fixed compact set `K`, tends to `0` in integral
provided `f_n → 0` in the `L¹(K)` sense (`∫⁻_K ‖f_n‖ₑ → 0`) and `g_n` is eventually bounded by a
fixed constant on `K`. This is the generic dominated-convergence mechanism behind passing a
strongly convergent factor times an eventually-bounded factor to the limit. -/
theorem tendsto_integral_mul_of_tendsto_lintegral_enorm_zero {m : ℕ}
    {K : Set (Vec m × ℝ)} (hK : IsCompact K)
    {fn gn : ℕ → Vec m × ℝ → ℝ}
    (hL1 : Tendsto (fun n => ∫⁻ z in K, ‖fn n z‖ₑ) atTop (nhds 0))
    {C : ℝ}
    (hbd : ∀ᶠ n in atTop, AEStronglyMeasurable (fn n) (volume.restrict K) ∧
      AEStronglyMeasurable (gn n) (volume.restrict K) ∧ ∀ z ∈ K, |gn n z| ≤ C)
    (hsupp : ∀ n, ∀ z, z ∉ K → fn n z * gn n z = 0) :
    Tendsto (fun n => ∫ z, fn n z * gn n z) atTop (nhds 0) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hlt1 : ∀ᶠ n in atTop, (∫⁻ z in K, ‖fn n z‖ₑ) < 1 :=
    (tendsto_order.mp hL1).2 1 (by norm_num)
  have hfin : ∀ᶠ n in atTop, (∫⁻ z in K, ‖fn n z‖ₑ) < ⊤ :=
    hlt1.mono fun n h => h.trans (by norm_num)
  have hbound : ∀ᶠ n in atTop, |∫ z, fn n z * gn n z| ≤ C * (∫⁻ z in K, ‖fn n z‖ₑ).toReal := by
    filter_upwards [hbd, hfin] with n ⟨hfnm, hgnm, hgnC⟩ hfnfin
    have hfnK : Integrable (fn n) (volume.restrict K) := ⟨hfnm, hfnfin⟩
    have hgnAe : ∀ᵐ z ∂(volume.restrict K), |gn n z| ≤ C := by
      filter_upwards [ae_restrict_mem hKm] with z hz using hgnC z hz
    have hprodK : Integrable (fun z => fn n z * gn n z) (volume.restrict K) := by
      have := hfnK.mul_bdd hgnm (by simpa [Real.norm_eq_abs] using hgnAe)
      simpa using this
    have hindic : (fun z => fn n z * gn n z)
        = K.indicator (fun z => fn n z * gn n z) := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hsupp n z hz]
    have hprod : Integrable (fun z => fn n z * gn n z) volume := by
      rw [hindic]; exact (integrable_indicator_iff hKm).mpr hprodK
    have heq : ∫ z, fn n z * gn n z = ∫ z in K, fn n z * gn n z := by
      conv_lhs => rw [hindic]
      exact integral_indicator hKm
    rw [heq]
    have hmaj : Integrable (fun z => |fn n z| * C) (volume.restrict K) :=
      (hfnK.abs).mul_const C
    have hbound1 : ‖∫ z in K, fn n z * gn n z‖ ≤ ∫ z in K, ‖fn n z * gn n z‖ :=
      norm_integral_le_integral_norm _
    have hbound2 : ∫ z in K, ‖fn n z * gn n z‖ ≤ ∫ z in K, |fn n z| * C := by
      refine integral_mono_ae hprodK.norm hmaj ?_
      filter_upwards [hgnAe] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    have hbound3 : ∫ z in K, |fn n z| * C = C * ∫ z in K, |fn n z| := by
      rw [integral_mul_const, mul_comm]
    have hbound4 : ∫ z in K, |fn n z| = (∫⁻ z in K, ‖fn n z‖ₑ).toReal := by
      have := integral_norm_eq_lintegral_enorm (μ := volume.restrict K) hfnm
      simpa [Real.norm_eq_abs] using this
    calc |∫ z in K, fn n z * gn n z| = ‖∫ z in K, fn n z * gn n z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z in K, ‖fn n z * gn n z‖ := hbound1
      _ ≤ ∫ z in K, |fn n z| * C := hbound2
      _ = C * ∫ z in K, |fn n z| := hbound3
      _ = C * (∫⁻ z in K, ‖fn n z‖ₑ).toReal := by rw [hbound4]
  have hzero : Tendsto (fun n => C * (∫⁻ z in K, ‖fn n z‖ₑ).toReal) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (∫⁻ z in K, ‖fn n z‖ₑ).toReal) atTop (nhds (0 : ℝ)) := by
      have h : Tendsto (fun n => (∫⁻ z in K, ‖fn n z‖ₑ).toReal) atTop
          (nhds ((0 : ℝ≥0∞).toReal)) :=
        (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hL1
      rwa [ENNReal.toReal_zero] at h
    simpa using h1.const_mul C
  exact tendsto_of_eventually_abs_sub_le hzero (by simpa using hbound)

/-- A function a.e.-bounded on a compact set is integrable there. -/
theorem integrableOn_of_bdd_isCompact {m : ℕ} {K : Set (Vec m × ℝ)} (hK : IsCompact K)
    {f : Vec m × ℝ → ℝ} (hfm : AEStronglyMeasurable f (volume.restrict K))
    {M : ℝ} (hfbd : ∀ᵐ z ∂(volume.restrict K), |f z| ≤ M) : IntegrableOn f K volume := by
  have hconst : IntegrableOn (fun _ : Vec m × ℝ => M) K volume :=
    integrableOn_const hK.measure_lt_top.ne
  refine Integrable.mono' hconst hfm ?_
  filter_upwards [hfbd] with z hz
  simpa [Real.norm_eq_abs] using hz

/-- A product `f · w`, with `f` a.e.-bounded on a compact set `K` and `w` a.e.-bounded and
vanishing outside `K`, is globally integrable. -/
theorem integrable_mul_of_bdd_isCompact_of_vanishing_outside {m : ℕ} {K : Set (Vec m × ℝ)}
    (hK : IsCompact K) {f w : Vec m × ℝ → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict K))
    {M : ℝ} (hfbd : ∀ᵐ z ∂(volume.restrict K), |f z| ≤ M)
    (hwm : AEStronglyMeasurable w (volume.restrict K))
    {C : ℝ} (hwbd : ∀ᵐ z ∂(volume.restrict K), |w z| ≤ C)
    (hsupp : ∀ z, z ∉ K → f z * w z = 0) : Integrable (fun z => f z * w z) volume := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hfK : Integrable f (volume.restrict K) := integrableOn_of_bdd_isCompact hK hfm hfbd
  have hprodK : Integrable (fun z => f z * w z) (volume.restrict K) := by
    have := hfK.mul_bdd hwm (by simpa [Real.norm_eq_abs] using hwbd)
    simpa using this
  have hindic : (fun z => f z * w z) = K.indicator (fun z => f z * w z) := by
    funext z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hsupp z hz]
  rw [hindic]
  exact (integrable_indicator_iff hKm).mpr hprodK

private theorem test_operator_bounds {m d : ℕ} {φ : Vec m × ℝ → ℝ}
    (hφ1 : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ2 : HasCompactSupport φ) :
    ∃ CT CL : ℝ,
      Continuous (fun z => timeDeriv m φ z) ∧
      (∀ z, z ∉ tsupport φ → timeDeriv m φ z = 0) ∧
      (∀ z ∈ tsupport φ, ‖timeDeriv m φ z‖ ≤ CT) ∧
      Continuous (fun z => partialLaplacian m d φ z) ∧
      (∀ z, z ∉ tsupport φ → partialLaplacian m d φ z = 0) ∧
      (∀ z ∈ tsupport φ, ‖partialLaplacian m d φ z‖ ≤ CL) := by
  set K := tsupport φ
  have hK : IsCompact K := hφ2
  have hΨcont : ∀ i : Fin m,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m × ℝ => fderiv ℝ φ x (basisVec i, 0)) := by
    intro i
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ1.fderiv_right (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ (basisVec i, (0 : ℝ))).contDiff.comp h1
  -- timeDeriv φ: continuity, vanishing outside K, boundedness on K.
  have heqT : (fun z => timeDeriv m φ z) = fun z => fderiv ℝ φ z (0, 1) := by
    funext z; exact timeDeriv_eq_fderiv_apply (hφ1.differentiable (by simp) z)
  have hTcont : Continuous (fun z => timeDeriv m φ z) := by
    rw [heqT]
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ1.fderiv_right (by simp)
    exact h1.continuous.clm_apply continuous_const
  have hTsub : tsupport (fun z => timeDeriv m φ z) ⊆ K := by
    rw [heqT]; exact tsupport_fderiv_apply_subset ℝ (0, 1)
  have hTvanish : ∀ z, z ∉ K → timeDeriv m φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun hc => hz (hTsub hc))
  obtain ⟨CT, hCT⟩ := hK.exists_bound_of_continuousOn hTcont.continuousOn
  -- partialLaplacian m d φ: pointwise second-derivative formula, continuity, vanishing, bound.
  have hLapEq : ∀ z, partialLaplacian m d φ z = ∑ i : Fin m, if (i : ℕ) < d then
      fderiv ℝ (fun x : Vec m × ℝ => fderiv ℝ φ x (basisVec i, 0)) z (basisVec i, 0) else 0 := by
    intro z
    unfold partialLaplacian
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · have hinner : (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x (basisVec i))
          = fun x : Vec m => (fun x' : Vec m × ℝ => fderiv ℝ φ x' (basisVec i, 0)) (x, z.2) := by
        funext x
        exact gradPair_eq_fderiv_apply (hφ1.differentiable (by simp) (x, z.2)) (basisVec i)
      rw [hinner]
      exact fderiv_slice_fst_eq ((hΨcont i).differentiable (by simp) z) (basisVec i)
    · rfl
  have hLcont : Continuous (fun z => partialLaplacian m d φ z) := by
    have heq2 : (fun z => partialLaplacian m d φ z) = fun z => ∑ i : Fin m, if (i : ℕ) < d then
        fderiv ℝ (fun x : Vec m × ℝ => fderiv ℝ φ x (basisVec i, 0)) z (basisVec i, 0) else 0 :=
      funext hLapEq
    rw [heq2]
    refine continuous_finsetSum Finset.univ (fun i _ => ?_)
    split_ifs with hi
    · have h2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun x : Vec m × ℝ => fderiv ℝ φ x (basisVec i,
      0))) :=
        (hΨcont i).fderiv_right (by simp)
      exact h2.continuous.clm_apply continuous_const
    · exact continuous_const
  have hLvanish : ∀ z, z ∉ K → partialLaplacian m d φ z = 0 := by
    intro z hz
    rw [hLapEq z]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    split_ifs with hi
    · have hsub1 : tsupport (fun x : Vec m × ℝ => fderiv ℝ φ x (basisVec i, 0)) ⊆ K :=
        tsupport_fderiv_apply_subset ℝ (basisVec i, 0)
      have hsub2 : tsupport (fun x : Vec m × ℝ =>
          fderiv ℝ (fun x' : Vec m × ℝ => fderiv ℝ φ x' (basisVec i, 0)) x (basisVec i, 0))
          ⊆ tsupport (fun x : Vec m × ℝ => fderiv ℝ φ x (basisVec i, 0)) :=
        tsupport_fderiv_apply_subset ℝ (basisVec i, 0)
      set g : Vec m × ℝ → ℝ := fun x =>
        fderiv ℝ (fun x' : Vec m × ℝ => fderiv ℝ φ x' (basisVec i, 0)) x (basisVec i, 0) with hgdef
      change g z = 0
      exact image_eq_zero_of_notMem_tsupport (fun hc => hz (hsub1 (hsub2 hc)))
    · rfl
  obtain ⟨CL, hCL⟩ := hK.exists_bound_of_continuousOn hLcont.continuousOn
  exact ⟨CT, CL, hTcont, hTvanish, hCT, hLcont, hLvanish, hCL⟩

private theorem integral_gradient_pairing_sum {m : ℕ} {φ q : Vec m × ℝ → ℝ}
    (hφ1 : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ2 : HasCompactSupport φ) {Mq : ℝ}
    (hqm : AEStronglyMeasurable q (volume.restrict (tsupport φ)))
    (hqbd : ∀ᵐ z ∂(volume.restrict (tsupport φ)), |q z| ≤ Mq)
    (Cg : Fin m → ℝ) (hCg : ∀ i, ∀ z ∈ tsupport φ, |gradPair m φ z (basisVec i)| ≤ Cg i) :
    let K := tsupport φ
    ∀ (W : Vec m × ℝ → Vec m) (MW : ℝ),
      AEStronglyMeasurable W (volume.restrict K) → (∀ᵐ z ∂(volume.restrict K), ‖W z‖ ≤ MW) →
      ∫ z, q z * gradPair m φ z (W z)
        = ∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * W z i := by
  dsimp only
  set K := tsupport φ
  have hK : IsCompact K := hφ2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsumIdentity : ∀ (W : Vec m × ℝ → Vec m) (MW : ℝ),
      AEStronglyMeasurable W (volume.restrict K) → (∀ᵐ z ∂(volume.restrict K), ‖W z‖ ≤ MW) →
      ∫ z, q z * gradPair m φ z (W z)
        = ∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * W z i := by
    intro W MW hWm hWbd
    have hpt : ∀ z, q z * gradPair m φ z (W z)
        = ∑ i : Fin m, gradPair m φ z (basisVec i) * q z * W z i := by
      intro z
      have heq := apply_eq_sum_basisVec (fderiv ℝ (fun x : Vec m => φ (x, z.2)) z.1) (W z)
      unfold gradPair
      rw [heq, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hint : ∀ i : Fin m, Integrable
        (fun z => gradPair m φ z (basisVec i) * q z * W z i) volume := by
      intro i
      have hwm : AEStronglyMeasurable (fun z => gradPair m φ z (basisVec i) * q z)
          (volume.restrict K) :=
        (continuous_gradPair_joint hφ1 (basisVec i)).aestronglyMeasurable.mul hqm
      have hwbd : ∀ᵐ z ∂(volume.restrict K), |gradPair m φ z (basisVec i) * q z| ≤ Cg i * Mq := by
        filter_upwards [ae_restrict_mem hKm, hqbd] with z hzK hzq
        rw [abs_mul]
        exact mul_le_mul (hCg i z hzK) hzq (abs_nonneg _) (le_trans (abs_nonneg _) (hCg i z hzK))
      have hwsupp : ∀ z, z ∉ K → gradPair m φ z (basisVec i) * q z = 0 := fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun hc => hz (tsupport_gradPair_joint_subset hφ1 (basisVec i) hc)), zero_mul]
      have hfm : AEStronglyMeasurable (fun z => W z i) (volume.restrict K) :=
        (continuous_apply i).comp_aestronglyMeasurable hWm
      have hfbd : ∀ᵐ z ∂(volume.restrict K), |W z i| ≤ MW := by
        filter_upwards [hWbd] with z hz
        rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (W z) i).trans hz
      have := integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hfm hfbd hwm hwbd
        (fun z hz => by rw [hwsupp z hz, mul_zero])
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    rw [hpt |> funext, integral_finsetSum Finset.univ (fun i _ => hint i)]
  exact hsumIdentity

private theorem tendsto_negative_pairing_of_difference {m : ℕ}
    {qn : ℕ → Vec m × ℝ → ℝ} {q F : Vec m × ℝ → ℝ} {Fn : ℕ → Vec m × ℝ → ℝ}
    {K : Set (Vec m × ℝ)} {Mq Mn MF : ℝ} (hK : IsCompact K)
    (hqm : AEStronglyMeasurable q (volume.restrict K))
    (hqbd : ∀ᵐ z ∂(volume.restrict K), |q z| ≤ Mq)
    (hqn : ∀ᶠ n in atTop, AEStronglyMeasurable (qn n) (volume.restrict K) ∧
      ∀ z ∈ K, |qn n z| ≤ Mn)
    (hFn : ∀ᶠ n in atTop, AEStronglyMeasurable (Fn n) (volume.restrict K) ∧
      ∀ z ∈ K, |Fn n z| ≤ MF)
    (hFnVanish : ∀ n, ∀ z, z ∉ K → Fn n z = 0)
    (hvan : Tendsto (fun n => ∫ z, (qn n z - q z) * Fn n z) atTop (nhds 0))
    (hweak : Tendsto (fun n => (∫ z, q z * Fn n z) - ∫ z, q z * F z) atTop (nhds 0)) :
    Tendsto (fun n => ∫ z, qn n z * (-(Fn n z))) atTop (nhds (∫ z, q z * (-(F z)))) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hT2raw : Tendsto (fun n => (∫ z, qn n z * Fn n z)
      - ∫ z, q z * F z) atTop (nhds 0) := by
    have hcomb : Tendsto (fun n => (∫ z, (qn n z - q z) * Fn n z)
        + ((∫ z, q z * Fn n z) - ∫ z, q z * F z)) atTop
        (nhds (0 + 0)) := hvan.add hweak
    rw [zero_add] at hcomb
    refine hcomb.congr' (?_ : (fun n => _) =ᶠ[atTop] (fun n => _))
    filter_upwards [hqn, hFn] with n hqn hgn
    have hInt1 : Integrable (fun z => qn n z * Fn n z) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqn.1
        (ae_restrict_of_forall_mem hKm hqn.2) hgn.1 (ae_restrict_of_forall_mem hKm hgn.2)
        (fun z hz => by rw [hFnVanish n z hz, mul_zero])
    have hInt2 : Integrable (fun z => q z * Fn n z) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqm hqbd hgn.1
        (ae_restrict_of_forall_mem hKm hgn.2) (fun z hz => by rw [hFnVanish n z hz, mul_zero])
    have heq : ∫ z, (qn n z - q z) * Fn n z
        = (∫ z, qn n z * Fn n z) - ∫ z, q z * Fn n z := by
      have hcong : ∫ z, (qn n z - q z) * Fn n z
          = ∫ z, (qn n z * Fn n z - q z * Fn n z) :=
        integral_congr_ae (Eventually.of_forall fun z => by ring)
      rw [hcong, integral_sub hInt1 hInt2]
    rw [heq]; ring
  have hT2mid : Tendsto (fun n => ∫ z, qn n z * Fn n z) atTop
      (nhds (∫ z, q z * F z)) := by
    have h := hT2raw.add_const (∫ z, q z * F z)
    simpa using h
  have hT2 : Tendsto (fun n => ∫ z, qn n z * (-(Fn n z))) atTop
      (nhds (∫ z, q z * (-(F z)))) := by
    have hneg := hT2mid.neg
    have hL : ∀ n, -(∫ z, qn n z * Fn n z)
        = ∫ z, qn n z * (-(Fn n z)) := by
      intro n
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    have hR : -(∫ z, q z * F z) = ∫ z, q z * (-(F z)) := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    rw [hR] at hneg
    exact hneg.congr' (Eventually.of_forall hL)
  exact hT2

private theorem integrable_mul_of_bounded_on_support {m : ℕ} {q g : Vec m × ℝ → ℝ}
    {K : Set (Vec m × ℝ)} {M : ℝ} (hKm : MeasurableSet K)
    (hqm : AEStronglyMeasurable q (volume.restrict K))
    (hqbd : ∀ᵐ z ∂(volume.restrict K), |q z| ≤ M) (hg : Integrable g)
    (hgzero : ∀ z, z ∉ K → g z = 0) : Integrable (fun z => q z * g z) := by
  have h : IntegrableOn (fun z => q z * g z) K := by
    have hprod := hg.restrict.mul_bdd hqm (by simpa only [Real.norm_eq_abs] using hqbd)
    exact hprod.congr (Eventually.of_forall fun z => mul_comm (g z) (q z))
  have heq : K.indicator (fun z => q z * g z) = fun z => q z * g z := by
    funext z
    by_cases hz : z ∈ K
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz, hgzero z hz, mul_zero]
  rw [← heq]
  exact h.integrable_indicator hKm

private theorem integral_four_pairings {m : ℕ} (q a b c d : Vec m × ℝ → ℝ)
    (hI1 : Integrable (fun z => q z * (-a z)))
    (hI2 : Integrable (fun z => q z * (-b z)))
    (hI3 : Integrable (fun z => q z * (-c z)))
    (hI4 : Integrable (fun z => q z * (-d z))) :
    (∫ z, q z * (-a z - b z - c z - d z)) = (∫ z, q z * (-a z)) +
      (∫ z, q z * (-b z)) + (∫ z, q z * (-c z)) + ∫ z, q z * (-d z) := by
  have hpt : (fun z => q z * (-a z - b z - c z - d z)) =
      fun z => q z * (-a z) + q z * (-b z) + q z * (-c z) + q z * (-d z) := by
    funext z
    ring
  rw [hpt]
  have hsum := integral_add ((hI1.add hI2).add hI3) hI4
  have h123 := integral_add (hI1.add hI2) hI3
  have h12 := integral_add hI1 hI2
  simp only [Pi.add_apply] at hsum h123 h12
  rw [h123, h12] at hsum
  exact hsum

private theorem tendsto_weak_gradient_pairing {m : ℕ} {T : ℝ}
    {φ q : Vec m × ℝ → ℝ} {b : ℕ → Vec m × ℝ → Vec m}
    {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ}
    (hφ1 : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ2 : HasCompactSupport φ)
    (hφ3 : tsupport φ ⊆ univ ×ˢ Iio T) (hq : IsLocallyBoundedOn m (Iio T) q)
    (hB : IsAdmissibleDrift m (Iio T) B divB)
    (hweak : ∀ g : Vec m × ℝ → ℝ, Integrable g → HasCompactSupport g →
      tsupport g ⊆ univ ×ˢ Iio T → ∀ i,
        Tendsto (fun n => ∫ z, g z * b n z i) atTop (nhds (∫ z, g z * B z i)))
    {M Mq : ℝ} (hqm : AEStronglyMeasurable q (volume.restrict (tsupport φ)))
    (hqbd : ∀ᵐ z ∂(volume.restrict (tsupport φ)), |q z| ≤ Mq)
    (hbbd : ∀ᶠ n in atTop, AEStronglyMeasurable (b n) (volume.restrict (tsupport φ)) ∧
      ∀ z ∈ tsupport φ, ‖b n z‖ ≤ M)
    (Cg : Fin m → ℝ) (hCg : ∀ i, ∀ z ∈ tsupport φ, |gradPair m φ z (basisVec i)| ≤ Cg i) :
    Tendsto (fun n => (∫ z, q z * gradPair m φ z (b n z)) -
      ∫ z, q z * gradPair m φ z (B z)) atTop (nhds 0) := by
  set K := tsupport φ
  have hK : IsCompact K := hφ2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKI : K ⊆ univ ×ˢ Iio T := hφ3
  have hsubJ : K ⊆ (univ : Set (Vec m)) ×ˢ (Prod.snd '' K) :=
    fun z hz => ⟨mem_univ _, mem_image_of_mem _ hz⟩
  have hsumIdentity := integral_gradient_pairing_sum hφ1 hφ2 hqm hqbd Cg hCg
  -- Integrability data for `hweak`'s test functions `gradPair φ (·) (basisVec i) * q`.
  have hgi : ∀ i : Fin m, Integrable (fun z => gradPair m φ z (basisVec i) * q z) volume :=
    fun i => integrable_mul_of_isLocallyBoundedOn hq (continuous_gradPair_joint hφ1 (basisVec i))
      (hasCompactSupport_gradPair_joint hφ1 hφ2 (basisVec i))
      ((tsupport_gradPair_joint_subset hφ1 (basisVec i)).trans hφ3)
  have hgisupp : ∀ i : Fin m, HasCompactSupport (fun z => gradPair m φ z (basisVec i) * q z) :=
    fun i => (hasCompactSupport_gradPair_joint hφ1 hφ2 (basisVec i)).mul_right
  have hgitsupp : ∀ i : Fin m, tsupport (fun z => gradPair m φ z (basisVec i) * q z)
      ⊆ (univ : Set (Vec m)) ×ˢ Iio T := fun i =>
    tsupport_mul_subset_left.trans ((tsupport_gradPair_joint_subset hφ1 (basisVec i)).trans hφ3)
  -- The admissible drift's own global measurability and local boundedness.
  have hBmeasK : AEStronglyMeasurable B (volume.restrict K) :=
    hB.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono hKI le_rfl)
  have hBslice := hB.2.2
  obtain ⟨ΛB, hΛB⟩ := hBslice (Prod.snd '' K) (hK.image continuous_snd)
    (by rintro τ ⟨z, hz, rfl⟩; exact (hKI hz).2)
  have hBnormbdd : ∀ᵐ z ∂(volume.restrict K), ‖B z‖ ≤ (ΛB : ℝ) := by
    have hvol : (volume : Measure (Vec m)).prod (volume.restrict (Prod.snd '' K))
        = volume.restrict ((univ : Set (Vec m)) ×ˢ (Prod.snd '' K)) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    have hae : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec m)) ×ˢ (Prod.snd '' K))),
        ‖B z‖ ≤ (ΛB : ℝ) := by
      rw [← hvol]
      exact ae_prod_of_ae_forall hΛB (fun τ hτ x => hτ.1 x)
    exact hae.filter_mono (ae_mono (Measure.restrict_mono hsubJ le_rfl))
  -- T2: assembling the vanishing and weak-* pieces.
  have hT2weak : Tendsto (fun n => (∫ z, q z * gradPair m φ z (b n z))
      - ∫ z, q z * gradPair m φ z (B z)) atTop (nhds 0) := by
    have heqB : ∫ z, q z * gradPair m φ z (B z)
        = ∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * B z i :=
      hsumIdentity B (ΛB : ℝ) hBmeasK hBnormbdd
    have heqn : ∀ᶠ n in atTop, ∫ z, q z * gradPair m φ z (b n z)
        = ∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * b n z i := by
      filter_upwards [hbbd] with n hbn
      exact hsumIdentity (b n) M hbn.1 (ae_restrict_of_forall_mem hKm hbn.2)
    have hwi : ∀ i : Fin m, Tendsto (fun n => ∫ z, gradPair m φ z (basisVec i) * q z * b n z i)
        atTop (nhds (∫ z, gradPair m φ z (basisVec i) * q z * B z i)) :=
      fun i => hweak _ (hgi i) (hgisupp i) (hgitsupp i) i
    have hsum : Tendsto (fun n => ∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * b n z i)
        atTop (nhds (∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * B z i)) :=
      tendsto_finsetSum Finset.univ (fun i _ => hwi i)
    have hsum' : Tendsto (fun n => (∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * b n z i)
        - ∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * B z i) atTop (nhds 0) := by
      simpa using hsum.sub_const (∑ i : Fin m, ∫ z, gradPair m φ z (basisVec i) * q z * B z i)
    exact hsum'.congr' (heqn.mono fun n hn => by dsimp only; rw [hn, heqB])
  exact hT2weak

/-- Passing a factor converging strongly in `L¹(K)` against a fixed weight `w`, bounded and
vanishing outside `K`, to the limit: the workhorse for the time-derivative and Laplacian
pairings, which do not involve the drift. -/
theorem tendsto_integral_qn_mul_const_of_isLocallyBoundedOn {m : ℕ}
    {K : Set (Vec m × ℝ)} (hK : IsCompact K)
    {qn : ℕ → Vec m × ℝ → ℝ} {q w : Vec m × ℝ → ℝ}
    (hL1 : Tendsto (fun n => ∫⁻ z in K, ‖qn n z - q z‖ₑ) atTop (nhds 0))
    {M : ℝ}
    (hqnbd : ∀ᶠ n in atTop, AEStronglyMeasurable (qn n) (volume.restrict K) ∧
      ∀ z ∈ K, |qn n z| ≤ M)
    (hqm : AEStronglyMeasurable q (volume.restrict K))
    (hqbd : ∀ᵐ z ∂(volume.restrict K), |q z| ≤ M)
    {C : ℝ} (hwm : AEStronglyMeasurable w (volume.restrict K))
    (hwC : ∀ z ∈ K, |w z| ≤ C) (hwsupp : ∀ z, z ∉ K → w z = 0) :
    Tendsto (fun n => ∫ z, qn n z * w z) atTop (nhds (∫ z, q z * w z)) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hwCae : ∀ᵐ z ∂(volume.restrict K), |w z| ≤ C := ae_restrict_of_forall_mem hKm hwC
  have hqw : Integrable (fun z => q z * w z) volume :=
    integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqm hqbd hwm hwCae
      (fun z hz => by rw [hwsupp z hz, mul_zero])
  have hvanish : Tendsto (fun n => ∫ z, (qn n z - q z) * w z) atTop (nhds 0) := by
    refine tendsto_integral_mul_of_tendsto_lintegral_enorm_zero hK hL1 (C := C) ?_ ?_
    · filter_upwards [hqnbd] with n hn
      exact ⟨hn.1.sub hqm, hwm, hwC⟩
    · intro n z hz; rw [hwsupp z hz, mul_zero]
  have hsplit : ∀ᶠ n in atTop, ∫ z, (qn n z - q z) * w z
      = (∫ z, qn n z * w z) - ∫ z, q z * w z := by
    filter_upwards [hqnbd] with n hn
    have hqnw : Integrable (fun z => qn n z * w z) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hn.1
        (ae_restrict_of_forall_mem hKm hn.2) hwm hwCae
        (fun z hz => by rw [hwsupp z hz, mul_zero])
    have heq : ∫ z, (qn n z - q z) * w z = ∫ z, (qn n z * w z - q z * w z) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_); ring
    rw [heq, integral_sub hqnw hqw]
  have hvanish' : Tendsto (fun n => (∫ z, qn n z * w z) - ∫ z, q z * w z) atTop (nhds 0) :=
    hvanish.congr' hsplit
  have := hvanish'.add_const (∫ z, q z * w z)
  simpa using this

/-! ### G-LIMIT -/

theorem isDistributionalDriftDiffusion_of_tendsto {m d : ℕ} {T : ℝ}
    (qn : ℕ → Vec m × ℝ → ℝ) (q : Vec m × ℝ → ℝ) (b : ℕ → Vec m × ℝ → Vec m)
    (divb : ℕ → Vec m × ℝ → ℝ) (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ)
    (hB : IsAdmissibleDrift m (Iio T) B divB)
    (hweak : ∀ g : Vec m × ℝ → ℝ, Integrable g → HasCompactSupport g →
      tsupport g ⊆ univ ×ˢ Iio T →
        (∀ i, Tendsto (fun n => ∫ z, g z * b n z i) atTop (nhds (∫ z, g z * B z i))) ∧
        Tendsto (fun n => ∫ z, g z * divb n z) atTop (nhds (∫ z, g z * divB z)))
    (hq : IsLocallyBoundedOn m (Iio T) q)
    (hbd : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iio T → ∃ M : ℝ,
      ∀ᶠ n in atTop, AEStronglyMeasurable (qn n) (volume.restrict K) ∧
        AEStronglyMeasurable (b n) (volume.restrict K) ∧
        AEStronglyMeasurable (divb n) (volume.restrict K) ∧
        ∀ z ∈ K, |qn n z| ≤ M ∧ ‖b n z‖ ≤ M ∧ |divb n z| ≤ M)
    (hL1 : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iio T →
      Tendsto (fun n => ∫⁻ z in K, ‖qn n z - q z‖ₑ) atTop (nhds 0))
    (hres : ∀ φ ∈ testFunctions m (Iio T), Tendsto (fun n => ∫ z, qn n z *
      (-(timeDeriv m φ z) - gradPair m φ z (b n z) - divb n z * φ z -
        partialLaplacian m d φ z)) atTop (nhds 0)) :
    IsDistributionalDriftDiffusion m d (Iio T) B divB q := by
  intro φ hφ
  obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
  have hK : IsCompact (tsupport φ) := hφ2
  have hKI : tsupport φ ⊆ (univ : Set (Vec m)) ×ˢ Iio T := hφ3
  set K := tsupport φ with hKdef
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨M, hbdM⟩ := hbd K hK hKI
  have hL1K := hL1 K hK hKI
  obtain ⟨Mq, hqbdJ⟩ := hq.2 (Prod.snd '' K) (hK.image continuous_snd)
    (by rintro τ ⟨z, hz, rfl⟩; exact (hKI hz).2)
  have hsubJ : K ⊆ (univ : Set (Vec m)) ×ˢ (Prod.snd '' K) :=
    fun z hz => ⟨mem_univ _, mem_image_of_mem _ hz⟩
  have hqm : AEStronglyMeasurable q (volume.restrict K) :=
    hq.1.mono_measure (Measure.restrict_mono hKI le_rfl)
  have hqbd : ∀ᵐ z ∂(volume.restrict K), |q z| ≤ Mq :=
    hqbdJ.filter_mono (ae_mono (Measure.restrict_mono hsubJ le_rfl))
  -- The second-derivative factory used three times below.
  obtain ⟨CT, CL, hTcont, hTvanish, hCT, hLcont, hLvanish, hCL⟩ :=
    test_operator_bounds (d := d) hφ1 hφ2
  have hqnbd1 : ∀ᶠ n in atTop, AEStronglyMeasurable (qn n) (volume.restrict K) ∧
      ∀ z ∈ K, |qn n z| ≤ max M Mq :=
    hbdM.mono fun n h => ⟨h.1, fun z hz => (h.2.2.2 z hz).1.trans (le_max_left M Mq)⟩
  have hqbd' : ∀ᵐ z ∂(volume.restrict K), |q z| ≤ max M Mq :=
    hqbd.mono fun z hz => hz.trans (le_max_right M Mq)
  -- T1: the time-derivative pairing.
  have hT1 : Tendsto (fun n => ∫ z, qn n z * (-(timeDeriv m φ z))) atTop
      (nhds (∫ z, q z * (-(timeDeriv m φ z)))) :=
    tendsto_integral_qn_mul_const_of_isLocallyBoundedOn hK hL1K hqnbd1 hqm hqbd'
      hTcont.neg.aestronglyMeasurable (fun z hz => by rw [abs_neg]; exact hCT z hz)
      (fun z hz => by rw [hTvanish z hz, neg_zero])
  -- T4: the Laplacian pairing.
  have hT4 : Tendsto (fun n => ∫ z, qn n z * (-(partialLaplacian m d φ z))) atTop
      (nhds (∫ z, q z * (-(partialLaplacian m d φ z)))) :=
    tendsto_integral_qn_mul_const_of_isLocallyBoundedOn hK hL1K hqnbd1 hqm hqbd'
      hLcont.neg.aestronglyMeasurable (fun z hz => by rw [abs_neg]; exact hCL z hz)
      (fun z hz => by rw [hLvanish z hz, neg_zero])
  -- Data shared by T2 (the drift-gradient pairing) and T3 (the divergence pairing).
  have hbbd : ∀ᶠ n in atTop, AEStronglyMeasurable (b n) (volume.restrict K) ∧
      ∀ z ∈ K, ‖b n z‖ ≤ M := hbdM.mono fun n h => ⟨h.2.1, fun z hz => (h.2.2.2 z hz).2.1⟩
  have hdivbbd : ∀ᶠ n in atTop, AEStronglyMeasurable (divb n) (volume.restrict K) ∧
      ∀ z ∈ K, |divb n z| ≤ M := hbdM.mono fun n h => ⟨h.2.2.1, fun z hz => (h.2.2.2 z hz).2.2⟩
  have hgradEq : ∀ n z, gradPair m φ z (b n z)
      = ∑ i : Fin m, b n z i * gradPair m φ z (basisVec i) :=
    fun n z => apply_eq_sum_basisVec (fderiv ℝ (fun x : Vec m => φ (x, z.2)) z.1) (b n z)
  have hgradEqB : ∀ z, gradPair m φ z (B z) = ∑ i : Fin m, B z i * gradPair m φ z (basisVec i) :=
    fun z => apply_eq_sum_basisVec (fderiv ℝ (fun x : Vec m => φ (x, z.2)) z.1) (B z)
  have hCgex : ∀ i : Fin m, ∃ C, ∀ x ∈ K, |gradPair m φ x (basisVec i)| ≤ C := fun i =>
    hK.exists_bound_of_continuousOn (continuous_gradPair_joint hφ1 (basisVec i)).continuousOn
  choose Cg hCg using hCgex
  set Cgrad : ℝ := ∑ i : Fin m, Cg i with hCgraddef
  obtain ⟨Cφ, hCφ⟩ := hK.exists_bound_of_continuousOn hφ1.continuous.continuousOn
  -- T2: the drift-gradient pairing.
  have hgradbBdd : ∀ᶠ n in atTop, AEStronglyMeasurable (fun z => gradPair m φ z (b n z))
      (volume.restrict K) ∧ ∀ z ∈ K, |gradPair m φ z (b n z)| ≤ M * Cgrad := by
    filter_upwards [hbbd] with n hbn
    have heqz : (fun z => gradPair m φ z (b n z))
        = fun z => ∑ i : Fin m, b n z i * gradPair m φ z (basisVec i) := funext (hgradEq n)
    refine ⟨?_, ?_⟩
    · rw [heqz]
      refine aestronglyMeasurable_finsetSum Finset.univ (fun i _ => ?_)
      exact (((continuous_apply i).comp_aestronglyMeasurable hbn.1).mul
        (continuous_gradPair_joint hφ1 (basisVec i)).aestronglyMeasurable)
    · intro z hz
      rw [hgradEq n z]
      have hbi : ∀ i : Fin m, |b n z i| ≤ M := fun i => by
        rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (b n z) i).trans (hbn.2 z hz)
      calc |∑ i : Fin m, b n z i * gradPair m φ z (basisVec i)|
          ≤ ∑ i : Fin m, |b n z i * gradPair m φ z (basisVec i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin m, M * Cg i := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [abs_mul]
            exact mul_le_mul (hbi i) (hCg i z hz) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hbi i))
        _ = M * Cgrad := by rw [hCgraddef, Finset.mul_sum]
  have hgradbVanish : ∀ n, ∀ z, z ∉ K → gradPair m φ z (b n z) = 0 := by
    intro n z hz
    rw [hgradEq n z]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [image_eq_zero_of_notMem_tsupport
      (fun hc => hz (tsupport_gradPair_joint_subset hφ1 (basisVec i) hc)), mul_zero]
  have hT2van : Tendsto (fun n => ∫ z, (qn n z - q z) * gradPair m φ z (b n z)) atTop
      (nhds 0) := by
    refine tendsto_integral_mul_of_tendsto_lintegral_enorm_zero hK hL1K (C := M * Cgrad) ?_ ?_
    · filter_upwards [hqnbd1, hgradbBdd] with n hqn hgn
      exact ⟨hqn.1.sub hqm, hgn.1, hgn.2⟩
    · intro n z hz; rw [hgradbVanish n z hz, mul_zero]
  -- The generic decomposition of `∫ q * gradPair φ (·) (W ·)` into its basis components,
  -- valid for any vector field `W` that is a.e.-strongly-measurable and a.e.-bounded on `K`.
  have hT2weak := tendsto_weak_gradient_pairing hφ1 hφ2 hφ3 hq hB
    (fun g hg hc hs => (hweak g hg hc hs).1) hqm hqbd hbbd Cg hCg
  have hT2 := tendsto_negative_pairing_of_difference hK hqm hqbd hqnbd1 hgradbBdd
    hgradbVanish hT2van hT2weak
  -- T3: the divergence pairing.
  have hdivphibdd : ∀ᶠ n in atTop, AEStronglyMeasurable (fun z => divb n z * φ z)
      (volume.restrict K) ∧ ∀ z ∈ K, |divb n z * φ z| ≤ M * Cφ := by
    filter_upwards [hdivbbd] with n hdn
    refine ⟨hdn.1.mul hφ1.continuous.aestronglyMeasurable, fun z hz => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hdn.2 z hz) (by rw [← Real.norm_eq_abs]; exact hCφ z hz) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hdn.2 z hz))
  have hdivphivanish : ∀ n, ∀ z, z ∉ K → divb n z * φ z = 0 := fun n z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hT3van : Tendsto (fun n => ∫ z, (qn n z - q z) * (divb n z * φ z)) atTop (nhds 0) := by
    refine tendsto_integral_mul_of_tendsto_lintegral_enorm_zero hK hL1K (C := M * Cφ) ?_ ?_
    · filter_upwards [hqnbd1, hdivphibdd] with n hqn hdn
      exact ⟨hqn.1.sub hqm, hdn.1, hdn.2⟩
    · intro n z hz; rw [hdivphivanish n z hz, mul_zero]
  have hgdiv : Integrable (fun z => φ z * q z) volume :=
    integrable_mul_of_isLocallyBoundedOn hq hφ1.continuous hφ2 hφ3
  have hgdivsupp : HasCompactSupport (fun z => φ z * q z) := hφ2.mul_right
  have hgdivtsupp : tsupport (fun z => φ z * q z) ⊆ (univ : Set (Vec m)) ×ˢ Iio T :=
    tsupport_mul_subset_left.trans hφ3
  have hT3weak : Tendsto (fun n => (∫ z, q z * (divb n z * φ z))
      - ∫ z, q z * (divB z * φ z)) atTop (nhds 0) := by
    have hw := (hweak _ hgdiv hgdivsupp hgdivtsupp).2
    have heq : ∀ n, ∫ z, φ z * q z * divb n z = ∫ z, q z * (divb n z * φ z) :=
      fun n => integral_congr_ae (Eventually.of_forall fun z => by ring)
    have heqB : ∫ z, φ z * q z * divB z = ∫ z, q z * (divB z * φ z) :=
      integral_congr_ae (Eventually.of_forall fun z => by ring)
    have hw' : Tendsto (fun n => ∫ z, q z * (divb n z * φ z)) atTop
        (nhds (∫ z, q z * (divB z * φ z))) := by
      have hfun : (fun n => ∫ z, q z * (divb n z * φ z)) = fun n => ∫ z, φ z * q z * divb n z :=
        funext fun n => (heq n).symm
      rw [hfun, ← heqB]
      exact hw
    simpa using hw'.sub_const (∫ z, q z * (divB z * φ z))
  have hT3 := tendsto_negative_pairing_of_difference hK hqm hqbd hqnbd1 hdivphibdd
    hdivphivanish hT3van hT3weak
  -- Boundedness/vanishing data for `gradPair φ (B ·)` and `divB · φ`, needed for the final
  -- integrability and limit-uniqueness argument.
  have hgradBvanish : ∀ z, z ∉ K → gradPair m φ z (B z) = 0 := fun z hz => by
    rw [hgradEqB z]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [image_eq_zero_of_notMem_tsupport
      (fun hc => hz (tsupport_gradPair_joint_subset hφ1 (basisVec i) hc)), mul_zero]
  have hdivBphivanish : ∀ z, z ∉ K → divB z * φ z = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  -- The four limit values `L1, L2, L3, L4` are globally integrable against `q`.
  have hIntL1 : Integrable (fun z => q z * (-(timeDeriv m φ z))) volume :=
    integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqm hqbd hTcont.neg.aestronglyMeasurable
      (ae_restrict_of_forall_mem hKm fun z hz => by rw [abs_neg]; exact hCT z hz)
      (fun z hz => by rw [hTvanish z hz, neg_zero, mul_zero])
  have hIntL2 : Integrable (fun z => q z * (-(gradPair m φ z (B z)))) volume :=
    integrable_mul_of_bounded_on_support hKm hqm hqbd
      (integrable_gradPair_mul_of_isAdmissibleDrift hB ⟨hφ1, hφ2, hφ3⟩).neg
      (fun z hz => by rw [hgradBvanish z hz, neg_zero])
  have hIntL3 : Integrable (fun z => q z * (-(divB z * φ z))) volume :=
    integrable_mul_of_bounded_on_support hKm hqm hqbd
      (integrable_divB_mul_of_isAdmissibleDrift hB ⟨hφ1, hφ2, hφ3⟩).neg
      (fun z hz => by rw [hdivBphivanish z hz, neg_zero])
  have hIntL4 : Integrable (fun z => q z * (-(partialLaplacian m d φ z))) volume :=
    integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqm hqbd hLcont.neg.aestronglyMeasurable
      (ae_restrict_of_forall_mem hKm fun z hz => by rw [abs_neg]; exact hCL z hz)
      (fun z hz => by rw [hLvanish z hz, neg_zero, mul_zero])
  -- The full residual against `q` splits into the four limit values.
  have hsplit : ∫ z, q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z -
      partialLaplacian m d φ z) = (∫ z, q z * (-(timeDeriv m φ z)))
      + (∫ z, q z * (-(gradPair m φ z (B z)))) + (∫ z, q z * (-(divB z * φ z)))
      + ∫ z, q z * (-(partialLaplacian m d φ z)) := by
    exact integral_four_pairings q _ _ _ _ hIntL1 hIntL2 hIntL3 hIntL4
  -- The finite-`n` residual against `qn n` splits into the four sequences `S1, ..., S4`.
  have hSsplit : ∀ᶠ n in atTop, ∫ z, qn n z * (-(timeDeriv m φ z) - gradPair m φ z (b n z) -
      divb n z * φ z - partialLaplacian m d φ z) = (∫ z, qn n z * (-(timeDeriv m φ z)))
      + (∫ z, qn n z * (-(gradPair m φ z (b n z)))) + (∫ z, qn n z * (-(divb n z * φ z)))
      + ∫ z, qn n z * (-(partialLaplacian m d φ z)) := by
    filter_upwards [hqnbd1, hgradbBdd, hdivphibdd] with n hqn hgn hdn
    have hI1 : Integrable (fun z => qn n z * (-(timeDeriv m φ z))) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqn.1
        (ae_restrict_of_forall_mem hKm hqn.2) hTcont.neg.aestronglyMeasurable
        (ae_restrict_of_forall_mem hKm fun z hz => by rw [abs_neg]; exact hCT z hz)
        (fun z hz => by rw [hTvanish z hz, neg_zero, mul_zero])
    have hI2 : Integrable (fun z => qn n z * (-(gradPair m φ z (b n z)))) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqn.1
        (ae_restrict_of_forall_mem hKm hqn.2) hgn.1.neg
        (ae_restrict_of_forall_mem hKm fun z hz => by rw [abs_neg]; exact hgn.2 z hz)
        (fun z hz => by rw [hgradbVanish n z hz, neg_zero, mul_zero])
    have hI3 : Integrable (fun z => qn n z * (-(divb n z * φ z))) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqn.1
        (ae_restrict_of_forall_mem hKm hqn.2) hdn.1.neg
        (ae_restrict_of_forall_mem hKm fun z hz => by rw [abs_neg]; exact hdn.2 z hz)
        (fun z hz => by rw [hdivphivanish n z hz, neg_zero, mul_zero])
    have hI4 : Integrable (fun z => qn n z * (-(partialLaplacian m d φ z))) volume :=
      integrable_mul_of_bdd_isCompact_of_vanishing_outside hK hqn.1
        (ae_restrict_of_forall_mem hKm hqn.2) hLcont.neg.aestronglyMeasurable
        (ae_restrict_of_forall_mem hKm fun z hz => by rw [abs_neg]; exact hCL z hz)
        (fun z hz => by rw [hLvanish z hz, neg_zero, mul_zero])
    exact integral_four_pairings (qn n) _ _ _ _ hI1 hI2 hI3 hI4
  have hSTendsto : Tendsto (fun n => (∫ z, qn n z * (-(timeDeriv m φ z)))
      + (∫ z, qn n z * (-(gradPair m φ z (b n z)))) + (∫ z, qn n z * (-(divb n z * φ z)))
      + ∫ z, qn n z * (-(partialLaplacian m d φ z))) atTop
      (nhds ((∫ z, q z * (-(timeDeriv m φ z))) + (∫ z, q z * (-(gradPair m φ z (B z))))
        + (∫ z, q z * (-(divB z * φ z))) + ∫ z, q z * (-(partialLaplacian m d φ z)))) :=
    ((hT1.add hT2).add hT3).add hT4
  have hSTendstoZero : Tendsto (fun n => (∫ z, qn n z * (-(timeDeriv m φ z)))
      + (∫ z, qn n z * (-(gradPair m φ z (b n z)))) + (∫ z, qn n z * (-(divb n z * φ z)))
      + ∫ z, qn n z * (-(partialLaplacian m d φ z))) atTop (nhds 0) :=
    (hres φ ⟨hφ1, hφ2, hφ3⟩).congr' hSsplit
  have hzeroSum : (∫ z, q z * (-(timeDeriv m φ z))) + (∫ z, q z * (-(gradPair m φ z (B z))))
      + (∫ z, q z * (-(divB z * φ z))) + ∫ z, q z * (-(partialLaplacian m d φ z)) = 0 :=
    tendsto_nhds_unique hSTendsto hSTendstoZero
  refine ⟨?_, ?_⟩
  · have hfinal : Integrable (fun z => q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) -
        divB z * φ z - partialLaplacian m d φ z)) := by
      convert ((hIntL1.add hIntL2).add hIntL3).add hIntL4 using 1
      funext z
      simp only [Pi.add_apply]
      ring
    exact hfinal.restrict
  · rw [hsplit]; exact hzeroSum

end CIV
