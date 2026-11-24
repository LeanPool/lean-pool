/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorBall
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveDistributionMeasure

/-!
# Existence of the local bounded Bedford–Taylor measure

On every relatively compact open subset the convergence theorem gives a limit
measure for the diagonal family of a locally bounded plurisubharmonic function.
Two such measures agree on the smaller set, since both are limits along the
same approximations; the measures of an exhaustion glue to one measure on the
whole domain.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder Distributions

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Measures finite on compact subsets of an open set and with equal integrals
against test functions there have equal restrictions. -/
theorem restrict_eq_of_testFunction_integral_eq {U : Opens (ComplexModel n)}
    {μ ν : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ z, φ z ∂μ = ∫ z, φ z ∂ν) :
    μ.restrict (U : Set (ComplexModel n)) = ν.restrict (U : Set (ComplexModel n)) := by
  let μU : Measure U := μ.comap Subtype.val
  let νU : Measure U := ν.comap Subtype.val
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hval : MeasurableEmbedding (Subtype.val : U → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hfin (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ U → ρ K < ⊤) :
      IsFiniteMeasureOnCompacts (ρ.comap (Subtype.val : U → ComplexModel n)) := ⟨by
    intro K hK
    rw [show ρ.comap Subtype.val K = ρ (Subtype.val '' K) by
      exact comap_subtype_coe_apply U.isOpen.measurableSet ρ K]
    exact hρ _ (hK.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.2)⟩
  let _ := hfin μ hμf
  let _ := hfin ν hνf
  let _ : IsLocallyFiniteMeasure μU := inferInstance
  let _ : IsLocallyFiniteMeasure νU := inferInstance
  let _ : μU.Regular := inferInstance
  let _ : νU.Regular := inferInstance
  have hrange : Set.range (Subtype.val : U → ComplexModel n) = (U : Set (ComplexModel n)) := by
    ext z; simp
  have hmapμ : μU.map Subtype.val = μ.restrict (U : Set (ComplexModel n)) := by
    change (μ.comap Subtype.val).map Subtype.val = _
    rw [hval.map_comap, hrange]
  have hmapν : νU.map Subtype.val = ν.restrict (U : Set (ComplexModel n)) := by
    change (ν.comap Subtype.val).map Subtype.val = _
    rw [hval.map_comap, hrange]
  have hsub : μU = νU := by
    apply Pending.Measure.eq_of_testFunction_integral_eq
    intro φ
    have hzero : ∀ z ∉ (U : Set (ComplexModel n)), φ z = 0 := fun z hz ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hz (φ.tsupport_subset h)
    calc (∫ z : U, φ z ∂μU) = ∫ z, φ z ∂(μU.map Subtype.val) :=
          (hval.integral_map (φ : ComplexModel n → ℝ)).symm
      _ = ∫ z, φ z ∂μ := by rw [hmapμ, setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      _ = ∫ z, φ z ∂ν := h φ
      _ = ∫ z, φ z ∂(νU.map Subtype.val) := by
          rw [hmapν, setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      _ = ∫ z : U, φ z ∂νU := hval.integral_map (φ : ComplexModel n → ℝ)
  rw [← hmapμ, ← hmapν, hsub]

theorem IsLocallyBoundedPshOn.exists_abs_le {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ C, ∀ z ∈ K, |u z| ≤ C := by
  classical
  have hloc : ∀ z ∈ K, ∃ V : Set (ComplexModel n), V ∈ 𝓝 z ∧ ∃ C : ℝ, ∀ w ∈ V, |u w| ≤ C := by
    intro z hz
    obtain ⟨V, hzV, -, C, hC⟩ := hu.2 z (hKΩ hz)
    exact ⟨V, V.isOpen.mem_nhds hzV, C, hC⟩
  choose! V hV C hC using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover V hV
  refine ⟨∑ x ∈ t, |C x|, fun z hz ↦ ?_⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hz)
  exact (hC x (htK x hxt) z hzx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x ↦ |C x|) (fun _ _ ↦ abs_nonneg _) hxt))

theorem isDecApprox_of_isDecreasingApproximation {Ω U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hUΩ : U ≤ Ω)
    {f : ℕ → ComplexModel n → ℝ} (hf : IsDecreasingApproximation U u f) :
    IsDecApprox U u f := by
  refine ⟨fun j ↦ ⟨(hf.1 j).1, (hf.1 j).2.2⟩, hf.2.1, hf.2.2, fun K hK hKU ↦ ?_⟩
  obtain ⟨C, hC⟩ := IsLocallyBoundedPshOn.exists_abs_le hu hK (hKU.trans hUΩ)
  exact ⟨-C, by rintro _ ⟨z, hz, rfl⟩; exact neg_le_of_abs_le (hC z hz)⟩

theorem isAdmissible_diagonal {Ω U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hUΩ : U ≤ Ω) {f : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation U u f) :
    IsAdmissible n U (fun _ ↦ u) (fun _ ↦ f) :=
  ⟨fun _ ↦ isDecApprox_of_isDecreasingApproximation hu hUΩ hf,
    fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩

theorem weaklyTendsTo_of_tendstoMixed {U : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    (hf : ∀ j, IsSmoothPshOn U (f j)) {μ : Measure (ComplexModel n)}
    (h : TendstoMixed U (fun _ ↦ f) μ) : WeaklyTendsTo U f hf μ := by
  intro φ hφ hφc hφU
  refine (h φ hφ hφc hφU).congr fun j ↦ ?_
  rw [(smoothMeasure_test_integral (hf j) φ hφ hφc hφU).2.2]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
    simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]]
  simp only [mixedDensity_diagonal]

theorem restrict_eq_of_claims {q : ℕ} {U' U : Opens (ComplexModel n)} (hU'U : U' ≤ U)
    {u : Fin n → ComplexModel n → ℝ} {μ μ' : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) (hμ'f : ∀ K, IsCompact K → K ⊆ U' → μ' K < ⊤)
    (hμ : ∀ F, IsAdmissible q U u F → TendstoMixed U F μ)
    (hμ' : ∀ F, IsAdmissible q U' u F → TendstoMixed U' F μ')
    (hex : ∃ F, IsAdmissible q U u F) :
    μ.restrict (U' : Set (ComplexModel n)) = μ'.restrict (U' : Set (ComplexModel n)) := by
  obtain ⟨F, hF⟩ := hex
  refine restrict_eq_of_testFunction_integral_eq (fun K hK hKU ↦ hμf K hK (hKU.trans hU'U))
    hμ'f fun φ ↦ ?_
  exact tendsto_nhds_unique (hμ F hF φ φ.continuous φ.hasCompactSupport
    (φ.tsupport_subset.trans hU'U)) (hμ' F (hF.mono hU'U) φ φ.continuous φ.hasCompactSupport
    φ.tsupport_subset)

/-- An exhaustion of an open set by relatively compact open subsets absorbing
every compact subset. -/
theorem exists_exhaustion (Ω : Opens (ComplexModel n)) :
    ∃ U : ℕ → Opens (ComplexModel n), Monotone U ∧ (∀ m, RelativelyCompactIn (U m) Ω) ∧
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → ∃ m, K ⊆ U m := by
  set U : ℕ → Opens (ComplexModel n) := fun m ↦
    ⟨ball 0 (m + 1) ∩ {z | ENNReal.ofReal (1 / (m + 1)) <
      Metric.infEDist z (Ω : Set (ComplexModel n))ᶜ},
      isOpen_ball.inter (isOpen_lt continuous_const Metric.continuous_infEDist)⟩ with hU
  refine ⟨U, fun m m' hmm' z hz ↦ ?_, fun m ↦ ?_, fun K hK hKΩ ↦ ?_⟩
  · have hm : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    refine ⟨ball_subset_ball (by linarith) hz.1, ?_⟩
    change ENNReal.ofReal _ < _
    refine lt_of_le_of_lt ?_ hz.2
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) (by linarith))
  · have hsub : closure (U m : Set (ComplexModel n)) ⊆ closedBall 0 (m + 1) ∩
        {z | ENNReal.ofReal (1 / (m + 1)) ≤ Metric.infEDist z (Ω : Set (ComplexModel n))ᶜ} :=
      closure_minimal (fun z hz ↦ ⟨ball_subset_closedBall hz.1, by
        have h2 : ENNReal.ofReal (1 / (m + 1)) < Metric.infEDist z (Ω : Set (ComplexModel n))ᶜ :=
          hz.2
        exact h2.le⟩)
        (isClosed_closedBall.inter (isClosed_le continuous_const Metric.continuous_infEDist))
    refine ⟨(isCompact_closedBall 0 (m + 1)).of_isClosed_subset isClosed_closure
      (hsub.trans inter_subset_left), fun z hz ↦ ?_⟩
    by_contra hzΩ
    have h0 : Metric.infEDist z (Ω : Set (ComplexModel n))ᶜ = 0 := Metric.infEDist_zero_of_mem hzΩ
    have := (hsub hz).2
    rw [mem_ofPred_eq, h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
    have : (0 : ℝ) < 1 / (m + 1) := by positivity
    linarith
  · rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, by simp [hKe]⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
    obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hKne
      ((Metric.continuous_infEDist (s := (Ω : Set (ComplexModel n))ᶜ)).continuousOn (s := K))
    have hpos : 0 < Metric.infEDist x (Ω : Set (ComplexModel n))ᶜ := by
      rw [pos_iff_ne_zero]
      intro h0
      have hmem := Metric.mem_closure_iff_infEDist_zero.mpr h0
      rw [(Ω.isOpen.isClosed_compl).closure_eq] at hmem
      exact hmem (hKΩ hxK)
    obtain ⟨δ, hδ, hδlt⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ <
        Metric.infEDist x (Ω : Set (ComplexModel n))ᶜ := by
      rcases eq_or_ne (Metric.infEDist x (Ω : Set (ComplexModel n))ᶜ) ⊤ with htop | htop
      · exact ⟨1, one_pos, by simp [htop]⟩
      · refine ⟨(Metric.infEDist x (Ω : Set (ComplexModel n))ᶜ).toReal / 2,
          by have := ENNReal.toReal_pos hpos.ne' htop; positivity, ?_⟩
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop]
        have := ENNReal.toReal_pos hpos.ne' htop
        linarith
    obtain ⟨m, hm⟩ := exists_nat_gt (max R (1 / δ))
    refine ⟨m, fun z hz ↦ ⟨?_, ?_⟩⟩
    · exact ball_subset_ball (by linarith [le_max_left R (1 / δ)]) (hR hz)
    · change ENNReal.ofReal _ < _
      refine lt_of_le_of_lt ?_ (hδlt.trans_le (hxmin hz))
      apply ENNReal.ofReal_le_ofReal
      have h1 : 1 / δ < m + 1 := by linarith [le_max_right R (1 / δ)]
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at h1
      linarith

/-- **Gluing.** For a tuple admitting decreasing smooth approximations on every
relatively compact open subset of `Ω` there is a measure on `Ω`, finite on
compact subsets, to which the mixed densities of every such approximation converge. -/
theorem exists_measure_tendstoMixed_of_exists {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ}
    (hadm : ∀ V : Opens (ComplexModel n), RelativelyCompactIn V Ω → ∃ F, IsAdmissible n V u F) :
    ∃ μ : Measure (ComplexModel n), μ (Ω : Set (ComplexModel n))ᶜ = 0 ∧
      (∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
      ∀ V : Opens (ComplexModel n), RelativelyCompactIn V Ω →
        ∀ F, IsAdmissible n V u F → TendstoMixed V F μ := by
  classical
  obtain ⟨U, hUmono, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  choose μs hμsc hμsf hμsP using fun m ↦ pClaim_all (n := n) (U m) u
  have hex (m : ℕ) : ∃ F, IsAdmissible n (U m) u F := hadm (U m) (hUrc m)
  have hcons {m m' : ℕ} (h : m ≤ m') :
      (μs m').restrict (U m : Set (ComplexModel n)) = (μs m).restrict (U m) :=
    restrict_eq_of_claims (hUmono h) (hμsf m') (hμsf m) (hμsP m') (hμsP m) (hex m')
  set D : ℕ → Set (ComplexModel n) := disjointed fun m ↦ (U m : Set (ComplexModel n)) with hD
  have hDsub (j : ℕ) : D j ⊆ U j := disjointed_subset _ _
  have hDmeas (j : ℕ) : MeasurableSet (D j) :=
    MeasurableSet.disjointed (fun m ↦ (U m).isOpen.measurableSet) j
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed _
  set μ : Measure (ComplexModel n) := Measure.sum fun j ↦ (μs j).restrict (D j) with hμ
  have hrestrict (m : ℕ) : μ.restrict (U m : Set (ComplexModel n)) = (μs m).restrict (U m) := by
    rw [hμ, Measure.restrict_sum _ (U m).isOpen.measurableSet]
    have hpiece (j : ℕ) : ((μs j).restrict (D j)).restrict (U m : Set (ComplexModel n)) =
        (μs m).restrict (D j ∩ U m) := by
      rw [Measure.restrict_restrict (U m).isOpen.measurableSet]
      rcases le_or_gt j m with hjm | hjm
      · have h1 : (U m : Set (ComplexModel n)) ∩ D j = D j :=
          inter_eq_right.mpr ((hDsub j).trans (hUmono hjm))
        have h2 : D j ∩ (U m : Set (ComplexModel n)) = D j :=
          inter_eq_left.mpr ((hDsub j).trans (hUmono hjm))
        rw [h1, h2, ← Measure.restrict_restrict_of_subset (hDsub j), ← hcons hjm,
          Measure.restrict_restrict_of_subset (hDsub j)]
      · have hdisj : Disjoint (U m : Set (ComplexModel n)) (D j) := by
          refine Set.disjoint_left.2 fun z hzm hzD ↦ ?_
          rw [hD, disjointed_eq_inter_compl] at hzD
          exact (mem_iInter₂.1 hzD.2 m hjm) hzm
        rw [hdisj.inter_eq, inter_comm, hdisj.inter_eq]
        simp
    simp only [hpiece]
    rw [← Measure.restrict_iUnion (fun i j hij ↦ (hDdisj hij).mono inter_subset_left
      inter_subset_left) fun j ↦ (hDmeas j).inter (U m).isOpen.measurableSet]
    congr 1
    rw [← iUnion_inter, iUnion_disjointed]
    exact inter_eq_right.mpr (subset_iUnion (fun m ↦ (U m : Set (ComplexModel n))) m)
  refine ⟨μ, ?_, fun K hK hKΩ ↦ ?_, fun V hV F hF φ hφ hφc hφV ↦ ?_⟩
  · rw [hμ, Measure.sum_apply _ Ω.isOpen.measurableSet.compl]
    refine tsum_eq_zero_iff.mpr fun j ↦ ?_
    rw [Measure.restrict_apply Ω.isOpen.measurableSet.compl]
    have : (Ω : Set (ComplexModel n))ᶜ ∩ D j = ∅ :=
      eq_empty_of_forall_notMem fun z hz ↦ hz.1 (hUΩ j (hDsub j hz.2))
    simp [this]
  · obtain ⟨m, hKm⟩ := hUabs K hK hKΩ
    calc μ K = μ.restrict (U m : Set (ComplexModel n)) K := by
          rw [Measure.restrict_apply' (U m).isOpen.measurableSet, inter_eq_left.mpr hKm]
      _ = (μs m).restrict (U m) K := by rw [hrestrict m]
      _ ≤ μs m K := Measure.restrict_apply_le _ _
      _ < ⊤ := hμsf m K hK hKm
  · obtain ⟨m, hVm⟩ := hUabs _ hV.1 hV.2
    have hVU : V ≤ U m := subset_closure.trans hVm
    obtain ⟨μV, -, hμVf, hμVP⟩ := pClaim_all (n := n) V u
    have hconsV := restrict_eq_of_claims hVU (hμsf m) hμVf (hμsP m) hμVP (hex m)
    have h := hμVP F hF φ hφ hφc hφV
    have hzeroV : ∀ z ∉ (V : Set (ComplexModel n)), φ z = 0 := fun z hz ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφV h)
    have hzeroU : ∀ z ∉ (U m : Set (ComplexModel n)), φ z = 0 := fun z hz ↦
      hzeroV z fun h ↦ hz (hVU h)
    have heq : ∫ z, φ z ∂μV = ∫ z, φ z ∂μ := by
      calc ∫ z, φ z ∂μV = ∫ z in (V : Set (ComplexModel n)), φ z ∂μV :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroV).symm
        _ = ∫ z in (V : Set (ComplexModel n)), φ z ∂(μs m) := by rw [hconsV]
        _ = ∫ z, φ z ∂(μs m).restrict (U m) := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroV,
              setIntegral_eq_integral_of_forall_compl_eq_zero hzeroU]
        _ = ∫ z, φ z ∂μ.restrict (U m) := by rw [hrestrict m]
        _ = ∫ z, φ z ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero hzeroU
    rw [← heq]
    exact h

/-- Gluing for a tuple of locally bounded PSH functions. -/
theorem exists_measure_tendstoMixed {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    ∃ μ : Measure (ComplexModel n), μ (Ω : Set (ComplexModel n))ᶜ = 0 ∧
      (∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
      ∀ V : Opens (ComplexModel n), RelativelyCompactIn V Ω →
        ∀ F, IsAdmissible n V u F → TendstoMixed V F μ := by
  refine exists_measure_tendstoMixed_of_exists fun V hV ↦ ?_
  choose f hf using fun i ↦ HolomorphicPullback.exists_decreasingMollifierApproximation (hu i) hV
  exact ⟨f, fun i ↦ isDecApprox_of_isDecreasingApproximation (hu i) (subset_closure.trans hV.2)
    (hf i), fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩

/-- **Existence of the local bounded Bedford–Taylor measure.** -/
theorem exists_isLocalBedfordTaylorMeasure {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) :
    ∃ μ : Measure (ComplexModel n), IsLocalBedfordTaylorMeasure Ω u μ := by
  obtain ⟨μ, hμc, hμf, hμT⟩ := exists_measure_tendstoMixed (n := n) (u := fun _ ↦ u) fun _ ↦ hu
  refine ⟨μ, hu, hμc, hμf, fun V hV ↦
    ⟨HolomorphicPullback.exists_decreasingMollifierApproximation hu hV, fun f hf ↦ ?_⟩⟩
  exact weaklyTendsTo_of_tendstoMixed hf.1
    (hμT V hV _ (isAdmissible_diagonal hu (subset_closure.trans hV.2) hf))

/-- **Existence of the local mixed bounded Bedford–Taylor measure**, given
existence of mixed decreasing approximations. -/
theorem exists_isLocalMixedBedfordTaylorMeasure {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    (happrox : ∀ U : Opens (ComplexModel n), RelativelyCompactIn U Ω →
      ∃ f, IsDecreasingMixedApproximation U u f) :
    ∃ μ : Measure (ComplexModel n), IsLocalMixedBedfordTaylorMeasure Ω u μ := by
  obtain ⟨μ, hμc, hμf, hμT⟩ := exists_measure_tendstoMixed (n := n) (u := u) hu
  refine ⟨μ, hu, hμc, hμf, fun V hV ↦ ⟨happrox V hV, fun f hf φ hφ hφc hφV ↦ ?_⟩⟩
  have hVΩ : V ≤ Ω := subset_closure.trans hV.2
  have hadm : IsAdmissible n V u (fun i k ↦ f k i) :=
    ⟨fun i ↦ isDecApprox_of_isDecreasingApproximation (hu i) hVΩ (hf.component i),
      fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  refine (hμT V hV _ hadm φ hφ hφc hφV).congr fun j ↦ ?_
  have hpsd : ∀ i, IsSmoothPsdOn V (f j i) := fun i ↦
    ⟨((hf.1 j).component i).1, ((hf.1 j).component i).2.2⟩
  exact (integral_densityMeasure hpsd hφV).symm

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
