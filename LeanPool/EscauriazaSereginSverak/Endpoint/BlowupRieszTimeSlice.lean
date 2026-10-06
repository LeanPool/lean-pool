/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszSliceCore
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.TsupportProduct

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
noncomputable section
namespace ESS

/-- A separated smooth space-time test has compact support in the product
of the spatial and time supports. -/
private theorem blowup_riesz_product_test_support
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψc : HasCompactSupport ψ) (hθc : HasCompactSupport θ) :
    HasCompactSupport (fun z : Vec3 × ℝ => ψ z.1 * θ z.2) := by
  change IsCompact (tsupport (fun z : Vec3 × ℝ => ψ z.1 * θ z.2))
  rw [CKN.tsupport_mul_prod_eq]
  exact hψc.isCompact.prod hθc.isCompact

/-- Exterior-supported tensors give a zero space-time Laplacian pairing for
separated spatial and temporal tests. -/
theorem blowup_rieszPressure_exterior_product_pairing_zero
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (U : Set Vec3)
    (hzero : ∀ i j z, z.1 ∈ U → F i j z = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) :
    ∫ z : Vec3 × ℝ,
      CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF z *
        (θ z.2 * CKN.spatialLaplacian ψ z.1) = 0 := by
  let φ : Vec3 × ℝ → ℝ := fun z => ψ z.1 * θ z.2
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  have hφc : HasCompactSupport φ := blowup_riesz_product_test_support hψc hθc
  have hφU : ∀ z ∈ tsupport φ, z.1 ∈ U := by
    intro z hz
    rw [CKN.tsupport_mul_prod_eq] at hz
    exact hψU hz.1
  have hdist := blowup_rieszPressureSpaceTime_exterior_distribution_zero
    F hF U hzero hφ hφc hφU
  simpa only [φ, blowup_rieszPressureJointLaplacian_product hψ hθ] using hdist

/-- The product of an `L^(3/2)` pressure and a separated smooth compact test
with a spatial Laplacian is integrable on space-time. -/
theorem blowup_pressure_mul_product_laplacian_integrable
    {p : Vec3 × ℝ → ℝ}
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) :
    Integrable (fun z : Vec3 × ℝ =>
      p z * (θ z.2 * CKN.spatialLaplacian ψ z.1)) volume := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  have hHolder : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  let : (ENNReal.ofReal (3 / 2 : ℝ)).HolderConjugate
      (ENNReal.ofReal (3 : ℝ)) := Real.HolderConjugate.ennrealOfReal hHolder
  have hLapSmooth : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialLaplacian ψ) :=
    CKN.contDiff_spatialLaplacian_smooth hψ
  have hLapCompact : HasCompactSupport (CKN.spatialLaplacian ψ) :=
    CKN.Foundation.Heat.laplacian_compact_support_global hψc
  have htestCont : Continuous (fun z : Vec3 × ℝ =>
      θ z.2 * CKN.spatialLaplacian ψ z.1) :=
    (hθ.continuous.comp continuous_snd).mul
      (hLapSmooth.continuous.comp continuous_fst)
  have htestCompact : HasCompactSupport (fun z : Vec3 × ℝ =>
      θ z.2 * CKN.spatialLaplacian ψ z.1) := by
    have h := blowup_riesz_product_test_support hLapCompact hθc
    convert h using 1
    ext z
    ring
  have htestLp : MemLp (fun z : Vec3 × ℝ =>
      θ z.2 * CKN.spatialLaplacian ψ z.1)
      (ENNReal.ofReal (3 : ℝ)) volume :=
    htestCont.memLp_of_hasCompactSupport htestCompact
  exact hp.integrable_mul htestLp

/-- Fubini separates the time weight from a pressure Laplacian pairing. -/
theorem blowup_pressure_product_laplacian_fubini
    {p : Vec3 × ℝ → ℝ}
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) :
    ∫ z : Vec3 × ℝ, p z * (θ z.2 * CKN.spatialLaplacian ψ z.1) =
      ∫ t : ℝ, θ t *
        ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian ψ x := by
  have hint := blowup_pressure_mul_product_laplacian_integrable hp hψ hψc hθ hθc
  have hprod : Integrable (fun z : Vec3 × ℝ =>
      p z * (θ z.2 * CKN.spatialLaplacian ψ z.1))
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hint
  change (∫ z : Vec3 × ℝ, p z * (θ z.2 * CKN.spatialLaplacian ψ z.1)
    ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
  rw [integral_prod_symm _ hprod]
  apply integral_congr_ae
  filter_upwards [] with t
  calc
    ∫ x : Vec3, p (x,t) * (θ t * CKN.spatialLaplacian ψ x) =
      ∫ x : Vec3, θ t * (p (x,t) * CKN.spatialLaplacian ψ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
    _ = θ t * ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian ψ x :=
      integral_const_mul _ _

private theorem blowup_exists_time_cutoff_Ioo {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      ∀ t ∈ Ioo a b, χ t = 1 := by
  have hs : IsOpen (Ioo (a - 1) (b + 1)) := isOpen_Ioo
  have ht : IsClosed (Icc a b) := isClosed_Icc
  have hsub : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  obtain ⟨χ, hχ, -, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hs ht hsub
  refine ⟨χ, hχ, ?_, fun t ht => (hone t).mp ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩
  change IsCompact (closure (Function.support χ))
  rw [hsupp, closure_Ioo (by linarith only [hab] : a - 1 ≠ b + 1)]
  exact isCompact_Icc

/-- A global `L^(3/2)` pressure has a locally integrable time function of its
pairings with any compact spatial Laplacian test. -/
theorem blowup_pressure_slice_laplacian_locallyIntegrable
    {p : Vec3 × ℝ → ℝ}
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    {a b : ℝ} (hab : a < b) :
    LocallyIntegrableOn
      (fun t : ℝ => ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian ψ x)
      (Ioo a b) volume := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := blowup_exists_time_cutoff_Ioo hab
  let H : ℝ → ℝ := fun t => ∫ x : Vec3,
    p (x,t) * CKN.spatialLaplacian ψ x
  have hprod := blowup_pressure_mul_product_laplacian_integrable hp hψ hψc hχ hχc
  have hprod' : Integrable (fun z : Vec3 × ℝ =>
      p z * (χ z.2 * CKN.spatialLaplacian ψ z.1))
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hprod
  have htime : Integrable (fun t : ℝ => ∫ x : Vec3,
      p (x,t) * (χ t * CKN.spatialLaplacian ψ x)) volume :=
    hprod'.integral_prod_right
  have hχH : Integrable (fun t : ℝ => χ t * H t) volume := by
    refine htime.congr (Filter.Eventually.of_forall fun t => ?_)
    dsimp [H]
    calc
      ∫ x : Vec3, p (x,t) * (χ t * CKN.spatialLaplacian ψ x) =
        ∫ x : Vec3, χ t * (p (x,t) * CKN.spatialLaplacian ψ x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
      _ = χ t * ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian ψ x :=
        integral_const_mul _ _
  have hHJ : IntegrableOn H (Ioo a b) volume := by
    apply (hχH.integrableOn (s := Ioo a b)).congr_fun_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [hχone t ht, one_mul]
  exact hHJ.locallyIntegrableOn

/-- For each fixed spatial test, the pressure of an exterior tensor has zero
spatial Laplacian pairing on almost every time slice. -/
theorem blowup_rieszPressure_exterior_slice_pairing_ae
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (U : Set Vec3)
    (hzero : ∀ i j z, z.1 ∈ U → F i j z = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      ∫ x : Vec3, CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ)
        (by norm_num) F hF (x,t) * CKN.spatialLaplacian ψ x = 0 := by
  let p : Vec3 × ℝ → ℝ :=
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF
  let H : ℝ → ℝ := fun t => ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian ψ x
  have hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num) F hF
  have hH : LocallyIntegrableOn H (Ioo a b) volume :=
    blowup_pressure_slice_laplacian_locallyIntegrable hp hψ hψc hab
  have hpair : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      ∫ t : ℝ, θ t • H t = 0 := by
    intro θ hθ hθc _
    have hzeroProd := blowup_rieszPressure_exterior_product_pairing_zero
      F hF U hzero hψ hψc hψU hθ hθc
    have hFub := blowup_pressure_product_laplacian_fubini hp hψ hψc hθ hθc
    simpa only [H, p, smul_eq_mul] using hFub.symm.trans hzeroProd
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hH hpair
  exact (ae_restrict_iff' measurableSet_Ioo).mpr hae

end ESS
