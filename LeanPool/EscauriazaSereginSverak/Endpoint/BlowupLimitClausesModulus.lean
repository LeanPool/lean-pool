/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesModulusEstimate
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesModulusFormula
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesBounds
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageGradient
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureUniform

/-!
# The explicit pairing modulus of the blow-up sequence

Clause (b) of `prop:blowup-limit`: for every compact set `K₀` and every
`a < 0` there is one constant `C` such that, for all sufficiently large `k`,
every smooth test `w` carried by `K₀` and all `s, t ∈ [a, 0]`,

  `|∫ (v^k(t) - v^k(s)) · w| ≤ C (|t - s| (‖Δw‖₂ + ‖∇w‖_∞) + |t - s|^{1/3} ‖div w‖_∞)`,

where the slices of `v^k` are taken from the `L³(B_{3/4})` trace representative
of `lem:weak-cont-L3`. The norms of `w` enter through any upper bounds `Gw`,
`Lw`, `Dw` for its first derivatives, its Laplacian in `L²` and its divergence.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Away from the null top face `t = 0`, a closed-in-time box lies in a
slightly longer open past box. -/
theorem blowupLimitClauses_box_ae_subset {K : Set Vec3} {R : ℝ} (hK : K ⊆ vec3Ball 0 R)
    {a a' : ℝ} (ha' : a' < a) :
    (K ×ˢ Icc a 0 : Set ParabolicPoint) ≤ᵐ[volume]
      (vec3Ball (0 : Vec3) R ×ˢ Ioo a' 0 : Set ParabolicPoint) := by
  have hnull : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)), z.2 ≠ 0 := by
    rw [ae_iff]
    have hset : {z : Vec3 × ℝ | ¬ z.2 ≠ 0} = (Set.univ : Set Vec3) ×ˢ {0} := by
      ext z
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [hnull] with z hz hzK
  exact ⟨hK hzK.1, lt_of_lt_of_le ha' hzK.2.1, lt_of_le_of_ne hzK.2.2 hz⟩

private theorem blowupLimitClauses_rescaled_flux_integrable
    {μ : Measure ParabolicPoint} [IsFiniteMeasure μ]
    (V : ParabolicPoint → Vec3)
    (DV : ParabolicPoint → Fin 3 → Fin 3 → ℝ)
    (P : ParabolicPoint → ℝ)
    (Dw : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (divw : ParabolicPoint → ℝ) (Gw DwBound : ℝ)
    (hV : MemLp V 2 μ) (hDV : MemLp DV 2 μ)
    (hP : MemLp P (3 / 2 : ℝ≥0∞) μ)
    (hDw : ∀ i j, Measurable (Dw i j))
    (hgradw : ∀ z i j, |Dw i j z| ≤ Gw)
    (hdiv : Measurable divw)
    (hdivw : ∀ z, |divw z| ≤ DwBound) :
    Integrable (fun z =>
      (∑ i : Fin 3, ∑ j : Fin 3, V z i * V z j * Dw i j z) -
      (∑ i : Fin 3, ∑ j : Fin 3, DV z i j * Dw i j z) + P z * divw z) μ := by
  have hVij : ∀ i j, Integrable (fun z => V z i * V z j) μ := by
    intro i j
    exact ((hV.eval i).integrable_mul (hV.eval j))
  have hDVij : ∀ i j, Integrable (fun z => DV z i j) μ := by
    intro i j
    exact ((hDV.eval i).eval j).integrable (by norm_num)
  have hPint : Integrable P μ := hP.integrable (by
    rw [← CKN.ofReal_threeHalves]
    exact ENNReal.one_le_ofReal.mpr (by norm_num))
  refine ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_).sub
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_)).add ?_
  · exact (hVij i j).mul_bdd (c := Gw) (hDw i j).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgradw z i j)
  · exact (hDVij i j).mul_bdd (c := Gw) (hDw i j).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgradw z i j)
  · exact hPint.mul_bdd (c := DwBound) hdiv.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hdivw z)

private theorem blowupLimitClauses_closedTime_slices_have_gradient
    {f : ParabolicPoint → Vec3} {Df : ParabolicPoint → Fin 3 → Vec3}
    {R a : ℝ} (hminusR : -R < a)
    (hgradR : ∀ᵐ τ ∂(volume.restrict (Ioo (-R) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) R) (fun x => f (x,τ) i)
        (fun x => Df (x,τ) i)) :
    ∀ᵐ τ ∂(volume.restrict (Icc a 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) R) (fun x => f (x,τ) i)
        (fun x => Df (x,τ) i) := by
  have hne : ∀ᵐ τ ∂(volume.restrict (Icc a 0)), τ ≠ 0 :=
    ae_mono Measure.restrict_le_self (Measure.ae_ne volume 0)
  have hall := (ae_restrict_iff' measurableSet_Ioo).1 hgradR
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Icc, hne]
    with τ hτ hτI hτne
  apply hτ
  refine ⟨?_, lt_of_le_of_ne hτI.2 hτne⟩
  linarith only [hminusR, hτI.1]

private theorem blowupLimitClauses_rescaled_support_and_time_window
    {K₀ : Set Vec3} (x₀ : Vec3) (t₀ r ρ R a : ℝ)
    (hK₀ρ : K₀ ⊆ vec3Ball (0 : Vec3) ρ) (hρR : ρ ≤ R)
    (hr : 0 < r) (hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hrR : r * R < 1 / 4) (hra : r ^ 2 * (-a) < 5 / 16) :
    (fun x : Vec3 => x₀ + r • x) '' K₀ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ∧
    ∀ τ, τ ∈ Icc a 0 → t₀ + r ^ 2 * τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    have hxρ := hK₀ρ hx
    rw [mem_vec3Ball, sub_zero] at hxρ ⊢
    have htri := vec3EuclideanNorm_add_le x₀ (r • x)
    rw [vec3EuclideanNorm_smul, abs_of_pos hr] at htri
    have hmul : r * vec3EuclideanNorm x < 1 / 4 := by
      have h1 : r * vec3EuclideanNorm x ≤ r * R :=
        mul_le_mul_of_nonneg_left (hxρ.le.trans hρR) hr.le
      linarith only [h1, hrR]
    linarith only [htri, hxnorm, hmul]
  · intro τ hτ
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg _
    have hlow : r ^ 2 * a ≤ r ^ 2 * τ := mul_le_mul_of_nonneg_left hτ.1 hr2
    have hup : r ^ 2 * τ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr2 hτ.2
    have hra' : r ^ 2 * a > -(5 / 16) := by linarith only [hra]
    constructor
    · nlinarith only [ht₀.1, hlow, hra']
    · linarith only [ht₀.2, hup]

private theorem blowupLimitClauses_gradient_memLp_on_window
    {Q : Set ParabolicPoint} {f : ParabolicPoint → Vec3}
    {Df : ParabolicPoint → Fin 3 → Vec3}
    {Dtrue : ParabolicPoint → Fin 3 → Fin 3 → ℝ}
    (hDf : Measurable Df) (hDfae : Df =ᵐ[volume] Dtrue)
    (hfin : (∫⁻ z in Q, ‖spatialGradientSq f Dtrue z‖ₑ) < ⊤) :
    MemLp Df 2 (volume.restrict Q) := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hDf.aestronglyMeasurable]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  apply ne_of_lt
  calc
    (∫⁻ z in Q, ‖Df z‖ₑ ^ (2 : ℝ≥0∞).toReal) ≤
      ∫⁻ z in Q, ‖spatialGradientSq f Dtrue z‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hDfae] with z hz
      rw [ENNReal.toReal_ofNat, hz, Real.enorm_of_nonneg (by
        unfold spatialGradientSq
        positivity), ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have h := blowupLimitAssembly_norm_sq_le_spatialGradientSq f Dtrue z
      rw [← Real.rpow_natCast] at h
      exact_mod_cast h
    _ < ⊤ := hfin

private theorem blowupLimitClauses_gradient_memLp_on_smaller_window
    {Q Qbig : Set ParabolicPoint} {f : ParabolicPoint → Vec3}
    {Df Dtrue : ParabolicPoint → Fin 3 → Vec3}
    (hDf : Measurable Df) (hDfae : Df =ᵐ[volume] Dtrue)
    (hfin : (∫⁻ z in Qbig, ‖spatialGradientSq f Dtrue z‖ₑ) < ⊤)
    (hμle : volume.restrict Q ≤ volume.restrict Qbig) :
    MemLp Df 2 (volume.restrict Q) ∧ MemLp Dtrue 2 (volume.restrict Q) := by
  have hDfL2 := (blowupLimitClauses_gradient_memLp_on_window hDf hDfae hfin).mono_measure hμle
  exact ⟨hDfL2, hDfL2.ae_eq (ae_restrict_of_ae hDfae)⟩

private theorem blowupLimitClauses_small_rescaling_bounds
    {r : ℕ → ℝ} (hr0 : Tendsto r atTop (𝓝 0)) :
    (∀ c : ℝ, 0 < c → ∀ d : ℝ, ∀ᶠ k in atTop, r k * d < c) ∧
    (∀ c : ℝ, 0 < c → ∀ d : ℝ, ∀ᶠ k in atTop, r k ^ 2 * d < c) := by
  constructor
  · intro c hc d
    have h : Tendsto (fun k => r k * d) atTop (𝓝 0) := by
      simpa only [zero_mul] using hr0.mul_const d
    exact h.eventually (eventually_lt_nhds hc)
  · intro c hc d
    have h : Tendsto (fun k => r k ^ 2 * d) atTop (𝓝 0) := by
      simpa using (hr0.pow 2).mul_const d
    exact h.eventually (eventually_lt_nhds hc)

private theorem blowupLimitClauses_flux_formula_on_compact_window
    {K : Set Vec3} {a : ℝ} (w : Vec3 → Vec3)
    (T V : ParabolicPoint → Vec3)
    (Df Dtrue : ParabolicPoint → Fin 3 → Vec3)
    (P : ParabolicPoint → ℝ) (Qbig : Set ParabolicPoint)
    (hBU : ∀ s t, s ∈ Icc a 0 → t ∈ Icc a 0 → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, T (x, t) i * w x i) -
        (∫ x : Vec3, ∑ i : Fin 3, T (x, s) i * w x i) =
      ∫ z in K ×ˢ Ioc s t,
        (∑ i : Fin 3, ∑ j : Fin 3,
          V z i * V z j * spatialDeriv (fun y => w y i) j z.1) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          Dtrue z i j * spatialDeriv (fun y => w y i) j z.1) +
        P z * ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1)
    (hT : T =ᵐ[volume.restrict Qbig] V)
    (hD : Df =ᵐ[volume] Dtrue)
    (hsub : ∀ s t, s ∈ Icc a 0 → t ∈ Icc a 0 → s ≤ t →
      volume.restrict (K ×ˢ Ioc s t) ≤ volume.restrict Qbig) :
    ∀ s t, s ∈ Icc a 0 → t ∈ Icc a 0 → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, T (x, t) i * w x i) -
        (∫ x : Vec3, ∑ i : Fin 3, T (x, s) i * w x i) =
      ∫ z in K ×ˢ Ioc s t,
        (∑ i : Fin 3, ∑ j : Fin 3,
          T z i * T z j * spatialDeriv (fun y => w y i) j z.1) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          Df z i j * spatialDeriv (fun y => w y i) j z.1) +
        P z * ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1 := by
  intro s t hs ht hst
  rw [hBU s t hs ht hst]
  apply integral_congr_ae
  filter_upwards [ae_mono (hsub s t hs ht hst) hT,
    ae_restrict_of_ae hD] with z hz hzD
  rw [hzD, hz]

private theorem blowupLimitClauses_pressure_memLp_on_window
    {Q Qbig : Set ParabolicPoint} {P : ParabolicPoint → ℝ}
    (B : ℝ)
    (hμle : volume.restrict Q ≤ volume.restrict Qbig)
    (hPbig : eLpNorm P (3 / 2 : ℝ≥0∞) (volume.restrict Qbig) ≤ ENNReal.ofReal B) :
    eLpNorm P (3 / 2 : ℝ≥0∞) (volume.restrict Q) ≤ ENNReal.ofReal B ∧
      MemLp P (3 / 2 : ℝ≥0∞) (volume.restrict Q) := by
  have hPQ : eLpNorm P (3 / 2 : ℝ≥0∞) (volume.restrict Q) ≤ ENNReal.ofReal B :=
    (eLpNorm_mono_measure _ hμle).trans hPbig
  exact ⟨hPQ, memLp_iff.2 (hPQ.trans_lt ENNReal.ofReal_lt_top)⟩

private theorem blowupLimitClauses_compact_window_finite
    {K : Set Vec3} (hK : IsCompact K) (a : ℝ) :
    IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict (K ×ˢ Icc a 0)) := by
  constructor
  change ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ Icc a 0)) univ < ⊤
  rw [Measure.restrict_apply_univ]
  exact (hK.prod isCompact_Icc).measure_lt_top

/-- The explicit pairing modulus of the blow-up sequence (`prop:blowup-limit`,
clause (b)), for the trace representative of `lem:weak-cont-L3`. -/
theorem blowupLimitClauses_pairing_modulus
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (hWm : Measurable W)
    (hW : ∀ t, (fun x => W (x, t)) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => weakContL3OfLp (v t x)))
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x, t)))
    (hsourceFormula : ∀ ψ : Vec3 → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t y i * ψ y i) -
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s y i * ψ y i) =
        ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume)
    (Mt : ℝ)
    (hsourceW : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x, t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal Mt)
    (Dm : ParabolicPoint → Fin 3 → Vec3) (hDm : Measurable Dm)
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du)
    {um : ParabolicPoint → Vec3} (hum : Measurable um)
    (hu_um : u =ᵐ[volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))] um)
    {K₀ : Set Vec3} (hK₀ : IsCompact K₀) {a : ℝ} (ha : a < 0) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ᶠ k in atTop,
      ∀ w : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w → tsupport w ⊆ K₀ →
      ∀ Gw Lw Dw : ℝ, 0 ≤ Gw → 0 ≤ Lw → 0 ≤ Dw →
      (∀ x i j, |spatialDeriv (fun y => w y i) j x| ≤ Gw) →
      (∀ i, eLpNorm (fun x => ∑ j : Fin 3,
        spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x) 2 volume ≤
          ENNReal.ofReal Lw) →
      (∀ x, |∑ i : Fin 3, spatialDeriv (fun y => w y i) i x| ≤ Dw) →
      ∀ s t, s ∈ Icc a 0 → t ∈ Icc a 0 →
        |(∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitTraceRescaling W x₀ t₀ (r k) (x, t) i * w x i) -
          (∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitTraceRescaling W x₀ t₀ (r k) (x, s) i * w x i)| ≤
          Cc * (|t - s| * (Lw + Gw) + |t - s| ^ (1 / 3 : ℝ) * Dw) := by
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    have h := hx₀
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at h
    simpa only [Set.mem_ofPred_eq, sub_zero] using h
  -- a radius for the support set and a longer past box
  obtain ⟨ρ₀, hρ₀⟩ := hK₀.exists_bound_of_continuousOn
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn
  set ρ : ℝ := |ρ₀| + 1 with hρdef
  have hρpos : 0 < ρ := by positivity
  have hK₀ρ : K₀ ⊆ vec3Ball (0 : Vec3) ρ := by
    intro x hx
    have h := hρ₀ x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg x)] at h
    rw [mem_vec3Ball, sub_zero]
    linarith only [h, le_abs_self ρ₀]
  set R : ℝ := ρ - a + 1 with hRdef
  have hR : 0 < R := by
    simp only [hRdef]
    linarith only [hρpos, ha]
  have hK₀R : K₀ ⊆ vec3Ball (0 : Vec3) R := by
    intro x hx
    have h := hK₀ρ hx
    rw [mem_vec3Ball] at h ⊢
    simp only [hRdef]
    linarith only [h, ha]
  set a' : ℝ := a - 1 with ha'def
  have ha'a : a' < a := by simp only [ha'def]; linarith only
  have ha' : a' < 0 := ha'a.trans ha
  -- the uniform slice bound on the support set
  obtain ⟨M', hM', hM'b⟩ :=
    blowupLimitAssembly_trace_compact_slice_bound W Mt hsourceW x₀ t₀ r hr K₀ hK₀
  set S : ℝ := M'.toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hslice : ∀ k τ, ∫⁻ x in K₀, ENNReal.ofReal (vec3EuclideanNorm
      (blowupLimitTraceRescaling W x₀ t₀ (r k) (x, τ))) ^ (2 : ℝ) ≤ ENNReal.ofReal S := by
    intro k τ
    rw [hSdef, ENNReal.ofReal_toReal hM'.ne]
    exact hM'b k τ
  -- the pressure bound on the longer past box
  obtain ⟨-, -, hp₁, -, ⟨Mₚ, hMₚ, hsourceP⟩, hp₂, hharm⟩ :=
    blowupLimitAssembly_source_pressure_data hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
  obtain ⟨Bp, hBp, hevP⟩ := blowupPressure_eventually_bounded_pastBox p _ hp₁ Mₚ hMₚ
    hsourceP hp₂ hharm x₀ t₀ r hx₀ ht₀ hr hr0 R a' hR ha'
  set B : ℝ := Bp.toReal with hBdef
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  -- the gradient and velocity bounds on the longer past box
  obtain ⟨Cg, -, hevG⟩ := blowupLimitClauses_energy_pressure_bounds hu hDu hp hL2 henergy
    hpLp hL3 hgrad hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 R a' hR ha'
  obtain ⟨Bv, -, hevV⟩ := blowupLimitClauses_tenThirds_bound hu hDu hp hL2 henergy
    hpLp hL3 hgrad hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 R a' hR ha'
  -- small scales
  obtain ⟨hsmall, hsmall2⟩ := blowupLimitClauses_small_rescaling_bounds hr0
  refine ⟨9 * S + 3 * Real.sqrt S + B * (volume K₀).toReal ^ (1 / 3 : ℝ), by positivity, ?_⟩
  filter_upwards [hevP, hevG, hevV, hsmall (1 / 4) (by norm_num) R,
    hsmall2 (1 / 4) (by norm_num) R, hsmall2 (1 / 4) (by norm_num) (-a'),
    hsmall2 (5 / 16) (by norm_num) (-a)] with k hPk hGk hVk hrR hrR2 hra' hra
  intro w hw hwc hwK Gw Lw Dw hGw hLw hDw hgradw hlapw hdivw
  set Q : Set ParabolicPoint := K₀ ×ˢ Icc a 0 with hQdef
  set Qbig : Set ParabolicPoint := vec3Ball (0 : Vec3) R ×ˢ Ioo a' 0 with hQbigdef
  have hμle : (volume : Measure ParabolicPoint).restrict Q ≤ volume.restrict Qbig :=
    Measure.restrict_mono_ae (blowupLimitClauses_box_ae_subset hK₀R ha'a)
  let _ : IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict Q) :=
    blowupLimitClauses_compact_window_finite hK₀ a
  set f : ParabolicPoint → Vec3 := blowupLimitTraceRescaling W x₀ t₀ (r k) with hfdef
  have hf : Measurable f := measurable_blowupLimitTraceRescaling W hWm x₀ t₀ (r k)
  set Df : ParabolicPoint → Fin 3 → Vec3 := blowupGradient x₀ t₀ (r k) Dm with hDfdef
  have hDf : Measurable Df := measurable_blowupLimitAssembly_blowupGradient hDm x₀ t₀ (r k)
  have hDfae : Df =ᵐ[volume] blowupGradient x₀ t₀ (r k) Du :=
    blowupLimitAssembly_blowupGradient_ae_eq hDmEq x₀ t₀ (r k) (hr k)
  -- the pressure on the box
  have hPbig : eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
      (volume.restrict Qbig) ≤ ENNReal.ofReal B := by
    rw [hBdef, ENNReal.ofReal_toReal hBp.ne]
    exact hPk
  obtain ⟨hPQ, hPmem⟩ := blowupLimitClauses_pressure_memLp_on_window B hμle hPbig
  -- the gradient on the box
  obtain ⟨hDfL2, hDu2⟩ := blowupLimitClauses_gradient_memLp_on_smaller_window
    hDf hDfae hGk.2.1.2 hμle
  -- the velocity on the box
  have hVQ : MemLp (blowupVelocity x₀ t₀ (r k) u) 2
      ((volume : Measure ParabolicPoint).restrict Q) := by
    have h := hVk.1.mono_measure hμle
    exact h.mono_exponent (by
      rw [← ENNReal.ofReal_ofNat 2]
      exact ENNReal.ofReal_le_ofReal (by norm_num))
  -- the weak gradients of the slices
  have hgradR := blowupLimitAssembly_trace_hasWeakGradientOn hDm hDmEq hgrad W hWm htrace
    hxnorm ht₀ (hr k) hrR hrR2
  have hminusR : -R < a := by
    simp only [hRdef]
    linarith only [hρpos]
  have hgradQ := blowupLimitClauses_closedTime_slices_have_gradient hminusR hgradR
  -- the flux formula with the rescaled fields
  have hρR : ρ ≤ R := by simp only [hRdef]; linarith only [ha]
  obtain ⟨himage, htime⟩ := blowupLimitClauses_rescaled_support_and_time_window
    x₀ t₀ (r k) ρ R a hK₀ρ hρR (hr k) hxnorm ht₀ (by linarith only [hrR])
      (by linarith only [hra])
  -- integrability of the flux on the box
  have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => w y i) := fun i =>
    (contDiff_apply ℝ ℝ i).comp hw
  have hφm : ∀ i j, Measurable (fun z : ParabolicPoint =>
      spatialDeriv (fun y => w y i) j z.1) := fun i j =>
    (blowupLimitClauses_spatialDeriv_contDiff (hwi i) j).continuous.measurable.comp
      measurable_fst
  have hdm : Measurable (fun z : ParabolicPoint =>
      ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1) :=
    Finset.measurable_sum _ fun i _ => hφm i i
  have hFint := blowupLimitClauses_rescaled_flux_integrable
    (μ := (volume : Measure ParabolicPoint).restrict Q)
    (fun z => blowupVelocity x₀ t₀ (r k) u z)
    (fun z i j => blowupGradient x₀ t₀ (r k) Du z i j)
    (fun z => blowupPressure x₀ t₀ (r k) p z)
    (fun i j z => spatialDeriv (fun y => w y i) j z.1)
    (fun z => ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1)
    Gw Dw hVQ hDu2 hPmem hφm (fun z => hgradw z.1) hdm (fun z => hdivw z.1)
  have hformulaBU := blowupLimitClauses_rescaled_flux_formula v W hW hsourceFormula hK₀
    a 0 le_rfl (hr k) ht₀.2 himage htime hw hwK hFint
  -- the same formula with the trace representative and the measurable gradient
  have hvel : blowupLimitTraceRescaling W x₀ t₀ (r k) =ᵐ[volume.restrict Qbig]
      blowupVelocity x₀ t₀ (r k) u :=
    blowupLimitAssembly_trace_ae_eq_blowupVelocity hum hu_um W hWm htrace hxnorm ht₀ (hr k)
      hrR hra'
  have hsub : ∀ s t, s ∈ Icc a 0 → t ∈ Icc a 0 → s ≤ t →
      volume.restrict (K₀ ×ˢ Ioc s t) ≤ volume.restrict Qbig := by
    intro s t hs ht hst
    refine le_trans (Measure.restrict_mono ?_ le_rfl) hμle
    intro z hz
    exact ⟨hz.1, le_trans hs.1 hz.2.1.le, le_trans hz.2.2 ht.2⟩
  have hformula := blowupLimitClauses_flux_formula_on_compact_window w
    (blowupLimitTraceRescaling W x₀ t₀ (r k))
    (blowupVelocity x₀ t₀ (r k) u)
    (blowupGradient x₀ t₀ (r k) Dm) (blowupGradient x₀ t₀ (r k) Du)
    (blowupPressure x₀ t₀ (r k) p) Qbig hformulaBU hvel hDfae hsub
  intro s t hs ht
  exact blowupLimitClauses_modulus_of_formula hK₀ hK₀R hf hDf hS0 (hslice k) hDfL2 hPmem
    hB0 hPQ hgradQ hw hwc hwK hGw hLw hDw hgradw hlapw hdivw hformula s t hs ht

end ESS

end
