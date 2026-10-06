/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingLimitInputs
public import LeanPool.CIVAxisymmetric.Zoom.LiftedWeakForm
public import LeanPool.CIVAxisymmetric.Zoom.RecedingDrTermVanish
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSwirlUniformEventual
public import LeanPool.CIVAxisymmetric.Statements.DtPast
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.LevelSums

/-!
# R2-R: the residual of the rescaled receding vorticity-quotient equation tends to zero

The receding-branch analogue of `CIV.tendsto_finResidual` (`CIV/Zoom/FiniteResidual.lean`) at
`(m, d) = (2, 1)`: against a test function `φ` on `Vec 2 × (-∞, -1)`, the pairing of the
rescaled azimuthal vorticity `Θ_n` with the adjoint operator of `eq:aniso:zoom:receding:limit`
tends to zero along the receding zoom sequence.

The weak form comes from `CIV.zoomTheta_pde` (`CIV/Zoom/RecedingEquation.lean`), rearranged so
that the drift-divergence pairing `CIV.integral_recedingResidual_eq` (a receding-axis,
axis-singularity-free analogue of `CIV.integral_liftedResidual_eq`) applies directly: every
term of `eq:aniso:zoom:receding:equation` outside the limit operator is collected into the
swirl flux `S_n²/(A_n+R)` (whose `∂_Z` reproduces the swirl-source term) and a source `G_n`
bundling the `∂_R Θ_n/(A_n+R)` term, the two curvature terms, and the force term. Each of the
three pieces of the weak-form remainder — `δ_n² ∫ Θ_n ∂_ZZ ψ`, `-∫ (S_n²/(A_n+R)) ∂_Z ψ`, and
`∫ G_n ψ` — is bounded by a constant times a factor tending to `0` uniformly on `tsupport ψ` as
`n → ∞`, since `A_n = r_n/λ_n → ∞` and `δ_n = λ_n^{2h} → 0`.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-! ## The weak form of a drift-diffusion equation on `Vec 2 × ℝ` off a closed set -/

/-- The sum of the single term of a `Fin 2`-indexed masked sum with cutoff `1`, the receding
analogue of `sum_fin_five_ite_lt_four`. -/
theorem sum_fin_two_ite_lt_one (a : Fin 2 → ℝ) :
    (∑ i : Fin 2, if (i : ℕ) < 1 then a i else 0) = a 0 := by
  rw [Fin.sum_univ_two]
  simp

/-- The integration by parts of the receding branch of the passage to the limit: if `q`, the
drift `B`, the flux `Fz` and the source `G` satisfy
`∂_τ q + B · ∇q = ∂_RR q + κ ∂_ZZ q + ∂_Z Fz + G` pointwise on an open set `S`, with `divB` the
divergence of `B` there, then against every test function supported in a compact subset of `S`
the residual of `eq:aniso:zoom:receding:limit` is `κ ∫ q ∂_ZZ ψ - ∫ Fz ∂_Z ψ + ∫ G ψ`. -/
theorem integral_recedingResidual_eq {S K : Set (Vec 2 × ℝ)} (hS : IsOpen S) (hK : IsCompact K)
    (hKS : K ⊆ S) {q Fz G divB : Vec 2 × ℝ → ℝ} {B : Vec 2 × ℝ → Vec 2} (κ : ℝ)
    (hq : ContDiffOn ℝ (⊤ : ℕ∞) q S) (hB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => B z i) S)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) Fz S) (hG : ContinuousOn G S)
    (hdiv : ∀ z ∈ S, ∑ i, fderiv ℝ (fun w => B w i) z (basisVec i, 0) = divB z)
    (hpde : ∀ z ∈ S, fderiv ℝ q z (0, 1) + ∑ i, B z i * fderiv ℝ q z (basisVec i, 0)
      = (∑ i : Fin 2, if (i : ℕ) < 1 then
          fderiv ℝ (fun w => fderiv ℝ q w (basisVec i, 0)) z (basisVec i, 0) else 0)
        + κ * fderiv ℝ (fun w => fderiv ℝ q w (basisVec 1, 0)) z (basisVec 1, 0)
        + fderiv ℝ Fz z (basisVec 1, 0) + G z)
    {ψ : Vec 2 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψK : tsupport ψ ⊆ K) :
    ∫ z, q z * (-(timeDeriv 2 ψ z) - gradPair 2 ψ z (B z) - divB z * ψ z
        - partialLaplacian 2 1 ψ z)
      = ∫ z, (κ * q z * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 1, 0)) z (basisVec 1, 0)
        - Fz z * fderiv ℝ ψ z (basisVec 1, 0) + G z * ψ z) := by
  have : (volume : Measure (Vec 2 × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set e : Fin 2 → Vec 2 × ℝ := fun i => (basisVec i, 0) with he
  have hψd : ∀ z, DifferentiableAt ℝ ψ z := fun z => hψ.differentiable (by simp) z
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hψ' : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ ψ w (e i)) := fun i =>
    contDiff_fderiv_apply_top hψ (e i)
  have hψ'c : ∀ i, HasCompactSupport (fun w => fderiv ℝ ψ w (e i)) := fun i =>
    hψc.fderiv_apply ℝ (e i)
  have hψ'K : ∀ i, tsupport (fun w => fderiv ℝ ψ w (e i)) ⊆ K := fun i =>
    (tsupport_fderiv_apply_subset ℝ (e i)).trans hψK
  have hq' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ q w (e i)) S := fun i =>
    contDiffOn_fderiv_apply_of_isOpen hS hq (e i)
  have hqB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => q w * B w i) S := fun i => hq.mul (hB i)
  have hPt := integrable_and_integral_ibpPair_eq_zero (E := Vec 2 × ℝ) (μ := volume) hS hK hKS hq
    hψ hψc hψK ((0 : Vec 2), (1 : ℝ))
  have hPB := fun i => integrable_and_integral_ibpPair_eq_zero (E := Vec 2 × ℝ) (μ := volume) hS
    hK hKS (hqB i) hψ hψc hψK (e i)
  have hQ := fun i => integrable_and_integral_ibpPair_eq_zero (E := Vec 2 × ℝ) (μ := volume) hS
    hK hKS hq (hψ' i) (hψ'c i) (hψ'K i) (e i)
  have hQ' := fun i => integrable_and_integral_ibpPair_eq_zero (E := Vec 2 × ℝ) (μ := volume) hS
    hK hKS (hq' i) hψ hψc hψK (e i)
  have hPF := integrable_and_integral_ibpPair_eq_zero (E := Vec 2 × ℝ) (μ := volume) hS hK hKS hF
    hψ hψc hψK (e 1)
  set P : Vec 2 × ℝ → ℝ := fun z =>
    -(q z * fderiv ℝ ψ z ((0 : Vec 2), (1 : ℝ)) + fderiv ℝ q z ((0 : Vec 2), (1 : ℝ)) * ψ z)
      - (∑ i, (q z * B z i * fderiv ℝ ψ z (e i)
          + fderiv ℝ (fun w => q w * B w i) z (e i) * ψ z))
      - (∑ i : Fin 2, if (i : ℕ) < 1 then
          ((q z * fderiv ℝ (fun w => fderiv ℝ ψ w (e i)) z (e i)
              + fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i))
            - (fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i)
              + fderiv ℝ (fun w => fderiv ℝ q w (e i)) z (e i) * ψ z)) else 0)
      - κ * ((q z * fderiv ℝ (fun w => fderiv ℝ ψ w (e 1)) z (e 1)
              + fderiv ℝ q z (e 1) * fderiv ℝ ψ z (e 1))
            - (fderiv ℝ q z (e 1) * fderiv ℝ ψ z (e 1)
              + fderiv ℝ (fun w => fderiv ℝ q w (e 1)) z (e 1) * ψ z))
      + (Fz z * fderiv ℝ ψ z (e 1) + fderiv ℝ Fz z (e 1) * ψ z) with hP_def
  have hPint : Integrable P ∧ ∫ z, P z = 0 := by
    have hsumB := integrable_and_integral_finset_sum_eq_zero (μ := volume) Finset.univ
      (f := fun i z => q z * B z i * fderiv ℝ ψ z (e i)
          + fderiv ℝ (fun w => q w * B w i) z (e i) * ψ z)
      fun i _ => hPB i
    have hsumQ := integrable_and_integral_finset_sum_eq_zero (μ := volume) Finset.univ
      (f := fun (i : Fin 2) z => if (i : ℕ) < 1 then
          ((q z * fderiv ℝ (fun w => fderiv ℝ ψ w (e i)) z (e i)
              + fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i))
            - (fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i)
              + fderiv ℝ (fun w => fderiv ℝ q w (e i)) z (e i) * ψ z)) else 0)
      fun i _ => by
        by_cases hi : (i : ℕ) < 1
        · simp only [hi, ↓reduceIte]
          exact integrable_and_integral_sub_eq_zero (hQ i) (hQ' i)
        · simp only [hi, ↓reduceIte]
          exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    exact integrable_and_integral_add_eq_zero
      (integrable_and_integral_sub_eq_zero
        (integrable_and_integral_sub_eq_zero
          (integrable_and_integral_sub_eq_zero (integrable_and_integral_neg_eq_zero hPt) hsumB)
          hsumQ)
        (integrable_and_integral_const_mul_eq_zero κ
          (integrable_and_integral_sub_eq_zero (hQ 1) (hQ' 1))))
      hPF
  have hbr : ∀ z, ψ z * (fderiv ℝ q z ((0 : Vec 2), (1 : ℝ))
      + ∑ i, fderiv ℝ (fun w => q w * B w i) z (e i) - q z * divB z
      - (∑ i : Fin 2, if (i : ℕ) < 1 then fderiv ℝ (fun w => fderiv ℝ q w (e i)) z (e i) else 0)
      - κ * fderiv ℝ (fun w => fderiv ℝ q w (e 1)) z (e 1) - fderiv ℝ Fz z (e 1) - G z) = 0 := by
    intro z
    by_cases hz : z ∈ S
    · have hqd : DifferentiableAt ℝ q z :=
        (hq.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
      have hBd : ∀ i, DifferentiableAt ℝ (fun w => B w i) z := fun i =>
        ((hB i).differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
      have hprod : ∑ i, fderiv ℝ (fun w => q w * B w i) z (e i)
          = ∑ i, B z i * fderiv ℝ q z (e i)
            + q z * ∑ i, fderiv ℝ (fun w => B w i) z (e i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hm : HasFDerivAt (fun w => q w * B w i)
            (q z • fderiv ℝ (fun w => B w i) z + B z i • fderiv ℝ q z) z :=
          hqd.hasFDerivAt.mul (hBd i).hasFDerivAt
        rw [hm.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      have h1 := hpde z hz
      have h2 := hdiv z hz
      rw [hprod]
      linear_combination ψ z * h1 + ψ z * q z * h2
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hKS (hψK h))
      rw [this, zero_mul]
  have hpt : ∀ z, q z * (-(timeDeriv 2 ψ z) - gradPair 2 ψ z (B z) - divB z * ψ z
        - partialLaplacian 2 1 ψ z)
      = (κ * q z * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 1, 0)) z (basisVec 1, 0)
        - Fz z * fderiv ℝ ψ z (basisVec 1, 0) + G z * ψ z) + P z := by
    intro z
    have hb := hbr z
    rw [timeDeriv_eq_fderiv (hψd z), gradPair_eq_fderiv (hψd z),
      fderiv_apply_eq_sum_basisVec, partialLaplacian_eq_fderiv hψ2]
    simp only [hP_def, he, sum_fin_two_ite_lt_one] at hb ⊢
    simp only [Fin.sum_univ_two] at hb ⊢
    linear_combination hb
  have hRint : Integrable (fun z => κ * q z * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 1, 0)) z
      (basisVec 1, 0) - Fz z * fderiv ℝ ψ z (basisVec 1, 0) + G z * ψ z) := by
    refine integrable_of_continuousOn_of_forall_notMem hK hKS ?_ ?_
    · have c1 : ContinuousOn (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 1, 0)) z
          (basisVec 1, 0)) S :=
        (contDiff_fderiv_apply_top (hψ' 1) (e 1)).continuous.continuousOn
      have c2 : ContinuousOn (fun z => fderiv ℝ ψ z (basisVec 1, 0)) S :=
        (hψ' 1).continuous.continuousOn
      exact ((continuousOn_const.mul hq.continuousOn).mul c1).sub (hF.continuousOn.mul c2)
        |>.add (hG.mul hψ.continuous.continuousOn)
    · intro z hz
      have hz' : z ∉ tsupport ψ := fun h => hz (hψK h)
      have hz'' : z ∉ tsupport (fun w => fderiv ℝ ψ w (basisVec 1, 0)) := fun h =>
        hz' (tsupport_fderiv_apply_subset ℝ _ h)
      rw [fderiv_apply_eq_zero_of_notMem_tsupport hz'', fderiv_apply_eq_zero_of_notMem_tsupport hz',
        image_eq_zero_of_notMem_tsupport hz']
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hRint hPint.1, hPint.2,
    add_zero]

/-! ## The joint-derivative bridge for `dr`, `dz`, `dtPast` on the plane -/

/-- `dr` is the joint derivative in the direction `((1, 0), 0)`. -/
theorem dr_eq_fderiv_apply {F : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ}
    (hF : DifferentiableAt ℝ F p) : dr F p = fderiv ℝ F p ((1, 0), 0) := by
  have hline : HasDerivAt (fun r : ℝ => (((r, p.1.2), p.2) : (ℝ × ℝ) × ℝ)) (((1, 0), 0)) p.1.1 :=
    ((hasDerivAt_id p.1.1).prodMk (hasDerivAt_const p.1.1 p.1.2)).prodMk
      (hasDerivAt_const p.1.1 p.2)
  have hcomp : HasDerivAt (fun r : ℝ => F ((r, p.1.2), p.2)) (fderiv ℝ F p ((1, 0), 0)) p.1.1 :=
    hF.hasFDerivAt.comp_hasDerivAt p.1.1 hline
  exact hcomp.deriv

/-- `dz` is the joint derivative in the direction `((0, 1), 0)`. -/
theorem dz_eq_fderiv_apply {F : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ}
    (hF : DifferentiableAt ℝ F p) : dz F p = fderiv ℝ F p ((0, 1), 0) := by
  have hline : HasDerivAt (fun s : ℝ => (((p.1.1, s), p.2) : (ℝ × ℝ) × ℝ)) (((0, 1), 0)) p.1.2 :=
    ((hasDerivAt_const p.1.2 p.1.1).prodMk (hasDerivAt_id p.1.2)).prodMk
      (hasDerivAt_const p.1.2 p.2)
  have hcomp : HasDerivAt (fun s : ℝ => F ((p.1.1, s), p.2)) (fderiv ℝ F p ((0, 1), 0)) p.1.2 :=
    hF.hasFDerivAt.comp_hasDerivAt p.1.2 hline
  exact hcomp.deriv

/-- `dtPast` is the joint derivative in the direction `((0, 0), 1)`, since a function
differentiable at `p` has equal one-sided and two-sided time derivatives. -/
theorem dtPast_eq_fderiv_apply {F : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ}
    (hF : DifferentiableAt ℝ F p) : dtPast F p = fderiv ℝ F p ((0, 0), 1) := by
  have hline : HasDerivAt (fun t : ℝ => ((p.1, t) : (ℝ × ℝ) × ℝ)) (((0, 0), 1)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hcomp : HasDerivAt (fun t : ℝ => F (p.1, t)) (fderiv ℝ F p ((0, 0), 1)) p.2 :=
    hF.hasFDerivAt.comp_hasDerivAt p.2 hline
  exact hcomp.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic p.2)

/-- A plane function differentiable on an open set `D` has a differentiable `dr` on any set
where a further `C²` bound is known. -/
theorem differentiableAt_dr_of_contDiffOn {F : (ℝ × ℝ) × ℝ → ℝ} {D : Set ((ℝ × ℝ) × ℝ)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ D) :
    DifferentiableAt ℝ (dr F) p := by
  have hFdiff : ∀ p' ∈ D, DifferentiableAt ℝ F p' := fun p' hp' =>
    (hF.differentiableOn (by norm_num) p' hp').differentiableAt (hD.mem_nhds hp')
  have heq : Set.EqOn (dr F) (fun p' => fderiv ℝ F p' ((1, 0), 0)) D := fun p' hp' =>
    dr_eq_fderiv_apply (hFdiff p' hp')
  have hevent := heq.eventuallyEq_of_mem (hD.mem_nhds hp)
  have hG : DifferentiableAt ℝ (fun p' => fderiv ℝ F p' ((1, 0), 0)) p := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ F) D := hF.fderiv_of_isOpen hD (by norm_num)
    exact ((h1.clm_apply contDiffOn_const).differentiableOn (by norm_num) p
      hp).differentiableAt (hD.mem_nhds hp)
  exact hG.congr_of_eventuallyEq hevent

/-- A plane function differentiable on an open set `D` has a differentiable `dz` on any set
where a further `C²` bound is known. -/
theorem differentiableAt_dz_of_contDiffOn {F : (ℝ × ℝ) × ℝ → ℝ} {D : Set ((ℝ × ℝ) × ℝ)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ D) :
    DifferentiableAt ℝ (dz F) p := by
  have hFdiff : ∀ p' ∈ D, DifferentiableAt ℝ F p' := fun p' hp' =>
    (hF.differentiableOn (by norm_num) p' hp').differentiableAt (hD.mem_nhds hp')
  have heq : Set.EqOn (dz F) (fun p' => fderiv ℝ F p' ((0, 1), 0)) D := fun p' hp' =>
    dz_eq_fderiv_apply (hFdiff p' hp')
  have hevent := heq.eventuallyEq_of_mem (hD.mem_nhds hp)
  have hG : DifferentiableAt ℝ (fun p' => fderiv ℝ F p' ((0, 1), 0)) p := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ F) D := hF.fderiv_of_isOpen hD (by norm_num)
    exact ((h1.clm_apply contDiffOn_const).differentiableOn (by norm_num) p
      hp).differentiableAt (hD.mem_nhds hp)
  exact hG.congr_of_eventuallyEq hevent

/-- The plane-and-time coordinate identification, as a continuous linear map. -/
@[expose] def planeLiftCLM : Vec 2 × ℝ →L[ℝ] (ℝ × ℝ) × ℝ :=
  (((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).prod
      (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2))).comp
    (ContinuousLinearMap.fst ℝ (Vec 2) ℝ)).prod (ContinuousLinearMap.snd ℝ (Vec 2) ℝ)

theorem planeLiftCLM_eq : (planeLiftCLM : Vec 2 × ℝ → (ℝ × ℝ) × ℝ) = planeLiftPoint := by
  funext w
  simp [planeLiftCLM, planeLiftPoint, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply]

theorem hasFDerivAt_planeLiftPoint (w : Vec 2 × ℝ) :
    HasFDerivAt planeLiftPoint planeLiftCLM w := by
  rw [← planeLiftCLM_eq]
  exact planeLiftCLM.hasFDerivAt

theorem hasFDerivAt_comp_planeLiftPoint {F : (ℝ × ℝ) × ℝ → ℝ} {w : Vec 2 × ℝ}
    (hF : DifferentiableAt ℝ F (planeLiftPoint w)) :
    HasFDerivAt (fun w' : Vec 2 × ℝ => F (planeLiftPoint w'))
      ((fderiv ℝ F (planeLiftPoint w)).comp planeLiftCLM) w :=
  hF.hasFDerivAt.comp w (hasFDerivAt_planeLiftPoint w)

theorem fderiv_comp_planeLiftPoint_basisVec0 {F : (ℝ × ℝ) × ℝ → ℝ} {w : Vec 2 × ℝ}
    (hF : DifferentiableAt ℝ F (planeLiftPoint w)) :
    fderiv ℝ (fun w' : Vec 2 × ℝ => F (planeLiftPoint w')) w (basisVec 0, 0)
      = dr F (planeLiftPoint w) := by
  rw [(hasFDerivAt_comp_planeLiftPoint hF).fderiv, dr_eq_fderiv_apply hF]
  simp [planeLiftCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, basisVec_apply]

theorem fderiv_comp_planeLiftPoint_basisVec1 {F : (ℝ × ℝ) × ℝ → ℝ} {w : Vec 2 × ℝ}
    (hF : DifferentiableAt ℝ F (planeLiftPoint w)) :
    fderiv ℝ (fun w' : Vec 2 × ℝ => F (planeLiftPoint w')) w (basisVec 1, 0)
      = dz F (planeLiftPoint w) := by
  rw [(hasFDerivAt_comp_planeLiftPoint hF).fderiv, dz_eq_fderiv_apply hF]
  simp [planeLiftCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, basisVec_apply]

theorem fderiv_comp_planeLiftPoint_time {F : (ℝ × ℝ) × ℝ → ℝ} {w : Vec 2 × ℝ}
    (hF : DifferentiableAt ℝ F (planeLiftPoint w)) :
    fderiv ℝ (fun w' : Vec 2 × ℝ => F (planeLiftPoint w')) w ((0 : Vec 2), (1 : ℝ))
      = dtPast F (planeLiftPoint w) := by
  rw [(hasFDerivAt_comp_planeLiftPoint hF).fderiv, dtPast_eq_fderiv_apply hF]
  simp [planeLiftCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply]

/-- The `Vec 2 × ℝ` double derivative of a plane function composed with `planeLiftPoint`, in the
direction `basisVec 0` twice, in terms of the plane function's own `dr ∘ dr`. -/
theorem fderiv_fderiv_comp_planeLiftPoint_basisVec0 {F : (ℝ × ℝ) × ℝ → ℝ}
    {D : Set ((ℝ × ℝ) × ℝ)} (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) {w : Vec 2 × ℝ}
    (hw : planeLiftPoint w ∈ D) :
    fderiv ℝ (fun w' : Vec 2 × ℝ =>
        fderiv ℝ (fun w'' : Vec 2 × ℝ => F (planeLiftPoint w'')) w' (basisVec 0, 0))
      w (basisVec 0, 0)
      = dr (dr F) (planeLiftPoint w) := by
  set U : Set (Vec 2 × ℝ) := planeLiftPoint ⁻¹' D with hU_def
  have hUopen : IsOpen U := hD.preimage continuous_planeLiftPoint
  have hFdiff : ∀ p ∈ D, DifferentiableAt ℝ F p := fun p hp =>
    (hF.differentiableOn (by norm_num) p hp).differentiableAt (hD.mem_nhds hp)
  have heq : Set.EqOn (fun w' : Vec 2 × ℝ =>
      fderiv ℝ (fun w'' : Vec 2 × ℝ => F (planeLiftPoint w'')) w' (basisVec 0, 0))
      (fun w' => dr F (planeLiftPoint w')) U := fun w' hw' =>
    fderiv_comp_planeLiftPoint_basisVec0 (hFdiff (planeLiftPoint w') hw')
  have hevent := heq.eventuallyEq_of_mem (hUopen.mem_nhds hw)
  rw [hevent.fderiv_eq]
  exact fderiv_comp_planeLiftPoint_basisVec0 (differentiableAt_dr_of_contDiffOn hD hF hw)

/-- The `Vec 2 × ℝ` double derivative of a plane function composed with `planeLiftPoint`, in the
direction `basisVec 1` twice, in terms of the plane function's own `dz ∘ dz`. -/
theorem fderiv_fderiv_comp_planeLiftPoint_basisVec1 {F : (ℝ × ℝ) × ℝ → ℝ}
    {D : Set ((ℝ × ℝ) × ℝ)} (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) {w : Vec 2 × ℝ}
    (hw : planeLiftPoint w ∈ D) :
    fderiv ℝ (fun w' : Vec 2 × ℝ =>
        fderiv ℝ (fun w'' : Vec 2 × ℝ => F (planeLiftPoint w'')) w' (basisVec 1, 0))
      w (basisVec 1, 0)
      = dz (dz F) (planeLiftPoint w) := by
  set U : Set (Vec 2 × ℝ) := planeLiftPoint ⁻¹' D with hU_def
  have hUopen : IsOpen U := hD.preimage continuous_planeLiftPoint
  have hFdiff : ∀ p ∈ D, DifferentiableAt ℝ F p := fun p hp =>
    (hF.differentiableOn (by norm_num) p hp).differentiableAt (hD.mem_nhds hp)
  have heq : Set.EqOn (fun w' : Vec 2 × ℝ =>
      fderiv ℝ (fun w'' : Vec 2 × ℝ => F (planeLiftPoint w'')) w' (basisVec 1, 0))
      (fun w' => dz F (planeLiftPoint w')) U := fun w' hw' =>
    fderiv_comp_planeLiftPoint_basisVec1 (hFdiff (planeLiftPoint w') hw')
  have hevent := heq.eventuallyEq_of_mem (hUopen.mem_nhds hw)
  rw [hevent.fderiv_eq]
  exact fderiv_comp_planeLiftPoint_basisVec1 (differentiableAt_dz_of_contDiffOn hD hF hw)

/-! ## The swirl flux and the receding source term -/

/-- The receding-axis swirl flux `S_n² / (A_n + R)` of `eq:aniso:zoom:receding:equation`. -/
@[expose] def swirlFluxPlane (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  zoomSRec lam h rc zc u p ^ 2 / (rc / lam + p.1.1)

/-- The receding-axis source `(1/(A_n+R))∂_RΘ_n − Θ_n/(A_n+R)² + λ_n⁴δ_n H_n
+ (V_n/(A_n+R))Θ_n` of `eq:aniso:zoom:receding:equation`: the four terms that vanish together
with the `∂_Z`-part of the swirl flux and the `δ_n²∂_ZZ` term as `n → ∞`. -/
@[expose] def recedingSourcePlane (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (f : ParabolicPoint → Vec3)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  1 / (rc / lam + p.1.1) * dr (zoomTheta lam h rc zc u) p
    - zoomTheta lam h rc zc u p / (rc / lam + p.1.1) ^ 2
    + lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc p)
    + zoomVRec lam h rc zc u p / (rc / lam + p.1.1) * zoomTheta lam h rc zc u p

/-- The `∂_Z`-derivative of the swirl flux is `(1/(A_n+R))` times the `∂_Z`-derivative of
`S_n²`, since the denominator `A_n + R` does not depend on `Z`. -/
theorem dz_swirlFluxPlane_eq (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) :
    dz (swirlFluxPlane lam h rc zc u) p
      = 1 / (rc / lam + p.1.1) * dz (fun q => zoomSRec lam h rc zc u q ^ 2) p := by
  show deriv (fun z => zoomSRec lam h rc zc u ((p.1.1, z), p.2) ^ 2 / (rc / lam + p.1.1)) p.1.2
      = 1 / (rc / lam + p.1.1)
        * deriv (fun z => zoomSRec lam h rc zc u ((p.1.1, z), p.2) ^ 2) p.1.2
  rw [deriv_div_const, div_eq_inv_mul, one_div]

/-- The rescaled azimuthal vorticity equation of `eq:aniso:zoom:receding:equation`, rewritten
with the transport in advective form and the divergence-free correction, swirl source and force
gathered into the swirl flux `swirlFluxPlane` and the source `recedingSourcePlane`, ready for
`integral_recedingResidual_eq`. -/
theorem zoomTheta_pde_source_form {lam h rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hR : p.1.1 ≠ -(rc / lam)) :
    dtPast (zoomTheta lam h rc zc u) p
        + zoomVRec lam h rc zc u p * dr (zoomTheta lam h rc zc u) p
        + zoomWRec lam h rc zc u p * dz (zoomTheta lam h rc zc u) p
      = dr (dr (zoomTheta lam h rc zc u)) p
        + (lam ^ (2 * h)) ^ 2 * dz (dz (zoomTheta lam h rc zc u)) p
        + dz (swirlFluxPlane lam h rc zc u) p
        + recedingSourcePlane lam h rc zc u f p := by
  have hpde := zoomTheta_pde lam h rc zc hlam u pr f hsol haxi p hp hR
  have hswirl := dz_swirlFluxPlane_eq lam h rc zc u p
  simp only [recedingSourcePlane]
  linarith only [hpde, hswirl]

/-- `dr` of a plane function `ContDiffOn` order `≥ 2` on an open set is continuous there. -/
theorem continuousOn_dr_of_contDiffOn {F : (ℝ × ℝ) × ℝ → ℝ} {D : Set ((ℝ × ℝ) × ℝ)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) : ContinuousOn (dr F) D := by
  have hFdiff : ∀ p ∈ D, DifferentiableAt ℝ F p := fun p hp =>
    (hF.differentiableOn (by norm_num) p hp).differentiableAt (hD.mem_nhds hp)
  have heq : Set.EqOn (dr F) (fun p => fderiv ℝ F p ((1, 0), 0)) D := fun p hp =>
    dr_eq_fderiv_apply (hFdiff p hp)
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ F) D := hF.fderiv_of_isOpen hD (by norm_num)
  exact (h1.clm_apply contDiffOn_const).continuousOn.congr heq

/-! ## Domain membership and bounds along the moving centre -/

/-- A compact subset of `Vec 2 × ℝ` with time bounded by `-1` is contained in the box
`Kp ×ˢ J` of its projections, with `J` also bounded by `-1`. -/
private theorem exists_box_of_isCompact_vec2' {K : Set (Vec 2 × ℝ)} (hK : IsCompact K)
    (hKsub : K ⊆ univ ×ˢ Iic (-1 : ℝ)) :
    ∃ (Kp : Set (ℝ × ℝ)) (J : Set ℝ), IsCompact Kp ∧ IsCompact J ∧ (∀ τ ∈ J, τ ≤ -1) ∧
      ∀ z ∈ K, (z.1 0, z.1 1) ∈ Kp ∧ z.2 ∈ J := by
  have hc0 : Continuous (fun z : Vec 2 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
  have hc1 : Continuous (fun z : Vec 2 × ℝ => z.1 1) := (continuous_apply 1).comp continuous_fst
  have hcp : Continuous (fun z : Vec 2 × ℝ => (z.1 0, z.1 1)) := hc0.prodMk hc1
  refine ⟨(fun z : Vec 2 × ℝ => (z.1 0, z.1 1)) '' K, Prod.snd '' K,
    hK.image hcp, hK.image continuous_snd, ?_, fun z hz => ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩⟩
  rintro τ ⟨z, hz, rfl⟩
  exact (hKsub hz).2

/-- Eventually in `n`, the receding zoom point of every point of a compact `K ⊆ Vec 2 × ℝ`
with `K ⊆ univ ×ˢ Iic (-1)` lies in the unit cylinder. -/
private theorem eventually_mem_unitCylinder_of_isCompact_vec2' {h ρ : ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {rc zc : ℕ → ℝ}
    (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) (lam : ℕ → ℝ)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) {K : Set (Vec 2 × ℝ)} (hK : IsCompact K)
    (hKsub : K ⊆ univ ×ˢ Iic (-1 : ℝ)) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z) ∈ unitCylinder := by
  obtain ⟨Kp, J, hKp, hJ, hJsub, hbox⟩ := exists_box_of_isCompact_vec2' hK hKsub
  filter_upwards [eventually_zoomPointRec_mem_unitCylinder_moving hh hρ0 hρ1 hcz lam hlam_lim Kp
    hKp J hJ hJsub] with n hn
  intro z hz
  obtain ⟨hzp, hzτ⟩ := hbox z hz
  exact hn (z.1 0, z.1 1) hzp z.2 hzτ

/-- Eventually in `n`, `A_n + R > 0` for `R` ranging over the radial projection of a
compact `K ⊆ Vec 2 × ℝ`. -/
private theorem eventually_one_le_ratio_add_of_isCompact_vec2' {rc : ℕ → ℝ} {lam : ℕ → ℝ}
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) {K : Set (Vec 2 × ℝ)} (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ z ∈ K, (1 : ℝ) ≤ rc n / lam n + z.1 0 := by
  have hc0 : Continuous (fun z : Vec 2 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  filter_upwards [hA.eventually_ge_atTop (B + 1)] with n hn
  intro z hz
  have h1 : |z.1 0| ≤ B := by
    have := hB z hz
    rwa [Real.norm_eq_abs] at this
  linarith only [hn, (abs_le.mp h1).1]

/-- `Θ_n` is bounded by `2C` at `τ ≤ -1` and `λ ≤ 1`. -/
private theorem abs_zoomTheta_le_two_mul' {C h lam rc zc : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hC : 0 ≤ C) (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hτ : p.2 ≤ -1) :
    |zoomTheta lam h rc zc u p| ≤ 2 * C := by
  have hΘ := abs_zoomTheta_le C h lam rc zc hlam_pos u hb (hu.of_le (by norm_num)) p hp
  have hτ1 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have e1 : (-p.2) ^ (-1 + h : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by
    linarith only [hh.2])
  have e2 : (-p.2) ^ (-1 - h : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by
    linarith only [hh.1])
  have e1' : 0 ≤ (-p.2) ^ (-1 + h : ℝ) := Real.rpow_nonneg (by linarith only [hτ1]) _
  have hd0 : 0 ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam_pos.le _
  have hd1 : lam ^ (2 * h) ≤ 1 := Real.rpow_le_one hlam_pos.le hlam_le (by linarith only [hh.1])
  have hd2 : (lam ^ (2 * h)) ^ 2 ≤ 1 := by nlinarith only [hd0, hd1]
  have hprod : (lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h : ℝ) ≤ 1 := by
    nlinarith only [hd2, e1, e1', sq_nonneg (lam ^ (2 * h))]
  have hsum : (lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h : ℝ) + (-p.2) ^ (-1 - h : ℝ) ≤ 2 := by
    linarith only [hprod, e2]
  calc |zoomTheta lam h rc zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h : ℝ) + (-p.2) ^ (-1 - h : ℝ)) := hΘ
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hsum hC
    _ = 2 * C := by ring

/-- `V_n` is bounded by `C` for `τ ≤ -1`. -/
private theorem abs_zoomVRec_le_of_tau_le_neg_one' {C h lam rc zc : ℝ} (hC : 0 ≤ C)
    (hlam_pos : 0 < lam) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hτ : p.2 ≤ -1) :
    |zoomVRec lam h rc zc u p| ≤ C := by
  have hbound := abs_zoomVRec_le C h lam rc zc hlam_pos u hb p hp
  have hexp : (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = -(1 / 2 : ℝ) := by ring
  rw [hexp] at hbound
  have hτge1 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτge1 (by
    norm_num)
  calc |zoomVRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

/-- `∂_R Θ_n` is bounded by `4C` for `τ ≤ -1` and `λ ≤ 1`. -/
private theorem abs_dr_zoomTheta_le_four_mul {C h lam rc zc : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hC : 0 ≤ C) (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hτ : p.2 ≤ -1) :
    |dr (zoomTheta lam h rc zc u) p| ≤ 4 * C := by
  have hd1 : lam ^ (2 * h) ≤ 1 := Real.rpow_le_one hlam_pos.le hlam_le (by linarith only [hh.1])
  have hbound := abs_dr_zoomTheta_le hlam_pos hb (hu.of_le (by norm_num)) hC hh.1.le hh.2.le hd1
    hp hτ
  have hτge1 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτge1 (by
    norm_num)
  calc |dr (zoomTheta lam h rc zc u) p| ≤ 4 * C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
    _ ≤ 4 * C * 1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 4 * C := mul_one _

/-- A function continuous on an open set of `Vec 2 × ℝ` whose product with a continuous
function of compact support closing inside that set is globally continuous. -/
private theorem continuous_mul_of_tsupport_subset_vec2ℝ {U : Set (Vec 2 × ℝ)} (hU : IsOpen U)
    {a b : Vec 2 × ℝ → ℝ} (ha : ContinuousOn a U) (hb : Continuous b) (hbU : tsupport b ⊆ U) :
    Continuous fun z => a z * b z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport b
  · exact (ha.continuousAt (hU.mem_nhds (hbU hz))).mul hb.continuousAt
  · have hopen : IsOpen (tsupport b)ᶜ := (isClosed_tsupport b).isOpen_compl
    have hev : (fun z => a z * b z) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, mul_zero]
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- A function on `Vec 2 × ℝ` vanishing off a measurable set of finite measure and bounded on
it has integral bounded by the bound times the measure. -/
private theorem abs_integral_le_of_forall_notMem_vec2 {S : Set (Vec 2 × ℝ)}
    (hS : volume S < ⊤) {g : Vec 2 × ℝ → ℝ} {Q : ℝ} (h0 : ∀ z, z ∉ S → g z = 0)
    (hQ : ∀ z ∈ S, |g z| ≤ Q) :
    |∫ z, g z| ≤ Q * (volume S).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const hS fun z hz => by
    rw [Real.norm_eq_abs]; exact hQ z hz

private theorem recResidual_abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by ring_nf
    _ ≤ |a| + |(-b)| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-! ## R2-R: the residual tends to zero -/

/-- R2-R: the residual of the rescaled receding vorticity-quotient equation tends to zero. -/
theorem tendsto_recResidual
    {C h CΓ ρ Rstar tstar : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar)
    (hR1 : Rstar ≤ 1) (htstar : tstar < 0) {rc zc : ℕ → ℝ}
    (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) (hC : 0 ≤ C)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f) {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) :
    ∀ φ ∈ testFunctions 2 (Iio (-1 : ℝ)), Tendsto (fun n => ∫ z,
      zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z) *
        (-(timeDeriv 2 φ z) - gradPair 2 φ z (recDrift (lam n) h (rc n) (zc n) u z)
          - recDriftDiv (lam n) h (rc n) (zc n) u z * φ z - partialLaplacian 2 1 φ z))
      atTop (nhds 0) := by
  rintro φ ⟨hφs, hφc, hφK⟩
  have hρ1 : ρ < 1 := hρR.trans_le hR1
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  have hfC : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder := hsol.2.2.1
  obtain ⟨Mf, hMf0⟩ := hforce
  have hMf0' : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ max Mf 0 :=
    fun z hz i α hα => (hMf0 z hz i α hα).trans (le_max_left _ _)
  set K : Set (Vec 2 × ℝ) := tsupport φ with hK_def
  have hKcompact : IsCompact K := hφc
  have hKsub : K ⊆ univ ×ˢ Iic (-1 : ℝ) :=
    fun z hz => ⟨mem_univ _, Set.mem_Iic.mpr (le_of_lt (hφK hz).2)⟩
  have hmem := eventually_mem_unitCylinder_of_isCompact_vec2' hh hρ0 hρ1 hcz lam hlam_lim
    hKcompact hKsub
  have hApos := eventually_one_le_ratio_add_of_isCompact_vec2' hA hKcompact
  have hlamlt : ∀ᶠ n in atTop, lam n < 1 :=
    (hlam_lim.mono_right nhdsWithin_le_nhds).eventually_mem
      (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
  have hKplaneC : IsCompact (planeLiftPoint '' K) := hKcompact.image continuous_planeLiftPoint
  have hKplaneT : ∀ p ∈ planeLiftPoint '' K, p.2 < 0 := by
    rintro _ ⟨z, hz, rfl⟩
    exact lt_of_le_of_lt (hKsub hz).2 (by norm_num)
  have hwindow := eventually_mem_zoomPointRec_moving hh hρ0 hρR htstar hcz hlam_lim
    (planeLiftPoint '' K) hKplaneC hKplaneT
  -- global bounds on `φ` and its first two derivatives on `K`
  have hc0 : Continuous (fun z : Vec 2 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
  obtain ⟨Rmax, hRmax⟩ := hKcompact.exists_bound_of_continuousOn hc0.continuousOn
  obtain ⟨Bφ0, hBφ0⟩ := hKcompact.exists_bound_of_continuousOn hφs.continuous.continuousOn
  obtain ⟨Bφ1', hBφ1'⟩ := hKcompact.exists_bound_of_continuousOn
    (hφs.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨Bφ2', hBφ2'⟩ := hKcompact.exists_bound_of_continuousOn
    ((hφs.fderiv_right (m := (⊤ : ℕ∞)) (by norm_num)).continuous_fderiv
      (by norm_num)).continuousOn
  set Bφ0' : ℝ := max Bφ0 0 with hBφ0'_def
  set Bφ1 : ℝ := max Bφ1' 0 with hBφ1_def
  set Bφ2 : ℝ := max Bφ2' 0 with hBφ2_def
  have hnorm1 : ‖basisVec (1 : Fin 2)‖ = (1 : ℝ) := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      rw [Real.norm_eq_abs, basisVec_apply]
      split_ifs <;> norm_num
    · have hle := norm_le_pi_norm (basisVec (1 : Fin 2)) 1
      simp only [basisVec_apply] at hle
      norm_num at hle
      linarith only [hle]
  have hnormdir : ‖((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)‖ = 1 := by
    rw [Prod.norm_def, hnorm1, norm_zero, max_eq_left (by norm_num : (0:ℝ) ≤ 1)]
  have hBφ1 : ∀ z ∈ K, |fderiv ℝ φ z (basisVec 1, 0)| ≤ Bφ1 := by
    intro z hz
    have h1 : ‖fderiv ℝ φ z (basisVec 1, 0)‖ ≤ ‖fderiv ℝ φ z‖ * ‖((basisVec 1, (0:ℝ)) : Vec 2 × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [hnormdir, mul_one] at h1
    have h2 : ‖fderiv ℝ φ z‖ ≤ Bφ1' := hBφ1' z hz
    calc |fderiv ℝ φ z (basisVec 1, 0)| = ‖fderiv ℝ φ z (basisVec 1, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ φ z‖ := h1
      _ ≤ Bφ1' := h2
      _ ≤ Bφ1 := le_max_left _ _
  have hBφ2 : ∀ z ∈ K, |fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0)|
      ≤ Bφ2 := by
    intro z hz
    have hcd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
      (hφs.fderiv_right (m := (⊤ : ℕ∞)) (by norm_num)).differentiable (by norm_num) z
    have hHF : HasFDerivAt (fun w => fderiv ℝ φ w (basisVec 1, 0))
        ((ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)).comp
          (fderiv ℝ (fderiv ℝ φ) z)) z :=
      (ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)).hasFDerivAt.comp z
        hcd.hasFDerivAt
    rw [hHF.fderiv]
    have hb1 : ‖(fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)‖
        ≤ ‖fderiv ℝ (fderiv ℝ φ) z‖ * ‖((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [hnormdir, mul_one] at hb1
    have hb2 : ‖(ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ))
          ((fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0))‖
        ≤ ‖(fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)‖ := by
      have := ContinuousLinearMap.le_opNorm
        (ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ))
        ((fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0))
      have hnorm_apply : ‖ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)‖
          ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
        rw [ContinuousLinearMap.apply_apply, one_mul]
        calc ‖x (basisVec 1, 0)‖ ≤ ‖x‖ * ‖((basisVec 1, (0:ℝ)) : Vec 2 × ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖x‖ := by rw [hnormdir, mul_one]
      calc ‖(ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ))
            ((fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0))‖
          ≤ ‖ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)‖
            * ‖(fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)‖ := this
        _ ≤ 1 * ‖(fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)‖ :=
            mul_le_mul_of_nonneg_right hnorm_apply (norm_nonneg _)
        _ = ‖(fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)‖ := one_mul _
    have h2 : ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ Bφ2' := hBφ2' z hz
    rw [Real.norm_eq_abs] at hb2
    show |(ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ)).comp
        (fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)| ≤ Bφ2
    rw [ContinuousLinearMap.comp_apply]
    calc |(ContinuousLinearMap.apply ℝ ℝ ((basisVec 1, (0 : ℝ)) : Vec 2 × ℝ))
          ((fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0))| ≤
          ‖(fderiv ℝ (fderiv ℝ φ) z) (basisVec 1, 0)‖ := hb2
      _ ≤ ‖fderiv ℝ (fderiv ℝ φ) z‖ := hb1
      _ ≤ Bφ2' := h2
      _ ≤ Bφ2 := le_max_left _ _

  set Rmax' : ℝ := max Rmax 0 with hRmax'_def
  have hRmax'0 : 0 ≤ Rmax' := le_max_right _ _
  have hRmax' : ∀ x ∈ K, ‖x.1 0‖ ≤ Rmax' := fun x hx => (hRmax x hx).trans (le_max_left _ _)
  have hAmore := hA.eventually_gt_atTop Rmax'
  -- the bound function and its limit
  set Fb : ℕ → ℝ := fun n => ((lam n ^ (2 * h)) ^ 2 * (2 * C) * Bφ2
      + CΓ ^ 2 * (lam n ^ (2 * h)) ^ 2 * Bφ1
      + ((rc n / lam n - Rmax')⁻¹ * (4 * C) + (rc n / lam n - Rmax') ⁻¹ ^ 2 * (2 * C)
          + lam n ^ 4 * lam n ^ (2 * h) * (2 * max Mf 0)
          + (rc n / lam n - Rmax')⁻¹ * C * (2 * C)) * Bφ0) * (volume K).toReal with hFb_def
  have hlam0 : Tendsto lam atTop (nhds (0 : ℝ)) := hlam_lim.mono_right nhdsWithin_le_nhds
  have hδtendsto : Tendsto (fun n => lam n ^ (2 * h)) atTop (nhds (0 : ℝ)) := by
    have hcont : Tendsto (fun l : ℝ => l ^ (2 * h)) (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) := by
      have h0 := (Real.continuousAt_rpow_const 0 (2 * h) (Or.inr (by linarith only [hh.1]))).tendsto
      rw [Real.zero_rpow (by linarith only [hh.1])] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact hcont.comp hlam_lim
  have hlam4tendsto : Tendsto (fun n => lam n ^ 4) atTop (nhds (0 : ℝ)) := by
    have := hlam0.pow 4
    simpa using this
  have hRatiotendsto : Tendsto (fun n => (rc n / lam n - Rmax')⁻¹) atTop (nhds (0 : ℝ)) := by
    have h1 : Tendsto (fun n => rc n / lam n - Rmax') atTop atTop :=
      hA.atTop_add (tendsto_const_nhds (x := (-Rmax' : ℝ))) |>.congr (fun n => by ring)
    exact h1.inv_tendsto_atTop
  have hFbtendsto : Tendsto Fb atTop (nhds (0 : ℝ)) := by
    have h1 : Tendsto (fun n => (lam n ^ (2 * h)) ^ 2 * (2 * C) * Bφ2) atTop (nhds (0 : ℝ)) := by
      have := ((hδtendsto.pow 2).mul_const (2 * C)).mul_const Bφ2
      simpa using this
    have h2 : Tendsto (fun n => CΓ ^ 2 * (lam n ^ (2 * h)) ^ 2 * Bφ1) atTop (nhds (0 : ℝ)) := by
      have := (hδtendsto.pow 2).const_mul (CΓ ^ 2) |>.mul_const Bφ1
      simpa using this
    have h3 : Tendsto (fun n => (rc n / lam n - Rmax')⁻¹ * (4 * C)) atTop (nhds (0 : ℝ)) := by
      have := hRatiotendsto.mul_const (4 * C); simpa using this
    have h4 : Tendsto (fun n => (rc n / lam n - Rmax') ⁻¹ ^ 2 * (2 * C)) atTop (nhds (0 : ℝ)) := by
      have := (hRatiotendsto.pow 2).mul_const (2 * C); simpa using this
    have h5 : Tendsto (fun n => lam n ^ 4 * lam n ^ (2 * h) * (2 * max Mf 0)) atTop
        (nhds (0 : ℝ)) := by
      have := (hlam4tendsto.mul hδtendsto).mul_const (2 * max Mf 0)
      simpa using this
    have h6 : Tendsto (fun n => (rc n / lam n - Rmax')⁻¹ * C * (2 * C)) atTop (nhds (0 : ℝ)) := by
      have := (hRatiotendsto.mul_const C).mul_const (2 * C); simpa using this
    have h7 : Tendsto (fun n => ((rc n / lam n - Rmax')⁻¹ * (4 * C)
        + (rc n / lam n - Rmax') ⁻¹ ^ 2 * (2 * C) + lam n ^ 4 * lam n ^ (2 * h) * (2 * max Mf 0)
        + (rc n / lam n - Rmax')⁻¹ * C * (2 * C)) * Bφ0) atTop (nhds (0 : ℝ)) := by
      have := (((h3.add h4).add h5).add h6).mul_const Bφ0
      simpa using this
    have h8 := (h1.add h2).add h7
    have := h8.mul_const (volume K).toReal
    simpa [hFb_def] using this
  refine squeeze_zero_norm' ?_ hFbtendsto
  -- eventually in `n`: assemble the residual
  filter_upwards [hmem, hApos, hlamlt, hwindow, hAmore] with n hmem_n hApos_n hlamlt_n hwindow_n
    hAmore_n
  set A : ℝ := rc n / lam n with hA_def
  set δ : ℝ := lam n ^ (2 * h) with hδ_def
  set D : Set ((ℝ × ℝ) × ℝ) := {p | zoomPointRec (lam n) h (rc n) (zc n) p ∈ unitCylinder}
    with hD_def
  have hDopen : IsOpen D :=
    isOpen_unitCylinder_prod.preimage (continuous_zoomPointRec (lam n) h (rc n) (zc n))
  have hplSmooth : ContDiff ℝ (⊤ : ℕ∞) planeLiftPoint := planeLiftCLM_eq ▸ planeLiftCLM.contDiff
  set S : Set (Vec 2 × ℝ) := {w | planeLiftPoint w ∈ D ∧ 0 < A + w.1 0} with hS_def
  have hSopen : IsOpen S :=
    (hDopen.preimage continuous_planeLiftPoint).inter
      (isOpen_lt continuous_const (continuous_const.add ((continuous_apply 0).comp
        continuous_fst)))
  have hKS : K ⊆ S := fun z hz => ⟨hmem_n z hz, by
    have := hApos_n z hz; simp only [hA_def]; linarith only [this]⟩
  -- smoothness of the plane-level objects on `D`
  have hΘsmoothPlane : ContDiffOn ℝ (⊤ : ℕ∞) (zoomTheta (lam n) h (rc n) (zc n) u) D := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p => azimuthalVorticity u (zoomPointRec (lam n) h (rc n) (zc n) p)) D :=
      (contDiffOn_azimuthalVorticity hu).comp
        (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).contDiffOn (fun p hp => hp)
    exact contDiffOn_const.mul hcomp
  have hVsmoothPlane : ContDiffOn ℝ (⊤ : ℕ∞) (zoomVRec (lam n) h (rc n) (zc n) u) D := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p => u (zoomPointRec (lam n) h (rc n) (zc n) p) 0) D :=
      (contDiffOn_pi.1 hu 0).comp (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).contDiffOn
        (fun p hp => hp)
    exact contDiffOn_const.mul hcomp
  have hWsmoothPlane : ContDiffOn ℝ (⊤ : ℕ∞) (zoomWRec (lam n) h (rc n) (zc n) u) D := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p => u (zoomPointRec (lam n) h (rc n) (zc n) p) 2) D :=
      (contDiffOn_pi.1 hu 2).comp (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).contDiffOn
        (fun p hp => hp)
    exact contDiffOn_const.mul hcomp
  have hSsmoothPlane : ContDiffOn ℝ (⊤ : ℕ∞) (zoomSRec (lam n) h (rc n) (zc n) u) D := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p => u (zoomPointRec (lam n) h (rc n) (zc n) p) 1) D :=
      (contDiffOn_pi.1 hu 1).comp (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).contDiffOn
        (fun p hp => hp)
    exact contDiffOn_const.mul hcomp
  have hSonD : S ⊆ planeLiftPoint ⁻¹' D := fun w hw => hw.1
  -- the plane-level smoothness of the swirl flux, on the open set where the denominator
  -- does not vanish
  set D' : Set ((ℝ × ℝ) × ℝ) := D ∩ {p | A + p.1.1 ≠ 0} with hD'_def
  have hp11cd : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => p.1.1) := contDiff_fst.comp contDiff_fst
  have hD'open : IsOpen D' :=
    hDopen.inter (isOpen_ne_fun (continuous_const.add hp11cd.continuous) continuous_const)
  have hSwirlSmoothPlane : ContDiffOn ℝ (⊤ : ℕ∞) (swirlFluxPlane (lam n) h (rc n) (zc n) u) D' := by
    have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (zoomSRec (lam n) h (rc n) (zc n) u) D' :=
      hSsmoothPlane.mono Set.inter_subset_left
    have hden : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => A + p.1.1) D' :=
      contDiffOn_const.add hp11cd.contDiffOn
    exact (hnum.pow 2).div hden (fun p hp => hp.2)
  have hSonD' : S ⊆ planeLiftPoint ⁻¹' D' := fun w hw => ⟨hw.1, by
    show A + (planeLiftPoint w).1.1 ≠ 0
    have heq : (planeLiftPoint w).1.1 = w.1 0 := rfl
    rw [heq]; exact ne_of_gt hw.2⟩
  -- `q`, `B`, `Fz`, `G` on `S`
  set q : Vec 2 × ℝ → ℝ := fun w => zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint w)
    with hq_def
  set B : Vec 2 × ℝ → Vec 2 := recDrift (lam n) h (rc n) (zc n) u with hB_def
  set divB : Vec 2 × ℝ → ℝ := recDriftDiv (lam n) h (rc n) (zc n) u with hdivB_def
  set Fz : Vec 2 × ℝ → ℝ := fun w => swirlFluxPlane (lam n) h (rc n) (zc n) u (planeLiftPoint w)
    with hFz_def
  set G : Vec 2 × ℝ → ℝ := fun w =>
    recedingSourcePlane (lam n) h (rc n) (zc n) u f (planeLiftPoint w) with hG_def
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q S :=
    hΘsmoothPlane.comp (hplSmooth.contDiffOn) hSonD
  have hB0eq : (fun w : Vec 2 × ℝ => B w 0) = fun w => zoomVRec (lam n) h (rc n) (zc n) u
      (planeLiftPoint w) := by funext w; simp [hB_def, recDrift]
  have hB1eq : (fun w : Vec 2 × ℝ => B w 1) = fun w => zoomWRec (lam n) h (rc n) (zc n) u
      (planeLiftPoint w) := by funext w; simp [hB_def, recDrift]
  have hB0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => B w 0) S := by
    rw [hB0eq]; exact hVsmoothPlane.comp hplSmooth.contDiffOn hSonD
  have hB1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => B w 1) S := by
    rw [hB1eq]; exact hWsmoothPlane.comp hplSmooth.contDiffOn hSonD
  have hBcd : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => B w i) S := by
    intro i; fin_cases i
    · exact hB0
    · exact hB1
  have hSdenom_ne : ∀ w ∈ S, A + w.1 0 ≠ 0 := fun w hw => ne_of_gt hw.2
  have hFz : ContDiffOn ℝ (⊤ : ℕ∞) Fz S := by
    have hnumEq : Fz
        = fun w => zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint w) ^ 2 / (A + w.1 0) := by
      funext w
      show swirlFluxPlane (lam n) h (rc n) (zc n) u (planeLiftPoint w)
          = zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint w) ^ 2 / (A + w.1 0)
      have : (planeLiftPoint w).1.1 = w.1 0 := rfl
      simp only [swirlFluxPlane, hA_def, this]
    rw [hnumEq]
    have hnum : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w => zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint w)) S :=
      hSsmoothPlane.comp hplSmooth.contDiffOn hSonD
    have hw10cd : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec 2 × ℝ => w.1 0) :=
      (contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_fst
    have hden : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec 2 × ℝ => A + w.1 0) S :=
      contDiffOn_const.add hw10cd.contDiffOn
    exact (hnum.pow 2).div hden hSdenom_ne
  have hG : ContinuousOn G S := by
    have h1 : ContinuousOn (fun w : Vec 2 × ℝ => dr (zoomTheta (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w)) S :=
      (continuousOn_dr_of_contDiffOn hDopen
        (hΘsmoothPlane.of_le (by norm_num))).comp
        (continuous_planeLiftPoint.continuousOn) hSonD
    have h2 : ContinuousOn (fun w : Vec 2 × ℝ =>
        zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint w)) S :=
      hΘsmoothPlane.continuousOn.comp continuous_planeLiftPoint.continuousOn hSonD
    have h3 : ContinuousOn (fun w : Vec 2 × ℝ =>
        curlComp f 1 (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint w))) S :=
      (contDiffOn_curlComp_unitCylinder hfC 1).continuousOn.comp
        ((contDiff_zoomPointRec (lam n) h (rc n) (zc n)).continuous.comp_continuousOn
          continuous_planeLiftPoint.continuousOn) hSonD
    have h4 : ContinuousOn (fun w : Vec 2 × ℝ =>
        zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint w)) S :=
      hVsmoothPlane.continuousOn.comp continuous_planeLiftPoint.continuousOn hSonD
    have hden1 : ContinuousOn (fun w : Vec 2 × ℝ => A + w.1 0) S :=
      continuousOn_const.add (((continuous_apply 0).comp continuous_fst).continuousOn)
    have hden2 : ContinuousOn (fun w : Vec 2 × ℝ => (A + w.1 0) ^ 2) S := hden1.pow 2
    have hGeq : G = fun w => 1 / (A + w.1 0) *
        dr (zoomTheta (lam n) h (rc n) (zc n) u) (planeLiftPoint w)
        - zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint w) / (A + w.1 0) ^ 2
        + lam n ^ 4 * δ * curlComp f 1 (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint w))
        + zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint w) / (A + w.1 0)
          * zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint w) := by
      funext w; simp only [hG_def, recedingSourcePlane]; rfl
    rw [hGeq]
    exact ((((continuousOn_const.div hden1 hSdenom_ne).mul h1).sub
      (h2.div hden2 (fun w hw => pow_ne_zero 2 (hSdenom_ne w hw)))).add
      (continuousOn_const.mul h3)).add ((h4.div hden1 hSdenom_ne).mul h2)
  -- the divergence identity
  have hdiv : ∀ w ∈ S, ∑ i, fderiv ℝ (fun w' => B w' i) w (basisVec i, 0) = divB w := by
    intro w hw
    have hVdiffPlane : DifferentiableAt ℝ (zoomVRec (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w) := (hVsmoothPlane.differentiableOn (by norm_num) (planeLiftPoint w)
      hw.1).differentiableAt (hDopen.mem_nhds hw.1)
    have hWdiffPlane : DifferentiableAt ℝ (zoomWRec (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w) := (hWsmoothPlane.differentiableOn (by norm_num) (planeLiftPoint w)
      hw.1).differentiableAt (hDopen.mem_nhds hw.1)
    have hV0 : fderiv ℝ (fun w' => B w' 0) w (basisVec 0, 0)
        = dr (zoomVRec (lam n) h (rc n) (zc n) u) (planeLiftPoint w) := by
      rw [hB0eq]; exact fderiv_comp_planeLiftPoint_basisVec0 hVdiffPlane
    have hW1 : fderiv ℝ (fun w' => B w' 1) w (basisVec 1, 0)
        = dz (zoomWRec (lam n) h (rc n) (zc n) u) (planeLiftPoint w) := by
      rw [hB1eq]; exact fderiv_comp_planeLiftPoint_basisVec1 hWdiffPlane
    have hRne : w.1 0 ≠ -(rc n / lam n) := by
      intro hc; have hp := hw.2; rw [hA_def] at hp; linarith only [hp, hc]
    have hRne' : (planeLiftPoint w).1.1 ≠ -(rc n / lam n) := hRne
    have hdivid := zoomRec_divergence_identity (lam n) h (rc n) (zc n) (hlam_pos n) u pr f hsol
      haxi (planeLiftPoint w) hw.1 hRne'
    have heqdivB : divB w
        = -(zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint w) / (rc n / lam n + w.1 0)) := rfl
    have heq11 : (planeLiftPoint w).1.1 = w.1 0 := rfl
    rw [heq11] at hdivid
    rw [Fin.sum_univ_two, hV0, hW1, heqdivB]
    linarith only [hdivid]
  -- the pde identity
  have hpde : ∀ w ∈ S, fderiv ℝ q w (0, 1) + ∑ i, B w i * fderiv ℝ q w (basisVec i, 0)
      = (∑ i : Fin 2, if (i : ℕ) < 1 then
          fderiv ℝ (fun w' => fderiv ℝ q w' (basisVec i, 0)) w (basisVec i, 0) else 0)
        + δ ^ 2 * fderiv ℝ (fun w' => fderiv ℝ q w' (basisVec 1, 0)) w (basisVec 1, 0)
        + fderiv ℝ Fz w (basisVec 1, 0) + G w := by
    intro w hw
    have hΘdiffPlane : DifferentiableAt ℝ (zoomTheta (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w) := (hΘsmoothPlane.differentiableOn (by norm_num) (planeLiftPoint w)
      hw.1).differentiableAt (hDopen.mem_nhds hw.1)
    have hVdiffPlane : DifferentiableAt ℝ (zoomVRec (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w) := (hVsmoothPlane.differentiableOn (by norm_num) (planeLiftPoint w)
      hw.1).differentiableAt (hDopen.mem_nhds hw.1)
    have hWdiffPlane : DifferentiableAt ℝ (zoomWRec (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w) := (hWsmoothPlane.differentiableOn (by norm_num) (planeLiftPoint w)
      hw.1).differentiableAt (hDopen.mem_nhds hw.1)
    have hFzdiffPlane : DifferentiableAt ℝ (swirlFluxPlane (lam n) h (rc n) (zc n) u)
        (planeLiftPoint w) := (hSwirlSmoothPlane.differentiableOn (by norm_num)
      (planeLiftPoint w) (hSonD' hw)).differentiableAt (hD'open.mem_nhds (hSonD' hw))
    have hqtime : fderiv ℝ q w (0, 1)
        = dtPast (zoomTheta (lam n) h (rc n) (zc n) u) (planeLiftPoint w) := by
      rw [hq_def]; exact fderiv_comp_planeLiftPoint_time hΘdiffPlane
    have hq0 : fderiv ℝ q w (basisVec 0, 0)
        = dr (zoomTheta (lam n) h (rc n) (zc n) u) (planeLiftPoint w) := by
      rw [hq_def]; exact fderiv_comp_planeLiftPoint_basisVec0 hΘdiffPlane
    have hq1 : fderiv ℝ q w (basisVec 1, 0)
        = dz (zoomTheta (lam n) h (rc n) (zc n) u) (planeLiftPoint w) := by
      rw [hq_def]; exact fderiv_comp_planeLiftPoint_basisVec1 hΘdiffPlane
    have hqq0 : fderiv ℝ (fun w' => fderiv ℝ q w' (basisVec 0, 0)) w (basisVec 0, 0)
        = dr (dr (zoomTheta (lam n) h (rc n) (zc n) u)) (planeLiftPoint w) := by
      rw [hq_def]
      exact fderiv_fderiv_comp_planeLiftPoint_basisVec0 hDopen
        (hΘsmoothPlane.of_le (by norm_num)) hw.1
    have hqq1 : fderiv ℝ (fun w' => fderiv ℝ q w' (basisVec 1, 0)) w (basisVec 1, 0)
        = dz (dz (zoomTheta (lam n) h (rc n) (zc n) u)) (planeLiftPoint w) := by
      rw [hq_def]
      exact fderiv_fderiv_comp_planeLiftPoint_basisVec1 hDopen
        (hΘsmoothPlane.of_le (by norm_num)) hw.1
    have hFztime : fderiv ℝ Fz w (basisVec 1, 0)
        = dz (swirlFluxPlane (lam n) h (rc n) (zc n) u) (planeLiftPoint w) := by
      rw [hFz_def]; exact fderiv_comp_planeLiftPoint_basisVec1 hFzdiffPlane
    have hRne : w.1 0 ≠ -(rc n / lam n) := by
      intro hc; have hp := hw.2; rw [hA_def] at hp; linarith only [hp, hc]
    have hRne' : (planeLiftPoint w).1.1 ≠ -(rc n / lam n) := hRne
    have hsource := zoomTheta_pde_source_form (hlam_pos n) hsol haxi (planeLiftPoint w) hw.1 hRne'
    have hBeq0 : B w 0 = zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint w) :=
      congrFun hB0eq w
    have hBeq1 : B w 1 = zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint w) :=
      congrFun hB1eq w
    rw [Fin.sum_univ_two, hBeq0, hBeq1, hqtime, hq0, hq1, sum_fin_two_ite_lt_one, hqq0, hqq1,
      hFztime]
    have hGeqw : G w = recedingSourcePlane (lam n) h (rc n) (zc n) u f (planeLiftPoint w) := rfl
    rw [hGeqw, hδ_def]
    linarith only [hsource]
  -- apply the weak-form identity
  have hKS' : K ⊆ S := hKS
  have hweak := integral_recedingResidual_eq hSopen hKcompact hKS' (δ ^ 2) hq hBcd hFz hG hdiv
    hpde
    hφs hφc subset_rfl
  rw [Real.norm_eq_abs, hweak]
  -- bound the three-term remainder
  have hSdenom_ne' : ∀ w ∈ K, A + w.1 0 ≠ 0 := fun w hw => hSdenom_ne w (hKS hw)
  have hApos_n' : ∀ w ∈ K, (0 : ℝ) < A + w.1 0 := fun w hw => by
    have := hApos_n w hw; linarith only [this]
  have hAmore_n' : Rmax' < A := hAmore_n
  set g : Vec 2 × ℝ → ℝ := fun z => δ ^ 2 * q z *
      fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0)
      - Fz z * fderiv ℝ φ z (basisVec 1, 0) + G z * φ z with hg_def
  have hg0 : ∀ z, z ∉ K → g z = 0 := by
    intro z hz
    have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
    have hφ'z : fderiv ℝ φ z (basisVec 1, 0) = 0 :=
      fderiv_apply_eq_zero_of_notMem_tsupport hz _
    have hφ''z : fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0) = 0 := by
      have hz' : z ∉ tsupport (fun w => fderiv ℝ φ w (basisVec 1, 0)) := fun h =>
        hz (tsupport_fderiv_apply_subset ℝ _ h)
      exact fderiv_apply_eq_zero_of_notMem_tsupport hz' _
    simp [hg_def, hφz, hφ'z, hφ''z]
  have hgQ : ∀ z ∈ K, |g z| ≤ δ ^ 2 * (2 * C) * Bφ2 + CΓ ^ 2 * δ ^ 2 * Bφ1
      + ((A - Rmax')⁻¹ * (4 * C) + (A - Rmax') ⁻¹ ^ 2 * (2 * C)
          + lam n ^ 4 * δ * (2 * max Mf 0) + (A - Rmax')⁻¹ * C * (2 * C)) * Bφ0 := by
    intro z hz
    have hqbound : |q z| ≤ 2 * C := by
      rw [hq_def]
      exact abs_zoomTheta_le_two_mul' hh hC (hlam_pos n) hlamlt_n.le hb hu (hmem_n z hz)
        (le_of_lt (hφK hz).2)
    have hApos_z : (0 : ℝ) < A + z.1 0 := hApos_n' z hz
    have hApos1_z : (1 : ℝ) ≤ A + z.1 0 := hApos_n z hz
    have hdenom_bound : (A + z.1 0)⁻¹ ≤ (A - Rmax')⁻¹ := by
      have h1 : A - Rmax' ≤ A + z.1 0 := by
        have := hRmax' z hz; have h2 := abs_le.mp this; linarith only [h2.1]
      have h1pos : 0 < A - Rmax' := by linarith only [hAmore_n']
      have := one_div_le_one_div_of_le h1pos h1
      rwa [one_div, one_div] at this
    have hSzbound : |zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)|
        ≤ CΓ * δ / (A + z.1 0) := by
      have hcirc : |circulation u (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z))|
          ≤ CΓ := by
        have hmemz := hmem_n z hz
        have hwz := hwindow_n (planeLiftPoint z) ⟨z, hz, rfl⟩
        exact hΓ _ hwz.1 _ hwz.2
      have := abs_zoomSRec_le_of_circulation (hlam_pos n) hApos_z hcirc
      rwa [← hA_def, ← hδ_def] at this
    have hFzbound : |Fz z| ≤ CΓ ^ 2 * δ ^ 2 := by
      rw [hFz_def]
      show |swirlFluxPlane (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ CΓ ^ 2 * δ ^ 2
      have heqz : swirlFluxPlane (lam n) h (rc n) (zc n) u (planeLiftPoint z)
          = zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint z) ^ 2 / (A + z.1 0) := by
        have hz11 : (planeLiftPoint z).1.1 = z.1 0 := rfl
        simp only [swirlFluxPlane, hz11, hA_def]
      rw [heqz, abs_div, abs_of_pos hApos_z, abs_of_nonneg (sq_nonneg _)]
      calc zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint z) ^ 2 / (A + z.1 0)
          = |zoomSRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ^ 2 / (A + z.1 0) := by
            rw [sq_abs]
        _ ≤ (CΓ * δ / (A + z.1 0)) ^ 2 / (A + z.1 0) := by
            gcongr
        _ = CΓ ^ 2 * δ ^ 2 / (A + z.1 0) ^ 3 := by
            rw [div_pow, div_div]
            ring_nf
        _ ≤ CΓ ^ 2 * δ ^ 2 := by
            have h1 : (1 : ℝ) ≤ (A + z.1 0) ^ 3 := one_le_pow₀ hApos1_z
            rw [div_le_iff₀ (by positivity)]
            nlinarith only [h1, sq_nonneg CΓ, sq_nonneg δ, sq_nonneg (CΓ * δ)]
    have hVzbound : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ C :=
      abs_zoomVRec_le_of_tau_le_neg_one' hC (hlam_pos n) hb (hmem_n z hz) (le_of_lt (hφK hz).2)
    have hdrΘzbound : |dr (zoomTheta (lam n) h (rc n) (zc n) u) (planeLiftPoint z)| ≤ 4 * C :=
      abs_dr_zoomTheta_le_four_mul hh hC (hlam_pos n) hlamlt_n.le hb hu (hmem_n z hz)
        (le_of_lt (hφK hz).2)
    have hRm_pos : (0 : ℝ) < A - Rmax' := by linarith only [hAmore_n']
    have hGzbound : |G z| ≤ (A - Rmax')⁻¹ * (4 * C) + (A - Rmax') ⁻¹ ^ 2 * (2 * C)
        + lam n ^ 4 * δ * (2 * max Mf 0) + (A - Rmax')⁻¹ * C * (2 * C) := by
      have hGeqz : G z = recedingSourcePlane (lam n) h (rc n) (zc n) u f (planeLiftPoint z) :=
        rfl
      rw [hGeqz]
      unfold recedingSourcePlane
      have hforceTerm : |lam n ^ 4 * lam n ^ (2 * h) *
          curlComp f 1 (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z))|
          ≤ 2 * max Mf 0 * (lam n ^ 4 * lam n ^ (2 * h)) :=
        abs_recedingForce_le (hlam_pos n) hMf0' (hmem_n z hz)
      have hΘzbound : |zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ 2 * C := by
        exact abs_zoomTheta_le_two_mul' hh hC (hlam_pos n) hlamlt_n.le hb hu (hmem_n z hz)
          (le_of_lt (hφK hz).2)
      set ta : ℝ := 1 / (A + z.1 0) * dr (zoomTheta (lam n) h (rc n) (zc n) u)
        (planeLiftPoint z) with hta_def
      set tb : ℝ := zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z) / (A + z.1 0) ^ 2
        with htb_def
      set tc : ℝ := lam n ^ 4 * lam n ^ (2 * h) *
        curlComp f 1 (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z)) with htc_def
      set td : ℝ := zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z) / (A + z.1 0)
        * zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z) with htd_def
      have hstep1 : |ta - tb + tc + td| ≤ |ta - tb| + |tc| + |td| := by
        have h1 := abs_add_le (ta - tb + tc) td
        have h2 := abs_add_le (ta - tb) tc
        linarith only [h1, h2]
      have hstep2 : |ta - tb| ≤ |ta| + |tb| := recResidual_abs_sub_le_abs_add_abs ta tb
      have hstepfin : |ta - tb + tc + td| ≤ |ta| + |tb| + |tc| + |td| := by
        linarith only [hstep1, hstep2]
      refine hstepfin.trans ?_
      have htabound : |ta| ≤ (A - Rmax')⁻¹ * (4 * C) := by
        rw [hta_def, abs_mul, abs_of_pos (div_pos one_pos hApos_z), one_div]
        exact mul_le_mul hdenom_bound hdrΘzbound (abs_nonneg _)
          (inv_nonneg.mpr hRm_pos.le)
      have htbbound : |tb| ≤ (A - Rmax') ⁻¹ ^ 2 * (2 * C) := by
        have hdsq : (A + z.1 0)⁻¹ ^ 2 ≤ (A - Rmax')⁻¹ ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.mpr hApos_z.le) hdenom_bound 2
        rw [htb_def, abs_div, abs_of_nonneg (sq_nonneg (A + z.1 0)), div_eq_mul_inv, ← inv_pow]
        exact (mul_le_mul hΘzbound hdsq (sq_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
      have htcbound : |tc| ≤ lam n ^ 4 * δ * (2 * max Mf 0) := by
        rw [htc_def, ← hδ_def]; exact hforceTerm.trans_eq (by ring)
      have hVoverA : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z) / (A + z.1 0)|
          ≤ (A - Rmax')⁻¹ * C := by
        rw [abs_div, abs_of_pos hApos_z, div_eq_mul_inv]
        calc |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| * (A + z.1 0)⁻¹
            ≤ C * (A + z.1 0)⁻¹ :=
              mul_le_mul_of_nonneg_right hVzbound (inv_nonneg.mpr hApos_z.le)
          _ ≤ C * (A - Rmax')⁻¹ := mul_le_mul_of_nonneg_left hdenom_bound hC
          _ = (A - Rmax')⁻¹ * C := mul_comm _ _
      have htdbound : |td| ≤ (A - Rmax')⁻¹ * C * (2 * C) := by
        rw [htd_def, abs_mul]
        exact mul_le_mul hVoverA hΘzbound (abs_nonneg _)
          (mul_nonneg (inv_nonneg.mpr hRm_pos.le) hC)
      linarith only [htabound, htbbound, htcbound, htdbound]
    have hgz : g z = δ ^ 2 * q z *
        fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0)
        - Fz z * fderiv ℝ φ z (basisVec 1, 0) + G z * φ z := by rw [hg_def]
    have hδnn : (0 : ℝ) ≤ δ ^ 2 := by rw [hδ_def]; positivity
    have htri : |g z| ≤ |δ ^ 2 * q z *
          fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0)|
        + |Fz z * fderiv ℝ φ z (basisVec 1, 0)| + |G z * φ z| := by
      rw [hgz]
      set A1 : ℝ := δ ^ 2 * q z *
        fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0) with hA1_def
      set A2 : ℝ := Fz z * fderiv ℝ φ z (basisVec 1, 0) with hA2_def
      set A3 : ℝ := G z * φ z with hA3_def
      have h1 : |A1 - A2 + A3| ≤ |A1 - A2| + |A3| := abs_add_le _ _
      have h2 : |A1 - A2| ≤ |A1| + |A2| := recResidual_abs_sub_le_abs_add_abs _ _
      linarith only [h1, h2]
    have hterm1 : |δ ^ 2 * q z *
          fderiv ℝ (fun w => fderiv ℝ φ w (basisVec 1, 0)) z (basisVec 1, 0)|
        ≤ δ ^ 2 * (2 * C) * Bφ2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hδnn]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hqbound hδnn) (hBφ2 z hz) (abs_nonneg _)
        (mul_nonneg hδnn (by linarith only [hC]))
    have hterm2 : |Fz z * fderiv ℝ φ z (basisVec 1, 0)| ≤ CΓ ^ 2 * δ ^ 2 * Bφ1 := by
      rw [abs_mul]
      exact mul_le_mul hFzbound (hBφ1 z hz) (abs_nonneg _) (by positivity)
    have hterm3 : |G z * φ z| ≤ ((A - Rmax')⁻¹ * (4 * C) + (A - Rmax') ⁻¹ ^ 2 * (2 * C)
        + lam n ^ 4 * δ * (2 * max Mf 0) + (A - Rmax')⁻¹ * C * (2 * C)) * Bφ0 := by
      rw [abs_mul]
      exact mul_le_mul hGzbound (hBφ0 z hz) (abs_nonneg _) ((abs_nonneg (G z)).trans hGzbound)
    linarith only [htri, hterm1, hterm2, hterm3]
  have hbound := abs_integral_le_of_forall_notMem_vec2 hKcompact.measure_lt_top hg0 hgQ
  have hFbeq : Fb n =
      (δ ^ 2 * (2 * C) * Bφ2 + CΓ ^ 2 * δ ^ 2 * Bφ1
        + ((A - Rmax')⁻¹ * (4 * C) + (A - Rmax') ⁻¹ ^ 2 * (2 * C)
            + lam n ^ 4 * δ * (2 * max Mf 0) + (A - Rmax')⁻¹ * C * (2 * C)) * Bφ0)
        * (volume K).toReal := by
    rw [hFb_def, hδ_def, hA_def]
  rw [hFbeq]
  exact hbound

end CIV
