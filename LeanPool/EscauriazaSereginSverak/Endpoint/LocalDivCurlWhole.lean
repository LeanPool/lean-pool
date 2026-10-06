/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalDivCurlSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceFlux
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.SupportThickening

/-!
# Whole-space div–curl regularity for Sobolev families

Compactly supported fields with Sobolev divergence and curl have one additional
weak derivative, with the estimate inherited from the smooth whole-space
div–curl inequality.
-/

public section

open MeasureTheory Set Filter
open scoped Convolution Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem localDivCurlWhole_mollify_eq_integral {f : Vec3 → ℝ}
    {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    CKN.mollify f ε hε x =
      ∫ y, f y * CKN.mollifier (d := 3) ε hε (x - y) := by
  rw [show CKN.mollify f ε hε x =
      ∫ t, CKN.mollifier (d := 3) ε hε t * f (x - t) by
        simp [CKN.mollify, convolution_def]]
  let F : Vec3 → ℝ := fun y => f y * CKN.mollifier (d := 3) ε hε (x - y)
  calc
    (∫ t, CKN.mollifier (d := 3) ε hε t * f (x - t)) = ∫ t, F (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp [F, mul_comm]
    _ = ∫ y, F y :=
      (Measure.measurePreserving_sub_left (volume : Measure Vec3) x).integral_comp
        (Homeomorph.subLeft x).measurableEmbedding F
    _ = ∫ y, f y * CKN.mollifier (d := 3) ε hε (x - y) := by
      rfl

@[expose] def localDivCurlWholeTestKernel (ε : ℝ) (hε : 0 < ε) (x : Vec3) : Vec3 → ℝ :=
  fun y => CKN.mollifier (d := 3) ε hε (x - y)

private theorem localDivCurlWholeTestKernel_contDiff (ε : ℝ) (hε : 0 < ε)
    (x : Vec3) : ContDiff ℝ (⊤ : ℕ∞) (localDivCurlWholeTestKernel ε hε x) := by
  exact (CKN.mollifier_contDiff hε).comp (contDiff_const.sub contDiff_id)

private theorem localDivCurlWholeTestKernel_compact (ε : ℝ) (hε : 0 < ε)
    (x : Vec3) : HasCompactSupport (localDivCurlWholeTestKernel ε hε x) := by
  exact (CKN.mollifier_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft x)

private theorem localDivCurlWholeTestKernel_deriv (ε : ℝ) (hε : 0 < ε)
    (x y : Vec3) (j : Fin 3) :
    spatialDeriv (localDivCurlWholeTestKernel ε hε x) j y =
      -spatialDeriv (CKN.mollifier (d := 3) ε hε) j (x - y) := by
  let k : Vec3 → ℝ := CKN.mollifier (d := 3) ε hε
  let φ : Vec3 → ℝ := fun z => k (x - z)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := CKN.mollifier_contDiff hε
  have hinner : HasFDerivAt (fun z : Vec3 => x - z)
      (-(1 : Vec3 →L[ℝ] Vec3)) y := (hasFDerivAt_id y).const_sub x
  have houter : HasFDerivAt k (fderiv ℝ k (x - y)) (x - y) :=
    ((hk.differentiable (by simp) (x - y)).hasFDerivAt)
  have hcomp := houter.comp y hinner
  have hderiv : (fderiv ℝ φ y) (basisVec j) =
      - (fderiv ℝ k (x - y)) (basisVec j) := by
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hcomp.fderiv
  change (fderiv ℝ (fun z => CKN.mollifier (d := 3) ε hε (x - z)) y)
      (basisVec j) =
    - (fderiv ℝ (CKN.mollifier (d := 3) ε hε) (x - y)) (basisVec j)
  simpa [φ, k] using hderiv

private theorem localDivCurlWhole_memLp_smooth_compact {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    MemLp f 2 volume :=
  hf.continuous.memLp_of_hasCompactSupport hfc

private theorem localDivCurlWhole_mollify_congr_ae {f g : Vec3 → ℝ}
    (hfg : f =ᵐ[volume] g) {ε : ℝ} (hε : 0 < ε) :
    CKN.mollify f ε hε = CKN.mollify g ε hε := by
  simp only [CKN.mollify]
  exact MeasureTheory.convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure Vec3)) Filter.EventuallyEq.rfl hfg

private theorem localDivCurlWhole_mollify_wordDeriv {m : ℕ} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ}
    (h : IsSobolevFamilyOn m univ f D) {ε : ℝ} (hε : 0 < ε)
    (α : List (Fin 3)) (hα : α.length ≤ m) (x : Vec3) :
    wordDeriv α (fun y => CKN.mollify f ε hε y) x =
      CKN.mollify (D α) ε hε x := by
  induction m generalizing f D α with
  | zero =>
      have hnil : α = [] := by
        have := hα
        cases α <;> simp_all
      subst α
      have hzero : D [] =ᵐ[volume] f := by
        simpa only [Measure.restrict_univ] using h.zero
      simpa [wordDeriv] using congrFun
        (localDivCurlWhole_mollify_congr_ae hzero.symm hε) x
  | succ m ih =>
      cases α with
      | nil =>
          have hzero : D [] =ᵐ[volume] f := by
            simpa only [Measure.restrict_univ] using h.zero
          simpa [wordDeriv] using congrFun
            (localDivCurlWhole_mollify_congr_ae hzero.symm hε) x
      | cons j β =>
          have hshift : IsSobolevFamilyOn m univ (D [j]) (fun γ => D (j :: γ)) :=
            (isSobolevFamilyOn_succ_iff.mp h).2 j |>.2
          have hweakD : HasWeakPartialDerivOn univ j (D []) (D [j]) :=
            h.weak [] j (by simp)
          have hzero : D [] =ᵐ[volume] f := by
            simpa only [Measure.restrict_univ] using h.zero
          have hD0mem : MemLp (D []) 2 volume := by
            simpa only [Measure.restrict_univ] using h.memL2 [] (by simp)
          have hDmem : MemLp (D [j]) 2 volume := by
            simpa only [Measure.restrict_univ] using h.memL2 [j] (by simp)
          have htrans (y : Vec3) :
              (fderiv ℝ (CKN.mollify (D []) ε hε) y) (basisVec j) =
                CKN.mollify (D [j]) ε hε y :=
            CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
              isOpen_univ
              (hD0mem.locallyIntegrable (by norm_num))
              (hDmem.locallyIntegrable (by norm_num)) hweakD hε
              (x := y) (by intro z hz; exact Set.mem_univ _)
          have hmoll : CKN.mollify f ε hε = CKN.mollify (D []) ε hε :=
            localDivCurlWhole_mollify_congr_ae hzero.symm hε
          have hderivD (y : Vec3) :
              spatialDeriv (fun z => CKN.mollify (D []) ε hε z) j y =
                CKN.mollify (D [j]) ε hε y := by
            exact htrans y
          have hderiv (y : Vec3) :
              spatialDeriv (fun z => CKN.mollify f ε hε z) j y =
                CKN.mollify (D [j]) ε hε y := by
            rw [show spatialDeriv (fun z => CKN.mollify f ε hε z) j y =
              spatialDeriv (fun z => CKN.mollify (D []) ε hε z) j y by
                exact congrArg (fun g : Vec3 → ℝ => spatialDeriv g j y) hmoll]
            exact hderivD y
          have hβ : β.length ≤ m := by
            simpa using hα
          have ihβ := ih hshift β hβ
          rw [show wordDeriv (j :: β) (fun y => CKN.mollify f ε hε y) x =
            wordDeriv β (fun y => spatialDeriv (fun z => CKN.mollify f ε hε z) j y) x
              by rfl]
          have hderivfun :
              (fun y => spatialDeriv (fun z => CKN.mollify f ε hε z) j y) =
                (fun y => CKN.mollify (D [j]) ε hε y) := by
            funext y
            exact hderiv y
          rw [hderivfun]
          simpa only [List.cons.injEq] using ihβ

@[expose] def localDivCurlWholeRadius (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem localDivCurlWholeRadius_pos (n : ℕ) :
    0 < localDivCurlWholeRadius n := by
  dsimp [localDivCurlWholeRadius]
  positivity

private theorem localDivCurlWholeRadius_le_one (n : ℕ) :
    localDivCurlWholeRadius n ≤ 1 := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  dsimp [localDivCurlWholeRadius]
  exact (inv_le_one₀ (by positivity)).2 hn

private theorem localDivCurlWholeRadius_tendsto :
    Tendsto localDivCurlWholeRadius atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp hden

private theorem localDivCurlWhole_mollify_memLp {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) (n : ℕ) :
    MemLp (CKN.mollify f (localDivCurlWholeRadius n)
      (localDivCurlWholeRadius_pos n)) 2 volume := by
  have hkint : Integrable
      (CKN.mollifier (d := 3) (localDivCurlWholeRadius n)
        (localDivCurlWholeRadius_pos n)) volume :=
    (CKN.mollifier_contDiff (d := 3) (localDivCurlWholeRadius_pos n)
      (n := 0)).continuous.integrable_of_hasCompactSupport
      (CKN.mollifier_hasCompactSupport (d := 3) (localDivCurlWholeRadius_pos n))
  have hbound : eLpNorm
      (CKN.mollify f (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n))
      2 volume ≤ eLpNorm f 2 volume := by
    simpa only [CKN.mollify] using
      CKN.young_convolution_nonneg_integral_one_of_aemeasurable
        (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top
        (CKN.mollifier_nonneg (d := 3) (localDivCurlWholeRadius_pos n)) hkint
        (CKN.mollifier_integral_one (d := 3) (localDivCurlWholeRadius_pos n))
        (CKN.mollifier_contDiff (d := 3) (localDivCurlWholeRadius_pos n)
          (n := 0)).continuous.measurable hf.aestronglyMeasurable.aemeasurable
  have hfinite : eLpNorm
      (CKN.mollify f (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n))
      2 volume < ∞ := hbound.trans_lt hf.eLpNorm_lt_top
  exact hfinite

private theorem localDivCurlWhole_mollify_tendsto {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm
      (CKN.mollify f (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n) - f)
      2 volume) atTop (𝓝 0) :=
  CKN.tendsto_eLpNorm_sub_zero_mollify (by norm_num) ENNReal.coe_ne_top hf
    localDivCurlWholeRadius_tendsto localDivCurlWholeRadius_pos

private theorem localDivCurlWhole_mollify_smooth {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (CKN.mollify f (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n)) :=
  CKN.mollify_contDiff (localDivCurlWholeRadius_pos n)
    (hf.locallyIntegrable (by norm_num))

private theorem localDivCurlWhole_mollify_compact {f : Vec3 → ℝ} {K : Set Vec3}
    (hK : IsCompact K) (hzero : ∀ x, x ∉ K → f x = 0) (n : ℕ) :
    HasCompactSupport
      (CKN.mollify f (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (CKN.thickening_compact hK.isBounded (δ := 12))
  exact CKN.mollify_support_subset (localDivCurlWholeRadius_pos n) hzero
    (by simpa using localDivCurlWholeRadius_le_one n)

private theorem localDivCurlWhole_spatialDeriv_compact {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (j : Fin 3) :
    HasCompactSupport (spatialDeriv f j) := by
  change HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec j))
  exact hf.fderiv_apply (𝕜 := ℝ) (basisVec j)

private theorem localDivCurlWhole_wordDeriv_compact {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (α : List (Fin 3)) : HasCompactSupport (wordDeriv α f) := by
  induction α generalizing f with
  | nil => simpa [wordDeriv] using hfc
  | cons j α ih =>
      exact ih (contDiff_wordDeriv hf [j])
        (localDivCurlWhole_spatialDeriv_compact hfc j)

private theorem localDivCurlWhole_eLpNorm_eq_sqrt {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂volume)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (f x)

private theorem localDivCurlWhole_integral_sq_eq {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) :
    ∫ x, f x ^ 2 ∂volume = (eLpNorm f 2 volume).toReal ^ 2 := by
  rw [localDivCurlWhole_eLpNorm_eq_sqrt hf,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x))]

private theorem localDivCurlWhole_eLpNorm_tendsto_zero_of_integral_sq
    {ι : Type*} {l : Filter ι} {g : ι → Vec3 → ℝ}
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hsq : Tendsto (fun i => ∫ x, g i x ^ 2 ∂volume) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (g i) 2 volume) l (𝓝 0) := by
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hnorm := (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp hroot
  have hzero : ENNReal.ofReal (Real.sqrt 0) = 0 := by simp
  rw [hzero] at hnorm
  exact hnorm.congr fun i => (localDivCurlWhole_eLpNorm_eq_sqrt (hg i)).symm

private theorem localDivCurlWhole_integral_sq_tendsto_zero
    {g : ℕ → Vec3 → ℝ} (hg : ∀ n, MemLp (g n) 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (g n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g n x ^ 2 ∂volume) atTop (𝓝 0) := by
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  have hsq := (continuous_pow 2).tendsto _ |>.comp hreal
  simp only [ENNReal.toReal_zero, Function.comp_def] at hsq
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    hsq.congr fun n => (localDivCurlWhole_integral_sq_eq (hg n)).symm

private theorem localDivCurlWhole_integral_sq_tendsto
    {g : ℕ → Vec3 → ℝ} {f : Vec3 → ℝ}
    (hg : ∀ n, MemLp (g n) 2 volume) (hf : MemLp f 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (g n - f) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g n x ^ 2 ∂volume)
      atTop (𝓝 (∫ x, f x ^ 2 ∂volume)) := by
  have hfact : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hF : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg f hf).2 hconv
  have hnorm := (continuous_norm.tendsto _).comp hF
  have hsq := (continuous_pow 2).tendsto _ |>.comp hnorm
  simp only [Function.comp_def, Lp.norm_toLp] at hsq
  rw [localDivCurlWhole_integral_sq_eq hf]
  exact hsq.congr fun n => (localDivCurlWhole_integral_sq_eq (hg n)).symm

private theorem localDivCurlWhole_integral_sq_pair_tendsto_zero
    {g : ℕ → Vec3 → ℝ} (hg : ∀ n, MemLp (g n) 2 volume)
    (hconv : Tendsto
      (fun p : ℕ × ℕ => eLpNorm (g p.1 - g p.2) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ x, (g p.1 x - g p.2 x) ^ 2 ∂volume)
      atTop (𝓝 0) := by
  have hmem (p : ℕ × ℕ) : MemLp (fun x => g p.1 x - g p.2 x) 2 volume :=
    (hg p.1).sub (hg p.2)
  have hconv' : Tendsto
      (fun p : ℕ × ℕ => eLpNorm (fun x => g p.1 x - g p.2 x) 2 volume)
      atTop (𝓝 0) := by
    change Tendsto
      (fun p : ℕ × ℕ => eLpNorm (fun x => g p.1 x - g p.2 x) 2 volume)
      atTop (𝓝 0) at hconv
    exact hconv
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv'
  have hreal' : Tendsto
      (fun p : ℕ × ℕ =>
        (eLpNorm (fun x => g p.1 x - g p.2 x) 2 volume).toReal) atTop (𝓝 0) := by
    change Tendsto (ENNReal.toReal ∘ fun p : ℕ × ℕ =>
      eLpNorm (fun x => g p.1 x - g p.2 x) 2 volume) atTop (𝓝 0)
    exact hreal
  have hsq := (continuous_pow 2).tendsto _ |>.comp hreal'
  have hnorm : Tendsto
      (fun p : ℕ × ℕ => (eLpNorm (fun x => g p.1 x - g p.2 x) 2 volume).toReal ^ 2)
      atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => x ^ 2) ∘ fun p : ℕ × ℕ =>
      (eLpNorm (fun x => g p.1 x - g p.2 x) 2 volume).toReal) atTop (𝓝 0)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsq
  refine hnorm.congr fun p => ?_
  exact (localDivCurlWhole_integral_sq_eq (hmem p)).symm

@[expose] def localDivCurlWholeApprox (V : Fin 3 → Vec3 → ℝ)
    (n : ℕ) : Fin 3 → Vec3 → ℝ :=
  fun i => CKN.mollify (V i) (localDivCurlWholeRadius n)
    (localDivCurlWholeRadius_pos n)

private theorem localDivCurlWhole_spatialDeriv_sub {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : Fin 3) :
    spatialDeriv (fun x => f x - g x) j =
      fun x => spatialDeriv f j x - spatialDeriv g j x := by
  funext x
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
    (fderiv_fun_sub ((hf.differentiable (by simp)) x)
      ((hg.differentiable (by simp)) x))
  simpa [spatialDeriv] using h

private theorem localDivCurlWhole_approx_smooth
    {V : Fin 3 → Vec3 → ℝ} (hVmem : ∀ i, MemLp (V i) 2 volume)
    (n : ℕ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (localDivCurlWholeApprox V n i) := by
  exact localDivCurlWhole_mollify_smooth (hVmem i) n

private theorem localDivCurlWhole_approx_compact
    {V : Fin 3 → Vec3 → ℝ} {K : Set Vec3}
    (hK : IsCompact K) (hVzero : ∀ i x, x ∉ K → V i x = 0)
    (n : ℕ) (i : Fin 3) : HasCompactSupport (localDivCurlWholeApprox V n i) := by
  exact localDivCurlWhole_mollify_compact hK (hVzero i) n

private theorem localDivCurlWhole_approx_family
    {V : Fin 3 → Vec3 → ℝ} {K : Set Vec3}
    (hVmem : ∀ i, MemLp (V i) 2 volume) (hK : IsCompact K)
    (hVzero : ∀ i x, x ∉ K → V i x = 0) (n : ℕ) (i : Fin 3) (q : ℕ) :
    IsSobolevFamilyOn q univ (localDivCurlWholeApprox V n i)
      (fun α => wordDeriv α (localDivCurlWholeApprox V n i)) := by
  apply isSobolevFamilyOn_wordDeriv isOpen_univ
    (localDivCurlWhole_approx_smooth hVmem n i)
  intro α hα
  have hmem : MemLp (wordDeriv α (localDivCurlWholeApprox V n i)) 2 volume :=
    localDivCurlWhole_memLp_smooth_compact
      (contDiff_wordDeriv (localDivCurlWhole_approx_smooth hVmem n i) α)
      (localDivCurlWhole_wordDeriv_compact
        (localDivCurlWhole_approx_smooth hVmem n i)
        (localDivCurlWhole_approx_compact hK hVzero n i) α)
  simpa only [Measure.restrict_univ] using hmem

private theorem localDivCurlWhole_normSq_nonneg (m : ℕ) (U : Set Vec3)
    (D : List (Fin 3) → Vec3 → ℝ) : 0 ≤ sobolevNormSqOn m U D := by
  unfold sobolevNormSqOn
  apply Finset.sum_nonneg
  intro α hα
  exact integral_nonneg fun x => sq_nonneg (D α x)

private theorem localDivCurlWhole_normSq_congr {m : ℕ}
    {D E : List (Fin 3) → Vec3 → ℝ}
    (h : ∀ α, α.length ≤ m → ∀ x, D α x = E α x) :
    sobolevNormSqOn m univ D = sobolevNormSqOn m univ E := by
  unfold sobolevNormSqOn
  apply Finset.sum_congr rfl
  intro α hα
  apply integral_congr_ae
  filter_upwards [] with x
  rw [h α (mem_sobolevWords.mp hα) x]


private theorem localDivCurlWhole_l2_exists_limit {f : ℕ → Vec3 → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume)
    (hcauchy : Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 volume)
      atTop (𝓝 0)) :
    ∃ g : Vec3 → ℝ, MemLp g 2 volume ∧
      Tendsto (fun n => eLpNorm (f n - g) 2 volume) atTop (𝓝 0) := by
  have hfact : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let F : ℕ → Lp ℝ 2 volume := fun n => (hf n).toLp (f n)
  have hdist (p : ℕ × ℕ) : dist (F p.1) (F p.2) =
      (eLpNorm (f p.1 - f p.2) 2 volume).toReal := by
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hf p.1).coeFn_toLp, (hf p.2).coeFn_toLp] with x hx hy
    simp only [Pi.sub_apply, F, hx, hy]
  have hcauchyReal : Tendsto
      (fun p : ℕ × ℕ => (eLpNorm (f p.1 - f p.2) 2 volume).toReal)
      atTop (𝓝 0) := by
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcauchy
    simpa only [ENNReal.toReal_zero, Function.comp_def] using hreal
  have hcauchyF : CauchySeq F := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    exact hcauchyReal.congr fun p => (hdist p).symm
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchyF
  refine ⟨G, Lp.memLp G, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hG
  refine hG.congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [(hf n).coeFn_toLp] with x hx
  simp only [Pi.sub_apply, F, hx]

private theorem localDivCurlWhole_l2_cauchy_of_tendsto {f : ℕ → Vec3 → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) {g : Vec3 → ℝ} (hg : MemLp g 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 volume)
      atTop (𝓝 0) := by
  have hfact : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let F : ℕ → Lp ℝ 2 volume := fun n => (hf n).toLp (f n)
  have hF : Tendsto F atTop (𝓝 ((hg).toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 hconv
  have hdist (p : ℕ × ℕ) : dist (F p.1) (F p.2) =
      (eLpNorm (f p.1 - f p.2) 2 volume).toReal := by
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hf p.1).coeFn_toLp, (hf p.2).coeFn_toLp] with x hx hy
    simp only [Pi.sub_apply, F, hx, hy]
  have hdistZero : Tendsto
      (fun p : ℕ × ℕ => dist (F p.1) (F p.2)) atTop (𝓝 0) := by
    exact (cauchySeq_iff_tendsto_dist_atTop_0.mp hF.cauchySeq)
  have hreal : Tendsto
      (fun p : ℕ × ℕ => (eLpNorm (f p.1 - f p.2) 2 volume).toReal)
      atTop (𝓝 0) := hdistZero.congr fun p => hdist p
  have hENN : Tendsto
      (fun p : ℕ × ℕ => ENNReal.ofReal (dist (F p.1) (F p.2)))
      atTop (𝓝 0) := by
    change Tendsto (ENNReal.ofReal ∘ fun p : ℕ × ℕ => dist (F p.1) (F p.2))
      atTop (𝓝 0)
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hdistZero
  refine hENN.congr fun p => ?_
  rw [hdist p]
  exact ENNReal.ofReal_toReal ((hf p.1).sub (hf p.2)).eLpNorm_ne_top

private theorem localDivCurlWhole_mollify_pair_tendsto {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm
      (CKN.mollify f (localDivCurlWholeRadius p.1)
          (localDivCurlWholeRadius_pos p.1) -
        CKN.mollify f (localDivCurlWholeRadius p.2)
          (localDivCurlWholeRadius_pos p.2)) 2 volume) atTop (𝓝 0) := by
  exact localDivCurlWhole_l2_cauchy_of_tendsto
    (f := fun n => CKN.mollify f (localDivCurlWholeRadius n)
      (localDivCurlWholeRadius_pos n))
    (fun n => localDivCurlWhole_mollify_memLp hf n) hf
    (localDivCurlWhole_mollify_tendsto hf)

private theorem localDivCurlWhole_mollify_divergence
    {V : Fin 3 → Vec3 → ℝ} {d : Vec3 → ℝ}
    (hVmem : ∀ i, MemLp (V i) 2 volume)
    (hdiv : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, ∑ i : Fin 3, V i x * spatialDeriv φ i x = -∫ x, d x * φ x)
    {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    (∑ i : Fin 3, spatialDeriv (fun y => CKN.mollify (V i) ε hε y) i x) =
      CKN.mollify d ε hε x := by
  let φ := localDivCurlWholeTestKernel ε hε x
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := localDivCurlWholeTestKernel_contDiff ε hε x
  have hφc : HasCompactSupport φ := localDivCurlWholeTestKernel_compact ε hε x
  have hφd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv φ i) := by
    simpa [φ, wordDeriv] using contDiff_wordDeriv hφ [i]
  have hφdc (i : Fin 3) : HasCompactSupport (spatialDeriv φ i) := by
    change HasCompactSupport (fun y => (fderiv ℝ φ y) (basisVec i))
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hφdmem (i : Fin 3) : MemLp (spatialDeriv φ i) 2 volume :=
    localDivCurlWhole_memLp_smooth_compact (hφd i) (hφdc i)
  have hkernelDerivMem (i : Fin 3) :
      MemLp (fun y => spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) 2 volume := by
    apply (memLp_congr_ae (ae_of_all _ fun y => ?_)).2 (hφdmem i).neg
    rw [show φ = localDivCurlWholeTestKernel ε hε x by rfl]
    change spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y) =
      -spatialDeriv (localDivCurlWholeTestKernel ε hε x) i y
    rw [localDivCurlWholeTestKernel_deriv ε hε x y i]
    simp
  have hkernelInt (i : Fin 3) : Integrable (fun y =>
      V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) volume :=
    (hVmem i).integrable_mul (hkernelDerivMem i)
  have htest := hdiv φ hφ hφc
  have htest' :
      (∫ y, ∑ i : Fin 3, V i y * spatialDeriv φ i y) =
        -(∫ y, ∑ i : Fin 3,
          V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) := by
    calc
      _ = ∫ y, -(∑ i : Fin 3,
            V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) := by
              apply integral_congr_ae
              filter_upwards [] with y
              rw [show φ = localDivCurlWholeTestKernel ε hε x by rfl]
              calc
                ∑ i : Fin 3, V i y * spatialDeriv
                    (localDivCurlWholeTestKernel ε hε x) i y =
                    ∑ i : Fin 3, -(V i y *
                      spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [localDivCurlWholeTestKernel_deriv ε hε x y i]
                    ring
                _ = -∑ i : Fin 3, V i y *
                    spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y) := by
                    rw [Finset.sum_neg_distrib]
      _ = _ := by rw [integral_neg]
  have hpair :
      (∫ y, ∑ i : Fin 3,
          V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) =
        ∫ y, d y * φ y := by
    exact neg_injective (htest'.symm.trans htest)
  calc
    _ = ∑ i : Fin 3, ∫ y,
          V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (serrin_mollify_spatialDeriv
              ((hVmem i).locallyIntegrable (by norm_num)) hε i x)
      _ = ∫ y, ∑ i : Fin 3,
          V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y) := by
            symm
            exact integral_finsetSum Finset.univ (fun i hi => hkernelInt i)
      _ = ∫ y, d y * φ y := hpair
      _ = CKN.mollify d ε hε x :=
            (localDivCurlWhole_mollify_eq_integral hε x).symm

private theorem localDivCurlWhole_mollify_curl
    {V ω : Fin 3 → Vec3 → ℝ}
    (hVmem : ∀ i, MemLp (V i) 2 volume)
    (hcurl : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ k : Fin 3,
      ∫ x, ω k x * φ x =
        ∫ x, (V (k + 1) x * spatialDeriv φ (k + 2) x -
          V (k + 2) x * spatialDeriv φ (k + 1) x))
    {ε : ℝ} (hε : 0 < ε) (k : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => CKN.mollify (V (k + 2)) ε hε y) (k + 1) x -
      spatialDeriv (fun y => CKN.mollify (V (k + 1)) ε hε y) (k + 2) x =
        CKN.mollify (ω k) ε hε x := by
  let φ := localDivCurlWholeTestKernel ε hε x
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := localDivCurlWholeTestKernel_contDiff ε hε x
  have hφc : HasCompactSupport φ := localDivCurlWholeTestKernel_compact ε hε x
  have hφd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv φ i) := by
    simpa [φ, wordDeriv] using contDiff_wordDeriv hφ [i]
  have hφdc (i : Fin 3) : HasCompactSupport (spatialDeriv φ i) := by
    change HasCompactSupport (fun y => (fderiv ℝ φ y) (basisVec i))
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hφdmem (i : Fin 3) : MemLp (spatialDeriv φ i) 2 volume :=
    localDivCurlWhole_memLp_smooth_compact (hφd i) (hφdc i)
  have hkernelDerivMem (i : Fin 3) :
      MemLp (fun y => spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y)) 2 volume := by
    apply (memLp_congr_ae (ae_of_all _ fun y => ?_)).2 (hφdmem i).neg
    rw [show φ = localDivCurlWholeTestKernel ε hε x by rfl]
    change spatialDeriv (CKN.mollifier (d := 3) ε hε) i (x - y) =
      -spatialDeriv (localDivCurlWholeTestKernel ε hε x) i y
    rw [localDivCurlWholeTestKernel_deriv ε hε x y i]
    simp
  have hkernelInt (i j : Fin 3) : Integrable (fun y =>
      V i y * spatialDeriv (CKN.mollifier (d := 3) ε hε) j (x - y)) volume :=
    (hVmem i).integrable_mul (hkernelDerivMem j)
  have htest := hcurl φ hφ hφc k
  have htest' :
      (∫ y, ω k y * φ y) =
        ∫ y, (V (k + 2) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
              (k + 1) (x - y) -
          V (k + 1) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
              (k + 2) (x - y)) := by
    calc
      _ = ∫ y, (V (k + 1) y * spatialDeriv φ (k + 2) y -
          V (k + 2) y * spatialDeriv φ (k + 1) y) := htest
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [show φ = localDivCurlWholeTestKernel ε hε x by rfl,
          localDivCurlWholeTestKernel_deriv ε hε x y (k + 2),
          localDivCurlWholeTestKernel_deriv ε hε x y (k + 1)]
        ring
  have htest'' :
      (∫ y, ω k y * φ y) =
        (∫ y, V (k + 2) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
            (k + 1) (x - y)) -
          ∫ y, V (k + 1) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
            (k + 2) (x - y) := by
    calc
      _ = ∫ y, (V (k + 2) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
            (k + 1) (x - y) -
          V (k + 1) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
            (k + 2) (x - y)) := htest'
      _ = _ := integral_sub (hkernelInt (k + 2) (k + 1))
        (hkernelInt (k + 1) (k + 2))
  calc
    _ = (∫ y, V (k + 2) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
            (k + 1) (x - y)) -
          ∫ y, V (k + 1) y * spatialDeriv (CKN.mollifier (d := 3) ε hε)
            (k + 2) (x - y) := by
          rw [serrin_mollify_spatialDeriv
            ((hVmem (k + 2)).locallyIntegrable (by norm_num)) hε (k + 1) x,
            serrin_mollify_spatialDeriv
            ((hVmem (k + 1)).locallyIntegrable (by norm_num)) hε (k + 2) x]
    _ = ∫ y, ω k y * φ y := by
          exact htest''.symm
    _ = CKN.mollify (ω k) ε hε x := by
          rw [localDivCurlWhole_mollify_eq_integral hε x]
          apply integral_congr_ae
          filter_upwards [] with y
          simp [φ, localDivCurlWholeTestKernel]

/-- Whole-space higher order div–curl regularity for compactly supported Sobolev families.
The divergence and curl are distributional, and the estimate has the constant from
`divCurl_smooth_whole`. -/
theorem divCurl_whole_family (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Fin 3 → Vec3 → ℝ) (DV : Fin 3 → List (Fin 3) → Vec3 → ℝ)
      (d : Vec3 → ℝ) (Dd : List (Fin 3) → Vec3 → ℝ)
      (ω : Fin 3 → Vec3 → ℝ) (Dω : Fin 3 → List (Fin 3) → Vec3 → ℝ) (K : Set Vec3),
      IsCompact K → (∀ i x, x ∉ K → V i x = 0) →
      (∀ i, IsSobolevFamilyOn m univ (V i) (DV i)) →
      IsSobolevFamilyOn m univ d Dd →
      (∀ k, IsSobolevFamilyOn m univ (ω k) (Dω k)) →
      (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, ∑ i : Fin 3, V i x * spatialDeriv φ i x = -∫ x, d x * φ x) →
      (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ k : Fin 3,
        ∫ x, ω k x * φ x =
          ∫ x, (V (k + 1) x * spatialDeriv φ (k + 2) x -
            V (k + 2) x * spatialDeriv φ (k + 1) x)) →
      ∃ DV' : Fin 3 → List (Fin 3) → Vec3 → ℝ,
        (∀ i, IsSobolevFamilyOn (m + 1) univ (V i) (DV' i)) ∧
        ∑ i, sobolevNormSqOn (m + 1) univ (DV' i) ≤
          C * (sobolevNormSqOn m univ Dd + ∑ k, sobolevNormSqOn m univ (Dω k) +
            ∑ i, sobolevNormSqOn m univ (DV i)) := by
  obtain ⟨C, hC, hSmooth⟩ := divCurl_smooth_whole m
  refine ⟨C, hC, ?_⟩
  intro V DV d Dd ω Dω K hK hVzero hV hD hω hdiv hcurl
  have hDVzero (i : Fin 3) : DV i [] =ᵐ[volume] V i := by
    simpa only [Measure.restrict_univ] using (hV i).zero
  have hDVmem0 (i : Fin 3) : MemLp (DV i []) 2 volume := by
    simpa only [Measure.restrict_univ] using (hV i).memL2 [] (by simp)
  have hVmem (i : Fin 3) : MemLp (V i) 2 volume :=
    MemLp.ae_eq (hDVzero i) (hDVmem0 i)
  have hDdmem (α : List (Fin 3)) (hα : α.length ≤ m) :
      MemLp (Dd α) 2 volume := by
    simpa only [Measure.restrict_univ] using hD.memL2 α hα
  have hDzero : Dd [] =ᵐ[volume] d := by
    simpa only [Measure.restrict_univ] using hD.zero
  have hdmem : MemLp d 2 volume := MemLp.ae_eq hDzero (hDdmem [] (by simp))
  have hωmem (k : Fin 3) : MemLp (ω k) 2 volume := by
    have hzero : Dω k [] =ᵐ[volume] ω k := by
      simpa only [Measure.restrict_univ] using (hω k).zero
    have hbase : MemLp (Dω k []) 2 volume := by
      simpa only [Measure.restrict_univ] using (hω k).memL2 [] (by simp)
    exact MemLp.ae_eq hzero hbase
  have hDωmem (k : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m) :
      MemLp (Dω k α) 2 volume := by
    simpa only [Measure.restrict_univ] using (hω k).memL2 α hα
  let W : ℕ → Fin 3 → Vec3 → ℝ := localDivCurlWholeApprox V
  have hWsm (n : ℕ) (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (W n i) := by
    exact localDivCurlWhole_approx_smooth hVmem n i
  have hWc (n : ℕ) (i : Fin 3) : HasCompactSupport (W n i) := by
    exact localDivCurlWhole_approx_compact hK hVzero n i
  have hWfamily (n : ℕ) (i : Fin 3) :
      IsSobolevFamilyOn (m + 1) univ (W n i)
        (fun α => wordDeriv α (W n i)) := by
    exact localDivCurlWhole_approx_family hVmem hK hVzero n i (m + 1)
  have hwordDerivSub (α : List (Fin 3)) {f g : Vec3 → ℝ}
      (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
      wordDeriv α (fun x => f x - g x) =
        fun x => wordDeriv α f x - wordDeriv α g x := by
    induction α generalizing f g with
    | nil => rfl
    | cons j α ih =>
        have hsub := localDivCurlWhole_spatialDeriv_sub hf hg j
        rw [wordDeriv, hsub]
        exact ih (contDiff_wordDeriv hf [j]) (contDiff_wordDeriv hg [j])
  have hdivPoint (n : ℕ) (x : Vec3) :
      (∑ i : Fin 3, spatialDeriv (W n i) i x) =
        CKN.mollify d (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n) x := by
    simpa [W, localDivCurlWholeApprox] using
      localDivCurlWhole_mollify_divergence hVmem hdiv
        (localDivCurlWholeRadius_pos n) x
  have hcurlPoint (n : ℕ) (k : Fin 3) (x : Vec3) :
      spatialDeriv (W n (k + 2)) (k + 1) x -
        spatialDeriv (W n (k + 1)) (k + 2) x =
          CKN.mollify (ω k) (localDivCurlWholeRadius n)
            (localDivCurlWholeRadius_pos n) x := by
    simpa [W, localDivCurlWholeApprox] using
      localDivCurlWhole_mollify_curl hVmem hcurl
        (localDivCurlWholeRadius_pos n) k x
  have hdivEq (n p : ℕ) :
      (fun x => ∑ i : Fin 3,
        spatialDeriv (fun y => W n i y - W p i y) i x) =
        (fun x => CKN.mollify d (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
          CKN.mollify d (localDivCurlWholeRadius p)
            (localDivCurlWholeRadius_pos p) x) := by
    funext x
    calc
      (∑ i : Fin 3, spatialDeriv (fun y => W n i y - W p i y) i x) =
          ∑ i : Fin 3, (spatialDeriv (W n i) i x - spatialDeriv (W p i) i x) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact congrFun (localDivCurlWhole_spatialDeriv_sub (hWsm n i) (hWsm p i) i) x
      _ = (∑ i : Fin 3, spatialDeriv (W n i) i x) -
          ∑ i : Fin 3, spatialDeriv (W p i) i x := by
            rw [Finset.sum_sub_distrib]
      _ = _ := by rw [hdivPoint n x, hdivPoint p x]
  have hcurlEq (n p : ℕ) (k : Fin 3) :
      (fun x => spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
        spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x) =
        (fun x => CKN.mollify (ω k) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
          CKN.mollify (ω k) (localDivCurlWholeRadius p)
            (localDivCurlWholeRadius_pos p) x) := by
    funext x
    rw [localDivCurlWhole_spatialDeriv_sub (hWsm n (k + 2)) (hWsm p (k + 2)) (k + 1),
      localDivCurlWhole_spatialDeriv_sub (hWsm n (k + 1)) (hWsm p (k + 1)) (k + 2)]
    have hn := hcurlPoint n k x
    have hp := hcurlPoint p k x
    linarith only [hn, hp]
  have hdivDeriv (α : List (Fin 3)) (hα : α.length ≤ m) (n p : ℕ) :
      wordDeriv α (fun x => ∑ i : Fin 3,
        spatialDeriv (fun y => W n i y - W p i y) i x) =
        (fun x => CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
          CKN.mollify (Dd α) (localDivCurlWholeRadius p)
            (localDivCurlWholeRadius_pos p) x) := by
    rw [hdivEq n p, hwordDerivSub α
      (localDivCurlWhole_mollify_smooth hdmem n)
      (localDivCurlWhole_mollify_smooth hdmem p)]
    funext x
    rw [localDivCurlWhole_mollify_wordDeriv hD
      (localDivCurlWholeRadius_pos n) α hα x,
      localDivCurlWhole_mollify_wordDeriv hD
        (localDivCurlWholeRadius_pos p) α hα x]
  have hcurlDeriv (k : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m)
      (n p : ℕ) :
      wordDeriv α (fun x =>
        spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
          spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x) =
        (fun x => CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
          CKN.mollify (Dω k α) (localDivCurlWholeRadius p)
            (localDivCurlWholeRadius_pos p) x) := by
    rw [hcurlEq n p k, hwordDerivSub α
      (localDivCurlWhole_mollify_smooth (hωmem k) n)
      (localDivCurlWhole_mollify_smooth (hωmem k) p)]
    funext x
    rw [localDivCurlWhole_mollify_wordDeriv (hω k)
      (localDivCurlWholeRadius_pos n) α hα x,
      localDivCurlWhole_mollify_wordDeriv (hω k)
        (localDivCurlWholeRadius_pos p) α hα x]
  have hbaseDeriv (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m)
      (n p : ℕ) :
      wordDeriv α (fun x => W n i x - W p i x) =
        (fun x => CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
          CKN.mollify (DV i α) (localDivCurlWholeRadius p)
            (localDivCurlWholeRadius_pos p) x) := by
    rw [hwordDerivSub α (hWsm n i) (hWsm p i)]
    funext x
    have hn := localDivCurlWhole_mollify_wordDeriv (hV i)
      (localDivCurlWholeRadius_pos n) α hα x
    have hp := localDivCurlWhole_mollify_wordDeriv (hV i)
      (localDivCurlWholeRadius_pos p) α hα x
    simpa [W, localDivCurlWholeApprox] using
      congrArg₂ (fun a b : ℝ => a - b) hn hp
  have hdivNormEq (n p : ℕ) :
      sobolevNormSqOn m univ (fun α => wordDeriv α (fun x => ∑ i : Fin 3,
        spatialDeriv (fun y => W n i y - W p i y) i x)) =
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
        CKN.mollify (Dd α) (localDivCurlWholeRadius p)
          (localDivCurlWholeRadius_pos p) x) := by
    apply localDivCurlWhole_normSq_congr
    intro α hα x
    exact congrFun (hdivDeriv α hα n p) x
  have hcurlNormEq (k : Fin 3) (n p : ℕ) :
      sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
        spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
          spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x)) =
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
        CKN.mollify (Dω k α) (localDivCurlWholeRadius p)
          (localDivCurlWholeRadius_pos p) x) := by
    apply localDivCurlWhole_normSq_congr
    intro α hα x
    exact congrFun (hcurlDeriv k α hα n p) x
  have hbaseNormEq (i : Fin 3) (n p : ℕ) :
      sobolevNormSqOn m univ (fun α => wordDeriv α (fun x => W n i x - W p i x)) =
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x -
        CKN.mollify (DV i α) (localDivCurlWholeRadius p)
          (localDivCurlWholeRadius_pos p) x) := by
    apply localDivCurlWhole_normSq_congr
    intro α hα x
    exact congrFun (hbaseDeriv i α hα n p) x
  let dataPair : ℕ × ℕ → ℝ := fun q =>
    sobolevNormSqOn m univ (fun α x =>
      CKN.mollify (Dd α) (localDivCurlWholeRadius q.1)
        (localDivCurlWholeRadius_pos q.1) x -
      CKN.mollify (Dd α) (localDivCurlWholeRadius q.2)
        (localDivCurlWholeRadius_pos q.2) x) +
    (∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
      CKN.mollify (Dω k α) (localDivCurlWholeRadius q.1)
        (localDivCurlWholeRadius_pos q.1) x -
      CKN.mollify (Dω k α) (localDivCurlWholeRadius q.2)
        (localDivCurlWholeRadius_pos q.2) x)) +
    ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
      CKN.mollify (DV i α) (localDivCurlWholeRadius q.1)
        (localDivCurlWholeRadius_pos q.1) x -
      CKN.mollify (DV i α) (localDivCurlWholeRadius q.2)
        (localDivCurlWholeRadius_pos q.2) x)
  have hDdPairSq (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun q : ℕ × ℕ => ∫ x,
        (CKN.mollify (Dd α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (Dd α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x) ^ 2 ∂volume)
        atTop (𝓝 0) := by
    let g : ℕ → Vec3 → ℝ := fun n => CKN.mollify (Dd α)
      (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n)
    have hg (n : ℕ) : MemLp (g n) 2 volume :=
      localDivCurlWhole_mollify_memLp (hDdmem α hα) n
    have hpairs := localDivCurlWhole_mollify_pair_tendsto (hDdmem α hα)
    have hsq := localDivCurlWhole_integral_sq_pair_tendsto_zero hg hpairs
    simpa [g] using hsq
  have hDωPairSq (k : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun q : ℕ × ℕ => ∫ x,
        (CKN.mollify (Dω k α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (Dω k α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x) ^ 2 ∂volume)
        atTop (𝓝 0) := by
    let g : ℕ → Vec3 → ℝ := fun n => CKN.mollify (Dω k α)
      (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n)
    have hg (n : ℕ) : MemLp (g n) 2 volume :=
      localDivCurlWhole_mollify_memLp (hDωmem k α hα) n
    have hpairs := localDivCurlWhole_mollify_pair_tendsto (hDωmem k α hα)
    have hsq := localDivCurlWhole_integral_sq_pair_tendsto_zero hg hpairs
    simpa [g] using hsq
  have hDVPairSq (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun q : ℕ × ℕ => ∫ x,
        (CKN.mollify (DV i α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (DV i α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x) ^ 2 ∂volume)
        atTop (𝓝 0) := by
    have hmem : MemLp (DV i α) 2 volume := by
      simpa only [Measure.restrict_univ] using (hV i).memL2 α hα
    let g : ℕ → Vec3 → ℝ := fun n => CKN.mollify (DV i α)
      (localDivCurlWholeRadius n) (localDivCurlWholeRadius_pos n)
    have hg (n : ℕ) : MemLp (g n) 2 volume :=
      localDivCurlWhole_mollify_memLp hmem n
    have hpairs := localDivCurlWhole_mollify_pair_tendsto hmem
    have hsq := localDivCurlWhole_integral_sq_pair_tendsto_zero hg hpairs
    simpa [g] using hsq
  have hDdPairNorm : Tendsto (fun q : ℕ × ℕ =>
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dd α) (localDivCurlWholeRadius q.1)
          (localDivCurlWholeRadius_pos q.1) x -
        CKN.mollify (Dd α) (localDivCurlWholeRadius q.2)
          (localDivCurlWholeRadius_pos q.2) x)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun q : ℕ × ℕ => ∑ α ∈ sobolevWords m, ∫ x,
        (CKN.mollify (Dd α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (Dd α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x) ^ 2 ∂volume)
        atTop (𝓝 (∑ α ∈ sobolevWords m, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro α hα
      exact hDdPairSq α (mem_sobolevWords.mp hα)
    simpa [sobolevNormSqOn] using hsum
  have hDωPairNorm (k : Fin 3) : Tendsto (fun q : ℕ × ℕ =>
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dω k α) (localDivCurlWholeRadius q.1)
          (localDivCurlWholeRadius_pos q.1) x -
        CKN.mollify (Dω k α) (localDivCurlWholeRadius q.2)
          (localDivCurlWholeRadius_pos q.2) x)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun q : ℕ × ℕ => ∑ α ∈ sobolevWords m, ∫ x,
        (CKN.mollify (Dω k α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (Dω k α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x) ^ 2 ∂volume)
        atTop (𝓝 (∑ α ∈ sobolevWords m, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro α hα
      exact hDωPairSq k α (mem_sobolevWords.mp hα)
    simpa [sobolevNormSqOn] using hsum
  have hDVPairNorm (i : Fin 3) : Tendsto (fun q : ℕ × ℕ =>
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (DV i α) (localDivCurlWholeRadius q.1)
          (localDivCurlWholeRadius_pos q.1) x -
        CKN.mollify (DV i α) (localDivCurlWholeRadius q.2)
          (localDivCurlWholeRadius_pos q.2) x)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun q : ℕ × ℕ => ∑ α ∈ sobolevWords m, ∫ x,
        (CKN.mollify (DV i α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (DV i α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x) ^ 2 ∂volume)
        atTop (𝓝 (∑ α ∈ sobolevWords m, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro α hα
      exact hDVPairSq i α (mem_sobolevWords.mp hα)
    simpa [sobolevNormSqOn] using hsum
  have hDataPair : Tendsto dataPair atTop (𝓝 0) := by
    have hωsum : Tendsto (fun q : ℕ × ℕ => ∑ k : Fin 3,
        sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (Dω k α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (Dω k α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x)) atTop (𝓝 0) := by
      have hsum : Tendsto (fun q : ℕ × ℕ => ∑ k : Fin 3,
          sobolevNormSqOn m univ (fun α x =>
            CKN.mollify (Dω k α) (localDivCurlWholeRadius q.1)
              (localDivCurlWholeRadius_pos q.1) x -
            CKN.mollify (Dω k α) (localDivCurlWholeRadius q.2)
              (localDivCurlWholeRadius_pos q.2) x)) atTop
          (𝓝 (∑ k : Fin 3, (0 : ℝ))) := by
        apply tendsto_finsetSum
        intro k hk
        exact hDωPairNorm k
      simpa using hsum
    have hVsum : Tendsto (fun q : ℕ × ℕ => ∑ i : Fin 3,
        sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (DV i α) (localDivCurlWholeRadius q.1)
            (localDivCurlWholeRadius_pos q.1) x -
          CKN.mollify (DV i α) (localDivCurlWholeRadius q.2)
            (localDivCurlWholeRadius_pos q.2) x)) atTop (𝓝 0) := by
      have hsum : Tendsto (fun q : ℕ × ℕ => ∑ i : Fin 3,
          sobolevNormSqOn m univ (fun α x =>
            CKN.mollify (DV i α) (localDivCurlWholeRadius q.1)
              (localDivCurlWholeRadius_pos q.1) x -
            CKN.mollify (DV i α) (localDivCurlWholeRadius q.2)
              (localDivCurlWholeRadius_pos q.2) x)) atTop
          (𝓝 (∑ i : Fin 3, (0 : ℝ))) := by
        apply tendsto_finsetSum
        intro i hi
        exact hDVPairNorm i
      simpa using hsum
    have hadd := hDdPairNorm.add (hωsum.add hVsum)
    simpa [dataPair, add_assoc] using hadd
  have hEstimate (n p : ℕ) :
      (∑ i : Fin 3, sobolevNormSqOn (m + 1) univ
        (fun α => wordDeriv α (fun x => W n i x - W p i x))) ≤ C * dataPair (n, p) := by
    have hSmoothBound := hSmooth
      (fun i x => W n i x - W p i x)
      (fun i => (hWsm n i).sub (hWsm p i))
      (fun i => (hWc n i).sub (hWc p i))
    have hRhsEq :
        (sobolevNormSqOn m univ (fun α => wordDeriv α (fun x => ∑ i : Fin 3,
          spatialDeriv (fun y => W n i y - W p i y) i x)) +
        ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
          spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
            spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (fun x => W n i x - W p i x))) = dataPair (n, p) := by
      dsimp [dataPair]
      have hcurlSum :
          (∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
            spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
              spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x))) =
          ∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
            CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
              (localDivCurlWholeRadius_pos n) x -
            CKN.mollify (Dω k α) (localDivCurlWholeRadius p)
              (localDivCurlWholeRadius_pos p) x) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcurlNormEq k n p
      have hbaseSum :
          (∑ i : Fin 3, sobolevNormSqOn m univ
            (fun α => wordDeriv α (fun x => W n i x - W p i x))) =
          ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
            CKN.mollify (DV i α) (localDivCurlWholeRadius n)
              (localDivCurlWholeRadius_pos n) x -
            CKN.mollify (DV i α) (localDivCurlWholeRadius p)
              (localDivCurlWholeRadius_pos p) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hbaseNormEq i n p
      calc
        _ = (sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
              ∑ i : Fin 3, spatialDeriv (fun y => W n i y - W p i y) i x)) +
            ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
              spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
                spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x))) +
            ∑ i : Fin 3, sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x => W n i x - W p i x)) := rfl
        _ = (sobolevNormSqOn m univ (fun α x =>
              CKN.mollify (Dd α) (localDivCurlWholeRadius n)
                (localDivCurlWholeRadius_pos n) x -
              CKN.mollify (Dd α) (localDivCurlWholeRadius p)
                (localDivCurlWholeRadius_pos p) x) +
            ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
              spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
                spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x))) +
            ∑ i : Fin 3, sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x => W n i x - W p i x)) := by
                rw [hdivNormEq n p]
        _ = (sobolevNormSqOn m univ (fun α x =>
              CKN.mollify (Dd α) (localDivCurlWholeRadius n)
                (localDivCurlWholeRadius_pos n) x -
              CKN.mollify (Dd α) (localDivCurlWholeRadius p)
                (localDivCurlWholeRadius_pos p) x) +
            ∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
              CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
                (localDivCurlWholeRadius_pos n) x -
              CKN.mollify (Dω k α) (localDivCurlWholeRadius p)
                (localDivCurlWholeRadius_pos p) x)) +
            ∑ i : Fin 3, sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x => W n i x - W p i x)) := by
                rw [hcurlSum]
        _ = dataPair (n, p) := by rw [hbaseSum]
    calc
      _ ≤ C * (sobolevNormSqOn m univ (fun α => wordDeriv α (fun x => ∑ i : Fin 3,
          spatialDeriv (fun y => W n i y - W p i y) i x)) +
        ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
          spatialDeriv (fun y => W n (k + 2) y - W p (k + 2) y) (k + 1) x -
            spatialDeriv (fun y => W n (k + 1) y - W p (k + 1) y) (k + 2) x)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (fun x => W n i x - W p i x))) := hSmoothBound
      _ = C * dataPair (n, p) := congrArg (fun r : ℝ => C * r) hRhsEq
  have hEstimateLimit : Tendsto (fun q : ℕ × ℕ => C * dataPair q) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hDataPair
  have hHighPairSq (i : Fin 3) (α : List (Fin 3))
      (hα : α.length ≤ m + 1) :
      Tendsto (fun q : ℕ × ℕ => ∫ x,
        (wordDeriv α (W q.1 i) x - wordDeriv α (W q.2 i) x) ^ 2 ∂volume)
        atTop (𝓝 0) := by
    let g : ℕ → Vec3 → ℝ := fun n => wordDeriv α (W n i)
    have hmem (n : ℕ) : MemLp (g n) 2 volume := by
      simpa only [Measure.restrict_univ] using (hWfamily n i).memL2 α hα
    have hterm (q : ℕ × ℕ) :
        ∫ x, (g q.1 x - g q.2 x) ^ 2 ∂volume ≤ C * dataPair q := by
      have hterm' :
          ∫ x, wordDeriv α (fun x => W q.1 i x - W q.2 i x) x ^ 2 ∂volume ≤
            ∑ j : Fin 3, sobolevNormSqOn (m + 1) univ
              (fun β => wordDeriv β (fun x => W q.1 j x - W q.2 j x)) := by
        have hsingle :
            ∫ x, wordDeriv α (fun x => W q.1 i x - W q.2 i x) x ^ 2 ∂volume ≤
              ∑ β ∈ sobolevWords (m + 1),
                ∫ x, wordDeriv β (fun x => W q.1 i x - W q.2 i x) x ^ 2 ∂volume := by
          apply Finset.single_le_sum (s := sobolevWords (m + 1))
            (f := fun β => ∫ x,
              wordDeriv β (fun x => W q.1 i x - W q.2 i x) x ^ 2 ∂volume)
          · intro β hβ
            exact integral_nonneg fun x => sq_nonneg _
          · exact mem_sobolevWords.mpr hα
        have hin :
            ∫ x, wordDeriv α (fun x => W q.1 i x - W q.2 i x) x ^ 2 ∂volume ≤
              sobolevNormSqOn (m + 1) univ
                (fun β => wordDeriv β (fun x => W q.1 i x - W q.2 i x)) := by
          simpa [sobolevNormSqOn] using hsingle
        have hout : sobolevNormSqOn (m + 1) univ
              (fun β => wordDeriv β (fun x => W q.1 i x - W q.2 i x)) ≤
              ∑ j : Fin 3, sobolevNormSqOn (m + 1) univ
                (fun β => wordDeriv β (fun x => W q.1 j x - W q.2 j x)) := by
          apply Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin 3 => sobolevNormSqOn (m + 1) univ
              (fun β => wordDeriv β (fun x => W q.1 j x - W q.2 j x)))
          · intro j hj
            exact localDivCurlWhole_normSq_nonneg (m + 1) univ
              (fun β => wordDeriv β (fun x => W q.1 j x - W q.2 j x))
          · exact Finset.mem_univ i
        exact hin.trans hout
      calc
        _ = ∫ x, wordDeriv α (fun x => W q.1 i x - W q.2 i x) x ^ 2 ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hwordDerivSub α (hWsm q.1 i) (hWsm q.2 i)]
        _ ≤ ∑ j : Fin 3, sobolevNormSqOn (m + 1) univ
            (fun β => wordDeriv β (fun x => W q.1 j x - W q.2 j x)) := hterm'
        _ ≤ C * dataPair q := hEstimate q.1 q.2
    have hsq := tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hEstimateLimit
      (fun q => integral_nonneg fun x => sq_nonneg (g q.1 x - g q.2 x)) hterm
    have hpair : Tendsto (fun q : ℕ × ℕ =>
        ∫ x, (g q.1 x - g q.2 x) ^ 2 ∂volume) atTop (𝓝 0) := hsq
    simpa [g] using hpair
  have hHighPairNorm (i : Fin 3) (α : List (Fin 3))
      (hα : α.length ≤ m + 1) :
      Tendsto (fun q : ℕ × ℕ =>
        eLpNorm (wordDeriv α (W q.1 i) - wordDeriv α (W q.2 i)) 2 volume)
        atTop (𝓝 0) := by
    have hmemPair (q : ℕ × ℕ) :
        MemLp (fun x => wordDeriv α (W q.1 i) x - wordDeriv α (W q.2 i) x) 2 volume :=
      have hq1 : MemLp (wordDeriv α (W q.1 i)) 2 volume := by
        simpa only [Measure.restrict_univ] using (hWfamily q.1 i).memL2 α hα
      have hq2 : MemLp (wordDeriv α (W q.2 i)) 2 volume := by
        simpa only [Measure.restrict_univ] using (hWfamily q.2 i).memL2 α hα
      hq1.sub hq2
    exact localDivCurlWhole_eLpNorm_tendsto_zero_of_integral_sq hmemPair
      (hHighPairSq i α hα)
  let L : (i : Fin 3) → (α : List (Fin 3)) → α.length ≤ m + 1 → Vec3 → ℝ :=
    fun i α hα => Classical.choose
      (localDivCurlWhole_l2_exists_limit (f := fun n => wordDeriv α (W n i))
        (fun n => by
          simpa only [Measure.restrict_univ] using (hWfamily n i).memL2 α hα)
        (hHighPairNorm i α hα))
  have hLspec (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m + 1) :
      MemLp (L i α hα) 2 volume ∧
        Tendsto (fun n => eLpNorm (wordDeriv α (W n i) - L i α hα) 2 volume)
          atTop (𝓝 0) := by
    exact Classical.choose_spec
      (localDivCurlWhole_l2_exists_limit (f := fun n => wordDeriv α (W n i))
        (fun n => by
          simpa only [Measure.restrict_univ] using (hWfamily n i).memL2 α hα)
        (hHighPairNorm i α hα))
  let DV' : Fin 3 → List (Fin 3) → Vec3 → ℝ := fun i α =>
    if hnil : α = [] then V i else
      if hα : α.length ≤ m + 1 then L i α hα else 0
  have hDV'mem (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m + 1) :
      MemLp (DV' i α) 2 volume := by
    by_cases hnil : α = []
    · subst α
      simpa [DV'] using hVmem i
    · simpa [DV', hnil, hα] using (hLspec i α hα).1
  have hDV'conv (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m + 1) :
      Tendsto (fun n => eLpNorm (wordDeriv α (W n i) - DV' i α) 2 volume)
        atTop (𝓝 0) := by
    by_cases hnil : α = []
    · subst α
      change Tendsto (fun n => eLpNorm
        (CKN.mollify (V i) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) - V i) 2 volume) atTop (𝓝 0)
      exact localDivCurlWhole_mollify_tendsto (hVmem i)
    · simpa [DV', hnil, hα] using (hLspec i α hα).2
  have hOut (i : Fin 3) : IsSobolevFamilyOn (m + 1) univ (V i) (DV' i) := by
    apply IsSobolevFamilyOn.of_tendsto isOpen_univ
      (Dn := fun n α => wordDeriv α (W n i)) (D := fun α => DV' i α)
    · intro n
      exact hWfamily n i
    · intro α hα
      simpa only [Measure.restrict_univ] using hDV'mem i α hα
    · intro α hα
      simpa only [Measure.restrict_univ] using hDV'conv i α hα
  have hdivOne (n : ℕ) :
      (fun x => ∑ i : Fin 3, spatialDeriv (W n i) i x) =
        (fun x => CKN.mollify d (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    funext x
    exact hdivPoint n x
  have hcurlOne (n : ℕ) (k : Fin 3) :
      (fun x => spatialDeriv (W n (k + 2)) (k + 1) x -
        spatialDeriv (W n (k + 1)) (k + 2) x) =
        (fun x => CKN.mollify (ω k) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    funext x
    exact hcurlPoint n k x
  have hdivOneDeriv (n : ℕ) (α : List (Fin 3)) (hα : α.length ≤ m) :
      wordDeriv α (fun x => ∑ i : Fin 3, spatialDeriv (W n i) i x) =
        (fun x => CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    rw [show wordDeriv α (fun x => ∑ i : Fin 3, spatialDeriv (W n i) i x) =
      wordDeriv α (fun x => CKN.mollify d (localDivCurlWholeRadius n)
        (localDivCurlWholeRadius_pos n) x) by
          exact congrArg (wordDeriv α) (hdivOne n)]
    funext x
    exact localDivCurlWhole_mollify_wordDeriv hD
      (localDivCurlWholeRadius_pos n) α hα x
  have hcurlOneDeriv (n : ℕ) (k : Fin 3) (α : List (Fin 3))
      (hα : α.length ≤ m) :
      wordDeriv α (fun x => spatialDeriv (W n (k + 2)) (k + 1) x -
        spatialDeriv (W n (k + 1)) (k + 2) x) =
        (fun x => CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    rw [show wordDeriv α (fun x => spatialDeriv (W n (k + 2)) (k + 1) x -
        spatialDeriv (W n (k + 1)) (k + 2) x) =
      wordDeriv α (fun x => CKN.mollify (ω k) (localDivCurlWholeRadius n)
        (localDivCurlWholeRadius_pos n) x) by
          exact congrArg (wordDeriv α) (hcurlOne n k)]
    funext x
    exact localDivCurlWhole_mollify_wordDeriv (hω k)
      (localDivCurlWholeRadius_pos n) α hα x
  have hbaseOneDeriv (n : ℕ) (i : Fin 3) (α : List (Fin 3))
      (hα : α.length ≤ m) :
      wordDeriv α (W n i) =
        (fun x => CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    funext x
    exact localDivCurlWhole_mollify_wordDeriv (hV i)
      (localDivCurlWholeRadius_pos n) α hα x
  have hdivNormEqOne (n : ℕ) :
      sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
        ∑ i : Fin 3, spatialDeriv (W n i) i x)) =
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    apply localDivCurlWhole_normSq_congr
    intro α hα x
    exact congrFun (hdivOneDeriv n α hα) x
  have hcurlNormEqOne (n : ℕ) (k : Fin 3) :
      sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
        spatialDeriv (W n (k + 2)) (k + 1) x -
          spatialDeriv (W n (k + 1)) (k + 2) x)) =
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    apply localDivCurlWhole_normSq_congr
    intro α hα x
    exact congrFun (hcurlOneDeriv n k α hα) x
  have hbaseNormEqOne (n : ℕ) (i : Fin 3) :
      sobolevNormSqOn m univ (fun α => wordDeriv α (W n i)) =
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) := by
    apply localDivCurlWhole_normSq_congr
    intro α hα x
    exact congrFun (hbaseOneDeriv n i α hα) x
  have hSmoothEstimate (n : ℕ) :
      (∑ i : Fin 3, sobolevNormSqOn (m + 1) univ
        (fun α => wordDeriv α (W n i))) ≤
      C * (sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) +
        (∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
            (localDivCurlWholeRadius_pos n) x)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (DV i α) (localDivCurlWholeRadius n)
            (localDivCurlWholeRadius_pos n) x)) := by
    have hSmoothBound := hSmooth (W n) (hWsm n) (hWc n)
    have hEq :
        (sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
          ∑ i : Fin 3, spatialDeriv (W n i) i x)) +
        ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
          spatialDeriv (W n (k + 2)) (k + 1) x -
            spatialDeriv (W n (k + 1)) (k + 2) x)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (W n i))) =
        (sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (Dd α) (localDivCurlWholeRadius n)
            (localDivCurlWholeRadius_pos n) x) +
        ∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
            (localDivCurlWholeRadius_pos n) x) +
        ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
          CKN.mollify (DV i α) (localDivCurlWholeRadius n)
            (localDivCurlWholeRadius_pos n) x)) := by
      have hcurlSum :
          (∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
            spatialDeriv (W n (k + 2)) (k + 1) x -
              spatialDeriv (W n (k + 1)) (k + 2) x))) =
          ∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
            CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
              (localDivCurlWholeRadius_pos n) x) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcurlNormEqOne n k
      have hbaseSum :
          (∑ i : Fin 3, sobolevNormSqOn m univ
            (fun α => wordDeriv α (W n i))) =
          ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
            CKN.mollify (DV i α) (localDivCurlWholeRadius n)
              (localDivCurlWholeRadius_pos n) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hbaseNormEqOne n i
      calc
        _ = (sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
              ∑ i : Fin 3, spatialDeriv (W n i) i x)) +
            ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
              spatialDeriv (W n (k + 2)) (k + 1) x -
                spatialDeriv (W n (k + 1)) (k + 2) x))) +
            ∑ i : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (W n i)) := rfl
        _ = (sobolevNormSqOn m univ (fun α x =>
              CKN.mollify (Dd α) (localDivCurlWholeRadius n)
                (localDivCurlWholeRadius_pos n) x) +
            ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
              spatialDeriv (W n (k + 2)) (k + 1) x -
                spatialDeriv (W n (k + 1)) (k + 2) x))) +
            ∑ i : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (W n i)) := by
                rw [hdivNormEqOne n]
        _ = (sobolevNormSqOn m univ (fun α x =>
              CKN.mollify (Dd α) (localDivCurlWholeRadius n)
                (localDivCurlWholeRadius_pos n) x) +
            ∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
              CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
                (localDivCurlWholeRadius_pos n) x)) +
            ∑ i : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (W n i)) := by
                rw [hcurlSum]
        _ = _ := by rw [hbaseSum]
    calc
      _ ≤ C * (sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
          ∑ i : Fin 3, spatialDeriv (W n i) i x)) +
        ∑ k : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (fun x =>
          spatialDeriv (W n (k + 2)) (k + 1) x -
            spatialDeriv (W n (k + 1)) (k + 2) x)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (W n i))) := hSmoothBound
      _ = _ := congrArg (fun r : ℝ => C * r) hEq


  have hDdNormLimit : Tendsto (fun n => sobolevNormSqOn m univ
      (fun α x => CKN.mollify (Dd α) (localDivCurlWholeRadius n)
        (localDivCurlWholeRadius_pos n) x)) atTop
      (𝓝 (sobolevNormSqOn m univ Dd)) := by
    have hsum : Tendsto (fun n => ∑ α ∈ sobolevWords m, ∫ x,
        (CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) ^ 2 ∂volume) atTop
        (𝓝 (∑ α ∈ sobolevWords m, ∫ x, Dd α x ^ 2 ∂volume)) := by
      apply tendsto_finsetSum
      intro α hα
      have hmem := hDdmem α (mem_sobolevWords.mp hα)
      exact localDivCurlWhole_integral_sq_tendsto
        (fun n => localDivCurlWhole_mollify_memLp hmem n) hmem
        (localDivCurlWhole_mollify_tendsto hmem)
    simpa [sobolevNormSqOn] using hsum
  have hDωNormLimit (k : Fin 3) : Tendsto (fun n => sobolevNormSqOn m univ
      (fun α x => CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
        (localDivCurlWholeRadius_pos n) x)) atTop
      (𝓝 (sobolevNormSqOn m univ (Dω k))) := by
    have hsum : Tendsto (fun n => ∑ α ∈ sobolevWords m, ∫ x,
        (CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) ^ 2 ∂volume) atTop
        (𝓝 (∑ α ∈ sobolevWords m, ∫ x, Dω k α x ^ 2 ∂volume)) := by
      apply tendsto_finsetSum
      intro α hα
      have hmem := hDωmem k α (mem_sobolevWords.mp hα)
      exact localDivCurlWhole_integral_sq_tendsto
        (fun n => localDivCurlWhole_mollify_memLp hmem n) hmem
        (localDivCurlWhole_mollify_tendsto hmem)
    simpa [sobolevNormSqOn] using hsum
  have hDVNormLimit (i : Fin 3) : Tendsto (fun n => sobolevNormSqOn (m + 1) univ
      (fun α => wordDeriv α (W n i))) atTop
      (𝓝 (sobolevNormSqOn (m + 1) univ (DV' i))) := by
    have hsum : Tendsto (fun n => ∑ α ∈ sobolevWords (m + 1), ∫ x,
        wordDeriv α (W n i) x ^ 2 ∂volume) atTop
        (𝓝 (∑ α ∈ sobolevWords (m + 1), ∫ x, DV' i α x ^ 2 ∂volume)) := by
      apply tendsto_finsetSum
      intro α hα
      exact localDivCurlWhole_integral_sq_tendsto
        (fun n => by
          simpa only [Measure.restrict_univ] using (hWfamily n i).memL2 α
            (mem_sobolevWords.mp hα))
        (hDV'mem i α (mem_sobolevWords.mp hα))
        (hDV'conv i α (mem_sobolevWords.mp hα))
    simpa [sobolevNormSqOn] using hsum
  have hLeftLimit : Tendsto (fun n => ∑ i : Fin 3,
      sobolevNormSqOn (m + 1) univ (fun α => wordDeriv α (W n i))) atTop
      (𝓝 (∑ i : Fin 3, sobolevNormSqOn (m + 1) univ (DV' i))) := by
    apply tendsto_finsetSum
    intro i hi
    exact hDVNormLimit i
  have hωsum : Tendsto (fun n => ∑ k : Fin 3,
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x)) atTop
      (𝓝 (∑ k : Fin 3, sobolevNormSqOn m univ (Dω k))) := by
    apply tendsto_finsetSum
    intro k hk
    exact hDωNormLimit k
  have hVsum : Tendsto (fun n => ∑ i : Fin 3,
      sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x)) atTop
      (𝓝 (∑ i : Fin 3, sobolevNormSqOn m univ (DV i))) := by
    apply tendsto_finsetSum
    intro i hi
    have hsum : Tendsto (fun n => ∑ α ∈ sobolevWords m, ∫ x,
        (CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) ^ 2 ∂volume) atTop
        (𝓝 (∑ α ∈ sobolevWords m, ∫ x, DV i α x ^ 2 ∂volume)) := by
      apply tendsto_finsetSum
      intro α hα
      have hmem : MemLp (DV i α) 2 volume := by
        simpa only [Measure.restrict_univ] using (hV i).memL2 α
          (mem_sobolevWords.mp hα)
      exact localDivCurlWhole_integral_sq_tendsto
        (fun n => localDivCurlWhole_mollify_memLp hmem n) hmem
        (localDivCurlWhole_mollify_tendsto hmem)
    simpa [sobolevNormSqOn] using hsum
  have hDataLimit : Tendsto (fun n =>
      (sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) +
      (∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x)) +
      ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x))) atTop
      (𝓝 (sobolevNormSqOn m univ Dd +
        (∑ k : Fin 3, sobolevNormSqOn m univ (Dω k)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ (DV i))) := by
    have hadd := hDdNormLimit.add (hωsum.add hVsum)
    simpa only [add_assoc] using hadd
  have hRightLimit : Tendsto (fun n => C *
      (sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dd α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x) +
      (∑ k : Fin 3, sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (Dω k α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x)) +
      ∑ i : Fin 3, sobolevNormSqOn m univ (fun α x =>
        CKN.mollify (DV i α) (localDivCurlWholeRadius n)
          (localDivCurlWholeRadius_pos n) x))) atTop
      (𝓝 (C * (sobolevNormSqOn m univ Dd +
        (∑ k : Fin 3, sobolevNormSqOn m univ (Dω k)) +
        ∑ i : Fin 3, sobolevNormSqOn m univ (DV i)))) := by
    simpa using tendsto_const_nhds.mul hDataLimit
  refine ⟨DV', ?_, ?_⟩
  · exact hOut
  · exact le_of_tendsto_of_tendsto hLeftLimit hRightLimit
      (Filter.Eventually.of_forall hSmoothEstimate)


end ESS
