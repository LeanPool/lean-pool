/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressurePotentialDecayBase

/-!
# Potential decay estimates

Far-field derivative bounds and the resulting decay of the scalar potential.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

private theorem associatedPressureNewtonianPotential_iteratedFDeriv_far_bound
    {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (k : ℕ) :
    ∃ R ≥ 1, ∃ M ≥ 0, ∃ c ≥ 0, ∀ t x,
      4 * R < vec3EuclideanNorm x →
        ‖iteratedFDeriv ℝ k
          (CKN.pressureNewtonianPotential (fun y => g (y, t))) x‖ ≤
          c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := by
  let K : Set Vec3 := (tsupport g).image Prod.fst
  have hproj : Continuous (fun z : Vec3 × ℝ => z.1) := continuous_fst
  have hK : IsCompact K := hgc.isCompact.image hproj
  have hNormImage : BddAbove (vec3EuclideanNorm '' K) :=
    hK.bddAbove_image CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn
  obtain ⟨B, hB⟩ := hNormImage
  let R : ℝ := max 1 B
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  obtain ⟨M, hM, hmass⟩ := associatedPressurePotentialSource_slice_integral_bound hg hgc
  obtain ⟨c, hc, hfar⟩ :=
    CKN.Foundation.Heat.exists_norm_iteratedFDeriv_pressureNewtonianPotential_le k
  refine ⟨R, hR, M, hM, c, hc, ?_⟩
  intro t x hx
  let U : Set Vec3 := Metric.ball x (vec3EuclideanNorm x / 16)
  have hU : IsOpen U := Metric.isOpen_ball
  have hxnorm : 0 < vec3EuclideanNorm x := lt_trans (by positivity) hx
  have hxU : x ∈ U := by
    change dist x x < vec3EuclideanNorm x / 16
    simpa only [dist_self] using div_pos hxnorm (by norm_num)
  have hsourceZero : ∀ y ∉ K, g (y, t) = 0 := by
    intro y hy
    have hnot : (y, t) ∉ tsupport g := by
      intro hmem
      exact hy ⟨(y, t), hmem, rfl⟩
    exact image_eq_zero_of_notMem_tsupport hnot
  have hsourceCompact : HasCompactSupport (fun y : Vec3 => g (y, t)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro y hy
    exact ⟨(y, t), subset_tsupport (f := g)
      (Function.mem_support.mpr (by simpa using hy)), rfl⟩
  have hsourceInt : Integrable (fun y : Vec3 => g (y, t)) volume :=
    (hg.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      hsourceCompact
  have hsep : ∀ y ∈ U, ∀ z ∈ K,
      vec3EuclideanNorm x / 2 ≤ vec3EuclideanNorm (y - z) := by
    intro y hy z hz
    have hdist : ‖y - x‖ < vec3EuclideanNorm x / 16 := by
      simpa [U, dist_eq_norm] using hy
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hnear : vec3EuclideanNorm (y - x) < vec3EuclideanNorm x / 8 := by
      have hnorm :=
        CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm (y - x)
      have hmul : Real.sqrt 3 * ‖y - x‖ ≤ 2 * ‖y - x‖ :=
        mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
      linarith only [hdist, hnorm, hmul]
    have hlarge : 3 * vec3EuclideanNorm x / 4 ≤ vec3EuclideanNorm y := by
      have htriangle : vec3EuclideanNorm x ≤
          vec3EuclideanNorm y + vec3EuclideanNorm (x - y) := by
        calc
        vec3EuclideanNorm x = vec3EuclideanNorm (y + (x - y)) := by
            congr 1
            abel
          _ ≤ vec3EuclideanNorm y + vec3EuclideanNorm (x - y) :=
            CKN.Foundation.Parabolic.vec3EuclideanNorm_add_le _ _
      rw [show vec3EuclideanNorm (x - y) = vec3EuclideanNorm (y - x) by
        rw [show x - y = -(y - x) by abel,
          CKN.Foundation.Parabolic.vec3EuclideanNorm_neg]] at htriangle
      linarith only [htriangle, hnear, hxnorm]
    have hsmall : vec3EuclideanNorm z ≤ R :=
      (hB ⟨z, hz, rfl⟩).trans (le_max_right _ _)
    have htriangle : vec3EuclideanNorm y ≤
        vec3EuclideanNorm (y - z) + vec3EuclideanNorm z := by
      calc
        vec3EuclideanNorm y = vec3EuclideanNorm ((y - z) + z) := by
          congr 1
          abel
        _ ≤ vec3EuclideanNorm (y - z) + vec3EuclideanNorm z :=
          CKN.Foundation.Parabolic.vec3EuclideanNorm_add_le _ _
    have hRsmall : R ≤ vec3EuclideanNorm x / 4 := by linarith only [hx]
    nlinarith only [hlarge, hsmall, htriangle, hRsmall]
  have hdelta : 0 < vec3EuclideanNorm x / 2 := by
    have hxlarge : 0 < vec3EuclideanNorm x := lt_trans (by positivity) hx
    exact half_pos hxlarge
  have hbound := hfar (fun y : Vec3 => g (y, t)) hsourceInt K U hU
    hsourceZero (vec3EuclideanNorm x / 2) hdelta hsep x hxU
  have hmass' : (∫ y : Vec3, |g (y, t)|) ≤ M := hmass t
  have hle : c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ *
      (∫ y : Vec3, |g (y, t)|) ≤
      c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := by
    have hfactor : 0 ≤ c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ := by
      positivity
    exact mul_le_mul_of_nonneg_left hmass' hfactor
  exact hbound.trans hle

private theorem associatedPressureNewtonianPotential_iteratedFDeriv_far_decay
    {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (k : ℕ) :
    ∃ R ≥ 1, ∃ C ≥ 0, ∀ t x,
      4 * R < vec3EuclideanNorm x →
        ‖iteratedFDeriv ℝ k
          (CKN.pressureNewtonianPotential (fun y => g (y, t))) x‖ ≤
          C * (1 + vec3EuclideanNorm x) ^ (-(1 + k : ℝ)) := by
  obtain ⟨R, hR, M, hM, c, hc, hfar⟩ :=
    associatedPressureNewtonianPotential_iteratedFDeriv_far_bound hg hgc k
  let n : ℕ := 1 + k
  let C : ℝ := c * M * 4 ^ n
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hc hM) (by positivity)
  refine ⟨R, hR, C, hC, ?_⟩
  intro t x hx
  have hxnorm : 0 < vec3EuclideanNorm x := lt_trans (by positivity) hx
  have hr : 1 < vec3EuclideanNorm x := by
    nlinarith only [hR, hx]
  have hbase : 0 < 1 + vec3EuclideanNorm x := by positivity
  have htwor : 0 < 2 * vec3EuclideanNorm x := by positivity
  have hleBase : 1 + vec3EuclideanNorm x ≤ 2 * vec3EuclideanNorm x := by
    linarith only [hr]
  have hpow : (1 + vec3EuclideanNorm x) ^ n ≤
      (2 * vec3EuclideanNorm x) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hleBase n
  have hinv : ((2 * vec3EuclideanNorm x) ^ n)⁻¹ ≤
      ((1 + vec3EuclideanNorm x) ^ n)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hscale : ((vec3EuclideanNorm x / 2) ^ n)⁻¹ =
      2 ^ n * (vec3EuclideanNorm x ^ n)⁻¹ := by
    rw [div_pow]
    field_simp [ne_of_gt hxnorm]
  have hratio : (vec3EuclideanNorm x ^ n)⁻¹ =
      2 ^ n * ((2 * vec3EuclideanNorm x) ^ n)⁻¹ := by
    rw [mul_pow]
    field_simp [ne_of_gt hxnorm]
  have hinvBracket : ((1 + vec3EuclideanNorm x) ^ n)⁻¹ =
      (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) :=
    (CKN.Foundation.Heat.inv_pow_eq_rpow_neg hbase n)
  have hpower : ((vec3EuclideanNorm x / 2) ^ n)⁻¹ ≤
      4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
    rw [hscale, hratio]
    calc
      2 ^ n * (2 ^ n * ((2 * vec3EuclideanNorm x) ^ n)⁻¹) ≤
          2 ^ n * (2 ^ n * ((1 + vec3EuclideanNorm x) ^ n)⁻¹) := by
            gcongr
      _ = 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
            calc
              _ = (2 ^ n * 2 ^ n) * ((1 + vec3EuclideanNorm x) ^ n)⁻¹ := by ring
              _ = 4 ^ n * ((1 + vec3EuclideanNorm x) ^ n)⁻¹ := by
                congr 1
                rw [← mul_pow]
                norm_num
              _ = 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
                rw [hinvBracket]
  have hraw := hfar t x hx
  calc
    _ ≤ c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := hraw
    _ ≤ c * M * 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
      dsimp [C, n]
      have hfactor : 0 ≤ c * M := mul_nonneg hc hM
      calc
        c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M =
            (c * M) * ((vec3EuclideanNorm x / 2) ^ n)⁻¹ := by ring
        _ ≤ (c * M) *
            (4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ))) :=
              mul_le_mul_of_nonneg_left hpower hfactor
        _ = c * M * 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by ring
    _ = C * (1 + vec3EuclideanNorm x) ^ (-(1 + k : ℝ)) := by
      simp [C, n, Nat.cast_add]

private theorem associatedPressureContinuous_spatialDecay_of_far
    {f : Vec3 × ℝ → ℝ} (hf : Continuous f) {K : Set ℝ}
    (hK : IsCompact K) (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    (m : ℕ) (R : ℝ) (hR : 1 ≤ R) (C : ℝ) (hC : 0 ≤ C)
    (hfar : ∀ t x, 4 * R < vec3EuclideanNorm x →
      |f (x, t)| ≤ C * (1 + vec3EuclideanNorm x) ^ (-(m : ℝ))) :
    ∃ C' ≥ 0, ∀ z, |f z| ≤ C' *
      (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) := by
  let B : Set Vec3 := CKN.euclideanClosedBall 0 (4 * R)
  let S : Set (Vec3 × ℝ) := B ×ˢ K
  let absf : Vec3 × ℝ → ℝ := fun z => |f z|
  have hRpos : 0 < 4 * R := by linarith only [hR]
  have hB : IsCompact B := by
    exact CKN.isCompact_euclideanClosedBall 0 hRpos.le
  have hS : IsCompact S := hB.prod hK
  have hImage : BddAbove (absf '' S) := by
    exact hS.bddAbove_image hf.abs.continuousOn
  obtain ⟨M₀, hM₀⟩ := hImage
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let C' : ℝ := C + M * (1 + 4 * R) ^ m
  have hC' : 0 ≤ C' := by
    dsimp [C']
    exact add_nonneg hC (mul_nonneg hM (by positivity))
  refine ⟨C', hC', ?_⟩
  intro z
  by_cases ht : z.2 ∉ K
  · have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) :=
      Real.rpow_nonneg
        (add_nonneg (by norm_num) (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1))
        (-(m : ℝ))
    simpa [hzero z.2 ht z.1] using mul_nonneg hC' hprof
  · by_cases hx : 4 * R < vec3EuclideanNorm z.1
    · exact (hfar z.2 z.1 hx).trans (by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C']
          exact le_add_of_nonneg_right (mul_nonneg hM (by positivity))
        · exact Real.rpow_nonneg
            (add_nonneg (by norm_num)
              (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) (-(m : ℝ)))
    · have hnorm : vec3EuclideanNorm z.1 ≤ 4 * R := le_of_not_gt hx
      have hball : z.1 ∈ B := by
        apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hRpos.le).2
        simpa [B, vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two] using hnorm
      have hzS : z ∈ S := ⟨hball, by simpa using ht⟩
      have hlocal : |f z| ≤ M := by
        have hpoint := hM₀ ⟨z, hzS, rfl⟩
        change |f z| ≤ M₀ at hpoint
        dsimp [M]
        exact hpoint.trans (le_max_left _ _)
      have hA : 0 < 1 + vec3EuclideanNorm z.1 :=
        add_pos_of_pos_of_nonneg (by norm_num)
          (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)
      have hAupper : 1 + vec3EuclideanNorm z.1 ≤ 1 + 4 * R := by
        linarith only [hnorm]
      have hpow : (1 + vec3EuclideanNorm z.1) ^ m ≤ (1 + 4 * R) ^ m :=
        pow_le_pow_left₀ (by positivity) hAupper m
      have hfactor : 1 ≤ (1 + 4 * R) ^ m *
          ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by
        have hpos : 0 < (1 + vec3EuclideanNorm z.1) ^ m := pow_pos hA m
        have hdiv : 1 ≤ (1 + 4 * R) ^ m /
            ((1 + vec3EuclideanNorm z.1) ^ m) := by
          apply (le_div_iff₀ hpos).2
          simpa only [one_mul] using hpow
        simpa [div_eq_mul_inv] using hdiv
      have hrpow : (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) =
          ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by
        rw [Real.rpow_neg hA.le]
        exact congrArg Inv.inv (by norm_num)
      rw [hrpow]
      dsimp [C']
      calc
        |f z| ≤ M := hlocal
        _ ≤ M * ((1 + 4 * R) ^ m *
            ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹) := by
          calc
            M = M * 1 := by ring
            _ ≤ M * ((1 + 4 * R) ^ m *
                ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹) :=
              mul_le_mul_of_nonneg_left hfactor hM
        _ ≤ (C + M * (1 + 4 * R) ^ m) *
            ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by
          calc
            M * ((1 + 4 * R) ^ m *
                ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹) =
                (M * (1 + 4 * R) ^ m) *
                  ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by ring
            _ ≤ (C + M * (1 + 4 * R) ^ m) *
                  ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by positivity)

/-- The Newtonian potential commutes with time differentiation for smooth,
compactly supported sources, as used in `lem:helmholtz-test`. -/
theorem associatedPressureNewtonianPotential_timePartial
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (z : Vec3 × ℝ) :
    CKN.timePartial (associatedPressureNewtonianPotential g) z =
      associatedPressureNewtonianPotential
        (fun q => CKN.timePartial (show ParabolicPoint → ℝ from g) q) z := by
  let K : Set Vec3 := (tsupport g).image Prod.fst
  let source : ℝ → Vec3 → ℝ := fun t x => g (x, t)
  let gTime : Vec3 × ℝ → ℝ := fun q =>
    CKN.timePartial (show ParabolicPoint → ℝ from g) q
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hpotentialConv (f : Vec3 × ℝ → ℝ) (q : Vec3 × ℝ) :
      associatedPressureNewtonianPotential f q =
        ((fun y : Vec3 => f (y, q.2)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ), (volume : Measure Vec3)]
          (-newtonianKernel)) q.1 := by
    rw [associatedPressureNewtonianPotential, CKN.pressureNewtonianPotential,
      convolution_def]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [ContinuousLinearMap.lsmul_apply]
    exact mul_comm _ _
  have hK : IsCompact K := hgc.isCompact.image continuous_fst
  have hsource : ContDiff ℝ (⊤ : ℕ∞) (↿source) := by
    have hswap : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec3 => (q.2, q.1)) :=
      contDiff_snd.prodMk contDiff_fst
    exact hg.comp hswap
  have hsourceOn : ContDiffOn ℝ (1 : ℕ∞) (↿source)
      ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set Vec3)) := by
    exact (hsource.of_le (by norm_num)).contDiffOn
  have hsourceZero : ∀ t : ℝ, ∀ x : Vec3, t ∈ (Set.univ : Set ℝ) →
      x ∉ K → source t x = 0 := by
    intro t x _ hx
    have hnot : (x, t) ∉ tsupport g := by
      intro hmem
      exact hx ⟨(x, t), hmem, rfl⟩
    change g (x, t) = 0
    exact image_eq_zero_of_notMem_tsupport hnot
  have hfd := MeasureTheory.hasFDerivAt_convolution_right_with_param
    (L := L) (s := (Set.univ : Set ℝ)) (k := K)
    isOpen_univ hK hsourceZero locallyIntegrable_newtonianKernel.neg
    hsourceOn (z.2, z.1) (by simp)
  let dsource : Vec3 → (ℝ × Vec3) →L[ℝ] ℝ := fun y =>
    fderiv ℝ ↿source (z.2, y)
  have hdsourceCont : Continuous dsource := by
    have hcont := hsource.continuous_fderiv (by simp)
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hdsourceZero : ∀ y ∉ K, dsource y = 0 := by
    intro y hy
    have hsourceZeroNear : ∀ᶠ q : ℝ × Vec3 in 𝓝 (z.2, y),
        ↿source q = 0 := by
      have hKopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
      have hyNhds : Kᶜ ∈ 𝓝 y := hKopen.mem_nhds hy
      rw [nhds_prod_eq]
      filter_upwards [prod_mem_prod (isOpen_univ.mem_nhds (Set.mem_univ z.2)) hyNhds]
      rintro ⟨t, x⟩ ⟨_, hx⟩
      exact hsourceZero t x (Set.mem_univ _) hx
    have hsourceZeroNear' : ↿source =ᶠ[𝓝 (z.2, y)] fun _ => (0 : ℝ) := by
      filter_upwards [hsourceZeroNear] with q hq
      exact hq
    have hzfd : HasFDerivAt (↿source)
        (0 : (ℝ × Vec3) →L[ℝ] ℝ) (z.2, y) :=
      hasFDerivAt_zero_of_eventually_const
        (f := ↿source) (x := (z.2, y)) (c := (0 : ℝ))
        hsourceZeroNear'
    simpa [dsource] using hzfd.fderiv
  have hdsourceCompact : HasCompactSupport dsource := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro y hy
    by_contra hyK
    exact hy (hdsourceZero y hyK)
  have hcurve : HasDerivAt (fun t : ℝ => (t, z.1)) (1, 0) z.2 := by
    simpa using (hasDerivAt_id z.2).prodMk (hasDerivAt_const z.2 z.1)
  have hchain := hfd.comp z.2 hcurve
  have hchainDeriv := hchain.hasDerivAt.deriv
  have hfdEval := hfd.fderiv
  have hconvDeriv := congrArg (fun D : (ℝ × Vec3) →L[ℝ] ℝ => D (1, 0)) hfdEval
  have hconvDeriv' :
      (((-newtonianKernel) ⋆[L.precompR (ℝ × Vec3), (volume : Measure Vec3)]
        dsource) z.1) (1, 0) =
        (associatedPressureNewtonianPotential gTime) z := by
    rw [convolution_precompR_apply (f := -newtonianKernel) (L := L)
      locallyIntegrable_newtonianKernel.neg hdsourceCompact hdsourceCont z.1 (1, 0)]
    have hdir (y : Vec3) : dsource y (1, 0) = gTime (y, z.2) := by
      have hcurve' : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) z.2 := by
        simpa using (hasDerivAt_id z.2).prodMk (hasDerivAt_const z.2 y)
      have hsrcDiff : DifferentiableAt ℝ (↿source) (z.2, y) :=
        (hsource.differentiable (by simp)) (z.2, y)
      have hsrcCurve := hsrcDiff.hasFDerivAt.comp z.2 hcurve'
      have hsrcDeriv := hsrcCurve.hasDerivAt.deriv
      have hcurveEq :
          (↿source) ∘ (fun t : ℝ => (t, y)) =
            (fun t : ℝ => g (y, t)) := by
        funext t
        rfl
      rw [hcurveEq] at hsrcDeriv
      change (fderiv ℝ (↿source) (z.2, y)) (1, 0) =
        deriv (fun t : ℝ => g (y, t)) z.2
      simpa [gTime, CKN.timePartial] using hsrcDeriv.symm
    have hconvolution :
        (fun y : Vec3 => ((-newtonianKernel) ⋆[L, (volume : Measure Vec3)]
          (fun q : Vec3 => dsource q (1, 0))) y) =
        (fun y : Vec3 => ((fun q : Vec3 => gTime (q, z.2)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ), (volume : Measure Vec3)]
          (-newtonianKernel)) y) := by
      funext y
      rw [convolution_flip]
      congr 1
      funext q
      exact hdir q
    calc
      ((-newtonianKernel) ⋆[L, (volume : Measure Vec3)]
          (fun q : Vec3 => dsource q (1, 0))) z.1 =
          ((fun y : Vec3 => gTime (y, z.2)) ⋆[
            (ContinuousLinearMap.lsmul ℝ ℝ), (volume : Measure Vec3)]
            (-newtonianKernel)) z.1 :=
        congrArg (fun f : Vec3 → ℝ => f z.1) hconvolution
      _ = associatedPressureNewtonianPotential gTime z :=
        (hpotentialConv gTime z).symm
  have hHslice : (fun t : ℝ =>
      ((-newtonianKernel) ⋆[L, (volume : Measure Vec3)] (source t)) z.1) =
      (fun t => associatedPressureNewtonianPotential g (z.1, t)) := by
    funext t
    change ((-newtonianKernel) ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).flip, (volume : Measure Vec3)]
      (fun y : Vec3 => g (y, t))) z.1 =
        associatedPressureNewtonianPotential g (z.1, t)
    rw [convolution_flip]
    exact (hpotentialConv g (z.1, t)).symm
  have htimeEq : CKN.timePartial (associatedPressureNewtonianPotential g) z =
      deriv (fun t : ℝ => associatedPressureNewtonianPotential g (z.1, t)) z.2 := by
    rfl
  have htimeH : CKN.timePartial (associatedPressureNewtonianPotential g) z =
      deriv (fun t : ℝ =>
        ((-newtonianKernel) ⋆[L, (volume : Measure Vec3)] (source t)) z.1) z.2 := by
    calc
      _ = deriv (fun t : ℝ => associatedPressureNewtonianPotential g (z.1, t)) z.2 :=
        htimeEq
      _ = deriv (fun t : ℝ =>
          ((-newtonianKernel) ⋆[L, (volume : Measure Vec3)] (source t)) z.1) z.2 :=
        congrArg (fun f : ℝ → ℝ => deriv f z.2) hHslice.symm
  have hchainDeriv' :
      deriv (fun t : ℝ =>
        ((-newtonianKernel) ⋆[L, (volume : Measure Vec3)] (source t)) z.1) z.2 =
        (((-newtonianKernel) ⋆[L.precompR (ℝ × Vec3), (volume : Measure Vec3)]
          dsource) z.1) (1, 0) := by
    calc
      _ = (((-newtonianKernel) ⋆[L.precompR (ℝ × Vec3), (volume : Measure Vec3)]
          dsource) z.1) (1, 0) := by
        simpa [dsource, Function.comp_def, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply] using hchainDeriv
      _ = _ := rfl
  exact htimeH.trans (hchainDeriv'.trans hconvDeriv')

private theorem associatedPressureHelmholtz_direction_zero_of_slice_zero
    {φ : Vec3 × ℝ → Vec3}
    (hψsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzScalarPotential φ))
    (hzero : ∀ t, t ∉ (tsupport φ).image Prod.snd → ∀ x,
      associatedPressureHelmholtzScalarPotential φ (x, t) = 0)
    (i : Fin 3) (t : ℝ) (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :
    rieszPressureJointDirection (associatedPressureHelmholtzScalarPotential φ) i (x, t) = 0 := by
  rw [← rieszPressure_sliceSpatialDeriv_eq_joint hψsmooth i (x, t)]
  have hslice : (fun y : Vec3 =>
      associatedPressureHelmholtzScalarPotential φ (y, t)) = fun _ => (0 : ℝ) := by
    funext y
    exact hzero t ht y
  rw [hslice]
  simp [CKN.spatialDeriv]

private theorem associatedPressureHelmholtz_hessian_zero_of_slice_zero
    {φ : Vec3 × ℝ → Vec3}
    (hψsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzScalarPotential φ))
    (hzero : ∀ t, t ∉ (tsupport φ).image Prod.snd → ∀ x,
      associatedPressureHelmholtzScalarPotential φ (x, t) = 0)
    (i j : Fin 3) (t : ℝ) (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :
    rieszPressureJointHessian (associatedPressureHelmholtzScalarPotential φ) i j (x, t) = 0 := by
  rw [← rieszPressure_sliceMixedSecond_eq_joint hψsmooth i j (x, t)]
  have hslice : (fun y : Vec3 =>
      associatedPressureHelmholtzScalarPotential φ (y, t)) = fun _ => (0 : ℝ) := by
    funext y
    exact hzero t ht y
  rw [hslice]
  have hdir : CKN.spatialDeriv (fun _ : Vec3 => (0 : ℝ)) j = fun _ => 0 := by
    funext y
    simp [CKN.spatialDeriv]
  rw [CKN.mixedSecond]
  rw [hdir]
  simp [CKN.spatialDeriv]

private theorem associatedPressureHelmholtz_decay_all_component_bounds
    {φ : Vec3 × ℝ → Vec3}
    (hgrad : ∀ i : Fin 3, ∃ C ≥ 0, ∀ z,
      |rieszPressureJointDirection (associatedPressureHelmholtzScalarPotential φ) i z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)))
    (hhess : ∀ i j : Fin 3, ∃ C ≥ 0, ∀ z,
      |rieszPressureJointHessian (associatedPressureHelmholtzScalarPotential φ) i j z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ))) :
    (∃ C ≥ 0, ∀ i z,
      |rieszPressureJointDirection (associatedPressureHelmholtzScalarPotential φ) i z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))) ∧
    (∃ C ≥ 0, ∀ i j z,
      |rieszPressureJointHessian (associatedPressureHelmholtzScalarPotential φ) i j z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ))) := by
  choose Dg hDg hGbound using hgrad
  let CgAll : ℝ := ∑ i : Fin 3, Dg i
  have hCgAll : 0 ≤ CgAll := Finset.sum_nonneg (fun i _ => hDg i)
  have hDgle (i : Fin 3) : Dg i ≤ CgAll :=
    Finset.single_le_sum (fun j _ => hDg j) (Finset.mem_univ i)
  have hgradAll : ∃ C ≥ 0, ∀ i z,
      |rieszPressureJointDirection
        (associatedPressureHelmholtzScalarPotential φ) i z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    refine ⟨CgAll, hCgAll, ?_⟩
    intro i z
    have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
      Real.rpow_nonneg
        (add_nonneg (by norm_num) (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
    exact (hGbound i z).trans
      (mul_le_mul_of_nonneg_right (hDgle i) hprof)
  choose Dh hDh hHbound using hhess
  let ChAll : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, Dh i j
  have hChAll : 0 ≤ ChAll := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hDh i j))
  have hDhInner (i j : Fin 3) : Dh i j ≤ ∑ k : Fin 3, Dh i k :=
    Finset.single_le_sum (fun k _ => hDh i k) (Finset.mem_univ j)
  have hDhOuter (i : Fin 3) : (∑ j : Fin 3, Dh i j) ≤ ChAll := by
    dsimp [ChAll]
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun j _ => hDh k j)) (Finset.mem_univ i)
  have hDhAll (i j : Fin 3) : Dh i j ≤ ChAll :=
    (hDhInner i j).trans (hDhOuter i)
  have hhessAll : ∃ C ≥ 0, ∀ i j z,
      |rieszPressureJointHessian
        (associatedPressureHelmholtzScalarPotential φ) i j z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
    refine ⟨ChAll, hChAll, ?_⟩
    intro i j z
    have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) :=
      Real.rpow_nonneg
        (add_nonneg (by norm_num) (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
    exact (hHbound i j z).trans
      (mul_le_mul_of_nonneg_right (hDhAll i j) hprof)
  exact ⟨hgradAll, hhessAll⟩

/-- The scalar Newtonian Helmholtz potential has all the spatial decay data
required to invoke the proved Riesz pressure duality result. -/
theorem associatedPressureHelmholtzScalarPotential_decay
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    RieszPressurePotentialDecay (associatedPressureHelmholtzScalarPotential φ) := by
  let g : Fin 3 → Vec3 × ℝ → ℝ := fun k z => φ z k
  have hg (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g k) :=
    (CKN.component_mem_spaceTimeTestFunction hφ k).1
  have hgc (k : Fin 3) : HasCompactSupport (g k) :=
    (CKN.component_mem_spaceTimeTestFunction hφ k).2.1
  choose R₀ hR₀ C₀ hC₀ hfar₀ using fun k =>
    associatedPressureNewtonianPotential_iteratedFDeriv_far_decay (hg k) (hgc k) 1
  choose R₁ hR₁ C₁ hC₁ hfar₁ using fun k =>
    associatedPressureNewtonianPotential_iteratedFDeriv_far_decay (hg k) (hgc k) 2
  choose R₂ hR₂ C₂ hC₂ hfar₂ using fun k =>
    associatedPressureNewtonianPotential_iteratedFDeriv_far_decay (hg k) (hgc k) 3
  let Rv : ℝ := ∑ k : Fin 3, R₀ k
  let Rg : ℝ := ∑ k : Fin 3, R₁ k
  let Rh : ℝ := ∑ k : Fin 3, R₂ k
  let Cv : ℝ := ∑ k : Fin 3, C₀ k
  let Cg : ℝ := ∑ k : Fin 3, C₁ k
  let Ch : ℝ := ∑ k : Fin 3, C₂ k
  have hRv : 1 ≤ Rv := by
    dsimp [Rv]
    calc
      1 ≤ R₀ 0 := hR₀ 0
      _ ≤ ∑ k : Fin 3, R₀ k := Finset.single_le_sum
        (fun k hk => le_trans (by norm_num) (hR₀ k)) (Finset.mem_univ 0)
  have hRg : 1 ≤ Rg := by
    dsimp [Rg]
    calc
      1 ≤ R₁ 0 := hR₁ 0
      _ ≤ ∑ k : Fin 3, R₁ k := Finset.single_le_sum
        (fun k hk => le_trans (by norm_num) (hR₁ k)) (Finset.mem_univ 0)
  have hRh : 1 ≤ Rh := by
    dsimp [Rh]
    calc
      1 ≤ R₂ 0 := hR₂ 0
      _ ≤ ∑ k : Fin 3, R₂ k := Finset.single_le_sum
        (fun k hk => le_trans (by norm_num) (hR₂ k)) (Finset.mem_univ 0)
  have hCv : 0 ≤ Cv := by
    dsimp [Cv]
    exact Finset.sum_nonneg (fun k _ => hC₀ k)
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    exact Finset.sum_nonneg (fun k _ => hC₁ k)
  have hCh : 0 ≤ Ch := by
    dsimp [Ch]
    exact Finset.sum_nonneg (fun k _ => hC₂ k)
  have hRvle (k : Fin 3) : R₀ k ≤ Rv := by
    dsimp [Rv]
    exact Finset.single_le_sum
      (fun j _ => le_trans (by norm_num) (hR₀ j)) (Finset.mem_univ k)
  have hRgle (k : Fin 3) : R₁ k ≤ Rg := by
    dsimp [Rg]
    exact Finset.single_le_sum
      (fun j _ => le_trans (by norm_num) (hR₁ j)) (Finset.mem_univ k)
  have hRhle (k : Fin 3) : R₂ k ≤ Rh := by
    dsimp [Rh]
    exact Finset.single_le_sum
      (fun j _ => le_trans (by norm_num) (hR₂ j)) (Finset.mem_univ k)
  have hψsmooth := associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hK : IsCompact ((tsupport φ).image Prod.snd) :=
    hφ.2.1.isCompact.image continuous_snd
  have hzero (t : ℝ) (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :
      associatedPressureHelmholtzScalarPotential φ (x, t) = 0 :=
    (associatedPressureHelmholtzPotentials_zero_off_time_support ht x).1
  have hfarVal (t : ℝ) (x : Vec3) (hx : 4 * Rv < vec3EuclideanNorm x) :
      |associatedPressureHelmholtzScalarPotential φ (x, t)| ≤
        Cv * (1 + vec3EuclideanNorm x) ^ (-(2 : ℝ)) := by
    rw [associatedPressureHelmholtzScalarPotential_eq_sum_spatialPartial hφ]
    calc
      |∑ k : Fin 3, CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (g k)) k (x, t)| ≤
          ∑ k : Fin 3, |CKN.spatialPartialProd
            (associatedPressureNewtonianPotential (g k)) k (x, t)| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin 3,
          C₀ k * (1 + vec3EuclideanNorm x) ^ (-(2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hsmooth := associatedPressureNewtonianPotential_contDiff (hg k) (hgc k)
        have hslice := hsmooth.comp
          (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) t)
        have hderiv := associatedPressureFirstSpatialDerivative_le_iteratedFDeriv
          (f := CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) k x
        have hfar := hfar₀ k t x (by nlinarith only [hx, hRvle k])
        change |CKN.spatialDeriv
          (CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) k x| ≤ _
        have hpot : ‖iteratedFDeriv ℝ 1
            (CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) x‖ ≤
            C₀ k * (1 + vec3EuclideanNorm x) ^ (-(1 + (1 : ℝ))) := by
          simpa [Nat.cast_add] using hfar
        rw [show -(1 + (1 : ℝ)) = -(2 : ℝ) by norm_num] at hpot
        exact hderiv.trans hpot
      _ = Cv * (1 + vec3EuclideanNorm x) ^ (-(2 : ℝ)) := by
        dsimp [Cv]
        rw [← Finset.sum_mul]
  have hfarGrad (i : Fin 3) (t : ℝ) (x : Vec3)
      (hx : 4 * Rg < vec3EuclideanNorm x) :
      |rieszPressureJointDirection
          (associatedPressureHelmholtzScalarPotential φ) i (x, t)| ≤
        Cg * (1 + vec3EuclideanNorm x) ^ (-(3 : ℝ)) := by
    rw [associatedPressureHelmholtzScalarPotential_direction_eq_sum hφ]
    calc
      |∑ k : Fin 3, CKN.spatialPartialProd
          (CKN.spatialPartialProd (associatedPressureNewtonianPotential (g k)) k)
          i (x, t)| ≤
          ∑ k : Fin 3, |CKN.spatialPartialProd
            (CKN.spatialPartialProd (associatedPressureNewtonianPotential (g k)) k)
            i (x, t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin 3,
          C₁ k * (1 + vec3EuclideanNorm x) ^ (-(3 : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hsmooth := associatedPressureNewtonianPotential_contDiff (hg k) (hgc k)
        have hslice := hsmooth.comp
          (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) t)
        have hfar := hfar₁ k t x (by nlinarith only [hx, hRgle k])
        have hpot : ‖iteratedFDeriv ℝ 2
            (CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) x‖ ≤
            C₁ k * (1 + vec3EuclideanNorm x) ^ (-(1 + (2 : ℝ))) := by
          simpa [Nat.cast_add] using hfar
        rw [show -(1 + (2 : ℝ)) = -(3 : ℝ) by norm_num] at hpot
        change |CKN.spatialDeriv
          (CKN.spatialDeriv
            (CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) k)
          i x| ≤ _
        exact (associatedPressureSecondSpatialDerivative_le_iteratedFDeriv hslice i k x).trans
          hpot
      _ = Cg * (1 + vec3EuclideanNorm x) ^ (-(3 : ℝ)) := by
        dsimp [Cg]
        rw [← Finset.sum_mul]
  have hfarHess (i j : Fin 3) (t : ℝ) (x : Vec3)
      (hx : 4 * Rh < vec3EuclideanNorm x) :
      |rieszPressureJointHessian
          (associatedPressureHelmholtzScalarPotential φ) i j (x, t)| ≤
        Ch * (1 + vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
    rw [associatedPressureHelmholtzScalarPotential_hessian_eq_sum hφ]
    calc
      |∑ k : Fin 3, CKN.spatialPartialProd
          (CKN.spatialPartialProd
            (CKN.spatialPartialProd (associatedPressureNewtonianPotential (g k)) k) j)
          i (x, t)| ≤
          ∑ k : Fin 3, |CKN.spatialPartialProd
            (CKN.spatialPartialProd
              (CKN.spatialPartialProd (associatedPressureNewtonianPotential (g k)) k) j)
            i (x, t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin 3,
          C₂ k * (1 + vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hsmooth := associatedPressureNewtonianPotential_contDiff (hg k) (hgc k)
        have hslice := hsmooth.comp
          (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) t)
        have hfar := hfar₂ k t x (by nlinarith only [hx, hRhle k])
        have hpot : ‖iteratedFDeriv ℝ 3
            (CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) x‖ ≤
            C₂ k * (1 + vec3EuclideanNorm x) ^ (-(1 + (3 : ℝ))) := by
          simpa [Nat.cast_add] using hfar
        rw [show -(1 + (3 : ℝ)) = -(4 : ℝ) by norm_num] at hpot
        change |CKN.spatialDeriv
          (CKN.spatialDeriv
            (CKN.spatialDeriv
              (CKN.pressureNewtonianPotential (fun y : Vec3 => g k (y, t))) k) j)
          i x| ≤ _
        exact (associatedPressureThirdSpatialDerivative_le_iteratedFDeriv hslice i j k x).trans
          hpot
      _ = Ch * (1 + vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
        dsimp [Ch]
        rw [← Finset.sum_mul]
  have hval := associatedPressureContinuous_spatialDecay_of_far
    hψsmooth.continuous hK (fun t ht x => hzero t ht x) 2 Rv hRv Cv hCv
    (fun t x hx => hfarVal t x hx)
  have hgradzero (i : Fin 3) (t : ℝ)
      (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :=
    associatedPressureHelmholtz_direction_zero_of_slice_zero hψsmooth hzero i t ht x
  have hgrad (i : Fin 3) := associatedPressureContinuous_spatialDecay_of_far
    (rieszPressureJointDirection_contDiff hψsmooth i).continuous hK
    (fun t ht x => hgradzero i t ht x) 3 Rg hRg Cg hCg
    (fun t x hx => hfarGrad i t x hx)
  have hhesszero (i j : Fin 3) (t : ℝ)
      (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :=
    associatedPressureHelmholtz_hessian_zero_of_slice_zero hψsmooth hzero i j t ht x
  have hhess (i j : Fin 3) := associatedPressureContinuous_spatialDecay_of_far
    (rieszPressureJointHessian_contDiff hψsmooth i j).continuous hK
    (fun t ht x => hhesszero i j t ht x) 4 Rh hRh Ch hCh
    (fun t x hx => hfarHess i j t x hx)
  have ⟨hgradAll, hhessAll⟩ :=
    associatedPressureHelmholtz_decay_all_component_bounds hgrad hhess
  refine ⟨⟨(tsupport φ).image Prod.snd, hK, fun t ht x => hzero t ht x⟩,
    hval, hgradAll, hhessAll⟩

end CKN.Leray

end
