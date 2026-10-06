/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliCutoff

/-!
# Space-time cutoff for a local energy estimate

This module combines the spatial and temporal weights for `lem:caccioppoli`.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace ESS

@[expose] def caccioppoliSpaceTimeWeight (x₀ : Vec3) (t r ε : ℝ)
    (q : Vec3 × ℝ) : ℝ :=
  caccioppoliSpatialWeight x₀ r q.1 ^ 2 * caccioppoliTimeWeight t r ε q.2 ^ 2

private theorem fderiv_caccioppoliSpaceTimeWeight_spatial
    {η : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (q : Vec3 × ℝ) (j : Fin 3) :
    (fderiv ℝ (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) q)
      (basisVec j, 0) =
      2 * η q.1 * (fderiv ℝ η q.1) (basisVec j) * θ q.2 ^ 2 := by
  let f : Vec3 → ℝ := fun y => η y ^ 2
  let g : ℝ → ℝ := fun s => θ s ^ 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hη.pow 2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hθ.pow 2
  have hfprod : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z.1) := by fun_prop
  have hgprod : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z.2) := by fun_prop
  have hmul := fderiv_mul (hfprod.differentiable (by simp) q)
    (hgprod.differentiable (by simp) q)
  have hfun : (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) =
      (fun z => f z.1) * (fun z => g z.2) := by funext z; rfl
  rw [hfun, hmul]
  have hfirst :
      (fderiv ℝ (fun z : Vec3 × ℝ => f z.1) q) (basisVec j, 0) =
        (fderiv ℝ f q.1) (basisVec j) := by
    have hcomp := (hf.differentiable (by simp) q.1).hasFDerivAt.comp q
      (hasFDerivAt_fst (𝕜 := ℝ) (E := Vec3) (F := ℝ) (p := q))
    have hEq : (fun z : Vec3 × ℝ => f z.1) = f ∘ Prod.fst := rfl
    rw [hEq, hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hsecond :
      (fderiv ℝ (fun z : Vec3 × ℝ => g z.2) q) (basisVec j, 0) = 0 := by
    have hcomp := (hg.differentiable (by simp) q.2).hasFDerivAt.comp q
      (hasFDerivAt_snd (𝕜 := ℝ) (E := Vec3) (F := ℝ) (p := q))
    have hEq : (fun z : Vec3 × ℝ => g z.2) = g ∘ Prod.snd := rfl
    rw [hEq, hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  simp only [add_apply, smul_apply, hfirst, hsecond]
  have hpow := fderiv_pow 2 (hη.differentiable (by simp) q.1)
  have hpow' : fderiv ℝ f q.1 = (2 • η q.1 ^ (2 - 1)) • fderiv ℝ η q.1 := by
    change fderiv ℝ (fun y : Vec3 => η y ^ 2) q.1 = _
    exact hpow
  rw [hpow']
  simp only [f, g, smul_apply, smul_eq_mul, Nat.reduceSub, pow_one]
  ring_nf

private theorem fderiv_caccioppoliSpaceTimeWeight_time
    {η : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (q : Vec3 × ℝ) :
    (fderiv ℝ (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) q) (0, 1) =
      2 * η q.1 ^ 2 * θ q.2 * deriv θ q.2 := by
  let f : Vec3 → ℝ := fun y => η y ^ 2
  let g : ℝ → ℝ := fun s => θ s ^ 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hη.pow 2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hθ.pow 2
  have hfprod : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z.1) := by fun_prop
  have hgprod : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z.2) := by fun_prop
  have hmul := fderiv_mul (hfprod.differentiable (by simp) q)
    (hgprod.differentiable (by simp) q)
  have hfun : (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) =
      (fun z => f z.1) * (fun z => g z.2) := by funext z; rfl
  rw [hfun, hmul]
  have hfirst :
      (fderiv ℝ (fun z : Vec3 × ℝ => f z.1) q) (0, 1) = 0 := by
    have hcomp := (hf.differentiable (by simp) q.1).hasFDerivAt.comp q
      (hasFDerivAt_fst (𝕜 := ℝ) (E := Vec3) (F := ℝ) (p := q))
    have hEq : (fun z : Vec3 × ℝ => f z.1) = f ∘ Prod.fst := rfl
    rw [hEq, hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hsecond :
      (fderiv ℝ (fun z : Vec3 × ℝ => g z.2) q) (0, 1) =
        (fderiv ℝ g q.2) 1 := by
    have hcomp := (hg.differentiable (by simp) q.2).hasFDerivAt.comp q
      (hasFDerivAt_snd (𝕜 := ℝ) (E := Vec3) (F := ℝ) (p := q))
    have hEq : (fun z : Vec3 × ℝ => g z.2) = g ∘ Prod.snd := rfl
    rw [hEq, hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hderiv : (fderiv ℝ g q.2) 1 = 2 * θ q.2 * deriv θ q.2 := by
    have hpow := fderiv_pow 2 (hθ.differentiable (by simp) q.2)
    have hpow' : fderiv ℝ g q.2 =
        (2 • θ q.2 ^ (2 - 1)) • fderiv ℝ θ q.2 := by
      change fderiv ℝ (fun s : ℝ => θ s ^ 2) q.2 = _
      exact hpow
    rw [hpow']
    have hHas := (hθ.differentiable (by simp) q.2).hasDerivAt
    have hF := hHas.hasFDerivAt
    have hderivEq : fderiv ℝ θ q.2 =
        ContinuousLinearMap.toSpanSingleton ℝ (deriv θ q.2) := by
      rw [← hF.fderiv]
    rw [hderivEq]
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, pow_one]
  simp only [add_apply, smul_apply, hfirst, hsecond, hderiv]
  simp only [f, g, smul_eq_mul]
  ring

/-- Properties of the product cutoff used in `lem:caccioppoli`. -/
theorem caccioppoliSpaceTimeWeight_properties
    {x₀ : Vec3} {t r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hεsmall : 4 * ε < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliSpaceTimeWeight x₀ t r ε) ∧
    HasCompactSupport (caccioppoliSpaceTimeWeight x₀ t r ε) ∧
    tsupport (caccioppoliSpaceTimeWeight x₀ t r ε) ⊆
      vec3Ball x₀ (2 * r) ×ˢ Ioo t (t + 4 * r ^ 2) ∧
    (∀ q, 0 ≤ caccioppoliSpaceTimeWeight x₀ t r ε q ∧
      caccioppoliSpaceTimeWeight x₀ t r ε q ≤ 1) ∧
    (∀ q j, (fderiv ℝ (caccioppoliSpaceTimeWeight x₀ t r ε) q)
      (basisVec j, 0) =
        2 * caccioppoliSpatialWeight x₀ r q.1 *
          (classicalGradient (caccioppoliSpatialWeight x₀ r) q.1) j *
          caccioppoliTimeWeight t r ε q.2 ^ 2) ∧
    (∀ q, q.2 ≤ t + r ^ 2 →
      0 ≤ (fderiv ℝ (caccioppoliSpaceTimeWeight x₀ t r ε) q) (0, 1)) ∧
    (∀ q, t + r ^ 2 ≤ q.2 →
      -(1600 / 199 : ℝ) / r ^ 2 ≤
        (fderiv ℝ (caccioppoliSpaceTimeWeight x₀ t r ε) q) (0, 1)) ∧
    (∀ q, vec3EuclideanNorm (q.1 - x₀) < r →
      t + 2 * ε ≤ q.2 → q.2 ≤ t + r ^ 2 →
      caccioppoliSpaceTimeWeight x₀ t r ε q = 1) ∧
    (∀ q, ∑ j : Fin 3,
      ((fderiv ℝ (caccioppoliSpaceTimeWeight x₀ t r ε) q) (basisVec j, 0)) ^ 2 ≤
        (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) *
          caccioppoliSpaceTimeWeight x₀ t r ε q) := by
  have hη := caccioppoliSpatialWeight_properties x₀ hr
  have hθ := caccioppoliTimeWeight_properties (t := t) hε hr hεsmall
  let η := caccioppoliSpatialWeight x₀ r
  let θ := caccioppoliTimeWeight t r ε
  have hηc : HasCompactSupport η := hη.2.1
  have hθc : HasCompactSupport θ := hθ.2.1
  have hηts : tsupport η ⊆ vec3Ball x₀ (2 * r) := hη.2.2.1
  have hθts : tsupport θ ⊆ Icc (t + ε) (t + 3 * r ^ 2) := hθ.2.2.1
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := hη.1
  have hθsmooth : ContDiff ℝ (⊤ : ℕ∞) θ := hθ.1
  have hηrange : ∀ y, 0 ≤ η y ∧ η y ≤ 1 := fun y => ⟨(hη.2.2.2.2 y).1,
    (hη.2.2.2.2 y).2.1⟩
  have hθrange : ∀ s, 0 ≤ θ s ∧ θ s ≤ 1 := fun s => (hθ.2.2.2.2.1 s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => η q.1 ^ 2 * θ q.2 ^ 2)
    fun_prop
  · apply HasCompactSupport.intro (hηc.isCompact.prod hθc.isCompact)
    intro q hq
    by_contra hnonzero
    have hy : η q.1 ≠ 0 := by
      intro hz
      exact hnonzero (by simp [caccioppoliSpaceTimeWeight, η, hz])
    have hs : θ q.2 ≠ 0 := by
      intro hz
      exact hnonzero (by simp [caccioppoliSpaceTimeWeight, θ, hz])
    exact hq ⟨subset_tsupport η (Function.mem_support.mpr hy),
      subset_tsupport θ (Function.mem_support.mpr hs)⟩
  · have hclosed : IsClosed (tsupport η ×ˢ tsupport θ) :=
      hηc.isCompact.isClosed.prod hθc.isCompact.isClosed
    have hsupport : Function.support (caccioppoliSpaceTimeWeight x₀ t r ε) ⊆
        tsupport η ×ˢ tsupport θ := by
      intro q hq
      change caccioppoliSpaceTimeWeight x₀ t r ε q ≠ 0 at hq
      have hy : η q.1 ≠ 0 := by
        intro hz
        exact hq (by simp [caccioppoliSpaceTimeWeight, η, hz])
      have hs : θ q.2 ≠ 0 := by
        intro hz
        exact hq (by simp [caccioppoliSpaceTimeWeight, θ, hz])
      exact ⟨subset_tsupport η (Function.mem_support.mpr hy),
        subset_tsupport θ (Function.mem_support.mpr hs)⟩
    have htsSupport : tsupport (caccioppoliSpaceTimeWeight x₀ t r ε) ⊆
        tsupport η ×ˢ tsupport θ := by
      change closure (Function.support (caccioppoliSpaceTimeWeight x₀ t r ε)) ⊆ _
      exact closure_minimal hsupport hclosed
    exact htsSupport.trans (Set.prod_mono hηts (by
      intro s hs
      have htime := hθts hs
      constructor
      · linarith only [hε, htime.1]
      · have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
        have htop : t + 3 * r ^ 2 < t + 4 * r ^ 2 := by nlinarith only [hr2]
        exact htime.2.trans_lt htop))
  · intro q
    change 0 ≤ η q.1 ^ 2 * θ q.2 ^ 2 ∧ η q.1 ^ 2 * θ q.2 ^ 2 ≤ 1
    constructor
    · positivity
    · have hηr := hηrange q.1
      have hθr := hθrange q.2
      have hsη : η q.1 ^ 2 ≤ 1 := by nlinarith only [hηr.1, hηr.2]
      have hsθ : θ q.2 ^ 2 ≤ 1 := by nlinarith only [hθr.1, hθr.2]
      nlinarith only [hsη, hsθ]
  · intro q j
    change (fderiv ℝ (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) q)
      (basisVec j, 0) = _
    rw [fderiv_caccioppoliSpaceTimeWeight_spatial hηsmooth hθsmooth]
    rfl
  · intro q hq
    change 0 ≤
      (fderiv ℝ (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) q) (0, 1)
    rw [fderiv_caccioppoliSpaceTimeWeight_time hηsmooth hθsmooth]
    have hθ' := hθ.2.2.2.2.2.1 q.2 hq
    have hθ' : 0 ≤ deriv θ q.2 := by simpa [θ] using hθ'
    have hcoef : 0 ≤ 2 * η q.1 ^ 2 * θ q.2 :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hθrange q.2).1
    exact mul_nonneg hcoef hθ'
  · intro q hq
    change -(1600 / 199 : ℝ) / r ^ 2 ≤
      (fderiv ℝ (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) q) (0, 1)
    rw [fderiv_caccioppoliSpaceTimeWeight_time hηsmooth hθsmooth]
    have hθ' := hθ.2.2.2.2.2.2 q.2 hq
    have hθ' : deriv θ q.2 ≤ 0 ∧
        |deriv θ q.2| ≤ (800 / 199 : ℝ) / r ^ 2 := by simpa [θ] using hθ'
    have hθabs : |deriv θ q.2| ≤ (800 / 199 : ℝ) / r ^ 2 := hθ'.2
    have hθlower : -(800 / 199 : ℝ) / r ^ 2 ≤ deriv θ q.2 := by
      have habs := (abs_le.mp hθabs).1
      simpa only [neg_div] using habs
    have hfactor : 0 ≤ 2 * η q.1 ^ 2 * θ q.2 := by
      exact mul_nonneg (by positivity) (hθrange q.2).1
    have hprod := mul_le_mul_of_nonneg_left hθlower hfactor
    have hηsq : η q.1 ^ 2 ≤ 1 := by nlinarith only [(hηrange q.1).1, (hηrange q.1).2]
    have hθle : θ q.2 ≤ 1 := (hθrange q.2).2
    have hcoeff : 2 * η q.1 ^ 2 * θ q.2 ≤ 2 := by nlinarith only [hηsq, (hθrange q.2).1, hθle]
    have hscaled : 2 * η q.1 ^ 2 * θ q.2 * (-(800 / 199 : ℝ) / r ^ 2) ≥
        -(1600 / 199 : ℝ) / r ^ 2 := by
      have hn : -(800 / 199 : ℝ) / r ^ 2 ≤ 0 := by
        have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hr2.le
      calc
        2 * η q.1 ^ 2 * θ q.2 * (-(800 / 199 : ℝ) / r ^ 2) ≥
            2 * (-(800 / 199 : ℝ) / r ^ 2) :=
          mul_le_mul_of_nonpos_right hcoeff hn
        _ = -(1600 / 199 : ℝ) / r ^ 2 := by ring
    linarith only [hprod, hscaled]
  · intro q hy hs₁ hs₂
    change η q.1 ^ 2 * θ q.2 ^ 2 = 1
    have heta : η q.1 = 1 := hη.2.2.2.1 q.1 hy
    have htheta : θ q.2 = 1 := hθ.2.2.2.1 q.2 hs₁ hs₂
    simp [heta, htheta]
  · intro q
    have hderiv (j : Fin 3) :
        (fderiv ℝ (caccioppoliSpaceTimeWeight x₀ t r ε) q)
          (basisVec j, 0) =
        2 * η q.1 * (classicalGradient η q.1) j * θ q.2 ^ 2 := by
      change (fderiv ℝ (fun z : Vec3 × ℝ => η z.1 ^ 2 * θ z.2 ^ 2) q)
          (basisVec j, 0) = _
      simpa [classicalGradient_apply] using
        fderiv_caccioppoliSpaceTimeWeight_spatial hηsmooth hθsmooth q j
    simp_rw [hderiv]
    change ∑ j : Fin 3,
      (2 * η q.1 * (classicalGradient η q.1) j * θ q.2 ^ 2) ^ 2 ≤
        (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) * (η q.1 ^ 2 * θ q.2 ^ 2)
    have hgrad := (hη.2.2.2.2 q.1).2.2
    have hgradSq :
        ∑ j : Fin 3, (classicalGradient η q.1 j) ^ 2 ≤ ((400 / 99 : ℝ) / r) ^ 2 := by
      have hnormSq := (sq_le_sq₀ (vec3EuclideanNorm_nonneg _)
        (by positivity : 0 ≤ (400 / 99 : ℝ) / r)).2 hgrad
      have hsum : vec3EuclideanNorm (classicalGradient η q.1) ^ 2 =
          ∑ j : Fin 3, (classicalGradient η q.1 j) ^ 2 := by
        unfold vec3EuclideanNorm
        exact Real.sq_sqrt (Finset.sum_nonneg fun j hj => sq_nonneg _)
      rw [hsum] at hnormSq
      exact hnormSq
    have hηr := hηrange q.1
    have hθr := hθrange q.2
    calc
      ∑ j : Fin 3, (2 * η q.1 * (classicalGradient η q.1 j) * θ q.2 ^ 2) ^ 2 =
          4 * η q.1 ^ 2 * θ q.2 ^ 4 *
            ∑ j : Fin 3, (classicalGradient η q.1 j) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ 4 * η q.1 ^ 2 * θ q.2 ^ 4 * ((400 / 99 : ℝ) / r) ^ 2 := by
        gcongr
      _ ≤ (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) *
          (η q.1 ^ 2 * θ q.2 ^ 2) := by
        have hθsq : θ q.2 ^ 2 ≤ 1 := by nlinarith only [hθr.1, hθr.2]
        have hcoef : 4 * ((400 / 99 : ℝ) / r) ^ 2 =
            4 * (400 / 99 : ℝ) ^ 2 / r ^ 2 := by
          field_simp [ne_of_gt hr]
        have hcoef' : 4 * η q.1 ^ 2 * θ q.2 ^ 4 * ((400 / 99 : ℝ) / r) ^ 2 =
            (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) *
              (η q.1 ^ 2 * θ q.2 ^ 2) * θ q.2 ^ 2 := by
          rw [← hcoef]
          ring
        rw [hcoef']
        have hbase : 0 ≤
            (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) * (η q.1 ^ 2 * θ q.2 ^ 2) := by
          positivity
        calc
          (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) *
                (η q.1 ^ 2 * θ q.2 ^ 2) * θ q.2 ^ 2 ≤
              (4 * (400 / 99 : ℝ) ^ 2 / r ^ 2) *
                (η q.1 ^ 2 * θ q.2 ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hθsq hbase
          _ = _ := by ring


end ESS
