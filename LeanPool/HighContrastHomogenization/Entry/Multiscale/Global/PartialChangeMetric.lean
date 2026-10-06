/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.Containment

/-!
# High-contrast homogenization: Entry.Multiscale.Global.PartialChangeMetric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The metric part of a partial geometry change

The projective-metric bookkeeping of a partial geometry change, serving `p.global.selection`:
the geometry update moves the current metric a distance exactly `ε` towards the target when the
target is not reached, and the residual distance to the target drops by `ε`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockLogDet blockScale matPow matSqrt
  matSqrt_eq matSqrt_spec specBound specBound_le specBound_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Scalar order bounds for a positive definite matrix and one of its fractional powers.
The extremal eigenvalues control all spectral inequalities for the power. -/
private theorem normalizedMat_power_order_characterization {d : ℕ} [NeZero d]
    (N : Mat d) (hNPD : N.PosDef) (θ : ℝ) (hθ1_nonneg : 0 ≤ 1 - θ) :
    (∀ t : ℝ, MatLoewnerLE (t • matPow θ N) N ↔ t ≤ specMin N ^ (1 - θ)) ∧
      (∀ t : ℝ, MatLoewnerLE N (t • matPow θ N) ↔ specBound N ^ (1 - θ) ≤ t) := by
  open scoped MatrixOrder in
  classical
  have hcont_rpow : ∀ θ' : ℝ, ContinuousOn (fun x : ℝ => x ^ θ') (spectrum ℝ N) := by
    intro θ'
    exact continuousOn_id.rpow_const fun x hx => by
      left
      obtain ⟨i, rfl⟩ := hNPD.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact ne_of_gt (hNPD.eigenvalues_pos i)
  have hcfc_id : cfc (fun x : ℝ => x) N = N := by
    simpa using! cfc_id ℝ N hNPD.isHermitian
  have hHermPow : (matPow θ N).IsHermitian := (Geometry.matPow_posDef hNPD θ).isHermitian
  have hHermSmul : ∀ t : ℝ, (t • matPow θ N).IsHermitian := by
    intro t
    show Matrix.conjTranspose (t • matPow θ N) = t • matPow θ N
    rw [Matrix.conjTranspose_smul, hHermPow]
    simp
  constructor
  · intro t
    have hcmul : t • matPow θ N = cfc (fun x : ℝ => t * x ^ θ) N := by
      rw [show matPow θ N = cfc (fun x : ℝ => x ^ θ) N from rfl,
        ← cfc_const_mul t (fun x : ℝ => x ^ θ) N (hcont_rpow θ)]
    have hmatrixOrder : (t • matPow θ N ≤ N) ↔ ∀ x ∈ spectrum ℝ N, t * x ^ θ ≤ x := by
      have hraw := cfc_le_iff (fun x : ℝ => t * x ^ θ) (fun x : ℝ => x) N
        (continuousOn_const.mul (hcont_rpow θ)) continuousOn_id (ha := hNPD.isHermitian)
      rw [hcfc_id, ← hcmul] at hraw
      exact hraw
    rw [← BlockGeometricMean.matLE_iff (hHermSmul t) hNPD.isHermitian, hmatrixOrder]
    constructor
    · intro hall
      obtain ⟨i0, hi0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
        hNPD.isHermitian.eigenvalues
      have hxi0 : hNPD.isHermitian.eigenvalues i0 ∈ spectrum ℝ N := by
        rw [hNPD.isHermitian.spectrum_real_eq_range_eigenvalues]
        exact Set.mem_range_self i0
      have hb := hall _ hxi0
      have hxpos : 0 < hNPD.isHermitian.eigenvalues i0 := hNPD.eigenvalues_pos i0
      have h1 : hNPD.isHermitian.eigenvalues i0 ^ (1 - θ) =
          hNPD.isHermitian.eigenvalues i0 / hNPD.isHermitian.eigenvalues i0 ^ θ := by
        rw [Real.rpow_sub hxpos, Real.rpow_one]
      have hstep : t ≤ hNPD.isHermitian.eigenvalues i0 ^ (1 - θ) := by
        rw [h1, le_div_iff₀ (Real.rpow_pos_of_pos hxpos θ)]
        linarith only [hb]
      rw [Geometry.specMin_eq_finset_inf_eigenvalues hNPD, hi0.2]
      exact hstep
    · intro ht x hx
      rw [hNPD.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      have hxpos : 0 < hNPD.isHermitian.eigenvalues i := hNPD.eigenvalues_pos i
      have hSm : specMin N ≤ hNPD.isHermitian.eigenvalues i := by
        rw [Geometry.specMin_eq_finset_inf_eigenvalues hNPD]
        exact Finset.inf'_le _ (Finset.mem_univ i)
      have hpow : specMin N ^ (1 - θ) ≤ hNPD.isHermitian.eigenvalues i ^ (1 - θ) :=
        Real.rpow_le_rpow (Geometry.specMin_pos hNPD).le hSm hθ1_nonneg
      have ht' : t ≤ hNPD.isHermitian.eigenvalues i ^ (1 - θ) := le_trans ht hpow
      have h1 : hNPD.isHermitian.eigenvalues i ^ (1 - θ) =
          hNPD.isHermitian.eigenvalues i / hNPD.isHermitian.eigenvalues i ^ θ := by
        rw [Real.rpow_sub hxpos, Real.rpow_one]
      rw [h1, le_div_iff₀ (Real.rpow_pos_of_pos hxpos θ)] at ht'
      linarith only [ht']
  · intro t
    have hcmul : t • matPow θ N = cfc (fun x : ℝ => t * x ^ θ) N := by
      rw [show matPow θ N = cfc (fun x : ℝ => x ^ θ) N from rfl,
        ← cfc_const_mul t (fun x : ℝ => x ^ θ) N (hcont_rpow θ)]
    have hmatrixOrder : (N ≤ t • matPow θ N) ↔ ∀ x ∈ spectrum ℝ N, x ≤ t * x ^ θ := by
      have hraw := cfc_le_iff (fun x : ℝ => x) (fun x : ℝ => t * x ^ θ) N
        continuousOn_id (continuousOn_const.mul (hcont_rpow θ)) (ha := hNPD.isHermitian)
      rw [hcfc_id, ← hcmul] at hraw
      exact hraw
    rw [← BlockGeometricMean.matLE_iff hNPD.isHermitian (hHermSmul t), hmatrixOrder]
    constructor
    · intro hall
      obtain ⟨j0, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        hNPD.isHermitian.eigenvalues
      have hxj0 : hNPD.isHermitian.eigenvalues j0 ∈ spectrum ℝ N := by
        rw [hNPD.isHermitian.spectrum_real_eq_range_eigenvalues]
        exact Set.mem_range_self j0
      have hb := hall _ hxj0
      have hxpos : 0 < hNPD.isHermitian.eigenvalues j0 := hNPD.eigenvalues_pos j0
      have h1 : hNPD.isHermitian.eigenvalues j0 ^ (1 - θ) =
          hNPD.isHermitian.eigenvalues j0 / hNPD.isHermitian.eigenvalues j0 ^ θ := by
        rw [Real.rpow_sub hxpos, Real.rpow_one]
      have hstep : hNPD.isHermitian.eigenvalues j0 ^ (1 - θ) ≤ t := by
        rw [h1, div_le_iff₀ (Real.rpow_pos_of_pos hxpos θ)]
        linarith only [hb]
      rw [Geometry.specBound_eq_finset_sup_eigenvalues hNPD, hj0.2]
      exact hstep
    · intro ht x hx
      rw [hNPD.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      have hxpos : 0 < hNPD.isHermitian.eigenvalues i := hNPD.eigenvalues_pos i
      have hSm : hNPD.isHermitian.eigenvalues i ≤ specBound N := by
        rw [Geometry.specBound_eq_finset_sup_eigenvalues hNPD]
        exact Finset.le_sup' _ (Finset.mem_univ i)
      have hpow : hNPD.isHermitian.eigenvalues i ^ (1 - θ) ≤ specBound N ^ (1 - θ) :=
        Real.rpow_le_rpow hxpos.le hSm hθ1_nonneg
      have ht' : hNPD.isHermitian.eigenvalues i ^ (1 - θ) ≤ t := le_trans hpow ht
      have h1 : hNPD.isHermitian.eigenvalues i ^ (1 - θ) =
          hNPD.isHermitian.eigenvalues i / hNPD.isHermitian.eigenvalues i ^ θ := by
        rw [Real.rpow_sub hxpos, Real.rpow_one]
      rw [h1, div_le_iff₀ (Real.rpow_pos_of_pos hxpos θ)] at ht'
      linarith only [ht']

/-- `p.global.selection`: the metric part of a partial geometry change. `m₊ = geometryUpdate ε m
m⋆` with
`m⋆ = m(𝐀_{n+2L,q})` not reached (`d_pr([m],[m⋆]) > ε`, so `d_pr([m₊],[m⋆]) = d_pr([m],[m⋆]) - ε`
by `Geometry.projectiveDistance_geometryUpdate_eq_min`), `𝐀_{n+2L,q} ≤ 𝐀_{k,q}`
(`explicitCanonicalMetric_projectiveDistance_le_logDet`), and the bridge sandwich
`e.global.selection.geometry.comparison`
(`explicitCanonicalMetric_projectiveDistance_le_of_deltaSandwich`),
glued by `projectiveDistance_triangle` and the symmetry of `projectiveDistance`. -/
theorem partial_change_metric {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (ε δ : ℝ)
    (m : Mat d) (k n : ℤ) (L : ℕ) (hm : m.PosDef) (hε : 0 < ε) (hδ : δ ∈ Set.Ico (0 : ℝ) 1)
    (hsym : ∀ j, IsSymmetricBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))
    (hpos : ∀ j, Book.Ch02.BlockPosDef (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))
    (hsymP : IsSymmetricBlockMat
      (adaptedMean P (Geometry.explicitRoundedGrid jStar
        (geometryUpdate ε m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2
            * (L : ℤ))))))
        (n + L)))
    (hposP : Book.Ch02.BlockPosDef
      (adaptedMean P (Geometry.explicitRoundedGrid jStar
        (geometryUpdate ε m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2
            * (L : ℤ))))))
        (n + L)))
    (hmono : BlockMatLoewnerLE (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L
      : ℤ)))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar m) k))
    (hfar : ε < projectiveDistance m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L
        : ℤ)))))
    (hbr₁ : BlockMatLoewnerLE
      (blockScale (1 - δ) (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar
        (geometryUpdate ε m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2
            * (L : ℤ))))))
        (n + L)))
    (hbr₂ : BlockMatLoewnerLE
      (adaptedMean P (Geometry.explicitRoundedGrid jStar
        (geometryUpdate ε m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2
            * (L : ℤ))))))
        (n + L))
      (blockScale (1 + δ) (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L :
        ℤ))))) :
    projectiveDistance
        (geometryUpdate ε m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2
            * (L : ℤ)))))
        (explicitCanonicalMetric
          (adaptedMean P (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n
                + 2 * (L : ℤ))))))
            (n + L))) -
      projectiveDistance m (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid
        jStar m) k)) ≤
      -ε + 1 / 2 * detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ)) +
        1 / 2 * Real.log ((1 + δ) / (1 - δ))  := by
  classical
  open scoped MatrixOrder in
  ·
    set F2L := adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) with hF2L_def
    set Fk := adaptedMean P (Geometry.explicitRoundedGrid jStar m) k with hFk_def
    set mStar := explicitCanonicalMetric F2L with hmStar_def
    set mPlus := geometryUpdate ε m mStar with hmPlus_def
    set Fhost := adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + L) with hFhost_def
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      have htriv : ∀ A B : Mat 0, MatLoewnerLE A B := by
        intro A B x
        simp [vecDot]
      have hb0 : specBound (normalizedMat m mStar) = 0 :=
        le_antisymm (specBound_le le_rfl (htriv _ _)) (specBound_nonneg _)
      have hs0 : specMin (normalizedMat m mStar) = 0 := by
        have hset : {t : ℝ | MatLoewnerLE (t • (1 : Mat 0)) (normalizedMat m mStar)} = Set.univ :=
          Set.eq_univ_of_forall fun t => htriv _ _
        simp only [specMin, hset, Real.sSup_univ]
      have hMS0 : projectiveDistance m mStar = 0 := by
        simp only [projectiveDistance, hb0, hs0]
        norm_num
      exfalso
      rw [hMS0] at hfar
      linarith only [hfar, hε]
    · letI : NeZero d := ⟨hdpos.ne'⟩
      have hF2Lsym : IsSymmetricBlockMat F2L := hsym (n + 2 * (L : ℤ))
      have hF2Lpos : Book.Ch02.BlockPosDef F2L := hpos (n + 2 * (L : ℤ))
      have hFksym : IsSymmetricBlockMat Fk := hsym k
      have hFkpos : Book.Ch02.BlockPosDef Fk := hpos k
      have hStarPD : mStar.PosDef := explicitCanonicalMetric_posDef F2L hF2Lsym hF2Lpos
      have hFkPD : (explicitCanonicalMetric Fk).PosDef := explicitCanonicalMetric_posDef Fk
        hFksym hFkpos
      have hFhostPD : (explicitCanonicalMetric Fhost).PosDef := explicitCanonicalMetric_posDef
        Fhost hsymP hposP
      have hne : ¬ ProjectiveEq m mStar := by
        intro hEq
        have hz := (Geometry.projectiveDistance_eq_zero_iff hm hStarPD).2 hEq
        linarith only [hfar, hz, hε]
      have hmPlusPD : mPlus.PosDef := by
        rw [hmPlus_def]; exact Geometry.geometryUpdate_posDef hm hStarPD ε
      have hdMSpos : 0 < projectiveDistance m mStar := lt_trans hε hfar
      set N := normalizedMat m mStar with hN_def
      have hNPD : N.PosDef := by rw [hN_def]; exact Geometry.normalizedMat_posDef hm hStarPD
      set θ := min (ε / projectiveDistance m mStar) 1 with hθ_def
      have hθ_eq : θ = ε / projectiveDistance m mStar := by
        rw [hθ_def]; exact min_eq_left ((div_le_one hdMSpos).mpr hfar.le)
      have hθmul : θ * projectiveDistance m mStar = ε := by
        rw [hθ_eq, div_mul_cancel₀ ε hdMSpos.ne']
      have hθ_mem : θ ∈ Set.Ioc (0 : ℝ) 1 := by
        rw [hθ_def]; exact Geometry.geometryUpdate_exponent_mem_Ioc hm hStarPD hne hε
      have hθ_pos : 0 < θ := hθ_mem.1
      have hθ_lt1 : θ < 1 := by
        rw [hθ_eq, div_lt_one hdMSpos]; exact hfar
      have hθ1_nonneg : (0 : ℝ) ≤ 1 - θ := by linarith only [hθ_lt1]
      -- basic square-root algebra for `m`
      have hSmPD : (matSqrt m).PosDef := by
        rw [matSqrt_eq_cfc_sqrt hm.posSemidef]; exact Geometry.posDef_sqrt hm
      have hSS : matSqrt m * matSqrt m = m := (matSqrt_spec hm.posSemidef).2
      have hTm_eq : matSqrt m⁻¹ = (matSqrt m)⁻¹ := by
        have hinv : (matSqrt m)⁻¹ * (matSqrt m)⁻¹ = m⁻¹ := by
          rw [← Matrix.mul_inv_rev, hSS]
        exact matSqrt_eq hm.inv.posSemidef hSmPD.inv.posSemidef hinv
      have hSmDet : IsUnit (matSqrt m).det := (Matrix.isUnit_iff_isUnit_det _).mp hSmPD.isUnit
      have hST : matSqrt m * matSqrt m⁻¹ = 1 := by
        rw [hTm_eq]; exact Matrix.mul_nonsing_inv (matSqrt m) hSmDet
      have hTS : matSqrt m⁻¹ * matSqrt m = 1 := by
        rw [hTm_eq]; exact Matrix.nonsing_inv_mul (matSqrt m) hSmDet
      have hTPD : (matSqrt m⁻¹).PosDef := Geometry.matSqrt_inv_posDef hm
      have hTherm : matTranspose (matSqrt m⁻¹) = matSqrt m⁻¹ := by
        simpa [matTranspose] using Geometry.transpose_eq_of_isHermitian hTPD.isHermitian
      have hTdet : IsUnit (matSqrt m⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).mp hTPD.isUnit
      have hmPlus_unfold : mPlus = matSqrt m * matPow θ N * matSqrt m := by
        rw [hmPlus_def, geometryUpdate, ite_eq_right hne, ← hθ_def, ← hN_def]
      have hTmStarT : matTranspose (matSqrt m⁻¹) * mStar * matSqrt m⁻¹ = N := by
        rw [hTherm, hN_def, normalizedMat]
      have hcross : ∀ t : ℝ,
          matTranspose (matSqrt m⁻¹) * (t • mPlus) * matSqrt m⁻¹ = t • matPow θ N := by
        intro t
        rw [hTherm, hmPlus_unfold, Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        have e1 : matSqrt m⁻¹ * (matSqrt m * matPow θ N * matSqrt m) * matSqrt m⁻¹
            = (matSqrt m⁻¹ * matSqrt m) * matPow θ N * (matSqrt m * matSqrt m⁻¹) := by
          noncomm_ring
        rw [e1, hTS, hST, Matrix.one_mul, Matrix.mul_one]
      have hcongrLow : ∀ t : ℝ,
          MatLoewnerLE (t • mPlus) mStar ↔ MatLoewnerLE (t • matPow θ N) N := by
        intro t
        have hiff := Geometry.matLoewnerLE_congr_iff_of_isUnit_det
          (A := t • mPlus) (B := mStar) (P := matSqrt m⁻¹) hTdet
        rw [hcross t, hTmStarT] at hiff
        exact hiff
      have hcongrUp : ∀ t : ℝ,
          MatLoewnerLE mStar (t • mPlus) ↔ MatLoewnerLE N (t • matPow θ N) := by
        intro t
        have hiff := Geometry.matLoewnerLE_congr_iff_of_isUnit_det
          (A := mStar) (B := t • mPlus) (P := matSqrt m⁻¹) hTdet
        rw [hcross t, hTmStarT] at hiff
        exact hiff
      have ⟨hkeyLow, hkeyUp⟩ :=
        normalizedMat_power_order_characterization N hNPD θ hθ1_nonneg
      have hfullLow : ∀ t : ℝ, MatLoewnerLE (t • mPlus) mStar ↔ t ≤ specMin N ^ (1 - θ) :=
        fun t => (hcongrLow t).trans (hkeyLow t)
      have hfullUp : ∀ t : ℝ, MatLoewnerLE mStar (t • mPlus) ↔ specBound N ^ (1 - θ) ≤ t :=
        fun t => (hcongrUp t).trans (hkeyUp t)
      have hSpecMinEq : specMin (normalizedMat mPlus mStar) = specMin N ^ (1 - θ) := by
        apply le_antisymm
        · exact (hfullLow _).1
            ((Geometry.matLoewnerLE_smul_left_iff_specMin hmPlusPD hStarPD _).2 le_rfl)
        · exact (Geometry.matLoewnerLE_smul_left_iff_specMin hmPlusPD hStarPD _).1
            ((hfullLow _).2 le_rfl)
      have hSpecBoundEq : specBound (normalizedMat mPlus mStar) = specBound N ^ (1 - θ) := by
        apply le_antisymm
        · exact (Geometry.matLoewnerLE_right_iff_specBound_le hmPlusPD hStarPD _).1
            ((hfullUp _).2 le_rfl)
        · exact (hfullUp _).1
            ((Geometry.matLoewnerLE_right_iff_specBound_le hmPlusPD hStarPD _).2 le_rfl)
      obtain ⟨i0e, j0e, hi0e, hj0e, hije⟩ := Geometry.spectral_extrema_attained hNPD
      have hNL : specMin N ≤ specBound N := by rw [hi0e, hj0e]; exact (hije j0e).1
      have hSBpos : 0 < specBound N := lt_of_lt_of_le (Geometry.specMin_pos hNPD) hNL
      have hbase : projectiveDistance m mStar = 1 / 2 * Real.log (specBound N / specMin N) := by
        simp only [hN_def, projectiveDistance]
      have hfinal : (1 - θ) * projectiveDistance m mStar = projectiveDistance m mStar - ε := by
        rw [sub_mul, one_mul, hθmul]
      have hcollinear : projectiveDistance mPlus mStar = projectiveDistance m mStar - ε := by
        obtain ⟨Lx, Ux, hLxpos, hLUx, hlowx, hupx, hLxdef, hUxdef, hdistx⟩ :=
          Geometry.projectiveDistance_eq_log_relative_spread hmPlusPD hStarPD
        calc projectiveDistance mPlus mStar
            = 1 / 2 * Real.log (Ux / Lx) := hdistx
          _ = 1 / 2 * Real.log (specBound N ^ (1 - θ) / specMin N ^ (1 - θ)) := by
                rw [hLxdef, hUxdef, hSpecMinEq, hSpecBoundEq]
          _ = 1 / 2 * Real.log ((specBound N / specMin N) ^ (1 - θ)) := by
                rw [Real.div_rpow (specBound_nonneg N) (Geometry.specMin_pos hNPD).le]
          _ = 1 / 2 * ((1 - θ) * Real.log (specBound N / specMin N)) := by
                rw [Real.log_rpow (div_pos hSBpos (Geometry.specMin_pos hNPD))]
          _ = (1 - θ) * (1 / 2 * Real.log (specBound N / specMin N)) := by ring
          _ = (1 - θ) * projectiveDistance m mStar := by rw [hbase]
          _ = projectiveDistance m mStar - ε := hfinal
      have htri1 : projectiveDistance mPlus (explicitCanonicalMetric Fhost) ≤
          projectiveDistance mPlus mStar + projectiveDistance mStar (explicitCanonicalMetric
            Fhost) :=
        Geometry.projectiveDistance_triangle hmPlusPD hStarPD hFhostPD
      have hsand : projectiveDistance mStar (explicitCanonicalMetric Fhost) ≤
          1 / 2 * Real.log ((1 + δ) / (1 - δ)) :=
        explicitCanonicalMetric_projectiveDistance_le_of_deltaSandwich F2L Fhost δ hδ hF2Lsym
          hF2Lpos
          hsymP hposP hbr₁ hbr₂
      have htri2 : projectiveDistance m mStar ≤
          projectiveDistance m (explicitCanonicalMetric Fk) + projectiveDistance
            (explicitCanonicalMetric Fk) mStar :=
        Geometry.projectiveDistance_triangle hm hFkPD hStarPD
      have hlog : projectiveDistance (explicitCanonicalMetric Fk) mStar ≤
          1 / 2 * detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ)) := by
        have hraw := explicitCanonicalMetric_projectiveDistance_le_logDet Fk F2L hFksym hFkpos
          hF2Lsym hF2Lpos hmono
        rw [← hmStar_def] at hraw
        have heq : detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ))
            = blockLogDet Fk - blockLogDet F2L := by
          simp only [detIncrement, ← hFk_def, ← hF2L_def]
        rw [heq]
        exact hraw
      linarith only [htri1, hcollinear, hsand, htri2, hlog]

end

end HCPolySupport.HighContrast.Multiscale
