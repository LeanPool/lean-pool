/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicAffineResidual
public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicCaccioppoliNorm
public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicGradientOscillation

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicAffineDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem triadic_cube_ext {d : ℕ} {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) (hindex : Q.index = R.index) : Q = R := by
  cases Q
  cases R
  cases hscale
  cases hindex
  rfl

private theorem h1_grad_hilbert_memLp_two_normalized {d : ℕ}
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (u.grad x)) 2
      (normalizedCubeMeasure Q) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  simpa only [Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply] using
    u.grad_memL2_normalizedCubeMeasure i

private theorem cubeLpNorm_euclidean_eq_toReal_eLpNorm_hilbert {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (F x)) =
      (MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (F x)) 2
        (normalizedCubeMeasure Q)).toReal := by
  simp only [cubeLpNorm, euclideanNorm_eq_norm_ofVec,
    MeasureTheory.eLpNorm_norm _ hF]

private theorem central_descendant_two_children_origin_cube {d : ℕ}
    (k : ℤ) (depth p t : ℕ) :
    centralDescendant
        (centralDescendant
          (centralChild (centralChild (originCube d k))) depth) (2 * p * t) =
      originCube d (k - ((depth + 2 * p * t + 2 : ℕ) : ℤ)) := by
  apply triadic_cube_ext
  · simp only [centralDescendant_scale, centralChild_scale]
    simp [originCube]
    omega
  · funext i
    rw [centralDescendant_index, centralDescendant_index]
    simp [centralChild, originCube]

theorem exists_harmonic_normalized_affine_candidate_error_decay_at_integer_rate
    (d p : ℕ) [NeZero d] (hp : 0 < p) :
    ∃ (depth : ℕ) (C : ℝ), 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∀ (c : ℝ) (e : Vec d) (t : ℕ),
            let R := centralDescendant
              (centralDescendant (centralChild (centralChild Q)) depth) (2 * p * t)
            ∃ c' e',
              HighContrast.normalizedAffineCandidateError R u.toFun c' e' ≤
                C * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
                  HighContrast.normalizedAffineCandidateError Q u.toFun c e := by
  obtain ⟨depth, CO, hCOtop, hCO⟩ :=
    exists_harmonic_gradient_oscillation_decay_at_integer_rate d p hp
  obtain ⟨CK, hCKpos, hCK⟩ :=
    exists_harmonic_centralChild_euclideanGradient_cubeLpNorm_le d
  let B : ℝ := cubeBesovW12LocalPoincareConstant d * CO.toReal * CK
  let C : ℝ := 1 + B
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (cubeBesovW12LocalPoincareConstant_nonneg d)
        ENNReal.toReal_nonneg)
      hCKpos.le
  have hCpos : 0 < C := by
    dsimp [C]
    linarith only [hBnonneg]
  refine ⟨depth, C, hCpos, ?_⟩
  intro Q u hu c e t
  obtain ⟨v, hvfun, hvgrad, hvharmonic⟩ :=
    hu.exists_sub_affine_harmonic Q u c e
  let P : TriadicCube d := centralChild Q
  have hPQ : P ∈ descendantsAtDepth Q 1 := by
    simpa [P] using centralDescendant_mem_descendantsAtDepth Q 1
  let vP : H1Function (openCubeSet P) := v.restrictToOpenSubcube hPQ
  have hvP : WeakPoissonEquationOn (openCubeSet P) vP (fun _ => 0) := by
    simpa [vP, H1Function.restrictToOpenSubcube] using
      hvharmonic.restrict (isOpen_openCubeSet P)
        (openCubeSet_subset_of_mem_descendantsAtDepth hPQ)
  let D : TriadicCube d := centralDescendant (centralChild P) depth
  let R : TriadicCube d := centralDescendant D (2 * p * t)
  let g : Vec d := cubeAverageVec R vP.grad
  have hosc := hCO P vP hvP t
  have hvPmem := h1_grad_hilbert_memLp_two_normalized P vP
  have hoscRhsTop :
      CO * ((3 : ℝ≥0∞)⁻¹) ^ ((2 * p - 1) * t) *
          MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (vP.grad x)) 2
            (normalizedCubeMeasure P) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCOtop (ENNReal.pow_ne_top (by norm_num)))
      hvPmem.eLpNorm_ne_top
  have hoscReal := ENNReal.toReal_mono hoscRhsTop hosc
  have hRmeas : MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (vP.grad x - g)) (normalizedCubeMeasure R) :=
    (MeasureTheory.memLp_iff.2
      (lt_of_le_of_lt hosc (lt_top_iff_ne_top.2 hoscRhsTop))).aestronglyMeasurable
  have hoscCube :
      cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => euclideanNorm (vP.grad x - g)) ≤
        CO.toReal * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
          cubeLpNorm P (2 : ℝ≥0∞)
            (fun x => euclideanNorm (vP.grad x)) := by
    rw [cubeLpNorm_euclidean_eq_toReal_eLpNorm_hilbert R _ hRmeas,
      cubeLpNorm_euclidean_eq_toReal_eLpNorm_hilbert P _ hvPmem.aestronglyMeasurable]
    simpa only [P, D, R, g,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, one_div] using hoscReal
  have hVP :
      cubeLpNorm P (2 : ℝ≥0∞)
          (fun x => euclideanNorm (vP.grad x)) ≤
        CK * (cubeScaleFactor Q)⁻¹ *
          cubeLpNorm Q (2 : ℝ≥0∞) v.toFun := by
    simpa [P, vP] using hCK Q v hvharmonic
  have hparent :
      (cubeScaleFactor Q)⁻¹ * cubeLpNorm Q (2 : ℝ≥0∞) v.toFun =
        HighContrast.normalizedAffineCandidateError Q u.toFun c e := by
    unfold HighContrast.normalizedAffineCandidateError
      HighContrast.normalizedCubeL2Distance
    rw [hvfun]
    simp [cubeBesovScaleWeight, Real.rpow_neg_one]
  have hRQ : openCubeSet R ⊆ openCubeSet Q := by
    exact (centralDescendant_openCubeSet_subset D (2 * p * t)).trans
      ((centralDescendant_openCubeSet_subset (centralChild P) depth).trans
        ((centralDescendant_openCubeSet_subset P 1).trans
          (openCubeSet_subset_of_mem_descendantsAtDepth hPQ)))
  obtain ⟨z, hzfun, hzgrad, _hzharmonic⟩ :=
    hu.exists_sub_affine_harmonic Q u c (e + g)
  let zR : H1Function (openCubeSet R) :=
    z.restrict (isOpen_openCubeSet R) hRQ
  have hzfunR : zR.toFun = fun x => u.toFun x - (c + vecDot (e + g) x) := by
    simpa [zR, H1Function.restrict] using hzfun
  have hzgradR : zR.grad = fun x => vP.grad x - g := by
    funext x
    ext i
    have hzx := congrFun hzgrad x
    have hvx := congrFun hvgrad x
    change z.grad x i = v.grad x i - g i
    rw [hzx, hvx]
    change u.grad x i - (e i + g i) = u.grad x i - e i - g i
    ring
  have hpoincare :=
    HighContrast.normalizedAffineCandidateError_cubeAverage_le_euclideanGradient
      R u.toFun c (e + g) zR hzfunR
  refine ⟨c + cubeAverage R zR.toFun, e + g, ?_⟩
  calc
    HighContrast.normalizedAffineCandidateError R u.toFun
          (c + cubeAverage R zR.toFun) (e + g) ≤
        cubeBesovW12LocalPoincareConstant d *
          cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (zR.grad x)) := hpoincare
    _ = cubeBesovW12LocalPoincareConstant d *
          cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (vP.grad x - g)) := by rw [hzgradR]
    _ ≤ cubeBesovW12LocalPoincareConstant d *
          (CO.toReal * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
            cubeLpNorm P (2 : ℝ≥0∞)
            (fun x => euclideanNorm (vP.grad x))) := by
        exact mul_le_mul_of_nonneg_left hoscCube
          (cubeBesovW12LocalPoincareConstant_nonneg d)
    _ ≤ cubeBesovW12LocalPoincareConstant d *
          (CO.toReal * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
            (CK * (cubeScaleFactor Q)⁻¹ *
              cubeLpNorm Q (2 : ℝ≥0∞) v.toFun)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hVP
            (mul_nonneg ENNReal.toReal_nonneg (by positivity)))
          (cubeBesovW12LocalPoincareConstant_nonneg d)
    _ = B * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
          HighContrast.normalizedAffineCandidateError Q u.toFun c e := by
        rw [← hparent]
        dsimp [B]
        ring
    _ ≤ C * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
          HighContrast.normalizedAffineCandidateError Q u.toFun c e := by
        have hBC : B ≤ C := by
          dsimp [C]
          exact le_add_of_nonneg_left (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBC (by positivity))
          (HighContrast.normalizedAffineCandidateError_nonneg Q u.toFun c e)

/-- Identity-cube specialization of the integer-rate affine improvement.  At
parameter `p`, a descent of `2 * p * t` variable scales gains the power
`(2 * p - 1) * t`, up to a fixed initial depth. -/
theorem exists_identity_harmonic_normalized_affine_candidate_error_decay_at_integer_rate
    (d p : ℕ) [NeZero d] (hp : 0 < p) :
    ∃ (depth : ℕ) (C : ℝ), 0 < C ∧
      ∀ t : ℕ,
        let N := depth + 2 * p * t + 2
        ∀ (k : ℤ) (u : H1Function (openCubeSet (originCube d k))),
          WeakPoissonEquationOn (openCubeSet (originCube d k)) u (fun _ => 0) →
            ∀ (c : ℝ) (e : Vec d), ∃ c' e',
              HighContrast.normalizedAffineCandidateError
                  (originCube d (k - (N : ℤ))) u.toFun c' e' ≤
                C * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) *
                  HighContrast.normalizedAffineCandidateError
                    (originCube d k) u.toFun c e := by
  obtain ⟨depth, C, hC, hdecay⟩ :=
    exists_harmonic_normalized_affine_candidate_error_decay_at_integer_rate
      d p hp
  refine ⟨depth, C, hC, ?_⟩
  intro t
  dsimp only
  intro k u hu c e
  obtain ⟨c', e', hcandidate⟩ := hdecay (originCube d k) u hu c e t
  refine ⟨c', e', ?_⟩
  rw [← central_descendant_two_children_origin_cube
    (d := d) k depth p t]
  exact hcandidate

/-- Identity-harmonic functions admit a dimension-only affine improvement on
a fixed deeper centered cube. -/
theorem exists_identity_harmonic_normalized_affine_candidate_error_decay
    (d : ℕ) [NeZero d] :
    ∃ N : ℕ, 0 < N ∧
      ∀ (k : ℤ) (u : H1Function (openCubeSet (originCube d k))),
        WeakPoissonEquationOn (openCubeSet (originCube d k)) u (fun _ => 0) →
          ∀ (c : ℝ) (e : Vec d), ∃ c' e',
            HighContrast.normalizedAffineCandidateError
                (originCube d (k - (N : ℤ))) u.toFun c' e' ≤
              (1 / 8 : ℝ) * HighContrast.normalizedAffineCandidateError
                (originCube d k) u.toFun c e := by
  obtain ⟨depth, C, hCpos, hdecay⟩ :=
    exists_harmonic_normalized_affine_candidate_error_decay_at_integer_rate d 1
      (by norm_num)
  have heps : 0 < (1 : ℝ) / (8 * C) := by positivity
  obtain ⟨t, ht⟩ :=
    exists_pow_lt_of_lt_one heps (by norm_num : (1 : ℝ) / 3 < 1)
  let N : ℕ := depth + 2 * t + 2
  refine ⟨N, by omega, ?_⟩
  intro k u hu c e
  obtain ⟨c', e', hcandidate⟩ :=
    hdecay (originCube d k) u hu c e t
  have hcandidate' :
      HighContrast.normalizedAffineCandidateError
          (centralDescendant
            (centralDescendant
              (centralChild (centralChild (originCube d k))) depth) (2 * t))
          u.toFun c' e' ≤
        C * ((1 : ℝ) / 3) ^ t *
          HighContrast.normalizedAffineCandidateError
            (originCube d k) u.toFun c e := by
    simpa using hcandidate
  have hfactor : C * ((1 : ℝ) / 3) ^ t ≤ (1 / 8 : ℝ) := by
    calc
      C * ((1 : ℝ) / 3) ^ t ≤ C * ((1 : ℝ) / (8 * C)) :=
        (mul_lt_mul_of_pos_left ht hCpos).le
      _ = (1 / 8 : ℝ) := by field_simp [hCpos.ne']
  have hgeometry : centralDescendant
        (centralDescendant
          (centralChild (centralChild (originCube d k))) depth) (2 * t) =
      originCube d (k - (N : ℤ)) := by
    simpa [N] using
      central_descendant_two_children_origin_cube (d := d) k depth 1 t
  refine ⟨c', e', ?_⟩
  rw [← hgeometry]
  calc
    HighContrast.normalizedAffineCandidateError
          (centralDescendant
            (centralDescendant
              (centralChild (centralChild (originCube d k))) depth) (2 * t))
          u.toFun c' e' ≤
        C * ((1 : ℝ) / 3) ^ t *
          HighContrast.normalizedAffineCandidateError
            (originCube d k) u.toFun c e := hcandidate'
    _ ≤ (1 / 8 : ℝ) * HighContrast.normalizedAffineCandidateError
          (originCube d k) u.toFun c e :=
      mul_le_mul_of_nonneg_right hfactor
        (HighContrast.normalizedAffineCandidateError_nonneg
          (originCube d k) u.toFun c e)

end CubeCalderonZygmund

end

end HCPolySupport
