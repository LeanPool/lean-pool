/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AffineSobolevPullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ScalarMaximizerExistence
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# High-contrast homogenization: Entry.Response.Kernel.ReferenceCubeAveragePullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pullback to the reference cube

For the linear change of variables `x = q y`, this file transports the Lebesgue measure, cube
averages and the doubled-field integrability along the pullback, and identifies the depth-`n`
descendant cells of the reference cube, indexed by the triadic index box, with the image of the
corresponding translated origin cubes. It records the injectivity and measurability the transport
needs, the volume of a translated cube, and the metric comparison between the rounded and unrounded
grid bounding the pullback's operator norm. It also supplies, for the recentred coefficient
families `a_-` and `a_+`, the existence of a scalar canonical response maximizer on every aligned
subcell of the terminal generation.  The module serves the manuscript's `p.response.transfer`.
-/

section
/-!
## HC bridge II (B5): pullback to the reference cube

Paper `p.response.transfer`. Depends on `ScaleAverageSeminorm.lean` (B4).
-/

open HCPolySupport.HighContrast (matSqrt)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## B5. Pullback to the reference cube: the eccentricity-free constant
(`p.response.transfer`).  Old: `adaptedWeakSeminorm_affinePullback_le`
(`HCPoly/Provider/Response/AdaptedWeakTransport.lean`),
`explicitRoundedGrid_metricFrobenius_product_le` (`AdaptedWeakProduct.lean`), and the slotwise
bridges `ofReal_partialSeminorm_metricPullback_fst_le_separate`/`_snd_`) to the
CG seminorm `cubeBesovNegativeVectorPartialSeminorm`
(`Deterministic/WeakNormInterfaces/Definitions.lean`). -/

/-! ### HELPERS — all CLOSED, new declarations to be pasted alongside the theorems. -/

theorem opNorm_inv_pos {m : Mat d} (hm : m.PosDef) : 0 < ‖m⁻¹‖ := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hv : (fun _ => (1 : ℝ) : Vec d) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hd⟩
    norm_num at this
  have h1 := Geometry.one_le_opNorm_mul_opNorm_inv hm hv
  rcases (norm_nonneg (m⁻¹)).lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at h1; linarith only [h1]

omit [NeZero d] in
theorem inverseNormLE_unroundedGrid {m : Mat d} (hm : m.PosDef) :
    Geometry.InverseNormLE (Geometry.unroundedGrid m) 1 := by
  intro v
  have h := Geometry.vecNormSq_le_vecNormSq_mulVec_of_le_dotProduct
    (M := Geometry.unroundedGrid m) (c := 1) zero_le_one
    (fun x => by rw [one_mul]; exact Geometry.vecNormSq_le_dotProduct_unroundedGrid hm x) v
  simpa [Geometry.matVecMul_eq_mulVec] using h

omit [NeZero d] in
theorem isUnit_det_unroundedGrid {m : Mat d} (hm : m.PosDef) :
    IsUnit (Geometry.unroundedGrid m).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (inverseNormLE_unroundedGrid hm).isUnit

omit [NeZero d] in
theorem opNorm_unroundedGrid_inv_le {m : Mat d} (hm : m.PosDef) :
    ‖(Geometry.unroundedGrid m)⁻¹‖ ≤ 1 := by
  have hinv := inverseNormLE_unroundedGrid hm
  have hdet := isUnit_det_unroundedGrid hm
  refine Geometry.opNorm_le_of_vecNormSq_mulVec_le zero_le_one fun w => ?_
  have h := hinv ((Geometry.unroundedGrid m)⁻¹ *ᵥ w)
  rw [Geometry.matVecMul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec] at h
  exact h

theorem norm_one_mat : ‖(1 : Mat d)‖ = 1 := by
  rw [← Book.Ch02.matrixOperatorNorm_eq_l2_opNorm, Book.Ch02.matrixOperatorNorm_one]

theorem opNorm_metric_product_le {l : ℕ} (hl : 2 * d ≤ 3 ^ l) {m : Mat d} (hm : m.PosDef) :
    ‖(Geometry.unroundedGrid m)⁻¹ * Geometry.explicitRoundedGrid l m‖ *
        ‖(Geometry.explicitRoundedGrid l m)⁻¹ * Geometry.unroundedGrid m‖ ≤ 3 := by
  set q := Geometry.explicitRoundedGrid l m with hq
  set L := Geometry.unroundedGrid m with hL
  set E := q - L with hE
  have hLdet : IsUnit L.det := isUnit_det_unroundedGrid hm
  have hqdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Geometry.isUnit_roundedGrid hl hm)
  have hEle : ‖E‖ ≤ 1 / 2 :=
    (Geometry.opNorm_roundingError_le l m).trans (Geometry.mul_inv_pow_le_half hl)
  set B := L⁻¹ * E with hB
  have hBle : ‖B‖ ≤ 1 / 2 := by
    have h := (norm_mul_le L⁻¹ E).trans
      (mul_le_mul (opNorm_unroundedGrid_inv_le hm) hEle (norm_nonneg _) zero_le_one)
    simpa using h
  have hfac : L⁻¹ * q = 1 + B := by
    have hsplit : q = L + E := by rw [hE]; abel
    rw [hsplit, Matrix.mul_add, Matrix.nonsing_inv_mul _ hLdet]
  have h1 : ‖L⁻¹ * q‖ ≤ 3 / 2 := by
    rw [hfac]
    calc ‖(1 : Mat d) + B‖ ≤ ‖(1 : Mat d)‖ + ‖B‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by rw [norm_one_mat]; linarith only [hBle]
  have hBlt : ‖-B‖ < 1 := by rw [norm_neg]; linarith only [hBle]
  set T : Mat d := tsum (fun i : ℕ => (-B) ^ i) with hT
  have hTB : T * (1 + B) = 1 := by
    have h := geom_series_mul_neg (-B) hBlt
    rwa [sub_neg_eq_add] at h
  have hkey : (1 + B) * (q⁻¹ * L) = 1 := by
    rw [← hfac, Matrix.mul_assoc, ← Matrix.mul_assoc q, Matrix.mul_nonsing_inv q hqdet,
      Matrix.one_mul, Matrix.nonsing_inv_mul L hLdet]
  have hTeq : q⁻¹ * L = T := by
    calc q⁻¹ * L = 1 * (q⁻¹ * L) := (Matrix.one_mul _).symm
      _ = (T * (1 + B)) * (q⁻¹ * L) := by rw [hTB]
      _ = T * ((1 + B) * (q⁻¹ * L)) := Matrix.mul_assoc _ _ _
      _ = T := by rw [hkey, Matrix.mul_one]
  have h2 : ‖q⁻¹ * L‖ ≤ 2 := by
    rw [hTeq]
    have hg := tsum_geometric_le_of_norm_lt_one (-B) hBlt
    rw [norm_one_mat, norm_neg] at hg
    have hpos : (0 : ℝ) < 1 - ‖B‖ := by linarith only [hBle]
    have hinv2 : (1 - ‖B‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith only [hBle]
    calc ‖T‖ ≤ 1 - 1 + (1 - ‖B‖)⁻¹ := hg
      _ ≤ 2 := by linarith only [hinv2]
  calc ‖L⁻¹ * q‖ * ‖q⁻¹ * L‖ ≤ (3 / 2) * 2 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 3 := by norm_num

/-- `|q^T m^{-1/2}|_F |q^{-1} m^{1/2}|_F ≤ 3 d²` for `q = explicitRoundedGrid l m`
(old `AdaptedWeakProduct.lean`; paper `p.response.transfer`, `≤ 3` in operator norm).

The old `51/50 · d²` needed `kZero d ≤ l`; on the current carrier only the
repo-standing `2 * d ≤ 3 ^ l` (`HCPoly/Entry/Geometry/RoundedGridBasic.lean`) is available, which
gives
the paper's own constant `3` instead. -/
theorem explicitRoundedGrid_metricFrobenius_product_le (l : ℕ) (hl : 2 * d ≤ 3 ^ l)
    (m : Mat d) (hm : m.PosDef) :
    Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (matTranspose (Geometry.explicitRoundedGrid l m)
      * (matSqrt m)⁻¹)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq ((Geometry.explicitRoundedGrid l m)⁻¹ *
          matSqrt m)) ≤
      3 * (d : ℝ) ^ 2 := by
  set q := Geometry.explicitRoundedGrid l m with hq
  set S := matSqrt m with hSdef
  set L := Geometry.unroundedGrid m with hL
  set a := Real.sqrt ‖m⁻¹‖ with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (opNorm_inv_pos hm)
  have : Invertible a := invertibleOfNonzero hapos.ne'
  have hScfc : S = CFC.sqrt m := matSqrt_eq_cfc_sqrt hm.posSemidef
  have hLS : L = a • S := by rw [hScfc]; rfl
  have hSposdef : S.PosDef := by rw [hScfc]; exact Geometry.posDef_sqrt hm
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).mp hSposdef.isUnit
  have hSsymm : Sᵀ = S := by
    rw [hScfc]; ext i j; exact Geometry.sqrt_apply_comm hm i j
  have hqsymm : qᵀ = q := Geometry.explicitRoundedGrid_transpose hm
  have hLsymm : Lᵀ = L := by rw [hLS, Matrix.transpose_smul, hSsymm]
  have hLdet : IsUnit L.det := isUnit_det_unroundedGrid hm
  have hSinv : S⁻¹ = a • L⁻¹ := by
    rw [hLS, Matrix.inv_smul S a hSdet, invOf_eq_inv, smul_smul,
      mul_inv_cancel₀ hapos.ne', one_smul]
  have hSeq : S = a⁻¹ • L := by
    rw [hLS, smul_smul, inv_mul_cancel₀ hapos.ne', one_smul]
  have hAform : matTranspose q * S⁻¹ = a • (L⁻¹ * q)ᵀ := by
    have h1 : (L⁻¹ * q)ᵀ = q * L⁻¹ := by
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hLsymm, hqsymm]
    change qᵀ * S⁻¹ = a • (L⁻¹ * q)ᵀ
    rw [h1, hqsymm, hSinv, Matrix.mul_smul]
  have hBform : q⁻¹ * S = a⁻¹ • (q⁻¹ * L) := by
    rw [hSeq, Matrix.mul_smul]
  have hnormA : ‖matTranspose q * S⁻¹‖ = a * ‖L⁻¹ * q‖ := by
    have hT : ‖(L⁻¹ * q)ᵀ‖ = ‖L⁻¹ * q‖ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.l2_opNorm_conjTranspose (L⁻¹ * q)
    rw [hAform, norm_smul, Real.norm_eq_abs, abs_of_pos hapos, hT]
  have hnormB : ‖q⁻¹ * S‖ = a⁻¹ * ‖q⁻¹ * L‖ := by
    rw [hBform, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos)]
  have hop : ‖matTranspose q * S⁻¹‖ * ‖q⁻¹ * S‖ ≤ 3 := by
    rw [hnormA, hnormB]
    have hcore := opNorm_metric_product_le hl hm
    rw [← hL, ← hq] at hcore
    calc a * ‖L⁻¹ * q‖ * (a⁻¹ * ‖q⁻¹ * L‖)
        = (a * a⁻¹) * (‖L⁻¹ * q‖ * ‖q⁻¹ * L‖) := by ring
      _ = ‖L⁻¹ * q‖ * ‖q⁻¹ * L‖ := by rw [mul_inv_cancel₀ hapos.ne', one_mul]
      _ ≤ 3 := hcore
  have hAf := Book.Ch02.matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm
    (matTranspose q * S⁻¹)
  have hBf := Book.Ch02.matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm (q⁻¹ * S)
  rw [Book.Ch02.matrixOperatorNorm_eq_l2_opNorm] at hAf hBf
  change Book.Ch02.matrixFrobeniusNorm (matTranspose q * S⁻¹) *
      Book.Ch02.matrixFrobeniusNorm (q⁻¹ * S) ≤ _
  calc Book.Ch02.matrixFrobeniusNorm (matTranspose q * S⁻¹) *
        Book.Ch02.matrixFrobeniusNorm (q⁻¹ * S)
      ≤ ((d : ℝ) * ‖matTranspose q * S⁻¹‖) * ((d : ℝ) * ‖q⁻¹ * S‖) :=
        mul_le_mul hAf hBf (Book.Ch02.matrixFrobeniusNorm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg _))
    _ = (d : ℝ) ^ 2 * (‖matTranspose q * S⁻¹‖ * ‖q⁻¹ * S‖) := by ring
    _ ≤ (d : ℝ) ^ 2 * 3 := by
        exact mul_le_mul_of_nonneg_left hop (sq_nonneg _)
    _ = 3 * (d : ℝ) ^ 2 := by ring

omit [NeZero d] in
theorem continuous_matVecMul (q : Mat d) : Continuous (matVecMul q) := by
  refine continuous_pi fun i => ?_
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

omit [NeZero d] in
theorem measurable_matVecMul (q : Mat d) : Measurable (matVecMul q) :=
  (continuous_matVecMul q).measurable

omit [NeZero d] in
/-- The invertible linear map `x ↦ q x` as a measurable equivalence. -/
@[expose]
def matMeasurableEquiv {q : Mat d} (hq : IsUnit q) : Vec d ≃ᵐ Vec d where
  toFun := matVecMul q
  invFun := matVecMul q⁻¹
  left_inv := matVecMul_inv_matVecMul hq
  right_inv := matVecMul_matVecMul_inv_cancel hq
  measurable_toFun := measurable_matVecMul q
  measurable_invFun := measurable_matVecMul q⁻¹

omit [NeZero d] in
theorem map_matVecMul_volume {q : Mat d} (hq : IsUnit q) :
    Measure.map (matVecMul q) (volume : Measure (Vec d))
      = ENNReal.ofReal |q.det|⁻¹ • volume := by
  have hdet : LinearMap.det (Matrix.toLin' q) ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Vec d)) hdet
  rw [LinearMap.det_toLin', abs_inv] at h
  have hfun : ⇑(Matrix.toLin' q) = matVecMul q := by
    funext v
    simp [Matrix.toLin'_apply, Geometry.matVecMul_eq_mulVec]
  rwa [hfun] at h

omit [NeZero d] in
theorem setIntegral_comp_matVecMul {q : Mat d} (hq : IsUnit q) {A : Set (Vec d)}
    (hA : MeasurableSet A) (g : Vec d → ℝ) :
    ∫ y in (matVecMul q) ⁻¹' A, g (matVecMul q y) ∂volume
      = |q.det|⁻¹ * ∫ x in A, g x ∂volume := by
  classical
  have hmeas : Measurable (matVecMul q) := measurable_matVecMul q
  have hpre : MeasurableSet ((matVecMul q) ⁻¹' A) := hA.preimage hmeas
  have h2 : (fun y => ((matVecMul q) ⁻¹' A).indicator (fun y => g (matVecMul q y)) y)
      = fun y => (A.indicator g) (matVecMul q y) := by
    funext y
    by_cases hy : matVecMul q y ∈ A
    · simp [Set.indicator_of_mem, hy, Set.mem_preimage]
    · simp [Set.indicator_of_notMem, hy, Set.mem_preimage]
  calc ∫ y in (matVecMul q) ⁻¹' A, g (matVecMul q y) ∂volume
      = ∫ y, ((matVecMul q) ⁻¹' A).indicator (fun y => g (matVecMul q y)) y ∂volume :=
        (integral_indicator hpre).symm
    _ = ∫ y, (A.indicator g) (matVecMul q y) ∂volume := by rw [h2]
    _ = ∫ x, (A.indicator g) x ∂(Measure.map (matVecMul q) volume) :=
        (integral_map_equiv (matMeasurableEquiv hq) (A.indicator g)).symm
    _ = ∫ x, (A.indicator g) x ∂(ENNReal.ofReal |q.det|⁻¹ • volume) := by
        rw [map_matVecMul_volume hq]
    _ = |q.det|⁻¹ * ∫ x in A, g x ∂volume := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
          integral_indicator hA]

/-! ### Stage 2 : cube-average pullback -/

omit [NeZero d] in
theorem injective_matVecMul {q : Mat d} (hq : IsUnit q) :
    Function.Injective (matVecMul q) := by
  intro x y hxy
  have h := congrArg (matVecMul q⁻¹) hxy
  rwa [matVecMul_inv_matVecMul hq, matVecMul_inv_matVecMul hq] at h

omit [NeZero d] in
theorem preimage_matVecMul_adaptedCellAtCenter {q : Mat d} (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) :
    (matVecMul q) ⁻¹' (adaptedCellAtCenter q k w)
      = openCubeSet (translateCube w (originCube d k)) := by
  rw [Geometry.adaptedCellAtCenter_eq_affine_standardCell,
    Set.preimage_image_eq _ (injective_matVecMul hq)]
  rfl

omit [NeZero d] in
theorem cubeVolume_translateCube_originCube (k : ℤ) (w : Fin d → ℤ) :
    cubeVolume (translateCube w (originCube d k)) = ((3 : ℝ) ^ k) ^ d := rfl

omit [NeZero d] in
theorem volume_adaptedCellAtCenter_toReal (q : Mat d) (k : ℤ) (w : Fin d → ℤ) :
    (volume (adaptedCellAtCenter q k w)).toReal = |q.det| * ((3 : ℝ) ^ k) ^ d := by
  rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ k)]

omit [NeZero d] in
theorem cubeAverage_comp_matVecMul {q : Mat d} (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ)
    (g : Vec d → ℝ) :
    cubeAverage (translateCube w (originCube d k)) (fun y => g (matVecMul q y))
      = volumeAverage (adaptedCellAtCenter q k w) g := by
  have hAmeas : MeasurableSet (adaptedCellAtCenter q k w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq k w).measurableSet
  have hint : ∫ y in cubeSet (translateCube w (originCube d k)), g (matVecMul q y) ∂volume
      = |q.det|⁻¹ * ∫ x in adaptedCellAtCenter q k w, g x ∂volume := by
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
      ← preimage_matVecMul_adaptedCellAtCenter hq k w]
    exact setIntegral_comp_matVecMul hq hAmeas g
  unfold cubeAverage volumeAverage
  rw [hint, volume_adaptedCellAtCenter_toReal, cubeVolume_translateCube_originCube, mul_inv]
  ring

omit [NeZero d] in
theorem cubeAverageVec_comp_matVecMul {q : Mat d} (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ)
    (Y : Vec d → Vec d) :
    cubeAverageVec (translateCube w (originCube d k)) (fun y => Y (matVecMul q y))
      = volumeAverageVec (adaptedCellAtCenter q k w) Y := by
  funext i
  exact cubeAverage_comp_matVecMul hq k w (fun x => Y x i)

omit [NeZero d] in
theorem volumeAverageVec_matVecMul {A : Set (Vec d)} (W : Mat d) (Y : Vec d → Vec d)
    (hY : ∀ i, IntegrableOn (fun x => Y x i) A) :
    volumeAverageVec A (fun x => matVecMul W (Y x)) = matVecMul W (volumeAverageVec A Y) := by
  funext i
  exact volumeAverage_vecDot_left (W i) Y hY

/-! ### Stage 3 : index bridge -/

omit [NeZero d] in
theorem mem_triadicIndexBox_iff {n : ℕ} {w : Fin d → ℤ} :
    w ∈ triadicIndexBox d n ↔ ∀ i, |w i| ≤ (((3 ^ n - 1) / 2 : ℕ) : ℤ) := by
  rw [triadicIndexBox, Fintype.mem_piFinset]
  constructor
  · intro h i
    rw [abs_le]
    exact ⟨(Finset.mem_Icc.mp (h i)).1, (Finset.mem_Icc.mp (h i)).2⟩
  · intro h i
    rw [Finset.mem_Icc]
    exact ⟨(abs_le.mp (h i)).1, (abs_le.mp (h i)).2⟩

omit [NeZero d] in
theorem triadicIndexBound_succ (n : ℕ) :
    (((3 ^ (n + 1) - 1) / 2 : ℕ) : ℤ) = 3 * (((3 ^ n - 1) / 2 : ℕ) : ℤ) + 1 := by
  have h1 : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have h2 : (3 : ℕ) ^ n % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have h3 : (3 : ℕ) ^ (n + 1) = 3 * 3 ^ n := by ring
  omega

omit [NeZero d] in
theorem card_triadicIndexBox_nat (n : ℕ) :
    (triadicIndexBox d n).card = ((3 : ℕ) ^ n) ^ d := by
  classical
  have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 2 ∣ (3 : ℕ) ^ n - 1 := by
    have hodd : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have hIcc : (Finset.Icc (-(((3 ^ n - 1) / 2 : ℕ) : ℤ)) (((3 ^ n - 1) / 2 : ℕ) : ℤ)).card
      = (3 : ℕ) ^ n := by
    rw [Int.card_Icc]
    have h2 : 2 * ((3 ^ n - 1) / 2 : ℕ) = (3 : ℕ) ^ n - 1 := Nat.mul_div_cancel' hdvd
    omega
  unfold triadicIndexBox
  rw [Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hIcc)]
  simp

omit [NeZero d] in
theorem index_mem_triadicIndexBox_of_mem_descendantsAtDepth (t : ℤ) :
    ∀ (n : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d t) n →
      R.index ∈ triadicIndexBox d n
  | 0, R, hR => by
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hR
      subst hR
      rw [mem_triadicIndexBox_iff]
      intro i
      simp [originCube]
  | n + 1, R, hR => by
      rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨S, hS, hRS⟩
      obtain ⟨digits, hRdef⟩ := mem_childCubes_iff.mp hRS
      have hSbox := mem_triadicIndexBox_iff.mp
        (index_mem_triadicIndexBox_of_mem_descendantsAtDepth t n S hS)
      rw [mem_triadicIndexBox_iff]
      intro i
      have hidx : R.index i = 3 * S.index i + ((digits i : ℕ) : ℤ) - 1 := by rw [hRdef]
      have hlt : ((digits i : ℕ) : ℤ) < 3 := by exact_mod_cast (digits i).isLt
      have hd0 : (0 : ℤ) ≤ ((digits i : ℕ) : ℤ) := Int.natCast_nonneg _
      have hSi := hSbox i
      rw [abs_le] at hSi
      rw [hidx, triadicIndexBound_succ, abs_le]
      omega

omit [NeZero d] in
theorem injective_translateCube_originCube (k : ℤ) :
    Function.Injective (fun w : Fin d → ℤ => translateCube w (originCube d k)) := by
  intro a b hab
  funext i
  have h := congrArg (fun R : TriadicCube d => R.index i) hab
  simpa [translateCube, originCube] using h

omit [NeZero d] in
theorem descendantsAtDepth_originCube_eq_image (t : ℤ) (n : ℕ) :
    descendantsAtDepth (originCube d t) n
      = (triadicIndexBox d n).image
          (fun w => translateCube w (originCube d (t - (n : ℤ)))) := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    refine Finset.mem_image.mpr
      ⟨R.index, index_mem_triadicIndexBox_of_mem_descendantsAtDepth t n R hR, ?_⟩
    have hs : R.scale = t - (n : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hR
    cases R with
    | mk s idx =>
        simp only at hs
        subst hs
        simp [translateCube, originCube]
  · rw [Finset.card_image_of_injective _ (injective_translateCube_originCube (t - (n : ℤ))),
      descendantsAtDepth_card, card_triadicIndexBox_nat]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

omit [NeZero d] in
theorem descendantsAverage_originCube_eq (t : ℤ) (n : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage (originCube d t) n F
      = ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n, F (translateCube w (originCube d (t - (n : ℤ)))) := by
  classical
  have hrfl : descendantsAverage (originCube d t) n F
      = ((descendantsAtDepth (originCube d t) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d t) n, F R := rfl
  rw [hrfl, descendantsAtDepth_originCube_eq_image,
    Finset.sum_image (fun a _ b _ h => injective_translateCube_originCube (t - (n : ℤ)) h),
    Finset.card_image_of_injective _ (injective_translateCube_originCube (t - (n : ℤ)))]

/-! ### Stage 4 : core inequalities -/

omit [NeZero d] in
theorem matVecMul_mul_apply (A B : Mat d) (v : Vec d) :
    matVecMul (A * B) v = matVecMul A (matVecMul B v) := by
  rw [Geometry.matVecMul_eq_mulVec, Geometry.matVecMul_eq_mulVec, Geometry.matVecMul_eq_mulVec,
    Matrix.mulVec_mulVec]

omit [NeZero d] in
theorem vecNormSq_fst_le_blockVecDot (Y : BlockVec d) : vecNormSq Y.1 ≤ blockVecDot Y Y := by
  have h2 := vecNormSq_nonneg Y.2
  simp only [vecNormSq] at h2 ⊢
  simp only [blockVecDot]
  linarith only [h2]

omit [NeZero d] in
theorem vecNormSq_snd_le_blockVecDot (Y : BlockVec d) : vecNormSq Y.2 ≤ blockVecDot Y Y := by
  have h1 := vecNormSq_nonneg Y.1
  simp only [vecNormSq] at h1 ⊢
  simp only [blockVecDot]
  linarith only [h1]

omit [NeZero d] in
theorem integrableOn_apply_of_vecNormSq_le {U : Set (Vec d)} (hUfin : volume U ≠ ⊤)
    {Y : Vec d → Vec d} (hYm : AEStronglyMeasurable Y (volume.restrict U))
    {f : Vec d → ℝ} (hf : IntegrableOn f U)
    (hle : ∀ x, vecNormSq (Y x) ≤ f x) (i : Fin d) :
    IntegrableOn (fun x => Y x i) U := by
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hUfin⟩
  have hg : IntegrableOn (fun x => (1 + f x) / 2) U := by
    have h1 : IntegrableOn (fun x => (1 : ℝ) + f x) U := (integrable_const (1 : ℝ)).add hf
    simpa [div_eq_mul_inv] using! h1.mul_const (2 : ℝ)⁻¹
  refine Integrable.mono' hg ((continuous_apply i).comp_aestronglyMeasurable hYm) ?_
  filter_upwards with x
  have h1 : (Y x i) ^ 2 ≤ vecNormSq (Y x) := sq_apply_le_vecNormSq (Y x) i
  have h2 : vecNormSq (Y x) ≤ f x := hle x
  have h3 : |Y x i| ≤ (1 + (Y x i) ^ 2) / 2 := by
    nlinarith only [sq_nonneg (|Y x i| - 1), sq_abs (Y x i)]
  rw [Real.norm_eq_abs]
  linarith only [h1, h2, h3]

omit [NeZero d] in
theorem depthAverage_pullback_le {q : Mat d} (hq : IsUnit q) (W : Mat d) (t : ℤ) (n : ℕ)
    (Z : Vec d → BlockVec d) (sl : BlockVec d → Vec d)
    (hsl_lin : ∀ V : Set (Vec d), volumeAverageVec V (fun x => sl (Z x)) = sl (cellAverage V Z))
    (hsl_le : ∀ Y : BlockVec d, vecNormSq (sl Y) ≤ blockVecDot Y Y)
    (hint : ∀ w ∈ triadicIndexBox d n, ∀ i : Fin d,
      IntegrableOn (fun x => sl (Z x) i) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    cubeBesovNegativeVectorDepthAverage (originCube d t)
        (fun y => matVecMul W (sl (Z (matVecMul q y)))) n
      ≤ Book.Ch02.matrixFrobeniusNormSq W *
        ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)) := by
  classical
  have hkey : ∀ w ∈ triadicIndexBox d n,
      vecNormSq (cubeAverageVec (translateCube w (originCube d (t - (n : ℤ))))
          (fun y => matVecMul W (sl (Z (matVecMul q y)))))
        ≤ Book.Ch02.matrixFrobeniusNormSq W *
          blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z) := by
    intro w hw
    have h1 : cubeAverageVec (translateCube w (originCube d (t - (n : ℤ))))
        (fun y => matVecMul W (sl (Z (matVecMul q y))))
        = volumeAverageVec (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => matVecMul W (sl (Z x))) :=
      cubeAverageVec_comp_matVecMul hq _ w (fun x => matVecMul W (sl (Z x)))
    have h2 : volumeAverageVec (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (fun x => matVecMul W (sl (Z x)))
        = matVecMul W (sl (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)) := by
      rw [volumeAverageVec_matVecMul W (fun x => sl (Z x)) (hint w hw), hsl_lin]
    rw [h1, h2]
    calc vecNormSq (matVecMul W (sl (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)))
        ≤ Book.Ch02.matrixFrobeniusNormSq W *
            vecNormSq (sl (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)) :=
          Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq _ _
      _ ≤ Book.Ch02.matrixFrobeniusNormSq W *
            blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z) :=
          mul_le_mul_of_nonneg_left (hsl_le _) (Book.Ch02.matrixFrobeniusNormSq_nonneg W)
  have hcardnn : (0 : ℝ) ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ := by positivity
  unfold cubeBesovNegativeVectorDepthAverage
  rw [descendantsAverage_originCube_eq]
  calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          vecNormSq (cubeAverageVec (translateCube w (originCube d (t - (n : ℤ))))
            (fun y => matVecMul W (sl (Z (matVecMul q y)))))
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (Book.Ch02.matrixFrobeniusNormSq W *
            blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hkey) hcardnn
    _ = Book.Ch02.matrixFrobeniusNormSq W *
          ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Z)) := by
        rw [← Finset.mul_sum]; ring

omit [NeZero d] in
theorem partialSeminorm_le_tsum_core (t : ℤ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (u : Vec d → Vec d) (inner : ℕ → ℝ)
    (hdepth : ∀ n, cubeBesovNegativeVectorDepthAverage (originCube d t) u n ≤ C ^ 2 * inner n)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (inner n)) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N u ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) * C *
        ∑' n : ℕ, (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (inner n) := by
  classical
  have hpre : (0 : ℝ) ≤ (3 : ℝ) ^ (-((t : ℝ) / 2)) * C :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC
  have hterm : ∀ n : ℕ,
      cubeBesovNegativeVectorDepthSeminorm (originCube d t) (1 / 2 : ℝ) u n
        ≤ (3 : ℝ) ^ (-((t : ℝ) / 2)) * C *
            ((3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (inner n)) := by
    intro n
    have h1 : Real.sqrt (cubeBesovNegativeVectorDepthAverage (originCube d t) u n)
        ≤ C * Real.sqrt (inner n) := by
      have h := Real.sqrt_le_sqrt (hdepth n)
      rwa [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at h
    have hw : Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (n : ℝ))
        = (3 : ℝ) ^ (-((t : ℝ) / 2)) * (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) := by
      change (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) = _
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    unfold cubeBesovNegativeVectorDepthSeminorm
    rw [hw]
    calc (3 : ℝ) ^ (-((t : ℝ) / 2)) * (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
          Real.sqrt (cubeBesovNegativeVectorDepthAverage (originCube d t) u n)
        ≤ (3 : ℝ) ^ (-((t : ℝ) / 2)) * (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
            (C * Real.sqrt (inner n)) := by
          refine mul_le_mul_of_nonneg_left h1 ?_
          positivity
      _ = (3 : ℝ) ^ (-((t : ℝ) / 2)) * C *
            ((3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (inner n)) := by ring
  unfold cubeBesovNegativeVectorPartialSeminorm
  calc ∑ j ∈ Finset.range (N + 1),
        cubeBesovNegativeVectorDepthSeminorm (originCube d t) (1 / 2 : ℝ) u j
      ≤ ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-((t : ℝ) / 2)) * C *
          ((3 : ℝ) ^ (((t : ℝ) - (j : ℝ)) / 2) * Real.sqrt (inner j)) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (3 : ℝ) ^ (-((t : ℝ) / 2)) * C *
          ∑ j ∈ Finset.range (N + 1),
            ((3 : ℝ) ^ (((t : ℝ) - (j : ℝ)) / 2) * Real.sqrt (inner j)) := by
        rw [Finset.mul_sum]
    _ ≤ (3 : ℝ) ^ (-((t : ℝ) / 2)) * C *
          ∑' n : ℕ, ((3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (inner n)) := by
        refine mul_le_mul_of_nonneg_left ?_ hpre
        refine hsum.sum_le_tsum _ (fun n _ => ?_)
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

/-! ### Stage 5 : the slotwise pullback bound and the two theorems -/

omit [NeZero d] in
theorem partialSeminorm_pullback_slot_le {q : Mat d} (hq : IsUnit q) (W : Mat d) (t : ℤ) (N : ℕ)
    (Z : Vec d → BlockVec d) (sl : BlockVec d → Vec d)
    (hsl_lin : ∀ V : Set (Vec d), volumeAverageVec V (fun x => sl (Z x)) = sl (cellAverage V Z))
    (hsl_le : ∀ Y : BlockVec d, vecNormSq (sl Y) ≤ blockVecDot Y Y)
    (hZm : AEStronglyMeasurable (fun x => sl (Z x))
      (volume.restrict (HighContrast.adaptedCell q t)))
    (hX : MemLp (fun x => blockVecDot (Z x) (Z x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul W (sl (Z (matVecMul q y)))) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) * Real.sqrt (Book.Ch02.matrixFrobeniusNormSq W) *
        besovSeminorm t (cellAverageFamily q t Z) := by
  classical
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfint : IntegrableOn (fun x => blockVecDot (Z x) (Z x)) (HighContrast.adaptedCell q t) :=
    memLp_one_iff_integrable.mp hX
  have hbase : ∀ i : Fin d, IntegrableOn (fun x => sl (Z x) i) (HighContrast.adaptedCell q t) :=
    fun i => integrableOn_apply_of_vecNormSq_le hUfin hZm hfint (fun x => hsl_le (Z x)) i
  have hint : ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n, ∀ i : Fin d,
      IntegrableOn (fun x => sl (Z x) i) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun n w hw i => (hbase i).mono_set (adaptedCellAtCenter_subset_adaptedCell q t n hw)
  have hdepth : ∀ n : ℕ, cubeBesovNegativeVectorDepthAverage (originCube d t)
      (fun y => matVecMul W (sl (Z (matVecMul q y)))) n
      ≤ (Real.sqrt (Book.Ch02.matrixFrobeniusNormSq W)) ^ 2 *
        ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot (cellAverageFamily q t Z n w) (cellAverageFamily q t Z n w)) := by
    intro n
    rw [Real.sq_sqrt (Book.Ch02.matrixFrobeniusNormSq_nonneg W)]
    exact depthAverage_pullback_le hq W t n Z sl hsl_lin hsl_le (hint n)
  exact partialSeminorm_le_tsum_core t N _ (Real.sqrt_nonneg _) _ _ hdepth
    (summable_besov_cellAverageFamily q hq t Z hX)

/-- The pullback bound for the first slot: the negative Besov seminorm up to depth `N` of
`y ↦ matVecMul (matTranspose q) (X (matVecMul q y)).1` is at most `3 ^ (-t/2)` times the
Frobenius factor `Real.sqrt (matrixFrobeniusNormSq (matTranspose q * (matSqrt m)⁻¹))` times the
Besov seminorm of the cell-average family of the block field. -/
theorem partialSeminorm_pullback_fst_le (q : Mat d) (hq : IsUnit q) (m : Mat d) (hm : m.PosDef)
    (t : ℤ) (N : ℕ) (X : Vec d → BlockVec d)
    (hX : MemLp (fun x => blockVecDot
        (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)
        (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) 1
      (volume.restrict (HighContrast.adaptedCell q t)))
    (hXm : AEStronglyMeasurable
      (fun x => ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
      (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul (matTranspose q) (X (matVecMul q y)).1) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (matTranspose q * (matSqrt m)⁻¹)) *
        besovSeminorm t (cellAverageFamily q t fun x =>
          (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) := by
  -- A no-op use of the section instance `[NeZero d]`, which the statement
  -- carries (through `besovSeminorm`/`cellAverageFamily`) but the proof term does not mention.
  have _ := NeZero.ne d
  have hSunit : IsUnit (matSqrt m) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_matSqrt hm)
  have hu : (fun y => matVecMul (matTranspose q) (X (matVecMul q y)).1)
      = fun y => matVecMul (matTranspose q * (matSqrt m)⁻¹)
          (Prod.fst ((fun x : Vec d =>
            ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
              (matVecMul q y))) := by
    funext y
    rw [matVecMul_mul_apply]
    change matVecMul (matTranspose q) (X (matVecMul q y)).1
        = matVecMul (matTranspose q)
            (matVecMul (matSqrt m)⁻¹ (matVecMul (matSqrt m) (X (matVecMul q y)).1))
    rw [matVecMul_inv_matVecMul hSunit]
  rw [hu]
  exact partialSeminorm_pullback_slot_le (q := q) hq (matTranspose q * (matSqrt m)⁻¹) t N
    (fun x : Vec d =>
      ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
    Prod.fst (fun _ => rfl) vecNormSq_fst_le_blockVecDot
    (continuous_fst.comp_aestronglyMeasurable hXm) hX

/-- The pullback bound for the second slot: the negative Besov seminorm up to depth `N` of
`y ↦ matVecMul q⁻¹ (X (matVecMul q y)).2` is at most `3 ^ (-t/2)` times the Frobenius factor
`Real.sqrt (matrixFrobeniusNormSq (q⁻¹ * matSqrt m))` times the Besov seminorm of the
cell-average family of the block field. -/
theorem partialSeminorm_pullback_snd_le (q : Mat d) (hq : IsUnit q) (m : Mat d) (hm : m.PosDef)
    (t : ℤ) (N : ℕ) (X : Vec d → BlockVec d)
    (hX : MemLp (fun x => blockVecDot
        (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)
        (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) 1
      (volume.restrict (HighContrast.adaptedCell q t)))
    (hXm : AEStronglyMeasurable
      (fun x => ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
      (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul q⁻¹ (X (matVecMul q y)).2) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (q⁻¹ * matSqrt m)) *
        besovSeminorm t (cellAverageFamily q t fun x =>
          (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) := by
  -- A no-op use of the section instance `[NeZero d]`.
  have _ := NeZero.ne d
  have hSunit : IsUnit (matSqrt m) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_matSqrt hm)
  have hu : (fun y => matVecMul q⁻¹ (X (matVecMul q y)).2)
      = fun y => matVecMul (q⁻¹ * matSqrt m)
          (Prod.snd ((fun x : Vec d =>
            ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
              (matVecMul q y))) := by
    funext y
    rw [matVecMul_mul_apply]
    change matVecMul q⁻¹ (X (matVecMul q y)).2
        = matVecMul q⁻¹
            (matVecMul (matSqrt m) (matVecMul (matSqrt m)⁻¹ (X (matVecMul q y)).2))
    rw [matVecMul_matVecMul_inv_cancel hSunit]
  rw [hu]
  exact partialSeminorm_pullback_slot_le (q := q) hq (q⁻¹ * matSqrt m) t N
    (fun x : Vec d =>
      ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
    Prod.snd (fun _ => rfl) vecNormSq_snd_le_blockVecDot
    (continuous_snd.comp_aestronglyMeasurable hXm) hX

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Response maximizers on every aligned subcell

The terminal-optimizer replacement of `p.response.transfer` compares the optimizer of the
terminal cell with the optimizer of each aligned subcell `z + ⋄_j^q` of the coarse scale.
This module supplies the existence input for that comparison: for the recentred coefficient
families `a_-` and `a_+` and for every sample, a scalar canonical response maximizer exists
on each translated aligned cell `adaptedCellAtCenter q j w`.  The centered-cell statements
`nonempty_scalarCanonicalMaximizer_respCoeffMinus` and `..._respCoeffPlus` are transported to
the translate by exhibiting the translate as an affine image of the centered adapted cell,
which is open, bounded, convex and nonempty.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Existence of a scalar canonical maximizer for `a_- = a - g` on the translated aligned
cell `z + ⋄_j^q` at `z = 3^j q w`, the aligned subcell produced by subdividing the coarse
scale.  This is the translate of `nonempty_scalarCanonicalMaximizer_respCoeffMinus` to the
recentred coefficient `a_-`. -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter {d : ℕ}
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r (respCoeffMinus F a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j (adaptedCellCenter q j w) a
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) (respg_isSkew F)
  have hne : (adaptedCellAtCenter q j w).Nonempty := by
    obtain ⟨z, hz⟩ := Recurrence.adaptedCell_nonempty q j
    exact ⟨adaptedCellCenter q j w + z, z, hz, rfl⟩
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q j w) := by
    change IsOpenBoundedConvexDomain
      (HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w))
    rw [Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq j (adaptedCellCenter q j w)
  have hbase : Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r
      (fun x => f x - respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffMinus, hx]

/-- Existence of a scalar canonical maximizer for `a_+ = a^t + g` on the translated aligned
cell `z + ⋄_j^q` at `z = 3^j q w`, the aligned subcell produced by subdividing the coarse
scale.  This is the translate of `nonempty_scalarCanonicalMaximizer_respCoeffPlus` to the
recentred coefficient `a_+`. -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter {d : ℕ}
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r (respCoeffPlus F a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j (adaptedCellCenter q j w) a
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) (respg_isSkew F)
  have hne : (adaptedCellAtCenter q j w).Nonempty := by
    obtain ⟨z, hz⟩ := Recurrence.adaptedCell_nonempty q j
    exact ⟨adaptedCellCenter q j w + z, z, hz, rfl⟩
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q j w) := by
    change IsOpenBoundedConvexDomain
      (HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w))
    rw [Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq j (adaptedCellCenter q j w)
  have hbase : Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r
      (fun x => matTranspose (f x) + respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffPlus, hx]

end

end HCPolySupport.HighContrast.Multiscale
end
