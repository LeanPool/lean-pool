/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.Witness
public import LeanPool.HighContrastHomogenization.Frozen.PolynomialHomogenization
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder

/-!
# High-contrast homogenization: Provider.UniformEllipticity.UniformHomogenization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative homogenization under uniform ellipticity

`t.uniform.homogenization` is the uniformly elliptic instance of the general
polynomial homogenization theorem `t.random.homogenization`: a `ℤ^d`-stationary
law of unit range whose fields satisfy `e.uniform.ellipticity` with constants
`0 < λ ≤ 1 ≤ Λ` carries the whole conclusion list of the general theorem, at
discount exponent `g = 0`, with the homogenization length bounded by a power of
`2 + Λ/λ`.

The three data the general theorem quantifies over are produced here from
`e.uniform.ellipticity` alone.

* The reference block is the diagonal doubled block `diag(2Λ, 2λ⁻¹)`.  On every
  standard aligned cube the coarse block response of a `(λ, Λ)`-elliptic field is
  dominated by it, with no discount factor: the constant competitor is admissible
  at every cube, and the doubled quadratic form of a `(λ, Λ)`-elliptic matrix is
  bounded by `2Λ|p|² + 2λ⁻¹|q|²`.  Its reference aspect ratio is at most `4Λ/λ`.
* The gauge is `Ψ(t) = exp(t^d)`, with growth witness `2`.
* The source scale is identically zero, so its tail is trivial and the two-part
  tail of the general theorem collapses: the second term is then
  `exp(-(c t)^d)`, of the same shape as the first, and a dilation of the scale
  absorbs both into `exp(-t^d)`, the tail written at `e.uniform.scale.tail`.

**Scope.**  The Dirichlet clause below is the homogeneous negative-Sobolev
estimate of the general theorem, on the adapted cells of the homogenized matrix.
The `L²` estimate `e.uniform.dirichlet`, which carries a forcing term `f` and is
read on the ellipsoids `e.homogenized.ellipsoids`, is deduced in the reference
text from that estimate by a further duality argument — harmonic replacement on a
mesoscopic grid against a constant-coefficient adjoint problem — which is not
carried out here.  The large-scale energy estimate `e.uniform.energy` and the
first-order approximation are stated on the ellipsoids `E_r`, as in the reference
text.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## A representative with the prescribed ellipticity constants -/

/-- A coefficient field uniformly elliptic almost everywhere with constants
`(λ, Λ)` has a measurable representative uniformly elliptic with the same
constants at every point. -/
theorem exists_pointwise_isEllipticMatrix_representative {a : Source.AKL.Field d}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a x)) :
    ∃ f : CoeffField d, Measurable f ∧ (∀ x, IsEllipticMatrix lam Lam (f x)) ∧
      (⇑a : Vec d → Mat d) =ᵐ[volume] f := by
  have hTheta : (1 : ℝ) ≤ Lam / lam := (one_le_div hlam).2 hle
  have hb : ∀ᵐ x ∂volume,
      IsEllipticMatrix 1 (Lam / lam) (((lam⁻¹ : ℝ) • a) x) := by
    filter_upwards [hell, AEEqFun.coeFn_smul (lam⁻¹ : ℝ) a] with x hx hsm
    rw [hsm]
    simpa only [Pi.smul_apply] using isEllipticMatrix_inv_smul hlam hx
  obtain ⟨g, hgm, hgp, hbg⟩ :=
    (Source.AKL.field_ae_elliptic_iff_exists_pointwise_representative hTheta
      ((lam⁻¹ : ℝ) • a)).1 hb
  refine ⟨fun x => lam • g x, hgm.const_smul lam,
    fun x => isEllipticMatrix_smul hlam hle (hgp x), ?_⟩
  filter_upwards [hbg, AEEqFun.coeFn_smul (lam⁻¹ : ℝ) a] with x hbgx hsm
  have hgx : g x = lam⁻¹ • a x := by
    rw [← hbgx, hsm]
    rfl
  rw [hgx, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]

/-! ## The reference block of a uniformly elliptic law -/

/-- The doubled quadratic form of a `(λ, Λ)`-elliptic matrix is bounded by
`2Λ|p|² + 2λ⁻¹|q|²`: the two inequalities of `e.uniform.ellipticity` read on the
Schur blocks as `σ + kᵗσ⁻¹k ≤ Λ` and `σ⁻¹ ≤ λ⁻¹`. -/
theorem blockVecDot_blockMatrixOfCoeff_le_of_isEllipticMatrix {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) ≤
      2 * Lam * vecNormSq p + 2 * lam⁻¹ * vecNormSq q := by
  have hquad := blockMatrixOfCoeff_quadratic_eq A p q
  have hNpsd : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul ((symmPart A)⁻¹) x) :=
    fun x => symmPart_inv_nonneg_of_isEllipticMatrix hA x
  have hsub := vecDot_matVecMul_sub_le_two hNpsd q (matVecMul (skewPart A) p)
  have hq := symmPart_inv_upperBound_of_isEllipticMatrix hA q
  have hkp := skew_symmPartInv_le hA p
  have hp0 : 0 ≤ vecDot p (matVecMul (symmPart A) p) :=
    le_trans (mul_nonneg hA.1.le (vecNormSq_nonneg p))
      (lowerBound_symmPart_of_isEllipticMatrix hA p)
  rw [hquad]
  linarith only [hsub, hq, hkp, hp0]

/-- The reference block of a uniformly elliptic law: the diagonal doubled block
`diag(2Λ, 2λ⁻¹)`. -/
@[expose]
def uniformRefBlock (d : ℕ) (lam Lam : ℝ) : BlockMat d :=
  blockDiag ((2 * Lam) • (1 : Mat d)) ((2 * lam⁻¹) • (1 : Mat d))

theorem blockVecDot_uniformRefBlock (lam Lam : ℝ) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (uniformRefBlock d lam Lam) (p, q)) =
      2 * Lam * vecNormSq p + 2 * lam⁻¹ * vecNormSq q :=
  blockVecDot_blockMatVecMul_blockDiag_smul_one _ _ p q

theorem isSymmetricBlockMat_uniformRefBlock (lam Lam : ℝ) :
    IsSymmetricBlockMat (uniformRefBlock d lam Lam) := by
  have hone : ∀ i j : Fin d, (1 : Mat d) i j = (1 : Mat d) j i := by
    intro i j
    by_cases h : i = j
    · rw [h]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          change ((2 * Lam) • (1 : Mat d)) i j = ((2 * Lam) • (1 : Mat d)) j i
          simp only [Matrix.smul_apply, smul_eq_mul, hone i j]
      | inr j => rfl
  | inr i =>
      cases β with
      | inl j => rfl
      | inr j =>
          change ((2 * lam⁻¹) • (1 : Mat d)) i j = ((2 * lam⁻¹) • (1 : Mat d)) j i
          simp only [Matrix.smul_apply, smul_eq_mul, hone i j]

theorem blockPosDef_uniformRefBlock {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam) :
    BlockPosDef (uniformRefBlock d lam Lam) := by
  intro X hX
  obtain ⟨p, q⟩ := X
  rw [blockVecDot_uniformRefBlock]
  have hpq : 0 < vecNormSq p + vecNormSq q := blockNormSq_pos hX
  have h1 : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  have h2 : 0 ≤ vecNormSq q := vecNormSq_nonneg q
  have hA : 0 ≤ 2 * Lam * vecNormSq p := by positivity
  have hB : 0 ≤ 2 * lam⁻¹ * vecNormSq q := by positivity
  by_cases hp : vecNormSq p = 0
  · have hq : 0 < vecNormSq q := by
      rw [hp] at hpq
      linarith only [hpq]
    have hBpos : 0 < 2 * lam⁻¹ * vecNormSq q := by positivity
    linarith only [hA, hBpos]
  · have hp' : 0 < vecNormSq p := lt_of_le_of_ne h1 (Ne.symm hp)
    have hApos : 0 < 2 * Lam * vecNormSq p := by positivity
    linarith only [hB, hApos]

/-! ## Coarse graining preserves uniform ellipticity -/

/-- The constant competitor bounds the coarse energy of a uniformly elliptic
field on every bounded open convex domain of positive volume. -/
theorem mu_le_of_isEllipticFieldOn {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hvol : 0 < (volume U).toReal)
    {lam Lam : ℝ} {f : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U f)
    (p q : Vec d) :
    Mu U (p, q) f ≤ Lam * vecNormSq p + lam⁻¹ * vecNormSq q := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hUm : MeasurableSet U := hU.isOpen.measurableSet
  have hAdm : IsBlockMuAdmissible U (p, q) (constBlockState (p, q)) :=
    isBlockMuAdmissible_constBlockState U (p, q)
  have hBdd : BddBelow (muValueSet U (p, q) f) := by
    refine ⟨0, ?_⟩
    rintro r ⟨Y, -, rfl⟩
    refine volumeAverage_nonneg_of_nonneg_on hUm ?_
    intro x hx
    have hquad := blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (Y.eval x)
    have hval : blockEnergyDensity f Y x = (1 / 2 : ℝ) *
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (f x)) (Y.eval x)) := rfl
    rw [hval]
    exact mul_nonneg (by norm_num) hquad
  have hMuLe : Mu U (p, q) f ≤
      volumeAverage U (blockEnergyDensity f (constBlockState (p, q))) :=
    csInf_le hBdd (muValueSet_mem hAdm)
  have hInt : IntegrableOn (blockEnergyDensity f (constBlockState (p, q))) U :=
    (hAdm.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := f) hEll).energyIntegrable
  refine hMuLe.trans (volumeAverage_le_of_le_on hUm hInt hvol.ne' ?_)
  intro x hx
  have hquad := blockVecDot_blockMatrixOfCoeff_le_of_isEllipticMatrix (hEll.2 x hx) p q
  have hval : blockEnergyDensity f (constBlockState (p, q)) x = (1 / 2 : ℝ) *
      blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff (f x)) (p, q)) := rfl
  rw [hval]
  linarith only [hquad]

theorem volume_standardCell_toReal_pos (k : ℤ) (w : Fin d → ℤ) :
    0 < (volume (standardCell d k w)).toReal := by
  change 0 < (volume (openCubeSet (translateCube w (originCube d k)))).toReal
  rw [volume_openCubeSet_toReal]
  exact cubeVolume_pos _

/-- **Coarse graining preserves uniform ellipticity.**  The coarse block response
of a field satisfying `e.uniform.ellipticity` is dominated, on every standard
aligned cube and at every scale, by the diagonal reference block `diag(2Λ, 2λ⁻¹)`
— with no discount factor, so the domination holds at the exponent `g = 0`. -/
theorem coarseBlock_blockMatLoewnerLE_uniformRefBlock [NeZero d] {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) {a : CoeffSpace d}
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a.1 x))
    (k : ℤ) (w : Fin d → ℤ) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (uniformRefBlock d lam Lam) := by
  obtain ⟨f, hfm, hfp, hfa⟩ :=
    exists_pointwise_isEllipticMatrix_representative hlam hle hell
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have hvol : 0 < (volume (standardCell d k w)).toReal :=
    volume_standardCell_toReal_pos k w
  have hEll : IsEllipticFieldOn lam Lam (standardCell d k w) f :=
    Sharp.isEllipticFieldOn_of_measurable hfm (fun x _ => hfp x) hU.isOpen.measurableSet
  have hcb : coarseBlock (standardCell d k w) a = coarseBlockMatrix (standardCell d k w) f :=
    coarseBlock_eq_of_ae_eq a hfa
  intro Pv
  obtain ⟨p, q⟩ := Pv
  rw [hcb, blockVecDot_uniformRefBlock, ← Sharp.mu_eq_half_blockQuadratic hU hEll hvol]
  have hMu := mu_le_of_isEllipticFieldOn hU hvol hEll p q
  linarith only [hMu]

/-! ## The gauge -/

/-- The gauge of a uniformly elliptic law: `Ψ(t) = exp(t^d)`. -/
@[expose]
def uniformGauge (d : ℕ) : ℝ → ℝ := fun t => Real.exp (t ^ d)

/-- `exp(t^d)` is an admissible gauge: increasing on `ℝ₊` with values in
`[1, ∞)`. -/
theorem admissiblePsi_uniformGauge (d : ℕ) :
    IndependentSums.AdmissiblePsi (uniformGauge d) := by
  constructor
  · intro x hx y _ hxy
    exact Real.exp_le_exp.2 (pow_le_pow_left₀ hx hxy d)
  · intro t ht
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (t ^ d) := Real.exp_le_exp.2 (pow_nonneg ht d)

/-- `exp(t^d)` has growth witness `2`: `t exp(t^d) ≤ exp((2t)^d)` for `t ≥ 1`. -/
theorem hasPsiGrowth_uniformGauge (hd : 1 ≤ d) :
    IndependentSums.HasPsiGrowth (uniformGauge d) 2 := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have htd : t ≤ t ^ d := le_self_pow₀ ht (by omega)
  have h2d : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := pow_le_pow_right₀ one_le_two hd
  have hfac : t ≤ ((2 : ℝ) ^ d - 1) * t ^ d := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ d - 1 := by linarith only [h2d]
    have h2 : (0 : ℝ) ≤ t ^ d := pow_nonneg ht0 d
    nlinarith only [h1, h2, htd]
  have hself : t ≤ Real.exp t := by linarith only [Real.add_one_le_exp t]
  have hexp : t ≤ Real.exp (((2 : ℝ) ^ d - 1) * t ^ d) :=
    le_trans hself (Real.exp_le_exp.2 hfac)
  have hmul : (2 * t) ^ d = 2 ^ d * t ^ d := by rw [mul_pow]
  calc t * Real.exp (t ^ d)
      ≤ Real.exp (((2 : ℝ) ^ d - 1) * t ^ d) * Real.exp (t ^ d) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = Real.exp (((2 : ℝ) ^ d - 1) * t ^ d + t ^ d) := (Real.exp_add _ _).symm
    _ = Real.exp ((2 * t) ^ d) := by rw [hmul]; ring_nf

/-! ## The coarse ellipticity bundle -/

/-- A law satisfying `e.uniform.ellipticity` carries the coarse ellipticity
assumption of the general theorem at the exponent `g = 0`, with the diagonal
reference block `diag(2Λ, 2λ⁻¹)`, the gauge `exp(t^d)`, growth witness `2`, and
the zero source scale. -/
theorem coarseEllipticityDagger_of_ae_isEllipticMatrix [NeZero d] (hd : 1 ≤ d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    {P : Measure (CoeffSpace d)}
    (hell : ∀ᵐ a ∂P, ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a.1 x)) :
    HCPoly.Frozen.CoarseEllipticityDagger P 0 (uniformRefBlock d lam Lam)
      (uniformGauge d) 2 (fun _ => 0) where
  g_mem := Set.mem_Ico.2 ⟨le_rfl, one_pos⟩
  refBlock_isSymm := isSymmetricBlockMat_uniformRefBlock lam Lam
  refBlock_posDef := blockPosDef_uniformRefBlock hlam (lt_of_lt_of_le hlam hle)
  gauge_admissible := admissiblePsi_uniformGauge d
  one_lt_growthWitness := by norm_num
  gauge_growth := hasPsiGrowth_uniformGauge hd
  source_measurable := measurable_const
  source_nonneg := fun _ => le_rfl
  source_tail := by
    intro t ht
    rw [upperTailEvent_zero ht, measureReal_empty]
    exact inv_nonneg.2 (Real.exp_pos _).le
  coarse_bound := by
    filter_upwards [hell] with a ha m _ k _ w _
    rw [blockScale_discount_zero]
    exact coarseBlock_blockMatLoewnerLE_uniformRefBlock hlam hle ha k w

/-! ## The reference aspect ratio -/

theorem specBound_smul_one [NeZero d] {c : ℝ} (hc : 0 ≤ c) :
    specBound (c • (1 : Mat d)) = c := by
  refine le_antisymm (specBound_le hc (MatLoewnerLE.refl _)) ?_
  have h := matLoewnerLE_specBound_smul_one (c • (1 : Mat d)) (Pi.single (0 : Fin d) 1)
  rw [vecDot_matVecMul_smul_one, vecDot_matVecMul_smul_one, vecNormSq_single'] at h
  linarith only [h]

theorem lambdaRef_uniformRefBlock [NeZero d] {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) :
    lambdaRef (uniformRefBlock d lam Lam) = lam / 2 := by
  have hlr : (uniformRefBlock d lam Lam).lowerRight = (2 * lam⁻¹) • (1 : Mat d) := rfl
  rw [lambdaRef, hlr, specBound_smul_one (by positivity)]
  field_simp

theorem bigLambdaRef_uniformRefBlock_le {lam Lam : ℝ} (hLam : 0 ≤ Lam) :
    bigLambdaRef (uniformRefBlock d lam Lam) ≤ 2 * Lam := by
  have hskew : schurSkew (uniformRefBlock d lam Lam) = 0 := by
    simp [schurSkew, uniformRefBlock, blockDiag]
  have hsigma : schurSigma (uniformRefBlock d lam Lam) = (2 * Lam) • (1 : Mat d) := by
    simp only [schurSigma, hskew]
    simp [uniformRefBlock, blockDiag, matTranspose]
  refine csInf_le ⟨0, fun t ht => ht.1⟩ ⟨by positivity, 0, isSkewMat_zero, ?_⟩
  rw [hskew, hsigma, sub_zero]
  simpa using MatLoewnerLE.refl ((2 * Lam) • (1 : Mat d))

theorem zero_le_aspectRatio_uniformRefBlock [NeZero d] {lam : ℝ} (hlam : 0 < lam)
    (Lam : ℝ) : 0 ≤ aspectRatio (uniformRefBlock d lam Lam) := by
  have h0 : 0 ≤ bigLambdaRef (uniformRefBlock d lam Lam) :=
    Real.sInf_nonneg fun _ ht => ht.1
  rw [aspectRatio, lambdaRef_uniformRefBlock hlam]
  positivity

/-- **The reference aspect ratio of a uniformly elliptic law**: the aspect ratio
`Π = Λ₀/λ₀` of the diagonal reference block `diag(2Λ, 2λ⁻¹)` is at most
`4Λ/λ`. -/
theorem aspectRatio_uniformRefBlock_le [NeZero d] {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : 0 ≤ Lam) :
    aspectRatio (uniformRefBlock d lam Lam) ≤ 4 * (Lam / lam) := by
  have hpos : (0 : ℝ) < lam / 2 := by positivity
  have heq : 4 * (Lam / lam) * (lam / 2) = 2 * Lam := by
    field_simp
    ring
  rw [aspectRatio, lambdaRef_uniformRefBlock hlam, div_le_iff₀ hpos, heq]
  exact bigLambdaRef_uniformRefBlock_le hLam

/-- The length bound of the general theorem, read through the reference aspect
ratio of a uniformly elliptic law: `2 + Π K ≤ (2 + Λ/λ)^4` at the growth witness
`K = 2`. -/
theorem two_add_aspectRatio_uniformRefBlock_le [NeZero d] {lam Lam : ℝ}
    (hlam : 0 < lam) (hR : 1 ≤ Lam / lam) (hLam : 0 ≤ Lam) :
    2 + aspectRatio (uniformRefBlock d lam Lam) * 2 ≤ (2 + Lam / lam) ^ (4 : ℕ) := by
  have hasp := aspectRatio_uniformRefBlock_le (d := d) hlam hLam
  have h3 : (3 : ℝ) ≤ 2 + Lam / lam := by linarith only [hR]
  have h27 : (27 : ℝ) ≤ (2 + Lam / lam) ^ (3 : ℕ) := by
    calc (27 : ℝ) = 3 ^ (3 : ℕ) := by norm_num
      _ ≤ (2 + Lam / lam) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h3 3
  have hsplit : (2 + Lam / lam) ^ (4 : ℕ) = (2 + Lam / lam) * (2 + Lam / lam) ^ (3 : ℕ) := by
    ring
  have hmul : (2 + Lam / lam) * 27 ≤ (2 + Lam / lam) * (2 + Lam / lam) ^ (3 : ℕ) :=
    mul_le_mul_of_nonneg_left h27 (by linarith only [h3])
  rw [hsplit]
  linarith only [hasp, hmul, hR]

/-! ## Theorem `t.uniform.homogenization` -/

/-- **Theorem `t.uniform.homogenization`**: quantitative homogenization under
uniform ellipticity.

For a `ℤ^d`-stationary law of unit range whose fields satisfy
`e.uniform.ellipticity` with `0 < λ ≤ 1 ≤ Λ` there are a homogenized matrix with
positive definite symmetric part, a corrector family, and a homogenization scale
`X ≥ 1` whose tail is `e.uniform.scale.tail`: the exponent is the dimension, and
the deterministic factor in front of `t` is a power of `2 + Λ/λ` with a
dimensional exponent.  On one translation invariant event of full probability the
Dirichlet estimate, the corrector equation and estimate, the Liouville
classification, the large-scale energy estimate `e.uniform.energy` and the
first-order approximation all hold.

The estimates are those of the general theorem `t.random.homogenization`,
specialized at the exponent `g = 0`: the two-part tail collapses to `exp(-t^d)`
because the source scale of a uniformly elliptic law vanishes, and the
homogenization length `L ≤ (2 + Π K)^C` becomes `(2 + Λ/λ)^C` because the
reference block `diag(2Λ, 2λ⁻¹)` has reference aspect ratio `Π ≤ 4Λ/λ`.

**Scope.**  The Dirichlet clause is the homogeneous negative-Sobolev estimate on
the adapted cells of the homogenized matrix, not the `L²` estimate
`e.uniform.dirichlet` with a forcing term `f` on the ellipsoids
`e.homogenized.ellipsoids`; the reference text deduces the latter from the
former by a separate duality argument, which is not carried out here.  The
large-scale energy estimate and the first-order approximation are stated on the
ellipsoids `E_r` of `e.homogenized.ellipsoids`. -/
theorem uniform_homogenization_of_polynomial_homogenization (d : ℕ) (hd : 2 ≤ d) :
    ∃ (κ C : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ),
      0 < κ ∧ 0 < C ∧ (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      ∀ lam Lam : ℝ, 0 < lam → lam ≤ 1 → 1 ≤ Lam →
        ∀ P : Measure (CoeffSpace d), IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P → HCPoly.Frozen.IsUnitRangeLaw P →
          (∀ᵐ a ∂P, ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a.1 x)) →
          ∃ (abar : Mat d) (X : CoeffSpace d → ℝ)
            (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            Measurable X ∧
            (∀ a, 1 ≤ X a) ∧
            (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
              gradPhi (c • e + e') a
                =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
            (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
              gradPhi e (translateCoeff z a)
                =ᵐ[volume] fun x => gradPhi e a (x + Source.AKL.intTranslation z)) ∧
            (∀ t : ℝ, 1 ≤ t →
              P.real {a | C * (2 + Lam / lam) ^ C * t ≤ X a} ≤
                Real.exp (-(t ^ (d : ℝ)))) ∧
            (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
            ∃ Ωend : Set (CoeffSpace d),
              MeasurableSet Ωend ∧
              P.real Ωend = 1 ∧
              (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
              (∀ s₀ : ℝ, s₀ ∈ Set.Ico (1 / 4 : ℝ) (1 / 2 : ℝ) →
                  ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                    (∃ j : ℤ, ∃ z : Vec d,
                      U = (fun x : Vec d =>
                        z + matVecMul (matSqrt (symmPart abar)) x) ''
                          openCubeSet (originCube d j)) →
                    HasBallSandwich (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                    U ⊆ ellipsoid abar 1 →
                    ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                      ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                        ∀ g₀ : H1Function U,
                          (∃ Lg : ℝ, ∀ᵐ x ∂volume.restrict U,
                            |g₀.toFun x| + Real.sqrt (vecNormSq (g₀.grad x)) ≤ Lg) →
                          hsNormSq U s₀ g₀.grad ≠ ⊤ →
                          ∀ h : H1Function U,
                            MemAffineH10 U g₀ h →
                            IsWeakSolutionOn (fun _ => abar) U h.grad →
                            ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                              MemH1a0 (scaledCoeff ε a) U
                                (fun x => uFun x - g₀.toFun x)
                                (fun x => uGrad x - g₀.grad x) →
                              IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                              negSobolevNorm U s₀
                                  (fun x => matVecMul (matSqrt (symmPart abar))
                                    (uGrad x - h.grad x)) +
                                negSobolevNorm U s₀
                                  (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                                    (matVecMul (scaledCoeff ε a x - skewPart abar)
                                        (uGrad x) -
                                      matVecMul (symmPart abar) (h.grad x))) ≤
                                ENNReal.ofReal (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                  hsNormSq U s₀
                                    (fun x => matVecMul (matSqrt (symmPart abar))
                                      (g₀.grad x)) ^ (1 / 2 : ℝ)) ∧
              (∀ a ∈ Ωend, ∀ e : Vec d,
                HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                  IsWeakSolutionOn (fun x => a.1 x) Set.univ
                    (fun x => e + gradPhi e a x)) ∧
              (∀ a ∈ Ωend, ∀ e : Vec d, ∀ r : ℝ, X a ≤ r →
                ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun x => matVecMul (matSqrt (symmPart abar)) (gradPhi e a x)) +
                  ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                        (matVecMul (a.1 x - skewPart abar) (e + gradPhi e a x) -
                          matVecMul (symmPart abar) e)) ≤
                  ENNReal.ofReal
                    (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                      (r / X a) ^ (-κ))) ∧
              (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
                  MemLiouvilleClass (fun x => a.1 x) ϑ v Dv →
                  ∃ (e : Vec d) (c : ℝ),
                    v =ᵐ[volume] fun x => vecDot e x + Phi e a x + c) ∧
                (∀ (e : Vec d) (c : ℝ),
                  MemLiouvilleClass (fun x => a.1 x) ϑ
                    (fun x => vecDot e x + Phi e a x + c)
                    (fun x => e + gradPhi e a x))) ∧
              (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                  MemH1a (fun x => a.1 x) (ellipsoid abar R) u Du →
                  IsWeakSolutionOn (fun x => a.1 x) (ellipsoid abar R) Du →
                  (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                    weightedGradNorm (fun x => a.1 x) (ellipsoid abar r) Du ≤
                      ENNReal.ofReal C *
                        weightedGradNorm (fun x => a.1 x) (ellipsoid abar R) Du) ∧
                  (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                    ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      weightedGradNorm (fun x => a.1 x) (ellipsoid abar r)
                          (fun x => Du x - (e + gradPhi e a x)) ≤
                        ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                          weightedGradNorm (fun x => a.1 x) (ellipsoid abar R) Du)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cd, C₀, hcd, hC₀pos, hT1⟩ :=
    HCPoly.Frozen.polynomial_homogenization_random_source d hd
  obtain ⟨CT, cSrc, κ, C₁, hCT, hcSrc, hκ, hC₁pos, hmain⟩ :=
    hT1 0 (Set.mem_Ico.2 ⟨le_rfl, one_pos⟩)
  set cAbs : ℝ := min cd (cSrc ^ d)
  have hcAbs : 0 < cAbs := lt_min hcd (by positivity)
  set dilation : ℝ := max 1 ((1 + Real.log 2) / cAbs) with hdilDef
  have hdil1 : (1 : ℝ) ≤ dilation := le_max_left _ _
  have hdil0 : (0 : ℝ) ≤ dilation := le_trans zero_le_one hdil1
  set Cout : ℝ := max (CT * dilation) (4 * CT)
  have hCoutPos : 0 < Cout := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨κ, Cout, C₀, C₁, hκ, hCoutPos, hC₀pos, hC₁pos, ?_⟩
  intro lam Lam hlam hlam1 hLam P hP hstat hunit hell
  have hle : lam ≤ Lam := le_trans hlam1 hLam
  have hR : (1 : ℝ) ≤ Lam / lam := (one_le_div hlam).2 hle
  have hbase1 : (1 : ℝ) ≤ 2 + Lam / lam := by linarith only [hR]
  obtain ⟨abar, Lpoly, X, Phi, gradPhi, hLpoly1, hXmeas, hX1, hlin, hshift, hLpolyLe,
    htail, hpd, Ωend, hΩmeas, hΩone, hΩinv, hdir, hcorr, hcorrEst, hliou, hreg⟩ :=
    hmain P (uniformRefBlock d lam Lam) (uniformGauge d) 2 (fun _ => 0) hP hstat hunit
      (coarseEllipticityDagger_of_ae_isEllipticMatrix (by omega) hlam hle hell)
  have hIco : Set.Ico ((1 + (0 : ℝ)) / 4) (1 / 2 : ℝ) = Set.Ico (1 / 4 : ℝ) (1 / 2 : ℝ) := by
    rw [add_zero]
  rw [hIco] at hdir
  -- the polynomial length in terms of the ellipticity ratio
  have hLbound : Lpoly ≤ (2 + Lam / lam) ^ Cout := by
    have hstep : (2 + aspectRatio (uniformRefBlock d lam Lam) * 2) ^ CT ≤
        ((2 + Lam / lam) ^ (4 : ℕ)) ^ CT := by
      refine Real.rpow_le_rpow ?_ (two_add_aspectRatio_uniformRefBlock_le hlam hR
        (le_trans zero_le_one hLam)) hCT.le
      have := zero_le_aspectRatio_uniformRefBlock (d := d) hlam Lam
      linarith only [this]
    have hpow : ((2 + Lam / lam) ^ (4 : ℕ)) ^ CT = (2 + Lam / lam) ^ ((4 : ℝ) * CT) := by
      rw [← Real.rpow_natCast (2 + Lam / lam) 4,
        ← Real.rpow_mul (by linarith only [hbase1])]
      norm_num
    have hexp : (2 + Lam / lam) ^ ((4 : ℝ) * CT) ≤ (2 + Lam / lam) ^ Cout :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (by
        have := le_max_right (CT * dilation) (4 * CT)
        linarith only [this])
    calc Lpoly ≤ (2 + aspectRatio (uniformRefBlock d lam Lam) * 2) ^ CT := hLpolyLe
      _ ≤ ((2 + Lam / lam) ^ (4 : ℕ)) ^ CT := hstep
      _ = (2 + Lam / lam) ^ ((4 : ℝ) * CT) := hpow
      _ ≤ (2 + Lam / lam) ^ Cout := hexp
  -- the collapsed tail
  have htail' : ∀ t : ℝ, 1 ≤ t →
      P.real {a | Cout * (2 + Lam / lam) ^ Cout * t ≤ X a} ≤
        Real.exp (-(t ^ (d : ℝ))) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
    have hu1 : (1 : ℝ) ≤ dilation * s := one_le_mul_of_one_le_of_one_le hdil1 hs
    have hu0 : (0 : ℝ) ≤ dilation * s := le_trans zero_le_one hu1
    have hupow : (0 : ℝ) ≤ (dilation * s) ^ (d : ℝ) := Real.rpow_nonneg hu0 _
    have hsubset : {a | Cout * (2 + Lam / lam) ^ Cout * s ≤ X a} ⊆
        {a | CT * Lpoly * (dilation * s) ≤ X a} := by
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      refine le_trans ?_ ha
      have hprod : CT * dilation * Lpoly ≤ Cout * (2 + Lam / lam) ^ Cout :=
        mul_le_mul (le_max_left _ _) hLbound (by linarith only [hLpoly1])
          (le_trans (by positivity) (le_max_left _ _))
      calc CT * Lpoly * (dilation * s) = CT * dilation * Lpoly * s := by ring
        _ ≤ Cout * (2 + Lam / lam) ^ Cout * s :=
            mul_le_mul_of_nonneg_right hprod hs0
    have hmono := measureReal_mono (μ := P) hsubset
    have hT := htail (dilation * s) hu1
    simp only [mul_zero, sub_zero] at hT
    have hterm1 : Real.exp (-cd * (dilation * s) ^ (d : ℝ)) ≤
        Real.exp (-cAbs * (dilation * s) ^ (d : ℝ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hupow)
    have hterm2 : (uniformGauge d (cSrc * (dilation * s)))⁻¹ ≤
        Real.exp (-cAbs * (dilation * s) ^ (d : ℝ)) := by
      have hval : (uniformGauge d (cSrc * (dilation * s)))⁻¹ =
          Real.exp (-(cSrc ^ d * (dilation * s) ^ d)) := by
        change (Real.exp ((cSrc * (dilation * s)) ^ d))⁻¹ = _
        rw [← Real.exp_neg, mul_pow]
      rw [hval, ← Real.rpow_natCast (dilation * s) d]
      refine Real.exp_le_exp.2 ?_
      have hneg : -(cSrc ^ d) ≤ -cAbs := neg_le_neg (min_le_right _ _)
      calc -(cSrc ^ d * (dilation * s) ^ (d : ℝ))
          = -(cSrc ^ d) * (dilation * s) ^ (d : ℝ) := by ring
        _ ≤ -cAbs * (dilation * s) ^ (d : ℝ) :=
            mul_le_mul_of_nonneg_right hneg hupow
    have hdpow : (dilation * s) ^ (d : ℝ) = dilation ^ (d : ℝ) * s ^ (d : ℝ) :=
      Real.mul_rpow hdil0 hs0
    have hdilpow : dilation ≤ dilation ^ (d : ℝ) := by
      calc dilation = dilation ^ (1 : ℝ) := (Real.rpow_one dilation).symm
        _ ≤ dilation ^ (d : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hdil1 (by exact_mod_cast (by omega : 1 ≤ d))
    have hspow : (1 : ℝ) ≤ s ^ (d : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (d : ℝ) := (Real.one_rpow _).symm
        _ ≤ s ^ (d : ℝ) := Real.rpow_le_rpow zero_le_one hs (by positivity)
    have hcdil : 1 + Real.log 2 ≤ cAbs * dilation := by
      have hmem := le_max_right 1 ((1 + Real.log 2) / cAbs)
      rw [← hdilDef] at hmem
      rw [div_le_iff₀ hcAbs] at hmem
      linarith only [hmem]
    have hge : Real.log 2 ≤ cAbs * dilation ^ (d : ℝ) - 1 := by
      have := mul_le_mul_of_nonneg_left hdilpow hcAbs.le
      linarith only [this, hcdil]
    have hkey : Real.log 2 ≤ (cAbs * dilation ^ (d : ℝ) - 1) * s ^ (d : ℝ) := by
      have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
      calc Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
        _ ≤ (cAbs * dilation ^ (d : ℝ) - 1) * s ^ (d : ℝ) :=
            mul_le_mul hge hspow zero_le_one (le_trans hlog hge)
    have hfinal : 2 * Real.exp (-cAbs * (dilation * s) ^ (d : ℝ)) ≤
        Real.exp (-(s ^ (d : ℝ))) := by
      rw [hdpow]
      calc 2 * Real.exp (-cAbs * (dilation ^ (d : ℝ) * s ^ (d : ℝ)))
          = Real.exp (Real.log 2) *
              Real.exp (-cAbs * (dilation ^ (d : ℝ) * s ^ (d : ℝ))) := by
            rw [Real.exp_log two_pos]
        _ = Real.exp (Real.log 2 + -cAbs * (dilation ^ (d : ℝ) * s ^ (d : ℝ))) :=
            (Real.exp_add _ _).symm
        _ ≤ Real.exp (-(s ^ (d : ℝ))) := Real.exp_le_exp.2 (by linarith only [hkey])
    calc P.real {a | Cout * (2 + Lam / lam) ^ Cout * s ≤ X a}
        ≤ P.real {a | CT * Lpoly * (dilation * s) ≤ X a} := hmono
      _ ≤ Real.exp (-cd * (dilation * s) ^ (d : ℝ)) +
            (uniformGauge d (cSrc * (dilation * s)))⁻¹ := hT
      _ ≤ 2 * Real.exp (-cAbs * (dilation * s) ^ (d : ℝ)) := by
          linarith only [hterm1, hterm2]
      _ ≤ Real.exp (-(s ^ (d : ℝ))) := hfinal
  have hCTle : CT ≤ Cout :=
    le_trans (by linarith only [hCT]) (le_max_right (CT * dilation) (4 * CT))
  refine ⟨abar, X, Phi, gradPhi, hXmeas, hX1, hlin, hshift, htail', hpd, Ωend, hΩmeas,
    hΩone, hΩinv, hdir, hcorr, ?_, hliou, ?_⟩
  · intro a ha e r hr
    refine le_trans (hcorrEst a ha e r hr) (ENNReal.ofReal_le_ofReal ?_)
    have hXa : (1 : ℝ) ≤ X a := hX1 a
    have hroot : 0 ≤ Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) := Real.sqrt_nonneg _
    have hratio : 0 ≤ (r / X a) ^ (-κ) :=
      Real.rpow_nonneg (div_nonneg (by linarith only [hXa, hr]) (by linarith only [hXa])) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCTle hroot) hratio
  · intro a ha R hRle u Du hmem hsol
    obtain ⟨hen, happ⟩ := hreg a ha R hRle u Du hmem hsol
    refine ⟨fun r hrmem => le_trans (hen r hrmem) ?_, happ⟩
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCTle) le_rfl

end

end HighContrast
end HCPolySupport
