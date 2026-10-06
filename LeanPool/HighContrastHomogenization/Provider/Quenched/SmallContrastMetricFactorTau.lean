/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMetricFactor
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCalibrationAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMetricFactorTau

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The shear size of the response skew

The recentering skew of the small-contrast weak norm is `h_0 = h_rsp(K_t)`,
the antisymmetric part of the Schur skew coordinate of the terminal adapted
mean.  The metric factor of `SmallContrastMetricFactor` needs the
`m_0`-normalized size `τ` of this skew, and it must not grow with the
generation.

The bound is read off a *two-sided* comparison of the terminal mean with the
split metric `M_0 = diag(m_0,m_0^{-1})`:

* the upper half, at the doubled vector `(x,0)`, gives
  `|σ_*^{-1/2}K x|² ≤ C |m_0^{1/2}x|²` — the Schur form's own `(0 - Kx)` slot;
* the lower half, at `(0,y)`, gives `|m_0^{-1/2}y|² ≤ κ |σ_*^{-1/2}y|²`;

and reading the second at `y = Kx` produces
`|m_0^{-1/2}Kx|² ≤ κ C |m_0^{1/2}x|²`, i.e. the normalized Schur coordinate
has size at most `(κC)^{1/2}`.

The passage from `K` to its antisymmetric part costs nothing: the transposed
bound follows from the same one by Cauchy–Schwarz in the `m_0` metric, and
the parallelogram bound absorbs the factor `1/2` of the antisymmetrization.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Elementary facts about a positive quadratic form -/

private theorem le_of_sq_le_mul {t c : ℝ} (ht0 : 0 ≤ t) (hc : 0 ≤ c)
    (h : t ^ 2 ≤ c * t) : t ≤ c := by
  rcases eq_or_lt_of_le ht0 with heq | hpos
  · rw [← heq]
    exact hc
  · nlinarith only [h, hpos]

private theorem quad_nonneg {Q : Mat d} (hQ : Q.PosSemidef) (v : Vec d) :
    0 ≤ v ⬝ᵥ Q *ᵥ v := by
  simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg v

/-- The parallelogram bound for a positive semidefinite quadratic form, in the
difference form. -/
private theorem quad_sub_le_two {Q : Mat d} (hQ : Q.PosSemidef) (a b : Vec d) :
    (a - b) ⬝ᵥ Q *ᵥ (a - b) ≤ 2 * (a ⬝ᵥ Q *ᵥ a) + 2 * (b ⬝ᵥ Q *ᵥ b) := by
  have hkey : 0 ≤ (a + b) ⬝ᵥ Q *ᵥ (a + b) := quad_nonneg hQ _
  have hs : (a - b) ⬝ᵥ Q *ᵥ (a - b) =
      a ⬝ᵥ Q *ᵥ a - a ⬝ᵥ Q *ᵥ b - b ⬝ᵥ Q *ᵥ a + b ⬝ᵥ Q *ᵥ b := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  have ha : (a + b) ⬝ᵥ Q *ᵥ (a + b) =
      a ⬝ᵥ Q *ᵥ a + a ⬝ᵥ Q *ᵥ b + b ⬝ᵥ Q *ᵥ a + b ⬝ᵥ Q *ᵥ b := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    ring
  rw [ha] at hkey
  rw [hs]
  linarith only [hkey]

/-- Scalar homogeneity of a quadratic form. -/
private theorem quad_smul (Q : Mat d) (c : ℝ) (v : Vec d) :
    (c • v) ⬝ᵥ Q *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ Q *ᵥ v) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  ring

/-! ## The transposed bound -/

/-- **The transposed matrix obeys the same normalized bound.**  If
`|m^{-1/2}Kx|² ≤ λ|m^{1/2}x|²` for every `x`, the same holds for `Kᵗ`.  The
proof is Cauchy–Schwarz in the `m` metric at the vector `m^{-1}Kᵗx`. -/
theorem quad_transpose_le {m K : Mat d} (hm : m.PosDef) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hK : ∀ x : Vec d, (K *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ x) ≤ lam * (x ⬝ᵥ m *ᵥ x))
    (x : Vec d) :
    (Kᵀ *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (Kᵀ *ᵥ x) ≤ lam * (x ⬝ᵥ m *ᵥ x) := by
  set u : Vec d := Kᵀ *ᵥ x with hu
  set v : Vec d := m⁻¹ *ᵥ u with hv
  have hmv : m *ᵥ v = u := by
    rw [hv, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hm), Matrix.one_mulVec]
  have hPsi : v ⬝ᵥ m *ᵥ v = u ⬝ᵥ m⁻¹ *ᵥ u := by
    rw [hmv, hv, dotProduct_comm]
  have hswap : u ⬝ᵥ m⁻¹ *ᵥ u = x ⬝ᵥ K *ᵥ v := by
    rw [← hv, hu, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  set t : ℝ := u ⬝ᵥ m⁻¹ *ᵥ u with ht
  have ht0 : 0 ≤ t := quad_nonneg hm.inv.posSemidef u
  have hPsix : 0 ≤ x ⬝ᵥ m *ᵥ x := quad_nonneg hm.posSemidef x
  have hcs : (x ⬝ᵥ K *ᵥ v) ^ 2 ≤
      (x ⬝ᵥ m *ᵥ x) * ((K *ᵥ v) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ v)) :=
    dotProduct_sq_le_quad_mul_quad hm x (K *ᵥ v)
  have hKv : (K *ᵥ v) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ v) ≤ lam * t := by
    have h := hK v
    rwa [hPsi] at h
  have hsq : t ^ 2 ≤ (lam * (x ⬝ᵥ m *ᵥ x)) * t := by
    have hrw : (lam * (x ⬝ᵥ m *ᵥ x)) * t = (x ⬝ᵥ m *ᵥ x) * (lam * t) := by ring
    rw [hrw]
    calc t ^ 2 = (x ⬝ᵥ K *ᵥ v) ^ 2 := by rw [← hswap]
      _ ≤ (x ⬝ᵥ m *ᵥ x) * ((K *ᵥ v) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ v)) := hcs
      _ ≤ (x ⬝ᵥ m *ᵥ x) * (lam * t) :=
          mul_le_mul_of_nonneg_left hKv hPsix
  exact le_of_sq_le_mul ht0 (mul_nonneg hlam hPsix) hsq

/-- **The antisymmetric part obeys the same normalized bound.** -/
theorem quad_responseSkew_le {m K : Mat d} (hm : m.PosDef) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hK : ∀ x : Vec d, (K *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ x) ≤ lam * (x ⬝ᵥ m *ᵥ x))
    (x : Vec d) :
    (Response.responseSkew K *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (Response.responseSkew K *ᵥ x) ≤
      lam * (x ⬝ᵥ m *ᵥ x) := by
  have hexp : Response.responseSkew K *ᵥ x =
      (2 : ℝ)⁻¹ • (K *ᵥ x - Kᵀ *ᵥ x) := by
    rw [Response.responseSkew, Matrix.smul_mulVec,
      conjTranspose_eq_transpose', Matrix.sub_mulVec]
  rw [hexp, quad_smul]
  have hpar := quad_sub_le_two hm.inv.posSemidef (K *ᵥ x) (Kᵀ *ᵥ x)
  have h1 := hK x
  have h2 := quad_transpose_le hm hlam hK x
  have hfour : ((2 : ℝ)⁻¹) ^ 2 = 1 / 4 := by norm_num
  rw [hfour]
  linarith only [hpar, h1, h2]

/-! ## The two-sided comparison of the terminal mean -/

private theorem toFullBlockVec_pair (x y : Vec d) :
    toFullBlockVec ((x, y) : BlockVec d) = Sum.elim x y := by
  funext α
  cases α <;> rfl

/-- **The normalized Schur coordinate of a two-sidedly comparable block.**  If
the block `A` with Schur data `(S, S_*, K)` satisfies `A ≤ C M_0` and
`M_0 ≤ κ A` for the split metric `M_0 = diag(m,m^{-1})`, then
`|m^{-1/2}Kx|² ≤ κ C |m^{1/2}x|²`. -/
theorem schur_skew_quad_le_of_sandwich {m : Mat d}
    {A : BlockMat d} {S SStar K : Mat d} (hS : S.PosDef)
    (hform : toFullBlockMat A = schurBlock S SStar K)
    {C kap : ℝ} (hkap : 0 ≤ kap)
    (hup : BlockMatLoewnerLE A (blockScale C (blockDiag m m⁻¹)))
    (hlow : BlockMatLoewnerLE (blockDiag m m⁻¹) (blockScale kap A))
    (x : Vec d) :
    (K *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ x) ≤ kap * C * (x ⬝ᵥ m *ᵥ x) := by
  -- the quadratic form of `A`, slot by slot
  have hquadA : ∀ p q : Vec d,
      blockVecDot ((p, q) : BlockVec d)
        (blockMatVecMul A ((p, q) : BlockVec d)) =
        p ⬝ᵥ S *ᵥ p + (q - K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q - K *ᵥ p) := by
    intro p q
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, hform, toFullBlockVec_pair,
      Response.quadratic_schurBlock]
  have hquadM : ∀ p q : Vec d,
      blockVecDot ((p, q) : BlockVec d)
        (blockMatVecMul (blockDiag m m⁻¹) ((p, q) : BlockVec d)) =
        p ⬝ᵥ m *ᵥ p + q ⬝ᵥ m⁻¹ *ᵥ q :=
    fun p q => Response.metricBlockNormSq_eq m ((p, q) : BlockVec d)
  -- the upper half at `(x, 0)`
  have hupx := hup ((x, 0) : BlockVec d)
  rw [blockVecDot_blockMatVecMul_blockScale, hquadA, hquadM] at hupx
  have hzero : ((0 : Vec d) - K *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ ((0 : Vec d) - K *ᵥ x) =
      (K *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (K *ᵥ x) := by
    have hneg : (0 : Vec d) - K *ᵥ x = -(K *ᵥ x) := by abel
    rw [hneg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have hzeroM : (0 : Vec d) ⬝ᵥ m⁻¹ *ᵥ (0 : Vec d) = 0 := by
    rw [Matrix.mulVec_zero, dotProduct_zero]
  rw [hzero, hzeroM, add_zero] at hupx
  have hSx : 0 ≤ x ⬝ᵥ S *ᵥ x := quad_nonneg hS.posSemidef x
  have hupper : (K *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (K *ᵥ x) ≤ C * (x ⬝ᵥ m *ᵥ x) := by
    linarith only [hupx, hSx]
  -- the lower half at `(0, Kx)`
  have hlowy := hlow ((0, K *ᵥ x) : BlockVec d)
  rw [blockVecDot_blockMatVecMul_blockScale, hquadA, hquadM] at hlowy
  have hz1 : (0 : Vec d) ⬝ᵥ m *ᵥ (0 : Vec d) = 0 := by
    rw [Matrix.mulVec_zero, dotProduct_zero]
  have hz2 : (0 : Vec d) ⬝ᵥ S *ᵥ (0 : Vec d) = 0 := by
    rw [Matrix.mulVec_zero, dotProduct_zero]
  have hz3 : K *ᵥ (0 : Vec d) = 0 := Matrix.mulVec_zero K
  rw [hz1, hz2, hz3, zero_add, zero_add, sub_zero] at hlowy
  have hlower : (K *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ x) ≤
      kap * ((K *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (K *ᵥ x)) := by
    linarith only [hlowy]
  calc (K *ᵥ x) ⬝ᵥ m⁻¹ *ᵥ (K *ᵥ x)
      ≤ kap * ((K *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (K *ᵥ x)) := hlower
    _ ≤ kap * (C * (x ⬝ᵥ m *ᵥ x)) := mul_le_mul_of_nonneg_left hupper hkap
    _ = kap * C * (x ⬝ᵥ m *ᵥ x) := by ring

/-- **The response skew of a two-sidedly comparable block is normalized-small.**
This is the `τ`-input of `blockSize_skewBlockCongr_reference_le` at the
recentered reference, where the canonical shear has been removed. -/
theorem responseSkew_quad_le_of_sandwich {m : Mat d} (hm : m.PosDef)
    {A : BlockMat d} {S SStar K : Mat d} (hS : S.PosDef)
    (hform : toFullBlockMat A = schurBlock S SStar K)
    {C kap : ℝ} (hC : 0 ≤ C) (hkap : 0 ≤ kap)
    (hup : BlockMatLoewnerLE A (blockScale C (blockDiag m m⁻¹)))
    (hlow : BlockMatLoewnerLE (blockDiag m m⁻¹) (blockScale kap A))
    (x : Vec d) :
    vecDot (matVecMul (Response.responseSkew K) x)
        (matVecMul m⁻¹ (matVecMul (Response.responseSkew K) x)) ≤
      Real.sqrt (kap * C) ^ 2 * vecDot x (matVecMul m x) := by
  have hlam : 0 ≤ kap * C := mul_nonneg hkap hC
  have hsq : Real.sqrt (kap * C) ^ 2 = kap * C := Real.sq_sqrt hlam
  rw [hsq]
  exact quad_responseSkew_le hm hlam
    (fun z => schur_skew_quad_le_of_sandwich hS hform hkap hup hlow z) x

end

end HCPolySupport.HighContrast.Quenched
