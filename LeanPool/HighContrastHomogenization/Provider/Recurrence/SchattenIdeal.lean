/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.SchattenDefinedness
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.DetTransport
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSandwich

/-!
# High-contrast homogenization: Provider.Recurrence.SchattenIdeal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The ideal property of the Schatten size

The fixed-grid recurrence changes the normalization of the averaged response
from the child mean `E_j` to the parent mean `E_p` through the exact congruence
`E_p^{-1/2}(G-E_j)E_p^{-1/2} = C^t(E_j^{-1/2}(G-E_j)E_j^{-1/2})C` with
`C = E_j^{1/2}E_p^{-1/2}`, and then transports the Schatten size across it.  The
result is the averaged fluctuation after the change of normalization, in the
proof of `p.fixed.geometry.parent.child.recurrence`, whose constant is allowed to
depend on the dimension and on the exponent.

The transport is the ideal property of the Schatten norm, read through the
scalar Loewner sandwich.  A symmetric block `H` is caught between
`∓|H|_{S_Q}I`; congruence preserves the Loewner order, so `C^tHC` is caught
between `∓|H|_{S_Q}C^tC`; and `C^tC` is the relative mean
`P = E_p^{-1/2}E_jE_p^{-1/2}` of the determinant transport, which lies below
`e^{Δ}I`.  So `C^tHC` is caught between `∓|H|_{S_Q}e^{Δ}I`, and a block caught
between `∓tI` has Schatten size at most `(2d)^{1/Q}t`.  The chain costs the
dimensional factor `(2d)^{1/Q}`, which is the shape of the printed constant
`C(d,Q)`; nothing downstream sees the loss.

The exact ideal inequality `|C^tHC|_{S_Q} ≤ |C^tC|·|H|_{S_Q}` is stronger than
what is proved here, and is not available by this argument: it asks the spectrum
of `C^tHC` to be dominated by that of `H` in the sense of majorization, whereas
the Loewner order only bounds each eigenvalue separately.

The final section carries the pointwise estimate to the mixed norm
`‖·‖_{L^Q(S_Q)}`, which is where the recurrence uses it: combined with the
averaging estimate of `l.fixed.geometry.matrix.averaging` at the child
normalization it produces the printed display at the parent normalization.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The normalized block -/

/-- The flattening of the `F`-normalization is the literal congruence by the
inverse square root. -/
theorem toFullBlockMat_normalizedBlock (H F : BlockMat d) :
    toFullBlockMat (normalizedBlock H F) =
      matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat H * matSqrt (toFullBlockMat F)⁻¹ := by
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]

/-! ## The transported Schatten size -/

/-- **The ideal property of the Schatten size, in the normalization the
fixed-grid recurrence uses.**  Changing the normalization of a symmetric block
from the child mean to the parent mean multiplies its Schatten size by at most
`(2d)^{1/Q}e^{Δ}`, the determinant increment entering through the Loewner bound
`P ≤ e^{Δ}I` on the relative mean. -/
theorem schattenSize_le_of_le {Ej Ep H : BlockMat d} (hEj : (toFullBlockMat Ej).PosDef)
    (hEp : (toFullBlockMat Ep).PosDef) (hmean : toFullBlockMat Ep ≤ toFullBlockMat Ej)
    (hH : IsSymmetricBlockMat H) {Q : ℝ} (hQ : 0 < Q) :
    schattenSize Q H Ep ≤ (2 * d : ℝ) ^ Q⁻¹ *
      Real.exp (blockLogDet Ej - blockLogDet Ep) * schattenSize Q H Ej := by
  set Fj : FullBlockMat d := toFullBlockMat Ej with hFj
  set Fp : FullBlockMat d := toFullBlockMat Ep with hFp
  set C : FullBlockMat d := matSqrt Fj * matSqrt Fp⁻¹ with hCdef
  set e : ℝ := Real.exp (Real.log Fj.det - Real.log Fp.det) with hedef
  have hsymj : IsSymmetricBlockMat (normalizedBlock H Ej) :=
    isSymmetricBlockMat_normalizedBlock hH
  have hsymp : IsSymmetricBlockMat (normalizedBlock H Ep) :=
    isSymmetricBlockMat_normalizedBlock hH
  set s : ℝ := schattenNorm Q (normalizedBlock H Ej) with hsdef
  have hs0 : 0 ≤ s := zero_le_schattenNorm hsymj Q
  have he0 : 0 < e := Real.exp_pos _
  -- The congruence carrying the child normalization to the parent one.
  have hcongr : toFullBlockMat (normalizedBlock H Ep)
      = Cᴴ * toFullBlockMat (normalizedBlock H Ej) * C := by
    rw [toFullBlockMat_normalizedBlock, toFullBlockMat_normalizedBlock,
      conjTranspose_eq_transpose', hCdef]
    exact normalize_congr hEj hEp
  -- The relative mean is the Gram matrix of that congruence.
  have hCC : Cᴴ * C = matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹ := by
    have hTj : (matSqrt Fj)ᵀ = matSqrt Fj :=
      isSymm_of_isHermitian (matSqrt_spec hEj.posSemidef).1.isHermitian
    have hTp : (matSqrt Fp⁻¹)ᵀ = matSqrt Fp⁻¹ := transpose_matSqrt_inv hEp
    have hsq : matSqrt Fj * matSqrt Fj = Fj := (matSqrt_spec hEj.posSemidef).2
    rw [conjTranspose_eq_transpose', hCdef, Matrix.transpose_mul, hTj, hTp]
    calc matSqrt Fp⁻¹ * matSqrt Fj * (matSqrt Fj * matSqrt Fp⁻¹)
        = matSqrt Fp⁻¹ * (matSqrt Fj * matSqrt Fj) * matSqrt Fp⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹ := by rw [hsq]
  -- The relative mean is bounded above by the determinant increment.
  have hPpos : (matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹).PosDef := posDef_normalize hEj hEp
  have hPle : (e • (1 : FullBlockMat d) - matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹).PosSemidef := by
    refine Matrix.le_iff.mp ((norm_le_iff_le_smul_one hPpos.posSemidef he0.le).mp ?_)
    exact (determinant_transport hEj hEp hmean).2.2.2.1
  -- The child sandwich, transported by the congruence.
  obtain ⟨hsub, hadd⟩ := posSemidef_schattenNorm_smul_one_sub_add hsymj hQ
  have hconjsub : ((s * e) • (1 : FullBlockMat d)
      - toFullBlockMat (normalizedBlock H Ep)).PosSemidef := by
    have hc := hsub.conjTranspose_mul_mul_same C
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hCC,
      ← hcongr] at hc
    have hsum := (hPle.smul hs0).add hc
    have halg : s • (e • (1 : FullBlockMat d) - matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹)
        + (s • (matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹) - toFullBlockMat (normalizedBlock H Ep))
        = (s * e) • (1 : FullBlockMat d) - toFullBlockMat (normalizedBlock H Ep) := by
      rw [smul_sub, smul_smul]
      abel
    rwa [halg] at hsum
  have hconjadd : ((s * e) • (1 : FullBlockMat d)
      + toFullBlockMat (normalizedBlock H Ep)).PosSemidef := by
    have hc := hadd.conjTranspose_mul_mul_same C
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hCC,
      ← hcongr] at hc
    have hsum := (hPle.smul hs0).add hc
    have halg : s • (e • (1 : FullBlockMat d) - matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹)
        + (s • (matSqrt Fp⁻¹ * Fj * matSqrt Fp⁻¹) + toFullBlockMat (normalizedBlock H Ep))
        = (s * e) • (1 : FullBlockMat d) + toFullBlockMat (normalizedBlock H Ep) := by
      rw [smul_sub, smul_smul]
      abel
    rwa [halg] at hsum
  have hfinal := schattenNorm_le_of_posSemidef hsymp hQ (mul_nonneg hs0 he0.le) hconjsub hconjadd
  have hrewrite : Real.exp (blockLogDet Ej - blockLogDet Ep) = e := by
    rw [hedef, blockLogDet, blockLogDet, hFj, hFp]
  calc schattenSize Q H Ep = schattenNorm Q (normalizedBlock H Ep) := rfl
    _ ≤ (2 * d : ℝ) ^ Q⁻¹ * (s * e) := hfinal
    _ = (2 * d : ℝ) ^ Q⁻¹ * e * s := by ring
    _ = (2 * d : ℝ) ^ Q⁻¹ * Real.exp (blockLogDet Ej - blockLogDet Ep) *
          schattenSize Q H Ej := by rw [hrewrite, hsdef, schattenSize]

/-! ## The transported average -/

/-- **The ideal property of the Schatten size in the mixed norm.**  A pointwise
inequality between Schatten sizes passes to the `L^Q` norms of a random doubled
block. -/
theorem lqSchattenSize_le_of_le {P : Measure (CoeffSpace d)} {Ej Ep : BlockMat d}
    (hEj : (toFullBlockMat Ej).PosDef) (hEp : (toFullBlockMat Ep).PosDef)
    (hmean : toFullBlockMat Ep ≤ toFullBlockMat Ej) {W : CoeffSpace d → BlockMat d}
    (hW : ∀ a, IsSymmetricBlockMat (W a)) {Q : ℝ} (hQ : 0 < Q)
    (hWm : AEStronglyMeasurable (fun a => schattenSize Q (W a) Ep) P) :
    lqSchattenSize P Q W Ep ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (blockLogDet Ej - blockLogDet Ep)) *
        lqSchattenSize P Q W Ej := by
  set K : ℝ := (2 * d : ℝ) ^ Q⁻¹ * Real.exp (blockLogDet Ej - blockLogDet Ep) with hK
  have hK0 : 0 ≤ K := by positivity
  have hptwise : ∀ a : CoeffSpace d, ‖schattenSize Q (W a) Ep‖
      ≤ ‖(K • fun b => schattenSize Q (W b) Ej) a‖ := by
    intro a
    have hp : (0 : ℝ) ≤ schattenSize Q (W a) Ep :=
      zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock (hW a)) Q
    have hj : (0 : ℝ) ≤ schattenSize Q (W a) Ej :=
      zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock (hW a)) Q
    have hle : schattenSize Q (W a) Ep ≤ K * schattenSize Q (W a) Ej := by
      rw [hK]
      exact schattenSize_le_of_le hEj hEp hmean (hW a) hQ
    simpa [Real.norm_of_nonneg hp, Real.norm_of_nonneg (mul_nonneg hK0 hj)] using hle
  calc lqSchattenSize P Q W Ep
      ≤ eLpNorm (K • fun b => schattenSize Q (W b) Ej) (ENNReal.ofReal Q) P :=
        eLpNorm_mono hWm hptwise
    _ = ‖K‖ₑ * lqSchattenSize P Q W Ej := eLpNorm_const_smul K _ _ _
    _ = ENNReal.ofReal K * lqSchattenSize P Q W Ej := by rw [Real.enorm_eq_ofReal hK0]

/-- **The averaged fluctuation after the change of normalization.**
The averaged centered response is estimated at the child normalization by
`l.fixed.geometry.matrix.averaging`; the ideal property carries that estimate
to the parent normalization at the cost of the determinant increment and a
constant depending only on the dimension and the exponent. -/
theorem transported_average_le {P : Measure (CoeffSpace d)} {Ej Ep : BlockMat d}
    (hEjsymm : IsSymmetricBlockMat Ej) (hEpsymm : IsSymmetricBlockMat Ep)
    (hEj : Book.Ch02.BlockPosDef Ej) (hEp : Book.Ch02.BlockPosDef Ep)
    (hmean : BlockMatLoewnerLE Ep Ej) {W : CoeffSpace d → BlockMat d}
    (hW : ∀ a, IsSymmetricBlockMat (W a)) {Q : ℝ} (hQ : 0 < Q) {c : ℝ}
    {v : ℝ≥0∞} (haverage : lqSchattenSize P Q W Ej ≤ ENNReal.ofReal c * v)
    (hWm : AEStronglyMeasurable (fun a => schattenSize Q (W a) Ep) P) :
    lqSchattenSize P Q W Ep ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹ *
        Real.exp (blockLogDet Ej - blockLogDet Ep) * c) * v := by
  have hEj' : (toFullBlockMat Ej).PosDef := posDef_toFullBlockMat hEjsymm hEj
  have hEp' : (toFullBlockMat Ep).PosDef := posDef_toFullBlockMat hEpsymm hEp
  have hmean' : toFullBlockMat Ep ≤ toFullBlockMat Ej :=
    le_of_blockMatLoewnerLE hEpsymm hEjsymm hmean
  set K : ℝ := (2 * d : ℝ) ^ Q⁻¹ * Real.exp (blockLogDet Ej - blockLogDet Ep) with hK
  have hK0 : 0 ≤ K := by positivity
  calc lqSchattenSize P Q W Ep ≤ ENNReal.ofReal K * lqSchattenSize P Q W Ej :=
        lqSchattenSize_le_of_le hEj' hEp' hmean' hW hQ hWm
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal c * v) := mul_le_mul_right haverage _
    _ = ENNReal.ofReal (K * c) * v := by rw [ENNReal.ofReal_mul hK0, mul_assoc]

end

end Recurrence
end HighContrast
end HCPolySupport
