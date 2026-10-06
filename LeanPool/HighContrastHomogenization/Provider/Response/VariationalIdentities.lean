/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DomainBridge
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge

/-!
# High-contrast homogenization: Provider.Response.VariationalIdentities

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The variational identities in block form

The weak-norm estimate for the optimizer state reads the Chapter 2 variational
layer through a handful of displayed identities, all written on the
doubled block state `X(V) = (∇v, a∇v)` of the maximizer and on the coarse block
`𝐀(V;a)`.  This file transcribes them.

* the self-duality of the diagonal metric `M_0 = diag(m_0, m_0^{-1})`:
  `R M_0 R = M_0^{-1}`, read here both multiplicatively and on the quadratic
  form, which is the only way the proof uses it.
* the average of the optimizer state, `(X(V))_V = (R𝐀(V;a) + I_{2d})P` of
  [Armstrong–Kuusi, (2.32)] in the normalization used by the paper, together
  with its difference form.
* the exact identity behind the comparison of the optimizer averages of two
  cells.
* the energy identity for the optimizer,
  `J(V,p,q;a) = ½‖σ^{1/2}∇v‖²_{L̲²(V)}` of [Armstrong–Kuusi, (2.30)], and
* the pointwise energy of the optimizer state, the substitution
  `X_t·𝐀X_t = 2∇v_t·σ∇v_t` into the block of [Armstrong–Kuusi, (2.8)], with
  its averaged form `‖𝐀^{1/2}X_t‖²_{L̲²} = 2ℰ_t²`, and
* the expansion of the response functional around its maximizer, the per-cell
  half of the exact factor-two response identity.

Everything is proved on an arbitrary Chapter 2 domain, which is where the
Chapter 2 layer states it, and then specialized to the parent cell `U_t = q□_t`
and to an aligned cell `U_k(z) = z + q□_k` through the bridge of
`HCPoly.Provider.Response.DomainBridge`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## Elementary block arithmetic used by the identities -/

/-- The swap matrix `R` of `s.scale.selection` exchanges the two slots of a
doubled vector. -/
@[simp] theorem blockMatVecMul_blockR (X : BlockVec d) :
    blockMatVecMul (blockR d) X = (X.2, X.1) := by
  have h : blockMatVecMul (blockR d) X =
      (matVecMul 0 X.1 + matVecMul 1 X.2, matVecMul 1 X.1 + matVecMul 0 X.2) := rfl
  rw [h, zero_matVecMul, zero_matVecMul, matVecMul_one, matVecMul_one, zero_add, add_zero]

/-- The block reflection `A ↦ RAR` of the ambient layer exchanges the two
diagonal entries of a block diagonal matrix. -/
theorem blockReflect_blockDiag (A B : Mat d) :
    blockReflect (blockDiag A B) = blockDiag B A := rfl

/-- Block diagonal matrices multiply entrywise. -/
theorem blockMatMul_blockDiag (A B C E : Mat d) :
    blockMatMul (blockDiag A B) (blockDiag C E) = blockDiag (A * C) (B * E) := by
  simp [blockMatMul, blockDiag]

/-- The doubled matrix-vector product is additive in the matrix, in the
difference form the defect `𝐀(V) - 𝐀(W)` is written in. -/
theorem blockMatVecMul_blockSub (A B : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockSub A B) X = blockMatVecMul A X - blockMatVecMul B X := by
  have h : blockMatVecMul (blockSub A B) X =
      (matVecMul (A.upperLeft - B.upperLeft) X.1 +
          matVecMul (A.upperRight - B.upperRight) X.2,
        matVecMul (A.lowerLeft - B.lowerLeft) X.1 +
          matVecMul (A.lowerRight - B.lowerRight) X.2) := rfl
  rw [h, sub_matVecMul, sub_matVecMul, sub_matVecMul, sub_matVecMul]
  have h1 : blockMatVecMul A X - blockMatVecMul B X =
      (matVecMul A.upperLeft X.1 + matVecMul A.upperRight X.2 -
          (matVecMul B.upperLeft X.1 + matVecMul B.upperRight X.2),
        matVecMul A.lowerLeft X.1 + matVecMul A.lowerRight X.2 -
          (matVecMul B.lowerLeft X.1 + matVecMul B.lowerRight X.2)) := rfl
  rw [h1, Prod.mk.injEq]
  constructor <;> abel

/-- The quadratic form of a block reflection is the quadratic form of the
original at the reflected vector: `X·(RAR)X = (RX)·A(RX)`. -/
theorem blockVecDot_blockMatVecMul_blockReflect (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockReflect A) X) =
      blockVecDot (blockMatVecMul (blockR d) X)
        (blockMatVecMul A (blockMatVecMul (blockR d) X)) := by
  rw [blockMatVecMul_blockR]
  have hL : blockVecDot X (blockMatVecMul (blockReflect A) X) =
      vecDot X.1 (matVecMul A.lowerRight X.1 + matVecMul A.lowerLeft X.2) +
        vecDot X.2 (matVecMul A.upperRight X.1 + matVecMul A.upperLeft X.2) := rfl
  have hR : blockVecDot ((X.2, X.1) : BlockVec d)
      (blockMatVecMul A ((X.2, X.1) : BlockVec d)) =
      vecDot X.2 (matVecMul A.upperLeft X.2 + matVecMul A.upperRight X.1) +
        vecDot X.1 (matVecMul A.lowerLeft X.2 + matVecMul A.lowerRight X.1) := rfl
  rw [hL, hR, vecDot_add_right, vecDot_add_right, vecDot_add_right, vecDot_add_right]
  ring

/-! ## The self-dual diagonal metric -/

/-- **`R M_0 R = M_0^{-1}`, multiplicative form.**  The diagonal metric
`M_0 = diag(m_0, m_0^{-1})` and its block reflection are inverse to one
another. -/
theorem blockMatMul_metric_blockReflect {m : Mat d} (hm : IsUnit m.det) :
    blockMatMul (blockDiag m m⁻¹) (blockReflect (blockDiag m m⁻¹)) = blockIdentity d := by
  rw [blockReflect_blockDiag, blockMatMul_blockDiag, Matrix.mul_nonsing_inv m hm,
    Matrix.nonsing_inv_mul m hm]
  rfl

/-- **`R M_0 R = M_0^{-1}`**: the inverse of the diagonal metric is its block
reflection. -/
theorem blockMatInv_metric_eq_blockReflect {m : Mat d} (hm : IsUnit m.det) :
    blockMatInv (blockDiag m m⁻¹) = blockReflect (blockDiag m m⁻¹) := by
  refine toFullBlockMat_injective ?_
  rw [toFullBlockMat_blockMatInv]
  refine Matrix.inv_eq_right_inv ?_
  rw [← toFullBlockMat_blockMatMul, blockMatMul_metric_blockReflect hm,
    toFullBlockMat_blockIdentity]

/-- **`M_0^{1/2} = R M_0^{-1/2} R` on the quadratic form**, which is the only
reading the weak-norm estimate uses:
`|M_0^{1/2}(RZ)|² = |M_0^{-1/2}Z|²`, the right side being the quadratic form of
`M_0^{-1} = R M_0 R`. -/
theorem metric_quadratic_blockR (m : Mat d) (Z : BlockVec d) :
    blockVecDot (blockMatVecMul (blockR d) Z)
        (blockMatVecMul (blockDiag m m⁻¹) (blockMatVecMul (blockR d) Z)) =
      blockVecDot Z (blockMatVecMul (blockReflect (blockDiag m m⁻¹)) Z) :=
  (blockVecDot_blockMatVecMul_blockReflect (blockDiag m m⁻¹) Z).symm

/-! ## The optimizer average -/

/-- **The average identity `(X(V))_V = (R𝐀(V;a) + I_{2d})P`**
([Armstrong–Kuusi, (2.32)]).
Here `X(V) = (∇v, a∇v)` is the doubled state of the response maximizer, `P` is
the load vector `(-p, q)`, and the right side is written as `R(𝐀P) + P` because
`R` acts by exchanging the two slots. -/
theorem blockAverage_eq {U : Domain d} (a : CoeffOn U) {p q : Vec d} {v : Solution U a}
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    ((Book.Ch02.averageGradient U a v, averageFlux U a v) : BlockVec d) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) ((-p, q) : BlockVec d)) +
        ((-p, q) : BlockVec d) := by
  have hT := Internal.Ch02.BookCh02.responseBasicVariationalIdentitiesTheory U a
  have hg := hT.averageGradient_eq hv
  have hf := hT.averageFlux_eq hv
  set M := coarseMatrices U a with hM
  have hfst : (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) ((-p, q) : BlockVec d)).1 =
      -matVecMul M.b p - matVecMul (matTranspose M.kappa) (matVecMul M.sigmaStarInv q) := by
    have h : (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) ((-p, q) : BlockVec d)).1 =
        matVecMul M.b (-p) + matVecMul (-(matTranspose M.kappa * M.sigmaStarInv)) q := rfl
    rw [h, matVecMul_neg, neg_matVecMul, matVecMul_mul, sub_eq_add_neg]
  have hsnd : (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) ((-p, q) : BlockVec d)).2 =
      matVecMul M.sigmaStarInv (q + matVecMul M.kappa p) := by
    have h : (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) ((-p, q) : BlockVec d)).2 =
        matVecMul (-(M.sigmaStarInv * M.kappa)) (-p) + matVecMul M.sigmaStarInv q := rfl
    rw [h, neg_matVecMul, matVecMul_neg, neg_neg, matVecMul_add, matVecMul_mul]
    abel
  rw [blockMatVecMul_blockR, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [hg, hsnd]
    abel
  · rw [hf, hfst]
    abel

/-- **The difference of two optimizer averages**: subtracting two instances of
the average identity at the same load leaves `R` applied to the block defect. -/
theorem blockAverage_sub_eq {U W : Domain d} (a : CoeffOn U) (b : CoeffOn W)
    {p q : Vec d} {v : Solution U a} {w : Solution W b}
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) (hw : Book.Ch02.IsResponseMaximizer W b p q w) :
    ((Book.Ch02.averageGradient U a v, averageFlux U a v) : BlockVec d) -
        ((Book.Ch02.averageGradient W b w, averageFlux W b w) : BlockVec d) =
      blockMatVecMul (blockR d)
        (blockMatVecMul
          (blockSub (Book.Ch02.coarseBlockMatrix U a) (Book.Ch02.coarseBlockMatrix W b))
          ((-p, q) : BlockVec d)) := by
  rw [blockAverage_eq a hv, blockAverage_eq b hw, blockMatVecMul_blockSub,
    blockMatVecMul_blockR, blockMatVecMul_blockR, blockMatVecMul_blockR]
  rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub,
    Prod.mk.injEq]
  constructor <;> abel

/-- **The exact comparison identity** for the optimizer averages of two cells:
`|M_0^{1/2}((X(V))_V - (X(W))_W)|² = P·(𝐀(V) - 𝐀(W))M_0^{-1}(𝐀(V) - 𝐀(W))P`,
the right side being read through the self-duality `M_0^{-1} = R M_0 R`. -/
theorem metricNormSq_blockAverage_sub {U W : Domain d} (a : CoeffOn U) (b : CoeffOn W)
    {p q : Vec d} {v : Solution U a} {w : Solution W b} (m : Mat d)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v)
    (hw : Book.Ch02.IsResponseMaximizer W b p q w) :
    blockVecDot
        (((Book.Ch02.averageGradient U a v, averageFlux U a v) : BlockVec d) -
          ((Book.Ch02.averageGradient W b w, averageFlux W b w) : BlockVec d))
        (blockMatVecMul (blockDiag m m⁻¹)
          (((Book.Ch02.averageGradient U a v, averageFlux U a v) : BlockVec d) -
            ((Book.Ch02.averageGradient W b w, averageFlux W b w) : BlockVec d))) =
      blockVecDot
        (blockMatVecMul
          (blockSub (Book.Ch02.coarseBlockMatrix U a) (Book.Ch02.coarseBlockMatrix W b))
          ((-p, q) : BlockVec d))
        (blockMatVecMul (blockReflect (blockDiag m m⁻¹))
          (blockMatVecMul
            (blockSub (Book.Ch02.coarseBlockMatrix U a) (Book.Ch02.coarseBlockMatrix W b))
            ((-p, q) : BlockVec d))) := by
  rw [blockAverage_sub_eq a b hv hw]
  exact metric_quadratic_blockR m _

/-! ## The two energy identities -/

/-- **The maximizer energy identity** ([Armstrong–Kuusi, (2.30)]):
`J(V,p,q;a) = ½‖σ^{1/2}∇v(·,V,p,q;a)‖²_{L̲²(V)}`, the norm being the normalized
one and `variationEnergyValue` being its square. -/
theorem responseJ_eq_energy {U : Domain d} (a : CoeffOn U) {p q : Vec d}
    {v : Solution U a} (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    responseJ U a p q = (1 / 2 : ℝ) * variationEnergyValue U a v :=
  (Internal.Ch02.BookCh02.responseBasicVariationalIdentitiesTheory U
    a).responseJ_eq_energy hv

/-- The pointwise block energy of a gradient-flux pair, at a single point where
the symmetric part of the coefficient is invertible: substituting
`X = (ξ, Aξ)` into the pointwise block of [Armstrong–Kuusi, (2.8)] gives `2ξ·σξ`.  This
is the algebraic core of the pointwise energy of the optimizer state. -/
theorem blockEnergy_gradient_flux_of_isUnit {A : Mat d} (hdet : IsUnit (symmPart A).det)
    (g : Vec d) :
    blockVecDot ((g, matVecMul A g) : BlockVec d)
        (blockMatVecMul (blockMatrixOfCoeff A) ((g, matVecMul A g) : BlockVec d)) =
      2 * vecDot g (matVecMul (symmPart A) g) := by
  have h := pointwiseBlockEnergy_pair_eq_symmPart_sum_of_isUnit_det_symmPart A hdet g 0
  rw [add_zero, matVecMul_zero, sub_zero, vecDot_zero_left] at h
  linarith only [h]

/-- **The pointwise energy substitution**, the first of the two pointwise energy
identities:
`X_t·𝐀X_t = 2∇v_t·σ∇v_t` almost everywhere on the domain, for the doubled state
`X_t = (∇v_t, a∇v_t)` of any field `g` and the pointwise block of
[Armstrong–Kuusi, (2.8)]. -/
theorem pointwise_block_energy {U : Domain d} (a : CoeffOn U) (g : Vec d → Vec d) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      blockVecDot ((g x, matVecMul (a.toCoeffField x) (g x)) : BlockVec d)
          (blockMatVecMul (blockMatrixField a x)
            ((g x, matVecMul (a.toCoeffField x) (g x)) : BlockVec d)) =
        2 * vecDot (g x) (matVecMul (symmPart (a.toCoeffField x)) (g x)) := by
  filter_upwards [a.aeElliptic] with x hx
  exact blockEnergy_gradient_flux_of_isUnit
    (isUnit_det_symmPart_of_isEllipticMatrix hx) (g x)

/-- **The averaged energy identity**, the second of the two pointwise energy
identities:
`‖𝐀^{1/2}X_t‖²_{L̲²(U_t)} = 2ℰ_t²`, with `ℰ_t² = ‖σ^{1/2}∇v_t‖²_{L̲²(U_t)}` the
`variationEnergyValue` of the maximizer. -/
theorem average_block_energy_eq {U : Domain d} (a : CoeffOn U) (v : Solution U a) :
    Book.Ch02.average U (fun x =>
        blockVecDot ((v.toH1.grad x, matVecMul (a.toCoeffField x) (v.toH1.grad x)) : BlockVec d)
          (blockMatVecMul (blockMatrixField a x)
            ((v.toH1.grad x, matVecMul (a.toCoeffField x) (v.toH1.grad x)) : BlockVec d))) =
      2 * variationEnergyValue U a v := by
  have h : Book.Ch02.average U (fun x =>
        blockVecDot ((v.toH1.grad x, matVecMul (a.toCoeffField x) (v.toH1.grad x)) : BlockVec d)
          (blockMatVecMul (blockMatrixField a x)
            ((v.toH1.grad x, matVecMul (a.toCoeffField x) (v.toH1.grad x)) : BlockVec d))) =
      Book.Ch02.average U (fun x =>
        2 * vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x))) := by
    unfold Book.Ch02.average
    congr 1
    exact MeasureTheory.integral_congr_ae (pointwise_block_energy a v.toH1.grad)
  rw [h]
  unfold variationEnergyValue variationEnergyIntegrand Book.Ch02.average
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The expansion of the response functional around its maximizer, in block
form**: for every admissible competitor `w`,

  `⨍_V ‖𝐀^{1/2}(X(V) - X_w)‖² = 4(J(V,p,q;a) - ⨍_V(-½∇w·σ∇w - p·a∇w + q·∇w))`,

the printed identity together with the remark that its right side *"is one
quarter of the corresponding block energy"*, because the difference of two
primal optimizer fields has the form `(∇φ, a∇φ)` and the pointwise energy
identity applies to it.  This is the per-cell half of the exact factor-two
response identity; the averaging over the aligned subdivision is the
exact-partition step. -/
theorem average_block_energy_sub_eq {U : Domain d} (a : CoeffOn U) {p q : Vec d}
    {v : Solution U a} (hv : Book.Ch02.IsResponseMaximizer U a p q v) (w : Solution U a) :
    Book.Ch02.average U (fun x =>
        blockVecDot ((v.toH1.grad x - w.toH1.grad x,
              matVecMul (a.toCoeffField x) (v.toH1.grad x - w.toH1.grad x)) : BlockVec d)
          (blockMatVecMul (blockMatrixField a x)
            ((v.toH1.grad x - w.toH1.grad x,
              matVecMul (a.toCoeffField x) (v.toH1.grad x - w.toH1.grad x)) : BlockVec d))) =
      4 * (responseJ U a p q - responseValue U a p q w) := by
  have hT := Internal.Ch02.BookCh02.responseBasicVariationalIdentitiesTheory U a
  have hsecond := hT.secondVariation_eq hv w
  have h : Book.Ch02.average U (fun x =>
        blockVecDot ((v.toH1.grad x - w.toH1.grad x,
              matVecMul (a.toCoeffField x) (v.toH1.grad x - w.toH1.grad x)) : BlockVec d)
          (blockMatVecMul (blockMatrixField a x)
            ((v.toH1.grad x - w.toH1.grad x,
              matVecMul (a.toCoeffField x) (v.toH1.grad x - w.toH1.grad x)) : BlockVec d))) =
      Book.Ch02.average U (fun x =>
        2 * vecDot (v.toH1.grad x - w.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x - w.toH1.grad x))) := by
    unfold Book.Ch02.average
    congr 1
    exact MeasureTheory.integral_congr_ae
      (pointwise_block_energy a (fun x => v.toH1.grad x - w.toH1.grad x))
  have hhalf : secondVariationEnergyValue U a v w =
      Book.Ch02.average U (fun x =>
        (1 / 2 : ℝ) * vecDot (v.toH1.grad x - w.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x - w.toH1.grad x))) := rfl
  rw [h, hsecond, hhalf]
  unfold Book.Ch02.average
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

end

end Response
end HighContrast
end HCPolySupport
