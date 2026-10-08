/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCell
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra.H1Function
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.OriginCubeBridge

/-!
# High-contrast homogenization: Entry.Response.Core.AffineSobolevPullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `H¹` under an invertible linear pullback

This file extends the `H¹`-function calculus to invertible linear pullbacks: composing an `H¹`
function with an invertible linear change of coordinates again yields an `H¹` function, with the
weak gradient transforming by the transpose of the matrix. It identifies the image of the
reference cube under such a pullback with an adapted cell. For a cutoff transported by the same
kind of linear change of variables, it records the chain rule for the transported gradient and the
adjoint pairing identities distributing the grid between the two slots of the pulled-back pairing.
These are the change-of-variables ingredients of the cutoff argument in
`e.response.cutoff.estimate`,
and the pulled-back `H¹` witness on the reference cube is the input that the response transfer
`p.response.transfer` consumes. The module also records two short facts feeding the diagonal
weak-norm estimate `e.response.weak.estimate`: the branch-free bound on its finite-window head, and
the integrability of the doubled optimizer field on a subcell.
-/

section
/-!
## The branch-free head bound of the cell-average estimate

The cell-average estimate `e.response.weak.estimate` controls its finite-window head by a tail
term whose weight changes across the cutoff `1` of the all-scale maximum `M`: on `M ≤ 1` the head
is bounded through the older-scale weight `3 ^ (-(Quenched.contrastAlpha γ * H))`, while on `1 <
M` the whole
head is absorbed by the recent-scale weight `√M` alone.  This module assembles the two branch
bounds into a single estimate whose right-hand side carries the printed selector
`if 1 < M then √M else 3 ^ (-(Quenched.contrastAlpha γ * H))`, so that a consumer carrying `M`
need not decide
which side of the cutoff it lies on.

Both branch bounds enter as hypotheses and the head, the finite sums, the tail factor and the two
branch constants are abstract, so nothing here depends on how either branch is proved.
-/

namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The branch-free head bound behind `e.response.weak.estimate`.  If the head is bounded by
`Sums + cgood * 3 ^ (-(Quenched.contrastAlpha γ * H)) * Tail` on `M ≤ 1` and by `cbad * √M * Tail`
on `1 < M`,
with `Sums`, `Tail` and the two constants nonnegative, then it is bounded by `Sums` plus
`max cgood cbad` times the printed selector `if 1 < M then √M else 3 ^ (-(Quenched.contrastAlpha γ
* H))` times
`Tail`.  The good-branch weight is `3 ^ (-(Quenched.contrastAlpha γ * H))` rather than `1`, and
must occur with
that factor in the `M ≤ 1` hypothesis for the bound to hold. -/
theorem head_le_add_max_mul_ite {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (H : ℕ) {M : ℝ}
    (hM0 : 0 ≤ M) (Head Sums Tail cgood cbad : ℝ)
    (hcgood : 0 ≤ cgood) (hcbad : 0 ≤ cbad) (hSums : 0 ≤ Sums) (hTail : 0 ≤ Tail)
    (hgood : M ≤ 1 → Head ≤ Sums + cgood * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) * Tail)
    (hbad : 1 < M → Head ≤ cbad * Real.sqrt M * Tail) :
    Head ≤ Sums + max cgood cbad *
      (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) * Tail
        := by
  have hw0 : 0 ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hcgood' : 0 ≤ cgood * Tail := mul_nonneg hcgood hTail
  have hcbad' : 0 ≤ cbad * Tail := mul_nonneg hcbad hTail
  have hgood' : M ≤ 1 → Head - Sums
      ≤ (cgood * Tail) * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) := by
    intro hMle
    calc Head - Sums ≤ cgood * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) * Tail := by
          linarith only [hgood hMle]
      _ = (cgood * Tail) * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) := by ring
  have hbad' : 1 < M → Head - Sums ≤ (cbad * Tail) * Real.sqrt M := by
    intro hMgt
    calc Head - Sums ≤ Head := by linarith only [hSums]
      _ ≤ cbad * Real.sqrt M * Tail := hbad hMgt
      _ = (cbad * Tail) * Real.sqrt M := by ring
  have hkey := branchfree_tail_le γ hγ H M hM0 (cgood * Tail) (cbad * Tail) hcgood' hcbad'
    (Head - Sums) (Head - Sums) hgood' hbad'
  have hkey' : Head - Sums ≤ max (cgood * Tail) (cbad * Tail) *
      (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) := by
    simpa only [ite_self] using hkey
  have hW0 : 0 ≤ (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H :
    ℝ)))) := by
    have hmin0 : 0 ≤ min (Real.sqrt M) ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) :=
      le_min (Real.sqrt_nonneg M) hw0
    exact le_trans hmin0 (le_tail_branch M ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))))
      hM0 hw0)
  have hmax : max (cgood * Tail) (cbad * Tail) ≤ max cgood cbad * Tail := by
    refine max_le ?_ ?_
    · exact mul_le_mul_of_nonneg_right (le_max_left cgood cbad) hTail
    · exact mul_le_mul_of_nonneg_right (le_max_right cgood cbad) hTail
  have hstep : Head - Sums ≤ (max cgood cbad * Tail) *
      (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) :=
    le_trans hkey' (mul_le_mul_of_nonneg_right hmax hW0)
  calc Head = Sums + (Head - Sums) := by ring
    _ ≤ Sums + (max cgood cbad * Tail) *
          (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) := by
        linarith only [hstep]
    _ = Sums + max cgood cbad *
          (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) *
            Tail := by ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the doubled optimizer field on a subcell

Every cell-average step of the diagonal weak-norm estimate moves a matrix through the cell
average of the doubled optimizer field `optimizerField b u = (∇v, b ∇v)`, so each such step
needs both slots of that field to be integrable on the cell.

The gradient slot is `L²` because it is the weak gradient of an `H¹` function, and `L²` of a
finite measure is `L¹`.  The flux slot is `L²` because a uniformly elliptic coefficient field is
essentially bounded on the set where it is elliptic, and the product of a bounded measurable
field with an `L²` gradient is again `L²`.

The ellipticity hypothesis on the flux slot cannot be dropped.  For instance on `(0,1)` take
`∇v ≡ 1` (an `L²` gradient) and the measurable but unbounded scalar field `b x = x⁻¹`: then the
gradient slot is `L²` while the flux `b ∇v = x⁻¹` is not `L¹`.  So a bound on the coefficient
field is exactly what makes the flux slot integrable.

The gradient is `L²` only on the domain `U` to which the `AHarmonicFunction` is attached, so
these statements are asked on subsets `V ⊆ U`.  In the estimate the relevant subsets are the
triadic subcells `adaptedCellAtCenter q (t - n) w` of `HighContrast.adaptedCell q t`, which is why
the box
version below carries the membership `w ∈ triadicIndexBox d n`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The gradient slot of the doubled optimizer field is integrable on every finite-measure
subset of the domain: `H1Function.gradMemL2` gives `L²`, and `L² ⊆ L¹` there. -/
theorem integrableOn_optimizerField_fst_pub {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hVfin : volume V ≠ ⊤) (b : CoeffField d) (u : AHarmonicFunction b U) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField b u x).1 j) V := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have h2 : MemLp (fun x => u.toH1.grad x j) 2 (volume.restrict U) := u.toH1.gradMemL2 j
  have h2' : MemLp (fun x => u.toH1.grad x j) 2 (volume.restrict V) :=
    h2.mono_measure (Measure.restrict_mono hVU le_rfl)
  exact MemLp.integrable (by norm_num) h2'

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The gradient of a pulled-back cutoff

The linear change of variables `x = q y` transports a cutoff `φ` from the adapted cell to the
reference cube as `y ↦ φ (q y)`.  Its gradient is `qᵀ` applied to the gradient of `φ` at `q y`.
The two declarations below record the adjoint identity for the Euclidean pairing and the chain
rule in the coordinatewise gradient convention of the project.  This is the linear-algebraic step
of the cutoff argument in the response estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1,
(A.4)).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The adjoint identity for the Euclidean pairing: the transpose `qᵀ` is the adjoint of `q` with
respect to `vecDot`, i.e. `⟪qᵀ v, z⟫ = ⟪v, q z⟫`. -/
theorem vecDot_matVecMul_transpose {d : ℕ} (q : Mat d) (v z : Vec d) :
    vecDot (matVecMul (matTranspose q) v) z = vecDot v (matVecMul q z) := by
  simp only [vecDot, matVecMul, matTranspose, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The `k`-th coordinate of `∑ j, c j • basisVec j` is `c k`. -/
private theorem sum_smul_basisVec_apply {d : ℕ} (c : Fin d → ℝ) (k : Fin d) :
    (∑ j : Fin d, c j • basisVec j) k = c k := by
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp only [Pi.smul_apply, basisVec_apply, smul_eq_mul, ite_true, mul_one]
  · intro j _ hj
    have hkj : k ≠ j := fun h => hj h.symm
    simp only [Pi.smul_apply, basisVec_apply, smul_eq_mul, ite_eq_right hkj, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The `i`-th column of `q` is the image of the `i`-th basis vector under `matVecMul q`, written
as the linear combination `∑ j, q j i • basisVec j` of basis vectors. -/
private theorem matVecMul_basisVec_eq_sum {d : ℕ} (q : Mat d) (i : Fin d) :
    matVecMul q (basisVec i) = ∑ j : Fin d, q j i • basisVec j := by
  funext k
  rw [sum_smul_basisVec_apply (fun j : Fin d => q j i) k]
  simp only [matVecMul, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, mul_one]
  · intro j _ hj
    simp only [ite_eq_right hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The chain rule for the linear change of variables `x = q y`, in the coordinatewise gradient
convention of the project: the gradient of the pulled-back function `y ↦ φ (q y)` is `qᵀ` applied
to the gradient of `φ` at `q y`, i.e.
`(fun j => (fderiv ℝ (φ ∘ q)) y (basisVec j)) = matVecMul qᵀ (fun j => (fderiv ℝ φ (q y))
(basisVec j))`.
-/
theorem fderiv_comp_matVecMul_basisVec {d : ℕ} (q : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : Vec d) :
    (fun j => (fderiv ℝ (fun z : Vec d => φ (matVecMul q z)) y) (basisVec j))
      = matVecMul (matTranspose q) (fun j => (fderiv ℝ φ (matVecMul q y)) (basisVec j)) := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hderiv : HasFDerivAt (fun z : Vec d => φ (matVecMul q z))
      ((fderiv ℝ φ (matVecMul q y)).comp (matContinuousLinearMap q)) y :=
    (hdiff (matVecMul q y)).hasFDerivAt.comp y ((matContinuousLinearMap q).hasFDerivAt)
  have hfd : fderiv ℝ (fun z : Vec d => φ (matVecMul q z)) y
      = (fderiv ℝ φ (matVecMul q y)).comp (matContinuousLinearMap q) := hderiv.fderiv
  funext i
  rw [hfd, ContinuousLinearMap.comp_apply, matContinuousLinearMap_apply,
    matVecMul_basisVec_eq_sum, map_sum]
  change (∑ j : Fin d, (fderiv ℝ φ (matVecMul q y)) (q j i • basisVec j))
      = ∑ j : Fin d, (matTranspose q) i j *
          (fderiv ℝ φ (matVecMul q y)) (basisVec j)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  simp only [matTranspose, Matrix.transpose_apply]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The two slots of the pulled-back pairing

A linear change of variables `x = q y` transports a cutoff `φ` to `y ↦ φ (q y)`.  The gradient
of the transported cutoff is the transpose `qᵀ` applied to the gradient of `φ` at `q y`; this is
the chain rule recorded in `fderiv_comp_matVecMul_basisVec`.  The three declarations below collect
the linear-algebraic consequences needed to distribute the grid `q` between the two slots of the
Euclidean pairing without cost:  when one slot of the pairing is pulled back by `q⁻¹`, the other
acquires `qᵀ`, and the adjointness of `qᵀ` cancels the two against each other.  This is the
change-of-variables step of the cutoff argument in the response estimate
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- For an invertible matrix `q`, the inverse `q⁻¹` cancels `q` under `matVecMul`: applying `q`
to `q⁻¹ v` returns `v`. -/
theorem matVecMul_matVecMul_inv_cancel {d : ℕ} {q : Mat d} (hq : IsUnit q) (v : Vec d) :
    matVecMul q (matVecMul q⁻¹ v) = v := by
  have hqdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det (A := q)).mp hq
  rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet]
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- The gradient of the pulled-back cutoff `y ↦ φ (q y)` is `qᵀ` applied to the gradient of `φ`
at `q y`, in the coordinatewise gradient convention of the project: the gradient field of the
composition is the transpose of the grid applied to the pulled-back gradient field. -/
theorem scalarCutoffGradientField_comp_eq {d : ℕ} (q : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : Vec d) :
    scalarCutoffGradientField (fun z : Vec d => φ (matVecMul q z)) y
      = matVecMul (matTranspose q) (scalarCutoffGradientField φ (matVecMul q y)) := by
  funext i
  exact congrFun (fderiv_comp_matVecMul_basisVec q hφ y) i

/-- The Euclidean pairing is preserved when the first slot acquires `q⁻¹` and the second the
transpose of the grid: for an invertible `q`,
`⟪q⁻¹ v, ∇(φ ∘ q)(y)⟫ = ⟪v, ∇φ(q y)⟫`. -/
theorem vecDot_pullback_slots {d : ℕ} {q : Mat d} (hq : IsUnit q) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : Vec d) (y : Vec d) :
    vecDot (matVecMul q⁻¹ v)
        (scalarCutoffGradientField (fun z : Vec d => φ (matVecMul q z)) y)
      = vecDot v (scalarCutoffGradientField φ (matVecMul q y)) := by
  rw [scalarCutoffGradientField_comp_eq q hφ y]
  calc
    vecDot (matVecMul q⁻¹ v)
        (matVecMul (matTranspose q) (scalarCutoffGradientField φ (matVecMul q y)))
        = vecDot (matVecMul (matTranspose q) (scalarCutoffGradientField φ (matVecMul q y)))
            (matVecMul q⁻¹ v) := vecDot_comm _ _
    _ = vecDot (scalarCutoffGradientField φ (matVecMul q y))
            (matVecMul q (matVecMul q⁻¹ v)) :=
          vecDot_matVecMul_transpose q _ _
    _ = vecDot (scalarCutoffGradientField φ (matVecMul q y)) v := by
          rw [matVecMul_matVecMul_inv_cancel hq v]
    _ = vecDot v (scalarCutoffGradientField φ (matVecMul q y)) := vecDot_comm _ _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## `H¹` under an invertible linear pullback

The pinned CoarseGraining revision `8ec687c` has
`H1Function` constructors for **restriction** (`Sobolev/H1/BasicLemmas.lean`), **domain casts**
(`Book/Ch03/Theorems/PublicInternalBridges/H1Casts.lean`), **translation**
(`Sobolev/H1/Translation.lean`), **positive scalar dilation**
(`Sobolev/Foundations/CoerciveH1Dilation.lean`) and the two **measure-preserving**
symmetries of the centred cube — coordinate sign flip and coordinate swap
(`Sobolev/H1/OriginCubeSymmetry.lean`) — but **no pullback along a general invertible
linear map**.  That is what this file adds.

The construction is `u ↦ u ∘ q` with the chain-rule gradient `qᵀ (∇u ∘ q)`.  Unlike the sign-flip
and swap cases, `y ↦ q y` is *not* measure preserving, so the `L²` and weak-derivative transfers
both carry the Jacobian factor `|det q|⁻¹`; it cancels between the two sides of the weak
formulation, which is why no hypothesis on `det q` beyond invertibility is needed.

Everything is stated for a general source set `V` with `q V ⊆ U`.  For `p.response.transfer`, the
instance `q = respGrid jStar F`, `V = openCubeSet (originCube d t)`, `U = adaptedCell q t` is proved
inhabited in the last section.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The linear change of variables `x = q y` -/

/-- An invertible matrix acts on `Vec d` as a homeomorphism. -/
@[expose]
def matHomeomorph {q : Mat d} (hq : IsUnit q) : Vec d ≃ₜ Vec d where
  toFun := matVecMul q
  invFun := matVecMul q⁻¹
  left_inv := by
    intro x
    have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
    change Matrix.mulVec q⁻¹ (Matrix.mulVec q x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul q hdet, Matrix.one_mulVec]
  right_inv := by
    intro x
    have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
    change Matrix.mulVec q (Matrix.mulVec q⁻¹ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv q hdet, Matrix.one_mulVec]
  continuous_toFun := (matContinuousLinearMap q).continuous
  continuous_invFun := (matContinuousLinearMap q⁻¹).continuous

@[simp] theorem matHomeomorph_apply {q : Mat d} (hq : IsUnit q) (x : Vec d) :
    matHomeomorph hq x = matVecMul q x := rfl

@[simp] theorem matHomeomorph_symm_apply {q : Mat d} (hq : IsUnit q) (x : Vec d) :
    (matHomeomorph hq).symm x = matVecMul q⁻¹ x := rfl

theorem matVecMul_inv_matVecMul {q : Mat d} (hq : IsUnit q) (x : Vec d) :
    matVecMul q⁻¹ (matVecMul q x) = x := (matHomeomorph hq).symm_apply_apply x

theorem isOpen_image_matVecMul {q : Mat d} (hq : IsUnit q) {V : Set (Vec d)} (hV : IsOpen V) :
    IsOpen (matVecMul q '' V) := (matHomeomorph hq).isOpenMap V hV

theorem measurableEmbedding_matVecMul {q : Mat d} (hq : IsUnit q) :
    MeasurableEmbedding (matVecMul q) := (matHomeomorph hq).measurableEmbedding

/-- The push-forward of restricted Lebesgue measure under an invertible linear map: the Jacobian
factor `|det q|⁻¹` times restricted Lebesgue measure on the image. -/
theorem map_matVecMul_volume_restrict {q : Mat d} (hq : IsUnit q) (V : Set (Vec d)) :
    Measure.map (matVecMul q) (volume.restrict V)
      = ENNReal.ofReal |q.det|⁻¹ • volume.restrict (matVecMul q '' V) := by
  have hdet : q.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
  have hlin : LinearMap.det (Matrix.toLin' q) = q.det := LinearMap.det_toLin' q
  have hcoe : ⇑(Matrix.toLin' q) = matVecMul q := rfl
  have hmap : Measure.map (matVecMul q) (volume : Measure (Vec d))
      = ENNReal.ofReal |q.det|⁻¹ • volume := by
    have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := Matrix.toLin' q) (by rw [hlin]; exact hdet)
    rw [hlin, hcoe, abs_inv] at h
    exact h
  have hemb := measurableEmbedding_matVecMul hq
  have hpre : matVecMul q ⁻¹' (matVecMul q '' V) = V :=
    Set.preimage_image_eq V (matHomeomorph hq).injective
  calc Measure.map (matVecMul q) (volume.restrict V)
      = Measure.map (matVecMul q) (volume.restrict (matVecMul q ⁻¹' (matVecMul q '' V))) := by
        rw [hpre]
    _ = (Measure.map (matVecMul q) volume).restrict (matVecMul q '' V) :=
        (hemb.restrict_map volume _).symm
    _ = ENNReal.ofReal |q.det|⁻¹ • volume.restrict (matVecMul q '' V) := by
        rw [hmap, Measure.restrict_smul]

/-- The set-integral change of variables `x = q y`, with no integrability hypothesis (both sides
are Bochner junk values together). -/
theorem setIntegral_comp_matVecMul_image {q : Mat d} (hq : IsUnit q) (V : Set (Vec d))
    (g : Vec d → ℝ) :
    ∫ y in V, g (matVecMul q y) ∂volume
      = |q.det|⁻¹ * ∫ x in matVecMul q '' V, g x ∂volume := by
  have hemb := measurableEmbedding_matVecMul hq
  rw [← hemb.integral_map g, map_matVecMul_volume_restrict hq V, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-! ## `L²` under the pullback -/

/-- `L²` transfers along the pullback: the Jacobian factor is a finite positive constant, so it
changes nothing about membership. -/
theorem memL2On_comp_matVecMul {q : Mat d} (hq : IsUnit q) {U V : Set (Vec d)}
    (hsub : matVecMul q '' V ⊆ U) {f : Vec d → ℝ} (hf : MemL2On U f) :
    MemL2On V (fun y => f (matVecMul q y)) := by
  have hmap := map_matVecMul_volume_restrict hq V
  have h1 : MemLp f 2 (Measure.map (matVecMul q) (volume.restrict V)) := by
    rw [hmap]
    exact (memL2On_mono hsub hf).smul_measure ENNReal.ofReal_ne_top
  exact MemLp.comp_of_map h1 (matContinuousLinearMap q).continuous.measurable.aemeasurable

/-- A coordinatewise-`L²` vector field on `U` pulls back to one on `V`, after any fixed linear
post-composition `A`.  With `A = qᵀ` this is the gradient slot of the `H¹` pullback; with
`A = q⁻¹` it is the flux slot of the `p.response.transfer` pairing. -/
theorem gradMemL2On_matVecMul_comp_matVecMul {q : Mat d} (hq : IsUnit q) (A : Mat d)
    {U V : Set (Vec d)} (hsub : matVecMul q '' V ⊆ U) {G : Vec d → Vec d}
    (hG : GradMemL2On U G) :
    GradMemL2On V (fun y => matVecMul A (G (matVecMul q y))) := by
  intro i
  change MemL2On V (fun y => matVecMul A (G (matVecMul q y)) i)
  have heq : (fun y => matVecMul A (G (matVecMul q y)) i)
      = ∑ j : Fin d, (fun y : Vec d => A i j * G (matVecMul q y) j) := by
    funext y
    simp [matVecMul, Finset.sum_apply]
  rw [show MemL2On V (fun y => matVecMul A (G (matVecMul q y)) i)
        = MemLp (fun y => matVecMul A (G (matVecMul q y)) i) 2 (volume.restrict V) from rfl, heq]
  exact memLp_finsetSum' _
    (fun j _ => (memL2On_comp_matVecMul hq hsub (hG j)).const_mul (A i j))

/-! ## The chain rule for `x = q y` -/

/-- The image of a coordinate basis vector is the matching column. -/
theorem matVecMul_basisVec (q : Mat d) (i : Fin d) :
    matVecMul q (basisVec i) = ∑ j : Fin d, q j i • basisVec j := by
  funext a
  simp [matVecMul, basisVec_apply, Finset.sum_apply]

/-- The `i`-th coordinate of `qᵀ w`. -/
theorem matVecMul_matTranspose_apply (q : Mat d) (w : Vec d) (i : Fin d) :
    matVecMul (matTranspose q) w i = ∑ j : Fin d, q j i * w j := by
  simp [matVecMul, matTranspose]

/-- The chain rule in the shape the weak formulation consumes: the `i`-th partial of `φ` at
`q⁻¹ x` is the `q`-weighted combination of the partials of `φ ∘ q⁻¹` at `x`. -/
theorem fderiv_apply_basisVec_comp_matVecMul_inv {q : Mat d} (hq : IsUnit q)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) (x : Vec d) :
    (fderiv ℝ φ (matVecMul q⁻¹ x)) (basisVec i)
      = ∑ j : Fin d, q j i *
          (fderiv ℝ (fun z => φ (matVecMul q⁻¹ z)) x) (basisVec j) := by
  set ψ : Vec d → ℝ := fun z => φ (matVecMul q⁻¹ z) with hψdef
  have hψ_diff : Differentiable ℝ ψ := by
    have : ContDiff ℝ (⊤ : ℕ∞) ψ :=
      hφ.comp (matContinuousLinearMap q⁻¹).contDiff
    exact this.differentiable (by simp)
  set y : Vec d := matVecMul q⁻¹ x with hy
  have hxy : matVecMul q y = x := by
    rw [hy]; exact matVecMul_matVecMul_inv_cancel hq x
  have hcomp : (fun z : Vec d => ψ (matVecMul q z)) = φ := by
    funext z
    simp [hψdef, matVecMul_inv_matVecMul hq]
  have hderiv : HasFDerivAt (fun z : Vec d => ψ (matVecMul q z))
      ((fderiv ℝ ψ (matVecMul q y)).comp (matContinuousLinearMap q)) y :=
    ((hψ_diff (matVecMul q y)).hasFDerivAt).comp y
      ((matContinuousLinearMap q).hasFDerivAt)
  rw [hcomp] at hderiv
  have hfd : fderiv ℝ φ y = (fderiv ℝ ψ x).comp (matContinuousLinearMap q) := by
    rw [hxy] at hderiv
    exact hderiv.fderiv
  rw [hfd]
  change (fderiv ℝ ψ x) (matVecMul q (basisVec i)) = _
  rw [matVecMul_basisVec, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

/-! ## The weak gradient under the pullback -/

/-- **The weak-gradient pullback.**  If `u` has weak gradient `Du` on the image `q V`, then
`u ∘ q` has weak gradient `qᵀ (Du ∘ q)` on `V`.  The `L²` hypotheses are used only to move the
finite sum of the chain rule through the integral. -/
theorem hasWeakGradientOn_comp_matVecMul {q : Mat d} (hq : IsUnit q) {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemL2On (matVecMul q '' V) u)
    (hDu : GradMemL2On (matVecMul q '' V) Du)
    (h : HasWeakGradientOn (matVecMul q '' V) u Du) :
    HasWeakGradientOn V (fun y => u (matVecMul q y))
      (fun y => matVecMul (matTranspose q) (Du (matVecMul q y))) := by
  classical
  intro i φ hφ hφ_compact hφ_sub
  set W : Set (Vec d) := matVecMul q '' V with hW
  set ψ : Vec d → ℝ := fun z => φ (matVecMul q⁻¹ z) with hψdef
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp (matContinuousLinearMap q⁻¹).contDiff
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_compact : HasCompactSupport ψ := by
    change HasCompactSupport (φ ∘ (matHomeomorph hq).symm)
    simpa [hψdef, Function.comp] using hφ_compact.comp_homeomorph (matHomeomorph hq).symm
  have hψ_sub : tsupport ψ ⊆ W := by
    intro z hz
    have hz' : matVecMul q⁻¹ z ∈ tsupport φ := by
      rw [show ψ = φ ∘ (matHomeomorph hq).symm from rfl,
        tsupport_comp_eq_preimage φ (matHomeomorph hq).symm] at hz
      exact hz
    exact ⟨matVecMul q⁻¹ z, hφ_sub hz', matVecMul_matVecMul_inv_cancel hq z⟩
  -- the `L²` data on the image
  have hψL2 : MemL2On W ψ := (hψ_cont.memLp_of_hasCompactSupport hψ_compact).restrict W
  have hDψL2 : ∀ j : Fin d, MemL2On W (fun z => (fderiv ℝ ψ z) (basisVec j)) := by
    intro j
    have hcont : Continuous (fun z => (fderiv ℝ ψ z) (basisVec j)) := by
      simpa using (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun z => (fderiv ℝ ψ z) (basisVec j)) := by
      simpa using hψ_compact.fderiv_apply (𝕜 := ℝ) (basisVec j)
    exact (hcont.memLp_of_hasCompactSupport hsupp).restrict W
  -- the identity on the image
  have hkey :
      ∫ x in W, u x * (fderiv ℝ φ (matVecMul q⁻¹ x)) (basisVec i) ∂volume
        = -∫ x in W, matVecMul (matTranspose q) (Du x) i * ψ x ∂volume := by
    have hchain :
        (fun x => u x * (fderiv ℝ φ (matVecMul q⁻¹ x)) (basisVec i))
          = fun x => ∑ j : Fin d, q j i * (u x * (fderiv ℝ ψ x) (basisVec j)) := by
      funext x
      rw [fderiv_apply_basisVec_comp_matVecMul_inv hq hφ i x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [← hψdef]; ring
    have hint1 : ∀ j : Fin d,
        Integrable (fun x => q j i * (u x * (fderiv ℝ ψ x) (basisVec j)))
          (volume.restrict W) := by
      intro j
      simpa [Pi.mul_apply] using (hu.integrable_mul (hDψL2 j)).const_mul (q j i)
    have hint2 : ∀ j : Fin d,
        Integrable (fun x => q j i * (Du x j * ψ x)) (volume.restrict W) := by
      intro j
      simpa [Pi.mul_apply] using ((hDu j).integrable_mul hψL2).const_mul (q j i)
    have hsum1 :
        ∫ x in W, (∑ j : Fin d, q j i * (u x * (fderiv ℝ ψ x) (basisVec j))) ∂volume
          = ∑ j : Fin d, q j i * ∫ x in W, u x * (fderiv ℝ ψ x) (basisVec j) ∂volume := by
      rw [integral_finsetSum _ (fun j _ => hint1 j)]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    have hsum2 :
        ∑ j : Fin d, q j i * ∫ x in W, Du x j * ψ x ∂volume
          = ∫ x in W, matVecMul (matTranspose q) (Du x) i * ψ x ∂volume := by
      have hstep : ∑ j : Fin d, ∫ x in W, q j i * (Du x j * ψ x) ∂volume
          = ∫ x in W, (∑ j : Fin d, q j i * (Du x j * ψ x)) ∂volume :=
        (integral_finsetSum _ (fun j _ => hint2 j)).symm
      calc ∑ j : Fin d, q j i * ∫ x in W, Du x j * ψ x ∂volume
          = ∑ j : Fin d, ∫ x in W, q j i * (Du x j * ψ x) ∂volume := by
            exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
        _ = ∫ x in W, (∑ j : Fin d, q j i * (Du x j * ψ x)) ∂volume := hstep
        _ = ∫ x in W, matVecMul (matTranspose q) (Du x) i * ψ x ∂volume := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            change ∑ j : Fin d, q j i * (Du x j * ψ x)
              = matVecMul (matTranspose q) (Du x) i * ψ x
            rw [matVecMul_matTranspose_apply, Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by ring
    rw [hchain, hsum1]
    have hweak : ∀ j : Fin d,
        ∫ x in W, u x * (fderiv ℝ ψ x) (basisVec j) ∂volume
          = -∫ x in W, Du x j * ψ x ∂volume :=
      fun j => h j ψ hψ_smooth hψ_compact hψ_sub
    calc ∑ j : Fin d, q j i * ∫ x in W, u x * (fderiv ℝ ψ x) (basisVec j) ∂volume
        = ∑ j : Fin d, -(q j i * ∫ x in W, Du x j * ψ x ∂volume) := by
          exact Finset.sum_congr rfl fun j _ => by rw [hweak j]; ring
      _ = -∑ j : Fin d, q j i * ∫ x in W, Du x j * ψ x ∂volume := by
          rw [Finset.sum_neg_distrib]
      _ = -∫ x in W, matVecMul (matTranspose q) (Du x) i * ψ x ∂volume := by rw [hsum2]
  -- transport both sides back to `V`
  have hL :
      ∫ y in V, u (matVecMul q y) * (fderiv ℝ φ y) (basisVec i) ∂volume
        = |q.det|⁻¹ * ∫ x in W, u x * (fderiv ℝ φ (matVecMul q⁻¹ x)) (basisVec i) ∂volume := by
    have hcv := setIntegral_comp_matVecMul_image hq V
      (fun x => u x * (fderiv ℝ φ (matVecMul q⁻¹ x)) (basisVec i))
    simpa [hW, matVecMul_inv_matVecMul hq] using hcv
  have hR :
      ∫ y in V, matVecMul (matTranspose q) (Du (matVecMul q y)) i * φ y ∂volume
        = |q.det|⁻¹ * ∫ x in W, matVecMul (matTranspose q) (Du x) i * ψ x ∂volume := by
    have hcv := setIntegral_comp_matVecMul_image hq V
      (fun x => matVecMul (matTranspose q) (Du x) i * ψ x)
    simpa [hW, hψdef, matVecMul_inv_matVecMul hq] using hcv
  rw [hL, hR, hkey]
  ring

/-! ## The `H¹` constructor -/

/-- **The `H¹`-under-linear-pullback constructor.**  For an invertible `q` and an open `V` whose
image `q V` lies in the domain `U`, the pullback `y ↦ u (q y)` is an `H¹(V)` witness with the
chain-rule gradient `y ↦ qᵀ (∇u (q y))`.

The hypotheses are exactly: invertibility of `q`, openness of the source set, and the image
containment.  No hypothesis is placed on `det q` beyond invertibility, and none on `U`. -/
@[expose]
def pullbackMatVecMul {q : Mat d} (hq : IsUnit q) {U V : Set (Vec d)}
    (hV : IsOpen V) (hsub : matVecMul q '' V ⊆ U) (u : H1Function U) : H1Function V where
  toFun := fun y => u.toFun (matVecMul q y)
  grad := fun y => matVecMul (matTranspose q) (u.grad (matVecMul q y))
  memL2 := memL2On_comp_matVecMul hq hsub u.memL2
  gradMemL2 := gradMemL2On_matVecMul_comp_matVecMul hq (matTranspose q) hsub u.gradMemL2
  hasWeakGradient :=
    hasWeakGradientOn_comp_matVecMul hq
      (memL2On_mono hsub u.memL2) (gradMemL2On_mono hsub u.gradMemL2)
      (u.hasWeakGradient.restrict (isOpen_image_matVecMul hq hV) hsub)

@[simp] theorem pullbackMatVecMul_toFun {q : Mat d} (hq : IsUnit q) {U V : Set (Vec d)}
    (hV : IsOpen V) (hsub : matVecMul q '' V ⊆ U) (u : H1Function U) :
    (pullbackMatVecMul hq hV hsub u).toFun = fun y => u.toFun (matVecMul q y) := rfl

@[simp] theorem pullbackMatVecMul_grad {q : Mat d} (hq : IsUnit q) {U V : Set (Vec d)}
    (hV : IsOpen V) (hsub : matVecMul q '' V ⊆ U) (u : H1Function U) :
    (pullbackMatVecMul hq hV hsub u).grad
      = fun y => matVecMul (matTranspose q) (u.grad (matVecMul q y)) := rfl

/-! ## Satisfiability of the hypothesis bundle at `q = respGrid jStar F`

The constructor above would be worthless if its hypothesis bundle were empty in the situation
`p.response.transfer` needs.  It is not: at `q = respGrid jStar F` the bundle is inhabited, and
the image containment even holds with EQUALITY, because `adaptedCell q t` is by definition `q`
applied to the centred cube `centeredCube d t = openCubeSet (originCube d t)`.

Invertibility, however, is NOT available from `(explicitCanonicalMetric F).PosDef` alone: the only
route
to `IsUnit (explicitRoundedGrid jStar m)` in the tree is `Geometry.isUnit_roundedGrid`
(`HCPoly/Entry/Geometry/RoundedGridBasic.lean`), which also consumes `2 * d ≤ 3 ^ jStar` — the
same premise
that `explicitRoundedGrid_metricFrobenius_product_le` (`ScaleAverageSeminorm.lean`) carries.  It is
therefore carried here as a hypothesis, not silently assumed. -/

/-- The selected grid is invertible on the `PosDef` branch, provided the grid depth satisfies
`2 * d ≤ 3 ^ jStar`. -/
theorem isUnit_respGrid {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) : IsUnit (respGrid jStar F) :=
  Geometry.isUnit_roundedGrid hjStar hm

/-- The adapted cell IS the `q`-image of the reference cube: the image containment of the
constructor holds with equality at every `q` and every scale. -/
theorem image_openCubeSet_originCube_eq_adaptedCell (q : Mat d) (t : ℤ) :
    matVecMul q '' openCubeSet (originCube d t) = HighContrast.adaptedCell q t := rfl

/-- **Satisfiability witness.**  The hypothesis bundle of `pullbackMatVecMul` is inhabited at
`q = respGrid jStar F`: any `H¹` witness on the adapted cell `U_t` pulls back to an `H¹` witness
on the reference cube `openCubeSet (originCube d t)` with the chain-rule gradient. -/
@[expose]
def respPullbackH1 {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (u : H1Function (HighContrast.adaptedCell (respGrid jStar F) t)) :
    H1Function (openCubeSet (originCube d t)) :=
  pullbackMatVecMul (isUnit_respGrid hjStar hm) (isOpen_openCubeSet (originCube d t))
    (image_openCubeSet_originCube_eq_adaptedCell (respGrid jStar F) t).subset u

@[simp] theorem respPullbackH1_toFun {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (u : H1Function (HighContrast.adaptedCell (respGrid jStar F) t)) :
    (respPullbackH1 hjStar hm t u).toFun
      = fun y => u.toFun (matVecMul (respGrid jStar F) y) := rfl

@[simp] theorem respPullbackH1_grad {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (u : H1Function (HighContrast.adaptedCell (respGrid jStar F) t)) :
    (respPullbackH1 hjStar hm t u).grad
      = fun y => matVecMul (matTranspose (respGrid jStar F))
          (u.grad (matVecMul (respGrid jStar F) y)) := rfl

/-! ### `affineH1`, reconstructed locally

Only declaration needed from `HCPolySupport.HighContrast.Coupled.WeakForm`:
`affineH1`/`affineH1_grad`/`affineH1_toFun` (`WeakForm.lean`). Built there from the
primitives `H1Function.coordOnOpenCubeSetOriginCube` (`Sobolev/H1/OriginCubeBridge.lean`)
and `add_grad`/`add_toFun`/`smul_grad`/`smul_toFun` (`Sobolev/H1/Algebra/H1Function.lean`).
Reproduced verbatim from those. -/

theorem H1Function.sum_grad {ι : Type*} {U : Set (Vec d)} (s : Finset ι)
    (f : ι → H1Function U) :
    (∑ i ∈ s, f i).grad = fun x => ∑ i ∈ s, (f i).grad x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [HCPolySupport.H1Function.add_grad, Finset.sum_insert ha, ih]

theorem H1Function.sum_toFun {ι : Type*} {U : Set (Vec d)} (s : Finset ι)
    (f : ι → H1Function U) :
    (∑ i ∈ s, f i).toFun = fun x => ∑ i ∈ s, (f i).toFun x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [HCPolySupport.H1Function.add_toFun, Finset.sum_insert ha, ih]

/-- The affine map `x ↦ p·x` as an `H¹` function on the centered open cube, with
constant gradient `p`. -/
@[expose]
def affineH1 (m : ℤ) (p : Vec d) : H1Function (openCubeSet (originCube d m)) :=
  ∑ i : Fin d, p i • H1Function.coordOnOpenCubeSetOriginCube (n := m) i

@[simp] theorem affineH1_grad (m : ℤ) (p : Vec d) :
    (affineH1 m p).grad = fun _ => p := by
  rw [affineH1, H1Function.sum_grad]
  funext x
  simp only [HCPolySupport.H1Function.smul_grad]
  change (∑ i : Fin d, p i • basisVec i) = p
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVec, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun i => p i)]
  simp

@[simp] theorem affineH1_toFun (m : ℤ) (p : Vec d) :
    (affineH1 m p).toFun = fun x => vecDot p x := by
  rw [affineH1, H1Function.sum_toFun]
  funext x
  simp only [HCPolySupport.H1Function.smul_toFun]
  rfl

/-- **The cutoff bridge's input.**  The centred pulled-back potential `y ↦ v(qy) − ⟨P, qy⟩` on the
reference cube, as an `H¹` witness whose gradient is the FIRST SLOT of the pulled-back centred
optimizer field, i.e. `y ↦ qᵀ ((optimizerField b u (q y) − Y).1)` with `P = Y.1`.  This is exactly
the `u : H1Function (openCubeSet Q)` argument of the generic CG bridge
`abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
(`Book/Ch05/.../JUpperBoundWeakNorms/Product/Bridge.lean`). -/
@[expose]
def respCenteredPullbackH1 {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (b : CoeffField d)
    (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t)) (Y : BlockVec d) :
    H1Function (openCubeSet (originCube d t)) :=
  respPullbackH1 hjStar hm t u.toH1
    - affineH1 t (matVecMul (matTranspose (respGrid jStar F)) Y.1)

@[simp] theorem respCenteredPullbackH1_toFun {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (b : CoeffField d)
    (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t)) (Y : BlockVec d) :
    (respCenteredPullbackH1 hjStar hm t b u Y).toFun
      = fun y => u.toH1.toFun (matVecMul (respGrid jStar F) y)
          - vecDot Y.1 (matVecMul (respGrid jStar F) y) := by
  funext y
  simp [respCenteredPullbackH1, vecDot_matVecMul_transpose]

@[simp] theorem respCenteredPullbackH1_grad {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (b : CoeffField d)
    (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t)) (Y : BlockVec d) :
    (respCenteredPullbackH1 hjStar hm t b u Y).grad
      = fun y => matVecMul (matTranspose (respGrid jStar F))
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).1) := by
  funext y
  simp [respCenteredPullbackH1, optimizerField, sub_eq_add_neg, matVecMul_add, matVecMul_neg]

end

end HCPolySupport.HighContrast.Multiscale
end
