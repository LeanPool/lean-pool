/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm
public import LeanPool.HighContrastHomogenization.Provider.Response.EnergyMap

/-!
# High-contrast homogenization: Provider.Response.WeakNormCellAverage

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cell average under the metric root and the centering

The concrete scale-average seminorm is evaluated in the weak-norm estimate for
the optimizer state on the field

```
F = M_0^{1/2}(X_t - (X_t)_{U_t}),
```

so its cell averages are `M_0^{1/2}((X_t)_{U_k(z)} - (X_t)_{U_t})`.  Getting
there is two applications of linearity of the cell average, recorded here: a
fixed matrix passes through the average, and a constant subtracted from the
field is subtracted from the average.  Both carry the square-integrability of
the field on the cell as a hypothesis, which is what a Chapter 2 solution
supplies, and the second also carries the finiteness and nondegeneracy of the
cell volume, which every adapted cell has.

Together with the quadratic form identity for the root `diag(m_0^{1/2},
m_0^{-1/2})` of the diagonal metric, this turns each cell contribution of the
seminorm into `metricBlockNormSq m_0` of a difference of cell averages, which is
the shape the variational comparison of the optimizer averages is stated in.
The root enters only through the hypotheses `S^t = S` and
`S^2 = m_0`, which the printed positivity of the spatial metric supplies.

The last section records the scalar form of the block lift: on a field carried
by the gradient slot alone the doubled seminorm is the scale-average seminorm of
an `ℝ^d`-valued field with the ordinary Euclidean length.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The cell average through a fixed linear map -/

/-- The vector average commutes with a fixed matrix. -/
theorem averageVec_matVecMul {U : Domain d} (A : Mat d) {F : Vec d → Vec d}
    (hF : MemVectorL2 (U : Set (Vec d)) F) :
    Book.Ch02.averageVec U (fun x => matVecMul A (F x)) =
      matVecMul A (Book.Ch02.averageVec U F) := by
  funext i
  have h : (fun x => matVecMul A (F x) i) = fun x => vecDot (fun j => A i j) (F x) := by
    funext x
    simp [matVecMul, vecDot]
  change Book.Ch02.average U (fun x => matVecMul A (F x) i) = _
  rw [h, average_vecDot_const (fun j => A i j) hF]
  simp [matVecMul, vecDot]

/-- **The cell average commutes with a block diagonal matrix**: the step that
moves the metric root `M_0^{1/2} = diag(m_0^{1/2}, m_0^{-1/2})` of the diagonal
metric outside the cell average of the scale-average seminorm. -/
theorem blockCellAverage_blockDiag {U : Domain d} (A B : Mat d) {F : Vec d → BlockVec d}
    (h1 : MemVectorL2 (U : Set (Vec d)) fun x => (F x).1)
    (h2 : MemVectorL2 (U : Set (Vec d)) fun x => (F x).2) :
    blockCellAverage (U : Set (Vec d)) (fun x => blockMatVecMul (blockDiag A B) (F x)) =
      blockMatVecMul (blockDiag A B) (blockCellAverage (U : Set (Vec d)) F) := by
  have hfst : ∀ x : Vec d,
      (blockMatVecMul (blockDiag A B) (F x)).1 = matVecMul A (F x).1 := by
    intro x
    change matVecMul A (F x).1 + matVecMul 0 (F x).2 = matVecMul A (F x).1
    rw [zero_matVecMul, add_zero]
  have hsnd : ∀ x : Vec d,
      (blockMatVecMul (blockDiag A B) (F x)).2 = matVecMul B (F x).2 := by
    intro x
    change matVecMul 0 (F x).1 + matVecMul B (F x).2 = matVecMul B (F x).2
    rw [zero_matVecMul, zero_add]
  have hgoal : blockMatVecMul (blockDiag A B) (blockCellAverage (U : Set (Vec d)) F) =
      (matVecMul A (blockCellAverage (U : Set (Vec d)) F).1,
        matVecMul B (blockCellAverage (U : Set (Vec d)) F).2) := by
    refine Prod.ext ?_ ?_
    · change matVecMul A _ + matVecMul 0 _ = _
      rw [zero_matVecMul, add_zero]
    · change matVecMul 0 _ + matVecMul B _ = _
      rw [zero_matVecMul, zero_add]
  rw [hgoal]
  refine Prod.ext ?_ ?_
  · change Book.Ch02.averageVec U (fun x => (blockMatVecMul (blockDiag A B) (F x)).1) = _
    simp only [hfst]
    exact averageVec_matVecMul A h1
  · change Book.Ch02.averageVec U (fun x => (blockMatVecMul (blockDiag A B) (F x)).2) = _
    simp only [hsnd]
    exact averageVec_matVecMul B h2

/-- Square integrability passes to a subcell, which is how the parent optimizer
is measured on every aligned child. -/
theorem memVectorL2_mono {U V : Set (Vec d)} (hVU : V ⊆ U) {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : MemVectorL2 V F :=
  hF.mono_measure (MeasureTheory.Measure.restrict_mono hVU le_rfl)

/-- Square integrability survives subtracting a constant on a cell of finite
volume, which is what the centering `X_t - (X_t)_{U_t}` of the weak-norm
estimate does to the optimizer state. -/
theorem memVectorL2_sub_const {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {F : Vec d → Vec d} (hF : MemVectorL2 U F) (c : Vec d) :
    MemVectorL2 U (fun x => F x - c) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  exact hF.sub (MeasureTheory.memLp_const c)

/-- **The cell average of a centered field**: subtracting a constant from a
field subtracts it from every cell average, which is what turns
`X_t - (X_t)_{U_t}` into `(X_t)_{U_k(z)} - (X_t)_{U_t}` inside the seminorm. -/
theorem blockCellAverage_sub_const {U : Domain d} (c : BlockVec d) {F : Vec d → BlockVec d}
    (hne : MeasureTheory.volume (U : Set (Vec d)) ≠ 0)
    (htop : MeasureTheory.volume (U : Set (Vec d)) ≠ ⊤)
    (h1 : MemVectorL2 (U : Set (Vec d)) fun x => (F x).1)
    (h2 : MemVectorL2 (U : Set (Vec d)) fun x => (F x).2) :
    blockCellAverage (U : Set (Vec d)) (fun x => F x - c) =
      blockCellAverage (U : Set (Vec d)) F - c := by
  have hvol : (MeasureTheory.volume (U : Set (Vec d))).toReal ≠ 0 :=
    (ENNReal.toReal_pos hne htop).ne'
  have haux : ∀ (G : Vec d → Vec d) (e : Vec d),
      MemVectorL2 (U : Set (Vec d)) G →
      Book.Ch02.averageVec U (fun x => G x - e) = Book.Ch02.averageVec U G - e := by
    intro G e hG
    funext i
    have hint : MeasureTheory.IntegrableOn (fun x => G x i) (U : Set (Vec d))
        MeasureTheory.volume := integrableOn_component hG i
    have hconst : MeasureTheory.IntegrableOn (fun _ : Vec d => e i) (U : Set (Vec d))
        MeasureTheory.volume := MeasureTheory.integrableOn_const htop (by simp)
    change Book.Ch02.average U (fun x => G x i - e i) = Book.Ch02.average U (fun x => G x i) - e i
    unfold Book.Ch02.average
    rw [MeasureTheory.integral_sub hint hconst, MeasureTheory.setIntegral_const,
      MeasureTheory.measureReal_def, smul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ hvol, one_mul]
  refine Prod.ext ?_ ?_
  · change Book.Ch02.averageVec U (fun x => (F x).1 - c.1) = _
    rw [haux _ c.1 h1]; rfl
  · change Book.Ch02.averageVec U (fun x => (F x).2 - c.2) = _
    rw [haux _ c.2 h2]; rfl

/-! ## The metric root -/

/-- **The metric quadratic form is the squared length of the metric root's
image**: for a symmetric `S` with `S^2 = m` the map `diag(S, S^{-1})` is the
root `M_0^{1/2}` of the diagonal metric, and its squared image length
is the quadratic form.  This is the identity that lets the printed field
`M_0^{1/2}(X_t - (X_t)_{U_t})` be measured without ever constructing a root. -/
theorem blockVecDot_self_blockDiag_root {m S : Mat d} (hsymm : matTranspose S = S)
    (hsq : S * S = m) (v : BlockVec d) :
    blockVecDot (blockMatVecMul (blockDiag S S⁻¹) v) (blockMatVecMul (blockDiag S S⁻¹) v) =
      metricBlockNormSq m v := by
  have himg : blockMatVecMul (blockDiag S S⁻¹) v = (matVecMul S v.1, matVecMul S⁻¹ v.2) := by
    refine Prod.ext ?_ ?_
    · change matVecMul S v.1 + matVecMul 0 v.2 = _
      rw [zero_matVecMul, add_zero]
    · change matVecMul 0 v.1 + matVecMul S⁻¹ v.2 = _
      rw [zero_matVecMul, zero_add]
  have hupper : vecNormSq (matVecMul S v.1) = vecDot v.1 (matVecMul m v.1) := by
    rw [← vecDot_matVecMul_transpose_mul_self S v.1, hsymm, hsq]
  have hinv : matTranspose S⁻¹ * S⁻¹ = m⁻¹ := by
    change (S⁻¹).transpose * S⁻¹ = m⁻¹
    rw [Matrix.transpose_nonsing_inv, show S.transpose = S from hsymm, ← Matrix.mul_inv_rev, hsq]
  have hlower : vecNormSq (matVecMul S⁻¹ v.2) = vecDot v.2 (matVecMul m⁻¹ v.2) := by
    rw [← vecDot_matVecMul_transpose_mul_self S⁻¹ v.2, hinv]
  rw [himg, metricBlockNormSq_eq]
  change vecDot (matVecMul S v.1) (matVecMul S v.1) +
      vecDot (matVecMul S⁻¹ v.2) (matVecMul S⁻¹ v.2) = _
  rw [show vecDot (matVecMul S v.1) (matVecMul S v.1) = vecNormSq (matVecMul S v.1) from rfl,
    show vecDot (matVecMul S⁻¹ v.2) (matVecMul S⁻¹ v.2) = vecNormSq (matVecMul S⁻¹ v.2) from rfl,
    hupper, hlower]

/-! ## The block lift and its scalar form -/

end

end Response
end HighContrast
end HCPolySupport
