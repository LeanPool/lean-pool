/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Minors.AllOrders
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Quasiconvex.Periodic

/-!
# Null Lagrangians for periodic maps

For `ℤ^m`-periodic Lipschitz maps on `ℝ^m = Fin m → ℝ`, integrated over the open unit cube
`(0, 1)^m = unitCube m`, a fundamental domain of `ℤ^m`:

* `setIntegral_unitCube_fderiv_eq_zero`: `∫_{(0,1)^m} ∂_v f = 0` for a periodic Lipschitz
  `f : ℝ^m → ℝ`;
* `setIntegral_unitCube_grad_eq_zero`: `∫_{(0,1)^m} ∇φ = 0`, entrywise, for a periodic Lipschitz
  map `φ : ℝ^m → ℝ^d`;
* `setIntegral_unitCube_det_add_grad`: the determinant is a null Lagrangian for periodic Lipschitz
  perturbations: `∫_{(0,1)²} det (A + ∇ψ) = det A` for `ψ : ℝ² → ℝ²`.

All three come from one identity for minors of every order: `∫_{(0,1)^m} minor (A + ∇φ) = minor A`
for periodic Lipschitz `φ`. Every minor is a null Lagrangian for Lipschitz maps vanishing off a
bounded set (`setIntegral_minor_add_grad`, after B. Dacorogna, *Direct Methods in the Calculus of
Variations*, 2nd ed., Springer, 2008, Theorem 8.35), so the minor and its negative are quasiconvex
on the unit cube, hence quasiconvex with periodic test maps (`quasiconvexAtOn_iff_periodic`, [ibid.,
Proposition 5.13]); the two inequalities give the identity. The entries of `∇φ` are the `1 × 1`
minors (with `A = 0`), the determinant of a `2 × 2` matrix is its `2 × 2` minor, and `∂_v f` is a
linear combination of the entries of the gradient of the map `x ↦ (f x) ∈ ℝ^1`.
-/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

variable {m : ℕ}

/-- Every minor is a null Lagrangian for periodic perturbations: `∫_{(0,1)^m} minor (A + ∇φ) =
minor A` for a `ℤ^m`-periodic Lipschitz `φ`. The minor and its negative are null Lagrangians on the
unit cube (`setIntegral_minor_add_grad`), hence quasiconvex there, hence quasiconvex with periodic
test maps (`quasiconvexAtOn_iff_periodic`); the two inequalities give the equality. -/
private theorem setIntegral_unitCube_minor_add_grad {d k : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    {K : NNReal} (hφ : LipschitzWith K φ)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    ∫ x in unitCube m, minor (A + grad φ x) r c = minor A r c := by
  have hcont : Continuous fun B : Matrix (Fin d) (Fin m) ℝ => minor B r c :=
    (continuous_id.matrix_submatrix r c).matrix_det
  have hb : Bornology.IsBounded (unitCube m) :=
    (Metric.isBounded_Icc (0 : Fin m → ℝ) 1).subset fun x hx =>
      ⟨fun i => (hx i (Set.mem_univ _)).1.le, fun i => (hx i (Set.mem_univ _)).2.le⟩
  have hI : IntegrableOn (fun x => minor (A + grad φ x) r c) (unitCube m) :=
    rd_integrableOn hcont.measurable (isLocallyBounded_of_continuous hcont) A hφ
      (by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top)
  -- `s · minor` is quasiconvex on the unit cube (a null Lagrangian), hence with periodic test maps
  have hq : ∀ s : ℝ, QuasiconvexAtPeriodic (fun B => s * minor B r c) A := by
    intro s
    have hcs : Continuous fun B : Matrix (Fin d) (Fin m) ℝ => s * minor B r c :=
      continuous_const.mul hcont
    refine (quasiconvexAtOn_iff_periodic hcs.measurable (isLocallyBounded_of_continuous hcs)
      A).1 fun ψ L hψ h0 _ => ?_
    rw [integral_const_mul, setIntegral_minor_add_grad hb hψ h0]
    exact le_of_eq (by ring)
  have h1 := hq 1 φ K hφ hper (by simpa using hI)
  have h2 := hq (-1) φ K hφ hper (by simpa using hI.neg)
  simp only [one_mul, neg_one_mul, integral_neg] at h1 h2
  linarith

/-- `∫_{(0,1)^m} ∂_k φ_i = 0` for a `ℤ^m`-periodic Lipschitz `φ`: the entry `(i, k)` is the
`1 × 1` minor with the row `i` and the column `k`. -/
private theorem setIntegral_unitCube_grad_entry {d : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    {K : NNReal} (hφ : LipschitzWith K φ)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (i : Fin d) (k : Fin m) :
    ∫ x in unitCube m, grad φ x i k = 0 := by
  have h := setIntegral_unitCube_minor_add_grad hφ hper 0
    (OrderEmbedding.ofStrictMono (fun _ : Fin 1 => i) (Subsingleton.strictMono _))
    (OrderEmbedding.ofStrictMono (fun _ : Fin 1 => k) (Subsingleton.strictMono _))
  simpa [minor, Matrix.det_unique] using h

/-- `∫_{(0,1)^m} ∂_v f = 0` for a `ℤ^m`-periodic Lipschitz `f`. -/
theorem setIntegral_unitCube_fderiv_eq_zero {f : (Fin m → ℝ) → ℝ} {K : NNReal}
    (hf : LipschitzWith K f)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), f (x + fun i => (z i : ℝ)) = f x)
    (v : Fin m → ℝ) :
    ∫ x in unitCube m, fderiv ℝ f x v = 0 := by
  -- `f` as a map to `ℝ^1`
  set φ : (Fin m → ℝ) → Fin 1 → ℝ := fun x _ => f x with hφdef
  have hφ : LipschitzWith K φ := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [hφdef, dist_pi_const]; exact hf.dist_le_mul x y
  have hφper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x :=
    fun x z => by simp only [hφdef, hper]
  have hI : ∀ k, IntegrableOn (fun x => fderiv ℝ f x (Pi.single k 1)) (unitCube m) := fun k =>
    rd_integrableOn (f := fun B : Matrix (Fin 1) (Fin m) ℝ => B 0 k)
      (continuous_id.matrix_elem 0 k).measurable
      (isLocallyBounded_of_continuous (continuous_id.matrix_elem 0 k)) 0 hφ
      (by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top) |>.congr_fun
      (fun x _ => by simp [grad, hφdef]) (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  -- `∂_v f = ∑_k v_k ∂_k f`
  have hsum : ∀ x, fderiv ℝ f x v = ∑ k, v k * fderiv ℝ f x (Pi.single k 1) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext j
    simp [Pi.single_apply]
  simp_rw [hsum]
  rw [integral_finsetSum _ fun k _ => (hI k).const_mul (v k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, show (∫ x in unitCube m, fderiv ℝ f x (Pi.single k 1)) =
    ∫ x in unitCube m, grad φ x 0 k from rfl, setIntegral_unitCube_grad_entry hφ hφper 0 k,
    mul_zero]

/-- `∫_{(0,1)^m} ∇φ = 0`, entrywise, for a `ℤ^m`-periodic Lipschitz `φ : ℝ^m → ℝ^d`. -/
theorem setIntegral_unitCube_grad_eq_zero {d : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (i : Fin d) (k : Fin m) :
    ∫ x in unitCube m, grad φ x i k = 0 :=
  setIntegral_unitCube_grad_entry hφ hper i k

/-- The determinant is a null Lagrangian for periodic perturbations:
`∫_{(0,1)²} det (A + ∇ψ) = det A` for a `ℤ²`-periodic Lipschitz `ψ : ℝ² → ℝ²`. -/
theorem setIntegral_unitCube_det_add_grad {ψ : (Fin 2 → ℝ) → Fin 2 → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), ψ (x + fun i => (z i : ℝ)) = ψ x)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ x in unitCube 2, (A + grad ψ x).det = A.det := by
  have h := setIntegral_unitCube_minor_add_grad hψ hper A (OrderIso.refl (Fin 2)).toOrderEmbedding
    (OrderIso.refl (Fin 2)).toOrderEmbedding
  simpa [minor] using h

end CalculusOfVariations
