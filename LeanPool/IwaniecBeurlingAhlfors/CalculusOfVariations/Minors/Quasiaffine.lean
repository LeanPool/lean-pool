/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Minors.NullLagrangian
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Minors.RankOneAffine
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Gradient
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The `3 × 3` minors are quasiaffine

For a Lipschitz test map `φ` vanishing outside the unit cube,
`∫_{(0,1)^m} det ((A + ∇φ)_{rc}) = det (A_{rc})` for every `3 × 3` minor (`nl_minor3_quasiaffine`):
expand `det (X + Y) = det X + tr (adj X · Y) + tr (X · adj Y) + det Y` and integrate the minors of
`∇φ` of orders `1`, `2`, `3` (`Minors.NullLagrangian`). This is (8.44) of Theorem 8.35 of B.
Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer, 2008 ([D08], p.
409–411), for the `3 × 3` minors and the cube, by the proof of its part (ii) (expand `det (∇v + ∇w)`
into mixed minors, write them as divergences, and argue by density), with `v` affine and `w = φ`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The closed unit cube. -/
def nlIcc (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1

theorem nl_isCompact_Icc (m : ℕ) : IsCompact (nlIcc m) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem nl_unitCube_subset (m : ℕ) : unitCube m ⊆ nlIcc m :=
  Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self

section TestMap

variable {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
  (h0 : ∀ x ∉ unitCube m, φ x = 0)
include hφ h0

omit h0 in
theorem nl_lip_comp (i : Fin d) : LipschitzWith K fun y => φ y i := by
  have := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
  rw [one_mul] at this
  exact this

omit hφ in
theorem nl_hasCompactSupport_comp (i : Fin d) : HasCompactSupport fun y => φ y i :=
  HasCompactSupport.intro (nl_isCompact_Icc m) fun x hx => by
    rw [h0 x fun h => hx (nl_unitCube_subset m h)]; rfl

omit hφ in
theorem nl_fderiv_comp_zero (i : Fin d) {x : Fin m → ℝ} (hx : x ∉ nlIcc m) :
    fderiv ℝ (fun y => φ y i) x = 0 := by
  have hopen : IsOpen (nlIcc m)ᶜ := (nl_isCompact_Icc m).isClosed.isOpen_compl
  have hev : (fun y => φ y i) =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [h0 y fun h => hy (nl_unitCube_subset m h)]; rfl
  rw [hev.fderiv_eq]; simp

omit hφ in
theorem nl_grad_zero {x : Fin m → ℝ} (hx : x ∉ nlIcc m) : grad φ x = 0 := by
  ext i k
  simp only [grad, Matrix.of_apply, nl_fderiv_comp_zero h0 i hx]; rfl

omit h0 in
omit hφ h0 in
theorem nl_measurable_grad : Measurable fun x => grad φ x := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  exact measurable_fderiv_apply_const ℝ (fun y => φ y i) (Pi.single k 1)

omit h0 in
/-- For continuous `Φ`, `x ↦ Φ (B + ∇φ (x))` is bounded and measurable, hence integrable on the
cube. -/
theorem nl_integrableOn_cube {Φ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hΦ : Continuous Φ)
    (B : Matrix (Fin d) (Fin m) ℝ) (s : Set (Fin m → ℝ)) (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => Φ (B + grad φ x)) s := by
  set box : Set (Matrix (Fin d) (Fin m) ℝ) :=
    Set.pi Set.univ fun i => Set.pi Set.univ fun k => Set.Icc (B i k - K) (B i k + K)
  have hbox : IsCompact box := isCompact_univ_pi fun i => isCompact_univ_pi fun k => isCompact_Icc
  obtain ⟨M, hM⟩ := hbox.exists_bound_of_continuousOn hΦ.continuousOn
  refine Measure.integrableOn_of_bounded (M := M) hs
    (((hΦ.comp (continuous_const.add continuous_id)).measurable.comp
      (nl_measurable_grad)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => hM _ fun i _ k _ => ?_)
  have := abs_le.mp (rd_grad_abs_le hφ x i k)
  simp only [Matrix.add_apply]
  constructor <;> linarith [this.1, this.2]

/-- If `Φ (0) = 0`, then `x ↦ Φ (∇φ (x))` is integrable on `ℝ^m`, and its integral over the open
cube is its integral over `ℝ^m`. -/
theorem nl_integrable_of_zero {Φ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hΦ : Continuous Φ)
    (hΦ0 : Φ 0 = 0) : Integrable fun x => Φ (grad φ x) := by
  have h := nl_integrableOn_cube hφ hΦ 0 (nlIcc m)
    ((nl_isCompact_Icc m).measure_lt_top.ne)
  simp only [zero_add] at h
  exact h.integrable_of_forall_notMem_eq_zero fun x hx => by rw [nl_grad_zero h0 hx, hΦ0]

omit hφ in
theorem nl_setIntegral_cube_of_zero {Φ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hΦ0 : Φ 0 = 0) :
    ∫ x in unitCube m, Φ (grad φ x) = ∫ x, Φ (grad φ x) := by
  have hae : (Set.pi Set.univ fun _ : Fin m => Set.Ioo (0 : ℝ) 1) =ᵐ[volume]
      (Set.pi Set.univ fun _ : Fin m => Set.Icc (0 : ℝ) 1) := Measure.pi_Ioo_ae_eq_pi_Icc
  rw [show unitCube m = Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1 from rfl,
    setIntegral_congr_set hae]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [nl_grad_zero h0 hx, hΦ0]

/-- `∫ ∂_k φ_i = 0`. -/
theorem nl_integral_grad (i : Fin d) (k : Fin m) : ∫ x, grad φ x i k = 0 :=
  plancherel_integral_fderiv_eq_zero (nl_lip_comp hφ i)
    (nl_hasCompactSupport_comp h0 i) _

/-- `∫ (∂_a φ_p ∂_b φ_q − ∂_b φ_p ∂_a φ_q) = 0`. -/
theorem nl_integral_minor2 (p q : Fin d) (a b : Fin m) (σ : ℝ) :
    ∫ x, σ * (grad φ x p a * grad φ x q b - grad φ x p b * grad φ x q a) = 0 := by
  rw [integral_const_mul]
  have := nl_null2 (nl_lip_comp hφ p) (nl_lip_comp hφ q)
    (nl_hasCompactSupport_comp h0 p) (nl_hasCompactSupport_comp h0 q) a b
  simp only [grad, Matrix.of_apply]
  rw [this, mul_zero]

end TestMap

/-- `det (X + Y) = det X + tr (adj X · Y) + tr (X · adj Y) + det Y` for `3 × 3` matrices. -/
theorem nl_det_add (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    (X + Y).det = X.det + ∑ i, ∑ j, X.adjugate j i * Y i j + ∑ i, ∑ j, X i j * Y.adjugate j i +
      Y.det := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Fin.sum_univ_three]
  ring

section Minor

variable {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
  (h0 : ∀ x ∉ unitCube m, φ x = 0)
include hφ h0

/-- The cofactors of a `3 × 3` minor of `∇φ` integrate to `0`. -/
theorem nl_integral_adj (r : Fin 3 ↪o Fin d) (c : Fin 3 ↪o Fin m) (j i : Fin 3) :
    ∫ x, ((grad φ x).submatrix r c).adjugate j i = 0 := by
  have key : ∀ (p q a b : Fin 3) (σ : ℝ), (∀ x, ((grad φ x).submatrix r c).adjugate j i =
      σ * (grad φ x (r p) (c a) * grad φ x (r q) (c b) - grad φ x (r p) (c b) * grad φ x (r q)
          (c a))) →
      ∫ x, ((grad φ x).submatrix r c).adjugate j i = 0 := by
    intro p q a b σ h
    simp_rw [h]
    exact nl_integral_minor2 hφ h0 _ _ _ _ σ
  fin_cases j <;> fin_cases i
  · exact key 1 2 1 2 1 (fun x => by simp [Matrix.adjugate_fin_three])
  · exact key 0 2 1 2 (-1) (fun x => by simp [Matrix.adjugate_fin_three]; ring)
  · exact key 0 1 1 2 1 (fun x => by simp [Matrix.adjugate_fin_three])
  · exact key 1 2 0 2 (-1) (fun x => by simp [Matrix.adjugate_fin_three]; ring)
  · exact key 0 2 0 2 1 (fun x => by simp [Matrix.adjugate_fin_three])
  · exact key 0 1 0 2 (-1) (fun x => by simp [Matrix.adjugate_fin_three]; ring)
  · exact key 1 2 0 1 1 (fun x => by simp [Matrix.adjugate_fin_three])
  · exact key 0 2 0 1 (-1) (fun x => by simp [Matrix.adjugate_fin_three]; ring)
  · exact key 0 1 0 1 1 (fun x => by simp [Matrix.adjugate_fin_three])

/-- The `3 × 3` minors of `∇φ` integrate to `0`. -/
theorem nl_integral_det (r : Fin 3 ↪o Fin d) (c : Fin 3 ↪o Fin m) :
    ∫ x, ((grad φ x).submatrix r c).det = 0 := by
  have := nl_null3 (nl_lip_comp hφ (r 0)) (nl_lip_comp hφ (r 1))
    (nl_lip_comp hφ (r 2)) (nl_hasCompactSupport_comp h0 (r 0))
    (nl_hasCompactSupport_comp h0 (r 1)) (nl_hasCompactSupport_comp h0 (r 2))
    (c 0) (c 1) (c 2)
  rw [← this]
  congr 1; funext x
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, grad, Matrix.of_apply]
  ring

/-- **`3 × 3` minors are quasiaffine**: `∫_{(0,1)^m} det ((A + ∇φ)_{rc}) = det (A_{rc})`. -/
theorem nl_minor3_quasiaffine (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin 3 ↪o Fin d)
    (c : Fin 3 ↪o Fin m) :
    ∫ x in unitCube m, minor (A + grad φ x) r c =
      minor A r c := by
  set X := A.submatrix r c
  set F : Matrix (Fin d) (Fin m) ℝ → ℝ := fun J => ((A + J).submatrix r c).det - X.det
  have hFc : Continuous F := by
    have : Continuous fun J : Matrix (Fin d) (Fin m) ℝ => ((A + J).submatrix r c) :=
      (continuous_const.add continuous_id).matrix_submatrix r c
    exact this.matrix_det.sub continuous_const
  have hF0 : F 0 = 0 := by simp [F, X]
  have hsplit : ∀ J : Matrix (Fin d) (Fin m) ℝ, F J =
      (∑ i, ∑ j, X.adjugate j i * J (r i) (c j)) +
        (∑ i, ∑ j, X i j * (J.submatrix r c).adjugate j i) + (J.submatrix r c).det := by
    intro J
    have hs : (A + J).submatrix r c = X + J.submatrix r c := by ext; simp [X]
    simp only [F, hs, nl_det_add, Matrix.submatrix_apply]
    ring
  have hcube : volume (unitCube m) = 1 := rd_volume_unitCube m
  calc ∫ x in unitCube m, minor (A + grad φ x) r c
      = ∫ x in unitCube m, (X.det + F (grad φ x)) := by
        refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
          fun x _ => ?_
        simp only [F, minor]; ring
    _ = X.det + ∫ x in unitCube m, F (grad φ x) := by
        have hI := nl_integrableOn_cube hφ hFc 0 (unitCube m) (by rw [hcube]; simp)
        simp only [zero_add] at hI
        rw [integral_add (integrableOn_const (by rw [hcube]; simp) eNorm_ne_top) hI,
          setIntegral_const, Measure.real, hcube]
        simp
    _ = X.det + ∫ x, F (grad φ x) := by rw [nl_setIntegral_cube_of_zero h0 hF0]
    _ = X.det := by
        have i1 : Integrable fun x => ∑ i, ∑ j, X.adjugate j i * grad φ x (r i) (c j) :=
          nl_integrable_of_zero hφ h0 (Φ := fun J => ∑ i, ∑ j, X.adjugate j i * J (r i) (c j))
            (by fun_prop) (by simp)
        have i2 : Integrable fun x => ∑ i, ∑ j, X i j * ((grad φ x).submatrix r c).adjugate j i :=
          nl_integrable_of_zero hφ h0
            (Φ := fun J => ∑ i, ∑ j, X i j * (J.submatrix r c).adjugate j i)
            (by
              refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
                continuous_const.mul ?_
              have : Continuous fun J : Matrix (Fin d) (Fin m) ℝ => (J.submatrix r c).adjugate :=
                (continuous_id.matrix_submatrix r c).matrix_adjugate
              exact (continuous_apply i).comp ((continuous_apply j).comp this))
            (by simp)
        have i3 : Integrable fun x => ((grad φ x).submatrix r c).det :=
          nl_integrable_of_zero hφ h0 (Φ := fun J => (J.submatrix r c).det)
            (continuous_id.matrix_submatrix r c).matrix_det (by simp)
        simp_rw [hsplit]
        rw [integral_add (f := fun x => (∑ i, ∑ j, X.adjugate j i * grad φ x (r i) (c j)) +
            ∑ i, ∑ j, X i j * ((grad φ x).submatrix r c).adjugate j i) (i1.add i2) i3,
          integral_add i1 i2, nl_integral_det hφ h0 r c]
        have e1 : ∫ x, ∑ i, ∑ j, X.adjugate j i * grad φ x (r i) (c j) = 0 := by
          rw [integral_finsetSum _ fun i _ => ?_]
          · refine Finset.sum_eq_zero fun i _ => ?_
            rw [integral_finsetSum _ fun j _ => ?_]
            · refine Finset.sum_eq_zero fun j _ => ?_
              rw [integral_const_mul, nl_integral_grad hφ h0, mul_zero]
            · exact (nl_integrable_of_zero hφ h0 (Φ := fun J => J (r i) (c j))
                (by fun_prop) (by simp)).const_mul _
          · exact nl_integrable_of_zero hφ h0 (Φ := fun J => ∑ j, X.adjugate j i * J (r i) (c j))
              (by fun_prop) (by simp)
        have e2 : ∫ x, ∑ i, ∑ j, X i j * ((grad φ x).submatrix r c).adjugate j i = 0 := by
          have hadj : ∀ i j, Continuous fun J : Matrix (Fin d) (Fin m) ℝ =>
              (J.submatrix r c).adjugate j i := fun i j =>
            (continuous_apply i).comp ((continuous_apply j).comp
              ((continuous_id.matrix_submatrix r c).matrix_adjugate))
          rw [integral_finsetSum _ fun i _ => ?_]
          · refine Finset.sum_eq_zero fun i _ => ?_
            rw [integral_finsetSum _ fun j _ => ?_]
            · refine Finset.sum_eq_zero fun j _ => ?_
              rw [integral_const_mul, nl_integral_adj hφ h0 r c j i, mul_zero]
            · exact (nl_integrable_of_zero hφ h0 (hadj i j) (by simp)).const_mul _
          · exact nl_integrable_of_zero hφ h0
              (Φ := fun J => ∑ j, X i j * (J.submatrix r c).adjugate j i)
              (continuous_finsetSum _ fun j _ => continuous_const.mul (hadj i j)) (by simp)
        rw [e1, e2]; ring

end Minor

end CalculusOfVariations
