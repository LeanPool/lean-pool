/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DirectionalLeviDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosedProductCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConcentrationEigenvalueBound

/-!
# The forms `i β ∧ βBar` and the Levi test of weak positivity

Source: `chapter_pshfunctions.tex`, `def:pos_curr` (weak positivity of currents is tested on the
measures `T ∧ i β₁ ∧ βBar₁ ∧ ⋯ ∧ i β_{N-m} ∧ βBar_{N-m}`); Xia, *Foundations of pluripotential
theory*, `q01` (positive forms and currents); Demailly, *Complex analytic and differential
geometry*, III.1.

For a `ℂ`-linear form `β : ℂⁿ → ℂ` with real and imaginary parts `a = Re β`, `b = Im β`, the real
two-form `i β ∧ βBar` is `2 a ∧ b` (`oneOneSquare`):
`(i β ∧ βBar)(u, v) = i (β(u) βBar(v) - β(v) βBar(u)) = 2 (a(u) b(v) - a(v) b(u))`
(`oneOneSquare_apply`).  It is a semipositive real `(1,1)`-form
    (`isSemipositiveOneOne_oneOneSquare`),
so products of such forms are strongly positive (`betaProduct_mem_spCone`).

The main result is the converse direction needed for the `dd^c`-lemma: if a scalar distribution
`T` on an open set of `ℂ^{m+1}` has `dd^c T ∧ i β₁ ∧ βBar₁ ∧ ⋯ ∧ i β_m ∧ βBar_m ≥ 0` for all
constant `ℂ`-linear forms `β_j` (as a measure), then `T` has nonnegative distributional Levi
form in every direction (`hasNonnegativeDistributionalLevi_of_betaProduct_pairings`).  For a unit
vector `a` one takes `β_j = ⟨w_j, ·⟩` for the columns `w_1, …, w_m` of a unitary matrix whose
first column is `ā`; then the top density of `dd^c f ∧ ∏ i β_j ∧ βBar_j` is
`((2π)^m / π^{m+1}) · L_f(a)` (`topDensity_cons_unitaryBetaProduct`), by the unitary congruence
of mixed determinants.
-/

@[expose] public section

noncomputable section

open Set Filter Matrix
open scoped Topology ContDiff InnerProductSpace Distributions

namespace SGPT.PSH.BookCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.DirectionalLeviDensity
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Foundations.Analysis.Pending.ClosedProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
open SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
open SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion
open SGPT.Foundations.Analysis.Pending.CompactDifferentialTests
open SGPT.Foundations.Analysis.Pending.ScalarFullTestTranspose
open SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.ConcentrationEigenvalueBound

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-! ### The form `i β ∧ βBar` -/

section Square

variable {n : ℕ}

/-- The real part of a `ℂ`-linear form, as a real covector. -/
def reForm (β : ComplexModel n →L[ℂ] ℂ) : ComplexModel n →L[ℝ] ℝ :=
  Complex.reCLM.comp (β.restrictScalars ℝ)

/-- The imaginary part of a `ℂ`-linear form, as a real covector. -/
def imForm (β : ComplexModel n →L[ℂ] ℂ) : ComplexModel n →L[ℝ] ℝ :=
  Complex.imCLM.comp (β.restrictScalars ℝ)

@[simp] theorem reForm_apply (β : ComplexModel n →L[ℂ] ℂ) (v : ComplexModel n) :
    reForm β v = (β v).re := rfl

@[simp] theorem imForm_apply (β : ComplexModel n →L[ℂ] ℂ) (v : ComplexModel n) :
    imForm β v = (β v).im := rfl

/-- **The real two-form `i β ∧ βBar`** of a `(1,0)`-covector `β`: with `β = a + i b`,
`i β ∧ βBar = 2 a ∧ b`. -/
def oneOneSquare (β : ComplexModel n →L[ℂ] ℂ) : RealForm n 2 :=
  (2 : ℝ) • oneWedge (reForm β)
    (ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel n) ℝ (0 : Fin 1) (imForm β))

/-- The literal value `(i β ∧ βBar)(u, v) = i (β(u) βBar(v) - β(v) βBar(u))`, as a real number. -/
theorem oneOneSquare_apply (β : ComplexModel n →L[ℂ] ℂ) (u v : ComplexModel n) :
    oneOneSquare β ![u, v] = 2 * ((β u).re * (β v).im - (β v).re * (β u).im) := by
  rw [oneOneSquare, ContinuousAlternatingMap.smul_apply, oneWedge_apply_two, smul_eq_mul]
  rfl

/-- The complex formula: `(i β ∧ βBar)(u, v) = i (β(u) conj β(v) - β(v) conj β(u))`. -/
theorem oneOneSquare_apply_eq_complex (β : ComplexModel n →L[ℂ] ℂ) (u v : ComplexModel n) :
    (oneOneSquare β ![u, v] : ℂ) =
      Complex.I * (β u * (starRingEnd ℂ) (β v) - β v * (starRingEnd ℂ) (β u)) := by
  rw [oneOneSquare_apply]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem oneOneSquare_isOneOne (β : ComplexModel n →L[ℂ] ℂ) : IsOneOne (oneOneSquare β) := by
  intro u v
  simp only [oneOneSquare_apply, map_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

theorem oneOneSquare_apply_I_nonneg (β : ComplexModel n →L[ℂ] ℂ) (v : ComplexModel n) :
    0 ≤ oneOneSquare β ![v, Complex.I • v] := by
  simp only [oneOneSquare_apply, map_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  nlinarith [sq_nonneg (β v).re, sq_nonneg (β v).im]

/-- `i β ∧ βBar` is a semipositive real `(1,1)`-form. -/
theorem isSemipositiveOneOne_oneOneSquare (β : ComplexModel n →L[ℂ] ℂ) :
    IsSemipositiveOneOne (oneOneSquare β) :=
  ⟨oneOneSquare_isOneOne β, fun v => oneOneSquare_apply_I_nonneg β v⟩

/-- **The product `i β₁ ∧ βBar₁ ∧ ⋯ ∧ i β_q ∧ βBar_q`.** -/
def betaProduct {q : ℕ} (β : Fin q → ComplexModel n →L[ℂ] ℂ) : RealForm n (2 * q) :=
  wedgeProd q fun j => oneOneSquare (β j)

theorem wedgeProd_mem_spCone : ∀ (q : ℕ) (β : Fin q → RealForm n 2),
    (∀ j, IsSemipositiveOneOne (β j)) → wedgeProd q β ∈ spCone q
  | 0, _, _ => unit_mem_spCone
  | q + 1, β, hβ => by
    rw [wedgeProd_succ]
    exact wedge_mem_spCone (wedgeProd_mem_spCone q _ fun j => hβ _) (hβ _)

/-- Products of the forms `i β ∧ βBar` are strongly positive. -/
theorem betaProduct_mem_spCone {q : ℕ} (β : Fin q → ComplexModel n →L[ℂ] ℂ) :
    betaProduct β ∈ spCone q :=
  wedgeProd_mem_spCone q _ fun j => isSemipositiveOneOne_oneOneSquare (β j)

theorem betaProduct_mem_formSpan {q : ℕ} (β : Fin q → ComplexModel n →L[ℂ] ℂ) :
    betaProduct β ∈ formSpan n q :=
  mem_formSpan_of_mem_spCone (betaProduct_mem_spCone β)

/-- The normalized Hermitian matrix of `i β ∧ βBar` is `2π β βᴴ` in the coordinates
`β_j = β(e_j)`. -/
theorem normalizedHermitianMatrix_oneOneSquare (β : ComplexModel n →L[ℂ] ℂ) :
    normalizedHermitianMatrix (oneOneSquare β) =
      ((2 * Real.pi : ℝ) : ℂ) • vecMulVec (fun j => β (coordinateVector j))
        (fun k => star (β (coordinateVector k))) := by
  ext j k
  simp only [normalizedHermitianMatrix, oneOneSquare_apply, map_smul, smul_eq_mul,
    Matrix.smul_apply, vecMulVec_apply]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring

end Square

/-! ### Mixed coefficients against diagonal units -/

section Mixed

variable {m : ℕ}

/-- `C(K, E₁₁, …, E_mm) = K₀₀`. -/
theorem mixedCoefficient_cons_unitDiag_succ (K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons K (fun j : Fin m => unitDiag j.succ) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = K 0 0 := by
  classical
  set H : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Fin.cons K (fun j : Fin m => unitDiag j.succ) with hH
  have hrow : ∀ σ : Equiv.Perm (Fin (m + 1)),
      Matrix.det (fun j k => H (σ j) j k) = if σ = 1 then K 0 0 else 0 := by
    intro σ
    by_cases h1 : σ = 1
    · subst h1
      rw [ite_eq_left rfl]
      have hM : (Matrix.of fun j k => H ((1 : Equiv.Perm (Fin (m + 1))) j) j k) =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).updateRow 0
            (∑ k, K 0 k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) k) := by
        ext j k
        by_cases hj : j = 0
        · subst hj
          simp only [Matrix.of_apply, Equiv.Perm.one_apply, hH, Fin.cons_zero,
            Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, Matrix.one_apply,
            smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            ite_true]
        · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hj
          simp only [Matrix.of_apply, Equiv.Perm.one_apply, Matrix.updateRow_ne hj, hH,
            Fin.cons_succ, unitDiag, Matrix.diagonal_apply, Matrix.one_apply, Pi.single_apply]
          by_cases hik : i.succ = k
          · subst hik; simp
          · simp [hik]
      have hdet : Matrix.det (fun j k => H ((1 : Equiv.Perm (Fin (m + 1))) j) j k) =
          Matrix.det (Matrix.of fun j k => H ((1 : Equiv.Perm (Fin (m + 1))) j) j k) := rfl
      rw [hdet, hM, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]
    · rw [ite_eq_right h1]
      have hex : ∃ j, σ j ≠ 0 ∧ σ j ≠ j := by
        by_contra hno
        push Not at hno
        apply h1
        have h0 : σ 0 = 0 := by
          by_contra h0
          exact h0 (hno 0 h0)
        ext j
        by_cases hj : σ j = 0
        · have : j = 0 := σ.injective (hj.trans h0.symm)
          subst this
          simp [h0]
        · simp [hno j hj]
      obtain ⟨j, hj0, hjj⟩ := hex
      apply Matrix.det_eq_zero_of_row_eq_zero j
      intro k
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hj0
      have hne : j ≠ i.succ := fun h => hjj (hi.symm.trans h.symm)
      simp only [hH, ← hi, Fin.cons_succ, unitDiag, Matrix.diagonal_apply, Pi.single_apply]
      split_ifs <;> simp_all
  rw [mixedCoefficient]
  simp_rw [hrow]
  simp

/-- A column of a matrix gives the rank-one matrix `w wᴴ = W E_jj Wᴴ`. -/
theorem vecMulVec_col_eq_mul_unitDiag (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (j : Fin (m + 1)) :
    vecMulVec (fun l => W l j) (fun l => star (W l j)) = W * unitDiag j * Wᴴ := by
  ext a b
  simp only [vecMulVec_apply, Matrix.mul_apply, unitDiag, Matrix.diagonal_apply,
    Pi.single_apply, conjTranspose_apply, mul_ite, mul_one, mul_zero]
  simp

end Mixed

/-! ### The directional test -/

section Direction

variable {m : ℕ}

/-- The `ℂ`-linear forms `β_j = ⟨w_j, ·⟩`, `w_j = conj (W · (j+1))`, so `β_j(e_l) = W l (j+1)`. -/
def columnForms (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j : Fin m) :
    ComplexModel (m + 1) →L[ℂ] ℂ :=
  innerSL ℂ (WithLp.toLp 2 (fun l => star (W l j.succ)) : ComplexModel (m + 1))

theorem columnForms_coordinateVector (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j : Fin m)
    (l : Fin (m + 1)) : columnForms W j (coordinateVector l) = W l j.succ := by
  simp [columnForms, coordinateVector, EuclideanSpace.inner_single_right]

/-- **The directional density.** For a unitary `W` (`W Wᴴ = 1`) with first column `ā` (`‖a‖ = 1`),
    the top
density of `dd^c f ∧ ∏_j i β_j ∧ βBar_j`, `β_j = columnForms W j`, is `((2π)^m/π^{m+1}) L_f(a)`. -/
theorem topDensity_cons_unitaryBetaProduct {f : ComplexModel (m + 1) → ℝ}
    {z : ComplexModel (m + 1)} (hf : ContDiffAt ℝ 2 f z) (a : ComplexModel (m + 1))
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hWW' : W * Wᴴ = 1)
    (hW0 : ∀ i, W i 0 = star (a i)) :
    topDensity (wedgeProd (m + 1) (Fin.cons (smoothDDC f z)
        (fun j : Fin m => oneOneSquare (columnForms W j)))) =
      ((2 * Real.pi) ^ m / Real.pi ^ (m + 1)) * leviForm f z a := by
  have hslots : ∀ i, IsOneOne ((Fin.cons (smoothDDC f z)
      (fun j : Fin m => oneOneSquare (columnForms W j)) :
        Fin (m + 1) → RealForm (m + 1) 2) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact fun u v => smoothDDC_isOneOne hf u v
    · simp only [Fin.cons_succ]
      exact oneOneSquare_isOneOne _
  rw [topDensity_wedgeProd, actualMixedTopDensity_eq_normalizedMixedTopDensity _ hslots,
    normalizedMixedTopDensity]
  set c : Fin (m + 1) → ℂ := Fin.cons 1 (fun _ : Fin m => ((2 * Real.pi : ℝ) : ℂ)) with hc
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Wᴴ * complexHessian f z * W with hK
  have hfun : (fun i => normalizedHermitianMatrix ((Fin.cons (smoothDDC f z)
      (fun j : Fin m => oneOneSquare (columnForms W j)) : Fin (m + 1) → RealForm (m + 1) 2) i)) =
      fun i => c i • (W * ((Fin.cons K (fun j : Fin m => unitDiag j.succ) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i) * Wᴴ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, hc, one_smul, hK]
      rw [normalizedHermitianMatrix_smoothDDC hf, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW',
        Matrix.one_mul, Matrix.mul_assoc, hWW', Matrix.mul_one]
    · simp only [Fin.cons_succ, hc]
      rw [normalizedHermitianMatrix_oneOneSquare, ← vecMulVec_col_eq_mul_unitDiag]
      congr 2
      · funext l; exact columnForms_coordinateVector W j l
      · funext l; rw [columnForms_coordinateVector]
  have hdet : W.det * Wᴴ.det = 1 := by
    rw [← Matrix.det_mul, hWW', Matrix.det_one]
  rw [hfun, mixedCoefficient_smul_family,
    MixedMongeAmpere.mixedCoefficient_mul_mul, hdet,
    one_mul, mixedCoefficient_cons_unitDiag_succ]
  have hprod : ∏ i, c i = ((2 * Real.pi : ℝ) : ℂ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp [hc]
  have hK00 : K 0 0 = star (fun j => star (a j)) ⬝ᵥ complexHessian f z *ᵥ
      (fun j => star (a j)) := by
    simp only [hK, Matrix.mul_apply, conjTranspose_apply, dotProduct, Matrix.mulVec, hW0,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.star_apply]
    ring
  rw [hprod, hK00, dotProduct_mulVec_complexHessian_eq_leviForm hf, coordCombination_star]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- **The directional β-product test**: for a unit vector `a` there are constant `(1,0)`-forms
`β₁, …, β_m` such that the pairing of `dd^c T` with `φ · ∏ i β_j ∧ βBar_j` is
`((2π)^m/π^{m+1})` times the distributional Levi form of `T` in the direction `a`,
    tested on `φ`. -/
theorem exists_directional_betaProduct_test {U : TopologicalSpace.Opens (ComplexModel (m + 1))}
    (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (a : ComplexModel (m + 1)) (ha : ‖a‖ = 1) :
    ∃ (β : Fin m → ComplexModel (m + 1) →L[ℂ] ℂ) (α : 𝓓(U, RealForm (m + 1) (2 * m))),
      (∀ z, α z = φ z • betaProduct β) ∧
      (∑ i, ddc (scalarTopCurrent T) (formBasis (m + 1) m i) (coeffTest α i)) =
        ((2 * Real.pi) ^ m / Real.pi ^ (m + 1)) * distributionalLeviCLM a T φ := by
  set y : Fin (m + 1) → ℂ := fun j => star (a j) with hydef
  have hy : star y ⬝ᵥ y = 1 := by
    have h2 : ‖a‖ ^ 2 = 1 := by rw [ha]; norm_num
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    simp only [hydef, dotProduct, Pi.star_apply, star_star]
    rw [← Complex.ofReal_one, ← h2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  obtain ⟨W, _hWW, hWW', hW0⟩ := exists_unitary_col_zero y hy
  let β : Fin m → ComplexModel (m + 1) →L[ℂ] ℂ := columnForms W
  let γ : formSpan (m + 1) m := ⟨betaProduct β, betaProduct_mem_formSpan β⟩
  let α : 𝓓(U, RealForm (m + 1) (2 * m)) :=
    TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (γ : RealForm (m + 1) (2 * m))) φ
  have hαval (z : ComplexModel (m + 1)) : α z = φ z • betaProduct β := rfl
  have hαadj : scalarAdjointTest α =
      ((2 * Real.pi) ^ m / Real.pi ^ (m + 1)) • leviScalarTest a φ := by
    refine scalarAdjointTest_constForm_eq_leviScalarTest γ φ a
      ((2 * Real.pi) ^ m / Real.pi ^ (m + 1)) ?_
    intro z
    change topDensity (coordinateWedge (wedgeProd m fun j => oneOneSquare (β j))
      (smoothDDC φ z)) = _
    rw [← wedgeProd_snoc, NormalDirectionVanishing.wedgeProd_snoc_eq_cons,
      topDensity_cons_unitaryBetaProduct
        (φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a W
        hWW' (fun i => hW0 i)]
  refine ⟨β, α, hαval, ?_⟩
  rw [ddc_scalarTopCurrent_full_test_transpose, hαadj, map_smul, smul_eq_mul,
    apply_leviScalarTest]

/-- **Levi positivity from the β-product test.**  If `dd^c T ∧ ∏ i β_j ∧ βBar_j` is a positive
measure for all constant `(1,0)`-forms `β₁, …, β_m` (tested on the full compact test forms
`φ ∏ i β_j ∧ βBar_j`, `φ ≥ 0`), then `T` has nonnegative distributional Levi form. -/
theorem hasNonnegativeDistributionalLevi_of_betaProduct_pairings
    {U : TopologicalSpace.Opens (ComplexModel (m + 1))} (T : 𝓓'(U, ℝ))
    (hT : ∀ (β : Fin m → ComplexModel (m + 1) →L[ℂ] ℂ) (α : 𝓓(U, RealForm (m + 1) (2 * m)))
      (φ : 𝓓(U, ℝ)), (∀ z, 0 ≤ φ z) → (∀ z, α z = φ z • betaProduct β) →
        0 ≤ ∑ i, ddc (scalarTopCurrent T) (formBasis (m + 1) m i) (coeffTest α i)) :
    HasNonnegativeDistributionalLevi T := by
  have hunit (a : ComplexModel (m + 1)) (ha : ‖a‖ = 1)
      (φ : 𝓓(U, ℝ)) (hφ : ∀ z, 0 ≤ φ z) : 0 ≤ distributionalLeviCLM a T φ := by
    obtain ⟨β, α, hα, heq⟩ := exists_directional_betaProduct_test T φ a ha
    have h := hT β α φ hφ hα
    rw [heq] at h
    exact (mul_nonneg_iff_of_pos_left
      (div_pos (pow_pos (by positivity) m) (pow_pos Real.pi_pos (m + 1)))).mp h
  exact FullPositiveScalarCurrentLeviConverse.hasNonnegativeDistributionalLevi_of_unit T hunit

end Direction

end SGPT.PSH.BookCurrent
