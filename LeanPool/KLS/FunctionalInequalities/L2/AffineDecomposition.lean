/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Affine decomposition bounds in `L²`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), end of the proof of Proposition 7.1, p. 30: an
`f ∈ L²(μ)` splits as `c + ℓ + h` with `c` constant, `ℓ` linear and `h` orthogonal to the affine
functions, and a linear operator that kills constants and is bounded by `A` on linear functions and
on the affine-orthogonal part is bounded by `√2 A`.

`norm_apply_le_sqrt_two_mul` is the abstract Hilbert-space form, for orthogonal
finite-dimensional subspaces `K` (constants) and `L` (linear functions).

`affineOrthPart μ g = g - ∫ g dμ - Σ_j (∫ ⟪e_j, y⟫ g(y) dμ) ⟪e_j, ·⟫` is the concrete
affine-orthogonal part of a function on `ℝⁿ` for a centered probability measure `μ` with identity
covariance; its properties are stated with those moment hypotheses only.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.L2

/-- **Three-term orthogonal decomposition bound** (BKL p. 30). -/
theorem norm_apply_le_sqrt_two_mul {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
     [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K L : Submodule ℝ H) [FiniteDimensional ℝ K] [FiniteDimensional ℝ L] (hKL : K ⟂ L)
    (T : H →ₗ[ℝ] F) {A : ℝ} (hA : 0 ≤ A) (hK : ∀ x ∈ K, T x = 0)
    (hL : ∀ x ∈ L, ‖T x‖ ≤ A * ‖x‖) (hH : ∀ x ∈ (K ⊔ L)ᗮ, ‖T x‖ ≤ A * ‖x‖) (f : H) :
    ‖T f‖ ≤ Real.sqrt 2 * A * ‖f‖ := by
    let U := K ⊔ L
    let P := U.starProjection
    let q := f - P f
    have hP : P f ∈ U := by
      change (U.orthogonalProjectionOnto f : H) ∈ U
      exact (U.orthogonalProjectionOnto f).2
    have hq : q ∈ Uᗮ := by
      dsimp [q, P]
      exact U.sub_starProjection_mem_orthogonal f
    obtain ⟨k, hk, l, hl, hkl⟩ := Submodule.mem_sup.mp hP
    have hkU : k ∈ U := by
      exact (show K ≤ K ⊔ L from le_sup_left) hk
    have hlU : l ∈ U := by
      exact (show L ≤ K ⊔ L from le_sup_right) hl
    have hkl_inner : inner ℝ k l = 0 := hKL.inner_eq hk hl
    have hkq : inner ℝ k q = 0 := hq k hkU
    have hlq : inner ℝ l q = 0 := hq l hlU
    have hklq : inner ℝ (k + l) q = 0 := by
      rw [inner_add_left]
      rw [hkq, hlq, add_zero]
    have hnorm_kl :
        ‖k + l‖ ^ 2 = ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
      simpa [sq] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_real hkl_inner)
    have hnorm_f :
        ‖f‖ ^ 2 = ‖k‖ ^ 2 + ‖l‖ ^ 2 + ‖q‖ ^ 2 := by
      have h1 :
          ‖(k + l) + q‖ ^ 2 = ‖k + l‖ ^ 2 + ‖q‖ ^ 2 := by
        simpa [sq] using
          (norm_add_sq_eq_norm_sq_add_norm_sq_real hklq)
      have hf : f = (k + l) + q := by
        dsimp [q]
        rw [← hkl]
        abel
      rw [hf, h1, hnorm_kl]
    have hTf : T f = T l + T q := by
      have hkzero : T k = 0 := hK k hk
      have hf : f = (k + l) + q := by
        dsimp [q]
        rw [← hkl]
        abel
      rw [hf, map_add, map_add, hkzero, zero_add]
    have hT : ‖T f‖ ≤ A * (‖l‖ + ‖q‖) := by
      rw [hTf]
      calc
        ‖T l + T q‖ ≤ ‖T l‖ + ‖T q‖ := norm_add_le _ _
        _ ≤ A * ‖l‖ + A * ‖q‖ :=
          add_le_add (hL l hl) (hH q hq)
        _ = A * (‖l‖ + ‖q‖) := by ring
    have hsum :
        ‖l‖ + ‖q‖ ≤
          Real.sqrt 2 * Real.sqrt (‖l‖ ^ 2 + ‖q‖ ^ 2) := by
      calc
        ‖l‖ + ‖q‖ ≤ |‖l‖ + ‖q‖| := le_abs_self _
        _ ≤ Real.sqrt (2 * (‖l‖ ^ 2 + ‖q‖ ^ 2)) :=
          Real.abs_le_sqrt (by nlinarith [sq_nonneg (‖l‖ - ‖q‖)])
        _ = Real.sqrt 2 * Real.sqrt (‖l‖ ^ 2 + ‖q‖ ^ 2) := Real.sqrt_mul (by norm_num) _
    have hnorm_sqrt :
        Real.sqrt (‖l‖ ^ 2 + ‖q‖ ^ 2) ≤ ‖f‖ := by
      have hr : 0 ≤ Real.sqrt (‖l‖ ^ 2 + ‖q‖ ^ 2) :=
        Real.sqrt_nonneg _
      have hf : 0 ≤ ‖f‖ := norm_nonneg _
      have hr_sq :
          (Real.sqrt (‖l‖ ^ 2 + ‖q‖ ^ 2)) ^ 2 =
            ‖l‖ ^ 2 + ‖q‖ ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [hnorm_f]
    calc
      ‖T f‖ ≤ A * (‖l‖ + ‖q‖) := hT
      _ ≤ A * (Real.sqrt 2 * Real.sqrt (‖l‖ ^ 2 + ‖q‖ ^ 2)) := by
        gcongr
      _ ≤ A * (Real.sqrt 2 * ‖f‖) := by
        gcongr
      _ = Real.sqrt 2 * A * ‖f‖ := by ring

section Comparison

/-- `∫ u² ≤ ∫ v²` implies `‖u‖₂ ≤ ‖v‖₂` for `u, v ∈ L²`. -/
theorem eLpNorm_le_eLpNorm_of_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (h : ∫ x, u x ^ 2 ∂μ ≤ ∫ x, v x ^ 2 ∂μ) :
    eLpNorm u 2 μ ≤ eLpNorm v 2 μ := by
    have hu_int : Integrable (fun x => u x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
    have hv_int : Integrable (fun x => v x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).1 hv
    have hu_nonneg : 0 ≤ᵐ[μ] (fun x => u x ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg (u x))
    have hv_nonneg : 0 ≤ᵐ[μ] (fun x => v x ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg (v x))
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    have hpoint_u (x : α) :
        ‖u x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (u x ^ 2) := by
      rw [Real.eNorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) htwo]
      simp [sq_abs]
    have hpoint_v (x : α) :
        ‖v x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (v x ^ 2) := by
      rw [Real.eNorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) htwo]
      simp [sq_abs]
    have hu_lint :
        (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) =
          ENNReal.ofReal (∫ x, u x ^ 2 ∂μ) := by
      calc
        (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) =
            ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ := by
              simp_rw [hpoint_u]
        _ = ENNReal.ofReal (∫ x, u x ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hu_int hu_nonneg).symm
    have hv_lint :
        (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) =
          ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) := by
      calc
        (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) =
            ∫⁻ x, ENNReal.ofReal (v x ^ 2) ∂μ := by
              simp_rw [hpoint_v]
        _ = ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hv_int hv_nonneg).symm
    have hu_norm :
        eLpNorm u 2 μ =
          (ENNReal.ofReal (∫ x, u x ^ 2 ∂μ)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hu.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat]
      rw [hu_lint]
    have hv_norm :
        eLpNorm v 2 μ =
          (ENNReal.ofReal (∫ x, v x ^ 2 ∂μ)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hv.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat]
      rw [hv_lint]
    rw [hu_norm, hv_norm]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) (by norm_num)

end Comparison

section AffineOrthPart

variable {n : ℕ}

/-- The affine-orthogonal part of `g`: `g` minus its mean and its linear component. -/
noncomputable def affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  g x - ∫ y, g y ∂μ -
    ∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫

/-- The affine-orthogonal part is centered. -/
theorem integral_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x ∂μ = 0 := by
    have hlin (u : EuclideanSpace ℝ (Fin n)) :
        MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫) 2 μ := by
      simpa [Function.comp_def] using
        ((innerSL ℝ u).comp_memLp' hμ2)
    have hmean (u : EuclideanSpace ℝ (Fin n)) :
        ∫ x, ⟪u, x⟫ ∂μ = 0 := by
      have h :=
        (innerSL ℝ u).integral_comp_comm (hμ2.integrable one_le_two)
      simpa [Function.comp_def, hμ0] using h
    have hconst (c : ℝ) : ∫ x, c ∂μ = c := by
      rw [integral_const]
      simp
    have hterm (j : Fin n) :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) μ := by
      simpa only [smul_eq_mul] using
        (((hlin (EuclideanSpace.basisFun (Fin n) ℝ j)).integrable one_le_two).const_mul
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ))
    have hsum :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) μ := by
      refine integrable_finsetSum Finset.univ ?_
      intro j hj
      exact hterm j
    have hsub :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            g x - ∫ y, g y ∂μ) μ := by
      exact (hg.integrable one_le_two).sub (integrable_const _)
    have hsum_zero :
        ∫ x, (∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
          ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ = 0 := by
      rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro j hj
        simp [integral_const_mul, hmean]
      · intro j hj
        exact hterm j
    unfold affineOrthPart
    rw [integral_sub hsub hsum,
      integral_sub (hg.integrable one_le_two) (integrable_const _)]
    rw [hsum_zero]
    simp [hconst]

/-- The affine-orthogonal part is in `L²`. -/
theorem memLp_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    MemLp (affineOrthPart μ g) 2 μ := by
    have hlin (u : EuclideanSpace ℝ (Fin n)) :
        MemLp (fun x => ⟪u, x⟫) 2 μ := by
      simpa [Function.comp_def] using
        (innerSL ℝ u).comp_memLp' hμ2
    let a : Fin n → ℝ := fun j =>
      ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ
    have hsum :
        MemLp
          (fun x =>
            ∑ j : Fin n, a j *
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) 2 μ := by
      have hs :=
        memLp_finsetSum' Finset.univ (fun j _ =>
          (hlin (EuclideanSpace.basisFun (Fin n) ℝ j)).const_mul (a j))
      convert hs using 1
      funext x
      simp
    have hconst :
        MemLp (fun _ : EuclideanSpace ℝ (Fin n) => ∫ y, g y ∂μ) 2 μ :=
      memLp_const _
    have hmem := (hg.sub hconst).sub hsum
    convert hmem using 1
    funext x
    simp [affineOrthPart, a]

private theorem integral_inner_eq_zero_of_mean_zero
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪v, x⟫ ∂μ = 0 := by
  simpa [Function.comp_def, hμ0] using
    (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)

/-- The affine-orthogonal part is orthogonal to every linear function. -/
theorem integral_inner_mul_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪u, x⟫ * affineOrthPart μ g x ∂μ = 0 := by
    -- Check integrability of the products in the affine projection.
    have hu : MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫) 2 μ := by
      simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
    have hlin := integral_inner_eq_zero_of_mean_zero μ hμ2 hμ0
    have hbasis :
        ∀ j : Fin n,
          MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) 2 μ := by
      intro j
      simpa [Function.comp_def] using
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2
    have h₁ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫ * g x) μ :=
      hu.integrable_mul hg
    have h₂ :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪u, x⟫ * ∫ y, g y ∂μ) μ := by
      simpa [mul_comm] using
        ((hu.integrable one_le_two).const_mul (∫ y, g y ∂μ))
    have h₃ :
        ∀ j : Fin n,
          Integrable
            (fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪u, x⟫ *
                ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫)) μ := by
      intro j
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((hu.integrable_mul (hbasis j)).const_mul
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ))
    have hsum :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) μ := by
      simpa only [Finset.mul_sum] using
        (integrable_finsetSum _ (fun j hj => h₃ j))
    -- Evaluate the projection sum using the covariance identity.
    have hsum_eval :
        ∫ x, ⟪u, x⟫ *
            ∑ j,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ =
          ∑ j,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
      calc
        ∫ x, ⟪u, x⟫ *
            ∑ j,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ
            =
            ∫ x, ∑ j,
              ⟪u, x⟫ *
                ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ := by
              congr 1
              funext x
              rw [Finset.mul_sum]
        _ = ∑ j, ∫ x,
              ⟪u, x⟫ *
                ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ := by
              simpa using
                (integral_finsetSum
                  (μ := μ) (s := Finset.univ)
                  (f := fun j x =>
                    ⟪u, x⟫ *
                      ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫))
                  (fun j hj => h₃ j))
        _ = ∑ j,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
              apply Finset.sum_congr rfl
              intro j hj
              calc
                ∫ x, ⟪u, x⟫ *
                    ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ
                    =
                    (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                      ∫ x, ⟪u, x⟫ *
                        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ := by
                      rw [← integral_const_mul]
                      congr 1
                      funext x
                      ring
                _ = _ := by
                  rw [hμcov u (EuclideanSpace.basisFun (Fin n) ℝ j)]
    have hgj :
        ∀ j : Fin n,
          Integrable
            (fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * g x) μ := by
      intro j
      exact (hbasis j).integrable_mul hg
    have hfinal :
        ∫ x, ⟪u, x⟫ * g x ∂μ =
          ∑ j,
            ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) := by
      calc
        ∫ x, ⟪u, x⟫ * g x ∂μ =
            ∫ x,
              (∑ j,
                ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x ∂μ := by
              congr 1
              funext x
              rw [(EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner u x]
        _ = ∫ x, ∑ j,
              (⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x ∂μ := by
              congr 1
              funext x
              rw [Finset.sum_mul]
        _ = ∑ j, ∫ x,
              (⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x ∂μ := by
              simpa using
                (integral_finsetSum
                  (μ := μ) (s := Finset.univ)
                  (f := fun j x =>
                    (⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x)
                  (fun j hj => by
                    simpa [mul_assoc] using
                      (hgj j).const_mul
                        ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
    unfold affineOrthPart
    have hpoint :
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ⟪u, x⟫ *
            (g x - ∫ y, g y ∂μ -
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫)) =
        (fun x =>
          (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) -
            ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) := by
      funext x
      ring
    rw [hpoint]
    calc
      ∫ x,
          (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) -
            ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ
          =
          (∫ x, ⟪u, x⟫ * g x ∂μ -
            ∫ x, ⟪u, x⟫ * ∫ y, g y ∂μ ∂μ) -
            ∫ x, ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ := by
            calc
              ∫ x,
                  (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) -
                    ⟪u, x⟫ *
                      ∑ j,
                        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ *
                          g y ∂μ) *
                          ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ
                  =
                  ∫ x, (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) ∂μ -
                    ∫ x, ⟪u, x⟫ *
                      ∑ j,
                        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ *
                          g y ∂μ) *
                          ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ := by
                      exact integral_sub (h₁.sub h₂) hsum
              _ = _ := by
                rw [integral_sub h₁ h₂]
    _ = ∫ x, ⟪u, x⟫ * g x ∂μ -
            ∑ j,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
      rw [integral_mul_const, hlin u, hsum_eval]
      ring
    _ = 0 := by
      rw [hfinal]
      simp only [mul_comm]
      exact sub_self _

/-- For `f` centered and orthogonal to the linear functions, `f - gtilde = (f - g)~`. -/
theorem sub_affineOrthPart_eq (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
    f - affineOrthPart μ g = affineOrthPart μ (f - g) := by
    have hI :
        (∫ y, (f y - g y) ∂μ) =
          (∫ y, f y ∂μ) - ∫ y, g y ∂μ :=
      integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
    have hweighted (j : Fin n) :
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * (f y - g y) ∂μ) =
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y ∂μ) -
            ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ := by
      have hfj :
          Integrable
            (fun y => ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y) μ := by
        convert
          ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2).integrable_mul hf
            using 1
        rfl
      have hgj :
          Integrable
            (fun y => ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y) μ := by
        convert
          ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2).integrable_mul hg
            using 1
        rfl
      calc
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * (f y - g y) ∂μ) =
            ∫ y,
              (⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y -
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              ring
        _ = (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y ∂μ) -
            ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ :=
          integral_sub hfj hgj
    have hweighted_neg (j : Fin n) :
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * (f y - g y) ∂μ) =
          -∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ := by
      rw [hweighted, hfx]
      ring
    funext x
    simp only [Pi.sub_apply, affineOrthPart]
    rw [hI, hf0]
    simp_rw [hweighted_neg]
    simp only [Finset.sum_neg_distrib, neg_mul]
    ring

/-- The affine-orthogonal part of a `C²` function is `C²` with the same second derivative. -/
theorem contDiff_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (affineOrthPart μ g) ∧
      ∀ x, fderiv ℝ (fderiv ℝ (affineOrthPart μ g)) x = fderiv ℝ (fderiv ℝ g) x := by
    let e : Fin n → EuclideanSpace ℝ (Fin n) :=
      EuclideanSpace.basisFun (Fin n) ℝ
    let c : ℝ := ∫ y, g y ∂μ
    let a : Fin n → ℝ := fun j => ∫ y, ⟪e j, y⟫ * g y ∂μ
    let S : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun y => ∑ j, a j * ⟪e j, y⟫
    let C : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      ∑ j, a j • innerSL ℝ (e j)
    have hrepr :
        affineOrthPart μ g = fun y => g y - c - S y := by
      funext y
      simp only [affineOrthPart, c, a, S, e]
    have hlin (j : Fin n) :
        ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ⟪e j, y⟫) := by
      have heq :
          (fun y : EuclideanSpace ℝ (Fin n) => ⟪e j, y⟫) =
            innerSL ℝ (e j) := by
        funext y
        simp only [innerSL_apply_apply]
      rw [heq]
      exact (innerSL ℝ (e j)).contDiff
    have hS : ContDiff ℝ 2 S := by
      exact
        ContDiff.sum fun j _ =>
          (contDiff_const :
            ContDiff ℝ 2 (fun _ : EuclideanSpace ℝ (Fin n) => a j)).mul (hlin j)
    have hcont : ContDiff ℝ 2 (fun y => g y - c - S y) :=
      (hg.sub contDiff_const).sub hS
    have hSd (y : EuclideanSpace ℝ (Fin n)) : HasFDerivAt S C y := by
      have h :=
        HasFDerivAt.sum (u := Finset.univ)
          (fun j _ =>
            ((innerSL ℝ (e j)).hasFDerivAt (x := y)).const_mul (a j))
      have hsum :
          (∑ j : Fin n, fun z => a j * ⟪e j, z⟫) =
            (fun z => ∑ j : Fin n, a j * ⟪e j, z⟫) := by
        funext z
        simp only [Finset.sum_apply]
      change
        HasFDerivAt
          (fun z => ∑ j : Fin n, a j * ⟪e j, z⟫)
          (∑ j : Fin n, a j • innerSL ℝ (e j)) y
      rw [← hsum]
      simpa only [innerSL_apply_apply] using h
    have hfirst (y : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun z => g z - c - S z) y = fderiv ℝ g y - C := by
      have hg' : HasFDerivAt g (fderiv ℝ g y) y :=
        (hg.differentiable (by norm_num) y).hasFDerivAt
      exact ((hg'.sub_const c).sub (hSd y)).fderiv
    have hf :
        fderiv ℝ (affineOrthPart μ g) = fun y => fderiv ℝ g y - C := by
      rw [hrepr]
      funext y
      exact hfirst y
    constructor
    · rw [hrepr]
      exact hcont
    · intro x
      rw [hf, fderiv_sub_const]

/-- **The affine-orthogonal part is orthogonal to the affine part**: `∫ gtilde (g - gtilde) = 0`. -/
theorem integral_affineOrthPart_mul_sub (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x * (g x - affineOrthPart μ g x) ∂μ = 0 := by
    have hp : MemLp (affineOrthPart μ g) 2 μ :=
      memLp_affineOrthPart μ hμ2 hg
    have hp_int : Integrable (affineOrthPart μ g) μ :=
      hp.integrable one_le_two
    have hinner (j : Fin n) :
        MemLp
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) 2 μ := by
      change
        MemLp
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)) x) 2 μ
      simpa [Function.comp_def, id] using
        ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2)
    have hterm (j : Fin n) :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
              affineOrthPart μ g x) μ := by
      change
        Integrable
          ((fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) *
            affineOrthPart μ g) μ
      exact (hinner j).integrable_mul hp
    have hsum :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                  affineOrthPart μ g x)) μ := by
      exact integrable_finsetSum _ fun j _ =>
        (hterm j).const_mul
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ)
    have hsum_int :
        (∫ x, ∑ j : Fin n,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                affineOrthPart μ g x) ∂μ) =
          ∑ j : Fin n, ∫ x,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                affineOrthPart μ g x) ∂μ := by
      apply integral_finsetSum
      intro j hj
      exact (hterm j).const_mul
        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ)
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        affineOrthPart μ g x * (g x - affineOrthPart μ g x) =
          (∫ y, g y ∂μ) * affineOrthPart μ g x +
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                  affineOrthPart μ g x) := by
      simp only [affineOrthPart]
      rw [show
        g x -
            (g x - ∫ y, g y ∂μ -
              ∑ j : Fin n,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) =
          (∫ y, g y ∂μ) +
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ by ring]
      rw [mul_add, Finset.mul_sum]
      ring_nf
    have hconst :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (∫ y, g y ∂μ) * affineOrthPart μ g x) μ :=
      hp_int.const_mul _
    calc
      ∫ x, affineOrthPart μ g x * (g x - affineOrthPart μ g x) ∂μ =
          ∫ x,
            (∫ y, g y ∂μ) * affineOrthPart μ g x +
              ∑ j : Fin n,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  (⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                    affineOrthPart μ g x) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ =
          (∫ y, g y ∂μ) * (∫ x, affineOrthPart μ g x ∂μ) +
            ∑ j : Fin n,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                (∫ x,
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                    affineOrthPart μ g x ∂μ) := by
        rw [integral_add hconst hsum, integral_const_mul, hsum_int]
        simp only [integral_const_mul]
      _ = 0 := by
        rw [integral_affineOrthPart μ hμ2 hμ0 hg]
        simp_rw [
          integral_inner_mul_affineOrthPart μ hμ2 hμ0 hμcov hg]
        simp

/-- **Bessel's inequality for the affine-orthogonal part**: `∫ gtilde² ≤ ∫ g²`. -/
theorem integral_affineOrthPart_sq_le (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by
    let f := affineOrthPart μ g
    let P : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g x - f x
    have hf : MemLp f 2 μ := by
      simpa [f] using memLp_affineOrthPart μ hμ2 hg
    have hP : MemLp P 2 μ := by
      change MemLp (g - f) 2 μ
      exact hg.sub hf
    have hfi : Integrable f μ := hf.integrable (by norm_num)
    have hf2 : Integrable (fun x => f x ^ 2) μ := by
      convert hf.integrable_mul hf using 1;
        ext x; simp [Pi.mul_apply, pow_two]
    have hP2 : Integrable (fun x => P x ^ 2) μ := by
      convert hP.integrable_mul hP using 1;
        ext x; simp [Pi.mul_apply, pow_two]
    have hcrossi : Integrable (fun x => f x * P x) μ :=
      hf.integrable_mul hP
    have hP_formula :
        ∀ x, P x =
          (∫ y, g y ∂μ) +
            ∑ j : Fin n,
              (∫ y,
                ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ) *
                ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫ := by
      intro x
      simp [P, f, affineOrthPart]
      ring
    have hcross : ∫ x, f x * P x ∂μ = 0 := by
      let a : ℝ := ∫ y, g y ∂μ
      let b : Fin n → ℝ := fun j =>
        ∫ y, ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ
      let q : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun j x =>
        b j * ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫
      have hinner :
          ∀ j : Fin n,
            MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫) 2 μ := by
        intro j
        simpa using
          ((innerSL ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) j)).comp_memLp' hμ2)
      have hq : ∀ j : Fin n, Integrable (fun x => f x * q j x) μ := by
        intro j
        have h := hf.integrable_mul (hinner j)
        dsimp [q, b]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          h.mul_const
            (∫ y,
              ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ)
      have hs : Integrable (fun x => f x * ∑ j : Fin n, q j x) μ := by
        have hs' :
            Integrable (fun x => ∑ j : Fin n, f x * q j x) μ := by
          exact
            integrable_finsetSum (s := (Finset.univ : Finset (Fin n)))
              (f := fun j x => f x * q j x) (fun j hj => hq j)
        simpa only [Finset.mul_sum] using hs'
      have hc : Integrable (fun x => f x * a) μ := hfi.mul_const _
      have he :
          ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ =
            (∫ x, f x * a ∂μ) +
              ∑ j : Fin n, ∫ x, f x * q j x ∂μ := by
        calc
          ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ =
              ∫ x, (f x * a) + (f x * ∑ j : Fin n, q j x) ∂μ := by
                apply integral_congr_ae
                filter_upwards [] with x
                ring
          _ = (∫ x, f x * a ∂μ) +
              ∫ x, f x * ∑ j : Fin n, q j x ∂μ := by
                exact integral_add hc hs
          _ = (∫ x, f x * a ∂μ) +
              ∑ j : Fin n, ∫ x, f x * q j x ∂μ := by
                congr 1
                calc
                  ∫ x, f x * ∑ j : Fin n, q j x ∂μ =
                      ∫ x, ∑ j : Fin n, f x * q j x ∂μ := by
                        apply integral_congr_ae
                        filter_upwards [] with x
                        rw [Finset.mul_sum]
                  _ = ∑ j : Fin n, ∫ x, f x * q j x ∂μ := by
                    simpa using
                      (integral_finsetSum (s := (Finset.univ : Finset (Fin n)))
                        (f := fun j x => f x * q j x)
                        (fun j hj => hq j))
      have hz :
          ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ =
            a * (∫ x, f x ∂μ) +
              ∑ j : Fin n, b j *
                (∫ x,
                  ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫ * f x ∂μ) := by
        rw [he]
        congr 1
        · rw [integral_mul_const]
          ring
        · apply Finset.sum_congr rfl
          intro j hj
          dsimp [q]
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
      calc
        ∫ x, f x * P x ∂μ =
            ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hP_formula x]
        _ = a * (∫ x, f x ∂μ) +
              ∑ j : Fin n, b j *
                (∫ x,
                  ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫ * f x ∂μ) := hz
        _ = 0 := by
          rw [integral_affineOrthPart μ hμ2 hμ0 hg]
          simp only [mul_zero, zero_add]
          apply Finset.sum_eq_zero
          intro j hj
          have ho :=
            integral_inner_mul_affineOrthPart μ hμ2 hμ0 hμcov hg
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)
          dsimp [b, f]
          simpa using congrArg
            (fun z =>
              (∫ y,
                ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ) * z) ho
    have hsq :
        (∫ x, g x ^ 2 ∂μ) =
          (∫ x, f x ^ 2 ∂μ) +
            2 * (∫ x, f x * P x ∂μ) +
              ∫ x, P x ^ 2 ∂μ := by
      have hi : Integrable (fun x => 2 * (f x * P x) + P x ^ 2) μ :=
        (hcrossi.const_mul _).add hP2
      have hsplit :
          ∫ x, 2 * (f x * P x) + P x ^ 2 ∂μ =
            (∫ x, 2 * (f x * P x) ∂μ) +
              ∫ x, P x ^ 2 ∂μ :=
        integral_add (hcrossi.const_mul _) hP2
      calc
        ∫ x, g x ^ 2 ∂μ =
            ∫ x, (f x + P x) ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [P]
        _ = ∫ x, (f x ^ 2 + (2 * (f x * P x) + P x ^ 2)) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
        _ = (∫ x, f x ^ 2 ∂μ) +
              ∫ x, (2 * (f x * P x) + P x ^ 2) ∂μ := by
              exact integral_add hf2 hi
        _ = (∫ x, f x ^ 2 ∂μ) +
              (∫ x, 2 * (f x * P x) ∂μ) +
                ∫ x, P x ^ 2 ∂μ := by
              rw [hsplit]
              ring
        _ = (∫ x, f x ^ 2 ∂μ) +
              2 * (∫ x, f x * P x ∂μ) +
                ∫ x, P x ^ 2 ∂μ := by
              rw [integral_const_mul]
    have hnonneg : 0 ≤ ∫ x, P x ^ 2 ∂μ :=
      integral_nonneg fun x => sq_nonneg (P x)
    have hle : ∫ x, f x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by
      rw [hsq, hcross]
      linarith
    simpa [f] using hle

/-- **Contraction towards the affine-orthogonal functions**: if `f ∈ L²` is centered and orthogonal
to the linear functions, then `‖f - gtilde‖₂ ≤ ‖f - g‖₂`. -/
theorem eLpNorm_sub_affineOrthPart_le (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) (hf0 : ∫ x, f x ∂μ = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
    eLpNorm (f - affineOrthPart μ g) 2 μ ≤ eLpNorm (f - g) 2 μ := by
  rw [sub_affineOrthPart_eq μ hμ2 hf hf0 hfx hg]
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  refine eLpNorm_le_eLpNorm_of_integral_sq_le
      (memLp_affineOrthPart μ hμ2 hfg) hfg ?_
  exact integral_affineOrthPart_sq_le μ hμ2 hμ0 hμcov hfg

/-- **Square integral of an affine function** under a centered law with identity covariance. -/
theorem integral_affine_sq (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
      c ^ 2 + ∑ j, a j ^ 2 := by
    classical
    let v : EuclideanSpace ℝ (Fin n) :=
      ∑ j, a j • EuclideanSpace.basisFun (Fin n) ℝ j
    have hsum (x : EuclideanSpace ℝ (Fin n)) :
        ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ = ⟪v, x⟫ := by
      simp [v, sum_inner, inner_smul_left]
    have hlin_mem : MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪v, x⟫) 2 μ := by
      simpa [Function.comp_def] using (innerSL ℝ v).comp_memLp' hμ2
    have hlin_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ⟪v, x⟫) μ :=
      hlin_mem.integrable one_le_two
    have hprod_int :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => ⟪v, x⟫ * ⟪v, x⟫) μ := by
      exact hlin_mem.integrable_mul hlin_mem
    have hscaled_int :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => 2 * c * ⟪v, x⟫) μ := by
      exact hlin_int.const_mul (2 * c)
    have hzero : ∫ x, ⟪v, x⟫ ∂μ = 0 := by
      simpa [Function.comp_def, hμ0] using
        (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)
    have hvpoint (x : Fin n) : v.ofLp x = a x := by
      simp [v, Pi.single_apply]
    have hvv : ⟪v, v⟫ = ∑ j, a j ^ 2 := by
      rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hvpoint x]
      simp [Real.norm_eq_abs]
    have hfun :
        (fun x => (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2) =
          (fun x => c ^ 2 + (2 * c * ⟪v, x⟫ + ⟪v, x⟫ * ⟪v, x⟫)) := by
      funext x
      rw [hsum]
      ring
    have hconst : ∫ x, c ^ 2 ∂μ = c ^ 2 := by
      simp
    have hlin : ∫ x, 2 * c * ⟪v, x⟫ ∂μ = 0 := by
      rw [integral_const_mul, hzero, mul_zero]
    calc
      ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
          ∫ x, c ^ 2 + (2 * c * ⟪v, x⟫ + ⟪v, x⟫ * ⟪v, x⟫) ∂μ := by
            rw [hfun]
      _ = (∫ x, c ^ 2 ∂μ) +
            ∫ x, (2 * c * ⟪v, x⟫ + ⟪v, x⟫ * ⟪v, x⟫) ∂μ := by
            exact integral_add (integrable_const _) (hscaled_int.add hprod_int)
      _ = c ^ 2 + ∑ j, a j ^ 2 := by
            rw [integral_add hscaled_int hprod_int, hconst, hlin, hμcov v v, hvv]
            ring

/-- **Pythagoras for the affine decomposition** of `f ∈ L²(μ)`. -/
theorem integral_sq_eq_affine_decomposition (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ =
      (∫ x, f x ∂μ) ^ 2 + ∑ j, (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
        ∫ x, affineOrthPart μ f x ^ 2 ∂μ := by
    let h := affineOrthPart μ f
    let c := ∫ y, f y ∂μ
    let a : Fin n → ℝ := fun j =>
      ∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * f y ∂μ
    let P : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
      c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫
    have hdecomp : ∀ x, f x = h x + P x := by
      intro x
      simp only [h, P, c, a, affineOrthPart]
      ring
    have hh : MemLp h 2 μ := by
      simpa [h] using (memLp_affineOrthPart μ hμ2 hf)
    have hPfun : P = fun x => f x - h x := by
      funext x
      linarith [hdecomp x]
    have hP : MemLp P 2 μ := by
      rw [hPfun]
      exact hf.sub hh
    have hh_sq : Integrable (fun x => h x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).1 hh
    have hP_sq : Integrable (fun x => P x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).1 hP
    have hprod : Integrable (fun x => h x * P x) μ :=
      MemLp.integrable_mul hh hP
    have hcross0 : (∫ x, h x * (f x - h x) ∂μ) = 0 := by
      simpa [h] using
        (integral_affineOrthPart_mul_sub μ hμ2 hμ0 hμcov hf)
    have hcross : (∫ x, h x * P x ∂μ) = 0 := by
      calc
        (∫ x, h x * P x ∂μ) =
            ∫ x, h x * (f x - h x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hPfun]
        _ = 0 := hcross0
    have hPsq : (∫ x, P x ^ 2 ∂μ) = c ^ 2 + ∑ j, a j ^ 2 := by
      simpa [P] using
        (integral_affine_sq μ hμ2 hμ0 hμcov c a)
    have hsum :
        Integrable (fun x => h x ^ 2 + 2 * (h x * P x)) μ :=
      hh_sq.add (hprod.const_mul 2)
    have hsq :
        (∫ x, f x ^ 2 ∂μ) =
          (∫ x, h x ^ 2 ∂μ) + 2 * (∫ x, h x * P x ∂μ) +
            ∫ x, P x ^ 2 ∂μ := by
      calc
        (∫ x, f x ^ 2 ∂μ) =
            ∫ x, (h x + P x) ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hdecomp x]
        _ = ∫ x, (h x ^ 2 + 2 * (h x * P x) + P x ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
        _ = (∫ x, h x ^ 2 + 2 * (h x * P x) ∂μ) +
              ∫ x, P x ^ 2 ∂μ := integral_add hsum hP_sq
        _ = ((∫ x, h x ^ 2 ∂μ) +
              ∫ x, 2 * (h x * P x) ∂μ) +
              ∫ x, P x ^ 2 ∂μ := by
              rw [integral_add hh_sq (hprod.const_mul 2)]
        _ = (∫ x, h x ^ 2 ∂μ) + 2 * (∫ x, h x * P x ∂μ) +
              ∫ x, P x ^ 2 ∂μ := by
              rw [integral_const_mul]
    calc
      (∫ x, f x ^ 2 ∂μ) =
          (∫ x, h x ^ 2 ∂μ) + 2 * (∫ x, h x * P x ∂μ) +
            ∫ x, P x ^ 2 ∂μ := hsq
      _ = (∫ x, h x ^ 2 ∂μ) + (c ^ 2 + ∑ j, a j ^ 2) := by
        rw [hcross, hPsq]
        ring
      _ = (∫ x, f x ∂μ) ^ 2 +
            ∑ j, (∫ x,
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
            ∫ x, affineOrthPart μ f x ^ 2 ∂μ := by
        simp only [h, c, a]
        ring

end AffineOrthPart

end FunctionalInequalities.L2
