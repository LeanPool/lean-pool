/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Sobolev.Coefficients
public import LeanPool.EllipticPDE.Poincare.Density
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram


/-!
# General divergence-form bilinear form (general elliptic matrix `A`)

We generalise the Poisson form `∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫` of `BilinearForm.lean` to the symmetric
second-order divergence-form operator `L u = -Dⱼ(aᵢⱼ Dᵢu)` with a measurable, bounded,
uniformly elliptic coefficient matrix `A` (Evans §6.1.1: the divergence-form operator
and the uniform ellipticity condition):

  `B_A[U, V] = ∑ᵢ ∑ⱼ ⟪aᵢⱼ ∂ᵢu, ∂ⱼv⟫_{L²}`.

* **Continuity** (`β = d² Λ`): coefficient actions have operator norm `≤ Λ`, and coordinate norm
  is bounded by the ambient `H¹` norm.
* **Energy identity / lower bound** (`bilin_self_ge`): `B_A[U, U] = ∫_Ω ∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼu`, and
  pointwise ellipticity `∑ᵢⱼ aᵢⱼ ξᵢ ξⱼ ≥ λ |ξ|²` integrates to `B_A[U, U] ≥ λ · ‖∇u‖²`.
* **Coercivity** (`α = λ / (C_P + 1)`): the density Poincaré inequality `poincare_H01` controls
  the function part, so `B_A` dominates the full `H¹` norm.

This is the closing Examples remark of Evans §6.2.2: the symmetric, transport-free,
`c = 0` case where `γ = 0` in the Gårding inequality and coercivity is immediate from
ellipticity plus Poincaré. It mirrors
the technique of DeGiorgi `WeakFormulation/CoefficientOperator.lean`
(`coeffBilinSubmodule_coercive`) on our scalar `PiLp` Sobolev encoding.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Poincare

variable {d : ℕ}

/-! ### Integrability helpers for products of `L²` classes -/

/-- The square of an `L²` class is integrable. -/
lemma integrable_sq {Ω : Set (EuclideanSpace ℝ (Fin d))} (p : L2D Ω) :
    Integrable (fun x => (p x : ℝ) ^ 2) (volume.restrict Ω) := by
  refine (MeasureTheory.L2.integrable_inner p p).congr ?_
  filter_upwards with x
  simp only [Real.inner_apply, pow_two]

/-- `∫_Ω (p)² = ‖p‖²` for an `L²` class `p`. -/
lemma sq_integral_eq_norm_sq {Ω : Set (EuclideanSpace ℝ (Fin d))} (p : L2D Ω) :
    ∫ x in Ω, (p x : ℝ) ^ 2 = ‖p‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.inner_apply, pow_two]

/-- The triple product `aᵢⱼ · p · q` of bounded coefficient and two `L²` classes is
integrable on `Ω`. -/
lemma EllipticCoeff.integrable_triple (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (p q : L2D Ω) :
    Integrable (fun x => A.a x i j * (p x : ℝ) * (q x : ℝ)) (volume.restrict Ω) := by
  refine (MeasureTheory.L2.integrable_inner (A.actL i j p) q).congr ?_
  filter_upwards [A.actL_coeFn i j p] with x hx
  simp only [Real.inner_apply, hx]

/-! ### General divergence-form bilinear form -/

/-- The general divergence-form bilinear form as a bare bilinear map on `H₀¹(Ω)`:
`B_A[U, V] = ∑ᵢⱼ ⟪aᵢⱼ ∂ᵢu, ∂ⱼv⟫`. -/
def EllipticCoeff.bilinₗ (A : EllipticCoeff d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →ₗ[ℝ] (H01 Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun U V => ∑ i : Fin d, ∑ j : Fin d,
      ⟪A.actL i j ((U : H1amb Ω) i.succ), ((V : H1amb Ω) j.succ)⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, map_add,
          inner_add_left, Finset.sum_add_distrib])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, map_smul,
          real_inner_smul_left, smul_eq_mul, Finset.mul_sum])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply,
          inner_add_right, Finset.sum_add_distrib])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply,
          real_inner_smul_right, smul_eq_mul, Finset.mul_sum])

/-- The general divergence-form bilinear form as a bounded (continuous) bilinear form,
with operator-norm bound `d² Λ`. -/
def EllipticCoeff.bilin (A : EllipticCoeff d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (A.bilinₗ Ω).mkContinuous₂ ((d : ℝ) ^ 2 * A.Λ) (by
    intro U V
    simp only [EllipticCoeff.bilinₗ, LinearMap.mk₂_apply]
    calc ‖∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j ((U : H1amb Ω) i.succ), ((V : H1amb Ω) j.succ)⟫‖
        ≤ ∑ i : Fin d, ∑ j : Fin d,
            ‖⟪A.actL i j ((U : H1amb Ω) i.succ), ((V : H1amb Ω) j.succ)⟫‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A.Λ * ‖U‖ * ‖V‖ := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          calc ‖⟪A.actL i j ((U : H1amb Ω) i.succ), ((V : H1amb Ω) j.succ)⟫‖
              ≤ ‖A.actL i j ((U : H1amb Ω) i.succ)‖ * ‖(V : H1amb Ω) j.succ‖ :=
                norm_inner_le_norm _ _
            _ ≤ (A.Λ * ‖(U : H1amb Ω) i.succ‖) * ‖(V : H1amb Ω) j.succ‖ := by
                gcongr; exact A.norm_actL_le i j _
            _ ≤ (A.Λ * ‖U‖) * ‖V‖ :=
                mul_le_mul (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) A.Λ_nonneg)
                  (PiLp.norm_apply_le _ _) (norm_nonneg _)
                  (mul_nonneg A.Λ_nonneg (norm_nonneg _))
      _ = (d : ℝ) ^ 2 * A.Λ * ‖U‖ * ‖V‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring)

/-- Simp lemma: `A.bilin Ω U V = ∑ i, ∑ j, ⟪A.actL i j (∂ᵢu), (∂ⱼv)⟫`. -/
@[simp] lemma EllipticCoeff.bilin_apply (A : EllipticCoeff d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    A.bilin Ω U V = ∑ i : Fin d, ∑ j : Fin d,
      ⟪A.actL i j ((U : H1amb Ω) i.succ), ((V : H1amb Ω) j.succ)⟫ := by
  simp only [EllipticCoeff.bilin, LinearMap.mkContinuous₂_apply,
    EllipticCoeff.bilinₗ, LinearMap.mk₂_apply]

/-- **Energy identity:** `B_A[U, U] = ∫_Ω ∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼu`. -/
private lemma EllipticCoeff.bilin_self_eq_integral (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (U : H01 Ω) :
    A.bilin Ω U U = ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
      A.a x i j * ((U : H1amb Ω) i.succ x : ℝ) * ((U : H1amb Ω) j.succ x : ℝ) := by
  rw [EllipticCoeff.bilin_apply,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => A.integrable_triple i j _ _)]
  exact Finset.sum_congr rfl (fun j _ => A.inner_actL_eq i j _ _)

/-- **Energy lower bound from ellipticity:** `B_A[U, U] ≥ λ · ∑ᵢ ‖∂ᵢu‖²`. -/
lemma EllipticCoeff.bilin_self_ge (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (U : H01 Ω) :
    A.lam * ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 ≤ A.bilin Ω U U := by
  set g : Fin d → L2D Ω := fun i => (U : H1amb Ω) i.succ with hg
  have hPint : Integrable (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      (volume.restrict Ω) :=
    (integrable_finsetSum _ (fun i _ => integrable_sq (g i))).const_mul A.lam
  have hQint : Integrable (fun x => ∑ i : Fin d, ∑ j : Fin d,
      A.a x i j * (g i x : ℝ) * (g j x : ℝ)) (volume.restrict Ω) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))
  have hpoint : (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      ≤ᵐ[volume.restrict Ω] fun x => ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
    (ae_restrict_of_ae A.elliptic).mono (fun x hx => hx (fun i => g i x))
  have hlamS : ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2
      = A.lam * ∑ i : Fin d, ‖g i‖ ^ 2 := by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_sq (g i))]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => sq_integral_eq_norm_sq (g i))
  calc A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      = ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2 := hlamS.symm
    _ ≤ ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
          A.a x i j * (g i x : ℝ) * (g j x : ℝ) := integral_mono_ae hPint hQint hpoint
    _ = A.bilin Ω U U := (A.bilin_self_eq_integral U).symm

/-- **Coercivity of the general elliptic form** (the closing Examples remark of Evans
§6.2.2, `γ = 0`). Given the
test-function Poincaré bound with constant `C_P ≥ 0`, the symmetric uniformly elliptic
divergence form `B_A` is coercive on `H₀¹(Ω)` with constant `λ / (C_P + 1)`. -/
theorem EllipticCoeff.bilin_coercive (A : EllipticCoeff d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    IsCoercive (A.bilin Ω) := by
  have hpos : (0 : ℝ) < CP + 1 := by linarith
  have hne : (CP : ℝ) + 1 ≠ 0 := hpos.ne'
  refine ⟨A.lam / (CP + 1), div_pos A.lam_pos hpos, ?_⟩
  intro U
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  have hBUU : A.lam * S ≤ A.bilin Ω U U := A.bilin_self_ge U
  have hnorm : ‖U‖ ^ 2 = ‖(U : H1amb Ω) 0‖ ^ 2 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  have hpoin : ‖(U : H1amb Ω) 0‖ ^ 2 ≤ CP * S := poincare_H01 CP hbase U.2
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * S := by
    have : ‖U‖ ^ 2 ≤ (CP + 1) * S := by rw [hnorm]; nlinarith [hpoin]
    nlinarith [this]
  rw [mul_assoc]
  calc A.lam / (CP + 1) * (‖U‖ * ‖U‖)
      ≤ A.lam / (CP + 1) * ((CP + 1) * S) :=
        mul_le_mul_of_nonneg_left hkey (div_pos A.lam_pos hpos).le
    _ = A.lam * S := by field_simp
    _ ≤ A.bilin Ω U U := hBUU

end EllipticPdes.Sobolev
