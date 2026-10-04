/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Form.GeneralForm
public import LeanPool.EllipticPDE.Poincare.BoundedDomain


/-!
# Transport, zeroth-order term, the Gårding inequality, and shifted existence

We add to the principal part `B_A` of `GeneralForm.lean` a **transport** term `bᵢ Dᵢu` and a
**zeroth-order** term `c u` (both bounded measurable, `c` not assumed signed):

  `B[U, V] = ∑ᵢⱼ ⟪aᵢⱼ ∂ᵢu, ∂ⱼv⟫ + ∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ + ⟪c u₀, v₀⟫`.

This is Evans §6.1.1's full divergence-form operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu`.

* **Gårding inequality** (`FullEllipticOp.garding`, Evans §6.2.2, Theorem 2(ii)): there
  are `β > 0`, `γ ≥ 0` with `β ‖U‖²_{H¹} ≤ B[U, U] + γ ‖u₀‖²_{L²}` for all `U ∈ H₀¹(Ω)`.
  We take `β = λ/2` and `γ = λ/2 + ‖c‖∞ + d ‖b‖∞² / (2λ)`. The transport term is absorbed
  into the ellipticity gap by the Peter-Paul (Young) inequality.
* **Shifted existence** (`FullEllipticOp.weak_solution`, Evans §6.2.2, Theorem 3): for
  any shift
  `μ ≥ γ` the shifted form `B_μ[U, V] = B[U, V] + μ ⟪u₀, v₀⟫` is coercive (Gårding already
  controls the full `H¹` norm, so **no Poincaré inequality is needed** here), and Lax-Milgram
  yields a unique weak solution `u ∈ H₀¹(Ω)` of `Lu + μu = f` for every `f ∈ H⁻¹(Ω)`.

The `γ = 0` symmetric case (no transport, `c ≥ 0`, needing Poincaré) is the separate
`EllipticCoeff.bilin_coercive` of `GeneralForm.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The Peter-Paul (Young) inequality `B x y ≤ (λ/2) x² + (B²/2λ) y²` for `λ > 0`. -/
lemma young_peterPaul {lam B x y : ℝ} (hlam : 0 < lam) :
    B * x * y ≤ lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 := by
  have hl : lam ≠ 0 := hlam.ne'
  have h2l : (0 : ℝ) < 2 * lam := by linarith
  rw [← sub_nonneg]
  have key : lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 - B * x * y
      = (lam * x - B * y) ^ 2 / (2 * lam) := by field_simp; ring
  rw [key]
  exact div_nonneg (sq_nonneg _) h2l.le

/-! ### Full divergence-form operator -/

/-- A full second-order divergence-form operator: a uniformly elliptic principal part `A`
together with a bounded measurable transport field `b` and zeroth-order coefficient `c`. -/
structure FullEllipticOp (d : ℕ) extends EllipticCoeff d where
  /-- Transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- Zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- Sup bound on the transport field. -/
  Bsup : ℝ
  /-- Sup bound on the zeroth-order coefficient. -/
  Csup : ℝ
  /-- The bound on the transport field is nonnegative. -/
  Bsup_nonneg : 0 ≤ Bsup
  /-- The bound on the zeroth-order coefficient is nonnegative. -/
  Csup_nonneg : 0 ≤ Csup
  /-- Every component of the transport field is measurable. -/
  b_meas : ∀ i, Measurable (fun x => b x i)
  /-- The zeroth-order coefficient is measurable. -/
  c_meas : Measurable c
  /-- Every component of the transport field is bounded by `Bsup` almost everywhere. -/
  b_bdd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bsup
  /-- The zeroth-order coefficient is bounded by `Csup` almost everywhere. -/
  c_bdd : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Csup

namespace FullEllipticOp

variable (Op : FullEllipticOp d)

/-- The transport coefficient `bᵢ` acting on `L²(Ω)`. -/
def bAct {Ω : Set (EuclideanSpace ℝ (Fin d))} (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i))

/-- The zeroth-order coefficient `c` acting on `L²(Ω)`. -/
def cAct {Ω : Set (EuclideanSpace ℝ (Fin d))} : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd)

/-- Operator-norm bound for the transport action: `‖Op.bAct i g‖ ≤ Bsup · ‖g‖`. -/
lemma norm_bAct_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (i : Fin d) (g : L2D Ω) :
    ‖Op.bAct i g‖ ≤ Op.Bsup * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Operator-norm bound for the zeroth-order action: `‖Op.cAct g‖ ≤ Csup · ‖g‖`. -/
lemma norm_cAct_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (g : L2D Ω) :
    ‖Op.cAct g‖ ≤ Op.Csup * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-! ### Lower-order (transport + zeroth) bilinear form -/

/-- The lower-order part `∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ + ⟪c u₀, v₀⟫` as a bare bilinear map. -/
def lowerBilinₗ (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →ₗ[ℝ] (H01 Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun U V => (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
      + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, map_add,
          inner_add_left, Finset.sum_add_distrib]; ring)
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, map_smul,
          real_inner_smul_left, smul_eq_mul, mul_add, Finset.mul_sum])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply,
          inner_add_right, Finset.sum_add_distrib]; ring)
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply,
          real_inner_smul_right, smul_eq_mul, mul_add, Finset.mul_sum])

/-- The lower-order bilinear form as a bounded form, with norm bound `d·Bsup + Csup`. -/
def lowerBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (Op.lowerBilinₗ Ω).mkContinuous₂ ((d : ℝ) * Op.Bsup + Op.Csup) (by
    intro U V
    simp only [FullEllipticOp.lowerBilinₗ, LinearMap.mk₂_apply]
    have hb : ‖∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
        ≤ (d : ℝ) * Op.Bsup * ‖U‖ * ‖V‖ := by
      calc ‖∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
          ≤ ∑ i : Fin d, ‖⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : Fin d, Op.Bsup * ‖U‖ * ‖V‖ := by
            apply Finset.sum_le_sum; intro i _
            calc ‖⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
                ≤ ‖Op.bAct i ((U : H1amb Ω) i.succ)‖ * ‖(V : H1amb Ω) 0‖ :=
                  norm_inner_le_norm _ _
              _ ≤ (Op.Bsup * ‖U‖) * ‖V‖ :=
                  mul_le_mul (le_trans (Op.norm_bAct_le i _)
                    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) Op.Bsup_nonneg))
                    (PiLp.norm_apply_le _ _) (norm_nonneg _)
                    (mul_nonneg Op.Bsup_nonneg (norm_nonneg _))
        _ = (d : ℝ) * Op.Bsup * ‖U‖ * ‖V‖ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hc : ‖⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖ ≤ Op.Csup * ‖U‖ * ‖V‖ :=
      calc ‖⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖
          ≤ ‖Op.cAct ((U : H1amb Ω) 0)‖ * ‖(V : H1amb Ω) 0‖ := norm_inner_le_norm _ _
        _ ≤ (Op.Csup * ‖U‖) * ‖V‖ :=
            mul_le_mul (le_trans (Op.norm_cAct_le _)
              (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) Op.Csup_nonneg))
              (PiLp.norm_apply_le _ _) (norm_nonneg _)
              (mul_nonneg Op.Csup_nonneg (norm_nonneg _))
    calc ‖(∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
            + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖
        ≤ ‖∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
            + ‖⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖ := norm_add_le _ _
      _ ≤ (d : ℝ) * Op.Bsup * ‖U‖ * ‖V‖ + Op.Csup * ‖U‖ * ‖V‖ := add_le_add hb hc
      _ = ((d : ℝ) * Op.Bsup + Op.Csup) * ‖U‖ * ‖V‖ := by ring)

/-- Simp lemma: unfolds `lowerBilin Ω U V` to the transport and zeroth-order inner products. -/
@[simp] lemma lowerBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    Op.lowerBilin Ω U V
      = (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
        + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.lowerBilin, LinearMap.mkContinuous₂_apply,
    FullEllipticOp.lowerBilinₗ, LinearMap.mk₂_apply]

/-- The full divergence-form bilinear form `B = B_A + (transport + zeroth)`. -/
def fullBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  Op.toEllipticCoeff.bilin Ω + Op.lowerBilin Ω

/-- `fullBilin = B_A + lowerBilin`: principal part plus transport and zeroth-order. -/
lemma fullBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    Op.fullBilin Ω U V = Op.toEllipticCoeff.bilin Ω U V + Op.lowerBilin Ω U V := by
  simp only [FullEllipticOp.fullBilin, _root_.add_apply]

/-! ### Gårding inequality -/

/-- The Gårding shift constant `γ = λ/2 + ‖c‖∞ + d ‖b‖∞² / (2λ)`. -/
def gardingγ : ℝ :=
  Op.lam / 2 + Op.Csup + (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam)

/-- The Gårding shift constant `γ` is non-negative. -/
lemma gardingγ_nonneg : 0 ≤ Op.gardingγ := by
  have : (0 : ℝ) < 2 * Op.lam := by have := Op.lam_pos; linarith
  unfold gardingγ
  have h1 : (0 : ℝ) ≤ Op.lam / 2 := by have := Op.lam_pos; linarith
  have h2 : (0 : ℝ) ≤ (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) :=
    div_nonneg (by positivity) this.le
  linarith [Op.Csup_nonneg]

/-- **Gårding inequality** (Evans §6.2.2, Theorem 2(ii)). With `β = λ/2` and `γ` the
shift constant, `β ‖U‖²_{H¹} ≤ B[U, U] + γ ‖u₀‖²_{L²}` for every `U ∈ H₀¹(Ω)`. -/
theorem garding (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    Op.lam / 2 * ‖U‖ ^ 2
      ≤ Op.fullBilin Ω U U + Op.gardingγ * ‖(U : H1amb Ω) 0‖ ^ 2 := by
  set n0 : ℝ := ‖(U : H1amb Ω) 0‖ ^ 2 with hn0
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  set K : ℝ := (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) with hK
  -- principal-part lower bound from ellipticity
  have hA : Op.lam * S ≤ Op.toEllipticCoeff.bilin Ω U U := Op.toEllipticCoeff.bilin_self_ge U
  -- per-term Cauchy-Schwarz + Peter-Paul, written sign-free to avoid a sum-of-negations
  have hbound : ∀ i : Fin d, (0 : ℝ)
      ≤ (Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2 + Op.Bsup ^ 2 / (2 * Op.lam) * n0)
        + ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫ := by
    intro i
    have hcs : -⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫
        ≤ Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2 + Op.Bsup ^ 2 / (2 * Op.lam) * n0 := by
      calc -⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫
          ≤ |⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫| := neg_le_abs _
        _ ≤ ‖Op.bAct i ((U : H1amb Ω) i.succ)‖ * ‖(U : H1amb Ω) 0‖ := abs_real_inner_le_norm _ _
        _ ≤ Op.Bsup * ‖(U : H1amb Ω) i.succ‖ * ‖(U : H1amb Ω) 0‖ := by
            gcongr; exact Op.norm_bAct_le i _
        _ ≤ Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2 + Op.Bsup ^ 2 / (2 * Op.lam) * n0 := by
            rw [hn0]; exact young_peterPaul Op.lam_pos
    linarith [hcs]
  -- transport lower bound: `∑ ⟪bᵢ ∂ᵢu, u₀⟫ ≥ -(λ/2 S + K n0)`
  have hT : (0 : ℝ) ≤ (Op.lam / 2 * S + K * n0)
      + ∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫ := by
    calc (0 : ℝ) = ∑ _i : Fin d, (0 : ℝ) := by rw [Finset.sum_const_zero]
      _ ≤ ∑ i : Fin d, ((Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2
            + Op.Bsup ^ 2 / (2 * Op.lam) * n0)
            + ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫) :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = (Op.lam / 2 * S + K * n0)
            + ∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hK, hS]
          ring
  -- zeroth-order lower bound (|c| ≤ Csup, no sign assumed)
  have hC : -(Op.Csup * n0) ≤ ⟪Op.cAct ((U : H1amb Ω) 0), ((U : H1amb Ω) 0)⟫ := by
    rw [neg_le]
    calc -⟪Op.cAct ((U : H1amb Ω) 0), ((U : H1amb Ω) 0)⟫
        ≤ |⟪Op.cAct ((U : H1amb Ω) 0), ((U : H1amb Ω) 0)⟫| := neg_le_abs _
      _ ≤ ‖Op.cAct ((U : H1amb Ω) 0)‖ * ‖(U : H1amb Ω) 0‖ := abs_real_inner_le_norm _ _
      _ ≤ Op.Csup * n0 := by
          rw [hn0]
          calc ‖Op.cAct ((U : H1amb Ω) 0)‖ * ‖(U : H1amb Ω) 0‖
              ≤ (Op.Csup * ‖(U : H1amb Ω) 0‖) * ‖(U : H1amb Ω) 0‖ :=
                mul_le_mul_of_nonneg_right (Op.norm_cAct_le _) (norm_nonneg _)
            _ = Op.Csup * ‖(U : H1amb Ω) 0‖ ^ 2 := by ring
  -- the H¹ norm splits as n0 + S
  have hnorm : ‖U‖ ^ 2 = n0 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, hn0, hS]
  rw [Op.fullBilin_apply, Op.lowerBilin_apply, gardingγ, ← hK, hnorm]
  linarith [hA, hT, hC]

/-! ### Shifted coercivity and existence (Evans §6.2.2, Theorem 3) -/

/-- The zeroth `L²` form `⟪u₀, v₀⟫` on `H₀¹(Ω)`, used for the spectral shift. -/
def zerothForm (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun U V : H01 Ω => ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_left])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_left,
          smul_eq_mul])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_right])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_right,
          smul_eq_mul])).mkContinuous₂ 1 (by
    intro U V
    simp only [LinearMap.mk₂_apply]
    calc ‖⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫‖
        ≤ ‖(U : H1amb Ω) 0‖ * ‖(V : H1amb Ω) 0‖ := norm_inner_le_norm _ _
      _ ≤ ‖U‖ * ‖V‖ := mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
          (norm_nonneg _) (norm_nonneg _)
      _ = 1 * ‖U‖ * ‖V‖ := by ring)

/-- Simp lemma: `zerothForm Ω U V = ⟪(U : H1amb Ω) 0, (V : H1amb Ω) 0⟫`. -/
@[simp] lemma zerothForm_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    zerothForm Ω U V = ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.zerothForm, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]

/-- The shifted bilinear form `B_μ[U, V] = B[U, V] + μ ⟪u₀, v₀⟫` associated to `Lu + μu`. -/
def shiftedBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  Op.fullBilin Ω + μ • zerothForm Ω

/-- `shiftedBilin Ω μ U V = fullBilin Ω U V + μ · ⟪u₀, v₀⟫`. -/
lemma shiftedBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (U V : H01 Ω) :
    Op.shiftedBilin Ω μ U V = Op.fullBilin Ω U V + μ * ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.shiftedBilin, _root_.add_apply,
    _root_.smul_apply, zerothForm_apply, smul_eq_mul]

/-- **Shifted coercivity** (Evans §6.2.2, Theorem 3). For any shift `μ ≥ γ`, the shifted
form `B_μ` is
coercive with constant `λ/2`. The Gårding inequality already controls the full `H¹` norm,
so no Poincaré inequality is needed. -/
theorem shiftedBilin_coercive (Ω : Set (EuclideanSpace ℝ (Fin d))) {μ : ℝ}
    (hμ : Op.gardingγ ≤ μ) :
    IsCoercive (Op.shiftedBilin Ω μ) := by
  refine ⟨Op.lam / 2, by have := Op.lam_pos; linarith, ?_⟩
  intro U
  have hg := Op.garding Ω U
  have hn0 : (0 : ℝ) ≤ ‖(U : H1amb Ω) 0‖ ^ 2 := sq_nonneg _
  have hself : ⟪(U : H1amb Ω) 0, ((U : H1amb Ω) 0)⟫ = ‖(U : H1amb Ω) 0‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  rw [Op.shiftedBilin_apply, hself]
  have hμn : Op.gardingγ * ‖(U : H1amb Ω) 0‖ ^ 2 ≤ μ * ‖(U : H1amb Ω) 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hμ hn0
  have : Op.lam / 2 * ‖U‖ ^ 2 ≤ Op.fullBilin Ω U U + μ * ‖(U : H1amb Ω) 0‖ ^ 2 := by
    linarith [hg, hμn]
  calc Op.lam / 2 * ‖U‖ * ‖U‖ = Op.lam / 2 * ‖U‖ ^ 2 := by ring
    _ ≤ Op.fullBilin Ω U U + μ * ‖(U : H1amb Ω) 0‖ ^ 2 := this

/-- **Existence and uniqueness for `Lu + μu = f`** (Evans §6.2.2, Theorem 3). For a
shift `μ ≥ γ` and
any continuous functional `f` on `H₀¹(Ω)`, there is a unique `u ∈ H₀¹(Ω)` solving the shifted
weak problem `B_μ[u, v] = f v` for all `v`. -/
theorem weak_solution (Ω : Set (EuclideanSpace ℝ (Fin d))) {μ : ℝ}
    (hμ : Op.gardingγ ≤ μ) (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.shiftedBilin Ω μ u v = f v :=
  EllipticPdes.lax_milgram (Op.shiftedBilin_coercive Ω hμ) f

/-! ### Transport-free, nonnegative-zeroth coercive case (Evans §6.2.2, closing
Examples remark)
-/

/-- **Nonnegativity of the lower-order form** when the transport field vanishes (`b = 0`
a.e. on `Ω`) and the zeroth coefficient is nonnegative (`c ≥ 0` a.e. on `Ω`): the
transport terms `⟪bᵢ ∂ᵢu, u₀⟫` are zero and `⟪c u₀, u₀⟫ = ∫_Ω c u₀² ≥ 0`. -/
lemma lowerBilin_self_nonneg (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (U : H01 Ω) :
    0 ≤ Op.lowerBilin Ω U U := by
  rw [Op.lowerBilin_apply]
  have htrans : (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp only [FullEllipticOp.bAct]
    rw [inner_mulCoeffL_eq]
    have hzero : ∀ᵐ x ∂(volume.restrict Ω),
        Op.b x i * ((U : H1amb Ω) i.succ x : ℝ) * ((U : H1amb Ω) 0 x : ℝ) = 0 :=
      (hb i).mono fun x hx => by rw [hx, zero_mul, zero_mul]
    calc (∫ x in Ω, Op.b x i * ((U : H1amb Ω) i.succ x : ℝ) * ((U : H1amb Ω) 0 x : ℝ))
        = ∫ _x in Ω, (0 : ℝ) := integral_congr_ae hzero
      _ = 0 := integral_zero _ _
  rw [htrans, zero_add]
  simp only [FullEllipticOp.cAct]
  rw [inner_mulCoeffL_eq]
  refine integral_nonneg_of_ae (hc.mono fun x hx => ?_)
  simp only [Pi.zero_apply]
  nlinarith [hx, sq_nonneg ((U : H1amb Ω) 0 x : ℝ)]

/-- **Quantitative coercivity for the transport-free, nonnegative-zeroth case**
(Evans §6.2.2, closing Examples remark). If the transport field vanishes (`b ≡ 0`) and
the zeroth coefficient is
nonnegative (`c ≥ 0`), the full divergence form `B = B_A + c` dominates the full `H¹`
norm with the explicit constant `λ / (C_P + 1)`: the zeroth term only helps, ellipticity
controls the gradient, and the Poincaré inequality lifts that to the full `H¹` norm.
This is the constant-level form of [`fullBilin_coercive_of_nonneg_zeroth`]; the explicit
constant feeds the Lax-Milgram a-priori estimate. -/
theorem fullBilin_coercive_const_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (U : H01 Ω) :
    Op.lam / (CP + 1) * ‖U‖ * ‖U‖ ≤ Op.fullBilin Ω U U := by
  have hpos : (0 : ℝ) < CP + 1 := by linarith
  have hne : (CP : ℝ) + 1 ≠ 0 := hpos.ne'
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  have hA : Op.lam * S ≤ Op.toEllipticCoeff.bilin Ω U U := Op.toEllipticCoeff.bilin_self_ge U
  have hlow : 0 ≤ Op.lowerBilin Ω U U := Op.lowerBilin_self_nonneg Ω hb hc U
  have hBUU : Op.lam * S ≤ Op.fullBilin Ω U U := by
    rw [Op.fullBilin_apply]; linarith
  have hnorm : ‖U‖ ^ 2 = ‖(U : H1amb Ω) 0‖ ^ 2 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  have hpoin : ‖(U : H1amb Ω) 0‖ ^ 2 ≤ CP * S :=
    EllipticPdes.Poincare.poincare_H01 CP hbase U.2
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * S := by
    have : ‖U‖ ^ 2 ≤ (CP + 1) * S := by rw [hnorm]; nlinarith [hpoin]
    nlinarith [this]
  rw [mul_assoc]
  calc Op.lam / (CP + 1) * (‖U‖ * ‖U‖)
      ≤ Op.lam / (CP + 1) * ((CP + 1) * S) :=
        mul_le_mul_of_nonneg_left hkey (div_pos Op.lam_pos hpos).le
    _ = Op.lam * S := by field_simp
    _ ≤ Op.fullBilin Ω U U := hBUU

/-- **Coercivity for the transport-free, nonnegative-zeroth case** (Evans §6.2.2,
closing Examples remark). If the
transport field vanishes (`b ≡ 0`) and the zeroth coefficient is nonnegative (`c ≥ 0`), the
full divergence form `B = B_A + c` is coercive on `H₀¹(Ω)` *without a spectral shift*: the
zeroth term only helps, ellipticity controls the gradient, and the Poincaré inequality lifts
that to the full `H¹` norm (the `γ = 0` Gårding case, with constant `λ / (C_P + 1)`). -/
theorem fullBilin_coercive_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    IsCoercive (Op.fullBilin Ω) :=
  ⟨Op.lam / (CP + 1), div_pos Op.lam_pos (by linarith),
    Op.fullBilin_coercive_const_of_nonneg_zeroth Ω hb hc CP hCP hbase⟩

/-- **Existence and uniqueness for the transport-free, nonnegative-zeroth operator**
(the `γ = 0` specialisation of Evans's First Existence Theorem, §6.2.2). With `b ≡ 0`,
`c ≥ 0`, and the test-function Poincaré bound, the full
divergence form `B = B_A + c` is coercive with no spectral shift, so Lax-Milgram yields for
every continuous functional `f` on `H₀¹(Ω)` a unique weak solution `u` of `Lu = f`. This is
the existence theorem for `Lu = -Dⱼ(aᵢⱼ Dᵢu) + cu` with general uniformly elliptic `A`. -/
theorem weak_solution_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v :=
  EllipticPdes.lax_milgram (Op.fullBilin_coercive_of_nonneg_zeroth Ω hb hc CP hCP hbase) f

/-- **A-priori estimate for the weak solution** (general uniformly elliptic operator,
`b ≡ 0`, `c ≥ 0`; the Lax-Milgram a-priori bound of Evans §6.2.1, Theorem 1). Under the
hypotheses of
[`weak_solution_of_nonneg_zeroth`], any weak solution obeys the Lax-Milgram estimate
`‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖` with the coercivity constant `α = λ / (C_P + 1)` of the form,
i.e. `‖u‖_{H₀¹} ≤ (C_P + 1) / λ · ‖f‖`. -/
theorem weak_solution_of_nonneg_zeroth_bound (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    {f : H01 Ω →L[ℝ] ℝ} {u : H01 Ω}
    (hu : ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) :
    ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := by
  have h := norm_weak_solution_le
    (div_pos Op.lam_pos (by linarith : (0 : ℝ) < CP + 1))
    (Op.fullBilin_coercive_const_of_nonneg_zeroth Ω hb hc CP hCP hbase) hu
  rwa [inv_div] at h

/-- **Unconditional existence, uniqueness, and a-priori bound on an open box, general
uniformly elliptic operator.** The box specialisation of `weak_solution_of_nonneg_zeroth`:
on the coordinate box `∏ₖ (aₖ, bₖ)`, with `b ≡ 0` and `c ≥ 0`, the test-function Poincaré
hypothesis is discharged from the box geometry. The per-direction slice bound
`Poincare.slice_bound_euclBox` (which rests on `Poincare.poincare_box_dir`) is averaged by
`Poincare.poincare_testfn` into the graph-coordinate bound with constant
`C_P = C / (n + 1)`, so for every continuous functional `f` on `H₀¹` of the box there is a
unique weak solution of `Lu = -Dⱼ(aᵢⱼ Dᵢu) + cu = f`, obeying the Lax-Milgram estimate
`‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖` with coercivity constant `α = λ / (C / (n + 1) + 1)`, with no
abstract Poincaré input. This is Theorem `thm: main` with an `H⁻¹` right-hand side; the
`L²` instance is [`weak_solution_L2_of_nonneg_zeroth_euclBox`]. -/
theorem weak_solution_of_nonneg_zeroth_euclBox {n : ℕ} (Op : FullEllipticOp (n + 1))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k) (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict (Poincare.euclBox a b)), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict (Poincare.euclBox a b)), 0 ≤ Op.c x)
    (f : H01 (Poincare.euclBox a b) →L[ℝ] ℝ) :
    (∃! u : H01 (Poincare.euclBox a b),
      ∀ v : H01 (Poincare.euclBox a b), Op.fullBilin (Poincare.euclBox a b) u v = f v)
    ∧ ∀ u : H01 (Poincare.euclBox a b),
        (∀ v : H01 (Poincare.euclBox a b), Op.fullBilin (Poincare.euclBox a b) u v = f v) →
          ‖u‖ ≤ (C / (n + 1) + 1) / Op.lam * ‖f‖ := by
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbase : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      (h : IsTestFn (Poincare.euclBox a b) φ),
      ‖(h.testGraph 0 : L2D (Poincare.euclBox a b))‖ ^ 2
        ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 :=
    fun {_φ} h => Poincare.testfn_bound_euclBox hab hC h
  have hCP : (0 : ℝ) ≤ C / (n + 1) := div_nonneg hCnonneg (by positivity)
  exact ⟨Op.weak_solution_of_nonneg_zeroth (Poincare.euclBox a b) hb hc _ hCP hbase f,
    fun u hu =>
      Op.weak_solution_of_nonneg_zeroth_bound (Poincare.euclBox a b) hb hc _ hCP hbase hu⟩

/-- **Theorem `thm: main`: existence, uniqueness, and the a-priori bound on an open box,
`L²` right-hand side.** For the general uniformly elliptic operator
`Lu = -Dⱼ(aᵢⱼ Dᵢu) + cu` with `c ≥ 0` on the coordinate box `∏ₖ (aₖ, bₖ)`, and for every
`f ∈ L²(Ω)` entering through the pairing `⟨f, v⟩ = ∫_Ω f · v₀` (the embedding
`L²(Ω) ⊆ H⁻¹(Ω)`, [`l2Functional`]), there is a unique weak solution `u ∈ H₀¹(Ω)` of
`B[u, v] = ⟨f, v⟩`, and every weak solution obeys `‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖_{L²}` with the
coercivity constant `α = λ / (C / (n + 1) + 1)` of the form. The Poincaré input is
discharged from the box geometry; no abstract hypothesis remains. -/
theorem weak_solution_L2_of_nonneg_zeroth_euclBox {n : ℕ} (Op : FullEllipticOp (n + 1))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k) (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict (Poincare.euclBox a b)), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict (Poincare.euclBox a b)), 0 ≤ Op.c x)
    (f : L2D (Poincare.euclBox a b)) :
    (∃! u : H01 (Poincare.euclBox a b),
      ∀ v : H01 (Poincare.euclBox a b),
        Op.fullBilin (Poincare.euclBox a b) u v
          = ∫ x in Poincare.euclBox a b,
              (f x : ℝ) * ((v : H1amb (Poincare.euclBox a b)) 0 x : ℝ))
    ∧ ∀ u : H01 (Poincare.euclBox a b),
        (∀ v : H01 (Poincare.euclBox a b),
          Op.fullBilin (Poincare.euclBox a b) u v
            = ∫ x in Poincare.euclBox a b,
                (f x : ℝ) * ((v : H1amb (Poincare.euclBox a b)) 0 x : ℝ)) →
          ‖u‖ ≤ (C / (n + 1) + 1) / Op.lam * ‖f‖ := by
  have h := Op.weak_solution_of_nonneg_zeroth_euclBox a b hab C hC hb hc
    (l2Functional (Poincare.euclBox a b) f)
  simp only [l2Functional_eq_integral] at h
  refine ⟨h.1, fun u hu => ?_⟩
  refine le_trans (h.2 u hu) ?_
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hCP : (0 : ℝ) ≤ C / (n + 1) := div_nonneg hCnonneg (by positivity)
  have hK : (0 : ℝ) ≤ (C / (n + 1) + 1) / Op.lam :=
    div_nonneg (by linarith) Op.lam_pos.le
  exact mul_le_mul_of_nonneg_left (norm_l2Functional_le _ f) hK

/-- **Existence, uniqueness, and the a-priori bound on any domain inside a coordinate
box, `H⁻¹` right-hand side.** For the uniformly elliptic operator
`Lu = -Dⱼ(aᵢⱼ Dᵢu) + cu` with `c ≥ 0` on a domain `Ω` contained in the open box
`∏ₖ (aₖ, bₖ)`, the test-function Poincaré hypothesis is discharged by
[`Poincare.testfn_bound_of_subset_euclBox`] from the geometry of the bounding box, with
side contributions `(bᵢ - aᵢ)² / 2 ≤ C`. Every continuous functional `f` on `H₀¹(Ω)`
admits a unique weak solution, obeying the Lax-Milgram estimate with coercivity
constant `α = λ / (C / (n + 1) + 1)`. The `L²` instance is
[`weak_solution_L2_of_nonneg_zeroth_of_subset_euclBox`]. -/
theorem weak_solution_of_nonneg_zeroth_of_subset_euclBox {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k) (hsub : Ω ⊆ Poincare.euclBox a b)
    (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (f : H01 Ω →L[ℝ] ℝ) :
    (∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
    ∧ ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = f v) →
        ‖u‖ ≤ (C / (n + 1) + 1) / Op.lam * ‖f‖ := by
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbase : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
        ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 :=
    fun {_φ} h => Poincare.testfn_bound_of_subset_euclBox hab hsub hC h
  have hCP : (0 : ℝ) ≤ C / (n + 1) := div_nonneg hCnonneg (by positivity)
  exact ⟨Op.weak_solution_of_nonneg_zeroth Ω hb hc _ hCP hbase f,
    fun u hu =>
      Op.weak_solution_of_nonneg_zeroth_bound Ω hb hc _ hCP hbase hu⟩

/-- **`L²` right-hand-side instance on any domain inside a coordinate box.** For
`f ∈ L²(Ω)` entering through the pairing `⟨f, v⟩ = ∫_Ω f · v₀` ([`l2Functional`]), the
weak problem has a unique solution with `‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖_{L²}`,
`α = λ / (C / (n + 1) + 1)`. Derived from
[`weak_solution_of_nonneg_zeroth_of_subset_euclBox`]. -/
theorem weak_solution_L2_of_nonneg_zeroth_of_subset_euclBox {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k) (hsub : Ω ⊆ Poincare.euclBox a b)
    (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (f : L2D Ω) :
    (∃! u : H01 Ω, ∀ v : H01 Ω,
      Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
    ∧ ∀ u : H01 Ω,
        (∀ v : H01 Ω,
          Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
          ‖u‖ ≤ (C / (n + 1) + 1) / Op.lam * ‖f‖ := by
  have h := Op.weak_solution_of_nonneg_zeroth_of_subset_euclBox a b hab hsub C hC hb hc
    (l2Functional Ω f)
  simp only [l2Functional_eq_integral] at h
  refine ⟨h.1, fun u hu => ?_⟩
  refine le_trans (h.2 u hu) ?_
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hCP : (0 : ℝ) ≤ C / (n + 1) := div_nonneg hCnonneg (by positivity)
  have hK : (0 : ℝ) ≤ (C / (n + 1) + 1) / Op.lam :=
    div_nonneg (by linarith) Op.lam_pos.le
  exact mul_le_mul_of_nonneg_left (norm_l2Functional_le _ f) hK

/-- **Existence, uniqueness, and the a-priori bound on an arbitrary bounded domain,
`L²` right-hand side** (Theorem `thm: main` in full generality). The Poincaré constant
`CP` is supplied by `poincare_H01_of_bounded` and is quantified before the datum, so it
depends only on `Ω`; every `f ∈ L²(Ω)` then obeys `‖u‖_{H₀¹} ≤ (CP + 1)/λ · ‖f‖_{L²}`.

Terminal result of the library, stated in the manuscript. Nothing else consumes it. -/
theorem weak_solution_L2_of_nonneg_zeroth_of_bounded {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ f : L2D Ω,
      ((∃! u : H01 Ω, ∀ v : H01 Ω,
        Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
      ∧ ∀ u : H01 Ω,
          (∀ v : H01 Ω,
            Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
            ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖) := by
  obtain ⟨CP, hCP, hpoin⟩ := Poincare.poincare_H01_of_bounded hΩb
  have hbase : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
        ≤ CP * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 :=
    fun {φ} h => hpoin h.testGraph
      ((Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ, h, rfl⟩))
  refine ⟨CP, hCP, fun f => ?_⟩
  have hexist := Op.weak_solution_of_nonneg_zeroth Ω hb hc CP hCP hbase (l2Functional Ω f)
  simp only [l2Functional_eq_integral] at hexist
  refine ⟨hexist, fun u hu => ?_⟩
  -- Refold to `l2Functional` form: `_bound` expects the functional, while `hu` states the
  -- unfolded integral.
  have hhu : ∀ v : H01 Ω, Op.fullBilin Ω u v = l2Functional Ω f v := by
    intro v; rw [l2Functional_eq_integral]; exact hu v
  have hbound := Op.weak_solution_of_nonneg_zeroth_bound Ω hb hc CP hCP hbase hhu
  refine le_trans hbound ?_
  have hK : (0 : ℝ) ≤ (CP + 1) / Op.lam := div_nonneg (by linarith) Op.lam_pos.le
  exact mul_le_mul_of_nonneg_left (norm_l2Functional_le _ f) hK

end FullEllipticOp

end EllipticPdes.Sobolev
