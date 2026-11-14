/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.Superdiffusion.Support.Book.Ch02.Theorems.Quadraticity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity

/-!
# LambdaShaking

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The shaking-lambda source estimate `e.shaking.lambda`

This module proves the source estimate `e.shaking.lambda`: for every bounded
Lipschitz domain `U`, every coefficient field `a`, every `p, q` and every
`lambda > 0`,

This is the missing input of `Mesoscale.LoadNormalization`, whose
`le_of_shaking_lambda_bound` consumes exactly the right-hand side above with
`lam = mu`.

## Route

The source proof combines `e.homogeneity.in.a` + `e.homogeneous.J` (scaling the
coefficient field), `e.J.magic.squares` (the completed-square rearrangement of
`J` in terms of `sigma`, `sigma_*`, `k`), `e.ksym.by.sss` (nonnegativity of the
`p`-only part of the magic-squares formula) and Young's inequality with a free
parameter `eps`, optimized at the end.

Neither `e.homogeneity.in.a` nor the literal magic-squares identity is
available as a Lean statement at the `Domain`/`CoeffOn` level of the frozen
sensitivity anchors: CoarseGraining's coefficient-field homogeneity lives on
the `Set`-based `CoarseGraining.ResponseJ` layer
(`responseJ_homogeneous_coeffField`), and there is no `Book.Ch02` declaration
for `e.J.magic.squares`.  Both are replaced here by an equivalent and strictly
cheaper route through the *unconditional* Chapter 2 coarse-matrix formula
`responseJ_eq_coarseMatrices_formula_canonical`:

* `responseJ_smul` (quadraticity, unconditional) replaces `e.homogeneity.in.a`
  and `e.homogeneous.J`: it gives the exact identity
  `J(U, lam^{-1/2} p, lam^{1/2} q) = lam^{-1} J(U, p, lam q)`.
* The coarse-matrix formula gives the *quadratic expansion in the `q`-slot*
  (`responseJ_smul_right_eq` below):
  `J(U,p,t q) = J(U,0,q) t^2 + (J(U,p,q) - J(U,p,0) - J(U,0,q)) t + J(U,p,0)`.
  This is `e.J.magic.squares` in coordinates: the magic-squares formula says
  exactly that this quadratic is a nonnegative constant plus a
  `sigma_*^{-1}`-square, i.e. that its discriminant is nonpositive.
* `responseJ_nonneg` (unconditional) applied along the whole line `t` gives the
  discriminant inequality `sq_mixed_le`.  This replaces `e.ksym.by.sss`: the
  source uses `e.ksym.by.sss` only to know that the `p`-only part of the
  magic-squares formula is nonnegative, which is the same statement as
  nonnegativity of `J` at the minimizing `q`.
* The discriminant inequality is exactly what Young + optimization in `eps`
  produce, so the closed (optimized) form is obtained directly and the
  `eps`-form is recovered from it by Young's inequality.

Nothing in this module is conditional: every hypothesis is a source binder
(`0 < lam`, and `0 < eps` for the pre-optimization form).

## What is here

* `responseJ_smul_right_eq`, `sq_mixed_le`, `responseJ_smul_right_le` — private
  helpers (the quadratic expansion, its discriminant, and the resulting
  one-parameter estimate).
* `responseJ_shaking_lambda` — the source estimate at a general domain, in the
  exact shape consumed by `Mesoscale.LoadNormalization.le_of_shaking_lambda_bound`.
* `responseJ_shaking_lambda_epsilon` — the pre-optimization `eps`-form.
* `responseJ_shaking_lambda_normalizedLoading`,
  `responseJ_shaking_lambda_normalizedLoading_epsilon` — the same two estimates
  read at the frozen loading `((mu sigma0)^{-1/2} e, (mu sigma0)^{1/2} e)`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Shaking

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The quadratic expansion of `J` in the flux slot -/

/-- **`e.J.magic.squares` in coordinates.**  For fixed `p` and `q`, the map
`t ↦ J(U, p, t q)` is the quadratic polynomial with leading coefficient
`J(U,0,q)`, constant term `J(U,p,0)` and linear coefficient the polarization
defect `J(U,p,q) - J(U,p,0) - J(U,0,q)`.

This is an unconditional consequence of the Chapter 2 coarse-matrix formula. -/
private theorem responseJ_smul_right_eq (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (t : ℝ) :
    responseJ U a p (t • q) =
      responseJ U a 0 q * t ^ 2 +
        (responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q) * t +
        responseJ U a p 0 := by
  have hcomm :=
    vecDot_matVecMul_comm_of_isSymm (sigmaStarInvCoarse_isSymm U a) q
      (matVecMul (Ch02.kappaCoarse U a) p)
  rw [responseJ_eq_coarseMatrices_formula_canonical U a p (t • q),
    responseJ_eq_coarseMatrices_formula_canonical U a p q,
    responseJ_eq_coarseMatrices_formula_canonical U a p 0,
    responseJ_eq_coarseMatrices_formula_canonical U a 0 q]
  simp only [matVecMul_zero, vecDot_zero_left, vecDot_zero_right, add_zero,
    zero_add, matVecMul_add, matVecMul_smul, vecDot_add_left, vecDot_add_right,
    vecDot_smul_left, vecDot_smul_right]
  rw [hcomm]
  ring

/-- **The discriminant inequality.**  The quadratic `t ↦ J(U,p,t q)` is
nonnegative on all of `ℝ`, so its discriminant is nonpositive.

This is the role played by `e.ksym.by.sss` in the source proof: it is the exact
statement that the `p`-only part of the magic-squares formula is nonnegative. -/
private theorem sq_mixed_le (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    (responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q) ^ 2 ≤
      4 * (responseJ U a 0 q * responseJ U a p 0) := by
  have hquad : ∀ t : ℝ,
      0 ≤ responseJ U a 0 q * (t * t) +
        (responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q) * t +
        responseJ U a p 0 := by
    intro t
    calc (0 : ℝ) ≤ responseJ U a p (t • q) := responseJ_nonneg U a p (t • q)
      _ = responseJ U a 0 q * t ^ 2 +
            (responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q) * t +
            responseJ U a p 0 := responseJ_smul_right_eq U a p q t
      _ = responseJ U a 0 q * (t * t) +
            (responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q) * t +
            responseJ U a p 0 := by ring
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

/-! ## The one-parameter estimate -/

/-- The shaking estimate before the change of variables: for every `lam`,
`J(U,p,lam q) <= (J(U,p,q)^{1/2} + |lam - 1| J(U,0,q)^{1/2})^2`. -/
private theorem responseJ_smul_right_le (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (lam : ℝ) :
    responseJ U a p (lam • q) ≤
      (Real.sqrt (responseJ U a p q) +
        |lam - 1| * Real.sqrt (responseJ U a 0 q)) ^ 2 := by
  have hA : 0 ≤ responseJ U a 0 q := responseJ_nonneg U a 0 q
  have hC : 0 ≤ responseJ U a p 0 := responseJ_nonneg U a p 0
  have hJ : 0 ≤ responseJ U a p q := responseJ_nonneg U a p q
  have hdisc := sq_mixed_le U a p q
  set A := responseJ U a 0 q with hAdef
  set C := responseJ U a p 0 with hCdef
  set J := responseJ U a p q with hJdef
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ
  have hkey : |A + J - C| ≤ 2 * (Real.sqrt A * Real.sqrt J) := by
    have hnn : (0 : ℝ) ≤ 2 * (Real.sqrt A * Real.sqrt J) := by positivity
    have hsq : (A + J - C) ^ 2 ≤ (2 * (Real.sqrt A * Real.sqrt J)) ^ 2 := by
      have hexp : (2 * (Real.sqrt A * Real.sqrt J)) ^ 2 = 4 * (A * J) := by
        rw [mul_pow, mul_pow, hsA, hsJ]; ring
      rw [hexp]
      nlinarith [hdisc]
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hnn] at this
  have habs : (lam - 1) * (A + J - C) ≤
      2 * (|lam - 1| * (Real.sqrt A * Real.sqrt J)) := by
    have h1 : (lam - 1) * (A + J - C) ≤ |lam - 1| * |A + J - C| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |lam - 1| * |A + J - C| ≤
        |lam - 1| * (2 * (Real.sqrt A * Real.sqrt J)) :=
      mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
    linarith
  have hexp : (Real.sqrt J + |lam - 1| * Real.sqrt A) ^ 2 =
      J + 2 * (|lam - 1| * (Real.sqrt A * Real.sqrt J)) + (lam - 1) ^ 2 * A := by
    have hring : (Real.sqrt J + |lam - 1| * Real.sqrt A) ^ 2 =
        Real.sqrt J ^ 2 + 2 * (|lam - 1| * (Real.sqrt A * Real.sqrt J)) +
          |lam - 1| ^ 2 * Real.sqrt A ^ 2 := by ring
    rw [hring, hsA, hsJ, sq_abs]
  rw [responseJ_smul_right_eq U a p q lam, hexp]
  nlinarith [habs]

/-! ## The source estimate -/

/-- **`e.shaking.lambda`** at a general bounded Lipschitz domain: for every `p,
q` and every `lam > 0`,

The right-hand side is written in exactly the shape consumed by the hypothesis
`hK` of `Mesoscale.LoadNormalization.le_of_shaking_lambda_bound`. -/
theorem responseJ_shaking_lambda (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    {lam : ℝ} (hlam : 0 < lam) :
    responseJ U a ((Real.sqrt lam)⁻¹ • p) (Real.sqrt lam • q) ≤
      lam⁻¹ *
        (Real.sqrt (responseJ U a p q) +
          Real.sqrt 2⁻¹ * |lam - 1| *
            Real.sqrt (vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q))) ^ 2 := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
  have hsmul : (Real.sqrt lam)⁻¹ • (lam • q) = Real.sqrt lam • q := by
    rw [smul_smul]
    congr 1
    field_simp
    linarith [hsq]
  have hscale : responseJ U a ((Real.sqrt lam)⁻¹ • p) (Real.sqrt lam • q) =
      lam⁻¹ * responseJ U a p (lam • q) := by
    have h := responseJ_smul (U := U) (a := a) (Real.sqrt lam)⁻¹ p (lam • q)
    rw [hsmul] at h
    rw [h, inv_pow, Real.sq_sqrt hlam.le]
  have hVe : Real.sqrt (responseJ U a 0 q) =
      Real.sqrt 2⁻¹ *
        Real.sqrt (vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q)) := by
    rw [responseJ_zero_q_eq_sigmaStarInvCoarse U a q,
      show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  rw [hscale]
  refine (mul_le_mul_of_nonneg_left (responseJ_smul_right_le U a p q lam)
    (inv_nonneg.mpr hlam.le)).trans_eq ?_
  rw [hVe]
  ring

/-- **The pre-optimization (`eps`) form of `e.shaking.lambda`**: for every `eps
> 0`,
  `J(U, lam^{-1/2} p, lam^{1/2} q; a)
     <= (1+eps)/lam J(U,p,q;a)
        + (1+eps)/(2 eps lam) (lam-1)^2 (q. sigma_*^{-1}(U;a) q)`.

The closed form `responseJ_shaking_lambda` is the optimization of this bound in
`eps`; it is proved first here and this display is recovered from it by Young's
inequality, so the two are equivalent. -/
theorem responseJ_shaking_lambda_epsilon (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) {lam eps : ℝ} (hlam : 0 < lam) (heps : 0 < eps) :
    responseJ U a ((Real.sqrt lam)⁻¹ • p) (Real.sqrt lam • q) ≤
      (1 + eps) / lam * responseJ U a p q +
        (1 + eps) / (2 * eps * lam) * (lam - 1) ^ 2 *
          vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q) := by
  have hJ : 0 ≤ responseJ U a p q := responseJ_nonneg U a p q
  have hV : 0 ≤ vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q) := by
    have h := responseJ_nonneg U a 0 q
    rw [responseJ_zero_q_eq_sigmaStarInvCoarse U a q] at h
    linarith
  have hclosed := responseJ_shaking_lambda U a p q hlam
  set V := vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q) with hVdef
  set x := Real.sqrt (responseJ U a p q) with hxdef
  set y := Real.sqrt 2⁻¹ * |lam - 1| * Real.sqrt V with hydef
  have hx : x ^ 2 = responseJ U a p q := Real.sq_sqrt hJ
  have hy : y ^ 2 = 2⁻¹ * (lam - 1) ^ 2 * V := by
    rw [hydef, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2⁻¹),
      sq_abs, Real.sq_sqrt hV]
  have hyoung : (x + y) ^ 2 ≤ (1 + eps) * x ^ 2 + (1 + eps) / eps * y ^ 2 := by
    have hne : eps ≠ 0 := ne_of_gt heps
    have hid : ((1 + eps) * x ^ 2 + (1 + eps) / eps * y ^ 2) - (x + y) ^ 2 =
        (eps * x - y) ^ 2 / eps := by
      field_simp
      ring
    have hpos : 0 ≤ (eps * x - y) ^ 2 / eps :=
      div_nonneg (sq_nonneg _) heps.le
    linarith
  refine hclosed.trans ?_
  refine (mul_le_mul_of_nonneg_left hyoung (inv_nonneg.mpr hlam.le)).trans_eq ?_
  rw [hx, hy]
  field_simp

/-! ## The frozen loading -/

/-- `(mu sigma0)^{-1/2} e = mu^{-1/2} (sigma0^{-1/2} e)`. -/
private theorem sqrt_mul_inv_smul_shaking {mu sigma0 : ℝ} (hmu : 0 ≤ mu)
    (e : Vec d) :
    (Real.sqrt (mu * sigma0))⁻¹ • e =
      (Real.sqrt mu)⁻¹ • ((Real.sqrt sigma0)⁻¹ • e) := by
  rw [Real.sqrt_mul hmu, mul_inv, smul_smul]

/-- `(mu sigma0)^{1/2} e = mu^{1/2} (sigma0^{1/2} e)`. -/
private theorem sqrt_mul_smul_shaking {mu sigma0 : ℝ} (hmu : 0 ≤ mu)
    (e : Vec d) :
    Real.sqrt (mu * sigma0) • e = Real.sqrt mu • (Real.sqrt sigma0 • e) := by
  rw [Real.sqrt_mul hmu, smul_smul]

/-- **`e.shaking.lambda` at the frozen loading.**  Reading
`responseJ_shaking_lambda` with `lam = mu`, `p = sigma0^{-1/2} e` and
`q = sigma0^{1/2} e`, the left-hand side is literally the loading
`((mu sigma0)^{-1/2} e, (mu sigma0)^{1/2} e)` of
`responseJ_sensitivity_unconditional`, and the right-hand side is exactly the
hypothesis `hK` of
`Mesoscale.LoadNormalization.le_of_shaking_lambda_bound` at
`K = J(U, (mu sigma0)^{-1/2} e, (mu sigma0)^{1/2} e)`,
`J = J(U, sigma0^{-1/2} e, sigma0^{1/2} e)` and
`V = (sigma0^{1/2} e) . sigma_*^{-1}(U;a) (sigma0^{1/2} e)`. -/
theorem responseJ_shaking_lambda_normalizedLoading (U : Domain d)
    (a : CoeffOn U) {mu sigma0 : ℝ} (hmu : 0 < mu) (e : Vec d) :
    responseJ U a ((Real.sqrt (mu * sigma0))⁻¹ • e)
        (Real.sqrt (mu * sigma0) • e) ≤
      mu⁻¹ *
        (Real.sqrt (responseJ U a ((Real.sqrt sigma0)⁻¹ • e)
            (Real.sqrt sigma0 • e)) +
          Real.sqrt 2⁻¹ * |mu - 1| *
            Real.sqrt (vecDot (Real.sqrt sigma0 • e)
              (matVecMul (Ch02.sigmaStarInvCoarse U a)
                (Real.sqrt sigma0 • e)))) ^ 2 := by
  rw [sqrt_mul_inv_smul_shaking hmu.le, sqrt_mul_smul_shaking hmu.le]
  exact responseJ_shaking_lambda U a ((Real.sqrt sigma0)⁻¹ • e)
    (Real.sqrt sigma0 • e) hmu

/-- The `eps`-form of `e.shaking.lambda` at the frozen loading. -/
theorem responseJ_shaking_lambda_normalizedLoading_epsilon (U : Domain d)
    (a : CoeffOn U) {mu sigma0 eps : ℝ} (hmu : 0 < mu) (heps : 0 < eps)
    (e : Vec d) :
    responseJ U a ((Real.sqrt (mu * sigma0))⁻¹ • e)
        (Real.sqrt (mu * sigma0) • e) ≤
      (1 + eps) / mu *
          responseJ U a ((Real.sqrt sigma0)⁻¹ • e) (Real.sqrt sigma0 • e) +
        (1 + eps) / (2 * eps * mu) * (mu - 1) ^ 2 *
          vecDot (Real.sqrt sigma0 • e)
            (matVecMul (Ch02.sigmaStarInvCoarse U a) (Real.sqrt sigma0 • e)) := by
  rw [sqrt_mul_inv_smul_shaking hmu.le, sqrt_mul_smul_shaking hmu.le]
  exact responseJ_shaking_lambda_epsilon U a ((Real.sqrt sigma0)⁻¹ • e)
    (Real.sqrt sigma0 • e) hmu heps

end

end Algsuperdiff.Section24.Sensitivity.Provider.Shaking

