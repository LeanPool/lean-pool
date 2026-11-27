/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Minors.Quasiaffine
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.ZeroSet
public import Mathlib.Data.Fin.Parity

/-!
# Minors of every order are null Lagrangians and quasiaffine

For a Lipschitz `φ : ℝ^m → ℝ^d` vanishing outside a bounded set `Ω`, every `A` and every minor (of
any order `k`), `∫_Ω minor (A + ∇φ) = |Ω| minor A` (`setIntegral_minor_add_grad`). This is (8.44) of
Theorem 8.35 of B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer,
2008 ([D08], p. 409–410; `Ω` open there), with its proof (part (i) of the proof in [D08]):

* (Theorem 8.33, p. 407–408) For smooth `u^1, …, u^s` and the directions `c_1, …, c_s`:
  `∑_t (−1)^{t+1} ∂_{c_t} (∂ (u^2, …, u^s) / ∂ (x_{c_1}, …, x̂_{c_t}, …, x_{c_s})) = 0`, (8.42), and
  `∂ (u^1, …, u^s) / ∂ (x_{c_1}, …, x_{c_s})` is
  `∑_t (−1)^{t+1} ∂_{c_t} (u^1 ∂ (u^2, …, u^s) / ∂ (x_{c_1}, …, x̂_{c_t}, …, x_{c_s}))`, (8.43).
  (8.43) follows from (8.42) (`nl_jac_eq_sum_D_of`): expand the Jacobian along its first row and use
  the product rule. (8.42) is proved by induction on the order (`nl_sum_D_jac_eq_zero`): (8.43), one
  order lower, for each of the Jacobians in (8.42) makes the sum a sum over `t ≠ α` of
  `± ∂_{c_t} ∂_{c_α} (u^2 ∂ (u^3, …, u^s) / ∂ (…))`, the last Jacobian without the directions `c_t`
  and `c_α`, and for `r < β` the terms `(t, α) = (r, β)` and `(β, r)` have opposite signs. In Lean
  `α` is given by its position among the indices different from `t` (`Fin.succAbove`), which
  contains the distinction between `α < t` and `α > t` of [D08]. [D08] states the theorem for `u` of
  class `C²`; for `s ≥ 3` the second derivatives in its proof are those of functions that are then
  only of class `C¹`. Here `u` is smooth, which is enough for Theorem 8.35.
* (Step 1, p. 409–410) `∫_Ω det (ξ + ∇ψ) = |Ω| det ξ`, (8.46), for smooth `ψ` with compact support
  in `Ω`, by induction on the order (`nl_setIntegral_det_add_smooth`). Expand the determinant along
  the first row (Proposition 5.65 of [D08]): the terms with the entries `ξ^1_t` integrate by the
  hypothesis of induction; the terms with `∂_{c_t} ψ^1` vanish, by integration by parts and (8.42)
  for the rows `ξ^i + ∇ψ^i`, `i ≥ 2`, which are gradients (`nl_setIntegral_D_mul_det_eq_zero`).
  [D08] reduces first to square matrices, `ψ : ℝ^s → ℝ^s` ("by abuse of notation", p. 409); here `ψ`
  is a map of `m` variables and `c_1, …, c_s` are `s` different directions, the form in which the
  step of the induction uses its hypothesis (minors of order `s − 1` of a map of `s` variables). The
  induction starts at the order `0` (in [D08], at `1`).
* (Step 2, p. 410, "by an elementary density argument", with no details) The identity passes to
  compactly supported Lipschitz maps by mollification (`nl_lipschitz_limit`;
  `nl_integral_minor_sub`, with Step 1 on a ball that contains the supports, since mollified maps
  need not have their support in `Ω`), and the gradient of `φ` vanishes almost everywhere outside
  `Ω` (`rd_ae_grad_eq_zero`).

The minors of orders `2` and `3` are treated with explicit formulas in `Minors.NullLagrangian` and
`Minors.Quasiaffine`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace CalculusOfVariations

variable {d m k : ℕ}

/-! ### Jacobians -/

/-- The Jacobian `∂ (v_1, …, v_k) / ∂ (x_{c_1}, …, x_{c_k}) = det [∂_{c_j} v_i]`. -/
noncomputable def nlJac (v : Fin k → (Fin m → ℝ) → ℝ) (c : Fin k → Fin m) (x : Fin m → ℝ) : ℝ :=
  (Matrix.of fun i j => nlD (c j) (v i) x).det

/-- A Jacobian of smooth functions is smooth. -/
theorem nl_contDiff_jac {v : Fin k → (Fin m → ℝ) → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (c : Fin k → Fin m) : ContDiff ℝ ∞ (nlJac v c) := by
  have e : nlJac v c = fun x => ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
      ∏ i, nlD (c i) (v (σ i)) x := by
    funext x
    rw [nlJac, Matrix.det_apply']
    rfl
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => nl_D_contDiff (hv _) _)

/-- `∂_a ∑ g_i = ∑ ∂_a g_i`. -/
theorem nl_D_sum {ι : Type*} (s : Finset ι) {g : ι → (Fin m → ℝ) → ℝ}
    (hg : ∀ i ∈ s, ContDiff ℝ ∞ (g i)) (a : Fin m) (x : Fin m → ℝ) :
    nlD a (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, nlD a (g i) x := by
  have h : HasFDerivAt (fun y => ∑ i ∈ s, g i y) (∑ i ∈ s, fderiv ℝ (g i) x) x :=
    HasFDerivAt.fun_sum fun i hi => (((hg i hi).differentiable (by simp)) x).hasFDerivAt
  simp only [nlD]
  rw [h.fderiv, sum_apply]

/-- `∂_a (b g) = b ∂_a g`. -/
theorem nl_D_const_mul {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (b : ℝ) (a : Fin m)
    (x : Fin m → ℝ) : nlD a (fun y => b * g y) x = b * nlD a g x := by
  have h := ((hg.differentiable (by simp)) x).hasFDerivAt.const_mul b
  simp only [nlD]
  rw [h.fderiv]
  simp [smul_eq_mul]

/-- The expansion of a Jacobian along its first row. -/
theorem nl_jac_succ (v : Fin (k + 1) → (Fin m → ℝ) → ℝ) (c : Fin (k + 1) → Fin m)
    (x : Fin m → ℝ) : nlJac v c x = ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (nlD (c t) (v 0) x *
      nlJac (fun i => v i.succ) (fun j => c (t.succAbove j)) x) := by
  rw [nlJac, Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]
  rfl

/-- (8.43) of [D08] follows from (8.42) for `u^2, …, u^s` (the hypothesis `h`; here `s = k + 1` and
`u = v`): expand along the first row and use the product rule. -/
theorem nl_jac_eq_sum_D_of {v : Fin (k + 1) → (Fin m → ℝ) → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (c : Fin (k + 1) → Fin m) (x : Fin m → ℝ)
    (h : ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) *
      nlD (c t) (nlJac (fun i => v i.succ) fun j => c (t.succAbove j)) x = 0) :
    nlJac v c x = ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * nlD (c t)
      (fun y => v 0 y * nlJac (fun i => v i.succ) (fun j => c (t.succAbove j)) y) x := by
  rw [nl_jac_succ, ← add_zero (∑ t : Fin (k + 1), _), ← mul_zero (v 0 x), ← h, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [nl_D_mul (hv 0) (nl_contDiff_jac (fun i => hv i.succ) _)]
  ring

/-- **Theorem 8.33 of [D08], (8.42)**, for smooth functions (`s = k + 1`, and `w_0, …, w_{k−1}` are
`u^2, …, u^s`): `∑_t (−1)^t ∂_{c_t} (∂ w / ∂ (x_{c_0}, …, x̂_{c_t}, …, x_{c_k})) = 0`. The proof is
that of [D08], by induction on the order: (8.43), one order lower, makes the sum
`∑_{t, α} ± ∂_{c_t} ∂_{c_α} (w_0 ∂ (w_1, …, w_{k−1}) / ∂ (…))`, where the terms `(r, β)` and
`(β, r)` cancel. -/
theorem nl_sum_D_jac_eq_zero {w : Fin k → (Fin m → ℝ) → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (c : Fin (k + 1) → Fin m) (x : Fin m → ℝ) :
    ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * nlD (c t) (nlJac w fun j => c (t.succAbove j)) x = 0 := by
  induction k generalizing x with
  | zero =>
    have h1 : ∀ c' : Fin 0 → Fin m, nlJac w c' = fun _ => 1 := fun c' => by
      funext y; simp [nlJac]
    simp [h1, nlD]
  | succ k ih =>
    -- the function under the second derivatives
    set G : Fin (k + 2) → Fin (k + 1) → (Fin m → ℝ) → ℝ := fun t α y =>
      w 0 y * nlJac (fun i => w i.succ) (fun j => c (t.succAbove (α.succAbove j))) y with hG
    have hGs : ∀ t α, ContDiff ℝ ∞ (G t α) := fun t α =>
      (hw 0).mul (nl_contDiff_jac (fun i => hw i.succ) _)
    -- the hypothesis of induction: (8.43) for the minors of order `k + 1`
    have hJ : ∀ t : Fin (k + 2), nlJac w (fun j => c (t.succAbove j)) = fun y =>
        ∑ α : Fin (k + 1), (-1) ^ (α : ℕ) * nlD (c (t.succAbove α)) (G t α) y := fun t =>
      funext fun y => nl_jac_eq_sum_D_of hw _ y
        (ih (fun i => hw i.succ) (fun j => c (t.succAbove j)) y)
    have hD : ∀ t : Fin (k + 2),
        (-1) ^ (t : ℕ) * nlD (c t) (nlJac w fun j => c (t.succAbove j)) x =
        ∑ α : Fin (k + 1), (-1) ^ (t + α : ℕ) * nlD (c t) (nlD (c (t.succAbove α)) (G t α)) x := by
      intro t
      rw [hJ t, nl_D_sum _ (fun α _ => contDiff_const.mul (nl_D_contDiff (hGs t α) _)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [nl_D_const_mul (nl_D_contDiff (hGs t α) _), pow_add, mul_assoc]
    simp_rw [hD]
    rw [← Finset.sum_product']
    -- the terms `(r, β)` and `(β, r)` cancel
    refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1))
      (fun p _ => ?_) (fun p _ _ => ?_) (fun _ _ => Finset.mem_univ _) (fun p _ => ?_)
    · obtain ⟨t, α⟩ := p
      have hGe : G (t.succAbove α) (α.predAbove t) = G t α := by
        simp only [hG, Fin.succAbove_succAbove_succAbove_predAbove]
      simp only [Fin.succAbove_succAbove_predAbove, hGe, Fin.neg_one_pow_succAbove_add_predAbove]
      rw [nl_D_comm (hGs t α) (c (t.succAbove α)) (c t)]
      ring
    · exact fun h => Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst h)
    · ext1
      · exact Fin.succAbove_succAbove_predAbove _ _
      · exact Fin.predAbove_predAbove_succAbove _ _

/-- **Theorem 8.33 of [D08], (8.43)**, for smooth functions: a Jacobian is a divergence. -/
theorem nl_jac_eq_sum_D {v : Fin (k + 1) → (Fin m → ℝ) → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (c : Fin (k + 1) → Fin m) (x : Fin m → ℝ) :
    nlJac v c x = ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * nlD (c t)
      (fun y => v 0 y * nlJac (fun i => v i.succ) (fun j => c (t.succAbove j)) y) x :=
  nl_jac_eq_sum_D_of hv c x (nl_sum_D_jac_eq_zero (fun i => hv i.succ) c x)

/-! ### The minors of `A + ∇φ` -/

/-- The linear function `y ↦ ∑_l a_l y_l` has the partial derivatives `a_b`. -/
theorem nl_D_linear (a : Fin m → ℝ) (b : Fin m) (x : Fin m → ℝ) :
    nlD b (fun y => ∑ l, a l * y l) x = a b := by
  have h : HasFDerivAt (fun y : Fin m → ℝ => ∑ l, a l * y l)
      (∑ l, a l • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) l) x :=
    HasFDerivAt.fun_sum fun l _ => (hasFDerivAt_apply l x).const_mul (a l)
  rw [nlD, h.fderiv]
  simp [Pi.single_apply]

/-- The second term in the proof of (8.46) of [D08]: for smooth `ψ_0, …, ψ_k`, `ψ_0` with compact
support in `Ω`, `∫_Ω ∑_t (−1)^t ∂_{c_t} ψ_0 · M_t = 0`, where `M_t` is the minor without the column
`t` of the `k × (k + 1)` matrix with the rows `X_i + ∇ψ_{i+1}`, `0 ≤ i < k`. These rows are the
gradients of the functions `w_i`, the sum of a linear function and `ψ_{i+1}`; integrate by parts,
and use (8.42) for the `w_i`. -/
theorem nl_setIntegral_D_mul_det_eq_zero {Ω : Set (Fin m → ℝ)}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ) {ψ : Fin (k + 1) → (Fin m → ℝ) → ℝ}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hc : HasCompactSupport (ψ 0)) (hΩ : tsupport (ψ 0) ⊆ Ω) (c : Fin (k + 1) ↪ Fin m) :
    ∫ x in Ω, ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (nlD (c t) (ψ 0) x *
      (Matrix.of fun i j => X i (t.succAbove j) +
        nlD (c (t.succAbove j)) (ψ i.succ) x).det) = 0 := by
  -- the rows `X_i + ∇ψ_i`, as gradients
  set w : Fin k → (Fin m → ℝ) → ℝ := fun i y =>
    (∑ l, (∑ j, if c j = l then X i j else 0) * y l) + ψ i.succ y with hw
  have hlin : ∀ i, ContDiff ℝ ∞ fun y : Fin m → ℝ =>
      ∑ l, (∑ j, if c j = l then X i j else 0) * y l := fun i =>
    ContDiff.sum fun l _ => contDiff_const.mul (by fun_prop)
  have hws : ∀ i, ContDiff ℝ ∞ (w i) := fun i => (hlin i).add (hψ i.succ)
  have hwD : ∀ i j x, nlD (c j) (w i) x = X i j + nlD (c j) (ψ i.succ) x := by
    intro i j x
    refine (congrFun (nl_D_add (hlin i) (hψ i.succ) (c j)) x).trans ?_
    rw [nl_D_linear]
    simp [c.injective.eq_iff]
  have hJ : ∀ (t : Fin (k + 1)) x, (Matrix.of fun i j => X i (t.succAbove j) +
      nlD (c (t.succAbove j)) (ψ i.succ) x).det = nlJac w (fun j => c (t.succAbove j)) x := by
    intro t x
    rw [nlJac]
    congr 1
    ext i j
    simp only [Matrix.of_apply, hwD]
  have hP : ∀ t : Fin (k + 1), ContDiff ℝ ∞ fun y =>
      ψ 0 y * nlJac w (fun j => c (t.succAbove j)) y := fun t =>
    (hψ 0).mul (nl_contDiff_jac hws _)
  have hPc : ∀ t : Fin (k + 1), HasCompactSupport fun y =>
      ψ 0 y * nlJac w (fun j => c (t.succAbove j)) y := fun t => hc.mul_right
  -- integration by parts, with (8.42)
  have hdiv : ∀ x, ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (nlD (c t) (ψ 0) x *
      (Matrix.of fun i j => X i (t.succAbove j) + nlD (c (t.succAbove j)) (ψ i.succ) x).det) =
      ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * nlD (c t)
        (fun y => ψ 0 y * nlJac w (fun j => c (t.succAbove j)) y) x := by
    intro x
    rw [← add_zero (∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (_ * Matrix.det _)), ← mul_zero (ψ 0 x),
      ← nl_sum_D_jac_eq_zero hws c x, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hJ, nl_D_mul (hψ 0) (nl_contDiff_jac hws _)]
    ring
  have hsupp : ∀ x ∉ Ω, ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * nlD (c t)
      (fun y => ψ 0 y * nlJac w (fun j => c (t.succAbove j)) y) x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun t _ => ?_
    have h0 : fderiv ℝ (fun y => ψ 0 y * nlJac w (fun j => c (t.succAbove j)) y) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (hΩ (tsupport_mul_subset_left
        (tsupport_fderiv_subset ℝ h)))
    rw [nlD, h0]
    simp
  simp_rw [hdiv]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_finsetSum _ fun t _ =>
    (nl_integrable_of_smooth (nl_D_contDiff (hP t) _)
      (nl_hasCompactSupport_D (hPc t) _)).const_mul _]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [integral_const_mul, nl_integral_D_eq_zero (hP t) (hPc t), mul_zero]

/-- A continuous function is integrable on a bounded set. -/
theorem nl_integrableOn_of_continuous {g : (Fin m → ℝ) → ℝ} (hg : Continuous g)
    {Ω : Set (Fin m → ℝ)} (hb : Bornology.IsBounded Ω) : IntegrableOn g Ω :=
  (hg.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

/-- **Step 1 of the proof of Theorem 8.35 (i) of [D08], (8.46)**: for a bounded `Ω`, a `k × k`
matrix `X` and smooth `ψ_i` with compact support in `Ω`, `∫_Ω det (X + [∂_{c_j} ψ_i]) = |Ω| det X`.
By induction on `k`: expand along the first row; the terms with the entries of `X` integrate by the
hypothesis of induction, the terms with `∂_{c_t} ψ_0` by `nl_setIntegral_D_mul_det_eq_zero`. -/
theorem nl_setIntegral_det_add_smooth {Ω : Set (Fin m → ℝ)} (hb : Bornology.IsBounded Ω)
    (X : Matrix (Fin k) (Fin k) ℝ) {ψ : Fin k → (Fin m → ℝ) → ℝ} (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hc : ∀ i, HasCompactSupport (ψ i)) (hΩ : ∀ i, tsupport (ψ i) ⊆ Ω) (c : Fin k ↪ Fin m) :
    ∫ x in Ω, (Matrix.of fun i j => X i j + nlD (c j) (ψ i) x).det =
      (volume Ω).toReal * X.det := by
  induction k with
  | zero => simp [Measure.real]
  | succ k ih =>
    -- the minors without the first row and the column `t`
    set D : Fin (k + 1) → (Fin m → ℝ) → ℝ := fun t x => (Matrix.of fun i j : Fin k =>
      X i.succ (t.succAbove j) + nlD (c (t.succAbove j)) (ψ i.succ) x).det with hD
    have hDc : ∀ t, Continuous (D t) := fun t =>
      Continuous.matrix_det (continuous_matrix fun i j => continuous_const.add
        (nl_D_contDiff (hψ i.succ) _).continuous)
    have hexp : ∀ x, (Matrix.of fun i j => X i j + nlD (c j) (ψ i) x).det =
        (∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (X 0 t * D t x)) +
          ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (nlD (c t) (ψ 0) x * D t x) := by
      intro x
      rw [Matrix.det_succ_row_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have e : (Matrix.of fun i j => X i j + nlD (c j) (ψ i) x).submatrix Fin.succ t.succAbove =
          Matrix.of fun i j : Fin k =>
            X i.succ (t.succAbove j) + nlD (c (t.succAbove j)) (ψ i.succ) x := rfl
      rw [e, Matrix.of_apply]
      simp only [hD]
      ring
    -- the first term, by the hypothesis of induction
    have h1 : ∫ x in Ω, ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (X 0 t * D t x) =
        (volume Ω).toReal * X.det := by
      rw [integral_finsetSum _ fun t _ => ((nl_integrableOn_of_continuous (hDc t) hb).const_mul
        _).const_mul _, Matrix.det_succ_row_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [integral_const_mul, integral_const_mul]
      have := ih (X.submatrix Fin.succ t.succAbove) (fun i => hψ i.succ) (fun i => hc i.succ)
        (fun i => hΩ i.succ) ((Fin.succAboveEmb t).trans c)
      simp only [hD]
      rw [show (∫ x in Ω, (Matrix.of fun i j : Fin k => X i.succ (t.succAbove j) +
        nlD (c (t.succAbove j)) (ψ i.succ) x).det) = _ from this]
      ring
    -- the second term, by integration by parts and (8.42)
    have h2 := nl_setIntegral_D_mul_det_eq_zero (X.submatrix Fin.succ id) hψ (hc 0) (hΩ 0) c
    simp_rw [hexp]
    rw [integral_add, h1]
    · rw [show (∫ x in Ω, ∑ t : Fin (k + 1), (-1) ^ (t : ℕ) * (nlD (c t) (ψ 0) x * D t x)) = 0
        from h2, add_zero]
    · exact integrable_finsetSum _ fun t _ => ((nl_integrableOn_of_continuous (hDc t) hb).const_mul
        _).const_mul _
    · exact integrable_finsetSum _ fun t _ => (nl_integrableOn_of_continuous
        ((nl_D_contDiff (hψ 0) _).continuous.mul (hDc t)) hb).const_mul _

/-- **Step 2 of the proof of Theorem 8.35 (i) of [D08]**, density: for a Lipschitz `φ` with compact
support, `∫ (minor (A + ∇φ) − minor A) = 0`, by Step 1 for its mollifications, on a ball that
contains their supports. -/
theorem nl_integral_minor_sub {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hc : HasCompactSupport φ) (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ∫ x, (minor (A + grad φ x) r c - minor A r c) = 0 := by
  have hcomp : ∀ i, HasCompactSupport fun y => φ y i := fun i =>
    hc.comp_left (g := fun z : Fin d → ℝ => z i) rfl
  have hF : Continuous fun G : Fin d → Fin m → ℝ =>
      minor (A + Matrix.of G) r c - minor A r c := by
    have : Continuous fun G : Fin d → Fin m → ℝ => (A + Matrix.of G).submatrix r c :=
      (continuous_const.add continuous_id).matrix_submatrix r c
    exact this.matrix_det.sub continuous_const
  refine nl_lipschitz_limit (fun i y => φ y i) (fun _ => K) (nl_lip_comp hφ) hcomp
    (fun G => minor (A + Matrix.of G) r c - minor A r c) hF (by simp) fun ψ hψ hψc => ?_
  -- Step 1 on a ball that contains the supports
  have hS : IsCompact (⋃ i, tsupport (ψ i)) := isCompact_iUnion hψc
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  have hb : Bornology.IsBounded (Metric.closedBall (0 : Fin m → ℝ) R) := Metric.isBounded_closedBall
  have hΩ : ∀ i, tsupport (ψ i) ⊆ Metric.closedBall 0 R := fun i =>
    (Set.subset_iUnion (fun i => tsupport (ψ i)) i).trans hR
  have h1 := nl_setIntegral_det_add_smooth hb (A.submatrix r c) (fun i => hψ (r i))
    (fun i => hψc (r i)) (fun i => hΩ (r i)) c.toEmbedding
  have hD0 : ∀ x ∉ Metric.closedBall (0 : Fin m → ℝ) R, ∀ i a, nlD a (ψ i) x = 0 := by
    intro x hx i a
    have h0 : fderiv ℝ (ψ i) x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hx (hΩ i (tsupport_fderiv_subset ℝ h))
    rw [nlD, h0]
    simp
  have hmin : ∀ x, minor (A + Matrix.of fun i a => nlD a (ψ i) x) r c =
      (Matrix.of fun i j => A.submatrix r c i j + nlD (c.toEmbedding j) (ψ (r i)) x).det :=
    fun x => rfl
  have hcont : Continuous fun x => minor (A + Matrix.of fun i a => nlD a (ψ i) x) r c :=
    ((continuous_const.add (continuous_matrix fun i a =>
      (nl_D_contDiff (hψ i) a).continuous)).matrix_submatrix r c).matrix_det
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : Fin m → ℝ) R)
    fun x hx => ?_, integral_sub (nl_integrableOn_of_continuous hcont hb)
    (integrableOn_const hb.measure_lt_top.ne eNorm_ne_top), setIntegral_const, smul_eq_mul]
  · simp_rw [hmin]
    rw [h1, Measure.real]
    exact sub_self _
  · rw [show (Matrix.of fun i a => nlD a (ψ i) x) = 0 from by
      ext i a; exact hD0 x hx i a, add_zero, sub_self]

/-- **Minors of every order are null Lagrangians** ([D08], Theorem 8.35, (8.44)): for a bounded `Ω`
and a Lipschitz `φ` vanishing outside `Ω`, `∫_Ω minor (A + ∇φ) = |Ω| minor A`. -/
theorem setIntegral_minor_add_grad {Ω : Set (Fin m → ℝ)} (hb : Bornology.IsBounded Ω)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ Ω, φ x = 0)
    (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    ∫ x in Ω, minor (A + grad φ x) r c = (volume Ω).toReal * minor A r c := by
  have hfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hcs : HasCompactSupport φ := by
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    exact HasCompactSupport.intro (isCompact_closedBall _ R) fun x hx => h0 x fun h => hx (hR h)
  have hcont : Continuous fun J : Matrix (Fin d) (Fin m) ℝ => minor J r c :=
    (continuous_id.matrix_submatrix r c).matrix_det
  have hI : IntegrableOn (fun x => minor (A + grad φ x) r c) Ω :=
    nl_integrableOn_cube hφ hcont A Ω hfin
  have h1 : ∫ x in Ω, (minor (A + grad φ x) r c - minor A r c) = 0 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero, nl_integral_minor_sub hφ hcs A r c]
    filter_upwards [rd_ae_grad_eq_zero hφ] with x hx hxΩ
    rw [hx (h0 x hxΩ), add_zero, sub_self]
  rw [integral_sub hI (integrableOn_const hfin eNorm_ne_top), setIntegral_const, smul_eq_mul,
    Measure.real] at h1
  linarith

end CalculusOfVariations
