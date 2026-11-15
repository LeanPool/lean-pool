/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.Lines
public import LeanPool.RoyStrongSix.Thm1.MultEst

/-!
# Analytic derivatives of `P(v₀, e^{v₁})` are the invariant derivations

For `P ∈ ℂ[X₁, …, X_{d₀}, Y₁, …, Y_{d₁}]` put `F_P(v) = P(v₀, e^{v₁})` on `ℂ^{d₀} × ℂ^{d₁}`
(`evalExp`).
Then `F_P` is analytic and

  `D^t F_P (v) (m₀, …, m_{t-1}) = F_{D_{m_{t-1}} ⋯ D_{m₀} P}(v)`        (`iteratedFDeriv_evalExp`),

where `D_w` is the invariant derivation of `MultEst.lean`. This is the bridge between the
analytic interpolation determinant (`InterpDet.lean`) and the algebraic vanishing condition in
`MultEst`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Function
open scoped ContDiff

namespace StrongSix.Thm1

variable {K : Type*} [Field K] {d0 d1 : ℕ}

/-! ### `D_w` is a derivation -/

theorem invDer_add (w : LieG K d0 d1) (P Q : MvPolynomial (Var d0 d1) K) :
    invDer w (P + Q) = invDer w P + invDer w Q := by
  simp only [invDer, map_add, smul_add, mul_add, Finset.sum_add_distrib]
  abel

theorem invDer_C (w : LieG K d0 d1) (a : K) : invDer w (C a) = 0 := by
  simp [invDer]

theorem invDer_mul (w : LieG K d0 d1) (P Q : MvPolynomial (Var d0 d1) K) :
    invDer w (P * Q) = invDer w P * Q + P * invDer w Q := by
  have hl : ∀ i, pderiv i (P * Q) = P * pderiv i Q + Q * pderiv i P := fun i => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  calc invDer w (P * Q)
      = ∑ i, (C (w.1 i) * pderiv (Sum.inl i) P * Q + P * (C (w.1 i) * pderiv (Sum.inl i) Q)) +
        ∑ j, (C (w.2 j) * (X (Sum.inr j) * pderiv (Sum.inr j) P) * Q +
          P * (C (w.2 j) * (X (Sum.inr j) * pderiv (Sum.inr j) Q))) := by
        simp only [invDer, hl, smul_eq_C_mul]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
    _ = invDer w P * Q + P * invDer w Q := by
        simp only [invDer, smul_eq_C_mul, Finset.sum_add_distrib, add_mul, mul_add, Finset.sum_mul,
          Finset.mul_sum]
        ring

theorem invDer_X_inl (w : LieG K d0 d1) (k : Fin d0) : invDer w (X (Sum.inl k)) = C (w.1 k) := by
  classical
  simp [invDer, pderiv_X, Pi.single_apply, smul_eq_C_mul]

theorem invDer_X_inr (w : LieG K d0 d1) (j : Fin d1) :
    invDer w (X (Sum.inr j)) = C (w.2 j) * X (Sum.inr j) := by
  classical
  simp [invDer, pderiv_X, Pi.single_apply, smul_eq_C_mul]

theorem invDers_cons (w : LieG K d0 d1) (l : List (LieG K d0 d1)) (P : MvPolynomial (Var d0 d1) K) :
    invDers (w :: l) P = invDer w (invDers l P) := rfl

theorem invDers_nil (P : MvPolynomial (Var d0 d1) K) : invDers [] P = P := rfl

/-- `D_w` commutes with a change of coefficients. -/
theorem map_invDer {L : Type*} [Field L] (φ : K →+* L) (w : LieG K d0 d1)
    (P : MvPolynomial (Var d0 d1) K) :
    map φ (invDer w P) = invDer (fun i => φ (w.1 i), fun j => φ (w.2 j)) (map φ P) := by
  simp [invDer, pderiv_map, smul_eq_C_mul, map_sum]

theorem map_invDers {L : Type*} [Field L] (φ : K →+* L) (l : List (LieG K d0 d1))
    (P : MvPolynomial (Var d0 d1) K) :
    map φ (invDers l P) =
      invDers (l.map fun w => (fun i => φ (w.1 i), fun j => φ (w.2 j))) (map φ P) := by
  induction l with
  | nil => rfl
  | cons w l ih => rw [invDers_cons, map_invDer, ih]; rfl

/-! ### The analytic function `F_P` -/

/-- `exp_G(v) = (v₀, e^{v₁})` as a valuation of the variables. -/
noncomputable def expCoords (v : LieG ℂ d0 d1) : Var d0 d1 → ℂ :=
  Sum.elim v.1 fun j => Complex.exp (v.2 j)

/-- `F_P(v) = P(v₀, e^{v₁})`. -/
noncomputable def evalExp (P : MvPolynomial (Var d0 d1) ℂ) (v : LieG ℂ d0 d1) : ℂ :=
  eval (expCoords v) P

theorem contDiff_coord (v : Var d0 d1) : ContDiff ℂ ω (fun u : LieG ℂ d0 d1 => expCoords u v) := by
  cases v with
  | inl k => simp only [expCoords, Sum.elim_inl]; fun_prop
  | inr j => simp only [expCoords, Sum.elim_inr]; fun_prop

theorem contDiff_evalExp (P : MvPolynomial (Var d0 d1) ℂ) : ContDiff ℂ ω (evalExp P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    change ContDiff ℂ ω (fun u => eval (expCoords u) (C a))
    simp only [eval_C]; exact contDiff_const
  | add p q hp hq =>
    change ContDiff ℂ ω (fun u => eval (expCoords u) (p + q))
    simp only [map_add]; exact hp.add hq
  | mul_X p v hp =>
    change ContDiff ℂ ω (fun u => eval (expCoords u) (p * X v))
    simp only [map_mul, eval_X]; exact hp.mul (contDiff_coord v)

/-- Derivative along a line. -/
theorem hasDerivAt_evalExp_line (P : MvPolynomial (Var d0 d1) ℂ) (v w : LieG ℂ d0 d1) (t : ℂ) :
    HasDerivAt (fun t : ℂ => evalExp P (v + t • w)) (evalExp (invDer w P) (v + t • w)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    change HasDerivAt (fun t : ℂ => eval (expCoords (v + t • w)) (C a))
      (eval (expCoords (v + t • w)) (invDer w (C a))) t
    simp only [eval_C, invDer_C, map_zero]; exact hasDerivAt_const t a
  | add p q hp hq =>
    change HasDerivAt (fun t : ℂ => eval (expCoords (v + t • w)) (p + q))
      (eval (expCoords (v + t • w)) (invDer w (p + q))) t
    rw [invDer_add]; simp only [map_add]; exact hp.add hq
  | mul_X p u hp =>
    change HasDerivAt (fun t : ℂ => eval (expCoords (v + t • w)) (p * X u))
      (eval (expCoords (v + t • w)) (invDer w (p * X u))) t
    rw [invDer_mul]
    have hc : HasDerivAt (fun t : ℂ => expCoords (v + t • w) u)
        (eval (expCoords (v + t • w)) (invDer w (X u))) t := by
      cases u with
      | inl k =>
        simp only [expCoords, Sum.elim_inl, invDer_X_inl, eval_C, Prod.fst_add, Prod.smul_fst,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        simpa using ((hasDerivAt_id t).mul_const (w.1 k)).const_add (v.1 k)
      | inr j =>
        simp only [expCoords, Sum.elim_inr, invDer_X_inr, eval_mul, eval_C, eval_X, Prod.snd_add,
          Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := (((hasDerivAt_id t).mul_const (w.2 j)).const_add (v.2 j)).cexp
        simpa [mul_comm] using this
    simp only [map_add, map_mul, eval_X]
    exact hp.mul hc

/-- **One derivative.** `D F_P (v) (w) = F_{D_w P}(v)`. -/
theorem fderiv_evalExp (P : MvPolynomial (Var d0 d1) ℂ) (v w : LieG ℂ d0 d1) :
    fderiv ℂ (evalExp P) v w = evalExp (invDer w P) v := by
  have hd : DifferentiableAt ℂ (evalExp P) v :=
    ((contDiff_evalExp P).differentiable (by simp)) v
  have hline : HasDerivAt (fun t : ℂ => v + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add v
  have hd' : HasFDerivAt (evalExp P) (fderiv ℂ (evalExp P) v) (v + (0 : ℂ) • w) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℂ) hline
  have h2 := hasDerivAt_evalExp_line P v w 0
  have := h1.unique h2
  rw [this]; simp

/-- **The comparison lemma.** -/
theorem iteratedFDeriv_evalExp (P : MvPolynomial (Var d0 d1) ℂ) (t : ℕ) (v : LieG ℂ d0 d1)
    (m : Fin t → LieG ℂ d0 d1) :
    iteratedFDeriv ℂ t (evalExp P) v m = evalExp (invDers (List.ofFn m).reverse P) v := by
  induction t generalizing v with
  | zero => simp [invDers_nil]
  | succ t ih =>
    rw [peel (contDiff_evalExp P)]
    have hfun : (fun y => iteratedFDeriv ℂ t (evalExp P) y (Fin.init m)) =
        evalExp (invDers (List.ofFn (Fin.init m)).reverse P) := funext fun y => ih y (Fin.init m)
    rw [hfun, fderiv_evalExp, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    rfl

/-- The comparison lemma, pulled back along a linear map `ι : ℂ^n → ℂ^{d₀} × ℂ^{d₁}`. -/
theorem iteratedFDeriv_evalExp_comp {n : ℕ} (P : MvPolynomial (Var d0 d1) ℂ)
    (ι : (Fin n → ℂ) →L[ℂ] LieG ℂ d0 d1) (t : ℕ) (x : Fin n → ℂ) (m : Fin t → Fin n → ℂ) :
    iteratedFDeriv ℂ t (evalExp P ∘ ι) x m =
      evalExp (invDers (List.ofFn fun a => ι (m a)).reverse P) (ι x) := by
  rw [ι.iteratedFDeriv_comp_right (contDiff_evalExp P) x (by exact_mod_cast le_top)]
  exact iteratedFDeriv_evalExp P t (ι x) _

theorem contDiff_evalExp_comp {n : ℕ} (P : MvPolynomial (Var d0 d1) ℂ)
    (ι : (Fin n → ℂ) →L[ℂ] LieG ℂ d0 d1) : ContDiff ℂ ω (evalExp P ∘ ι) :=
  (contDiff_evalExp P).comp ι.contDiff

end StrongSix.Thm1

end LeanPool
