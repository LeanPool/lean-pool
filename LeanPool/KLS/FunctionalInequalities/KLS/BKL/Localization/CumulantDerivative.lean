/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.LogPartition
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local

/-!
# Parameter derivatives of posterior cumulants

Posterior cumulants are jointly smooth in the parameters and `D_c κ_m(μ_p)(h)[v] = κ_{m+1}(μ_p)(h,
v)` (BKL (81)); covariance
entries are second cumulants.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.BKL.Localization

private theorem iteratedFDeriv_param_slice
    {n : ℕ} (ψ : Param n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ψ (y, Q)) c h =
      iteratedFDeriv ℝ m ψ (c, Q)
        (fun i => (h i, (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let K := E →L[ℝ] E
  let L : E →L[ℝ] E × K := ContinuousLinearMap.inl ℝ E K
  let a : E × K := (0, Q)
  let g : E × K → ℝ := fun z => ψ (z + a)
  have hg : ContDiff ℝ ∞ g := by
    exact hψ.comp
      (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ (fun _ : E × K => a)))
  have hm_top : (m : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr le_top
  have hcomp :=
    L.iteratedFDeriv_comp_right hg c (i := m) hm_top
  have hshift :
      iteratedFDeriv ℝ m g (L c) =
        iteratedFDeriv ℝ m ψ (L c + a) := by
    simpa [g] using
      (iteratedFDeriv_comp_add_right (𝕜 := ℝ) m a (L c))
  have hcomp' := congrArg (fun T => T h) hcomp
  rw [hshift] at hcomp'
  simpa [E, K, L, a, g, Function.comp_def,
    ContinuousLinearMap.inl_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hcomp'

private def snocToCons (m : ℕ) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.mk
    (Fin.cases (Fin.last m) (fun i => i.castSucc))
    (Fin.lastCases 0 (fun i => i.succ))
    (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp)
    (by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp)

private theorem iteratedFDeriv_cons_eq_snoc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {m : ℕ}
    (hf : ContDiff ℝ ∞ f) (h : Fin m → E) (v : E) :
    iteratedFDeriv ℝ (m + 1) f x (Fin.cons v h) =
      iteratedFDeriv ℝ (m + 1) f x (Fin.snoc h v) := by
  have hperm :
      (Fin.snoc h v) ∘ ⇑(snocToCons m) = Fin.cons v h := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [snocToCons]
    · simp [snocToCons]
  have hp :=
    FunctionalInequalities.Analysis.iteratedFDeriv_perm
      hf (m + 1) (Fin.snoc h v) (snocToCons m) x
  rw [hperm] at hp
  exact hp

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/--
**Joint smoothness of the posterior cumulants** in the parameter `p = (c, Q)`: for a compactly
supported
prior and `m ≥ 1`, `p ↦ κ_m(μ_p)(h)` is `C^∞` on the whole parameter space (BKL arXiv:2610.05474v1,
Section 4:
`κ_m = D_c^m ψ` with `ψ` jointly smooth). -/
theorem contDiff_cumulant_posterior {m : ℕ} (hm : 1 ≤ m)
    (h : Fin m → EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞
      (fun q : Param n =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) := by
  let ψ : Param n → ℝ := fun p => logPartition μ p.1 p.2
  let U : Fin m → Param n := fun i => (h i, 0)
  have hψ : ContDiff ℝ ∞ ψ := by simpa [ψ] using contDiff_logPartition_joint μ hc
  have hcum :
    (fun q : Param n =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) =
      (fun q : Param n => (iteratedFDeriv ℝ m ψ q) U) := by
    funext q
    calc
      cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h =
          iteratedFDeriv ℝ m (fun y => logPartition μ y q.2) q.1 h :=
        congrArg (fun T => T h) (cumulant_compactPosterior μ hc q.1 q.2 hm)
      _ = (iteratedFDeriv ℝ m ψ q) U := by
        simpa [ψ, U] using iteratedFDeriv_param_slice ψ hψ h q.1 q.2
  rw [hcum]
  have htop : (∞ : ℕ∞ω) + (m : ℕ∞ω) ≤ ∞ := by
    rw [← WithTop.coe_natCast m, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.mpr le_top
  have hΦ : ContDiff ℝ ∞ (fun p : Param n => iteratedFDeriv ℝ m ψ p) :=
    hψ.iteratedFDeriv_right (m := ∞) (i := m) htop
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Param n) ℝ U
  simpa [A, Function.comp_def] using A.contDiff.comp hΦ

/--
**The `c`-derivative of a cumulant is the next cumulant**: `D_c κ_m(h)[v] = κ_{m+1}(h, v)` (BKL p.
20,
`∇ᵐv_t(0) = κ_{m+1}`; the noise of (67) only moves `c`). -/
theorem fderiv_cumulant_posterior_apply {m : ℕ} (hm : 1 ≤ m)
    (h : Fin m → EuclideanSpace ℝ (Fin n)) (p : Param n) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ
        (fun q : Param n =>
          cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h)
        p (v, 0) =
      cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (m + 1)
        (Fin.snoc h v) := by
  let ψ : Param n → ℝ := fun q => logPartition μ q.1 q.2
  let U : Fin m → Param n := fun i => (h i, 0)
  have hψ : ContDiff ℝ ∞ ψ := by simpa [ψ] using contDiff_logPartition_joint μ hc
  have hcum :
    (fun q : Param n =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) =
      (fun q : Param n => (iteratedFDeriv ℝ m ψ q) U) := by
    funext q
    calc
      cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h =
          iteratedFDeriv ℝ m (fun y => logPartition μ y q.2) q.1 h :=
        congrArg (fun T => T h) (cumulant_compactPosterior μ hc q.1 q.2 hm)
      _ = (iteratedFDeriv ℝ m ψ q) U := by
        simpa [ψ, U] using iteratedFDeriv_param_slice ψ hψ h q.1 q.2
  rw [hcum]
  have hdiff : Differentiable ℝ (fun q : Param n => iteratedFDeriv ℝ m ψ q) :=
    hψ.differentiable_iteratedFDeriv (m := m) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))
  let w : Param n := (v, 0)
  let Ulast : Fin (m + 1) → Param n := Fin.snoc U w
  have hderiv :
    fderiv ℝ (fun q : Param n => (iteratedFDeriv ℝ m ψ q) U) p (v, 0) =
      iteratedFDeriv ℝ (m + 1) ψ p Ulast := by
    calc
      fderiv ℝ (fun q : Param n => (iteratedFDeriv ℝ m ψ q) U) p (v, 0) =
          (fderiv ℝ (fun q : Param n => iteratedFDeriv ℝ m ψ q) p (v, 0)) U :=
        fderiv_continuousMultilinear_apply_const_apply hdiff.differentiableAt U (v, 0)
      _ = iteratedFDeriv ℝ (m + 1) ψ p (Fin.cons w U) := by
        simpa [w] using
          (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := ψ) (x := p) (Fin.cons w U)).symm
      _ = iteratedFDeriv ℝ (m + 1) ψ p Ulast := iteratedFDeriv_cons_eq_snoc hψ U w
  rw [hderiv]
  let hv : Fin (m + 1) → EuclideanSpace ℝ (Fin n) := Fin.snoc h v
  have hU : (fun i : Fin (m + 1) => ((hv i, 0) : Param n)) = Ulast := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hv, Ulast, w]
    · simp [hv, Ulast, U]
  have hs := iteratedFDeriv_param_slice ψ hψ hv p.1 p.2
  rw [hU] at hs
  calc
    iteratedFDeriv ℝ (m + 1) ψ p Ulast =
        iteratedFDeriv ℝ (m + 1) (fun y => logPartition μ y p.2) p.1 (Fin.snoc h v) := by
      simpa [ψ, hv] using hs.symm
    _ =
        cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (m + 1)
          (Fin.snoc h v) := by
      have hcumulant :=
        cumulant_compactPosterior μ hc p.1 p.2 (hm := Nat.succ_le_succ (Nat.zero_le m))
      exact (congrArg (fun T => T (Fin.snoc h v)) hcumulant).symm

/-- The posterior covariance is the second cumulant: `⟪A(p) x, y⟫ = κ₂(μ_p)(x, y)`. -/
theorem inner_cov_apply (p : Param n) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪cov μ hc p x, y⟫ =
      cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 2 ![x, y] := by
  change
    ⟪Covariance.operator
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) x, y⟫ =
      cumulant (compactPosterior μ hc p.1 p.2 :
        Measure (EuclideanSpace ℝ (Fin n))) 2 ![x, y]
  have hcompact :
      IsCompact
        (compactPosterior μ hc p.1 p.2 :
          Measure (EuclideanSpace ℝ (Fin n))).support := by
    rw [compactPosterior_support μ hc p.1 p.2]
    exact hc
  exact
    (cumulant_two_eq_covariance_of_integrable_exp
      (μ := (compactPosterior μ hc p.1 p.2 :
        Measure (EuclideanSpace ℝ (Fin n))))
      (hr := one_pos)
      (compact_support_integrable_exp
        (compactPosterior μ hc p.1 p.2 :
          Measure (EuclideanSpace ℝ (Fin n))) hcompact 1)
      x y).symm

end FunctionalInequalities.KLS.BKL.Localization
