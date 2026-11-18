/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.List.FinRange

/-!
# Permutation symmetry of raw iterated derivatives of real `C^∞` maps

Generic calculus support for the cumulant algebra of Bizeul–Klartag–Lehec arXiv:2610.05474v1,
pp. 20–21 ((71)–(74)): for a globally `C^∞` map between real normed spaces, successive directional
derivatives along a list (`directional`, inherited order) commute under adjacent swaps by genuine
real `C²` symmetry, hence under every permutation, and the list convention is exactly the raw
iterated Fréchet derivative, so `iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h`. No
analytic, finite-dimensional, complete, Hilbert or measure premise; no tensor symmetry is assumed.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Successive directional derivatives in the inherited list order. -/
def directional : List E → (E → F) → E → F
  | [], f => f
  | h :: hs, f => fun x => fderiv ℝ (directional hs f) x h

theorem directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))

private theorem directional_two {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional [v, w] f x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const w)]
  simp

/-- Adjacent directional derivatives commute by genuine real C² symmetry. -/
theorem directional_swap {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) (v w : E) :
    directional (v :: w :: hs) f = directional (w :: v :: hs) f := by
  funext x
  have hg := directional_contDiff hf hs
  have he (u t : E) :
    directional (u :: t :: hs) f x = directional [u, t] (directional hs f) x := rfl
  rw [he, he, directional_two hg, directional_two hg]
  exact
    hg.contDiffAt.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
      v w

/-- Full permutation symmetry follows from adjacent swaps; no tensor symmetry is a premise. -/
theorem directional_perm {f : E → F} (hf : ContDiff ℝ ∞ f) {hs ks : List E}
    (h : hs.Perm ks) : directional hs f = directional ks f := by
  induction h with
  | nil => rfl
  | cons v h IH =>
    change (fun x => fderiv ℝ (directional _ f) x v) = (fun x => fderiv ℝ (directional _ f) x v)
    rw [IH]
  | swap v w hs => exact directional_swap hf hs w v
  | trans h1 h2 IH1 IH2 => exact IH1.trans IH2

/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he :
      directional (List.ofFn (Fin.tail h)) f = fun y => iteratedFDeriv ℝ m f y (Fin.tail h) :=
      funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact
      ((hf.differentiable_iteratedFDeriv (m := m)
            (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))
            x).iteratedFDeriv_succ_apply_left').symm

/-- Raw real C∞ iterated derivatives are symmetric under every slot permutation. -/
theorem iteratedFDeriv_perm {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (h : Fin m → E) (σ : Equiv.Perm (Fin m)) (x : E) :
    iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h := by
  rw [← directional_ofFn hf, ← directional_ofFn hf]
  exact congrFun (directional_perm hf (σ.ofFn_comp_perm h)) x

end FunctionalInequalities.Analysis
