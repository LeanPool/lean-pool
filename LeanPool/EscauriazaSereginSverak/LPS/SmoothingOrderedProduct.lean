/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevLeibniz
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityDivCurlSmooth
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalDivCurlSmooth

/-!
# Ordered derivatives of smooth products

The classical coordinate derivatives of the regularized transport tensor
obey the Leibniz family used by the integer Sobolev norms in Part III.
This is the algebraic first step of the `H^m` transport estimate in
`eq:lps-Hm-energy`.
-/

public section

open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_spatialDeriv_add
    {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (j : Fin 3) :
    spatialDeriv (fun x => f x + g x) j =
      fun x => spatialDeriv f j x + spatialDeriv g j x := by
  funext x
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
    (fderiv_fun_add (hf.differentiable (by simp) x)
      (hg.differentiable (by simp) x))
  simpa [spatialDeriv] using h

private theorem lps_spatialDeriv_mul
    {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (j : Fin 3) :
    spatialDeriv (fun x => f x * g x) j =
      fun x => spatialDeriv f j x * g x + f x * spatialDeriv g j x := by
  funext x
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
    (fderiv_fun_mul (hf.differentiable (by simp) x)
      (hg.differentiable (by simp) x))
  simpa [spatialDeriv, smul_eq_mul, mul_comm, add_comm] using h

private theorem lps_wordDeriv_add
    {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (α : List (Fin 3)) :
    wordDeriv α (fun x => f x + g x) =
      fun x => wordDeriv α f x + wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_wordDeriv hf [j]
      have hgd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_wordDeriv hg [j]
      change wordDeriv α (spatialDeriv (fun x => f x + g x) j) = _
      rw [lps_spatialDeriv_add hf hg j]
      exact ih hfd hgd

/-- Ordered derivatives distribute over a smooth scalar difference
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_wordDeriv_sub
    {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (α : List (Fin 3)) :
    wordDeriv α (fun x => f x - g x) =
      fun x => wordDeriv α f x - wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_wordDeriv hf [j]
      have hgd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_wordDeriv hg [j]
      have hsub : spatialDeriv (fun x => f x - g x) j =
          fun x => spatialDeriv f j x - spatialDeriv g j x := by
        funext x
        have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
          (fderiv_fun_sub (hf.differentiable (by simp) x)
            (hg.differentiable (by simp) x))
        simpa [spatialDeriv] using h
      change wordDeriv α (spatialDeriv (fun x => f x - g x) j) = _
      rw [hsub]
      exact ih hfd hgd

/-- The classical ordered derivative of a smooth scalar product is
the ordered Leibniz family (eq:lps-Hm-energy). -/
theorem lps_wordDeriv_mul_leibniz
    {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (α : List (Fin 3)) :
    wordDeriv α (fun x => f x * g x) =
      sobolevLeibnizFamily α (fun β => wordDeriv β f)
        (fun β => wordDeriv β g) := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_wordDeriv hf [j]
      have hgd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_wordDeriv hg [j]
      change wordDeriv α (spatialDeriv (fun x => f x * g x) j) = _
      rw [lps_spatialDeriv_mul hf hg j]
      rw [lps_wordDeriv_add (hfd.mul hg) (hf.mul hgd) α]
      rw [ih hfd hg, ih hf hgd]
      rfl

/-- For a smooth solenoidal advecting field, convection is the
divergence of its tensor product (eq:lps-Hm-energy). -/
theorem lps_transport_divergence
    (v u : Vec3 → Vec3)
    (hv : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j))
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hdiv : ∀ x : Vec3,
      ∑ j : Fin 3, spatialDeriv (fun y => v y j) j x = 0)
    (i : Fin 3) (x : Vec3) :
    (∑ j : Fin 3, v x j * spatialDeriv (fun y => u y i) j x) =
      ∑ j : Fin 3,
        spatialDeriv (fun y => v y j * u y i) j x := by
  have hprod (j : Fin 3) :
      spatialDeriv (fun y => v y j * u y i) j x =
        spatialDeriv (fun y => v y j) j x * u x i +
          v x j * spatialDeriv (fun y => u y i) j x := by
    exact congrFun (lps_spatialDeriv_mul (hv j) (hu i) j) x
  simp_rw [hprod]
  rw [Finset.sum_add_distrib]
  have hzero :
      (∑ j : Fin 3, spatialDeriv (fun y => v y j) j x * u x i) = 0 := by
    rw [← Finset.sum_mul, hdiv x, zero_mul]
  rw [hzero, zero_add]

/-- Every ordered derivative of smooth solenoidal convection retains
a divergence-form tensor product (eq:lps-Hm-energy). -/
theorem lps_ordered_transport_divergence
    (v u : Vec3 → Vec3)
    (hv : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j))
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hdiv : ∀ x : Vec3,
      ∑ j : Fin 3, spatialDeriv (fun y => v y j) j x = 0)
    (α : List (Fin 3)) (i : Fin 3) :
    wordDeriv α
      (fun x => ∑ j : Fin 3,
        v x j * spatialDeriv (fun y => u y i) j x) =
      fun x => ∑ j : Fin 3,
        spatialDeriv
          (sobolevLeibnizFamily α
            (fun β => wordDeriv β (fun y => v y j))
            (fun β => wordDeriv β (fun y => u y i))) j x := by
  have hbase :
      (fun x => ∑ j : Fin 3,
        v x j * spatialDeriv (fun y => u y i) j x) =
      fun x => ∑ j : Fin 3,
        spatialDeriv (fun y => v y j * u y i) j x := by
    funext x
    exact lps_transport_divergence v u hv hu hdiv i x
  rw [hbase]
  have hsmooth (j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (spatialDeriv (fun y => v y j * u y i) j) :=
    contDiff_wordDeriv ((hv j).mul (hu i)) [j]
  rw [localDivCurlSmooth_wordDeriv_sum α hsmooth]
  funext x
  apply Finset.sum_congr rfl
  intro j _
  rw [localDivCurlSmooth_wordDeriv_spatialDeriv ((hv j).mul (hu i)) α j]
  rw [lps_wordDeriv_mul_leibniz (hv j) (hu i) α]

end ESS
