/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicSphereNorm

/-!
# HarmonicSphereRadial

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The radial Laplacian on the sup-normed carrier

Mathlib states the Laplacian only on an inner product space, and its harmonic
layer (`Analysis/InnerProductSpace/Harmonic/*`) is therefore unavailable on
`Vec d`, which carries no `InnerProductSpace R` instance at all.
CoarseGraining's `euclideanCoordLaplacian u x = sum_i d_i d_i u x` is the
carrier-native replacement, and this module computes it on a **radial**
function `w ↦ Phi (|w - z|)`, `|·|` the Euclidean gauge of
`HarmonicSphereNorm`:

```
  Delta (Phi ∘ |· - z|) (x) = Phi'' (|x - z|) + (d - 1) * Phi' (|x - z|) / |x - z|
```

for `x ≠ z`, together with the smoothness statement that a radial function whose
profile is constant near the origin is `C^n` on the whole carrier -- including at
the centre, where the Euclidean gauge itself is not differentiable.

The proof is the elementary two-fold chain rule of `HarmonicSphereNorm`
summed over the `d` coordinate directions; the identity
`sum_i (x i - z i)^2 = |x - z|^2` is what produces the dimensional coefficient.

## Contents

* `contDiff_vecNormSq`, `contDiffAt_euclideanNorm_sub` -- smoothness of the
  Euclidean gauge away from its centre.
* `euclideanCoordLaplacian_eq_zero_of_locally_const` -- a function that is
  constant on a neighbourhood has vanishing coordinate Laplacian there.
* `mem_euclideanBall_self`, `contDiff_radial` -- smoothness of a radial function
  with a profile that is constant near the origin.
* `euclideanCoordSecondDeriv_radial` -- the single-direction second derivative.
* `euclideanCoordLaplacian_radial` -- **the radial Laplacian**.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ} {Φ Φ' Φ'' : ℝ → ℝ} {z x : Vec d}

theorem contDiff_vecNormSq {n : WithTop ℕ∞} : ContDiff ℝ n (vecNormSq : Vec d → ℝ) := by
  have hfun : (vecNormSq : Vec d → ℝ) = fun y : Vec d => ∑ i : Fin d, y i * y i := rfl
  rw [hfun]
  refine ContDiff.sum fun i _ => ?_
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff.mul
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff

theorem contDiffAt_euclideanNorm_sub {n : WithTop ℕ∞} (hx : x ≠ z) :
    ContDiffAt ℝ n (fun w : Vec d => euclideanNorm (w - z)) x := by
  have hq : vecNormSq (x - z) ≠ 0 := fun h => (sub_ne_zero.mpr hx) (vecNormSq_eq_zero h)
  have hinner : ContDiffAt ℝ n (fun w : Vec d => vecNormSq (w - z)) x :=
    (contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)).contDiffAt
  exact (Real.contDiffAt_sqrt (n := n) hq).comp x hinner


theorem euclideanCoordLaplacian_eq_zero_of_locally_const {f : Vec d → ℝ} {c : ℝ}
    {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U)
    (hf : ∀ y ∈ U, f y = c) : euclideanCoordLaplacian f x = 0 := by
  have hd : ∀ i : Fin d, ∀ y ∈ U, euclideanCoordDeriv i f y = 0 := by
    intro i y hy
    have heq : f =ᶠ[nhds y] fun _ : Vec d => c :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy) hf
    rw [euclideanCoordDeriv, heq.fderiv_eq]
    simp
  refine Finset.sum_eq_zero fun i _ => ?_
  have heq2 : euclideanCoordDeriv i f =ᶠ[nhds x] fun _ : Vec d => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (hd i)
  rw [euclideanCoordSecondDeriv, heq2.fderiv_eq]
  simp

theorem mem_euclideanBall_self {r : ℝ} (hr : 0 < r) : z ∈ euclideanBall z r := by
  rw [mem_euclideanBall_iff_euclideanNorm_lt hr.le]
  simpa [euclideanNorm, vecNormSq, vecDot] using hr

/-- A radial function whose profile is constant near the origin and smooth away
from it is smooth on the whole carrier. -/
theorem contDiff_radial {n : WithTop ℕ∞} {a : ℝ} (ha : 0 < a)
    (hsmooth : ∀ t : ℝ, 0 < t → ContDiffAt ℝ n Φ t)
    (hconst : ∀ t : ℝ, 0 ≤ t → t < a → Φ t = Φ 0) :
    ContDiff ℝ n (fun w : Vec d => Φ (euclideanNorm (w - z))) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = z
  · subst hy
    have heq : (fun w : Vec d => Φ (euclideanNorm (w - y))) =ᶠ[nhds y] fun _ : Vec d => Φ 0 := by
      refine Filter.eventuallyEq_of_mem
        (s := euclideanBall y a) ((isOpen_euclideanBall y a).mem_nhds (mem_euclideanBall_self ha)) ?_
      intro w hw
      exact hconst _ (euclideanNorm_nonneg _)
        ((mem_euclideanBall_iff_euclideanNorm_lt ha.le).mp hw)
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact (hsmooth _ (euclideanNorm_pos (sub_ne_zero.mpr hy))).comp y
      (contDiffAt_euclideanNorm_sub hy)


theorem euclideanCoordSecondDeriv_radial
    (h1 : ∀ t : ℝ, 0 < t → HasDerivAt Φ (Φ' t) t)
    (h2 : ∀ t : ℝ, 0 < t → HasDerivAt Φ' (Φ'' t) t)
    (hx : x ≠ z) (i : Fin d) :
    euclideanCoordSecondDeriv i i (fun w : Vec d => Φ (euclideanNorm (w - z))) x =
      Φ'' (euclideanNorm (x - z)) * (x i - z i) ^ 2 / euclideanNorm (x - z) ^ 2
        + Φ' (euclideanNorm (x - z)) / euclideanNorm (x - z)
        - Φ' (euclideanNorm (x - z)) * (x i - z i) ^ 2 / euclideanNorm (x - z) ^ 3 := by
  have hNpos : 0 < euclideanNorm (x - z) := euclideanNorm_pos (sub_ne_zero.mpr hx)
  have hNne : euclideanNorm (x - z) ≠ 0 := ne_of_gt hNpos
  have hP : HasFDerivAt (fun y : Vec d => Φ' (euclideanNorm (y - z)))
      (coordFDeriv (fun j => Φ'' (euclideanNorm (x - z)) *
        ((x j - z j) / euclideanNorm (x - z)))) x :=
    hasFDerivAt_comp_euclideanNorm_sub hx (h2 _ hNpos)
  have hB : HasFDerivAt (fun y : Vec d => y i - z i) (coordFDeriv (basisVec i)) x :=
    hasFDerivAt_coord_sub i
  have hC : HasFDerivAt (fun y : Vec d => (euclideanNorm (y - z))⁻¹)
      (coordFDeriv (fun j => (-(euclideanNorm (x - z) ^ 2)⁻¹) *
        ((x j - z j) / euclideanNorm (x - z)))) x :=
    hasFDerivAt_comp_euclideanNorm_sub hx (hasDerivAt_inv hNne)
  have hg : HasFDerivAt (fun y : Vec d =>
      Φ' (euclideanNorm (y - z)) * (y i - z i) * (euclideanNorm (y - z))⁻¹)
      ((Φ' (euclideanNorm (x - z)) * (x i - z i)) •
          (coordFDeriv fun j => (-(euclideanNorm (x - z) ^ 2)⁻¹) *
            ((x j - z j) / euclideanNorm (x - z)))
        + (euclideanNorm (x - z))⁻¹ •
          (Φ' (euclideanNorm (x - z)) • coordFDeriv (basisVec i)
            + (x i - z i) • (coordFDeriv fun j => Φ'' (euclideanNorm (x - z)) *
              ((x j - z j) / euclideanNorm (x - z))))) x := (hP.mul hB).mul hC
  have heq : euclideanCoordDeriv i (fun w : Vec d => Φ (euclideanNorm (w - z))) =ᶠ[nhds x]
      fun y : Vec d =>
        Φ' (euclideanNorm (y - z)) * (y i - z i) * (euclideanNorm (y - z))⁻¹ := by
    refine Filter.eventuallyEq_of_mem
      (s := ({z}ᶜ : Set (Vec d))) (isOpen_compl_singleton.mem_nhds ?_) ?_
    · simpa using hx
    · intro y hy
      have hyz : y ≠ z := by simpa using hy
      show euclideanCoordDeriv i (fun w : Vec d => Φ (euclideanNorm (w - z))) y =
        Φ' (euclideanNorm (y - z)) * (y i - z i) * (euclideanNorm (y - z))⁻¹
      rw [euclideanCoordDeriv_comp_euclideanNorm_sub hyz
        (h1 _ (euclideanNorm_pos (sub_ne_zero.mpr hyz))) i]
      ring
  rw [euclideanCoordSecondDeriv, heq.fderiv_eq, hg.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    coordFDeriv_apply, basisVec_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  field_simp
  ring

theorem euclideanCoordLaplacian_radial
    (h1 : ∀ t : ℝ, 0 < t → HasDerivAt Φ (Φ' t) t)
    (h2 : ∀ t : ℝ, 0 < t → HasDerivAt Φ' (Φ'' t) t)
    (hx : x ≠ z) :
    euclideanCoordLaplacian (fun w : Vec d => Φ (euclideanNorm (w - z))) x =
      Φ'' (euclideanNorm (x - z))
        + ((d : ℝ) - 1) * Φ' (euclideanNorm (x - z)) / euclideanNorm (x - z) := by
  have hNpos : 0 < euclideanNorm (x - z) := euclideanNorm_pos (sub_ne_zero.mpr hx)
  have hNne : euclideanNorm (x - z) ≠ 0 := ne_of_gt hNpos
  have hsq : ∑ i : Fin d, (x i - z i) ^ 2 = euclideanNorm (x - z) ^ 2 := by
    rw [sq_euclideanNorm]
    simp [vecNormSq, vecDot, sq]
  have hterm : ∀ i : Fin d,
      euclideanCoordSecondDeriv i i (fun w : Vec d => Φ (euclideanNorm (w - z))) x =
        (Φ'' (euclideanNorm (x - z)) / euclideanNorm (x - z) ^ 2
          - Φ' (euclideanNorm (x - z)) / euclideanNorm (x - z) ^ 3) * (x i - z i) ^ 2
          + Φ' (euclideanNorm (x - z)) / euclideanNorm (x - z) := by
    intro i
    rw [euclideanCoordSecondDeriv_radial h1 h2 hx i]
    ring
  rw [euclideanCoordLaplacian]
  simp only [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
