/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicWeakAlgebra
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationNestedFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationTelescope

/-!
# OscillationNestedAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The nested-recentring assembly

This module runs the nested recentring end to end on the concentric triadic
family `U_j = z + cu_{n+j}`, `0 <= j <= N`, and produces the abstract form of
the display `e.nablaw.oscillations`.

## The mechanism

At every scale `j <= N` the corrector `w` is replaced by a harmonic function
`h_j = w - phi_j`, where `phi_j` in `H^1_0(U_j)` is the potential of the forcing
recentred on `U_j` (`OscillationNestedTransport`).  The defect obeys the
birth-scale bound `|| grad phi_j ||_{L2bar (U_j)} <= sqrt d * M * 3^{n+j}`.  On the
fine cube `U_0` the gradient of `w` is then written as the finite sum

```
  grad w = grad h_N + sum_{j < N} (grad h_j - grad h_{j+1}) + grad phi_0 ,
```

and each summand is estimated on `U_0` *directly from its own birth scale*.

## The two declared divergences

* **The gap restriction `d + 3`.**  The arbitrary-gap harmonic decay
  (`HarmonicReplaceGradient`) is available only for gaps `k >= d + 3`.  The coarse
  term therefore needs `N >= d + 3`, which is imposed as a hypothesis.
* **The small-gap branch.**  Increments born at a scale `j < d + 3` cannot use the
  decay.  They are dispatched instead by the *volume-ratio* comparison of
  `OscillationNestedFamily`, at the cost of the dimensional constant
  `(3 rho)^{d+2}` with `rho = sqrt (3^d)`.  This branch is a single comparison
  between two cubes, not a recurrence, so it does not reintroduce the false step.

Both are visible in the constant, which is written as an explicit sum of the
decay contribution `C(d) rho` and the small-gap contribution `(3 rho)^{d+2}`.

## Contents

* `exists_replacement_family` -- the per-scale harmonic replacements, chosen
  simultaneously at all scales.
* `exists_h1Function_increment` -- the harmonic increment `h_j - h_{j+1}` as an
  `H^1` function on the finer cube, weakly harmonic there, with the explicit
  gradient `grad phi_{j+1} - grad phi_j`.
* `exists_gradient_oscillation_nested_telescope` -- **the abstract display**.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic/oscillation layer of this same
directory.  It mentions no object of the manuscript: no model, no cutoff, no
shell, no corrector, no `sigmaBar`.  The forcing `G` is an abstract Lipschitz
vector field; the manuscript's `sigmaBar^{-1} grad (k_m - k_{m-h})` is one
instance of it, produced elsewhere.  It is intended to be portable into
CoarseGraining by a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the ball one-step estimate and the word
  "iterating").
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- **The triangle inequality in subtracted form.**

The normalized `L^2` deviation of a difference from a centre `c` is at most the
deviation of the first field from `c` plus the size of the second field. -/
private theorem sqrt_meanSquareDeviationVecOn_sub_le {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {f g : Vec d → Vec d}
    (hf : MemVectorL2 V f) (hg : MemVectorL2 V g) (c : Vec d) :
    Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V (fun x => f x - g x) c) ≤
      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V f c) +
        Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V g 0) := by
  have hgn : MemVectorL2 V (fun x => -g x) := hg.neg
  have hstep := sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2 hf hgn c 0
  rw [meanSquareDeviationVecOn_neg] at hstep
  simp only [add_zero] at hstep
  have hfun : (fun x => f x - g x) = fun x => f x + -g x := by
    funext x
    exact sub_eq_add_neg (f x) (g x)
  rw [hfun]
  exact hstep

/-- **The per-scale harmonic replacement family.**

From the single weak equation on the coarse cube `z + cu_{n+N}` one obtains, at
every scale `j <= N` simultaneously, an `H^1_0(z + cu_{n+j})` potential `phi_j`
whose subtraction makes `w` weakly harmonic on `z + cu_{n+j}` and whose gradient
has normalized `L^2` size at most `sqrt d * M * 3^{n+j}` there. -/
theorem exists_replacement_family [NeZero d] (z : Vec d) (n : ℤ) (N : ℕ)
    (w : H1Function (openCubeAtScale z (n + (N : ℤ)))) {G : Vec d → Vec d} {M : ℝ}
    (hM : 0 ≤ M) (hGdiff : ∀ i : Fin d, Differentiable ℝ fun y => G y i)
    (hGbound : ∀ x ∈ openCubeAtScale z (n + (N : ℤ)), ∀ i : Fin d,
      ‖fderiv ℝ (fun y => G y i) x‖ ≤ M)
    (hw : ∀ ψ : H10Function (openCubeAtScale z (n + (N : ℤ))),
      ∫ x in openCubeAtScale z (n + (N : ℤ)),
          vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
        ∫ x in openCubeAtScale z (n + (N : ℤ)),
          vecDot (G x) (ψ.toH1Function.grad x) ∂volume) :
    ∃ Φ : ∀ j : ℕ, H10Function (openCubeAtScale z (n + (j : ℤ))),
      ∀ j : ℕ, j ≤ N →
        IsWeaklyHarmonicOn (openCubeAtScale z (n + (j : ℤ)))
            (fun x => w.toFun x - (Φ j).toH1Function.toFun x) ∧
          Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (j : ℤ)))
              (Φ j).toH1Function.grad 0) ≤
            Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ (n + (j : ℤ)) := by
  have hex : ∀ j : ℕ, ∃ φ : H10Function (openCubeAtScale z (n + (j : ℤ))), j ≤ N →
      IsWeaklyHarmonicOn (openCubeAtScale z (n + (j : ℤ)))
          (fun x => w.toFun x - φ.toH1Function.toFun x) ∧
        Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (j : ℤ)))
            φ.toH1Function.grad 0) ≤
          Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ (n + (j : ℤ)) := by
    intro j
    by_cases hj : j ≤ N
    · have hle : n + (j : ℤ) ≤ n + (N : ℤ) := by omega
      obtain ⟨φ, hharm, hbound⟩ :=
        exists_h10Function_isWeaklyHarmonicOn_sub_sqrt_le_subcube z hle w hM hGdiff hGbound hw
      refine ⟨φ, fun _ => ⟨?_, hbound⟩⟩
      have heq : (w.restrict (isOpen_openCubeAtScale z (n + (j : ℤ)))
            (openCubeAtScale_subset_of_le z hle) - φ.toH1Function).toFun
          = fun x => w.toFun x - φ.toH1Function.toFun x := H1Function.sub_toFun _ _
      rwa [heq] at hharm
    · exact ⟨0, fun h => absurd h hj⟩
  choose Φ hΦ using hex
  exact ⟨Φ, hΦ⟩

/-- **The harmonic increment born at scale `j`.**

For `j < N` the difference `h_j - h_{j+1}` of the two harmonic replacements built
at consecutive scales is an `H^1` function on the finer cube `z + cu_{n+j}`, is
weakly harmonic there, and its weak gradient is
`grad phi_{j+1} - grad phi_j`: the corrector's own gradient cancels. -/
theorem exists_h1Function_increment (z : Vec d) (n : ℤ) (N j : ℕ) (hj : j < N)
    (w : H1Function (openCubeAtScale z (n + (N : ℤ))))
    (Φ : ∀ i : ℕ, H10Function (openCubeAtScale z (n + (i : ℤ))))
    (hharm : ∀ i : ℕ, i ≤ N → IsWeaklyHarmonicOn (openCubeAtScale z (n + (i : ℤ)))
      (fun x => w.toFun x - (Φ i).toH1Function.toFun x)) :
    ∃ h : H1Function (openCubeAtScale z (n + (j : ℤ))),
      IsWeaklyHarmonicOn (openCubeAtScale z (n + (j : ℤ))) h.toFun ∧
        h.grad = fun x =>
          (Φ (j + 1)).toH1Function.grad x - (Φ j).toH1Function.grad x := by
  have hVU : openCubeAtScale z (n + (j : ℤ)) ⊆ openCubeAtScale z (n + ((j + 1 : ℕ) : ℤ)) :=
    openCubeAtScale_subset_of_le z (by omega)
  have hVN : openCubeAtScale z (n + (j : ℤ)) ⊆ openCubeAtScale z (n + (N : ℤ)) :=
    openCubeAtScale_subset_of_le z (by omega)
  have hUN : openCubeAtScale z (n + ((j + 1 : ℕ) : ℤ)) ⊆ openCubeAtScale z (n + (N : ℤ)) :=
    openCubeAtScale_subset_of_le z (by omega)
  obtain ⟨a, hatf, hagr⟩ : ∃ a : H1Function (openCubeAtScale z (n + (j : ℤ))),
      a.toFun = (fun x => w.toFun x - (Φ j).toH1Function.toFun x) ∧
        a.grad = fun x => w.grad x - (Φ j).toH1Function.grad x :=
    ⟨w.restrict (isOpen_openCubeAtScale z (n + (j : ℤ))) hVN - (Φ j).toH1Function,
      H1Function.sub_toFun _ _, H1Function.sub_grad _ _⟩
  obtain ⟨b, hbtf, hbgr⟩ : ∃ b : H1Function (openCubeAtScale z (n + (j : ℤ))),
      b.toFun = (fun x => w.toFun x - (Φ (j + 1)).toH1Function.toFun x) ∧
        b.grad = fun x => w.grad x - (Φ (j + 1)).toH1Function.grad x :=
    ⟨(w.restrict (isOpen_openCubeAtScale z (n + ((j + 1 : ℕ) : ℤ))) hUN -
        (Φ (j + 1)).toH1Function).restrict
          (isOpen_openCubeAtScale z (n + (j : ℤ))) hVU,
      H1Function.sub_toFun _ _, H1Function.sub_grad _ _⟩
  refine ⟨a - b, ?_, ?_⟩
  · have h1 : IsWeaklyHarmonicOn (openCubeAtScale z (n + (j : ℤ))) a.toFun := by
      rw [hatf]
      exact hharm j hj.le
    have h2 : IsWeaklyHarmonicOn (openCubeAtScale z (n + (j : ℤ))) b.toFun := by
      rw [hbtf]
      exact (hharm (j + 1) hj).mono hVU
    have hi1 : IntegrableOn a.toFun (openCubeAtScale z (n + (j : ℤ))) volume :=
      a.memL2.integrable (by norm_num)
    have hi2 : IntegrableOn b.toFun (openCubeAtScale z (n + (j : ℤ))) volume :=
      b.memL2.integrable (by norm_num)
    have hsub := h1.sub h2 hi1 hi2
    rw [H1Function.sub_toFun]
    exact hsub
  · rw [H1Function.sub_grad, hagr, hbgr]
    funext x
    funext i
    simp only [Pi.sub_apply]
    ring

private theorem gradientOscillation_incrementDecay :
    ∀ {d : ℕ} (C₀ : ℝ),
      (0 : ℝ) ≤ C₀ →
        (∀ (z : Vec d) (n : ℤ) (k : ℕ),
            d + (3 : ℕ) ≤ k →
              ∀ (h : H1Function (openCubeAtScale z (n + (↑k : ℤ)))),
                IsWeaklyHarmonicOn (openCubeAtScale z (n + (↑k : ℤ))) h.toFun →
                  ∀ (c : Vec d),
                    √(Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) h.grad) ≤
                      C₀ * (3 : ℝ) ^ (-(↑k : ℤ)) *
                        √(Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (↑k : ℤ) - (1
                          : ℤ))) h.grad c)) →
          ∀ (ρ : ℝ),
            √((3 : ℝ) ^ d) = ρ →
              (0 : ℝ) ≤ ρ →
                (1 : ℝ) ≤ ρ →
                  ∀ (A : ℝ),
                    C₀ * ρ ≤ A →
                      ((3 : ℝ) * ρ) ^ (d + (2 : ℕ)) ≤ A →
                        ∀ (z : Vec d) (n : ℤ) (N : ℕ) (w : H1Function (openCubeAtScale z (n + (↑N
                          : ℤ)))) (M : ℝ)
                          (Φ : (j : ℕ) → H10Function (openCubeAtScale z (n + (↑j : ℤ)))),
                          (∀ j ≤ N,
                              (IsWeaklyHarmonicOn (openCubeAtScale z (n + (↑j : ℤ))) fun (x : Vec
                                d) =>
                                  w.toFun x - (Φ j).toFun x) ∧
                                √(Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (↑j :
                                  ℤ))) (Φ j).grad
                                      (0 : Vec d)) ≤
                                  √(↑d : ℝ) * M * (3 : ℝ) ^ (n + (↑j : ℤ))) →
                            (∀ (j : ℕ), ∀ m ≤ n + (↑j : ℤ), MemVectorL2 (openCubeAtScale z m) (Φ
                              j).grad) →
                              ∀ (E : ℕ → ℝ),
                                (∀ (j : ℕ), E j = √(↑d : ℝ) * M * (3 : ℝ) ^ (n + (↑j : ℤ))) →
                                  (∀ (j : ℕ), (0 : ℝ) ≤ E j) →
                                    ∀ (F : ℕ → Vec d → Vec d) (S : ℕ → ℝ),
                                      (∀ j < N, F j = fun (x : Vec d) => (Φ (j + (1 : ℕ))).grad x
                                        - (Φ j).grad x) →
                                        (∀ j ≤ N + (1 : ℕ), MemVectorL2 (openCubeAtScale z n) (F
                                          j)) →
                                          (∀ j ≤ N,
                                              S j = √(Book.Ch01.meanSquareOscillationVecOn
                                                (openCubeAtScale z n) (F j))) →
                                            (∀ (k : ℕ), (0 : ℝ) < (3 : ℝ) ^ (-(↑k : ℤ))) →
                                              ∀ j < N, S j ≤ A * (3 : ℝ) ^ (-(↑j : ℤ)) * (E j + ρ
                                                * E (j + (1 : ℕ))) := by
  intro d C₀ hC₀nn hdec ρ hρdef hρnn hρ1 A hA1 hA2 z n N w _ Φ hΦ hΦL2 E hE hEnn F S hFlow hFL2
    hSosc hp j hj
  have hFj : F j = fun x =>
      (Φ (j + 1)).toH1Function.grad x - (Φ j).toH1Function.grad x := hFlow j hj
  by_cases hgap : d + 3 ≤ j
  · obtain ⟨hInc, hIncharm, hIncgr⟩ :=
      exists_h1Function_increment z n N j hj w Φ fun i hi => (hΦ i hi).1
    have hbound := hdec z n j hgap hInc hIncharm (0 : Vec d)
    have hV1 : MemVectorL2 (openCubeAtScale z (n + (j : ℤ) - 1))
        (Φ (j + 1)).toH1Function.grad := hΦL2 (j + 1) _ (by omega)
    have hV2 : MemVectorL2 (openCubeAtScale z (n + (j : ℤ) - 1))
        (Φ j).toH1Function.grad := hΦL2 j _ (by omega)
    have hsplit1 := sqrt_meanSquareDeviationVecOn_sub_le hV1 hV2 (0 : Vec d)
    have hb1 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z (n + (j : ℤ) - 1)) (Φ (j + 1)).toH1Function.grad 0)
        ≤ ρ ^ 2 * E (j + 1) := by
      have hstep := sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le z
        (m := n + (j : ℤ) - 1) (m' := n + ((j + 1 : ℕ) : ℤ)) (i := 2)
        (by push_cast; ring) (hΦL2 (j + 1) _ le_rfl) (0 : Vec d)
      rw [hρdef] at hstep
      refine le_trans hstep ?_
      have hb := (hΦ (j + 1) hj).2
      rw [← hE (j + 1)] at hb
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have hb2 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z (n + (j : ℤ) - 1)) (Φ j).toH1Function.grad 0)
        ≤ ρ * E j := by
      have hstep := sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le z
        (m := n + (j : ℤ) - 1) (m' := n + (j : ℤ)) (i := 1)
        (by push_cast; ring) (hΦL2 j _ le_rfl) (0 : Vec d)
      rw [hρdef, pow_one] at hstep
      refine le_trans hstep ?_
      have hb := (hΦ j hj.le).2
      rw [← hE j] at hb
      exact mul_le_mul_of_nonneg_left hb hρnn
    have hchain : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z (n + (j : ℤ) - 1)) hInc.grad 0)
        ≤ ρ ^ 2 * E (j + 1) + ρ * E j := by
      rw [hIncgr]
      exact le_trans hsplit1 (add_le_add hb1 hb2)
    have hSj : S j = Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
        (openCubeAtScale z n) hInc.grad) := by
      rw [hSosc j hj.le, hFj, ← hIncgr]
    rw [hSj]
    refine le_trans hbound ?_
    refine le_trans (mul_le_mul_of_nonneg_left hchain
      (mul_nonneg hC₀nn (hp j).le)) ?_
    have hrw : C₀ * (3 : ℝ) ^ (-(j : ℤ)) * (ρ ^ 2 * E (j + 1) + ρ * E j)
        = C₀ * ρ * (3 : ℝ) ^ (-(j : ℤ)) * (E j + ρ * E (j + 1)) := by ring
    rw [hrw]
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA1 (hp j).le) ?_
    have h1 := hEnn j
    have h2 := mul_nonneg hρnn (hEnn (j + 1))
    linarith only [h1, h2]
  · have hjle : j ≤ d + 2 := by omega
    have hFjL2 : MemVectorL2 (openCubeAtScale z n) (F j) := hFL2 j (by omega)
    have hstep0 : S j ≤ Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z n) (F j) 0) := by
      rw [hSosc j hj.le]
      exact sqrt_meanSquareOscillationVecOn_le_sqrt_meanSquareDeviationVecOn_of_memVectorL2
        (volume_openCubeAtScale_ne_top z n) (volume_openCubeAtScale_toReal_pos z n) hFjL2 0
    have hsplit1 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z n) (F j) 0)
        ≤ Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
            (Φ (j + 1)).toH1Function.grad 0)
          + Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
            (Φ j).toH1Function.grad 0) := by
      rw [hFj]
      exact sqrt_meanSquareDeviationVecOn_sub_le (hΦL2 (j + 1) n (by omega))
        (hΦL2 j n (by omega)) 0
    have hb1 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
        (Φ (j + 1)).toH1Function.grad 0) ≤ ρ ^ (j + 1) * E (j + 1) := by
      have hstep := sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le z
        (m := n) (m' := n + ((j + 1 : ℕ) : ℤ)) (i := j + 1) rfl
        (hΦL2 (j + 1) _ le_rfl) (0 : Vec d)
      rw [hρdef] at hstep
      refine le_trans hstep ?_
      have hb := (hΦ (j + 1) hj).2
      rw [← hE (j + 1)] at hb
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have hb2 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
        (Φ j).toH1Function.grad 0) ≤ ρ ^ j * E j := by
      have hstep := sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le z
        (m := n) (m' := n + (j : ℤ)) (i := j) rfl (hΦL2 j _ le_rfl) (0 : Vec d)
      rw [hρdef] at hstep
      refine le_trans hstep ?_
      have hb := (hΦ j hj.le).2
      rw [← hE j] at hb
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hmul : ρ ^ j * (3 : ℝ) ^ j ≤ A := by
      have hid : ρ ^ j * (3 : ℝ) ^ j = (3 * ρ) ^ j := by rw [mul_pow]; ring
      rw [hid]
      exact le_trans (pow_le_pow_right₀ (by linarith only [hρ1]) hjle) hA2
    have h3neg : (3 : ℝ) ^ (-(j : ℤ)) = ((3 : ℝ) ^ j)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have hkey : ρ ^ j ≤ A * (3 : ℝ) ^ (-(j : ℤ)) := by
      rw [h3neg, ← div_eq_mul_inv]
      exact (le_div_iff₀ h3j).mpr hmul
    have hc1 : ρ ^ j * E j ≤ A * (3 : ℝ) ^ (-(j : ℤ)) * E j :=
      mul_le_mul_of_nonneg_right hkey (hEnn j)
    have hc2 : ρ ^ (j + 1) * E (j + 1)
        ≤ A * (3 : ℝ) ^ (-(j : ℤ)) * (ρ * E (j + 1)) := by
      have hpw : ρ ^ (j + 1) * E (j + 1) = ρ ^ j * (ρ * E (j + 1)) := by
        rw [pow_succ]; ring
      rw [hpw]
      exact mul_le_mul_of_nonneg_right hkey (mul_nonneg hρnn (hEnn (j + 1)))
    have hring : A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + ρ * E (j + 1))
        = A * (3 : ℝ) ^ (-(j : ℤ)) * E j
          + A * (3 : ℝ) ^ (-(j : ℤ)) * (ρ * E (j + 1)) := by ring
    rw [hring]
    linarith only [hstep0, hsplit1, hb1, hb2, hc1, hc2]

private theorem oscillationNestedAssembly_comparisonBounds1 :
    ∀ {d : ℕ} (C₀ : ℝ) (_ : (0 : ℝ) ≤ C₀)
      (_ :
        ∀ (z : Vec d) (n : ℤ) (k : ℕ),
          d + (3 : ℕ) ≤ k →
            ∀ (h : H1Function (openCubeAtScale z (n + (↑k : ℤ)))),
              IsWeaklyHarmonicOn (openCubeAtScale z (n + (↑k : ℤ))) h.toFun →
                ∀ (c : Vec d),
                  √(Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) h.grad) ≤
                    C₀ * (3 : ℝ) ^ (-(↑k : ℤ)) *
                      √(Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (↑k : ℤ) - (1 :
                        ℤ))) h.grad c))
      (ρ : ℝ) (_ : √((3 : ℝ) ^ d) = ρ) (_ : (0 : ℝ) ≤ ρ) (_ : (1 : ℝ) ≤ ρ) (A : ℝ) (_ : (0 : ℝ) ≤ A)
      (_ : C₀ * ρ ≤ A) (_ : ((3 : ℝ) * ρ) ^ (d + (2 : ℕ)) ≤ A) (z : Vec d) (n : ℤ) (N : ℕ) (_ : d
        + (3 : ℕ) ≤ N)
      (w : H1Function (openCubeAtScale z (n + (↑N : ℤ)))) (M : ℝ)
      (Φ : (j : ℕ) → H10Function (openCubeAtScale z (n + (↑j : ℤ))))
      (_ :
        ∀ j ≤ N,
          (IsWeaklyHarmonicOn (openCubeAtScale z (n + (↑j : ℤ))) fun (x : Vec d) => w.toFun x - (Φ
            j).toFun x) ∧
            √(Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (↑j : ℤ))) (Φ j).grad (0
              : Vec d)) ≤
              √(↑d : ℝ) * M * (3 : ℝ) ^ (n + (↑j : ℤ)))
      (_ : ∀ (j : ℕ), ∀ m ≤ n + (↑j : ℤ), MemVectorL2 (openCubeAtScale z m) (Φ j).grad)
      (_ : ∀ m ≤ n + (↑N : ℤ), MemVectorL2 (openCubeAtScale z m) w.grad) (E : ℕ → ℝ)
      (_ : ∀ (j : ℕ), E j = √(↑d : ℝ) * M * (3 : ℝ) ^ (n + (↑j : ℤ))) (_ : ∀ (j : ℕ), (0 : ℝ) ≤ E
        j) (Ph : ℕ → ℝ)
      (_ : ∀ (j : ℕ), Ph j = √(Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z (n + (↑j :
        ℤ))) w.grad))
      (F : ℕ → Vec d → Vec d) (cen : ℕ → Vec d)
      (_ : ∀ (j : ℕ), cen j = if j = N + (1 : ℕ) then (0 : Vec d) else volumeAverageVec
        (openCubeAtScale z n) (F j))
      (S : ℕ → ℝ) (_ : ∀ (j : ℕ), S j = √(Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
        (F j) (cen j)))
      (_ : ∀ j < N, F j = fun (x : Vec d) => (Φ (j + (1 : ℕ))).grad x - (Φ j).grad x)
      (_ : F N = fun (x : Vec d) => w.grad x - (Φ N).grad x) (_ : F (N + (1 : ℕ)) = (Φ (0 :
        ℕ)).grad)
      (_ : ∀ j ≤ N + (1 : ℕ), MemVectorL2 (openCubeAtScale z n) (F j))
      (_ :
        √(Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) w.grad) ≤
          ∑ x ∈ Finset.range N, S x + S N + S (N + (1 : ℕ))),
      (∀ (k : ℕ), (0 : ℝ) < (3 : ℝ) ^ (-(↑k : ℤ))) ∧
        Ph (0 : ℕ) = √(Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) w.grad) ∧
          Ph (0 : ℕ) ≤
            A * (3 : ℝ) ^ (-(↑N : ℤ)) * Ph N +
              (A * ((1 : ℝ) + (3 : ℝ) * ρ) * (↑N : ℝ) + A + (2 : ℝ)) * ((3 : ℝ) ^ n * (√(↑d : ℝ) *
                M)) := by
  intro d C₀ hC₀nn hdec ρ hρdef hρnn hρ1 A hAnn hA1 hA2 z n N hN w M Φ hΦ hΦL2 hwL2 E hE hEnn Ph
    hPh F cen hcen S hS hFlow hFmid hFtop hFL2 htri
  have hcenLow : ∀ j : ℕ, j ≤ N → cen j = volumeAverageVec (openCubeAtScale z n) (F j) := by
    intro j hj
    rw [hcen, ite_eq_right (by omega)]
  have hSosc : ∀ j : ℕ, j ≤ N → S j =
      Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) (F j)) := by
    intro j hj
    rw [hS, hcenLow j hj]
    rfl
  -- the fine-scale defect
  have hdefect : S (N + 1) ≤ E 0 := by
    have hcenTop : cen (N + 1) = 0 := by rw [hcen, ite_eq_left rfl]
    obtain ⟨g, hg⟩ : ∃ g : Vec d → Vec d, (Φ 0).toH1Function.grad = g := ⟨_, rfl⟩
    have h := (hΦ 0 (Nat.zero_le N)).2
    rw [← hE 0, hg] at h
    have hcube : openCubeAtScale z (n + ((0 : ℕ) : ℤ)) = openCubeAtScale z n := by norm_num
    rw [hcube] at h
    rw [hS, hcenTop, hFtop, hg]
    exact h
  -- the coarse harmonic term
  have hp : ∀ k : ℕ, (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := fun k => zpow_pos (by norm_num) _
  have hTle : S N ≤ A * (3 : ℝ) ^ (-(N : ℤ)) * (Ph N + E N) := by
    obtain ⟨hN0, hNtf, hNgr⟩ : ∃ h : H1Function (openCubeAtScale z (n + (N : ℤ))),
        h.toFun = (fun x => w.toFun x - (Φ N).toH1Function.toFun x) ∧
          h.grad = fun x => w.grad x - (Φ N).toH1Function.grad x :=
      ⟨w - (Φ N).toH1Function, H1Function.sub_toFun _ _, H1Function.sub_grad _ _⟩
    have hNharm : IsWeaklyHarmonicOn (openCubeAtScale z (n + (N : ℤ))) hN0.toFun := by
      rw [hNtf]
      exact (hΦ N le_rfl).1
    have hFN : F N = hN0.grad := by rw [hNgr, hFmid]
    have hbound := hdec z n N hN hN0 hNharm
      (volumeAverageVec (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad)
    have hV' : MemVectorL2 (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad := hwL2 _ (by omega)
    have hΦ' : MemVectorL2 (openCubeAtScale z (n + (N : ℤ) - 1))
        (Φ N).toH1Function.grad := hΦL2 N _ (by omega)
    have hsplit1 := sqrt_meanSquareDeviationVecOn_sub_le hV' hΦ'
      (volumeAverageVec (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad)
    have hw1 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad
        (volumeAverageVec (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad)) ≤ ρ * Ph N := by
      have hstep1 : Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
          (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad)
          ≤ Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
            (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad
            (volumeAverageVec (openCubeAtScale z (n + (N : ℤ))) w.grad)) :=
        sqrt_meanSquareOscillationVecOn_le_sqrt_meanSquareDeviationVecOn_of_memVectorL2
          (volume_openCubeAtScale_ne_top z _) (volume_openCubeAtScale_toReal_pos z _) hV' _
      have hstep2 := sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le z
        (m := n + (N : ℤ) - 1) (m' := n + (N : ℤ)) (i := 1) (by push_cast; ring)
        (hwL2 _ le_rfl) (volumeAverageVec (openCubeAtScale z (n + (N : ℤ))) w.grad)
      rw [hρdef, pow_one] at hstep2
      rw [hPh N]
      exact le_trans hstep1 hstep2
    have hΦ1 : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z (n + (N : ℤ) - 1)) (Φ N).toH1Function.grad 0) ≤ ρ * E N := by
      have hstep2 := sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le z
        (m := n + (N : ℤ) - 1) (m' := n + (N : ℤ)) (i := 1) (by push_cast; ring)
        (hΦL2 N _ le_rfl) (0 : Vec d)
      rw [hρdef, pow_one] at hstep2
      refine le_trans hstep2 ?_
      have hb := (hΦ N le_rfl).2
      rw [← hE N] at hb
      exact mul_le_mul_of_nonneg_left hb hρnn
    have hchain : Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale z (n + (N : ℤ) - 1)) hN0.grad
        (volumeAverageVec (openCubeAtScale z (n + (N : ℤ) - 1)) w.grad))
        ≤ ρ * Ph N + ρ * E N := by
      rw [hNgr]
      exact le_trans hsplit1 (add_le_add hw1 hΦ1)
    have hPhnn : 0 ≤ Ph N := by
      rw [hPh N]
      exact Real.sqrt_nonneg _
    have hfinal : S N ≤ C₀ * (3 : ℝ) ^ (-(N : ℤ)) * (ρ * Ph N + ρ * E N) := by
      rw [hSosc N le_rfl, hFN]
      exact le_trans hbound (mul_le_mul_of_nonneg_left hchain
        (mul_nonneg hC₀nn (hp N).le))
    have hrw : C₀ * (3 : ℝ) ^ (-(N : ℤ)) * (ρ * Ph N + ρ * E N)
        = C₀ * ρ * (3 : ℝ) ^ (-(N : ℤ)) * (Ph N + E N) := by ring
    rw [hrw] at hfinal
    exact le_trans hfinal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA1 (hp N).le) (by linarith only [hPhnn, hEnn N]))
  -- the harmonic increments
  have hSle := @gradientOscillation_incrementDecay (d) (C₀) (hC₀nn) (hdec) (ρ) (hρdef) (hρnn)
    (hρ1) (A) (hA1) (hA2) (z) (n) (N) (w) (M) (Φ) (hΦ) (hΦL2) (E) (hE) (hEnn) (F) (S) (hFlow)
      (hFL2) (hSosc) (hp)
  -- the telescope
  have hEle : ∀ j : ℕ, j ≤ N → E j ≤ Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ (n + (j : ℤ)) :=
    fun j _ => le_of_eq (hE j)
  have hPh0eq : Ph 0 = Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
      (openCubeAtScale z n) w.grad) := by
    rw [hPh 0]
    norm_num
  have hsplitfin : Ph 0 ≤ S N + (∑ j ∈ Finset.range N, S j) + 2 * E 0 := by
    rw [hPh0eq]
    linarith only [htri, hdefect, hEnn 0]
  have hmain := le_zpow_mul_add_nsmul_of_nested_decomposition (Phi := Ph) (E := E) (S := S)
    (T := S N) (n := n) (N := N) (A := A) (rho := ρ) (c := Real.sqrt (d : ℝ) * M)
    hAnn hρnn hEle hsplitfin hTle hSle
  exact ⟨hp, hPh0eq, hmain⟩

/-- **The nested-recentring display.**

Let `w` be an `H^1` function on the coarse concentric cube `z + cu_{n+N}` which
weakly solves `- Delta w = div G` there against `H^1_0` competitors, and suppose
the differentials of the coordinates of the forcing `G` are bounded by `M` on
that cube.  If the number of scales satisfies `N >= d + 3`, then

```
  || grad w - (grad w)_{z+cu_n} ||_{L2bar (z+cu_n)}
    <= C(d) 3^{-N} || grad w - (grad w)_{z+cu_{n+N}} ||_{L2bar (z+cu_{n+N})}
       + C(d) N 3^n M ,
```

with a constant depending only on the dimension.  This is the shape of the
manuscript's `e.nablaw.oscillations` with `N = m - h - n` and
`M = sigmaBar^{-1} || grad (k_m - k_{m-h}) ||_{L^infty}`: the full geometric gain
`3^{-(m-h-n)}` on the coarse term, and a forcing term linear in `m - h - n`
carrying the single factor `3^n`.  The coarse term appears here in the sharper
*oscillation* form; the printed norm form follows by mean recentring.

The proof never forms an adjacent-scale cube recurrence: increments born at
scale `j >= d + 3` are hit once by the arbitrary-gap harmonic decay from their
birth scale directly to the fine cube, and the finitely many increments born at
`j < d + 3` are dispatched by a single volume-ratio comparison.  See. -/
theorem exists_gradient_oscillation_nested_telescope (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (n : ℤ) (N : ℕ), d + 3 ≤ N →
      ∀ (w : H1Function (openCubeAtScale z (n + (N : ℤ)))) (G : Vec d → Vec d) (M : ℝ),
        0 ≤ M → (∀ i : Fin d, Differentiable ℝ fun y => G y i) →
        (∀ x ∈ openCubeAtScale z (n + (N : ℤ)), ∀ i : Fin d,
          ‖fderiv ℝ (fun y => G y i) x‖ ≤ M) →
        (∀ ψ : H10Function (openCubeAtScale z (n + (N : ℤ))),
          ∫ x in openCubeAtScale z (n + (N : ℤ)),
              vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
            ∫ x in openCubeAtScale z (n + (N : ℤ)),
              vecDot (G x) (ψ.toH1Function.grad x) ∂volume) →
          Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) w.grad)
            ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
                  (openCubeAtScale z (n + (N : ℤ))) w.grad)
              + C * (N : ℝ) * ((3 : ℝ) ^ n * M) := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C₀, hC₀nn, hdec⟩ := exists_gradient_oscillation_gap_decay_weakGradient hd
  obtain ⟨ρ, hρdef⟩ : ∃ r : ℝ, Real.sqrt ((3 : ℝ) ^ d) = r := ⟨_, rfl⟩
  have hρnn : (0 : ℝ) ≤ ρ := by
    rw [← hρdef]
    exact Real.sqrt_nonneg _
  have hρ1 : (1 : ℝ) ≤ ρ := by
    rw [← hρdef]
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_le_sqrt h1
  obtain ⟨A, hAdef⟩ : ∃ r : ℝ, r = C₀ * ρ + (3 * ρ) ^ (d + 2) := ⟨_, rfl⟩
  have hpow2 : (0 : ℝ) ≤ (3 * ρ) ^ (d + 2) := by positivity
  have hC₀ρ : (0 : ℝ) ≤ C₀ * ρ := mul_nonneg hC₀nn hρnn
  have hAnn : (0 : ℝ) ≤ A := by rw [hAdef]; linarith only [hC₀ρ, hpow2]
  have hA1 : C₀ * ρ ≤ A := by rw [hAdef]; linarith only [hpow2]
  have hA2 : (3 * ρ) ^ (d + 2) ≤ A := by rw [hAdef]; linarith only [hC₀ρ]
  obtain ⟨Kb, hKbdef⟩ : ∃ r : ℝ, r = A * (1 + 3 * ρ) + 2 * A + 2 := ⟨_, rfl⟩
  have h13 : (0 : ℝ) ≤ A * (1 + 3 * ρ) := mul_nonneg hAnn (by linarith only [hρnn])
  have hKbnn : (0 : ℝ) ≤ Kb := by rw [hKbdef]; linarith only [h13, hAnn]
  have hAKb : A ≤ Kb := by rw [hKbdef]; linarith only [h13, hAnn]
  have hsd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  refine ⟨Kb * (Real.sqrt (d : ℝ) + 1), mul_nonneg hKbnn (by linarith only [hsd]), ?_⟩
  intro z n N hN w G M hM hGdiff hGbound hw
  obtain ⟨Φ, hΦ⟩ := exists_replacement_family z n N w hM hGdiff hGbound hw
  have hΦL2 : ∀ (j : ℕ) (m : ℤ), m ≤ n + (j : ℤ) →
      MemVectorL2 (openCubeAtScale z m) (Φ j).toH1Function.grad := fun j m hm =>
    memVectorL2_mono (openCubeAtScale_subset_of_le z hm) (Φ j).toH1Function.grad_memVectorL2
  have hwL2 : ∀ m : ℤ, m ≤ n + (N : ℤ) → MemVectorL2 (openCubeAtScale z m) w.grad :=
    fun m hm => memVectorL2_mono (openCubeAtScale_subset_of_le z hm) w.grad_memVectorL2
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, ∀ j : ℕ,
      E j = Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ (n + (j : ℤ)) := ⟨_, fun _ => rfl⟩
  have hEnn : ∀ j : ℕ, 0 ≤ E j := by
    intro j
    rw [hE]
    exact mul_nonneg (mul_nonneg hsd hM) (zpow_three_pos _).le
  obtain ⟨Ph, hPh⟩ : ∃ P : ℕ → ℝ, ∀ j : ℕ, P j =
      Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
        (openCubeAtScale z (n + (j : ℤ))) w.grad) := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Vec d → Vec d, ∀ (j : ℕ) (x : Vec d), F j x =
      (if j < N then (Φ (j + 1)).toH1Function.grad x - (Φ j).toH1Function.grad x
        else if j = N then w.grad x - (Φ N).toH1Function.grad x
        else (Φ 0).toH1Function.grad x) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨cen, hcen⟩ : ∃ c : ℕ → Vec d, ∀ j : ℕ, c j =
      (if j = N + 1 then 0 else volumeAverageVec (openCubeAtScale z n) (F j)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ j : ℕ, S j =
      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n) (F j) (cen j)) :=
    ⟨_, fun _ => rfl⟩
  -- the three shapes of the summands
  have hFlow : ∀ j : ℕ, j < N → F j = fun x =>
      (Φ (j + 1)).toH1Function.grad x - (Φ j).toH1Function.grad x := by
    intro j hj
    funext x
    rw [hF, ite_eq_left hj]
  have hFmidx : ∀ x : Vec d, F N x = w.grad x - (Φ N).toH1Function.grad x := by
    intro x
    rw [hF, ite_eq_right (lt_irrefl N), ite_eq_left rfl]
  have hFtopx : ∀ x : Vec d, F (N + 1) x = (Φ 0).toH1Function.grad x := by
    intro x
    rw [hF, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hFmid : F N = fun x => w.grad x - (Φ N).toH1Function.grad x := by
    funext x
    exact hFmidx x
  have hFtop : F (N + 1) = (Φ 0).toH1Function.grad := by
    funext x
    exact hFtopx x
  have hFL2 : ∀ j : ℕ, j ≤ N + 1 → MemVectorL2 (openCubeAtScale z n) (F j) := by
    intro j hj
    by_cases h1 : j < N
    · rw [hFlow j h1]
      exact (hΦL2 (j + 1) n (by omega)).sub (hΦL2 j n (by omega))
    · by_cases h2 : j = N
      · rw [h2, hFmid]
        exact (hwL2 n (by omega)).sub (hΦL2 N n (by omega))
      · have h3 : j = N + 1 := by omega
        rw [h3, hFtop]
        exact hΦL2 0 n (by omega)
  -- the telescoping identity
  have hsumF : ∀ x : Vec d, ∑ j ∈ Finset.range (N + 1 + 1), F j x = w.grad x := by
    intro x
    have hlow : ∀ j ∈ Finset.range N, F j x =
        (fun i : ℕ => (Φ i).toH1Function.grad x) (j + 1) -
          (fun i : ℕ => (Φ i).toH1Function.grad x) j := by
      intro j hj
      rw [hF, ite_eq_left (Finset.mem_range.mp hj)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_congr rfl hlow,
      Finset.sum_range_sub (fun i : ℕ => (Φ i).toH1Function.grad x) N, hFmidx, hFtopx]
    abel
  -- the splitting inequality
  have hmemF : ∀ j ∈ Finset.range (N + 1 + 1), MemVectorL2 (openCubeAtScale z n) (F j) := by
    intro j hj
    exact hFL2 j (by have := Finset.mem_range.mp hj; omega)
  have htri := sqrt_meanSquareOscillationVecOn_finsetSum_le_of_memVectorL2
    (volume_openCubeAtScale_ne_top z n) (volume_openCubeAtScale_toReal_pos z n)
    (Finset.range (N + 1 + 1)) hmemF cen
  have hfun : (fun x => ∑ j ∈ Finset.range (N + 1 + 1), F j x) = w.grad := by
    funext x
    exact hsumF x
  rw [hfun] at htri
  have hsumS : ∑ j ∈ Finset.range (N + 1 + 1),
      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n) (F j) (cen j))
      = ∑ j ∈ Finset.range (N + 1 + 1), S j :=
    Finset.sum_congr rfl fun j _ => (hS j).symm
  rw [hsumS, Finset.sum_range_succ, Finset.sum_range_succ] at htri
  -- the recentred shape of the summands
  obtain ⟨hp, hPh0eq, hmain⟩ :=
    @oscillationNestedAssembly_comparisonBounds1 (d) (C₀) (hC₀nn) (hdec) (ρ) (hρdef) (hρnn) (hρ1)
      (A) (hAnn) (hA1) (hA2) (z) (n) (N) (hN) (w) (M) (Φ) (hΦ) (hΦL2) (hwL2) (E) (hE) (hEnn) (Ph)
        (hPh) (F) (cen) (hcen) (S) (hS) (hFlow) (hFmid) (hFtop) (hFL2) (htri)
  rw [hPh N, hPh0eq] at hmain
  -- the final arithmetic
  obtain ⟨Q, hQdef⟩ : ∃ r : ℝ, Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
      (openCubeAtScale z (n + (N : ℤ))) w.grad) = r := ⟨_, rfl⟩
  rw [hQdef] at hmain ⊢
  have hQnn : 0 ≤ Q := by
    rw [← hQdef]
    exact Real.sqrt_nonneg _
  have hq : (0 : ℝ) ≤ (3 : ℝ) ^ n * M := mul_nonneg (zpow_three_pos n).le hM
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℕ) ≤ N := by omega
    exact_mod_cast h1
  have hstep1 : A * (3 : ℝ) ^ (-(N : ℤ)) * Q
      ≤ Kb * (Real.sqrt (d : ℝ) + 1) * (3 : ℝ) ^ (-(N : ℤ)) * Q := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (hp N).le) hQnn
    linarith only [hAKb, mul_nonneg hKbnn hsd]
  have hc1 : A * (1 + 3 * ρ) * (N : ℝ) + A + 2 ≤ Kb * (N : ℝ) := by
    rw [hKbdef]
    linarith only [hAnn, mul_nonneg (by linarith only [hAnn] : (0 : ℝ) ≤ 2 * A + 2)
      (by linarith only [hNr] : (0 : ℝ) ≤ (N : ℝ) - 1)]
  have hstep2 : (A * (1 + 3 * ρ) * (N : ℝ) + A + 2) *
      ((3 : ℝ) ^ n * (Real.sqrt (d : ℝ) * M))
      ≤ Kb * (Real.sqrt (d : ℝ) + 1) * (N : ℝ) * ((3 : ℝ) ^ n * M) := by
    have hrw : (A * (1 + 3 * ρ) * (N : ℝ) + A + 2) *
        ((3 : ℝ) ^ n * (Real.sqrt (d : ℝ) * M))
        = ((A * (1 + 3 * ρ) * (N : ℝ) + A + 2) * Real.sqrt (d : ℝ)) *
          ((3 : ℝ) ^ n * M) := by ring
    rw [hrw]
    refine mul_le_mul_of_nonneg_right ?_ hq
    have hc2 : (A * (1 + 3 * ρ) * (N : ℝ) + A + 2) * Real.sqrt (d : ℝ)
        ≤ Kb * (N : ℝ) * Real.sqrt (d : ℝ) := mul_le_mul_of_nonneg_right hc1 hsd
    linarith only [hc2, mul_nonneg hKbnn (by linarith only [hNr] : (0 : ℝ) ≤ (N : ℝ))]
  linarith only [hmain, hstep1, hstep2]


/-- **The nested-recentring display in the printed norm form.**

The same estimate with the coarse term written as the normalized `L^2` norm of
`grad w` on the coarse cube, which is literally the right-hand side of
`e.nablaw.oscillations`:

```
  || grad w - (grad w)_{z+cu_n} ||_{L2bar (z+cu_n)}
    <= C(d) 3^{-N} || grad w ||_{L2bar (z+cu_{n+N})} + C(d) N 3^n M .
```

It follows from the oscillation form by mean recentring, the oscillation being
the deviation from the average and the norm the deviation from the origin. -/
theorem exists_gradient_oscillation_nested_telescope_norm (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (n : ℤ) (N : ℕ), d + 3 ≤ N →
      ∀ (w : H1Function (openCubeAtScale z (n + (N : ℤ)))) (G : Vec d → Vec d) (M : ℝ),
        0 ≤ M → (∀ i : Fin d, Differentiable ℝ fun y => G y i) →
        (∀ x ∈ openCubeAtScale z (n + (N : ℤ)), ∀ i : Fin d,
          ‖fderiv ℝ (fun y => G y i) x‖ ≤ M) →
        (∀ ψ : H10Function (openCubeAtScale z (n + (N : ℤ))),
          ∫ x in openCubeAtScale z (n + (N : ℤ)),
              vecDot (w.grad x) (ψ.toH1Function.grad x) ∂volume =
            ∫ x in openCubeAtScale z (n + (N : ℤ)),
              vecDot (G x) (ψ.toH1Function.grad x) ∂volume) →
          Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n) w.grad)
            ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                  (openCubeAtScale z (n + (N : ℤ))) w.grad 0)
              + C * (N : ℝ) * ((3 : ℝ) ^ n * M) := by
  obtain ⟨C, hCnn, hC⟩ := exists_gradient_oscillation_nested_telescope hd
  refine ⟨C, hCnn, ?_⟩
  intro z n N hN w G M hM hGdiff hGbound hw
  refine le_trans (hC z n N hN w G M hM hGdiff hGbound hw) ?_
  have hosc :
      Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
          (openCubeAtScale z (n + (N : ℤ))) w.grad)
        ≤ Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
          (openCubeAtScale z (n + (N : ℤ))) w.grad 0) :=
    sqrt_meanSquareOscillationVecOn_le_sqrt_meanSquareDeviationVecOn_of_memVectorL2
      (volume_openCubeAtScale_ne_top z _) (volume_openCubeAtScale_toReal_pos z _)
      w.grad_memVectorL2 0
  have hfac : (0 : ℝ) ≤ C * (3 : ℝ) ^ (-(N : ℤ)) :=
    mul_nonneg hCnn (zpow_pos (by norm_num) _).le
  have hstep := mul_le_mul_of_nonneg_left hosc hfac
  linarith only [hstep]


end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
