/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicMollifyWeyl
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayGap

/-!
# OscillationDecayWeak

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The arbitrary-gap oscillation decay for a *weakly* harmonic function

`OscillationDecayGap` proves the arbitrary-gap decay
`|| grad u - (grad u)_{z + cu_n} ||_{L2bar} <= C (d) 3^{-k} || grad u - c ||`
for a function `u` that is **smooth** and harmonic on the coarse cube.  The
object the argument downstream actually produces is not smooth: a harmonic
replacement obtained from an `H^1_0` solve is only `H^1`, hence only weakly
harmonic in the sense of `HarmonicWeak`, and `HarmonicWeak` cannot bootstrap its
own regularity.

This module removes that mismatch.  `HarmonicMollifyWeyl` provides the interior
smooth representative of a weakly harmonic function; combined with the proved
decay it yields the same estimate for the smooth representative, on cubes one
triadic scale inside the harmonicity cube.

## What is lost, and why

The mollification consumes one triadic scale: the smooth representative is
produced on `z + cu_{n+k-1}`, not on `z + cu_{n+k}`, because the mollifying
kernel needs room.  Two things follow.

* The gap restriction becomes `k >= d + 3` instead of `k >= d + 2`: the proved
  estimate is applied with gap `k - 1`.
* The right-hand side measures the deviation on `z + cu_{n+k-1}`.  The decay
  factor is still written `3^{-k}`; the single lost scale is absorbed into the
  dimensional constant (it multiplies it by `3`).

The conclusion is stated for the smooth representative `v`, together with
`v = u` almost everywhere on `z + cu_{n+k-1}`.  That is the usable form: all the
quantities in the estimate are integrals of `grad v`, and a consumer holding `u`
in `H^1` identifies `grad v` with the weak gradient of `u` from the
almost-everywhere equality.  Stating the estimate for `euclideanGradient u`
directly would be vacuous, since the pointwise `fderiv` of a merely `H^1`
function carries no information.

## Portability

This file depends only on **Mathlib** and on **CoarseGraining**
(`Homogenization.*`) and on other files of this same harmonic/oscillation
layer.  It mentions no object of the manuscript: no model, no cutoff, no shell,
no corrector.  It is intended to be portable into CoarseGraining by a single
mechanical namespace rename.

## Contents

* `euclideanClosedBall_subset_openCubeAtScale_of_succ` -- the one triadic scale
  of room: a Euclidean ball of radius `3^p` around a point of `z + cu_p` sits
  inside `z + cu_{p+1}`.
* `exists_gradient_oscillation_gap_decay_of_isWeaklyHarmonicOn` -- **the decay
  for a weakly harmonic function**, through its smooth representative.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

theorem euclideanClosedBall_subset_openCubeAtScale_of_succ {d : ℕ} {z : Vec d} {p : ℤ}
    {x : Vec d} (hx : x ∈ openCubeAtScale z p) :
    euclideanClosedBall x ((3 : ℝ) ^ p) ⊆ openCubeAtScale z (p + 1) := by
  intro y hy
  have hP : (0 : ℝ) < (3 : ℝ) ^ p := zpow_three_pos p
  have hyx : euclideanNorm (y - x) ≤ (3 : ℝ) ^ p :=
    (mem_euclideanClosedBall_iff_euclideanNorm_le hP.le).mp hy
  have hstep : (3 : ℝ) ^ (p + 1) = (3 : ℝ) ^ p * 3 :=
    zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) p
  rw [mem_openCubeAtScale_iff]
  intro i
  have h1 : |x i - z i| < (3 : ℝ) ^ p / 2 := (mem_openCubeAtScale_iff z p x).mp hx i
  have h2 : |y i - x i| ≤ (3 : ℝ) ^ p := by
    have hcoord : ‖(y - x) i‖ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) i
    have hle : ‖y - x‖ ≤ euclideanNorm (y - x) := norm_le_euclideanNorm _
    have hpi : (y - x) i = y i - x i := rfl
    rw [hpi, Real.norm_eq_abs] at hcoord
    linarith
  have h3 : |y i - z i| ≤ |y i - x i| + |x i - z i| := by
    have heq : y i - z i = (y i - x i) + (x i - z i) := by ring
    rw [heq]
    exact abs_add_le _ _
  rw [hstep]
  linarith

theorem exists_gradient_oscillation_gap_decay_of_isWeaklyHarmonicOn {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Vec d → ℝ, LocallyIntegrable u volume →
      ∀ (z : Vec d) (n : ℤ) (k : ℕ), d + 3 ≤ k →
        IsWeaklyHarmonicOn (openCubeAtScale z (n + (k : ℤ))) u →
        ∃ v : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
          (∀ᵐ x ∂volume, x ∈ openCubeAtScale z (n + (k : ℤ) - 1) → v x = u x) ∧
          ∀ c : Vec d,
            Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n)
                (euclideanGradient v))
              ≤ C * (3 : ℝ) ^ (-(k : ℤ)) *
                Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                  (openCubeAtScale z (n + (k : ℤ) - 1)) (euclideanGradient v) c) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  obtain ⟨C₀, hC₀nn, hdec⟩ := exists_gradient_oscillation_gap_decay hd
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro u hu z n k hk hw
  have hidx : n + (k : ℤ) - 1 + 1 = n + (k : ℤ) := by ring
  have hsub : ∀ x ∈ openCubeAtScale z (n + (k : ℤ) - 1),
      euclideanClosedBall x ((3 : ℝ) ^ (n + (k : ℤ) - 1))
        ⊆ openCubeAtScale z (n + (k : ℤ)) := by
    intro x hx
    have h := euclideanClosedBall_subset_openCubeAtScale_of_succ hx
    rwa [hidx] at h
  obtain ⟨v, hvs, hvae, hvlap⟩ := exists_contDiff_ae_eq_of_isWeaklyHarmonicOn
    (isOpen_openCubeAtScale z (n + (k : ℤ) - 1)) (zpow_three_pos (n + (k : ℤ) - 1)) hsub hu hw
  refine ⟨v, hvs, hvae, ?_⟩
  intro c
  have hkidx : n + ((k - 1 : ℕ) : ℤ) = n + (k : ℤ) - 1 := by omega
  have hbound := hdec v hvs z n (k - 1) (by omega)
    (fun x hx => hvlap x (by rwa [hkidx] at hx)) c
  rw [hkidx] at hbound
  have hexp : (3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) = 3 * (3 : ℝ) ^ (-(k : ℤ)) := by
    have h1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [h1, show -((k : ℤ) - 1) = 1 + -(k : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hexp] at hbound
  have hassoc : C₀ * (3 * (3 : ℝ) ^ (-(k : ℤ))) = 3 * C₀ * (3 : ℝ) ^ (-(k : ℤ)) := by ring
  rw [hassoc] at hbound
  exact hbound

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
