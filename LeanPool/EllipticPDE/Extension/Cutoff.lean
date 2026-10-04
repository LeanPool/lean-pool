/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.C1Test
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


/-!
# A one-sided cutoff along one coordinate

The extension by reflection is proved by testing strictly inside the half space and letting the
excluded slab shrink. The cutoff that excludes it is a function of the `j`-th coordinate alone:
`slabCut j ε` vanishes for `xⱼ ≤ ε` and is `1` for `xⱼ ≥ 2ε`, so a test function multiplied by
it is supported in the open half space.

Two properties are what the limit needs. The partial derivatives along the interface vanish
identically, so those directions leave no boundary term. The remaining one is bounded by `C/ε`
and supported in the slab, which is what the odd part of the reflection cancels against.

## Main declarations

* `EllipticPdes.Extension.slabCut`: the cutoff.
* `EllipticPdes.Extension.slabCut_eq_zero`, `EllipticPdes.Extension.slabCut_eq_one`: its values
  on the slab and beyond it.
* `EllipticPdes.Extension.partialD_slabCut_of_ne`: it is constant along the interface.
* `EllipticPdes.Extension.norm_partialD_slabCut_le`: the `C/ε` bound.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- The one-sided profile: `0` for `t ≤ 1`, `1` for `t ≥ 2`, smooth, with values in `[0, 1]`. -/
def stepProfile : ℝ → ℝ := fun t => Real.smoothTransition (t - 1)

theorem contDiff_stepProfile : ContDiff ℝ (⊤ : ℕ∞) stepProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem stepProfile_eq_zero {t : ℝ} (ht : t ≤ 1) : stepProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem stepProfile_eq_one {t : ℝ} (ht : 2 ≤ t) : stepProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem stepProfile_nonneg (t : ℝ) : 0 ≤ stepProfile t := Real.smoothTransition.nonneg _

theorem stepProfile_le_one (t : ℝ) : stepProfile t ≤ 1 := Real.smoothTransition.le_one _

/-- The profile is constant below the slab, so its derivative vanishes there. -/
theorem deriv_stepProfile_eq_zero_of_lt {t : ℝ} (ht : t < 1) : deriv stepProfile t = 0 := by
  have hev : stepProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds ht] with s hs using stepProfile_eq_zero hs.le
  rw [hev.deriv_eq, deriv_const]

/-- The profile is constant above the slab, so its derivative vanishes there. -/
theorem deriv_stepProfile_eq_zero_of_gt {t : ℝ} (ht : 2 < t) : deriv stepProfile t = 0 := by
  have hev : stepProfile =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [lt_mem_nhds ht] with s hs using stepProfile_eq_one hs.le
  rw [hev.deriv_eq, deriv_const]

/-- The profile is constant off `[1, 2]`, so its derivative is continuous with compact support
and therefore bounded. -/
theorem exists_bound_deriv_stepProfile : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv stepProfile t| ≤ C := by
  have hcs : HasCompactSupport (deriv stepProfile) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · exact deriv_stepProfile_eq_zero_of_lt h
    · exact deriv_stepProfile_eq_zero_of_gt h
  have hc : Continuous (deriv stepProfile) :=
    contDiff_stepProfile.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  exact ⟨C, le_trans (abs_nonneg _) (by simpa using hC 0), fun t => by simpa using hC t⟩

/-! ### The cutoff on the space -/

/-- **Cutoff excluding the slab `xⱼ ≤ ε`.** It depends on the `j`-th coordinate alone. -/
def slabCut (j : Fin d) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := stepProfile (x j / ε)

theorem contDiff_slabCut (j : Fin d) (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (slabCut j ε) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => x j / ε) :=
    ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff).div_const ε
  exact contDiff_stepProfile.comp h

theorem slabCut_nonneg (j : Fin d) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ slabCut j ε x := stepProfile_nonneg _

theorem slabCut_le_one (j : Fin d) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    slabCut j ε x ≤ 1 := stepProfile_le_one _

/-- On the excluded slab the cutoff vanishes. -/
theorem slabCut_eq_zero {j : Fin d} {ε : ℝ} (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x j ≤ ε) : slabCut j ε x = 0 :=
  stepProfile_eq_zero (by rw [div_le_one hε]; exact hx)

/-- Beyond the slab the cutoff is `1`. -/
theorem slabCut_eq_one {j : Fin d} {ε : ℝ} (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin d)}
    (hx : 2 * ε ≤ x j) : slabCut j ε x = 1 :=
  stepProfile_eq_one (by rw [le_div_iff₀ hε]; linarith)

/-- The derivative of the cutoff, in every direction. -/
theorem partialD_slabCut {j : Fin d} {ε : ℝ} (_hε : 0 < ε) (k : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (slabCut j ε) x
      = deriv stepProfile (x j / ε) * ((if j = k then (1 : ℝ) else 0) / ε) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) => y j / ε)
      = ⇑((1 / ε) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) := by
    funext y
    simp [div_eq_mul_inv, mul_comm]
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => y j / ε)
      ((1 / ε) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
    rw [hfun]
    exact ContinuousLinearMap.hasFDerivAt _
  have hc : HasDerivAt stepProfile (deriv stepProfile (x j / ε)) (x j / ε) :=
    (contDiff_stepProfile.differentiable (by simp) _).hasFDerivAt.hasDerivAt
  have hcomp : HasFDerivAt (slabCut j ε)
      ((deriv stepProfile (x j / ε)) •
        ((1 / ε) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x :=
    hc.comp_hasFDerivAt x hL
  rw [partialD, hcomp.fderiv]
  have hval : (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (EuclideanSpace.single k (1 : ℝ)) = if j = k then (1 : ℝ) else 0 := by
    simp [PiLp.single_apply]
  simp only [_root_.smul_apply, smul_eq_mul, hval]
  ring

/-- **Constancy of the cutoff along the interface.** -/
theorem partialD_slabCut_of_ne {j : Fin d} {ε : ℝ} (hε : 0 < ε) {k : Fin d} (hk : k ≠ j)
    (x : EuclideanSpace ℝ (Fin d)) : partialD k (slabCut j ε) x = 0 := by
  rw [partialD_slabCut hε k x, ite_eq_right (Ne.symm hk)]
  simp

/-- **Bound `C/ε` on the remaining partial derivative.** -/
theorem norm_partialD_slabCut_le {j : Fin d} {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC : ∀ t, |deriv stepProfile t| ≤ C) (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    |partialD k (slabCut j ε) x| ≤ C / ε := by
  rw [partialD_slabCut hε k x, abs_mul]
  have h1 : |(if j = k then (1 : ℝ) else 0) / ε| ≤ 1 / ε := by
    rw [abs_div, abs_of_pos hε]
    gcongr
    split <;> simp
  have h0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 0)
  calc |deriv stepProfile (x j / ε)| * |(if j = k then (1 : ℝ) else 0) / ε|
      ≤ C * (1 / ε) := mul_le_mul (hC _) h1 (abs_nonneg _) h0
    _ = C / ε := by ring

/-- **Support of the cutoff's derivative in the slab.** -/
theorem partialD_slabCut_eq_zero_of_gt {j : Fin d} {ε : ℝ} (hε : 0 < ε) (k : Fin d)
    {x : EuclideanSpace ℝ (Fin d)} (hx : 2 * ε < x j) : partialD k (slabCut j ε) x = 0 := by
  rw [partialD_slabCut hε k x, deriv_stepProfile_eq_zero_of_gt, zero_mul]
  rw [lt_div_iff₀ hε]
  linarith

/-- **Vanishing of the cutoff off the open half space**, so a test function multiplied by it is
supported where the hypothesis of a weak gradient applies. -/
theorem tsupport_mul_slabCut_subset {j : Fin d} {ε : ℝ} (hε : 0 < ε)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    tsupport (fun x => slabCut j ε x * ψ x) ⊆ {x : EuclideanSpace ℝ (Fin d) | 0 < x j} := by
  have hsub : Function.support (fun x => slabCut j ε x * ψ x)
      ⊆ {x : EuclideanSpace ℝ (Fin d) | ε ≤ x j} := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_le] at hcon
    refine hx ?_
    change slabCut j ε x * ψ x = 0
    rw [slabCut_eq_zero hε hcon.le, zero_mul]
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin d) | ε ≤ x j} :=
    isClosed_le continuous_const ((EuclideanSpace.proj j :
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous)
  exact fun x hx => lt_of_lt_of_le hε (closure_minimal hsub hclosed hx)

end EllipticPdes.Extension
