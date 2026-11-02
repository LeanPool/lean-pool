/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidualCorrectorExistence

/-!
# CorrectorComposed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The residual corrector at the boundary datum's affine lift, composed

* the residual bound `‖h - ℓ_h‖_{L^∞(W)} ≤ 2 d [∇h]_{C^{0,1/2}} (3^k/2)^{3/2}`
  (`AffineSplitLift.abs_sub_affineLift_volumeAverage_le`);
* the globally clamped `H¹` datum
  (`ResidualCorrectorExistence.exists_h1_clamp`), the carrier bridge from an
  `L^∞`-bound-on-`V` to the global bound CoarseGraining's truncation machinery
  wants;
* the corrector itself with both boundary bounds
  (`ResidualCorrectorExistence.exists_residualCorrector`), and the two-sided
  maximum principle (`BoundaryLaneMaxPrinciple.ae_abs_le_of_isWeaklyHarmonicOn`).

This module composes them into the single statement the boundary lane consumes:
on the anchor's own truncated window `V = (x+□_k) ∩ □_m`, the harmonic corrector
`w` carrying the datum `h - ℓ_h` exists and satisfies

```text
  ‖w‖_{L^∞(V)}  ≤  2 d [∇h]_{C^{0,1/2}(V)} (3^k/2)^{3/2} ,
```

which is the draft's `e.data.residual` display.

## What the hypotheses are, and where they come from (disclosed)

`HasGradientOn V h.toFun G` and `HolderSeminormBoundOn V (1/2) K G` are the
classical `C^{1,1/2}` half of the printed datum.  The frozen theorem's clause
(iv) supplies only `h ∈ H^{1+s}`, so these are **inputs** here, carried in the
statement and not derived; the module asserts nothing about their availability.
Everything else — convexity, nonemptiness, finiteness and positivity of the
window volume, the diameter bound — is discharged from `BoundaryLaneWindows`.

## References

* ABK26; the `C^{1,1/2}` datum.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book.Ch03 Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The residual level of the draft's `e.data.residual`, at the window
`(x+□_k) ∩ □_m`: `2 d [∇h]_{C^{0,1/2}} (3^k/2)^{3/2}`. -/
def affineResidualLevel (d : ℕ) (K : ℝ) (k : ℤ) : ℝ :=
  2 * (d : ℝ) * K * ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ)

theorem affineResidualLevel_nonneg (d : ℕ) {K : ℝ} (hK : 0 ≤ K) (k : ℤ) :
    0 ≤ affineResidualLevel d K k := by
  have hpow : (0 : ℝ) ≤ ((3 : ℝ) ^ k / 2) ^ (3 / 2 : ℝ) := by
    refine Real.rpow_nonneg ?_ _
    have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
    linarith only [h3]
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) * K :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hK
  rw [affineResidualLevel]
  exact mul_nonneg hd hpow

/-! ## 1. The residual bound on the truncated window -/

/-- **`e.data.residual` at the anchor's own window.**

The frozen theorem's boundary datum `h`, restricted to the truncated window `V
= (x+□_k) ∩ □_m`, differs from its affine lift at the average slope `(∇h)_V` by
at most `2 d K (3^k/2)^{3/2}` at every point of `V`. -/
theorem abs_sub_affineLift_le_affineResidualLevel {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) {f : Vec d → ℝ} {G : Vec d → Vec d}
    {K : ℝ} (hK : 0 ≤ K)
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : Support.HolderSeminormBoundOn (truncatedWindow x m k) (1 / 2 : ℝ) K G)
    {y : Vec d} (hy : y ∈ truncatedWindow x m k) :
    |f y - affineLift x (f x)
        (volumeAverageVec (truncatedWindow x m k) G) y| ≤
      affineResidualLevel d K k := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ k / 2 := by linarith only [h3]
  have hmain := abs_sub_affineLift_volumeAverage_le (f := f) (G := G)
    (convex_truncatedWindow x m k) (mem_truncatedWindow_self k hx) hy hK hr0
    (volume_truncatedWindow_pos k hx) (volume_truncatedWindow_lt_top x m k) hint hf hG
    (fun p hp => norm_sub_le_of_mem_truncatedWindow hp)
  rw [affineResidualLevel]
  exact hmain

/-! ## 2. The composed corrector -/

variable [NeZero d]

/-- **The residual corrector of the draft's item 2(ii), composed.**

On the anchor's truncated window `V = (x+□_k) ∩ □_m` there are an `H¹(V)` datum
`Ψ` agreeing on `V` with `h - ℓ_h` and a weakly harmonic `w` with

* `w - Ψ ∈ H¹₀(V)` (the Dirichlet condition `w = h - ℓ_h` on `∂V`), and
* `|w| ≤ 2 d K (3^k/2)^{3/2}` almost everywhere on `V`
  (the draft's `‖w‖_{L^∞(V)} ≤ C(d) 3^{3k/2} [∇h]_{C^{0,1/2}}`).

`Ψ` is the *clamped* datum: `h - ℓ_h` need not be globally bounded off `V`, and
CoarseGraining's truncation machinery asks for a global bound.  On `V` — the
only place the statement is read — `Ψ` and `h - ℓ_h` coincide, which is
recorded as the first clause.  Nothing else about `Ψ` is claimed. -/
theorem exists_residualCorrector_affineLift {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m))
    (h : H1Function (openCubeSet (originCube d m))) {G : Vec d → Vec d} {K : ℝ}
    (hK : 0 ≤ K)
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hgrad : HasGradientOn (truncatedWindow x m k) h.toFun G)
    (hG : Support.HolderSeminormBoundOn (truncatedWindow x m k) (1 / 2 : ℝ) K G) :
    ∃ Psi w : H1Function (truncatedWindow x m k),
      (∀ y ∈ truncatedWindow x m k, Psi.toFun y =
        h.toFun y - affineLift x (h.toFun x)
          (volumeAverageVec (truncatedWindow x m k) G) y) ∧
        IsWeaklyHarmonicOn (truncatedWindow x m k) w ∧
        MemH10 (truncatedWindow x m k) (fun y => w.toFun y - Psi.toFun y) ∧
        ∀ᵐ y ∂(volumeMeasureOn (truncatedWindow x m k)),
          |w.toFun y| ≤ affineResidualLevel d K k := by
  have hV : IsOpenBoundedConvexDomain (truncatedWindow x m k) :=
    isOpenBoundedConvexDomain_truncatedWindow x m k
  have : IsFiniteMeasure (volumeMeasureOn (truncatedWindow x m k)) :=
    hV.isFiniteMeasure_restrict_volume
  set A : Vec d := volumeAverageVec (truncatedWindow x m k) G with hA
  set Phi : H1Function (truncatedWindow x m k) :=
    h.restrict (isOpen_truncatedWindow x m k) (truncatedWindow_subset_domain x m k) -
      affineLiftH1 hV.isSobolevRegularDomain x (h.toFun x) A with hPhi
  have hPhival : ∀ y, Phi.toFun y = h.toFun y - affineLift x (h.toFun x) A y := by
    intro y
    rw [hPhi, H1Function.sub_toFun, affineLiftH1_toFun]
    rfl
  have hMnn : 0 ≤ affineResidualLevel d K k := affineResidualLevel_nonneg d hK k
  have hbound : ∀ y ∈ truncatedWindow x m k,
      |Phi.toFun y| ≤ affineResidualLevel d K k := by
    intro y hy
    rw [hPhival y, hA]
    exact abs_sub_affineLift_le_affineResidualLevel hx hK hint hgrad hG hy
  obtain ⟨Psi, hup, hlow, hagree⟩ := exists_h1_clamp hV Phi hMnn
  obtain ⟨w, hharm, hdiff, hbu, hbl⟩ :=
    exists_residualCorrector hV (truncatedWindow_nonempty k hx) Psi hup hlow
  refine ⟨Psi, w, fun y hy => ?_, hharm, hdiff, ?_⟩
  · rw [hagree y (hbound y hy), hPhival y]
  · exact ae_abs_le_of_isWeaklyHarmonicOn hV hharm hbu hbl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
