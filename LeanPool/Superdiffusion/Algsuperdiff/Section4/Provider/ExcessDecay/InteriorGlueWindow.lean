/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlue

/-!
# InteriorGlueWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Clause (iv) restricted to a sub-window

The anchor states its clause-(iv) force data on the **whole** cube `□_m`:
`g ∈ L²(⨍_{□_m})` and `[g]_{H^s(□_m)} < ∞`, in the volume-normalized and
Gagliardo-normalized carriers.  Every proved coarse-graining estimate is read
on a sub-window (the child `x + □_n`, or the parent `z + □_{n+2}`).  This
module supplies the restriction, unconditionally:

```text
  B ⊆ A ,  0 < |A| < ∞ ,  0 < |B|   ⟹   L²(⨍_A) ⊆ L²(⨍_B) ,
                                        H^s(A) ⊆ H^s(B) .
```

Both are the same two-line measure argument: the normalized measures differ from
the restricted Lebesgue measures by finite nonzero scalars, and restricted
Lebesgue measure is monotone in the set.  The Gagliardo case is the *product*
restriction `(⨍_B ⊗ vol|_B) = |B|^{-1} · (vol ⊗ vol)|_{B×B}`, whose set
monotonicity is again `Measure.restrict_mono`.

No estimate is claimed and no constant appears: these are membership
transports.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (clause (iv)).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-! ## 1. Volume facts for the anchor's windows -/

/-- The open realization of a triadic cube has finite volume. -/
theorem volume_openCubeSet_ne_top (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ ⊤ := (volume_openCubeSet_lt_top Q).ne

/-- The open realization of a triadic cube has positive volume. -/
theorem volume_openCubeSet_ne_zero (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ 0 := by
  intro hzero
  have htoReal : (volume (cubeSet Q)).toReal = 0 := by
    rw [← volume_openCubeSet_eq_volume_cubeSet, hzero]
    simp
  rw [volume_cubeSet_toReal] at htoReal
  exact (cubeVolume_pos Q).ne' htoReal

/-- Translates of an open cube keep its volume. -/
theorem volume_image_add_openCubeSet (z : Vec d) (Q : TriadicCube d) :
    volume ((fun y => z + y) '' openCubeSet Q) = volume (openCubeSet Q) := by
  rw [image_add_eq_translateSet z (openCubeSet Q), volume_translateSet_eq]

theorem volume_image_add_openCubeSet_ne_zero (z : Vec d) (Q : TriadicCube d) :
    volume ((fun y => z + y) '' openCubeSet Q) ≠ 0 := by
  rw [volume_image_add_openCubeSet z Q]
  exact volume_openCubeSet_ne_zero Q

/-! ## 2. The volume-normalized restriction -/

/-- **`L²(⨍_A) ⊆ L²(⨍_B)` for `B ⊆ A`.**  Exact: no constant, no measurability
side condition. -/
theorem memLp_normalizedVolumeMeasureOn_subset {p : ℝ≥0∞} {A B : Set (Vec d)}
    (hAB : B ⊆ A) (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ⊤)
    (hB0 : volume B ≠ 0) {f : Vec d → E}
    (h : MemLp f p (Support.normalizedVolumeMeasureOn A)) :
    MemLp f p (Support.normalizedVolumeMeasureOn B) := by
  rw [Support.normalizedVolumeMeasureOn_def] at h
  have hres : MemLp f p (volume.restrict A) := by
    have hsm := h.smul_measure (c := volume A) hAtop
    rwa [smul_smul, ENNReal.mul_inv_cancel hA0 hAtop, one_smul] at hsm
  have hresB : MemLp f p (volume.restrict B) :=
    hres.mono_measure (Measure.restrict_mono hAB le_rfl)
  rw [Support.normalizedVolumeMeasureOn_def]
  exact hresB.smul_measure (ENNReal.inv_ne_top.mpr hB0)

/-! ## 3. The Gagliardo restriction -/

/-- The Gagliardo measure of a window, as a scalar multiple of a restricted
product measure. -/
theorem normalizedGagliardoMeasureOn_eq_smul_restrict (A : Set (Vec d)) :
    Support.normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
  rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
    Measure.prod_smul_left, Measure.prod_restrict]

/-- **`H^s(A) ⊆ H^s(B)` for `B ⊆ A`**, at the level of the Gagliardo kernel's
`L²` membership. -/
theorem memLp_normalizedGagliardoMeasureOn_subset {p : ℝ≥0∞} {A B : Set (Vec d)}
    (hAB : B ⊆ A) (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ⊤)
    (hB0 : volume B ≠ 0) {f : Vec d × Vec d → E}
    (h : MemLp f p (Support.normalizedGagliardoMeasureOn A)) :
    MemLp f p (Support.normalizedGagliardoMeasureOn B) := by
  rw [normalizedGagliardoMeasureOn_eq_smul_restrict] at h
  have hres : MemLp f p ((volume.prod volume).restrict (A ×ˢ A)) := by
    have hsm := h.smul_measure (c := volume A) hAtop
    rwa [smul_smul, ENNReal.mul_inv_cancel hA0 hAtop, one_smul] at hsm
  have hsq : (B ×ˢ B : Set (Vec d × Vec d)) ⊆ A ×ˢ A := Set.prod_mono hAB hAB
  have hresB : MemLp f p ((volume.prod volume).restrict (B ×ˢ B)) :=
    hres.mono_measure (Measure.restrict_mono hsq le_rfl)
  rw [normalizedGagliardoMeasureOn_eq_smul_restrict]
  exact hresB.smul_measure (ENNReal.inv_ne_top.mpr hB0)

/-! ## 4. Clause (iv) at the anchor's child window -/

/-- **The anchor's clause-(iv) `L²` datum, read at a translated sub-cube.** -/
theorem memLp_two_child_of_clause_iv {n m : ℤ} {x : Vec d} {g : Vec d → Vec d}
    (hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m))
    (hg : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m)))) :
    MemLp g 2 (Support.normalizedVolumeMeasureOn
      ((fun y => x + y) '' openCubeSet (originCube d n))) :=
  memLp_normalizedVolumeMeasureOn_subset hsub
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero x (originCube d n)) hg

/-- **The anchor's clause-(iv) Gagliardo datum, read at a translated
sub-cube.** -/
theorem memLp_two_gagliardo_child_of_clause_iv {n m : ℤ} {x : Vec d} {s : ℝ}
    {g : Vec d → Vec d}
    (hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m))
    (hg : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n))) :=
  memLp_normalizedGagliardoMeasureOn_subset hsub
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero x (originCube d n)) hg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
