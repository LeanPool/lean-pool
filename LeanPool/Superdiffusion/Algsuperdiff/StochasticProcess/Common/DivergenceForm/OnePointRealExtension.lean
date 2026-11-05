/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointExtension

/-!
# OnePointRealExtension

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Zero extension of a real observable to the one-point compactification.
-/

/-!
# Real observables on the one-point carrier

The conservative model semigroup lives on `OnePoint X`, and observables of the
live space are read there by extending them by `0` at the point at infinity.
The library provides this extension for `ℝ≥0∞`-valued observables
(`onePointLiveExtension`); the real-valued version used by the comparison on
bounded measurable data is provided here, with the same measurability proof.

The statements are generic and belong with the kernel layer of the
MarkovProcess library, which is left unmodified here.
-/

namespace DivergenceFormProcess.Form

open MarkovProcess Topology

variable {X : Type*}

/-- Extend a real observable on the live space by zero at infinity. -/
def onePointRealExtension (f : X → ℝ) : OnePoint X → ℝ :=
  OnePoint.rec 0 f

@[simp] theorem onePointRealExtension_coe (f : X → ℝ) (x : X) :
    onePointRealExtension f (x : OnePoint X) = f x := rfl

@[simp] theorem onePointRealExtension_infty (f : X → ℝ) :
    onePointRealExtension f OnePoint.infty = 0 := rfl

theorem abs_onePointRealExtension_le {f : X → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ y, |f y| ≤ D) (z : OnePoint X) :
    |onePointRealExtension f z| ≤ D := by
  induction z using OnePoint.rec with
  | infty => simpa using hD
  | coe x => simpa using hfD x

section Measurability

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Zero extension of a real observable is measurable. -/
theorem measurable_onePointRealExtension {f : X → ℝ} (hf : Measurable f) :
    Measurable (onePointRealExtension f) := by
  intro A hA
  by_cases hzero : (0 : ℝ) ∈ A
  · have hpre : onePointRealExtension f ⁻¹' A =
        ((↑) : X → OnePoint X) '' (f ⁻¹' A) ∪ {OnePoint.infty} := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp only [Set.mem_preimage, onePointRealExtension_infty, hzero,
          Set.mem_union, OnePoint.infty_notMem_image_coe, Set.mem_singleton_iff,
          or_true]
      | coe x => simp only [Set.mem_preimage, onePointRealExtension_coe,
          Set.mem_union, Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right,
          OnePoint.coe_ne_infty, Set.mem_singleton_iff, or_false]
    rw [hpre]
    exact (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr
      (hf hA)).union OnePoint.isClosed_infty.measurableSet
  · have hpre : onePointRealExtension f ⁻¹' A =
        ((↑) : X → OnePoint X) '' (f ⁻¹' A) := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp only [Set.mem_preimage, onePointRealExtension_infty, hzero,
          OnePoint.infty_notMem_image_coe]
      | coe x => simp only [Set.mem_preimage, onePointRealExtension_coe,
          Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right]
    rw [hpre]
    exact OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr
      (hf hA)

end Measurability

end DivergenceFormProcess.Form
