/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NonKahlerLocus

/-!
# Adding a positive multiple of a Kähler form to a Kähler current

Source: Copy-4, `sec:nK` (`transcendental-nakamaye-copy4-20260911`); CT22,
Section 2 (the inclusion `E_nn(α) ⊆ E_nK(α)`).

The Kähler cone of a fixed complex manifold is a convex cone: a sum of two
Hermitian forms and a positive multiple of a Hermitian form are Hermitian, and
closedness and type `(1,1)` are already carried by `ClosedRealOneOneForm`.  So a
`KahlerBackground` can be added and positively rescaled.

The consumer is `KahlerCurrent.addSmulKahler`: if `T = θ + ddᶜu` is a Kähler
current in `α` dominating the Kähler form `ω'`, then, for `c > 0`,
`T + cω = (θ + cω) + ddᶜu` is a Kähler current in `α + c{ω}` dominating
`ω' + cω`, **with the same potential**, hence with the same Lelong numbers.
This is the only input of `E_nn(α) ⊆ E_nK(α)`.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ## The Kähler cone is a convex cone -/

theorem isOneOne_add {a b : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsOneOne a) (hb : IsOneOne b) : IsOneOne (a + b) := by
  intro u v
  simp only [ContinuousAlternatingMap.add_apply, ha u v, hb u v]

theorem isOneOne_smul {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (c : ℝ)
    (ha : IsOneOne a) : IsOneOne (c • a) := by
  intro u v
  simp only [ContinuousAlternatingMap.smul_apply, ha u v]

theorem isStrictlyPositive_add {a b : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    IsStrictlyPositive (a + b) := by
  intro u hu
  simpa only [ContinuousAlternatingMap.add_apply] using add_pos (ha u hu) (hb u hu)

theorem isStrictlyPositive_smul {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} {c : ℝ}
    (hc : 0 < c) (ha : IsStrictlyPositive a) : IsStrictlyPositive (c • a) := by
  intro u hu
  simpa only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] using
    mul_pos hc (ha u hu)

namespace PositiveClasses

open PositiveClasses

/-- The sum of two Kähler backgrounds. -/
def KahlerBackground.add (a b : KahlerBackground n M) : KahlerBackground n M where
  form := a.form + b.form
  isKahler := by
    refine ⟨fun e z hz => ?_, (a.form + b.form).property.1⟩
    exact ⟨isOneOne_add (a.isKahler.1 e z hz).1 (b.isKahler.1 e z hz).1,
      isStrictlyPositive_add (a.isKahler.1 e z hz).2 (b.isKahler.1 e z hz).2⟩

@[simp] theorem KahlerBackground.add_form (a b : KahlerBackground n M) :
    (a.add b).form = a.form + b.form := rfl

/-- A positive multiple of a Kähler background. -/
def KahlerBackground.smul {c : ℝ} (hc : 0 < c) (a : KahlerBackground n M) :
    KahlerBackground n M where
  form := c • a.form
  isKahler := by
    refine ⟨fun e z hz => ?_, (c • a.form).property.1⟩
    exact ⟨isOneOne_smul c (a.isKahler.1 e z hz).1,
      isStrictlyPositive_smul hc (a.isKahler.1 e z hz).2⟩

@[simp] theorem KahlerBackground.smul_form {c : ℝ} (hc : 0 < c)
    (a : KahlerBackground n M) : (KahlerBackground.smul hc a).form = c • a.form := rfl

end PositiveClasses

namespace NonKahlerLocus

open PositiveClasses NonKahlerLocus

/-- **A Kähler current stays a Kähler current after adding `cω`, with the same
potential.**  `T + cω` lies in `α + c{ω}` and dominates `ω' + cω`. -/
def KahlerCurrent.addSmulKahler {alpha : RealBottChern n M}
    (T : KahlerCurrent alpha) (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) :
    KahlerCurrent (alpha + c • RealBottChern.ofRepresentative omega.form) where
  representative := T.representative + c • omega.form
  represents := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
      T.represents]
  potential := T.potential
  lowerBound := T.lowerBound.add (KahlerBackground.smul hc omega)
  strictlyPsh := by
    have hform : T.representative + c • omega.form -
        (T.lowerBound.add (KahlerBackground.smul hc omega)).form =
        T.representative - T.lowerBound.form := by
      rw [KahlerBackground.add_form, KahlerBackground.smul_form]
      abel
    rw [hform]
    exact T.strictlyPsh

@[simp] theorem KahlerCurrent.addSmulKahler_potential {alpha : RealBottChern n M}
    (T : KahlerCurrent alpha) (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) :
    (T.addSmulKahler omega hc).potential = T.potential := rfl

end NonKahlerLocus

end

end SGPT.Foundations.Analysis.FirstPass
