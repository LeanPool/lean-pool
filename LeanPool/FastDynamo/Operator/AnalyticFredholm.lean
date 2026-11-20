/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.FredholmIsolation
public import Mathlib.Analysis.Analytic.Order

/-!
# Analytic Fredholm foundations

This file isolates the generic complex-analytic input which is available in
Mathlib without postulating an analytic Fredholm theorem.

For a Banach-space operator family we prove:

* equivalence of Mathlib's two notions of invertibility for continuous linear
  endomorphisms;
* openness of the invertible parameter locus;
* analyticity of the inverse family on that locus;
* the families `1 - K(z)` and their analyticity;
* codiscreteness of the invertible locus once a scalar analytic reduction (the
  finite-dimensional determinant produced in the classical analytic-Fredholm
  proof) has been constructed.

The reduction in the last item is taken as data, not postulated: Mathlib 4.35.0
constructs it for no general compact analytic family.  In this development it
is built for compact analytic pencils on a Hilbert space in
`AnalyticFredholmContinuation`, from the determinant criterion of
`FiniteDimensionalDeterminant`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Set Topology

namespace AnalyticFredholm

universe u

variable {X : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-! ## The invertible locus and its analytic inverse -/

/-- Parameters at which an endomorphism-valued family is invertible. -/
def invertibleSet (F : ℂ → (X →L[ℂ] X)) : Set ℂ :=
  {z | (F z).IsInvertible}

/-- Parameters at which an endomorphism-valued family is not invertible. -/
def noninvertibleSet (F : ℂ → (X →L[ℂ] X)) : Set ℂ :=
  (invertibleSet F)ᶜ

omit [CompleteSpace X] in
/-- For continuous linear endomorphisms, the bundled-equivalence notion of
invertibility agrees with being a unit of the endomorphism ring. -/
theorem isUnit_iff_isInvertible {T : X →L[ℂ] X} :
    IsUnit T ↔ T.IsInvertible := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨ContinuousLinearEquiv.ofUnit u, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨ContinuousLinearEquiv.toUnit e, rfl⟩

/-- Invertibility persists in a neighborhood of an invertible parameter. -/
theorem eventually_isInvertible {F : ℂ → (X →L[ℂ] X)} {z : ℂ}
    (hF : ContinuousAt F z) (hz : (F z).IsInvertible) :
    ∀ᶠ w in nhds z, (F w).IsInvertible := by
  have hopen : IsOpen {T : X →L[ℂ] X | IsUnit T} := Units.isOpen
  have hmem : {T : X →L[ℂ] X | IsUnit T} ∈ nhds (F z) :=
    hopen.mem_nhds ((isUnit_iff_isInvertible).2 hz)
  filter_upwards [hF hmem] with w hw
  exact isUnit_iff_isInvertible.mp hw

/-- The inverse of an analytic endomorphism-valued family is analytic at every
invertible parameter. -/
theorem analyticAt_inverse {F : ℂ → (X →L[ℂ] X)} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hz : (F z).IsInvertible) :
    AnalyticAt ℂ (fun w ↦ (F w).inverse) z := by
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  have hinv : AnalyticAt ℂ (@Ring.inverse (X →L[ℂ] X) _) (F z) :=
    _root_.analyticAt_inverse (𝕜 := ℂ)
      (A := X →L[ℂ] X) (IsUnit.unit (isUnit_iff_isInvertible.mpr hz))
  exact hinv.comp hF

/-! ## Identity minus a compact analytic family -/

/-- The operator family `1 - K(z)` used in the compact Fredholm
factorization. -/
def compactPencil (K : ℂ → (X →L[ℂ] X)) (z : ℂ) : X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X - K z

omit [CompleteSpace X] in
/-- Pointwise action of the compact pencil: `(1 - K(z)) x = x - K(z) x`. -/
@[simp] theorem compactPencil_apply (K : ℂ → (X →L[ℂ] X)) (z : ℂ) (x : X) :
    compactPencil K z x = x - K z x :=
  rfl

omit [CompleteSpace X] in
/-- Analyticity is preserved when passing from `K(z)` to `1 - K(z)`. -/
theorem analyticAt_compactPencil {K : ℂ → (X →L[ℂ] X)} {z : ℂ}
    (hK : AnalyticAt ℂ K z) : AnalyticAt ℂ (compactPencil K) z := by
  exact analyticAt_const.sub hK

/-! ## The exact finite-dimensional reduction boundary -/

/-- A scalar analytic reduction for an operator family.  In the classical
analytic Fredholm proof, `determinant` is the determinant of the
finite-dimensional Schur complement.  Keeping this as data precisely exposes
the one construction Mathlib 4.35.0 does not supply. -/
structure ScalarReduction (F : ℂ → (X →L[ℂ] X)) (U : Set ℂ) where
  /-- Scalar determinant of the finite-dimensional reduction. -/
  determinant : ℂ → ℂ
  /-- The determinant is analytic on the connected parameter domain. -/
  analyticOnNhd : AnalyticOnNhd ℂ determinant U
  /-- Characterization of operator invertibility on the reduction domain. -/
  isInvertible_iff_ne_zero : ∀ z ∈ U, (F z).IsInvertible ↔ determinant z ≠ 0

namespace ScalarReduction

variable {F : ℂ → (X →L[ℂ] X)} {U : Set ℂ}

omit [CompleteSpace X] in
/-- A known invertible parameter gives a nonzero value of the reduced
determinant. -/
theorem determinant_ne_zero (h : ScalarReduction F U) {z : ℂ}
    (hzU : z ∈ U) (hz : (F z).IsInvertible) : h.determinant z ≠ 0 :=
  (h.isInvertible_iff_ne_zero z hzU).mp hz

omit [CompleteSpace X] in
/-- On a connected domain containing one invertible parameter, invertible
parameters form a codiscrete subset.  Equivalently, noninvertible parameters
have no accumulation point in the domain. -/
theorem invertibleSet_mem_codiscreteWithin (h : ScalarReduction F U)
    (hU : IsConnected U) {z₀ : ℂ} (hz₀U : z₀ ∈ U)
    (hz₀ : (F z₀).IsInvertible) :
    invertibleSet F ∈ codiscreteWithin U := by
  have hdet : h.determinant ⁻¹' ({0}ᶜ : Set ℂ) ∈ codiscreteWithin U :=
    h.analyticOnNhd.preimage_zero_mem_codiscreteWithin
      (h.determinant_ne_zero hz₀U hz₀) hz₀U hU
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hdet ⊢
  intro z hzU
  have hunion :
      invertibleSet F ∪ Uᶜ = h.determinant ⁻¹' ({0}ᶜ : Set ℂ) ∪ Uᶜ := by
    ext w
    by_cases hwU : w ∈ U
    · simp only [mem_union, mem_compl_iff, hwU, not_true_eq_false, or_false,
        invertibleSet, mem_ofPred, mem_preimage, mem_compl_iff, mem_singleton_iff]
      exact h.isInvertible_iff_ne_zero w hwU
    · simp [hwU]
  rw [hunion]
  exact hdet z hzU

omit [CompleteSpace X] in
/-- Local punctured-neighborhood formulation of analytic-Fredholm
isolation. -/
theorem eventually_isInvertible_of_mem (h : ScalarReduction F U)
    (hU : IsConnected U) {z₀ z : ℂ} (hz₀U : z₀ ∈ U)
    (hz₀ : (F z₀).IsInvertible) (hzU : z ∈ U) :
    invertibleSet F ∪ Uᶜ ∈ nhdsWithin z ({z}ᶜ) := by
  exact mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
    (h.invertibleSet_mem_codiscreteWithin hU hz₀U hz₀) z hzU

end ScalarReduction

end AnalyticFredholm

end

end FastDynamo
