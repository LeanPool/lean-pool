/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalModeIsolation

/-!
# The horizontal spectrum consists of eigenvalues

The analytic Fredholm paragraph of §2.3 of the paper:

> At each exceptional point, Fredholm index zero gives a non-zero kernel, which the definition
> of `A_w` identifies with `ker(z − A_w)`.  Hence the spectrum of `A_w` in the open right
> half-plane consists of isolated eigenvalues.

`horizontalSpectrum N w` is the set of parameters `z` with `re z > 0` at which the shifted form
operator `𝔸_w(z) : V → V*` fails to be an isomorphism.  This module proves that every such `z`
is an eigenvalue of the form operator `A_w = horizontalFormOperator N w`, with an eigenvector
in the form-operator domain (`exists_isEigenpair_of_mem_horizontalSpectrum`).  Together with
`mem_horizontalSpectrum_of_isEigenpair` this identifies the horizontal spectrum with the
eigenvalues of `A_w` in the open right half plane (`mem_horizontalSpectrum_iff`), and
`isDiscrete_horizontalSpectrum` makes them isolated.

The Fredholm input is the factorisation `𝔸_w(z) = F_z(1 - K(z))` with `F_z` an isomorphism
and `K(z)` compact (`freeHorizontalForm_comp_compactPencil`): the Fredholm alternative for the
compact operator `K(z)` (`CompactFactor.hasEigenvalue_one_or_isInvertible_sub`) turns the
non-invertibility of `1 - K(z)` into a non-zero fixed vector of `K(z)`, which is a non-zero
null vector of `𝔸_w(z)`.  This is the index-zero statement of the paper, used in the form
"injective implies invertible".  The null vector satisfies the weak eigenvalue identity
`𝔩_w(b, φ) = -z⟨b, φ⟩`, which is the definition of `b ∈ D(A_w)` with `A_w b = z b`.  The
domain is the form-operator domain, as in the paper: for `w ∈ L^∞` with compact support (in
particular for the jump velocity `V⁰`) the paper defines `A_w` through its form.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalWeakForm

/-- A non-zero null vector of the shifted form operator `𝔸_w(z)` exists at every parameter of
the open right half plane where `1 - K(z)` fails to be invertible, `K(z)` being compact. -/
theorem exists_ne_zero_horizontalPencilForm_eq_zero (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hK : IsCompactOperator (horizontalFredholmKernel N w z))
    (hnot : ¬ (horizontalPencilForm N w z).IsInvertible) :
    ∃ b : WholePlaneC2H1, b ≠ 0 ∧ horizontalPencilForm N w z b = 0 := by
  have hid : (ContinuousLinearMap.id ℂ WholePlaneC2H1).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℂ WholePlaneC2H1, rfl⟩
  rcases CompactFactor.hasEigenvalue_one_or_isInvertible_sub hid hK with heig | hinv
  · obtain ⟨b, hb⟩ := heig.exists_hasEigenvector
    refine ⟨b, hb.2, ?_⟩
    have hfix : horizontalFredholmKernel N w z b = b := by
      have h1 : (ContinuousLinearMap.id ℂ WholePlaneC2H1).inverse
          (horizontalFredholmKernel N w z b) = b :=
        hb.apply_eq_smul.trans (one_smul ℂ b)
      rwa [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply] at h1
    have hP : AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z b = 0 := by
      rw [AnalyticFredholm.compactPencil_apply, hfix]
      exact sub_self b
    have h0 : freeHorizontalForm N z
        (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z b) = 0 :=
      (congrArg (freeHorizontalForm N z) hP).trans (freeHorizontalForm N z).map_zero
    exact (DFunLike.congr_fun (freeHorizontalForm_comp_compactPencil N w hz) b).symm.trans h0
  · exact absurd ((horizontalPencilForm_isInvertible_iff N w hz).mpr hinv) hnot

section Supported

variable (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
  (N : ℝ) (w : WholePlaneC3LInf)
  (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
  (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0)

include hs hsm hw3 hw

/-- **Every point of the horizontal spectrum is an eigenvalue of `A_w`.**  For a velocity
supported in a set of finite measure, every parameter `z` of the open right half plane at which
`𝔸_w(z)` fails to be an isomorphism `V → V*` carries an eigenvector of the form operator `A_w`:
an element `u` of its domain with `A_w u = z u` and non-zero `L²` value.  This is the sentence
"at each exceptional point, Fredholm index zero gives a non-zero kernel, which the definition of
`A_w` identifies with `ker(z − A_w)`" of §2.3 of the paper. -/
theorem exists_isEigenpair_of_mem_horizontalSpectrum {z : ℂ}
    (hz : z ∈ horizontalSpectrum N w) :
    ∃ u : HorizontalFormDomain N w, (horizontalFormOperator N w).IsEigenpair z u := by
  obtain ⟨b, hb, hnull⟩ := exists_ne_zero_horizontalPencilForm_eq_zero N w hz.1
    (isCompactOperator_horizontalFredholmKernel_of_ae_zero_off s hs hsm N w hw3 hw z) hz.2
  have hweak : HorizontalMode.HorizontalModeWeakEquation N w b z := by
    intro phi
    have h0 : horizontalPencilForm N w z b phi = 0 :=
      (DFunLike.congr_fun hnull phi).trans (zero_apply phi)
    have h := horizontalPencilForm_apply N w z b phi
    linear_combination h0 - h
  have hne : wholePlaneH1Embedding C2 b ≠ 0 := fun h0 =>
    hb (wholePlaneC2H1Embedding_injective
      (h0.trans (wholePlaneH1Embedding C2).map_zero.symm))
  obtain ⟨u, -, hu⟩ := HorizontalMode.isEigenpair_of_weakEquation N w b z hne hweak
  exact ⟨u, hu⟩

/-- **The spectrum of `A_w` in the open right half plane consists of eigenvalues.**  For a
velocity supported in a set of finite measure, the horizontal spectrum is exactly the set of
eigenvalues of the form operator `A_w` with positive real part; by
`isDiscrete_horizontalSpectrum` they are isolated.  This is the conclusion of the analytic
Fredholm paragraph of §2.3 of the paper. -/
theorem mem_horizontalSpectrum_iff {z : ℂ} :
    z ∈ horizontalSpectrum N w ↔
      0 < z.re ∧ ∃ u : HorizontalFormDomain N w, (horizontalFormOperator N w).IsEigenpair z u := by
  constructor
  · intro hz
    exact ⟨hz.1, exists_isEigenpair_of_mem_horizontalSpectrum s hs hsm N w hw3 hw hz⟩
  · rintro ⟨hre, u, hu⟩
    exact mem_horizontalSpectrum_of_isEigenpair N w hre u hu

end Supported

end HorizontalWeakForm

end

end FastDynamo
