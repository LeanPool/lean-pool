/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a

/-!
# High-contrast homogenization: Consistency.ClosureH1aPairing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak-gradient identity and the flux pairing on the `H¹_a` classes

This module checks the defining predicate `MemH1a` of `H¹_a(V)` of
`s.introduction`, and its zero-trace variant `MemH1a0`.  It checks the two conjuncts that make
those classes honest: that the weak-gradient
relation `HasWeakGradientOn` becomes an identity between convergent integrals on
the class, and that the measurability conjunct `IsMeasurableGradientPair`
supplies the measurable gradient slot that the flux-pairing statements would
otherwise have to assume.

The check is not local to this module.  The classes carry
`HasWeakGradientOn V u Du`, whose identity is satisfied vacuously as `0 = -0`
whenever both pairings diverge; if the first conjunct failed, a member would
satisfy the relation for no reason, the relation would assert nothing about `u`
and `Du`, and `IsWeakSolutionOn` — well formed only through the absolute
convergence of the flux pairing — would hold by the divergence of that pairing
and not by the weak interior equation.  If the second failed, the class would
not encode a measurable gradient field, so it would be an encoding other than
the object the paper prints.

The closure family of the coefficient-Sobolev classes of `s.introduction` is
established below in the two forms its consumers read.

First the weak-gradient relation itself: for a member of `H¹_a(V)` or
`H¹_{a,0}(V)` and a test local to `V`, both pairings of the relation converge
absolutely *and* the identity holds between them, so the relation is an identity
between convergent integrals and not the vacuous `0 = -0`.

Then the flux pairing of the weak interior equation, in the form where the
measurability of the gradient slot is read off the class instead of being
assumed — including for the shifted pair of `e.random.dirichlet`, whose
unshifted gradient slot is measurable because the class carries the
measurability of the difference and the estimate carries that of the boundary
datum's gradient.

This module is a consistency check of that definition and is not a result of the
paper.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The closure lemma for `H¹_a(V)`.**  For a member of the class on a
bounded `V` and a local test on `V`, **both** pairings of the weak-gradient
relation are absolutely convergent, so the `0 = -0` branch of
`HasWeakGradientOn` is unreachable on this class.

Hypotheses used, in full: the coefficient-class hypotheses `0 < lam` and `hell`;
boundedness of `V`; membership in `MemH1a`; and `φ` a local test on `V`.  No
measurability hypothesis appears — both slots are measurable by the class — and
neither `lam ≤ Lam` nor measurability of `V` is used. -/
theorem integrableOn_weakGradientPairings_of_memH1a_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) (i : Fin d) :
    IntegrableOn (fun x => u x * (fderiv ℝ φ x) (basisVec i)) V volume ∧
      IntegrableOn (fun x => Du x i * φ x) V volume :=
  ⟨integrableOn_mul_testGrad_of_integrableOn hφ
      (integrableOn_of_memH1a_class hVb hu) i,
    integrableOn_grad_mul_test_of_integrableOn_vecNormSq hφ
      (aestronglyMeasurable_grad_of_memH1a hu)
      (integrableOn_vecNormSq_grad_of_memH1a_class hlam hell hVb hu) i⟩

/-- **The closure lemma for `H¹_{a,0}(V)`.**  The same, on an arbitrary
`V`: the class's approximants are compactly supported inside `V`, and the
gradient pairing is read on the compact support of the test. -/
theorem integrableOn_weakGradientPairings_of_memH1a0_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du)
    {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) (i : Fin d) :
    IntegrableOn (fun x => u x * (fderiv ℝ φ x) (basisVec i)) V volume ∧
      IntegrableOn (fun x => Du x i * φ x) V volume :=
  ⟨integrableOn_mul_testGrad_of_integrableOn hφ
      (integrableOn_of_memH1a0_class hu) i,
    integrableOn_grad_mul_test_of_integrableOn_vecNormSq hφ
      (aestronglyMeasurable_grad_of_memH1a0 hu)
      (integrableOn_vecNormSq_grad_of_memH1a0_class hlam hell hu) i⟩

/-- **The form in which the weak-gradient identity is read, for `H¹_a(V)`.**
Both pairings converge absolutely **and** the identity holds between them. -/
theorem weakGradientPairing_eq_of_memH1a_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) (i : Fin d) :
    IntegrableOn (fun x => u x * (fderiv ℝ φ x) (basisVec i)) V volume ∧
      IntegrableOn (fun x => Du x i * φ x) V volume ∧
      ∫ x in V, u x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        -∫ x in V, Du x i * φ x ∂volume := by
  obtain ⟨h1, h2⟩ :=
    integrableOn_weakGradientPairings_of_memH1a_class hlam hell hVb hu hφ i
  exact ⟨h1, h2,
    hu.2.1 i φ hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset⟩

/-- **The form in which the weak-gradient identity is read, for
`H¹_{a,0}(V)`.** -/
theorem weakGradientPairing_eq_of_memH1a0_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du)
    {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) (i : Fin d) :
    IntegrableOn (fun x => u x * (fderiv ℝ φ x) (basisVec i)) V volume ∧
      IntegrableOn (fun x => Du x i * φ x) V volume ∧
      ∫ x in V, u x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        -∫ x in V, Du x i * φ x ∂volume := by
  obtain ⟨h1, h2⟩ :=
    integrableOn_weakGradientPairings_of_memH1a0_class hlam hell hu hφ i
  exact ⟨h1, h2,
    hu.2.1 i φ hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset⟩

/-! ### The flux-pairing chain, with the measurability read off the class

The pairing statements for a member of `H¹_a` or `H¹_{a,0}` take
`hDmeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V)` as an
explicit hypothesis.  It is a conjunct of the membership classes, so it can be
discharged; the statements below are the same ones with it removed. -/

/-- `integrableOn_weakPairing_of_memH1a` with the measurability discharged. -/
theorem integrableOn_weakPairing_of_memH1a_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V) (hVb : Bornology.IsBounded V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a b V u Du)
    {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) V
      volume :=
  integrableOn_weakPairing_of_memH1a hlam hle hell hV hVb hbmeas
    (aestronglyMeasurable_grad_of_memH1a hu) hu hφ

/-- `integrableOn_weakPairing_of_memH1a0` with the measurability discharged. -/
theorem integrableOn_weakPairing_of_memH1a0_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du)
    {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) V
      volume :=
  integrableOn_weakPairing_of_memH1a0 hlam hle hell hV hbmeas
    (aestronglyMeasurable_grad_of_memH1a0 hu) hu hφ

/-- `isWeakSolutionOn_iff_of_memH1a` with the measurability discharged. -/
theorem isWeakSolutionOn_iff_of_memH1a_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V) (hVb : Bornology.IsBounded V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a b V u Du) :
    IsWeakSolutionOn b V Du ↔
      ∀ φ : Vec d → ℝ, IsLocalTest V φ →
        ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (Du x)) ∂volume = 0 :=
  isWeakSolutionOn_iff_of_memH1a hlam hle hell hV hVb hbmeas
    (aestronglyMeasurable_grad_of_memH1a hu) hu

/-- The `H¹_{a,0}` counterpart, on an arbitrary measurable `V`. -/
theorem isWeakSolutionOn_iff_of_memH1a0_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) :
    IsWeakSolutionOn b V Du ↔
      ∀ φ : Vec d → ℝ, IsLocalTest V φ →
        ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (Du x)) ∂volume = 0 :=
  ⟨fun h φ hφ => (h φ hφ).2,
   fun h φ hφ =>
     ⟨integrableOn_weakPairing_of_memH1a0_class hlam hle hell hV hbmeas hu hφ,
      h φ hφ⟩⟩

/-- The gradient slot of the *unshifted* pair of the Dirichlet clause is
measurable: the class carries the measurability of `Du - Dg`, and the clause
carries that of `Dg`. -/
theorem aestronglyMeasurable_grad_of_memH1a0_sub {b : CoeffField d}
    {V : Set (Vec d)} {u g : Vec d → ℝ} {Du Dg : Vec d → Vec d}
    (hDgmeas : ∀ j, AEStronglyMeasurable (fun x => Dg x j) (volume.restrict V))
    (hu : MemH1a0 b V (fun x => u x - g x) (fun x => Du x - Dg x)) (j : Fin d) :
    AEStronglyMeasurable (fun x => Du x j) (volume.restrict V) := by
  have hsub : AEStronglyMeasurable (fun x => Du x j - Dg x j)
      (volume.restrict V) := hu.1.2 j
  have hsum : AEStronglyMeasurable (fun x => Du x j - Dg x j + Dg x j)
      (volume.restrict V) := hsub.add (hDgmeas j)
  have heq : (fun x => Du x j - Dg x j + Dg x j) = fun x => Du x j := by
    funext x
    ring
  rwa [heq] at hsum

/-- `integrableOn_vecNormSq_of_memH1a0_sub` with the measurability of the
unshifted gradient slot discharged. -/
theorem integrableOn_vecNormSq_of_memH1a0_sub_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u g : Vec d → ℝ} {Du Dg : Vec d → Vec d}
    {L : ℝ}
    (hDg : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)),
      Real.sqrt (vecNormSq (Dg x)) ≤ L)
    (hDgmeas : ∀ j, AEStronglyMeasurable (fun x => Dg x j) (volume.restrict V))
    (hu : MemH1a0 b V (fun x => u x - g x) (fun x => Du x - Dg x)) :
    IntegrableOn (fun x => vecNormSq (Du x)) V volume :=
  integrableOn_vecNormSq_of_memH1a0_sub hlam hell hVb hDg hDgmeas
    (aestronglyMeasurable_grad_of_memH1a0_sub hDgmeas hu) hu

/-- `integrableOn_weakPairing_of_memH1a0_sub` with the measurability of the
unshifted gradient slot discharged. -/
theorem integrableOn_weakPairing_of_memH1a0_sub_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V) (hVb : Bornology.IsBounded V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u g : Vec d → ℝ} {Du Dg : Vec d → Vec d} {L : ℝ}
    (hDg : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)),
      Real.sqrt (vecNormSq (Dg x)) ≤ L)
    (hDgmeas : ∀ j, AEStronglyMeasurable (fun x => Dg x j) (volume.restrict V))
    (hu : MemH1a0 b V (fun x => u x - g x) (fun x => Du x - Dg x))
    {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) V
      volume :=
  integrableOn_weakPairing_of_memH1a0_sub hlam hle hell hV hVb hbmeas hDg hDgmeas
    (aestronglyMeasurable_grad_of_memH1a0_sub hDgmeas hu) hu hφ

end

end HighContrast
end HCPolySupport
