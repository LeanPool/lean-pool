/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardGaugeAlgebra

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardFamilyClauses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the stationary corrector family clause at the pushforward marker

The identity-gauge producer reduces the clause to `RootNormalizedSupply`, which
is a **change of comparison matrix**: it asks the certificate for an
identity-gauge weak-error row, while the root's certificate supplies an
`abar`-gauge one, and no lemma transports between the two.

This module executes the architectural repair.  The physical corrector is
*defined* as the affine pushforward of the normalized-gauge one, so the
certificate-side demand becomes the normalized-gauge datum the converter
already produces.

| clause of the hole | discharged by |
|---|---|
| marker | the definitional record of the pushforward pair |
| slope linearity | `rootJointCarrier_add`/`_smul` through `pushforwardGradient_linear_ae` |
| integer covariance | `pushforwardCarrier_gradient_translate_ae` |
| weak-gradient pair on `univ` | `hasWeakGradientOn_univ_pushforward` |
| corrector equation on `univ` | `pushforward_isWeakSolutionOn` |

The integer-covariance clause is the delicate one: in the
normalized gauge an integer translation of the physical sample is a translation
by the **real** vector `L⁻¹ z`, and the Liouville input at a real translation is
exactly what `RealTranslateLiouville` supplies.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Slope linearity -/

/-- The pushforward gradient family is slope-linear on every sample. -/
theorem pushforwardPhysicalGradPhi_linear (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    ∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
      pushforwardPhysicalGradPhi d abar hS (c • e + e') a =ᵐ[volume]
        fun x ↦ c • pushforwardPhysicalGradPhi d abar hS e a x +
          pushforwardPhysicalGradPhi d abar hS e' a x := by
  intro c e e' a
  by_cases ha : a ∈ pushforwardCore d abar hS
  · have hevent : RootCorrectorEvent d (normalizedSample abar hS a) :=
      pushforwardEvent_of_mem_core_self ha
    have hslope : matVecMul (gaugeRoot abar) (c • e + e') =
        c • matVecMul (gaugeRoot abar) e + matVecMul (gaugeRoot abar) e' := by
      rw [matVecMul_add, matVecMul_smul]
    rw [pushforwardPhysicalGradPhi_of_mem ha (c • e + e'),
      pushforwardPhysicalGradPhi_of_mem ha e, pushforwardPhysicalGradPhi_of_mem ha e',
      hslope, rootJointCarrier_add _ _ hevent, rootJointCarrier_smul _ _ hevent]
    refine pushforwardGradient_linear_ae hS c ?_
    exact (NormalizedLocalH1Carrier.globalGradientRepresentative_addCarrier
      (NormalizedLocalH1Carrier.smulCarrier c
        (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
          (normalizedSample abar hS a)))
      (rootJointCarrier d (matVecMul (gaugeRoot abar) e')
        (normalizedSample abar hS a))).trans
      ((NormalizedLocalH1Carrier.globalGradientRepresentative_smulCarrier c
        (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
          (normalizedSample abar hS a))).fun_add
        (Filter.EventuallyEq.rfl :
          (rootJointCarrier d (matVecMul (gaugeRoot abar) e')
            (normalizedSample abar hS a)).globalGradientRepresentative
            =ᵐ[volume]
            (rootJointCarrier d (matVecMul (gaugeRoot abar) e')
              (normalizedSample abar hS a)).globalGradientRepresentative))
  · have h0 : pushforwardPhysicalGradPhi d abar hS (c • e + e') a = 0 :=
      Set.indicator_of_notMem ha _
    have h1 : pushforwardPhysicalGradPhi d abar hS e a = 0 :=
      Set.indicator_of_notMem ha _
    have h2 : pushforwardPhysicalGradPhi d abar hS e' a = 0 :=
      Set.indicator_of_notMem ha _
    rw [h0, h1, h2]
    refine Filter.Eventually.of_forall fun x ↦ ?_
    simp

/-! ## Integer covariance -/

/-- **Integer covariance of the pushforward gradient family.**  An integer
translation of the physical sample is, in the normalized gauge, a translation by
the real vector `L⁻¹ z`; the identification at that real translation is
`pushforwardCarrier_gradient_translate_ae`. -/
theorem pushforwardPhysicalGradPhi_stationary (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    ∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
      pushforwardPhysicalGradPhi d abar hS e (translateCoeff z a) =ᵐ[volume]
        fun x ↦ pushforwardPhysicalGradPhi d abar hS e a
          (x + Source.AKL.intTranslation z) := by
  intro z e a
  have hmem : translateCoeff z a ∈ pushforwardCore d abar hS ↔
      a ∈ pushforwardCore d abar hS := by
    change a ∈ translateCoeff z ⁻¹' pushforwardCore d abar hS ↔ _
    rw [pushforwardCore, preimage_translateCoeff_invariantTranslationCore]
  by_cases ha : a ∈ pushforwardCore d abar hS
  · have htranslated : translateCoeff z a ∈ pushforwardCore d abar hS := hmem.mpr ha
    rw [pushforwardPhysicalGradPhi_of_mem htranslated e,
      pushforwardPhysicalGradPhi_of_mem ha e]
    exact pushforwardGradient_translate_ae hS (Source.AKL.intTranslation z)
      (pushforwardCarrier_gradient_translate_ae abar hS z e
        (pushforwardEvent_of_mem_core_self ha) (pushforwardEvent_of_mem_core ha z))
  · have htranslated : translateCoeff z a ∉ pushforwardCore d abar hS :=
      fun h ↦ ha (hmem.mp h)
    have h0 : pushforwardPhysicalGradPhi d abar hS e (translateCoeff z a) = 0 :=
      Set.indicator_of_notMem htranslated _
    have h1 : pushforwardPhysicalGradPhi d abar hS e a = 0 :=
      Set.indicator_of_notMem ha _
    rw [h0, h1]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-! ## The marker and the hole -/

/-- **The pushforward construction marker.**  The definitional record of the
one pushforward pair attached to `abar`.  No certificate, order, rate, law, sample
or scale occurs. -/
@[expose]
def RootPushCorrectorFamily (d : ℕ) [NeZero d] (abar : Mat d)
    (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
    (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d) : Prop :=
  ∃ hS : (symmPart abar).PosDef,
    Phi = pushforwardPhysicalPhi d abar hS ∧ gradPhi = pushforwardPhysicalGradPhi d abar hS

/-- The root's corrector-family predicate, re-pointed at the pushforward
marker. -/
@[expose]
def RootPushCorrectorFamilyPredicate (d : ℕ) [NeZero d] :
    Mat d → (Vec d → CoeffSpace d → Vec d → ℝ) →
      (Vec d → CoeffSpace d → Vec d → Vec d) → Prop :=
  RootPushCorrectorFamily d

/-- **The certificate-side supply the pushforward producer needs.**  It is the
normalized-gauge datum — what
`exists_shiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow`
produces from the root's `abar`-comparison block row, and *not* the
identity-gauge row the identity-gauge producer asks for. -/
@[expose]
def RootNormalizedSupply (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop) : Prop :=
  ∀ (abar : Mat d) (hS : (symmPart abar).PosDef) (a : CoeffSpace d) (x : ℝ),
    GoodScale abar a x → ∀ z : Fin d → ℤ,
      RootCorrectorEvent d (normalizedSample abar hS (translateCoeff z a))

/-- **the stationary corrector family clause of the root assembly, at the pushforward marker.**
Every clause is discharged; the only certificate-side input is the
normalized-gauge datum, quantified after the marker and the family have been
chosen, so no scale datum precedes the construction. -/
theorem correctorFamilyHole_of_normalizedSupply (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop)
    (hsupply : RootNormalizedSupply d GoodScale) :
    ∀ abar : Mat d, (symmPart abar).PosDef →
      ∃ (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
        (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
        RootPushCorrectorFamilyPredicate d abar Phi gradPhi ∧
        (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
          gradPhi (c • e + e') a
            =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
        (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
          gradPhi e (translateCoeff z a)
            =ᵐ[volume] fun x => gradPhi e a (x + Source.AKL.intTranslation z)) ∧
        ∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
          ∀ e : Vec d,
            HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
              IsWeakSolutionOn (fun y => a.1 y) Set.univ
                (fun y => e + gradPhi e a y) := by
  intro abar hS
  refine ⟨pushforwardPhysicalPhi d abar hS, pushforwardPhysicalGradPhi d abar hS,
    ⟨hS, rfl, rfl⟩, pushforwardPhysicalGradPhi_linear d abar hS,
    pushforwardPhysicalGradPhi_stationary d abar hS, ?_⟩
  intro a x hgood e
  exact pushforwardPhysical_equation d abar hS
    (mem_invariantTranslationCore_iff.mpr (hsupply abar hS a x hgood)) e

end

end Root
end HighContrast
end HCPolySupport
