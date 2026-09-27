/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.FirstJetSupport

/-!
# The post-first-feedback circuit state

The geometric first-jet theorem is connected here to the actual circuit flag.
The target witness entering at gate five is replaced, modulo the preceding
state, by its rational tangent.  Thus later gates see the old seed state plus
one explicit first-Hasse-jet direction.
-/

@[expose] public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The normalized seed and fifth-gate target data at a rational first jet. -/
def FirstJetState (C : Circuit 8 8) : Prop :=
  ∃ (theta : Fin 3) (eps : F₂)
    (seedLinear seedCompanion : LinearForm) (seedRho : F₂),
    anfThreeProjection (C.gate 3) =
      vectorWedgeTwo seedLinear (rationalTwo (rationalSingleton theta)) ∧
    anfTwoProjection (C.gate 3) =
      seedRho • rationalTwo (rationalSingleton theta) +
        vectorWedge seedCompanion seedLinear +
        booleanContraction seedLinear
          (rationalTwo (rationalSingleton theta)) ∧
    vectorWedgeTwo seedLinear (rationalTwo (rationalSingleton theta)) ≠ 0 ∧
    InNormalizedFirstJet theta seedLinear ∧
    circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)}

/-- The first useful suffix gate installs the first Hasse jet in the actual
circuit flag.  All coordinate work is delegated to the correlated algebraic
normal form; this proof only performs state replacement. -/
theorem NormalizedEight.firstJetState
    {C : Circuit 8 8} (h : NormalizedEight C) : FirstJetState C := by
  rcases h.firstUsefulChild_isLowLow with
    ⟨target, child, shift, htarget, htargetOld, htargetNew, hshift,
      htargetEq, hchild⟩
  have htargetNotLow : target ∉ rationalLowSpace := by
    intro hlow
    apply htargetOld
    rw [h.wireSpace_four_eq]
    exact Submodule.mem_sup_left hlow
  rcases exists_low_add_seed_of_mem_four h hshift with
    ⟨low, e, hlow, hshiftEq⟩
  have hcollision : target = (low + C.gate 3) + child := by
    rcases f2_eq_zero_or_one e with rfl | rfl
    · have htargetEq' : target = low + child := by
        simpa using htargetEq.trans
          (congrArg (fun z : ANF 8 => z + child) hshiftEq)
      have hchildAmbient : child ∈ targetAmbient 8 (mulTarget 4) := by
        have htargetPlus := add_mem_targetAmbient_of_mem_rationalLow
          htarget hlow
        have heq : target + low = child := by
          rw [htargetEq']
          calc
            (low + child) + low = (low + low) + child := by ac_rfl
            _ = child := by rw [anf_add_self, zero_add]
        rwa [heq] at htargetPlus
      rcases hchild with ⟨u, v, hu, hv, hchildEq⟩
      have hchildLow : child ∈ rationalLowSpace := by
        rw [hchildEq]
        exact rationalLow_mul_mem_of_mem_targetAmbient hu hv
          (by simpa [hchildEq] using hchildAmbient)
      exact (htargetNotLow (by
        rw [htargetEq']
        exact Submodule.add_mem _ hlow hchildLow)).elim
    · simpa only [one_smul] using htargetEq.trans
        (congrArg (fun z : ANF 8 => z + child) hshiftEq)
  rcases hchild with ⟨childLeft, childRight,
    hchildLeft, hchildRight, hchildEq⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hchildLeft with
    ⟨childLeftConst, childLeftLinear, childLeftCoeff, hchildLeftRep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hchildRight with
    ⟨childRightConst, childRightLinear, childRightCoeff, hchildRightRep⟩
  rcases exists_targetAmbient_rep htarget with
    ⟨targetAffine, targetCoeff, htargetAffine, htargetRep⟩
  have hchildRep : child =
      (affineANF childLeftConst childLeftLinear +
          rationalANF childLeftCoeff) *
        (affineANF childRightConst childRightLinear +
          rationalANF childRightCoeff) := by
    rw [hchildEq, hchildLeftRep, hchildRightRep]
  have htargetQuartic := quarticProbeANF_eq_zero_of_mem_targetAmbient htarget
  have hlowQuartic := quarticProbeANF_eq_zero_of_mem_targetAmbient
    (rationalLowSpace_le_targetAmbient hlow)
  have hgQuartic := h.seed_quarticProbe_eq_zero
  have hchildQuartic : quarticProbeANF child = 0 := by
    have heq := congrArg quarticProbeANF hcollision
    rw [map_add, map_add, hlowQuartic, hgQuartic, htargetQuartic] at heq
    simpa using heq.symm
  have hchildProbe : quarticWedgeProbe (rationalTwo childLeftCoeff)
      (rationalTwo childRightCoeff) = 0 := by
    rw [hchildRep, lowProduct_quarticProjection] at hchildQuartic
    exact hchildQuartic
  have htargetCubic := anfThreeProjection_eq_zero_of_mem_targetAmbient htarget
  have hlowCubic := anfThreeProjection_eq_zero_of_mem_targetAmbient
    (rationalLowSpace_le_targetAmbient hlow)
  have hchildCubic : anfThreeProjection child =
      anfThreeProjection (C.gate 3) := by
    have heq := congrArg anfThreeProjection hcollision
    rw [map_add, map_add, hlowCubic, htargetCubic, zero_add] at heq
    exact ((add_eq_zero_iff_eq_neg.mp heq.symm).trans
      (by funext i j k; exact neg_eq_self_f2 _)).symm
  have htargetNonrational : ¬ IsRationalCoeff targetCoeff := by
    intro hrat
    rcases (IsRationalCoeff_iff targetCoeff).mp hrat with
      ⟨alpha, halpha⟩
    apply htargetNotLow
    rw [htargetRep, halpha]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left htargetAffine
    · apply Submodule.mem_sup_right
      exact (mem_rationalTargetSpace_iff _).mpr ⟨alpha, rfl⟩
  have hAt : CubicLowLowNormalCollisionAt
      (C.gate 3) target targetAffine targetCoeff :=
    ⟨child, low,
      childLeftConst, childRightConst, childLeftLinear, childRightLinear,
      childLeftCoeff, childRightCoeff,
      h.cubicSeedNormalForm, hlow, htargetAffine, hchildRep,
      hcollision, htargetRep, hchildProbe, hchildCubic,
      h.seed_cubicProjection_ne_zero, htargetNonrational⟩
  rcases cubicLowLowNormalCollisionAt_targetNormalForm hAt with
    ⟨theta, eps, seedLinear, seedCompanion, seedRho, rationalCoeff,
      _htargetAffine, _htargetRep, hgCubic, hgQuadratic, hgCubicNonzero,
      hdelta, hnormal⟩
  let jet : ANF 8 := targetANF (rationalTangentAt theta eps)
  let oldPart : ANF 8 := targetAffine + rationalANF rationalCoeff
  have holdPartLow : oldPart ∈ rationalLowSpace := by
    dsimp [oldPart]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left htargetAffine
    · exact Submodule.mem_sup_right
        ((mem_rationalTargetSpace_iff _).mpr ⟨rationalCoeff, rfl⟩)
  have holdPart : oldPart ∈ circuitFlag C 4 := by
    rw [h.wireSpace_four_eq]
    exact Submodule.mem_sup_left holdPartLow
  have hjetEq : jet = target + oldPart := by
    dsimp [jet, oldPart]
    rw [← hdelta]
    change targetANFLinear (targetCoeff + rationalCoeffRep rationalCoeff) = _
    rw [map_add, htargetRep]
    change targetANF targetCoeff + rationalANF rationalCoeff =
      (targetAffine + targetANF targetCoeff) +
        (targetAffine + rationalANF rationalCoeff)
    rw [add_add_add_comm, anf_add_self, zero_add]
  have hjetOld : jet ∉ circuitFlag C 4 := by
    intro hj
    apply htargetOld
    have hsum := Submodule.add_mem _ hj holdPart
    have heq : jet + oldPart = target := by
      rw [hjetEq]
      rw [add_assoc, anf_add_self, add_zero]
    rwa [heq] at hsum
  have hjetNew : jet ∈ circuitFlag C 5 := by
    rw [hjetEq]
    exact Submodule.add_mem _ htargetNew
      (wireSpace_mono (g := C.gate) (by omega) holdPart)
  refine ⟨theta, eps, seedLinear, seedCompanion, seedRho,
    hgCubic, hgQuadratic, hgCubicNonzero, hnormal, ?_⟩
  exact circuit_first_entry_replacement C (4 : Fin 8) jet hjetNew hjetOld

end

end N4
end UnrestrictedBooleanMul
