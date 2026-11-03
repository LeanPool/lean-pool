/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Symplectic
public import LeanPool.SingleCopyStabilizer.Measurement


/-! Arbitrary-qubit simultaneous CNOT action and its exact Pauli covariance.
The basis permutation is `x ↦ x - xᵢ w`, with `wᵢ=0`; over F₂ this is the
product of CNOTs controlled by i and targeted at the support of w. -/

@[expose] public section

noncomputable section


namespace LeanPool.SingleCopyStabilizer.CNOTAction

open Measurement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The invertible coordinate shear underlying simultaneous controlled-NOT gates. -/
def basisShear (i : ι) (w : Bits ι) (hw : w i = 0) : Bits ι ≃ₗ[ZMod 2] Bits ι where
  toFun := shearX i w
  invFun x := x + x i • w
  left_inv x := by
    ext j
    simp [shearX, hw]
  right_inv x := by
    ext j
    simp [shearX, hw]
  map_add' x y := by
    ext j
    simp [shearX, add_smul]
    ring
  map_smul' c x := by
    ext j
    simp [shearX]
    ring

/-- Pull amplitudes back along the inverse controlled shear. -/
def applyCNOTs (i : ι) (w : Bits ι) (hw : w i = 0)
    (ψ : Amplitude ι) : Amplitude ι := fun x => ψ ((basisShear i w hw).symm x)

theorem norm_preserved (i : ι) (w : Bits ι) (hw : w i = 0) (ψ : Amplitude ι) :
    (∑ x, bornWeight (applyCNOTs i w hw ψ) x) = ∑ x, bornWeight ψ x := by
  exact Fintype.sum_equiv (basisShear i w hw).symm.toEquiv _ _ (fun _ => rfl)

theorem normalized (i : ι) (w : Bits ι) (hw : w i = 0) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) : IsNormalized (applyCNOTs i w hw ψ) := by
  unfold IsNormalized
  rw [norm_preserved]
  exact hψ

theorem inverse_pairing (i : ι) (w : Bits ι) (hw : w i = 0) (v x : Bits ι) :
    shearZ i w v ⬝ᵥ x = v ⬝ᵥ (basisShear i w hw).symm x := by
  have h := shear_pairing i hw ((basisShear i w hw).symm x) v
  change ((basisShear i w hw) ((basisShear i w hw).symm x)) ⬝ᵥ shearZ i w v = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  simpa only [dotProduct_comm] using h

/-- Exact covariance of the concrete basis-permutation action. -/
theorem pauli_covariance (i : ι) (w : Bits ι) (hw : w i = 0)
    (u v : Bits ι) (ψ : Amplitude ι) :
    pauliAction (shearX i w u) (shearZ i w v) (applyCNOTs i w hw ψ) =
      applyCNOTs i w hw (pauliAction u v ψ) := by
  funext x
  have hpre : (basisShear i w hw).symm (x - shearX i w u) =
      (basisShear i w hw).symm x - u := by
    change (basisShear i w hw).symm (x - (basisShear i w hw) u) = _
    rw [map_sub, LinearEquiv.symm_apply_apply]
  have hsign := inverse_pairing i w hw v (x - shearX i w u)
  rw [hpre] at hsign
  simp only [pauliAction, applyCNOTs, hpre, hsign]

/-- Every Pauli eigenlabel is transported by the shear used in the paper. -/
theorem transports_eigenvector (i : ι) (w : Bits ι) (hw : w i = 0)
    (ψ : Amplitude ι) (u v : Bits ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ u v ζ) :
    IsPauliEigenvector (applyCNOTs i w hw ψ) (shearX i w u) (shearZ i w v) ζ := by
  intro x
  rw [congrFun (pauli_covariance i w hw u v ψ) x]
  exact heig ((basisShear i w hw).symm x)

omit [DecidableEq ι] [Fintype ι] in
/-- Explicit two-sided inverse, needed when the learned circuit is undone. -/
theorem inverse_action (i : ι) (w : Bits ι) (hw : w i = 0) (ψ : Amplitude ι) :
    (fun x => applyCNOTs i w hw ψ ((basisShear i w hw) x)) = ψ := by
  classical
  funext x
  simp [applyCNOTs]

end LeanPool.SingleCopyStabilizer.CNOTAction
