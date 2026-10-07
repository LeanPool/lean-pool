/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# Gradients of slices with the same trace

Two `H¹` slices that agree almost everywhere have almost everywhere equal weak
gradients (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Two `H¹` functions that agree almost everywhere have almost everywhere equal weak
gradients (`lem:lps-continuation`). -/
theorem lps_h1_gradient_ae_eq_of_slice_ae_eq
    {u v : Vec3 → Vec3} {Du Dv : Vec3 → Fin 3 → Vec3}
    (hU : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u x i) ∧
      h.grad = (fun x j => Du x i j))
    (hV : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => v x i) ∧
      h.grad = (fun x j => Dv x i j))
    (htrace : u =ᵐ[volume] v) :
    ∀ i j : Fin 3, (fun x : Vec3 => Du x i j) =ᵐ[volume]
      (fun x : Vec3 => Dv x i j) := by
  intro i j
  obtain ⟨hu, huFun, huGrad⟩ := hU i
  obtain ⟨hv, hvFun, hvGrad⟩ := hV i
  have huWeak : HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x : Vec3 => u x i) (fun x k => Du x i k) := by
    rw [← huFun, ← huGrad]
    exact hu.hasWeakGradient
  have hvWeak : HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x : Vec3 => v x i) (fun x k => Dv x i k) := by
    rw [← hvFun, ← hvGrad]
    exact hv.hasWeakGradient
  have huWeakV : HasWeakPartialDerivOn (Set.univ : Set Vec3) j
      (fun x : Vec3 => v x i) (fun x => Du x i j) := by
    intro φ hφ hφc hφsupp
    have htracei : (fun x : Vec3 => v x i) =ᵐ[volume]
        (fun x : Vec3 => u x i) := by
      filter_upwards [htrace] with x hx
      exact (congrFun hx i).symm
    have htracei' : (fun x : Vec3 => v x i) =ᵐ[volume.restrict Set.univ]
        (fun x : Vec3 => u x i) := by
      simpa using htracei
    calc
      ∫ x in (Set.univ : Set Vec3), v x i * (fderiv ℝ φ x) (basisVec j) ∂volume =
          ∫ x in (Set.univ : Set Vec3), u x i * (fderiv ℝ φ x) (basisVec j) ∂volume := by
        apply integral_congr_ae
        filter_upwards [htracei'] with x hx
        rw [hx]
      _ = -∫ x in (Set.univ : Set Vec3), Du x i j * φ x ∂volume :=
        huWeak j φ hφ hφc hφsupp
  have hDuMem : MemLp (fun x : Vec3 => Du x i j) 2 volume := by
    simpa [CKN.GradMemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ, huGrad] using hu.gradMemL2 j
  have hDvMem : MemLp (fun x : Vec3 => Dv x i j) 2 volume := by
    simpa [CKN.GradMemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ, hvGrad] using hv.gradMemL2 j
  have hDuLoc : LocallyIntegrableOn (fun x : Vec3 => Du x i j)
      (Set.univ : Set Vec3) volume :=
    (hDuMem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hDvLoc : LocallyIntegrableOn (fun x : Vec3 => Dv x i j)
      (Set.univ : Set Vec3) volume :=
    (hDvMem.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  simpa [CKN.volumeOn, Measure.restrict_univ] using
    HasWeakPartialDerivOn.ae_eq isOpen_univ hDuLoc hDvLoc
      huWeakV (hvWeak j)

end ESS

end
