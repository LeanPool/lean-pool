/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierWeakPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportDivergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalAssemblySupport

/-!
# Divergence form of the regularized momentum equation

The actual transport field is a smooth mollification of a `J` slice.
Its pointwise zero divergence converts the regularized transport term
to the tensor divergence used in the high-order energy identity.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The right-hand side of the regularized momentum equation equals
the heat operator minus tensor divergence and pressure gradient
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_regR12TimeRHS_divergence
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (t : ℝ)
    (hJ : IsInJ (fun x : Vec3 => u (x, t)))
    (hu : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (x : Vec3) (i : Fin 3) :
    CKN.Leray.regR12TimeRHS ρ ε hε u p (x, t) i =
      (∑ j : Fin 3,
        spatialDeriv (spatialDeriv (fun y : Vec3 => u (y, t) i) j) j x) -
      (∑ j : Fin 3,
        spatialDeriv (fun y : Vec3 =>
          CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (y, t) j *
            u (y, t) i) j x) -
      spatialDeriv (fun y : Vec3 => p (y, t)) i x := by
  let v : Vec3 → Vec3 :=
    fun y => CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (y, t)
  have hv : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun y => v y j) := by
    intro j
    exact lps_regUniformMollifiedInitial_smooth ρ ε hε hJ j
  have hdiv : ∀ y : Vec3,
      ∑ j : Fin 3, spatialDeriv (fun z => v z j) j y = 0 := by
    intro y
    exact CKN.Leray.regUniformMollifiedVelocity_divergence_eq_zero
      ρ ε hε u t hJ y
  have htransport := lps_transport_divergence v
    (fun y : Vec3 => u (y, t)) hv hu hdiv i x
  unfold CKN.Leray.regR12TimeRHS
  change
    (∑ j : Fin 3,
      spatialDeriv (spatialDeriv (fun y : Vec3 => u (y, t) i) j) j x) -
    (∑ j : Fin 3, v x j * spatialDeriv (fun y : Vec3 => u (y, t) i) j x) -
    spatialDeriv (fun y : Vec3 => p (y, t)) i x = _
  rw [htransport]

end ESS
