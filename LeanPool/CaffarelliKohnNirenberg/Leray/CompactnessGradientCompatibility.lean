/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientGlue
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluing

/-!
# Compactness Gradient Compatibility

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Topology
open CKN CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Locally integrable representatives of the same weak spatial derivative
agree almost everywhere on nested open space-time rectangles. -/
theorem weak_partial_representatives_agree_on_nested_rectangles
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hKmono : ∀ j, K j ⊆ K (j + 1))
    (hJmono : ∀ j, J j ⊆ J (j + 1))
    (f : Vec3 × ℝ → ℝ)
    (g : ℕ → Vec3 × ℝ → ℝ)
    (hgMeas : ∀ j, Measurable (g j))
    (m : Fin 3)
    (hlocal : ∀ j, ∀ᵐ t ∂(volume.restrict (J j)),
      LocallyIntegrableOn (fun x => g j (x,t)) (interior (K j)) volume ∧
      HasWeakPartialDerivOn (interior (K j)) m
        (fun x => f (x,t)) (fun x => g j (x,t)))
    {a b : ℕ} (hab : a ≤ b) :
    (g a) =ᵐ[((volume.restrict (interior (K a))).prod
      (volume.restrict (J a)))] (g b) := by
  have hKmonotone : Monotone K := monotone_nat_of_le_succ hKmono
  have hJmonotone : Monotone J := monotone_nat_of_le_succ hJmono
  have hΩab : interior (K a) ⊆ interior (K b) :=
    interior_mono (hKmonotone hab)
  have hJab : J a ⊆ J b := hJmonotone hab
  have hb := ae_restrict_of_ae_restrict_of_subset hJab (hlocal b)
  have htime : ∀ᵐ t ∂(volume.restrict (J a)),
      (fun x => g a (x,t)) =ᵐ[volume.restrict (interior (K a))]
        (fun x => g b (x,t)) := by
    filter_upwards [hlocal a, hb] with t ha ht
    exact HasWeakPartialDerivOn.ae_eq isOpen_interior
      ha.1 (ht.1.mono_set hΩab) ha.2
      (ht.2.restrict isOpen_interior hΩab)
  have hmeas : MeasurableSet
      {z : Vec3 × ℝ | g a z = g b z} :=
    measurableSet_eq_fun (hgMeas a) (hgMeas b)
  exact (ae_prod_iff_ae_ae hmeas).2
    ((ae_ae_comm hmeas).2 htime)

end CKN.Leray
