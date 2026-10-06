/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientGlue

/-!
# Compactness Gradient Time Glue

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Topology
open CKN CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Almost-every-time weak spatial derivatives on a nested product
exhaustion give one almost-every-time weak derivative on the full open
spatial domain. -/
theorem ae_weak_partial_on_union_of_exhaustions
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U)
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hKmono : ∀ j, K j ⊆ K (j + 1))
    (hKinner : ∀ j, K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hJmono : ∀ j, J j ⊆ J (j + 1))
    (hJcover : ⋃ j, J j = I)
    (f d : Vec3 × ℝ → ℝ) (m : Fin 3)
    (hlocal : ∀ j, ∀ᵐ t ∂(volume.restrict (J j)),
      HasWeakPartialDerivOn (interior (K j)) m
        (fun x => f (x, t)) (fun x => d (x, t))) :
    ∀ᵐ t ∂(volume.restrict I),
      HasWeakPartialDerivOn U m
        (fun x => f (x, t)) (fun x => d (x, t)) := by
  have hKmonotone : Monotone K := monotone_nat_of_le_succ hKmono
  have hJmonotone : Monotone J := monotone_nat_of_le_succ hJmono
  rw [← hJcover, ae_restrict_iUnion_iff]
  intro j
  have hk (k : ℕ) : ∀ᵐ t ∂(volume.restrict (J j)),
      HasWeakPartialDerivOn (interior (K k)) m
        (fun x => f (x, t)) (fun x => d (x, t)) := by
    let a := max j k
    have hJa : J j ⊆ J a := hJmonotone (le_max_left j k)
    have hΩa : interior (K k) ⊆ interior (K a) :=
      interior_mono (hKmonotone (le_max_right j k))
    have ha := ae_restrict_of_ae_restrict_of_subset hJa (hlocal a)
    filter_upwards [ha] with t ht
    exact ht.restrict isOpen_interior hΩa
  have hall : ∀ᵐ t ∂(volume.restrict (J j)), ∀ k,
      HasWeakPartialDerivOn (interior (K k)) m
        (fun x => f (x, t)) (fun x => d (x, t)) :=
    (ae_all_iff).mpr hk
  filter_upwards [hall] with t ht
  exact hasWeakPartialDerivOn_of_inner_exhaustion
    hU K hKmono hKinner hKcover
    (fun x => f (x, t)) (fun x => d (x, t)) m ht

end CKN.Leray
