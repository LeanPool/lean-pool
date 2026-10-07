/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressurePairing
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSolenoidalWords

/-!
# High-order pressure cancellation

The pressure-gradient pairing vanishes at every ordered Sobolev
derivative because the differentiated velocity remains solenoidal.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Every ordered derivative has zero whole-space pressure pairing
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_wordDeriv_pressure_pairing_zero
    {u : Vec3 → Vec3} {p : Vec3 → ℝ}
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hdiv : ∀ x : Vec3,
      ∑ i : Fin 3, spatialDeriv (fun y => u y i) i x = 0)
    (α : List (Fin 3))
    (hu0 : ∀ i : Fin 3,
      MemLp (wordDeriv α (fun x => u x i)) 2 volume)
    (hu1 : ∀ i : Fin 3,
      MemLp (spatialDeriv (wordDeriv α (fun x => u x i)) i) 2 volume)
    (hp0 : MemLp (wordDeriv α p) 2 volume)
    (hp1 : ∀ i : Fin 3,
      MemLp (spatialDeriv (wordDeriv α p) i) 2 volume) :
    (∑ i : Fin 3,
      ∫ x : Vec3,
        wordDeriv α (fun y => u y i) x *
          spatialDeriv (wordDeriv α p) i x) = 0 := by
  let h : Vec3 → Vec3 := fun x i => wordDeriv α (fun y => u y i) x
  have hh (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => h x i) :=
    contDiff_wordDeriv (hu i) α
  have hdiv' (x : Vec3) :
      ∑ i : Fin 3, spatialDeriv (fun y => h y i) i x = 0 :=
    lps_wordDeriv_solenoidal hu hdiv α x
  exact lps_solenoidal_pressure_pairing_zero
    hh (contDiff_wordDeriv hp α) hu0 hu1 hp0 hp1 hdiv'

end ESS
