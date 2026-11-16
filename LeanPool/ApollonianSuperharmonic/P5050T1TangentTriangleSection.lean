/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5050T1RadialSection
public import LeanPool.ApollonianSuperharmonic.P4909T1TangentSegments

-- [TABLET NODE: P5050T1TangentTriangleSection]

/-!
# P5050T1TangentTriangleSection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5050T1TangentTriangleSection :
    ∀ (a : Complex), ∀ (b : Complex), ∀ (c : Complex), ∀ (ρ : Real), ∀ (s : Real), ∀ (t : Real),
        (0 < ρ) → ((0 ≤ s) → ((0 ≤ t) → ((dist a b = ρ + s) → ((dist a c = ρ + t) → ((dist b c =
        s + t) → (IsPreconnected (Metric.sphere a ρ ∩
        convexHull Real ({a, b, c} : Set Complex)))))))) := by
  intro a b c ρ s t hρ hs ht hab hac hbc
-- BODY
  have hseg := P4909T1TangentSegments b c s t hbc
  have hsep : ∀ w ∈ convexHull Real ({b, c} : Set Complex),
      ρ ≤ ‖w - a‖ := by
    intro w hw
    rw [convexHull_pair] at hw
    rcases hseg.1 hw with hb | hc
    · have hwb : dist w b ≤ s := Metric.mem_closedBall.mp hb
      have htri := dist_triangle a w b
      rw [hab] at htri
      have hnorm : dist a w = ‖w - a‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      linarith [hnorm]
    · have hwc : dist w c ≤ t := Metric.mem_closedBall.mp hc
      have htri := dist_triangle a w c
      rw [hac] at htri
      have hnorm : dist a w = ‖w - a‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      linarith [hnorm]
  have hnonempty : ({b, c} : Set Complex).Nonempty := ⟨b, by simp⟩
  have hrad := (P5050T1RadialSection a ρ {b, c} hρ hnonempty hsep).2
  have hset : ({a, b, c} : Set Complex) = insert a ({b, c} : Set Complex) := by
    ext z
    simp []
  rw [hset] at hrad
  exact hrad

end ApollonianSuperharmonic

end
