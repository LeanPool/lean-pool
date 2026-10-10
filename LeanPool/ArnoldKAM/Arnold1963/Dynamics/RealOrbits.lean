/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Dynamics.LimitConjugacy
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingTorus

/-!
Real limit maps, quotient maps, and actual invariant trajectories on the angle torus.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The real-coordinate restriction of the limiting phase transformation. -/
def realLimitMap (x : RealPhaseCover n) : RealPhaseCover n :=
  realPartPhase (h.limitMap b (complexifyPhase x))

/-- The limiting phase transformation descended to real angles modulo `2π`. -/
def torusLimitMap (x : RealPhaseSpace n) : RealPhaseSpace n :=
  torusProjection (h.realLimitMap b (torusRepresentative x))

theorem realLimitMap_shift {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) (k : FourierIndex n) :
    h.realLimitMap b (realPhaseShift k x) = realPhaseShift k (h.realLimitMap b x) := by
  have hz : complexifyPhase x ∈ h.limitPhase b :=
    h.commonPhase_subset b ⟨hx, complexify_mem_angleStrip _ _⟩
  unfold realLimitMap
  rw [complexifyPhase_shift, h.limitMap_periodic b hz]
  exact realPartPhase_shift k _

theorem torusLimitMap_projection {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) :
    h.torusLimitMap b (torusProjection x) = torusProjection (h.realLimitMap b x) := by
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff (torusRepresentative (torusProjection x)) x).mp
    (torusProjection_representative _)
  unfold torusLimitMap
  rw [hk, h.realLimitMap_shift b hx, torusProjection_shift]

theorem realLimitMap_maps {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) :
    (h.realLimitMap b x).1 ∈ realSlice h.domain := by
  have hz : complexifyPhase x ∈ h.limitPhase b :=
    h.commonPhase_subset b ⟨hx, complexify_mem_angleStrip _ _⟩
  have hm := (h.limitMap_maps b hz).1
  have he := congrArg Prod.fst (h.limitMap_real_value b hx)
  change (complexifyPhase (h.realLimitMap b x)).1 ∈ h.domain
  rw [realLimitMap, he]
  exact hm

theorem torusLimitMap_maps : MapsTo (h.torusLimitMap b)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))
    (realSlice h.domain ×ˢ (univ : Set (RealTorus n))) := by
  intro x hx
  exact ⟨h.realLimitMap_maps b (x := torusRepresentative x) hx.1, mem_univ _⟩

theorem orbit_eq_real_angle {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) (t : ℝ) : h.orbit b p q t =
      h.limitMap b (complexifyPhase (p, q + t • realPart (h.limitFrequency b (complexify p)))) := by
  unfold orbit
  congr 1
  apply Prod.ext
  · rfl
  change complexify q + (t : ℂ) • h.limitFrequency b (complexify p) =
    complexify (q + t • realPart (h.limitFrequency b (complexify p)))
  rw [← h.limitFrequency_real_value b hp]
  ext j
  simp [complexify, smul_eq_mul]

theorem orbit_real_value {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) (t : ℝ) :
    complexifyPhase (realPartPhase (h.orbit b p q t)) = h.orbit b p q t := by
  rw [h.orbit_eq_real_angle b hp q t]
  exact h.limitMap_real_value b (x := (p, q + t • realPart (h.limitFrequency b (complexify p)))) hp

theorem orbit_mem_torus_image {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) (t : ℝ) : torusProjection (realPartPhase (h.orbit b p q t)) ∈
      h.torusLimitMap b '' ({p} ×ˢ (univ : Set (RealTorus n))) := by
  let x : RealPhaseCover n := (p, q + t • realPart (h.limitFrequency b (complexify p)))
  refine ⟨torusProjection x, ⟨rfl, mem_univ _⟩, ?_⟩
  rw [h.torusLimitMap_projection b (x := x) hp, h.orbit_eq_real_angle b hp q t]
  rfl

end KamProject.Arnold1963.Iteration.InitialData
