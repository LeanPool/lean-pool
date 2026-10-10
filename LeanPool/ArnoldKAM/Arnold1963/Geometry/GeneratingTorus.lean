/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingTransformation
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealCover

/-!
Real restrictions and descent to the physical angle torus, including representative
independence and injectivity on the quotient.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

theorem complexifyPhase_shift {n : ℕ} (k : FourierIndex n) (x : RealPhaseCover n) :
    complexifyPhase (realPhaseShift k x) = phaseShift k (complexifyPhase x) := by
  apply Prod.ext
  · rfl
  · funext j
    simp [complexifyPhase, realPhaseShift, phaseShift, complexify, realAngleShift, angleShift]

theorem realPartPhase_shift {n : ℕ} (k : FourierIndex n) (x : ComplexPhaseSpace n) :
    realPartPhase (phaseShift k x) = realPhaseShift k (realPartPhase x) := by
  apply Prod.ext
  · rfl
  · funext j
    simp [realPartPhase, realPhaseShift, phaseShift, realPart,
      realAngleShift, angleShift, complexify]

/-- The generating transformation restricted to unwrapped real phase coordinates. -/
def generatingRealTransform {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G : Set (ComplexSpace n)) (ρ r : ℝ≥0) (x : RealPhaseCover n) : RealPhaseCover n :=
  realPartPhase (generatingTransform S G (angleStrip n ρ) r (complexifyPhase x))

/-- The generating transformation descended to real angles modulo `2π`. -/
def generatingTorusTransform {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G : Set (ComplexSpace n)) (ρ r : ℝ≥0) (x : RealPhaseSpace n) : RealPhaseSpace n :=
  torusProjection (generatingRealTransform S G ρ r (torusRepresentative x))

theorem complexifyPhase_mem_generatingTarget {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ r : ℝ≥0} (hρ : r + r + r ≤ ρ) {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (erosion G (r + r))) :
    complexifyPhase x ∈ generatingTarget G (angleStrip n ρ) r :=
  phaseDomain_subset_generatingTarget G hρ ⟨hx, complexify_mem_angleStrip _ _⟩

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0} {M : ℝ}
  (S : AnalyticPhaseFunction n G ρ) (d : GeneratingData S.toFun G (angleStrip n ρ) r M)
  (hρ : r + r + r ≤ ρ)

include S d hρ

theorem generatingTransform_real {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (erosion G (r + r))) :
    complexifyPhase (generatingRealTransform S.toFun G ρ r x) =
      generatingTransform S.toFun G (angleStrip n ρ) r (complexifyPhase x) := by
  apply complexifyPhase_realPartPhase_of_conj
  have hh := S.generatingTransform_conj d (complexifyPhase_mem_generatingTarget hρ hx)
  simpa only [conjPhase_complexifyPhase] using hh.symm

theorem generatingRealTransform_mapsTo {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (erosion G (r + r))) :
    (generatingRealTransform S.toFun G ρ r x).1 ∈ realSlice G := by
  have hm := (d.transform_mapsTo (complexifyPhase_mem_generatingTarget hρ hx)).1
  have he := congrArg Prod.fst (S.generatingTransform_real d hρ hx)
  change (complexifyPhase (generatingRealTransform S.toFun G ρ r x)).1 ∈ G
  rw [he]
  exact hm

theorem generatingRealTransform_shift {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (erosion G (r + r))) (k : FourierIndex n) :
    generatingRealTransform S.toFun G ρ r (realPhaseShift k x) =
      realPhaseShift k (generatingRealTransform S.toFun G ρ r x) := by
  unfold generatingRealTransform
  rw [complexifyPhase_shift,
    S.generatingTransform_shift d (complexifyPhase_mem_generatingTarget hρ hx)]
  exact realPartPhase_shift k _

theorem generatingTorusTransform_projection {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (erosion G (r + r))) :
    generatingTorusTransform S.toFun G ρ r (torusProjection x) =
      torusProjection (generatingRealTransform S.toFun G ρ r x) := by
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff (torusRepresentative (torusProjection x)) x).1
    (torusProjection_representative _)
  unfold generatingTorusTransform
  rw [hk, S.generatingRealTransform_shift d hρ hx, torusProjection_shift]

theorem generatingTorusTransform_mapsTo : MapsTo (generatingTorusTransform S.toFun G ρ r)
    (realSlice (erosion G (r + r)) ×ˢ (univ : Set (RealTorus n)))
    (realSlice G ×ˢ (univ : Set (RealTorus n))) := by
  intro x hx
  exact ⟨S.generatingRealTransform_mapsTo d hρ (x := torusRepresentative x) hx.1, mem_univ _⟩

theorem generatingTorusTransform_injOn : InjOn (generatingTorusTransform S.toFun G ρ r)
    (realSlice (erosion G (r + r)) ×ˢ (univ : Set (RealTorus n))) := by
  intro x hx y hy he
  change torusProjection (generatingRealTransform S.toFun G ρ r (torusRepresentative x)) =
    torusProjection (generatingRealTransform S.toFun G ρ r (torusRepresentative y)) at he
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff
    (generatingRealTransform S.toFun G ρ r (torusRepresentative x))
    (generatingRealTransform S.toFun G ρ r (torusRepresentative y))).1 he
  have hB := congrArg complexifyPhase hk
  rw [S.generatingTransform_real d hρ (x := torusRepresentative x) hx.1, complexifyPhase_shift,
    S.generatingTransform_real d hρ (x := torusRepresentative y) hy.1] at hB
  have hy' := complexifyPhase_mem_generatingTarget hρ (x := torusRepresentative y) hy.1
  rw [← S.generatingTransform_shift d hy' k] at hB
  have hi := d.transform_injOn
    (complexifyPhase_mem_generatingTarget hρ (x := torusRepresentative x) hx.1)
    (shift_generatingTarget hy' k) hB
  rw [← complexifyPhase_shift] at hi
  have hr := congrArg realPartPhase hi
  simp only [realPartPhase_complexifyPhase] at hr
  have ht := (torusProjection_eq_iff (torusRepresentative x) (torusRepresentative y)).2 ⟨k, hr⟩
  simpa only [torusProjection_representative] using ht

end AnalyticPhaseFunction
end KamProject.Arnold1963
