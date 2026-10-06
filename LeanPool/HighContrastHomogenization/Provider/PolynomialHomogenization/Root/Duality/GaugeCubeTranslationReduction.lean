/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.NegSobolevTranslation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.GaugeCubeTranslationReduction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Moving the gauge-cube Hodge hypothesis off the translation

The gauge image of an adapted-cell witness is a triadic cube translated by an
arbitrary real vector.  Every ingredient of the Hodge hypothesis — the two
Hodge predicates, vector `L²` membership, and the negative fractional norm —
is translation invariant, so the hypothesis at the translated cube follows from
the same hypothesis at the cube itself, with the same constant.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Vector `L²` membership pulls back along a translation. -/
theorem memVectorL2_translateSet {S : Set (Vec d)} {F : Vec d → Vec d}
    (z : Vec d) (hF : MemVectorL2 (translateSet z S) F) :
    MemVectorL2 S (fun y => F (y + z)) := by
  have hmap : Measure.map (fun x : Vec d => x + z) (volume.restrict S) =
      volume.restrict (translateSet z S) :=
    (measurePreserving_addRight_restrict_translateSet z S).map_eq
  have hmem : MemLp F 2
      (Measure.map (fun x : Vec d => x + z) (volume.restrict S)) := by
    rw [hmap]
    exact hF
  exact hmem.comp_of_map (measurable_id.add_const z).aemeasurable

/-- **The gauge-cube Hodge hypothesis moves off an arbitrary translation.** -/
theorem gaugeHodgeHypothesis_translateSet (z : Vec d) (S : Set (Vec d))
    (A : Mat d) {s C : ℝ}
    (hbase : ∀ w F : Vec d → Vec d, MemVectorL2 S F →
      IsPotentialZeroTraceOn S w →
      IsSolenoidalOn S (fun y => matVecMul A (w y) + F y) →
      negSobolevNorm S s w ≤ ENNReal.ofReal C * negSobolevNorm S s F) :
    ∀ w F : Vec d → Vec d, MemVectorL2 (translateSet z S) F →
      IsPotentialZeroTraceOn (translateSet z S) w →
      IsSolenoidalOn (translateSet z S) (fun y => matVecMul A (w y) + F y) →
      negSobolevNorm (translateSet z S) s w ≤
        ENNReal.ofReal C * negSobolevNorm (translateSet z S) s F := by
  intro w F hF hw hsol
  have hset : translateSet (-z) (translateSet z S) = S := by
    rw [translateSet_translateSet]
    simp
  have hw0 : IsPotentialZeroTraceOn S (fun y => w (y + z)) := by
    have h := isPotentialZeroTraceOn_translateSet hw (-z)
    rw [hset] at h
    simpa [sub_neg_eq_add] using h
  have hsol0 : IsSolenoidalOn S
      (fun y => matVecMul A (w (y + z)) + F (y + z)) := by
    have h := isSolenoidalOn_translateSet hsol (-z)
    rw [hset] at h
    simpa [sub_neg_eq_add] using h
  have hF0 : MemVectorL2 S (fun y => F (y + z)) := memVectorL2_translateSet z hF
  have hmain := hbase _ _ hF0 hw0 hsol0
  have hwEq : negSobolevNorm (translateSet z S) s w =
      negSobolevNorm S s (fun y => w (y + z)) := by
    have h := negSobolevNorm_translateSet z S s (fun y => w (y + z))
    have hfun : (fun x : Vec d => (fun y => w (y + z)) (x - z)) = w := by
      funext x
      have hx : x - z + z = x := by abel
      simp only [hx]
    rwa [hfun] at h
  have hFEq : negSobolevNorm (translateSet z S) s F =
      negSobolevNorm S s (fun y => F (y + z)) := by
    have h := negSobolevNorm_translateSet z S s (fun y => F (y + z))
    have hfun : (fun x : Vec d => (fun y => F (y + z)) (x - z)) = F := by
      funext x
      have hx : x - z + z = x := by abel
      simp only [hx]
    rwa [hfun] at h
  rw [hwEq, hFEq]
  exact hmain

end

end RowSupply
end HighContrast
end HCPolySupport
