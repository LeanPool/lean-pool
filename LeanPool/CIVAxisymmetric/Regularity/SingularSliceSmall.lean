/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.SingularSlice
public import LeanPool.CIVAxisymmetric.Regularity.TopBoundaryEpsilon
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# A lower bound on the Theorem A quantity at a singular point of the blow-up slice

At a point of the singular set of the blow-up-time slice, the dimensionless smallness
quantity of `CIV.norm_le_of_small_L3_top_of_continuousOn` cannot be small on any backward
cylinder based at that point: were it small, the continuous ε-regularity conclusion would give
an everywhere bound on `u` near the point, contradicting singularity. This is the contrapositive
used at step 2 of design note R12.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- At a point of `singularSlice u`, the Theorem A smallness quantity exceeds `ε₀ r²` on every
backward cylinder of radius `r ≤ 1` centered there and contained in the unit ball, for the same
universal `ε₀` as `CIV.norm_le_of_small_L3_top_of_continuousOn`. -/
theorem lintegral_gt_of_mem_singularSlice (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution (vec3Ball 0 1) (Set.Ioo (-1 : ℝ) 0) q u Du p f →
        ContinuousOn (fun z : Vec3 × ℝ => u z) unitCylinder →
        ∀ (x : Vec3) (r : ℝ), 0 < r → r ≤ 1 → vec3Ball x r ⊆ vec3Ball 0 1 →
        x ∈ singularSlice u →
        ENNReal.ofReal (ε₀ * r ^ 2) <
          ∫⁻ z in (vec3Ball x r) ×ˢ Set.Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (r ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q := by
  obtain ⟨ε₀, hε₀, K, hK, hmain⟩ := norm_le_of_small_L3_top_of_continuousOn q hq
  refine ⟨ε₀, hε₀, ?_⟩
  intro u Du p f hsol hcont x r hr hr1 hsub hxsing
  by_contra hcon
  rw [not_lt] at hcon
  refine hxsing ⟨r / 2, K / r, by positivity, ?_⟩
  intro y hy t ht
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
  have htime : Set.Ioo (-(r ^ 2)) (0 : ℝ) ⊆ Set.Ioo (-1) 0 :=
    Set.Ioo_subset_Ioo (by linarith only [hr2]) le_rfl
  have htime' : Set.Ioo (-(r ^ 2) / 4) (0 : ℝ) ⊆ Set.Ioo (-1) 0 :=
    Set.Ioo_subset_Ioo (by linarith only [hr2]) le_rfl
  have hQ : vec3Ball x r ×ˢ Set.Ioo (-(r ^ 2)) 0 ⊆
      spaceTimeSet (vec3Ball 0 1) (Set.Ioo (-1 : ℝ) 0) :=
    Set.prod_mono hsub htime
  have hballHalf : vec3Ball x (r / 2) ⊆ vec3Ball 0 1 :=
    (vec3Ball_mono (by linarith only [hr])).trans hsub
  have hcontOn : ContinuousOn (fun z : Vec3 × ℝ => u z)
      (vec3Ball x (r / 2) ×ˢ Set.Ioo (-(r ^ 2) / 4) 0) :=
    hcont.mono (Set.prod_mono hballHalf htime')
  have hz : (y, t) ∈ vec3Ball x (r / 2) ×ˢ Set.Ioo (-(r ^ 2) / 4) (0 : ℝ) := by
    refine ⟨hy, ?_⟩
    have heq : (-(r ^ 2) / 4 : ℝ) = -((r / 2) ^ 2) := by ring
    rw [heq]
    exact ht
  have hbound := hmain (vec3Ball 0 1) (Set.Ioo (-1) 0) u Du p f x r hr hsol hQ hcon hcontOn
    (y, t) hz
  exact hbound

end CIV
