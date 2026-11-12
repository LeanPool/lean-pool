/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Complex.Basic

-- [TABLET NODE: P5050T1RadialSection]

/-!
# P5050T1RadialSection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5050T1RadialSection (a : Complex) (ρ : Real) (S : Set Complex)
      (hρ : 0 < ρ) (hS : S.Nonempty)
      (hsep : ∀ w ∈ convexHull Real S, ρ ≤ ‖w - a‖) :
      Metric.sphere a ρ ∩ convexHull Real (insert a S) =
        (fun w => a + (ρ / ‖w - a‖) • (w - a)) '' convexHull Real S ∧
      IsPreconnected (Metric.sphere a ρ ∩ convexHull Real (insert a S)) := by
-- BODY
    let K := convexHull Real S
    let F : Complex → Complex := fun w => a + (ρ / ‖w - a‖) • (w - a)
    have hK : IsPreconnected K := by
      apply Convex.isPreconnected
      exact convex_convexHull Real S
    have hcont : ContinuousOn F K := by
      have hsub : Continuous (fun w : Complex => w - a) := by fun_prop
      have hsq : Continuous (fun w : Complex => Complex.normSq (w - a)) :=
        Complex.continuous_normSq.comp hsub
      have hn : Continuous (fun w : Complex => ‖w - a‖) := by
        convert Real.continuous_sqrt.comp hsq using 1
        ext w
        change ‖w - a‖ = Real.sqrt (Complex.normSq (w - a))
        rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (norm_nonneg (w - a))]
      have hq : ContinuousOn (fun w : Complex => ρ / ‖w - a‖) K := by
        apply ContinuousOn.div continuousOn_const hn.continuousOn
        intro w hw
        exact ne_of_gt (lt_of_lt_of_le hρ (hsep w hw))
      change ContinuousOn (fun w : Complex => a + (ρ / ‖w - a‖) • (w - a)) K
      exact continuousOn_const.add (hq.smul (continuousOn_id.sub continuousOn_const))
    have heq : Metric.sphere a ρ ∩ convexHull Real (insert a S) = F '' K := by
      ext z
      constructor
      · rintro ⟨hz, hzK⟩
        rw [convexHull_insert hS, mem_convexJoin] at hzK
        rcases hzK with ⟨x, hx, w, hw, hzw⟩
        simp only [Set.mem_singleton_iff] at hx
        subst x
        rw [segment_eq_image_lineMap] at hzw
        rcases hzw with ⟨t, ht, hzt⟩
        have hzt' : z - a = t • (w - a) := by
          calc
            z - a = AffineMap.lineMap a w t - a := by rw [hzt]
            _ = t • (w - a) := by rw [AffineMap.lineMap_apply_module']; module
        have hn : ρ = t * ‖w - a‖ := by
          have hz' : ‖z - a‖ = ρ := by
            simpa [Metric.mem_sphere, dist_eq_norm] using hz
          rw [← hz', hzt', Complex.real_smul, Complex.norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg ht.1]
        have hden : ‖w - a‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hρ (hsep w hw))
        have htval : t = ρ / ‖w - a‖ := by
          rw [hn]
          field_simp
        refine ⟨w, hw, ?_⟩
        have hline : a + (ρ / ‖w - a‖) • (w - a) = AffineMap.lineMap a w t := by
          rw [AffineMap.lineMap_apply_module', ← htval]
          module
        simpa [F] using hline.trans hzt
      · rintro ⟨w, hw, rfl⟩
        have hden : 0 < ‖w - a‖ := lt_of_lt_of_le hρ (hsep w hw)
        have hu : 0 < ρ / ‖w - a‖ := div_pos hρ hden
        have hu1 : ρ / ‖w - a‖ ≤ 1 := (div_le_one hden).2 (hsep w hw)
        have hseg : F w ∈ segment Real a w := by
          rw [segment_eq_image_lineMap]
          refine ⟨ρ / ‖w - a‖, ⟨le_of_lt hu, hu1⟩, ?_⟩
          change AffineMap.lineMap a w (ρ / ‖w - a‖) = _
          rw [AffineMap.lineMap_apply_module']
          module
        have hconv : Convex Real (convexHull Real (insert a S)) :=
          convex_convexHull Real (insert a S)
        have ha : a ∈ convexHull Real (insert a S) := subset_convexHull Real _ (by simp)
        have hw' : w ∈ convexHull Real (insert a S) :=
          (convexHull_mono (Set.subset_insert a S)) hw
        refine ⟨?_, hconv.segment_subset ha hw' hseg⟩
        rw [Metric.mem_sphere, dist_eq_norm]
        change ‖a + (ρ / ‖w - a‖) • (w - a) - a‖ = ρ
        rw [show a + (ρ / ‖w - a‖) • (w - a) - a =
          (ρ / ‖w - a‖) • (w - a) by module]
        rw [Complex.real_smul, Complex.norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hu]
        field_simp
    exact ⟨heq, heq ▸ hK.image F hcont⟩

end ApollonianSuperharmonic

end
