/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3832T1ConeCollapse
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Tactic.FieldSimp

-- [TABLET NODE: P3832T1CollapsedConeDescent]

/-!
# P3832T1CollapsedConeDescent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3832T1CollapsedConeDescent {Y : Type*} [TopologicalSpace Y] :
    Function.Surjective P3832T1ConeCollapse ∧
      ∀ (g : C(Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, Y)) (c : Y),
        (∀ t : Set.Icc (0 : ℝ) 1, g (⟨0, by norm_num⟩, t) = c) →
        ∃ G : C({z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 //
            (z.2 : ℝ) ≤ z.1}, Y),
          ∀ z, G (P3832T1ConeCollapse z) = g z := by
-- BODY
  classical
  let SectorInterval := Set.Icc (0 : ℝ) 1
  let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
  let sectorCollapse := P3832T1ConeCollapse
  have sectorCollapse_continuous : Continuous sectorCollapse := by
    unfold sectorCollapse P3832T1ConeCollapse
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
  have sectorCollapse_surjective : Function.Surjective sectorCollapse := by
    intro z
    by_cases hr : (z.1.1 : ℝ) = 0
    · have hb : (z.1.2 : ℝ) = 0 :=
        le_antisymm (by simpa [hr] using z.2) z.1.2.2.1
      refine ⟨(z.1.1, ⟨0, by norm_num [SectorInterval]⟩), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [sectorCollapse, P3832T1ConeCollapse, hb]
    · have hrpos : 0 < (z.1.1 : ℝ) := lt_of_le_of_ne z.1.1.2.1 (Ne.symm hr)
      let t : SectorInterval := ⟨(z.1.2 : ℝ) / z.1.1,
        div_nonneg z.1.2.2.1 z.1.1.2.1,
        (div_le_one hrpos).2 z.2⟩
      refine ⟨(z.1.1, t), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change (z.1.1 : ℝ) * ((z.1.2 : ℝ) / z.1.1) = z.1.2
        field_simp
  have sectorConeDescent (g : C(SectorInterval × SectorInterval, Y)) (c : Y)
      (hzero : ∀ t : SectorInterval, g (⟨0, by norm_num [SectorInterval]⟩, t) = c) :
      ∃ G : C(SectorCone, Y), ∀ z, G (sectorCollapse z) = g z := by
    have hf : Function.FactorsThrough g sectorCollapse := by
      intro x y hxy
      have hfirst : x.1 = y.1 := congrArg (fun z : SectorCone => z.1.1) hxy
      have hmul : (x.1 : ℝ) * x.2 = (y.1 : ℝ) * y.2 :=
        congrArg (fun z : SectorCone => (z.1.2 : ℝ)) hxy
      by_cases hr : (x.1 : ℝ) = 0
      · have hx : x.1 = ⟨0, by norm_num [SectorInterval]⟩ := Subtype.ext hr
        have hy : y.1 = ⟨0, by norm_num [SectorInterval]⟩ := hfirst.symm.trans hx
        calc
          g x = g (⟨0, by norm_num [SectorInterval]⟩, x.2) := congrArg g (Prod.ext hx rfl)
          _ = c := hzero _
          _ = g (⟨0, by norm_num [SectorInterval]⟩, y.2) := (hzero _).symm
          _ = g y := congrArg g (Prod.ext hy.symm rfl)
      · have ht : x.2 = y.2 := by
          apply Subtype.ext
          rw [← hfirst] at hmul
          exact mul_left_cancel₀ hr hmul
        exact congrArg g (Prod.ext hfirst ht)
    let q : C(SectorInterval × SectorInterval, SectorCone) :=
      ⟨sectorCollapse, sectorCollapse_continuous⟩
    have hq : Topology.IsQuotientMap q :=
      Topology.IsQuotientMap.of_surjective_continuous
        sectorCollapse_surjective sectorCollapse_continuous
    have hfactor : Function.FactorsThrough g q := hf
    refine ⟨hq.lift g hfactor, ?_⟩
    intro z
    exact congrArg (fun f : C(SectorInterval × SectorInterval, Y) => f z)
      (hq.lift_comp g hfactor)
  exact ⟨sectorCollapse_surjective, sectorConeDescent⟩

end ApollonianSuperharmonic

end
