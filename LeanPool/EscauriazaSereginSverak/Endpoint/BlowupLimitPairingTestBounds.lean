/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Bounds for derivatives of smooth spatial tests

Smooth compactly supported vector tests have finite space-time `L∞`
derivative bounds on every compact cylinder.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem blowupLimit_component_hasCompactSupport
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hC : IsCompact C) (hwsupport : tsupport w ⊆ C)
    (i : Fin 3) : HasCompactSupport (fun x => (w x).ofLp i) := by
  have hcomponent : tsupport (fun x : Vec3 => (w x).ofLp i) ⊆ tsupport w := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      apply hx
      have hzero : w x = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [hzero]
    · exact isClosed_tsupport w
  exact HasCompactSupport.of_support_subset_isCompact hC
    ((subset_tsupport _).trans (hcomponent.trans hwsupport))

/-- Uniform `L∞` bounds for the spatial derivatives of a smooth compactly
supported test on a compact spacetime cylinder. -/
theorem blowup_limit_smooth_test_derivative_bounds
    {C : Set Vec3} (hC : IsCompact C) (a b : ℝ)
    (w : Vec3 → L2Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupport : tsupport w ⊆ C) :
    ∃ Mtest Mdiv : ℝ≥0∞,
      Mtest < ⊤ ∧ Mdiv < ⊤ ∧
      (∀ i j, MemLp
          (fun z : ParabolicPoint =>
            spatialDeriv (fun x => (w x).ofLp i) j z.1)
          ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
        eLpNorm
          (fun z : ParabolicPoint =>
            spatialDeriv (fun x => (w x).ofLp i) j z.1)
          ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mtest) ∧
      (MemLp
          (fun z : ParabolicPoint =>
            ∑ i : Fin 3, spatialDeriv (fun x => (w x).ofLp i) i z.1)
          ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
        eLpNorm
          (fun z : ParabolicPoint =>
            ∑ i : Fin 3, spatialDeriv (fun x => (w x).ofLp i) i z.1)
          ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mdiv) := by
  let μ : Measure ParabolicPoint := volume.restrict (C ×ˢ Icc a b)
  have hderiv (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint =>
        spatialDeriv (fun x => (w x).ofLp i) j z.1) ⊤ μ := by
    have hcomponentSmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => (w x).ofLp i) := by
      have hofLp : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : L2Vec3 => v.ofLp) :=
        PiLp.contDiff_ofLp (𝕜 := ℝ)
          (E := fun _ : Fin 3 => ℝ) (p := (2 : ℝ≥0∞))
      have hcoordinate : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : Vec3 => v i) := contDiff_apply ℝ ℝ i
      have hmap : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : L2Vec3 => (v.ofLp : Vec3)) := hofLp
      exact (hcoordinate.comp hmap).comp hw
    have hcomponentCompact : HasCompactSupport
        (fun x : Vec3 => (w x).ofLp i) :=
      blowupLimit_component_hasCompactSupport hC hwsupport i
    have hbound := vorticitySmooth_derivative_bounds
      hcomponentSmooth hcomponentCompact
    obtain ⟨L, hL, hLbound, _⟩ := hbound
    have hcontinuous : Continuous (fun z : ParabolicPoint =>
        spatialDeriv (fun x => (w x).ofLp i) j z.1) :=
      (CKN.contDiff_spatialDeriv_smooth hcomponentSmooth j).continuous.comp
        (continuous_fst.comp continuous_parabolicPoint_to_prod)
    apply memLp_top_of_bound hcontinuous.aestronglyMeasurable L
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    exact hLbound z.1 j
  have hderivLp (i j : Fin 3) :
      eLpNorm
        (fun z : ParabolicPoint =>
          spatialDeriv (fun x => (w x).ofLp i) j z.1)
        ⊤ μ < ⊤ := (hderiv i j).eLpNorm_lt_top
  let Mtest : ℝ≥0∞ := ∑ i : Fin 3, ∑ j : Fin 3,
    eLpNorm
      (fun z : ParabolicPoint =>
        spatialDeriv (fun x => (w x).ofLp i) j z.1)
      ⊤ μ
  have hMtest : Mtest < ⊤ := by
    dsimp [Mtest]
    exact ENNReal.sum_lt_top.2 fun i _ =>
      ENNReal.sum_lt_top.2 fun j _ => hderivLp i j
  have hderivBound (i j : Fin 3) :
      eLpNorm
        (fun z : ParabolicPoint =>
          spatialDeriv (fun x => (w x).ofLp i) j z.1)
        ⊤ μ ≤ Mtest := by
    dsimp [Mtest]
    calc
      eLpNorm
          (fun z : ParabolicPoint =>
            spatialDeriv (fun x => (w x).ofLp i) j z.1)
          ⊤ μ ≤ ∑ j : Fin 3, eLpNorm
              (fun z : ParabolicPoint =>
                spatialDeriv (fun x => (w x).ofLp i) j z.1)
              ⊤ μ :=
        Finset.single_le_sum
          (f := fun l : Fin 3 => eLpNorm
            (fun z : ParabolicPoint =>
              spatialDeriv (fun x => (w x).ofLp i) l z.1)
            ⊤ μ)
          (fun _ _ => bot_le) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm
            (fun z : ParabolicPoint =>
              spatialDeriv (fun x => (w x).ofLp i) j z.1)
            ⊤ μ :=
        Finset.single_le_sum
          (f := fun k : Fin 3 => ∑ l : Fin 3, eLpNorm
            (fun z : ParabolicPoint =>
              spatialDeriv (fun x => (w x).ofLp k) l z.1)
            ⊤ μ)
          (fun _ _ => bot_le) (Finset.mem_univ i)
  have hdiv : MemLp
      (fun z : ParabolicPoint =>
        ∑ i : Fin 3, spatialDeriv (fun x => (w x).ofLp i) i z.1)
      ⊤ μ := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact hderiv i i
  let Mdiv : ℝ≥0∞ := eLpNorm
    (fun z : ParabolicPoint =>
      ∑ i : Fin 3, spatialDeriv (fun x => (w x).ofLp i) i z.1)
    ⊤ μ
  have hMdiv : Mdiv < ⊤ := by
    exact hdiv.eLpNorm_lt_top
  refine ⟨Mtest, Mdiv, hMtest, hMdiv, ?_, ?_⟩
  · intro i j
    exact ⟨hderiv i j, hderivBound i j⟩
  · exact ⟨hdiv, le_rfl⟩

end ESS

end
