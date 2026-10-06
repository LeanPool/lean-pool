/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# A countable dense family of solenoidal test fields

The space `J` of `def:leray-hopf` has a countable set of smooth compactly
supported solenoidal fields that is dense in the `L²` sense. This lets the
pressure-free weak equation be tested against every element of `J` at almost
every time (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Smooth compactly supported solenoidal vector fields. -/
@[expose] def LpsSolenoidalTest : Set (Vec3 → Vec3) :=
  {ψ | ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
    ∀ x, ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x = 0}

/-- The `L²` space of vector fields on `ℝ³`. -/
@[expose] abbrev LpsVecL2 : Type := Lp (Fin 3 → ℝ) 2 (volume : Measure Vec3)

/-- Countably many smooth compactly supported solenoidal fields approximate
every element of `J` in `L²`. -/
theorem lps_exists_countable_solenoidal_dense :
    ∃ D : Set (Vec3 → Vec3), D.Countable ∧ D ⊆ LpsSolenoidalTest ∧
      ∀ w : Vec3 → Vec3, IsInJ w → ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ ψ ∈ D, eLpNorm (fun x => ψ x - w x) 2 volume < ε := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let T : Set LpsVecL2 := {f | ∃ ψ ∈ LpsSolenoidalTest, (f : Vec3 → Vec3) =ᵐ[volume] ψ}
  have hsep : IsSeparable T :=
    (isSeparable_univ_iff.mpr (inferInstance : SeparableSpace LpsVecL2)).mono (subset_univ _)
  obtain ⟨c, hcT, hccount, hTc⟩ := hsep.exists_countable_dense_subset
  choose! ψ hψS hψeq using fun f : LpsVecL2 => (show f ∈ T → ∃ ψ ∈ LpsSolenoidalTest,
    (f : Vec3 → Vec3) =ᵐ[volume] ψ from id)
  refine ⟨ψ '' c, hccount.image _, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hψS f (hcT hf)
  · intro w hw ε hε
    obtain ⟨hw2, aSeq, hsmooth, hcompact, hdiv, hlim⟩ := hw
    let η : ℝ≥0∞ := min (ε / 3) 1
    have hη0 : 0 < η := lt_min (ENNReal.div_pos hε.ne' (by norm_num)) one_pos
    have hηtop : η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop_zero.mp hlim) η hη0
    have hkS : aSeq k ∈ LpsSolenoidalTest := ⟨hsmooth k, hcompact k, hdiv k⟩
    have hmem : MemLp (aSeq k) 2 volume :=
      ((hsmooth k).continuous.memLp_of_hasCompactSupport (hcompact k))
    let fk : LpsVecL2 := hmem.toLp (aSeq k)
    have hfkT : fk ∈ T := ⟨aSeq k, hkS, hmem.coeFn_toLp⟩
    have hclose : fk ∈ closure c := hTc hfkT
    obtain ⟨f, hfc, hfdist⟩ := Metric.mem_closure_iff.mp hclose η.toReal
      (ENNReal.toReal_pos hη0.ne' hηtop)
    have hψf := hψeq f (hcT hfc)
    have hfk : (fk : Vec3 → Vec3) =ᵐ[volume] aSeq k := hmem.coeFn_toLp
    have hdiffNorm : eLpNorm (fun x => aSeq k x - ψ f x) 2 volume < η := by
      have h1 : eLpNorm (fun x => aSeq k x - ψ f x) 2 volume =
          eLpNorm (⇑(fk - f)) 2 volume := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [Lp.coeFn_sub fk f, hψf, hfk] with x h1 h2 h3
        simp only [h1, Pi.sub_apply, ← h2, h3]
      rw [h1]
      have h2 : ‖fk - f‖ < η.toReal := by rwa [dist_eq_norm] at hfdist
      rw [Lp.norm_def] at h2
      have h3 : eLpNorm (⇑(fk - f)) 2 volume ≠ ⊤ := Lp.eLpNorm_ne_top _
      calc eLpNorm (⇑(fk - f)) 2 volume = ENNReal.ofReal
            (eLpNorm (⇑(fk - f)) 2 volume).toReal := (ENNReal.ofReal_toReal h3).symm
        _ < ENNReal.ofReal η.toReal := (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hη0.ne' hηtop)).mpr h2
        _ = η := ENNReal.ofReal_toReal hηtop
    refine ⟨ψ f, ⟨f, hfc, rfl⟩, ?_⟩
    have hsplit : eLpNorm (fun x => ψ f x - w x) 2 volume ≤
        eLpNorm (fun x => aSeq k x - ψ f x) 2 volume +
          eLpNorm (fun x => aSeq k x - w x) 2 volume := by
      have h := eLpNorm_sub_le (f := fun x => aSeq k x - ψ f x)
        (g := fun x => aSeq k x - w x) (μ := volume) (p := 2) (by norm_num)
      have hc : eLpNorm (fun x => ψ f x - w x) 2 volume =
          eLpNorm ((fun x => aSeq k x - w x) - fun x => aSeq k x - ψ f x) 2 volume := by
        refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
        simp
      rw [hc, add_comm]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      rw [add_comm]
    calc eLpNorm (fun x => ψ f x - w x) 2 volume
        ≤ eLpNorm (fun x => aSeq k x - ψ f x) 2 volume +
          eLpNorm (fun x => aSeq k x - w x) 2 volume := hsplit
      _ < η + η := ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top hηtop (hk k le_rfl)) hdiffNorm (hk k le_rfl)
      _ ≤ ε / 3 + ε / 3 := add_le_add (min_le_left _ _) (min_le_left _ _)
      _ ≤ ε := by
        rw [← two_mul, mul_comm]
        calc ε / 3 * 2 ≤ ε / 3 * 3 := by gcongr; norm_num
          _ = ε := by rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

end ESS

end
