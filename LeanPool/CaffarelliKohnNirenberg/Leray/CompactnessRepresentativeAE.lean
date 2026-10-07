/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientBumps
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Compactness Representative AE

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Eventual fixed-scale identification with mollifications of an `L²`
slice identifies the measurable limit with that slice almost everywhere. -/
theorem compactnessMollifiedLimit_ae_eq_weak_slice_on
    {I : Set ℝ} {K : Set Vec3} (hK : MeasurableSet K)
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (V : I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hfixed : ∀ (t : I) x, x ∈ K → ∀ i : Fin 3,
      ∀ᶠ m : ℕ in atTop,
        limUnder atTop (fun k : ℕ =>
          CKN.mollify (fun y : Vec3 => u (σ k) (y,t.1) i)
            (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x) =
          CKN.mollify (fun y : Vec3 => V t y i)
            (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x) :
    ∀ t : I, ∀ᵐ x ∂(volume.restrict K),
      compactnessMollifiedLimit u σ (x,t.1) =
        fun i => V t x i := by
  intro t
  suffices hcoord : ∀ i : Fin 3, ∀ᵐ x ∂(volume.restrict K),
      compactnessMollifiedLimit u σ (x,t.1) i = V t x i by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    funext i
    exact hx i
  intro i
  have hvi : MemLp (fun y : Vec3 => V t y i) 2
      (volume : Measure Vec3) := by
    have hproj := (Lp.memLp (V t)).continuousLinearMap_comp
      (PiLp.proj 2 (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) i)
    simpa only [PiLp.proj_apply] using hproj
  have hloc : LocallyIntegrable (fun y : Vec3 => V t y i) volume :=
    hvi.locallyIntegrable (by norm_num)
  have hlim := CKN.ae_tendsto_mollify_sliceRadius hloc
  filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae hlim] with x hxK hx
  have hEq := hfixed t x hxK i
  have hpoint : Tendsto
      (fun m : ℕ => limUnder atTop (fun k : ℕ =>
        CKN.mollify (fun y : Vec3 => u (σ k) (y,t.1) i)
          (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x))
      atTop (nhds (V t x i)) :=
    Filter.Tendsto.congr' (hEq.mono fun m hm => hm.symm) hx
  change (limUnder atTop (fun m : ℕ => limUnder atTop (fun k : ℕ =>
    CKN.mollify (fun y : Vec3 => u (σ k) (y,t.1) i)
      (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x))) = V t x i
  exact hpoint.limUnder_eq

end CKN.Leray
