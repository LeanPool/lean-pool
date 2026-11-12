/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3776T1TileContractions
public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Analysis.Normed.Module.Convex

-- [TABLET NODE: P3776T1TileContractionsExist]

/-!
# P3776T1TileContractionsExist

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TileContractionProof

private theorem scale_mem :
    (by
      classical
      exact
        let ball : Set (Real × Real) := Metric.closedBall (0 : Real × Real) 1
        ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ (x : (↑ball : Type)), t • (↑x : ℝ × ℝ) ∈ ball
    ) := by
  classical
  intro ball t ht x
  change dist (t • x.val) 0 ≤ 1
  have hx : ‖x.val‖ ≤ 1 := by
    have hxmem : x.val ∈ Metric.closedBall (0 : Real × Real) 1 := by
      simp [ball]
    have hx' := Metric.mem_closedBall.mp hxmem
    simpa [dist_eq_norm] using hx'
  have ht' := Set.mem_Icc.mp ht
  rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht'.1]
  have hm : t * ‖x.val‖ ≤ 1 * 1 := by
    calc
      t * ‖x.val‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hx ht'.1
      _ ≤ 1 * 1 := by nlinarith [ht'.2]
  simpa using hm

private theorem realization_translate :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let rep : ι → ι := fun a => Classical.choose (P.vertex_orbit_representatives a)
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period : ι → P.lattice := fun a => Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (∀ (a : ι), TileRealization (P.tile a) =
            (fun (z : ℝ × ℝ) => z + GaussianRealPoint (↑(period a) : GaussianInt)) ''
            TileRealization (P.tile (rep a)))
    ) := by
  classical
  intro ι P rep rep_spec period coord a
  have h := (TileTranslationFormulas (P.tile (rep a)) (period a : GaussianInt)).2.2.2.1
  calc
    TileRealization (P.tile a) =
        TileRealization (P.tile (P.shift (period a) (rep a))) := by
      exact congrArg (fun i => TileRealization (P.tile i)) (coord a)
    _ = TileRealization (TileTranslation (P.tile (rep a)) (period a : GaussianInt)) := by
      rw [P.tile_periodic]
    _ = (fun z : Real × Real => z + GaussianRealPoint (period a : GaussianInt)) ''
        TileRealization (P.tile (rep a)) := by
      rw [h]
      apply congrArg (fun f : (Real × Real) → (Real × Real) =>
        f '' TileRealization (P.tile (rep a)))
      funext z
      apply Prod.ext <;>
        simp [GaussianRealPoint, GaussianInt.intCast_re, GaussianInt.intCast_im]

private theorem local_continuous :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let ball : Set (Real × Real) := Metric.closedBall (0 : Real × Real) 1
        let diskMap (r : ι) : ball ≃ₜ TileRealization (P.tile r) :=
          Classical.choice (show Nonempty (ball ≃ₜ TileRealization (P.tile r)) from
            by simpa [ball, LatticeTile, TopologicalDisk] using P.tiles_are_disks r)
        ∀ (scale_mem : ∀ (t : Real), (t ∈ Set.Icc (0 : Real) 1) → (∀ (x : ball), t • x.val ∈ ball)),
        let localHomotopy (r : ι) (t : Real) (z : Real × Real) : Real × Real :=
          if hz : z ∈ TileRealization (P.tile r) then
            if ht : t ∈ Set.Icc (0 : Real) 1 then
              let x := (diskMap r).symm ⟨z, hz⟩
              ((diskMap r) ⟨t • x.val, scale_mem t ht x⟩).val
            else (diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩ |>.val
          else (diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩ |>.val
        let localDomain (r : ι) : Set (Real × (Real × Real)) :=
          Set.Icc (0 : Real) 1 ×ˢ TileRealization (P.tile r)
        ∀ (r : ι), ContinuousOn (fun (p : ℝ × ℝ × ℝ) => localHomotopy r p.1 p.2) (localDomain r)
    ) := by
  classical
  intro ι P ball diskMap scale_mem localHomotopy localDomain r
  rw [continuousOn_iff_continuous_domRestrict]
  let D := localDomain r
  let point : D → TileRealization (P.tile r) := fun p =>
    ⟨p.val.2, (Set.mem_prod.mp p.property).2⟩
  have hpoint : Continuous point := by
    apply Continuous.subtype_mk
    exact continuous_snd.comp continuous_subtype_val
  let x : D → ball := fun p => (diskMap r).symm (point p)
  have hx : Continuous x := (diskMap r).symm.continuous.comp hpoint
  let scaled : D → ball := fun p =>
    ⟨p.val.1 • (x p).val,
      scale_mem p.val.1 (Set.mem_prod.mp p.property).1 (x p)⟩
  have hscaled : Continuous scaled := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).smul
      (continuous_subtype_val.comp hx)
  let out : D → TileRealization (P.tile r) := fun p => (diskMap r) (scaled p)
  have hout : Continuous out := (diskMap r).continuous.comp hscaled
  have hval : Continuous (fun p : D => (out p).val) :=
    continuous_subtype_val.comp hout
  apply hval.congr
  intro p
  have hp := Set.mem_prod.mp p.property
  change (out p).val = localHomotopy r p.val.1 p.val.2
  unfold localHomotopy
  rw [dite_eq_left hp.2, dite_eq_left hp.1]

private theorem homotopy_continuous :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let rep : ι → ι := fun a => Classical.choose (P.vertex_orbit_representatives a)
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period : ι → P.lattice := fun a => Classical.choose (rep_spec a).2
        let ball : Set (Real × Real) := Metric.closedBall (0 : Real × Real) 1
        let diskMap (r : ι) : ball ≃ₜ TileRealization (P.tile r) :=
          Classical.choice (show Nonempty (ball ≃ₜ TileRealization (P.tile r)) from
            by simpa [ball, LatticeTile, TopologicalDisk] using P.tiles_are_disks r)
        let center (a : ι) : Real × Real :=
          (diskMap (rep a) ⟨0, by simp [ball, Metric.mem_closedBall]⟩).val +
            GaussianRealPoint (period a : GaussianInt)
        ∀ (scale_mem : ∀ (t : Real), (t ∈ Set.Icc (0 : Real) 1) → (∀ (x : ball), t • x.val ∈ ball)),
        let localHomotopy (r : ι) (t : Real) (z : Real × Real) : Real × Real :=
          if hz : z ∈ TileRealization (P.tile r) then
            if ht : t ∈ Set.Icc (0 : Real) 1 then
              let x := (diskMap r).symm ⟨z, hz⟩
              ((diskMap r) ⟨t • x.val, scale_mem t ht x⟩).val
            else (diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩ |>.val
          else (diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩ |>.val
        let homotopy (a : ι) (t : Real) (z : Real × Real) : Real × Real :=
          if z ∈ TileRealization (P.tile a) then
            localHomotopy (rep a) t (z - GaussianRealPoint (period a : GaussianInt)) +
              GaussianRealPoint (period a : GaussianInt)
          else center a
        let localDomain (r : ι) : Set (Real × (Real × Real)) :=
          Set.Icc (0 : Real) 1 ×ˢ TileRealization (P.tile r)
        (∀ (r : ι), ContinuousOn (fun p : Real × (Real × Real) => localHomotopy r p.1 p.2)
            (localDomain r)) → ((∀ (a : ι), ∀ (z : Real × Real), (z ∈ TileRealization (P.tile a))
            → (z - GaussianRealPoint (period a : GaussianInt) ∈ TileRealization (P.tile (rep
            a)))) → (
        let targetDomain (a : ι) : Set (Real × (Real × Real)) :=
          Set.Icc (0 : Real) 1 ×ˢ TileRealization (P.tile a)
        ∀ (a : ι), ContinuousOn (fun (p : ℝ × ℝ × ℝ) => homotopy a p.1 p.2) (targetDomain a)))
    ) := by
  classical
  intro ι P rep rep_spec period ball diskMap center scale_mem localHomotopy homotopy localDomain
      local_continuous translated_preimage targetDomain a
  rw [continuousOn_iff_continuous_domRestrict]
  let D := targetDomain a
  let Dlocal := localDomain (rep a)
  let toLocal : D → Dlocal := fun p =>
    ⟨(p.val.1, p.val.2 - GaussianRealPoint (period a : GaussianInt)), by
      rw [Set.mem_prod]
      exact ⟨(Set.mem_prod.mp p.property).1,
        translated_preimage a p.val.2 (Set.mem_prod.mp p.property).2⟩⟩
  have htoLocal : Continuous toLocal := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
      ((continuous_snd.comp continuous_subtype_val).sub continuous_const)
  have hlocal : Continuous
      (fun p : Dlocal => localHomotopy (rep a) p.val.1 p.val.2) :=
    continuousOn_iff_continuous_domRestrict.mp (local_continuous (rep a))
  have hpre : Continuous
      (fun p : D => localHomotopy (rep a) (toLocal p).val.1 (toLocal p).val.2) := by
    exact hlocal.comp htoLocal
  have hout : Continuous
      (fun p : D => localHomotopy (rep a) (toLocal p).val.1 (toLocal p).val.2 +
        GaussianRealPoint (period a : GaussianInt)) :=
    hpre.add continuous_const
  apply hout.congr
  intro p
  have hp := Set.mem_prod.mp p.property
  change localHomotopy (rep a) (toLocal p).val.1 (toLocal p).val.2 +
    GaussianRealPoint (period a : GaussianInt) = homotopy a p.val.1 p.val.2
  unfold homotopy
  rw [ite_eq_left hp.2]

private theorem shift_free :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ u v : P.lattice, ∀ a, P.shift u a = P.shift v
            a → u = v
    ) := by
  classical
  intro ι P u v a huv
  have hpos := congrArg P.plane.position huv
  rw [P.position_periodic u a, P.position_periodic v a] at hpos
  have hpoint : GaussianRealPoint (u : GaussianInt) =
      GaussianRealPoint (v : GaussianInt) := add_left_cancel hpos
  simp only [GaussianRealPoint, Prod.mk.injEq] at hpoint
  apply Subtype.ext
  apply Zsqrtd.ext
  · exact_mod_cast hpoint.1
  · exact_mod_cast hpoint.2

private theorem period_shift :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let rep : ι → ι := fun a => Classical.choose (P.vertex_orbit_representatives a)
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period : ι → P.lattice := fun a => Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → ((∀ (u : P.lattice), ∀ (a : ι), rep
            (P.shift u a) = rep a) → ((∀ u v : P.lattice, ∀ a, P.shift u a = P.shift v a → u = v)
            → (∀ (u : ↥P.lattice), ∀ (a : ι), period (P.shift u a) = u + period a)))
    ) := by
  classical
  intro ι P rep rep_spec period coord rep_shift shift_free u a
  apply shift_free (period (P.shift u a)) (u + period a) (rep a)
  calc
    P.shift (period (P.shift u a)) (rep a) = P.shift u a := by
      calc
        P.shift (period (P.shift u a)) (rep a) =
            P.shift (period (P.shift u a)) (rep (P.shift u a)) :=
          congrArg (P.shift (period (P.shift u a))) (rep_shift u a).symm
        _ = P.shift u a := (coord (P.shift u a)).symm
    _ = P.shift (u + period a) (rep a) := by
      calc
        P.shift u a = P.shift u (P.shift (period a) (rep a)) :=
          congrArg (P.shift u) (coord a)
        _ = P.shift (u + period a) (rep a) := (P.shift_add u (period a) (rep a)).symm

end TileContractionProof

theorem P3776T1TileContractionsExist {ι : Type} (P : PeriodicTileCore ι) :
    Nonempty (P3776T1TileContractions P) := by
-- BODY
  classical
  let rep : ι → ι := fun a => Classical.choose (P.vertex_orbit_representatives a)
  have rep_spec (a : ι) :
      rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep a) :=
    (Classical.choose_spec (P.vertex_orbit_representatives a)).1
  let period : ι → P.lattice := fun a => Classical.choose (rep_spec a).2
  have coord (a : ι) : a = P.shift (period a) (rep a) :=
    Classical.choose_spec (rep_spec a).2
  let ball : Set (Real × Real) := Metric.closedBall (0 : Real × Real) 1
  let diskMap (r : ι) : ball ≃ₜ TileRealization (P.tile r) :=
    Classical.choice (show Nonempty (ball ≃ₜ TileRealization (P.tile r)) from
      by simpa [ball, LatticeTile, TopologicalDisk] using P.tiles_are_disks r)
  let center (a : ι) : Real × Real :=
    (diskMap (rep a) ⟨0, by simp [ball, Metric.mem_closedBall]⟩).val +
      GaussianRealPoint (period a : GaussianInt)
  have scale_mem (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1)
      (x : ball) : t • x.val ∈ ball := TileContractionProof.scale_mem t ht x
  have realization_translate (a : ι) :
      TileRealization (P.tile a) =
        (fun z : Real × Real => z + GaussianRealPoint (period a : GaussianInt)) ''
          TileRealization (P.tile (rep a)) := TileContractionProof.realization_translate ι P
              rep_spec coord a
  let localHomotopy (r : ι) (t : Real) (z : Real × Real) : Real × Real :=
    if hz : z ∈ TileRealization (P.tile r) then
      if ht : t ∈ Set.Icc (0 : Real) 1 then
        let x := (diskMap r).symm ⟨z, hz⟩
        ((diskMap r) ⟨t • x.val, scale_mem t ht x⟩).val
      else (diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩ |>.val
    else (diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩ |>.val
  let homotopy (a : ι) (t : Real) (z : Real × Real) : Real × Real :=
    if hz : z ∈ TileRealization (P.tile a) then
      localHomotopy (rep a) t (z - GaussianRealPoint (period a : GaussianInt)) +
        GaussianRealPoint (period a : GaussianInt)
    else center a
  have local_zero (r : ι) (z : Real × Real) (hz : z ∈ TileRealization (P.tile r)) :
      localHomotopy r 0 z =
        ((diskMap r) ⟨0, by simp [ball, Metric.mem_closedBall]⟩).val := by
    simp [localHomotopy, hz, ball, Set.mem_Icc]
  have local_one (r : ι) (z : Real × Real) (hz : z ∈ TileRealization (P.tile r)) :
      localHomotopy r 1 z = z := by
    simp [localHomotopy, hz, ball, (diskMap r).apply_symm_apply ⟨z, hz⟩]
  have local_support (r : ι) (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1)
      (z : Real × Real) (hz : z ∈ TileRealization (P.tile r)) :
      localHomotopy r t z ∈ TileRealization (P.tile r) := by
    unfold localHomotopy
    rw [dite_eq_left hz, dite_eq_left ht]
    exact ((diskMap r) ⟨t • ((diskMap r).symm ⟨z, hz⟩).val,
      scale_mem t ht ((diskMap r).symm ⟨z, hz⟩)⟩).property
  let localDomain (r : ι) : Set (Real × (Real × Real)) :=
    Set.Icc (0 : Real) 1 ×ˢ TileRealization (P.tile r)
  have local_continuous (r : ι) :
      ContinuousOn (fun p : Real × (Real × Real) => localHomotopy r p.1 p.2)
        (localDomain r) := TileContractionProof.local_continuous ι P scale_mem r
  have translated_preimage (a : ι) (z : Real × Real)
      (hz : z ∈ TileRealization (P.tile a)) :
      z - GaussianRealPoint (period a : GaussianInt) ∈
        TileRealization (P.tile (rep a)) := by
    rw [realization_translate a] at hz
    rcases (Set.mem_image _ _ _).mp hz with ⟨y, hy, hzy⟩
    rw [← hzy]
    simpa using hy
  let targetDomain (a : ι) : Set (Real × (Real × Real)) :=
    Set.Icc (0 : Real) 1 ×ˢ TileRealization (P.tile a)
  have homotopy_continuous (a : ι) :
      ContinuousOn (fun p : Real × (Real × Real) => homotopy a p.1 p.2)
        (targetDomain a) := TileContractionProof.homotopy_continuous ι P rep_spec scale_mem
            local_continuous translated_preimage a
  have rep_unique (a s : ι)
      (hs : s ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u s) :
      s = rep a := by
    exact (Classical.choose_spec (P.vertex_orbit_representatives a)).2 s hs
  have rep_shift (u : P.lattice) (a : ι) : rep (P.shift u a) = rep a := by
    apply (rep_unique (P.shift u a) (rep a) ?_).symm
    refine ⟨rep_spec a |>.1, ?_⟩
    refine ⟨u + period a, ?_⟩
    calc
      P.shift u a = P.shift u (P.shift (period a) (rep a)) :=
        congrArg (P.shift u) (coord a)
      _ = P.shift (u + period a) (rep a) := (P.shift_add u (period a) (rep a)).symm
  have shift_free : ∀ u v : P.lattice, ∀ a, P.shift u a = P.shift v a → u = v :=
      TileContractionProof.shift_free ι P
  have period_shift (u : P.lattice) (a : ι) :
      period (P.shift u a) = u + period a := TileContractionProof.period_shift ι P rep_spec coord
          rep_shift shift_free u a
  have point_add (u v : P.lattice) :
      GaussianRealPoint ((u + v : P.lattice) : GaussianInt) =
        GaussianRealPoint (u : GaussianInt) + GaussianRealPoint (v : GaussianInt) := by
    apply Prod.ext <;> simp [GaussianRealPoint]
  refine ⟨⟨center, homotopy, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro a
    rw [realization_translate a]
    exact (Set.mem_image _ _ _).2 ⟨
      (diskMap (rep a) ⟨0, by simp [ball, Metric.mem_closedBall]⟩).val,
      (diskMap (rep a) ⟨0, by simp [ball, Metric.mem_closedBall]⟩).property, rfl⟩
  · intro a
    simpa [targetDomain] using homotopy_continuous a
  · intro a z hz
    have hy := translated_preimage a z hz
    unfold homotopy
    rw [dite_eq_left hz, local_zero (rep a) (z - GaussianRealPoint (period a : GaussianInt)) hy]
  · intro a z hz
    have hy := translated_preimage a z hz
    unfold homotopy
    rw [dite_eq_left hz, local_one (rep a) (z - GaussianRealPoint (period a : GaussianInt)) hy]
    simp
  · intro a t ht z hz
    have hy := translated_preimage a z hz
    unfold homotopy
    rw [dite_eq_left hz, realization_translate a]
    exact (Set.mem_image _ _ _).2 ⟨localHomotopy (rep a) t
      (z - GaussianRealPoint (period a : GaussianInt)),
      local_support (rep a) t ht _ hy, rfl⟩
  · intro u a
    unfold center
    rw [rep_shift u a, period_shift u a, point_add]
    apply Prod.ext <;> abel
  · intro u a t z ht hz
    have hy := translated_preimage a z hz
    have hrep := rep_shift u a
    have hperiod := period_shift u a
    have hpoint : GaussianRealPoint (period (P.shift u a) : GaussianInt) =
        GaussianRealPoint (u : GaussianInt) +
          GaussianRealPoint (period a : GaussianInt) := by
      rw [hperiod, point_add]
    have htarget : z + GaussianRealPoint (u : GaussianInt) ∈
        TileRealization (P.tile (P.shift u a)) := by
      rw [realization_translate (P.shift u a)]
      apply (Set.mem_image _ _ _).2
      refine ⟨z - GaussianRealPoint (period a : GaussianInt), ?_, ?_⟩
      · simpa [hrep] using hy
      · rw [hpoint]
        abel
    unfold homotopy
    rw [dite_eq_left htarget, dite_eq_left hz]
    rw [hrep, hperiod, point_add]
    have harg : z + GaussianRealPoint (u : GaussianInt) -
        (GaussianRealPoint (u : GaussianInt) +
          GaussianRealPoint (period a : GaussianInt)) =
        z - GaussianRealPoint (period a : GaussianInt) := by
      abel
    rw [harg]
    abel

end ApollonianSuperharmonic

end
