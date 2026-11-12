/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting
public import LeanPool.ApollonianSuperharmonic.P3723T1GridDiskBoundaryStars
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

/-!
# P3723T1AllContactDrawingExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

-- [TABLET NODE: P3723T1AllContactDrawingExists]
namespace ContactDrawingGeometry

private theorem symmetric :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact P
            a b ↔ P3723T1EdgeContact P b a ) := by
  classical
  intro ι P a b
  simp only [P3723T1EdgeContact, ne_comm, Set.inter_comm]

private theorem present :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (p : Real × Real), (D.port a b = some p) → (P3723T1EdgeContact P a b)
            ) := by
  classical
  intro ι P D a b p hp
  by_contra hn
  have he := (D.port_eq_none_iff a b).mpr hn
  rw [hp] at he
  cases he

private theorem port_exists :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), (P3723T1EdgeContact P a b) → (∃ p, D.port a b = some p) ) := by
  classical
  intro ι P D a b hab
  exact ⟨_, D.port_midpoint a b hab⟩

private theorem qinjective :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (port_exists : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) → (∃ p, D.port a b
            = some p)),
        let q (a : ι) (b : {b // P3723T1EdgeContact P a b}) : Real × Real :=
          Classical.choose (port_exists a b b.property)
        (∀ (a : ι), ∀ (b : {b // P3723T1EdgeContact P a b}), D.port a b = some (q a b)) → (∀ (a
            : ι), Function.Injective (q a)) ) := by
  classical
  intro ι P D port_exists q hq a b c heq
  apply Subtype.ext
  by_contra hne
  exact D.incident_ports_distinct a b c (q a b) (q a c) (hq a b) (hq a c) hne heq

private theorem pulled_contact :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (P3723T1ContactPorts P) → (
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (∀ (a : ι), ∀ (b : ι),
            (P3723T1EdgeContact P a b) → (P3723T1EdgeContact P (rep a) (P.shift (-period a)
            b)))) ) := by
  classical
  intro ι P D rep rep_spec period period_spec a b hab
  have ht := (D.contact_periodic (-period a) a b).mpr hab
  have hs : P.shift (-period a) a = rep a := by
    calc
      P.shift (-period a) a = P.shift (-period a) (P.shift (period a) (rep a)) :=
        congrArg (P.shift (-period a)) (period_spec a)
      _ = P.shift (-period a + period a) (rep a) := (P.shift_add _ _ _).symm
      _ = rep a := by rw [neg_add_cancel, P.shift_zero]
  rw [hs] at ht
  exact ht

private theorem gproperties :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (port_exists : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) → (∃ p, D.port a b
            = some p)),
        let q (a : ι) (b : {b // P3723T1EdgeContact P a b}) : Real × Real :=
          Classical.choose (port_exists a b b.property)
        (∀ (a : ι), ∀ (b : {b // P3723T1EdgeContact P a b}), D.port a b = some (q a b)) → (∀
            (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1
            : ℝ)) : Type) → ℝ × ℝ), (∀ (a : ι), ∀ (i : { b : ι // P3723T1EdgeContact P a b }),
                Continuous (localStar a i) ∧
            Function.Injective (localStar a i) ∧ localStar a i ⟨(0 : ℝ),
            by norm_num⟩ = D.position a ∧ localStar a i ⟨(1 : ℝ),
            by norm_num⟩ = q a i ∧ Nonempty
            (P3723T1PolygonalParameterization (localStar a i))) → ((∀ (a : ι), ∀ (i :
                { b : ι // P3723T1EdgeContact P a b }), range (localStar a i) ⊆ interior
            (TileRealization (P.tile a)) ∪ {q a i}) → (
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι),
            (P3723T1EdgeContact P a b) → (P3723T1EdgeContact P (rep a)
            (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}))))) := by
  classical
  intro ι P D port_exists q hq localStar local_properties local_support rep rep_spec period
      period_spec pulled_contact g a b hab
  let r := rep a
  let u := period a
  let c : {b // P3723T1EdgeContact P r b} :=
    ⟨P.shift (-u) b, pulled_contact a b hab⟩
  let w := GaussianRealPoint u
  have heq : g a b = fun s => localStar r c s + w := by
    funext s
    simp only [g, dite_eq_left hab]
    rfl
  obtain ⟨hc, hi, h0, h1, ⟨poly⟩⟩ := local_properties r c
  have hcenter : D.position a = D.position r + w :=
    (congrArg D.position (period_spec a)).trans (D.position_periodic u r)
  have hneighbor : P.shift u c = b := by
    change P.shift u (P.shift (-u) b) = b
    rw [← P.shift_add, add_neg_cancel, P.shift_zero]
  have hport : D.port a b = some (q r c + w) := by
    calc
      D.port a b = D.port (P.shift u r) (P.shift u c) :=
        congrArg₂ D.port (period_spec a) hneighbor.symm
      _ = (D.port r c).map (fun p => p + w) := D.port_periodic u r c
      _ = some (q r c + w) := by rw [hq r c]; rfl
  have htile : P.tile a = TileTranslation (P.tile r) u :=
    (congrArg P.tile (period_spec a)).trans (P.tile_periodic u r)
  have hrealization : TileRealization (P.tile a) =
      (fun p => p + w) '' TileRealization (P.tile r) := by
    rw [htile]
    exact (TileTranslationFormulas (P.tile r) u).2.2.2.1
  have hinterior : interior (TileRealization (P.tile a)) =
      (fun p => p + w) '' interior (TileRealization (P.tile r)) := by
    rw [hrealization]
    exact ((Homeomorph.addRight w).image_interior _).symm
  rw [heq]
  refine ⟨hc.add continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    exact hi (add_right_cancel hst)
  · change localStar r c ⟨0, by norm_num⟩ + w = D.position a
    rw [h0, ← hcenter]
  · change D.port a b = some (localStar r c ⟨1, by norm_num⟩ + w)
    rw [h1]
    exact hport
  · refine ⟨{
      count := poly.count
      positive := poly.positive
      time := poly.time
      strict := poly.strict
      start := poly.start
      finish := poly.finish
      affine_on := ?_
    }⟩
    intro i
    obtain ⟨A, B, hpiece⟩ := poly.affine_on i
    refine ⟨A + w, B, ?_⟩
    intro s hs ht
    rw [hpiece s hs ht]
    abel
  · rintro z ⟨s, rfl⟩
    rcases local_support r c (Set.mem_range_self s) with hz | hz
    · apply Or.inl
      rw [hinterior]
      exact ⟨localStar r c s, hz, rfl⟩
    · apply Or.inr
      rw [Set.mem_singleton_iff] at hz ⊢
      change localStar r c s + w = localStar r c ⟨1, by norm_num⟩ + w
      rw [hz, h1]

private theorem range_form :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 :
            ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (a : ι), ∀ (b : ι), ∀ (hab : P3723T1EdgeContact P a b), Set.range (g a b) = (fun p =>
            p + GaussianRealPoint (period a)) '' Set.range (localStar (rep a) ⟨P.shift (-period
            a) b, pulled_contact a b hab⟩) ) := by
  classical
  intro ι P D localStar rep rep_spec period pulled_contact g a b hab
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s,
      ⟨s, rfl⟩, ?_⟩
    simp only [g, dite_eq_left hab]
  · rintro ⟨p, ⟨s, rfl⟩, rfl⟩
    refine ⟨s, ?_⟩
    simp only [g, dite_eq_left hab]

private theorem gintersections :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 :
            ℝ)) : Type) → ℝ × ℝ), (∀ (a : ι), ∀ (i : { b : ι // P3723T1EdgeContact P a b }), ∀
            (j : { b : ι // P3723T1EdgeContact P a b }), i ≠ j → range (localStar a i) ∩ range
            (localStar a j) = {D.position a}) → (
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι),
            (P3723T1EdgeContact P a b) → (P3723T1EdgeContact P (rep a) (P.shift (-period a)
            b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ (a : ι), ∀ (b : ι), ∀ (hab : P3723T1EdgeContact P a b), Set.range (g a b) = (fun p
            => p + GaussianRealPoint (period a)) '' Set.range (localStar (rep a) ⟨P.shift
            (-period a) b, pulled_contact a b hab⟩)) → (∀ a, ∀ b, ∀ c, P3723T1EdgeContact P a b
            → P3723T1EdgeContact P a c → b ≠ c → Set.range (g a b) ∩ Set.range (g a c) =
            {D.position a}))) ) := by
  classical
  intro ι P D localStar local_intersections rep rep_spec period period_spec pulled_contact g
      range_form a b c hab hac hbc
  let B : {b // P3723T1EdgeContact P (rep a) b} :=
    ⟨P.shift (-period a) b, pulled_contact a b hab⟩
  let C : {b // P3723T1EdgeContact P (rep a) b} :=
    ⟨P.shift (-period a) c, pulled_contact a c hac⟩
  have hne : B ≠ C := by
    intro h
    have hh : P.shift (-period a) b = P.shift (-period a) c := congrArg Subtype.val h
    apply hbc
    simpa only [← P.shift_add, add_neg_cancel, P.shift_zero] using
      congrArg (P.shift (period a)) hh
  have hj := local_intersections (rep a) B C hne
  rw [range_form a b hab, range_form a c hac,
    ← Set.image_inter (show Function.Injective
      (fun p : Real × Real => p + GaussianRealPoint (period a)) from
        fun _ _ h => add_right_cancel h), hj, Set.image_singleton]
  rw [← D.position_periodic, ← period_spec a]

private theorem gperiodic :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 :
            ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι),
            (P3723T1EdgeContact P a b) → (P3723T1EdgeContact P (rep a) (P.shift (-period a)
            b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ u : P.lattice, ∀ a, ∀ b, P3723T1EdgeContact P a b → ∀ s, g (P.shift u a) (P.shift u
            b) s = g a b s + GaussianRealPoint u) ) := by
  classical
  intro ι P D localStar rep rep_spec period period_spec pulled_contact g u a b hab s
  have hrep : rep (P.shift u a) = rep a := by
    apply (P.vertex_orbit_representatives (P.shift u a)).unique
    · exact rep_spec (P.shift u a)
    · refine ⟨(rep_spec a).1, ?_⟩
      refine ⟨u + period a, ?_⟩
      calc
        P.shift u a = P.shift u (P.shift (period a) (rep a) : ι) :=
          congrArg (P.shift u) (period_spec a)
        _ = P.shift (u + period a) (rep a) := (P.shift_add u (period a) (rep a)).symm
  have hperiod : period (P.shift u a) = u + period a := by
    have hleft := period_spec (P.shift u a)
    rw [hrep] at hleft
    have hrepperiod : P.shift (period (P.shift u a)) (rep a) =
        P.shift (u + period a) (rep a) := by
      calc
        P.shift (period (P.shift u a)) (rep a) = P.shift u a := hleft.symm
        _ = P.shift u (P.shift (period a) (rep a)) :=
          congrArg (P.shift u) (period_spec a)
        _ = P.shift (u + period a) (rep a) :=
          (P.shift_add u (period a) (rep a)).symm
    have hfix : P.shift (period (P.shift u a) - (u + period a)) (rep a) = rep a := by
      calc
        P.shift (period (P.shift u a) - (u + period a)) (rep a) =
            P.shift (-(u + period a))
              (P.shift (period (P.shift u a)) (rep a)) := by
                rw [← P.shift_add]
                congr 1; abel
        _ = P.shift (-(u + period a)) (P.shift (u + period a) (rep a)) :=
              congrArg (P.shift (-(u + period a))) hrepperiod
        _ = rep a := by rw [← P.shift_add, neg_add_cancel, P.shift_zero]
    have hz := D.unordered_stabilizer
      (period (P.shift u a) - (u + period a)) (rep a) (rep a) (by
        simpa using congrArg (fun x : ι => ({x, x} : Set ι)) hfix)
    have : period (P.shift u a) - (u + period a) = 0 := hz
    exact (sub_eq_zero.mp this)
  have hcontact : P3723T1EdgeContact P (P.shift u a) (P.shift u b) :=
    (D.contact_periodic u a b).mpr hab
  have hneighbor : P.shift (-period (P.shift u a)) (P.shift u b) =
      P.shift (-period a) b := by
    rw [hperiod, ← P.shift_add]
    congr 1; abel
  have hgauss : GaussianRealPoint (period (P.shift u a)) =
      GaussianRealPoint (period a) + GaussianRealPoint u := by
    rw [hperiod]
    ext <;> simp [GaussianRealPoint] <;> ring
  simp only [g, dite_eq_left hcontact, dite_eq_left hab]
  let c₁ : {x // P3723T1EdgeContact P (rep (P.shift u a)) x} :=
    ⟨P.shift (-period (P.shift u a)) (P.shift u b),
      pulled_contact (P.shift u a) (P.shift u b) hcontact⟩
  let c₂ : {x // P3723T1EdgeContact P (rep a) x} :=
    ⟨P.shift (-period a) b, pulled_contact a b hab⟩
  have htypes : {x // P3723T1EdgeContact P (rep (P.shift u a)) x} =
      {x // P3723T1EdgeContact P (rep a) x} :=
    congrArg (fun r => {x // P3723T1EdgeContact P r x}) hrep
  have castSubtypeVal {p q : ι → Prop} (e : p = q) (x : {y // p y}) :
      (cast (congrArg (fun r => {y // r y}) e) x).val = x.val := by
    cases e
    rfl
  have hcast : cast htypes c₁ = c₂ := by
    apply Subtype.ext
    have hv := castSubtypeVal
      (congrArg (fun r => P3723T1EdgeContact P r) hrep) c₁
    change (cast htypes c₁).val = c₂.val
    exact hv.trans hneighbor
  have hc₁₂ : c₁ ≍ c₂ := (cast_heq htypes c₁).symm.trans (heq_of_eq hcast)
  have hpair : (⟨rep (P.shift u a), c₁⟩ :
      Σ r, {x // P3723T1EdgeContact P r x}) = ⟨rep a, c₂⟩ := by
    exact Sigma.ext hrep hc₁₂
  have hstar := congrArg
    (fun z : Σ r, {x // P3723T1EdgeContact P r x} => localStar z.1 z.2 s) hpair
  change localStar (rep (P.shift u a)) c₁ s = localStar (rep a) c₂ s at hstar
  rw [hstar, hgauss]
  abel

private theorem half_parameters :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), ∀ (p : Real × Real), (D.port a b = some p) →
            (P3723T1EdgeContact P a b)) → (∀ (localStar : (a : ι) →
            { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        ∀ a, ∀ b, ∀ p, D.port a b = some p →
          ∃ f : Icc (0 : Real) 1 → Real × Real,
            Continuous f ∧ Function.Injective f ∧ Set.range f = halfArc a b ∧
            f ⟨0, by norm_num⟩ = D.position a ∧ f ⟨1, by norm_num⟩ = p ∧
            Nonempty (P3723T1PolygonalParameterization f)))) := by
  classical
  intro ι P D present localStar rep rep_spec period pulled_contact g gproperties halfArc a b p hp
  have hab := present a b p hp
  obtain ⟨hc, hi, h0, h1, hpoly, _hsupport⟩ := gproperties a b hab
  have hend : g a b ⟨1, by norm_num⟩ = p := Option.some.inj (h1.symm.trans hp)
  exact ⟨g a b, hc, hi, by simp only [halfArc, ite_eq_left hab], h0, hend, hpoly⟩

private theorem hclip_cont :
    (by
      classical
      exact
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        Continuous clip ) := by
  classical
  intro clip
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min continuous_id)

private theorem hmeet :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (hg1ab : D.port a b = some (g a b ⟨(1 : ℝ), by norm_num⟩)), ∀ (hg1ba : D.port b a =
            some (g b a
            ⟨(1 : ℝ), by norm_num⟩)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        ∀ (s : Icc (0 : Real) 1), (s ∈ (Set.univ : Set (Icc (0 : Real) 1)) ∩ frontier A) → (left
            s = right s) ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g hg1ab hg1ba clip left right
      A s hs
  have hend : g a b ⟨1, by norm_num⟩ = g b a ⟨1, by norm_num⟩ := by
    apply Option.some.inj
    calc
      some (g a b ⟨1, by norm_num⟩) = D.port a b := hg1ab.symm
      _ = D.port b a := D.port_symmetric a b
      _ = some (g b a ⟨1, by norm_num⟩) := hg1ba
  have hhalf : (s : Real) = 1 / 2 := by
    have hcl : s ∈ closure A := hs.2.1
    have hnint : s ∉ interior A := hs.2.2
    have hAclosed : IsClosed A := isClosed_Iic.preimage continuous_subtype_val
    have hle : (s : Real) ≤ 1 / 2 := hAclosed.closure_subset hcl
    have hge : 1 / 2 ≤ (s : Real) := by
      by_contra h
      have hlt : (s : Real) < 1 / 2 := lt_of_not_ge h
      have hopen : IsOpen ((Subtype.val : Icc (0 : Real) 1 → Real) ⁻¹' Set.Iio (1 / 2 : Real)) :=
        isOpen_Iio.preimage continuous_subtype_val
      have hsub : ((Subtype.val : Icc (0 : Real) 1 → Real) ⁻¹' Set.Iio (1 / 2 : Real)) ⊆ A := by
        intro t ht
        change (t : Real) < 1 / 2 at ht
        exact le_of_lt ht
      have hmem : s ∈ interior A := mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hopen.mem_nhds hlt) hsub)
      exact hnint hmem
    linarith
  have hscale₁ : clip (2 * s) = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    simp [clip, hhalf]
  have hscale₂ : clip (2 - 2 * s) = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clip, hhalf]
  simp only [left, right, hscale₁, hscale₂]
  exact hend

private theorem hfcont :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        (Continuous left) → ((Continuous right) → ((∀ (s : Icc (0 : Real) 1), (s ∈ (Set.univ :
            Set (Icc (0 : Real) 1)) ∩ frontier A) → (left s = right s)) → (Continuous f))) ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g clip left right A f hleftc
      hrightc hmeet
  apply continuousOn_univ.mp
  apply ContinuousOn.piecewise (s := Set.univ) (t := A) hmeet
  · exact hleftc.continuousOn.mono
      (show Set.univ ∩ closure A ⊆ Set.univ from fun _ _ => Set.mem_univ _)
  · exact hrightc.continuousOn.mono
      (show Set.univ ∩ closure Aᶜ ⊆ Set.univ from fun _ _ => Set.mem_univ _)

private theorem hscale_left :
    (by
      classical
      exact
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        ∀ (s : Icc (0 : Real) 1), (s ∈ A) → ((clip (2 * s) : Real) = 2 * s) ) := by
  classical
  intro clip A s hs
  have hnonneg : 0 ≤ (2 * (s : Real)) := by nlinarith [s.property.1]
  have hle : 2 * (s : Real) ≤ 1 := by dsimp [A] at hs; nlinarith [s.property.1]
  simp [clip, max_eq_right hnonneg, min_eq_right hle]

private theorem hscale_right :
    (by
      classical
      exact
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        ∀ (s : Icc (0 : Real) 1), (s ∉ A) → ((clip (2 - 2 * s) : Real) = 2 - 2 * s) ) := by
  classical
  intro clip A s hs
  have hnonneg : 0 ≤ 2 - 2 * (s : Real) := by
    have : (1 / 2 : Real) ≤ s := by dsimp [A] at hs; linarith
    nlinarith [s.property.2]
  have hle : 2 - 2 * (s : Real) ≤ 1 := by
    have : (1 / 2 : Real) < s := by dsimp [A] at hs; linarith
    nlinarith
  simp [clip, max_eq_right hnonneg, min_eq_right hle]

private theorem hf0 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (hg0ab : g a b ⟨(0 : ℝ), by norm_num⟩ = D.position a),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        f ⟨0, by norm_num⟩ = D.position a ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g hg0ab clip left right A f
  have hz : (⟨0, by norm_num⟩ : Icc (0 : Real) 1) ∈ A := by simp [A]
  have hc : clip (0 : Real) = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [clip]
  have hEq : Set.EqOn f left A := Set.piecewise_eqOn A left right
  calc
    f ⟨0, by norm_num⟩ = left ⟨0, by norm_num⟩ := hEq hz
    _ = D.position a := by
      simp only [left, show (2 : Real) * (0 : Real) = 0 by norm_num, hc]
      simpa [g, dite_eq_left hab] using hg0ab

private theorem hf1 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (hba : P3723T1EdgeContact P b a), ∀ (hg0ba : g b a ⟨(0 : ℝ), by norm_num⟩ =
            D.position b),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        f ⟨1, by norm_num⟩ = D.position b ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g hba hg0ba clip left right A f
  have hz : (⟨1, by norm_num⟩ : Icc (0 : Real) 1) ∉ A := by norm_num [A]
  have hc : clip (0 : Real) = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [clip]
  have hEq : Set.EqOn f right Aᶜ := Set.piecewise_eqOn_compl A left right
  calc
    f ⟨1, by norm_num⟩ = right ⟨1, by norm_num⟩ := hEq hz
    _ = D.position b := by
      simp only [right, show (2 : Real) - 2 * (1 : Real) = 0 by norm_num, hc]
      simpa [g, dite_eq_left hba] using hg0ba

private theorem hendab :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (∀ (p : ℝ × ℝ), (D.port a b = some p) → (g a b ⟨1,
                by norm_num⟩ = p)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g gproperties p hp
  have h₁ := (gproperties a b hab).2.2.2.1
  exact Option.some.inj (h₁.symm.trans hp)

private theorem hendba :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → ((P3723T1EdgeContact P b a) → (∀ (p : ℝ × ℝ), (D.port b
                a = some p) → (g b a ⟨1, by norm_num⟩ = p))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g gproperties hba p hpba
  have h₁ := (gproperties b a hba).2.2.2.1
  exact Option.some.inj (h₁.symm.trans hpba)

private theorem hcross :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪ {g a b ⟨(1 : ℝ),
            by norm_num⟩}) → ((range (g b a) ⊆ interior (TileRealization (P.tile b)) ∪ {g b a ⟨(1
                : ℝ),
                by norm_num⟩}) → (∀ (p : ℝ × ℝ), (g a b ⟨1, by norm_num⟩ = p) → ((g b a
                ⟨1, by norm_num⟩
            = p) → (Set.range (g a b) ∩ Set.range (g b a) = {p})))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g hsab hsba p hendab hendba
  ext z
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    have hsupp := hsab (Set.mem_range_self s)
    have htsupp := hsba ⟨t, ht⟩
    rcases hsupp with hia | hpa
    · rcases htsupp with hib | hpb
      · exfalso
        have hne : a ≠ b := hab.1
        have hmem : g a b s ∈ TileRealization (P.tile b) := interior_subset hib
        exact Set.disjoint_left.mp (D.interior_disjoint_tiles a b hne) hia hmem
      · simp only [Set.mem_singleton_iff] at hpb
        have : g a b s = p := hpb.trans hendba
        exact this
    · simp only [Set.mem_singleton_iff] at hpa
      have : g a b s = p := hpa.trans hendab
      exact this
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    refine ⟨⟨⟨1, by norm_num⟩, hendab⟩, ?_⟩
    exact ⟨⟨1, by norm_num⟩, hendba⟩

private theorem hfinj :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (higab : Function.Injective (g a b)), ∀ (higba : Function.Injective (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        (∀ (s : Icc (0 : Real) 1), (s ∈ A) → ((clip (2 * s) : Real) = 2 * s)) → ((∀ (s : Icc (0 :
            Real) 1), (s ∉ A) → ((clip (2 - 2 * s) : Real) = 2 -
            2 * s)) → (∀ (p : ℝ × ℝ), (g a b ⟨1, by norm_num⟩ = p) → ((g b a ⟨1,
            by norm_num⟩ = p) → ((Set.range (g a b) ∩ Set.range (g b a) = {p}) →
            (Function.Injective f)))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g higab higba clip left right
      A f hscale_left hscale_right p hendab hendba hcross s t hst
  by_cases hs : s ∈ A
  · by_cases ht : t ∈ A
    · have hval : g a b (clip (2 * s)) = g a b (clip (2 * t)) := by
        simpa [f, hs, ht, left] using hst
      have harg := higab hval
      apply Subtype.ext
      have hv := congrArg (fun x : Icc (0 : Real) 1 => (x : Real)) harg
      rw [hscale_left s hs, hscale_left t ht] at hv
      nlinarith
    · have hval : g a b (clip (2 * s)) = g b a (clip (2 - 2 * t)) := by
        simpa [f, hs, ht, left, right] using hst
      have hm : g a b (clip (2 * s)) ∈ Set.range (g a b) ∩ Set.range (g b a) :=
        ⟨⟨clip (2 * s), rfl⟩, ⟨clip (2 - 2 * t), hval.symm⟩⟩
      have hm' : g a b (clip (2 * s)) = p := by simpa [hcross] using hm
      have hleftend : clip (2 * s) = ⟨1, by norm_num⟩ :=
        higab (hm'.trans hendab.symm)
      have hrightp : g b a (clip (2 - 2 * t)) = p := hval.symm.trans hm'
      have hrightend : clip (2 - 2 * t) = ⟨1, by norm_num⟩ :=
        higba (hrightp.trans hendba.symm)
      apply Subtype.ext
      have hv₁ := congrArg (fun x : Icc (0 : Real) 1 => (x : Real)) hleftend
      have hv₂ := congrArg (fun x : Icc (0 : Real) 1 => (x : Real)) hrightend
      have hsval : 2 * (s : Real) = 1 := by
        calc
          _ = (clip (2 * s) : Real) := (hscale_left s hs).symm
          _ = 1 := congrArg Subtype.val hleftend
      have htval : 2 - 2 * (t : Real) = 1 := by
        calc
          _ = (clip (2 - 2 * t) : Real) := (hscale_right t ht).symm
          _ = 1 := congrArg Subtype.val hrightend
      nlinarith
  · by_cases ht : t ∈ A
    · have hval : g b a (clip (2 - 2 * s)) = g a b (clip (2 * t)) := by
        simpa [f, hs, ht, left, right] using hst
      have hm : g b a (clip (2 - 2 * s)) ∈ Set.range (g a b) ∩ Set.range (g b a) :=
        ⟨⟨clip (2 * t), hval.symm⟩, ⟨clip (2 - 2 * s), rfl⟩⟩
      have hm' : g b a (clip (2 - 2 * s)) = p := by
        have hmem := hcross ▸ hm
        simpa using hmem
      have hrightend : clip (2 - 2 * s) = ⟨1, by norm_num⟩ :=
        higba (hm'.trans hendba.symm)
      have hleftp : g a b (clip (2 * t)) = p := hval.symm.trans hm'
      have hleftend : clip (2 * t) = ⟨1, by norm_num⟩ :=
        higab (hleftp.trans hendab.symm)
      apply Subtype.ext
      have hv₁ := congrArg (fun x : Icc (0 : Real) 1 => (x : Real)) hrightend
      have hv₂ := congrArg (fun x : Icc (0 : Real) 1 => (x : Real)) hleftend
      have hsval : 2 - 2 * (s : Real) = 1 := by
        calc
          _ = (clip (2 - 2 * s) : Real) := (hscale_right s hs).symm
          _ = 1 := congrArg Subtype.val hrightend
      have htval : 2 * (t : Real) = 1 := by
        calc
          _ = (clip (2 * t) : Real) := (hscale_left t ht).symm
          _ = 1 := congrArg Subtype.val hleftend
      nlinarith
    · have hval : g b a (clip (2 - 2 * s)) = g b a (clip (2 - 2 * t)) := by
        simpa [f, hs, ht, right] using hst
      have harg := higba hval
      apply Subtype.ext
      have hv := congrArg (fun x : Icc (0 : Real) 1 => (x : Real)) harg
      rw [hscale_right s hs, hscale_right t ht] at hv
      linarith

private theorem hrange :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        ∀ (hba : P3723T1EdgeContact P b a),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        ∀ (p : ℝ × ℝ), (g a b ⟨1, by norm_num⟩ = p) → ((g b a ⟨1, by norm_num⟩ = p) →
            (Set.range f = edgeArc a b))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g halfArc edgeArc hba clip
      left right A f p hendab hendba
  have harc : edgeArc a b = Set.range (g a b) ∪ Set.range (g b a) := by
    simp [edgeArc, halfArc, hab, hba]
  rw [harc]
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hs : s ∈ A
    · left
      refine ⟨clip (2 * s), ?_⟩
      simpa [f, left] using (Set.piecewise_eqOn A left right hs).symm
    · right
      refine ⟨clip (2 - 2 * s), ?_⟩
      simpa [f, right] using (Set.piecewise_eqOn_compl A left right hs).symm
  · intro hz
    rcases hz with hz | hz
    · obtain ⟨t, rfl⟩ := hz
      let s : Icc (0 : Real) 1 := ⟨(t : Real) / 2, div_nonneg t.property.1 (by norm_num),
          by nlinarith [t.property.2]⟩
      have hsA : s ∈ A := by dsimp [A, s]; nlinarith [t.property.2]
      have hscale : clip (2 * s) = t := by
        apply Subtype.ext
        have ht0 := t.property.1
        have ht1 := t.property.2
        change max 0 (min 1 (2 * (s : Real))) = (t : Real)
        rw [show 2 * (s : Real) = (t : Real) by dsimp [s]; ring]
        simp [max_eq_right ht0, min_eq_right ht1]
      refine ⟨s, ?_⟩
      calc
        f s = left s := Set.piecewise_eqOn A left right hsA
        _ = g a b t := by simp [left, hscale]
    · obtain ⟨t, rfl⟩ := hz
      by_cases htone : t = ⟨1, by norm_num⟩
      · subst t
        let s : Icc (0 : Real) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
        have hsA : s ∈ A := by simp [A, s]
        have hclip : clip (2 * s) = ⟨1, by norm_num⟩ := by
          apply Subtype.ext
          norm_num [clip, s]
        refine ⟨s, ?_⟩
        calc
          f s = left s := Set.piecewise_eqOn A left right hsA
          _ = g a b ⟨1, by norm_num⟩ := by simp [left, hclip]
          _ = g b a ⟨1, by norm_num⟩ := hendab.trans hendba.symm
      · have htlt : (t : Real) < 1 := by
          by_contra h
          have : (t : Real) = 1 := by linarith [t.property.2]
          exact htone (Subtype.ext this)
        let s : Icc (0 : Real) 1 := ⟨1 - (t : Real) / 2, by linarith [t.property.2], by linarith
            [t.property.1]⟩
        have hsA : s ∉ A := by dsimp [A, s]; nlinarith
        have hscale : clip (2 - 2 * s) = t := by
          apply Subtype.ext
          have ht0 := t.property.1
          have ht1 := t.property.2
          change max 0 (min 1 (2 - 2 * (s : Real))) = (t : Real)
          rw [show 2 - 2 * (s : Real) = (t : Real) by dsimp [s]; ring]
          simp [max_eq_right ht0, min_eq_right ht1]
        refine ⟨s, ?_⟩
        calc
          f s = right s := Set.piecewise_eqOn_compl A left right hsA
          _ = g b a t := by simp [right, hscale]

private theorem left_eval :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (j : Fin (m + 1)), tm ⟨j.val, by omega⟩ = polyab.time j / 2)) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm j
  have hcond : j.val ≤ m := by omega
  simp only [tm, dite_eq_left hcond]
  have hj : (⟨j.val, by omega⟩ : Fin (m + 1)) = j := Fin.ext rfl
  exact congrArg (fun k : Fin (m + 1) => polyab.time k / 2) hj

private theorem right_eval :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (j : Fin n), tm ⟨m + 1 + j.val, by omega⟩ =
            1 - polyba.time ⟨n - 1 - j.val, by omega⟩ / 2 ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm j
  have hnot : ¬ m + 1 + j.val ≤ m := by omega
  simp only [tm, dite_eq_right hnot]
  have hj : (⟨n + m - (m + 1 + j.val), by omega⟩ : Fin (n + 1)) =
      ⟨n - 1 - j.val, by omega⟩ := by
    apply Fin.ext
    dsimp [m, n]
    omega
  exact congrArg (fun k : Fin (n + 1) => 1 - polyba.time k / 2) hj

private theorem htm_strict :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        (∀ (j : Fin (m + 1)), tm ⟨j.val, by omega⟩ = polyab.time j / 2) → ((∀ (j : Fin n), tm ⟨m
            + 1 + j.val, by omega⟩ =
            1 - polyba.time ⟨n - 1 - j.val, by omega⟩ / 2) → (StrictMono tm)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm
      left_eval right_eval
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change tm ⟨i.val, by omega⟩ < tm ⟨i.val + 1, by omega⟩
  by_cases hlt : i.val < m
  · let j : Fin (m + 1) := ⟨i.val, by omega⟩
    let j' : Fin (m + 1) := ⟨i.val + 1, by omega⟩
    have hjbound : i.val < polyab.count + 1 := by
      dsimp [m]
      omega
    have hj'bound : i.val + 1 < polyab.count + 1 := by
      dsimp [m]
      omega
    have hjlt : (⟨i.val, hjbound⟩ : Fin (polyab.count + 1)) <
        ⟨i.val + 1, hj'bound⟩ := by
      apply Fin.mk_lt_mk.mpr
      exact Nat.lt_succ_self _
    have hstep := polyab.strict hjlt
    rw [left_eval j, left_eval j']
    linarith
  · by_cases heq : i.val = m
    · have hi : (⟨i.val, by omega⟩ : Fin (m + n + 1)) = ⟨m, by omega⟩ := by
        apply Fin.ext
        exact heq
      have hisucc : (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)) = ⟨m + 1, by omega⟩ := by
        apply Fin.ext
        simp [heq]
      rw [hi]
      rw [hisucc]
      let jm : Fin (m + 1) := ⟨m, by omega⟩
      rw [left_eval jm]
      have hjlast : jm = Fin.last m := by apply Fin.ext; rfl
      rw [hjlast, polyab.finish]
      have hright0 : tm ⟨m + 1, by omega⟩ =
          1 - polyba.time ⟨n - 1, by omega⟩ / 2 := by
        calc
          tm ⟨m + 1, by omega⟩ = tm ⟨m + 1 + 0, by omega⟩ := by
            congr 1
          _ = 1 - polyba.time ⟨n - 1 - 0, by omega⟩ / 2 :=
            right_eval ⟨0, hnpos⟩
          _ = 1 - polyba.time ⟨n - 1, by omega⟩ / 2 := by
            congr 1
      rw [hright0]
      have hklt :
          (⟨n - 1, by simp [n]⟩ :
            Fin (polyba.count + 1)) <
          ⟨n, by simp [n]⟩ := by
        apply Fin.mk_lt_mk.mpr
        omega
      have hstep := polyba.strict hklt
      have hknlast :
          (⟨n, by omega⟩ : Fin (polyba.count + 1)) = Fin.last polyba.count := by
        apply Fin.ext
        rfl
      rw [hknlast, polyba.finish] at hstep
      linarith
    · let j : Fin n := ⟨i.val - m - 1, by omega⟩
      have hij : i.val = m + 1 + j.val := by dsimp [j]; omega
      have hjn : j.val + 1 < n := by dsimp [j]; omega
      rw [show (⟨i.val, by omega⟩ : Fin (m + n + 1)) =
          ⟨m + 1 + j.val, by omega⟩ by apply Fin.ext; simp [hij],
        right_eval j,
        show (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)) =
          ⟨m + 1 + (j.val + 1), by omega⟩ by apply Fin.ext; simp [hij]; omega,
        right_eval ⟨j.val + 1, hjn⟩]
      have hklt :
          (⟨n - 2 - j.val, by simpa [n] using (show n - 2 - j.val < n + 1 by omega)⟩ :
            Fin (polyba.count + 1)) <
          ⟨n - 1 - j.val, by simpa [n] using (show n - 1 - j.val < n + 1 by omega)⟩ := by
        apply Fin.mk_lt_mk.mpr
        omega
      have hstep := polyba.strict hklt
      have hidx : n - 2 - j.val = n - 1 - (j.val + 1) := by omega
      have hidxFin : (⟨n - 2 - j.val, by omega⟩ : Fin (n + 1)) =
          ⟨n - 1 - (j.val + 1), by omega⟩ := by
        apply Fin.ext
        exact hidx
      rw [hidxFin] at hstep
      linarith

private theorem htm_start :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        (0 < m) → (∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        (∀ (j : Fin (m + 1)), tm ⟨j.val, by omega⟩ = polyab.time j / 2) → (tm 0 = 0)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hmpos
      hnpos tm left_eval
  change tm ⟨0, by omega⟩ = 0
  rw [left_eval ⟨0, by omega⟩]
  simp [polyab.start]

private theorem htm_mid :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        (∀ (j : Fin (m + 1)), tm ⟨j.val, by omega⟩ = polyab.time j / 2) → (tm ⟨m,
            by omega⟩ = 1 / 2))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm
      left_eval
  let jm : Fin (m + 1) := ⟨m, by omega⟩
  rw [left_eval jm]
  have hjlast : jm = Fin.last m := by apply Fin.ext; rfl
  rw [hjlast, polyab.finish]

private theorem htm_finish :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        (∀ (j : Fin n), tm ⟨m + 1 + j.val, by omega⟩ =
            1 - polyba.time ⟨n - 1 - j.val, by omega⟩ / 2) → (tm (Fin.last (m + n)) = 1) ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm
      right_eval
  have hnlast : n - 1 < n := by omega
  have hindex : (Fin.last (m + n) : Fin (m + n + 1)) =
      ⟨m + 1 + (n - 1), by omega⟩ := by
    apply Fin.ext
    simp
    dsimp [m, n]
    omega
  rw [hindex, right_eval ⟨n - 1, by omega⟩]
  have hidx : n - 1 - (n - 1) = 0 := by omega
  have hzero : (⟨n - 1 - (n - 1), by omega⟩ : Fin (n + 1)) = 0 := by
    apply Fin.ext
    exact hidx
  rw [hzero, polyba.start]
  ring

private theorem hcastAt761 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), i.castSucc = (⟨i.val, by omega⟩ : Fin (m + n + 1)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i
  apply Fin.ext
  rfl

private theorem hsuccAt764 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), i.succ = (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i
  apply Fin.ext
  rfl

private theorem hlo'At767 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), (tm i.castSucc ≤
            (↑s : ℝ)) → ((i.castSucc = (⟨i.val, by omega⟩ : Fin (m + n + 1))) → (tm ⟨i.val,
            by omega⟩ ≤ (s : Real))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i s hlo
      hcast
  rw [← hcast]
  exact hlo

private theorem hhi'At770 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ((↑s : ℝ) ≤ tm
            i.succ) → ((i.succ = (⟨i.val + 1, by omega⟩ : Fin (m + n + 1))) → ((s : Real) ≤
            tm ⟨i.val + 1, by omega⟩)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i s hhi
      hsucc
  rw [← hsucc]
  exact hhi

private theorem hlastbound :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), ∀ (hleftidx : (↑i : ℕ) < m),
        let j : Fin m := ⟨i.val, by omega⟩
        let j' : Fin (m + 1) := j.succ
        polyab.time j' ≤ 1)) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i hleftidx
      j j'
  calc
    polyab.time j' ≤ polyab.time (Fin.last m) :=
      polyab.strict.monotone (Fin.le_last j')
    _ = 1 := polyab.finish

private theorem hsAAt786 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let m := polyab.count
        let n := polyba.count
        (0 < n) → (
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (hleftidx : (↑i : ℕ) < m),
        let j : Fin m := ⟨i.val, by omega⟩
        let j' : Fin (m + 1) := j.succ
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ((s : Real) ≤ tm ⟨i.val + 1,
            by omega⟩) → ((tm ⟨i.val + 1, by omega⟩ = polyab.time j' / 2) → ((polyab.time j' ≤ 1) →
            (s ∈ A)))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba A m n hnpos tm
      i hleftidx j j' s hhi' hend hlastbound
  change (s : Real) ≤ 1 / 2
  rw [hend] at hhi'
  nlinarith [hlastbound]

private theorem htlowerAt794 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (hleftidx : (↑i : ℕ) < m),
        let j : Fin m := ⟨i.val, by omega⟩
        let j' : Fin (m + 1) := j.succ
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hlo' : tm ⟨i.val, by omega⟩ ≤ (s : Real)), ∀
            (hhi' : (s : Real) ≤ tm ⟨i.val + 1, by omega⟩), ∀ (hstart : tm ⟨i.val, by omega⟩ =
            polyab.time j.castSucc / 2), ∀ (hend : tm ⟨i.val + 1, by omega⟩ = polyab.time j' /
            2), ∀ (hlastbound : polyab.time j' ≤ 1),
        let t : Icc (0 : Real) 1 := ⟨2 * (s : Real), by
          constructor
          · nlinarith [s.property.1]
          · nlinarith⟩
        polyab.time j.castSucc ≤ (t : Real) ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm i
      hleftidx j j' s hlo' hhi' hstart hend hlastbound t
  have h := hlo'
  rw [hstart] at h
  dsimp [t]
  linarith

private theorem htupperAt799 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (hleftidx : (↑i : ℕ) < m),
        let j : Fin m := ⟨i.val, by omega⟩
        let j' : Fin (m + 1) := j.succ
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hhi' : (s : Real) ≤ tm ⟨i.val + 1,
            by omega⟩), ∀ (hend : tm ⟨i.val + 1, by omega⟩ = polyab.time j' / 2), ∀ (hlastbound :
            polyab.time j' ≤ 1),
        let t : Icc (0 : Real) 1 := ⟨2 * (s : Real), by
          constructor
          · nlinarith [s.property.1]
          · nlinarith⟩
        (t : Real) ≤ polyab.time j' ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm i
      hleftidx j j' s hhi' hend hlastbound t
  have h := hhi'
  rw [hend] at h
  dsimp [t]
  linarith

private theorem htvalAt804 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        ∀ (hscale_left : ∀ (s : Icc (0 : Real) 1), (s ∈ A) → ((clip (2 * s) : Real) = 2 * s)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (hleftidx : (↑i : ℕ) < m),
        let j : Fin m := ⟨i.val, by omega⟩
        let j' : Fin (m + 1) := j.succ
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hhi' : (s : Real) ≤ tm ⟨i.val + 1,
            by omega⟩), ∀ (hend : tm ⟨i.val + 1, by omega⟩ = polyab.time j' / 2), ∀ (hlastbound :
                polyab.time j' ≤ 1), (s ∈ A) → (
        let t : Icc (0 : Real) 1 := ⟨2 * (s : Real), by
          constructor
          · nlinarith [s.property.1]
          · nlinarith⟩
        clip (2 * s) = t)) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba clip A
      hscale_left m n hnpos tm i hleftidx j j' s hhi' hend hlastbound hsA t
  apply Subtype.ext
  exact hscale_left s hsA

private theorem hfvalueAt807 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (hleftidx : (↑i : ℕ) < m),
        let j : Fin m := ⟨i.val, by omega⟩
        let j' : Fin (m + 1) := j.succ
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hhi' : (s : Real) ≤ tm ⟨i.val + 1,
            by omega⟩), ∀ (hend : tm ⟨i.val + 1, by omega⟩ = polyab.time j' / 2), ∀ (hlastbound :
                polyab.time j' ≤ 1), (s ∈ A) → (
        let t : Icc (0 : Real) 1 := ⟨2 * (s : Real), by
          constructor
          · nlinarith [s.property.1]
          · nlinarith⟩
        (clip (2 * s) = t) → (f s = g a b t))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba clip left
      right A f m n hnpos tm i hleftidx j j' s hhi' hend hlastbound hsA t htval
  calc
    f s = left s := Set.piecewise_eqOn A left right hsA
    _ = g a b t := by simp [left, htval]

private theorem hcastAt824 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), i.castSucc = (⟨i.val, by omega⟩ : Fin (m + n + 1)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i
  apply Fin.ext
  rfl

private theorem hsuccAt827 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), i.succ = (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i
  apply Fin.ext
  rfl

private theorem hlo'At830 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), (tm i.castSucc ≤
            (↑s : ℝ)) → ((i.castSucc = (⟨i.val, by omega⟩ : Fin (m + n + 1))) → (tm ⟨i.val,
            by omega⟩ ≤ (s : Real))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i s hlo
      hcast
  rw [← hcast]
  exact hlo

private theorem hhi'At833 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)), ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ((↑s : ℝ) ≤ tm
            i.succ) → ((i.succ = (⟨i.val + 1, by omega⟩ : Fin (m + n + 1))) → ((s : Real) ≤
            tm ⟨i.val + 1, by omega⟩)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i s hhi
      hsucc
  rw [← hsucc]
  exact hhi

private theorem hcurIndex :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        (⟨n - r, by omega⟩ : Fin (n + 1)) = k.succ ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i r hr k
  apply Fin.ext
  dsimp [k]
  omega

private theorem hnextIndex :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        (⟨n - r - 1, by omega⟩ : Fin (n + 1)) = k.castSucc ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i r hr k
  apply Fin.ext
  dsimp [k]

private theorem hendIndexAt843 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), (¬(↑i : ℕ) < m) → (
        let r : Nat := i.val - m
        ∀ (hr : r < n), (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)) =
          ⟨m + 1 + r, by omega⟩))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i hleftidx
      r hr
  apply Fin.ext
  dsimp [r]
  omega

private theorem hstartAt848 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (right_eval : ∀ (j : Fin n), tm ⟨m + 1 + j.val, by omega⟩ =
            1 - polyba.time ⟨n - 1 - j.val, by omega⟩ / 2), ∀ (htm_mid : tm ⟨m, by omega⟩ = 1 /
                2), ∀ (i : Fin (m + n)), ∀ (hleftidx : ¬(↑i : ℕ) < m),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        tm ⟨i.val, by omega⟩ =
          1 - polyba.time k.succ / 2 ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n hnpos tm
      right_eval htm_mid i hleftidx r hr k
  by_cases hrzero : r = 0
  · have hiv : i.val = m := by dsimp [r] at hrzero ⊢; omega
    have hindex : (⟨i.val, by omega⟩ : Fin (m + n + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      exact hiv
    have hksucc : k.succ = Fin.last n := by
      apply Fin.ext
      dsimp [k]
      omega
    calc
      tm ⟨i.val, by omega⟩ = tm ⟨m, by omega⟩ := congrArg tm hindex
      _ = 1 / 2 := htm_mid
      _ = 1 - polyba.time k.succ / 2 := by rw [hksucc, polyba.finish]; norm_num
  · let j : Fin n := ⟨r - 1, by omega⟩
    have hstartIndex : (⟨i.val, by omega⟩ : Fin (m + n + 1)) =
        ⟨m + 1 + j.val, by omega⟩ := by
      apply Fin.ext
      dsimp [j, r]
      omega
    calc
      tm ⟨i.val, by omega⟩ = tm ⟨m + 1 + j.val, by omega⟩ :=
        congrArg tm hstartIndex
      _ = 1 - polyba.time ⟨n - 1 - j.val, by omega⟩ / 2 := right_eval j
      _ = 1 - polyba.time k.succ / 2 := by
        have hidx : (⟨n - 1 - j.val, by omega⟩ : Fin (n + 1)) = k.succ := by
          apply Fin.ext
          dsimp [k, j, r]
          omega
        exact congrArg (fun z : Real => 1 - z / 2)
          (congrArg polyba.time hidx)

private theorem hendAt880 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (right_eval : ∀ (j : Fin n), tm ⟨m + 1 + j.val, by omega⟩ =
            1 - polyba.time ⟨n - 1 - j.val, by omega⟩ / 2), ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        ((⟨i.val + 1, by omega⟩ : Fin (m + n + 1)) =
          ⟨m + 1 + r, by omega⟩) → (tm ⟨i.val + 1, by omega⟩ =
          1 - polyba.time k.castSucc / 2)) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm
      right_eval i r hr k hendIndex
  calc
    tm ⟨i.val + 1, by omega⟩ = tm ⟨m + 1 + r, by omega⟩ :=
      congrArg tm hendIndex
    _ = 1 - polyba.time ⟨n - 1 - r, by omega⟩ / 2 :=
      right_eval ⟨r, hr⟩
    _ = 1 - polyba.time k.castSucc / 2 := by
      have hidx : (⟨n - 1 - r, by omega⟩ : Fin (n + 1)) = k.castSucc := by
        apply Fin.ext
        dsimp [k]
        omega
      exact congrArg (fun z : Real => 1 - z / 2)
        (congrArg polyba.time hidx)

private theorem hA_imp_mid :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let m := polyab.count
        let n := polyba.count
        ∀ (hnpos : 0 < n),
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        (StrictMono tm) → ((tm ⟨m, by omega⟩ = 1 / 2) → (∀ (i : Fin (m +
            n)), (¬(↑i : ℕ) < m) → (
        let r : Nat := i.val - m
        (r < n) → (∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), (tm ⟨i.val, by omega⟩ ≤ (s :
            Real)) → (s ∈ A → i.val = m ∧ (s : Real) = 1 / 2))))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba A m n hnpos tm
      htm_strict htm_mid i hleftidx r hr s hlo' hsA
  by_cases heq : i.val = m
  · have hi : (⟨i.val, by omega⟩ : Fin (m + n + 1)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      exact heq
    have hhalf : (s : Real) = 1 / 2 := by
      have hlow := hlo'
      rw [hi, htm_mid] at hlow
      change (s : Real) ≤ 1 / 2 at hsA
      exact le_antisymm hsA hlow
    exact ⟨heq, hhalf⟩
  · have hi : (⟨m, by omega⟩ : Fin (m + n + 1)) < ⟨i.val, by omega⟩ := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hmid : 1 / 2 < tm ⟨i.val, by omega⟩ := by
      calc
        1 / 2 = tm ⟨m, by omega⟩ := htm_mid.symm
        _ < tm ⟨i.val, by omega⟩ := htm_strict hi
    have hlow := hlo'
    change (s : Real) ≤ 1 / 2 at hsA
    linarith

private theorem hsRight :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        ∀ (p : ℝ × ℝ), (g a b ⟨1, by norm_num⟩ = p) → ((g b a ⟨1, by norm_num⟩ = p) → (
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)), ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), (s ∈ A → i.val = m ∧ (s :
            Real) = 1 / 2) → (f s = right s))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba clip left
      right A f p hendab hendba m n i s hA_imp_mid
  by_cases hsA : s ∈ A
  · obtain ⟨_, hhalf⟩ := hA_imp_mid hsA
    have hc1 : clip (2 * s) = ⟨1, by norm_num⟩ := by
      apply Subtype.ext
      change max 0 (min 1 (2 * (s : Real))) = 1
      rw [hhalf]
      norm_num
    have hc2 : clip (2 - 2 * s) = ⟨1, by norm_num⟩ := by
      apply Subtype.ext
      change max 0 (min 1 (2 - 2 * (s : Real))) = 1
      rw [hhalf]
      norm_num
    have hval : left s = right s := by
      simp only [left, right, hc1, hc2]
      exact hendab.trans hendba.symm
    calc
      f s = left s := Set.piecewise_eqOn A left right hsA
      _ = right s := hval
  · exact Set.piecewise_eqOn_compl A left right hsA

private theorem hkbound :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        polyba.time k.succ ≤ 1 ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n i r hr k
  calc
    polyba.time k.succ ≤ polyba.time (Fin.last n) :=
      polyba.strict.monotone (Fin.le_last k.succ)
    _ = 1 := polyba.finish

private theorem hsHalf :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), (tm ⟨i.val, by omega⟩ ≤ (s : Real)) → ((tm
            ⟨i.val, by omega⟩ =
          1 - polyba.time k.succ / 2) → ((polyba.time k.succ ≤ 1) → ((1 / 2 : Real) ≤ s)))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i r hr
      k s hlo' hstart hkbound
  have hlow := hlo'
  rw [hstart] at hlow
  nlinarith

private theorem htlowerAt951 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hlo' : tm ⟨i.val, by omega⟩ ≤ (s : Real)), ∀
            (hhi' : (s : Real) ≤ tm ⟨i.val + 1, by omega⟩), ∀ (hstart : tm ⟨i.val, by omega⟩ =
          1 - polyba.time k.succ / 2), ∀ (hend : tm ⟨i.val + 1, by omega⟩ =
          1 - polyba.time k.castSucc / 2), ∀ (hkbound : polyba.time k.succ ≤ 1), ∀ (hsHalf : (1 /
              2 : Real) ≤ s),
        let t : Icc (0 : Real) 1 := ⟨2 - 2 * (s : Real), by
          constructor
          · have hlow := hlo'
            rw [hstart] at hlow
            nlinarith [s.property.2]
          · nlinarith [s.property.1, hsHalf]⟩
        polyba.time k.castSucc ≤ (t : Real) ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i r hr
      k s hlo' hhi' hstart hend hkbound hsHalf t
  have h := hhi'
  rw [hend] at h
  dsimp [t]
  linarith

private theorem htupperAt956 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hlo' : tm ⟨i.val, by omega⟩ ≤ (s : Real)), ∀
            (hstart : tm ⟨i.val, by omega⟩ =
          1 - polyba.time k.succ / 2), ∀ (hkbound : polyba.time k.succ ≤ 1), ∀ (hsHalf : (1 / 2 :
              Real) ≤ s),
        let t : Icc (0 : Real) 1 := ⟨2 - 2 * (s : Real), by
          constructor
          · have hlow := hlo'
            rw [hstart] at hlow
            nlinarith [s.property.2]
          · nlinarith [s.property.1, hsHalf]⟩
        (t : Real) ≤ polyba.time k.succ ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba m n tm i r hr
      k s hlo' hstart hkbound hsHalf t
  have h := hlo'
  rw [hstart] at h
  dsimp [t]
  linarith

private theorem htvalAt961 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        ∀ (hscale_right : ∀ (s : Icc (0 : Real) 1), (s ∉ A) → ((clip (2 - 2 * s) : Real) = 2 - 2
            * s)),
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hlo' : tm ⟨i.val, by omega⟩ ≤ (s : Real)), ∀
            (hstart : tm ⟨i.val, by omega⟩ =
          1 - polyba.time k.succ / 2), ∀ (hA_imp_mid : s ∈ A → i.val = m ∧ (s : Real) = 1 / 2), ∀
              (hkbound : polyba.time k.succ ≤ 1), ∀ (hsHalf : (1 / 2 : Real) ≤ s),
        let t : Icc (0 : Real) 1 := ⟨2 - 2 * (s : Real), by
          constructor
          · have hlow := hlo'
            rw [hstart] at hlow
            nlinarith [s.property.2]
          · nlinarith [s.property.1, hsHalf]⟩
        clip (2 - 2 * s) = t ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba clip A
      hscale_right m n tm i r hr k s hlo' hstart hA_imp_mid hkbound hsHalf t
  apply Subtype.ext
  change (clip (2 - 2 * (s : Real)) : Real) = 2 - 2 * (s : Real)
  by_cases hsA : s ∈ A
  · obtain ⟨_, hhalf⟩ := hA_imp_mid hsA
    change max 0 (min 1 (2 - 2 * (s : Real))) = 2 - 2 * (s : Real)
    rw [hhalf]
    norm_num
  · exact hscale_right s hsA

private theorem hfvalueAt970 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
            P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        let m := polyab.count
        let n := polyba.count
        let tm : Fin (m + n + 1) → Real := fun i =>
          if hi : i.val ≤ m then
            polyab.time ⟨i.val, by omega⟩ / 2
          else
            1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
        ∀ (i : Fin (m + n)),
        let r : Nat := i.val - m
        ∀ (hr : r < n),
        let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
        ∀ (s : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (hlo' : tm ⟨i.val, by omega⟩ ≤ (s : Real)), ∀
            (hstart : tm ⟨i.val, by omega⟩ =
          1 - polyba.time k.succ / 2), ∀ (hsRight : f s = right s), ∀ (hkbound : polyba.time
              k.succ ≤ 1), ∀ (hsHalf : (1 / 2 : Real) ≤ s),
        let t : Icc (0 : Real) 1 := ⟨2 - 2 * (s : Real), by
          constructor
          · have hlow := hlo'
            rw [hstart] at hlow
            nlinarith [s.property.2]
          · nlinarith [s.property.1, hsHalf]⟩
        (clip (2 - 2 * s) = t) → (f s = g b a t) ) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba clip left
      right A f m n tm i r hr k s hlo' hstart hsRight hkbound hsHalf t htval
  calc
    f s = right s := hsRight
    _ = g b a t := by simp [right, htval]

private theorem parameter_homeomorph :
    (by
      classical
      exact
        ∀ (A : Set (Real × Real)), ∀ (f : Icc (0 : Real) 1 → Real × Real), (Continuous f) →
            ((Function.Injective f) → ((Set.range f = A) → (∃ h : Icc (0 : Real) 1 ≃ₜ A, ∀ s, (h
            s : Real × Real) = f s))) ) := by
  classical
  intro A f hc hi hr
  let F : Icc (0 : Real) 1 → A := fun s =>
    ⟨f s, hr ▸ Set.mem_range_self s⟩
  have hFc : Continuous F := hc.subtype_mk _
  have hFi : Function.Injective F := fun s t hst =>
    hi (congrArg Subtype.val hst)
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨s, hs⟩ := (Set.ext_iff.mp hr y).mpr y.property
    exact ⟨s, Subtype.ext hs⟩
  let h := (isHomeomorph_iff_continuous_bijective.mpr ⟨hFc, hFi, hFs⟩).homeomorph
  exact ⟨h, fun _ => rfl⟩

private theorem half_periodic :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 :
            ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ u : P.lattice, ∀ a, ∀ b, P3723T1EdgeContact P a b → ∀ s, g (P.shift u a) (P.shift u
            b) s = g a b s + GaussianRealPoint u) → (
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        ∀ u : P.lattice, ∀ a, ∀ b, halfArc (P.shift u a) (P.shift u b) = (fun p => p +
            GaussianRealPoint u) '' halfArc a b) ) := by
  classical
  intro ι P D localStar rep rep_spec period pulled_contact g gperiodic halfArc u a b
  by_cases hab : P3723T1EdgeContact P a b
  · simp only [halfArc, ite_eq_left hab, ite_eq_left ((D.contact_periodic u a b).mpr hab)]
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨g a b s, ⟨s, rfl⟩, (gperiodic u a b hab s).symm⟩
    · rintro ⟨q, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, gperiodic u a b hab s⟩
  · have hn : ¬ P3723T1EdgeContact P (P.shift u a) (P.shift u b) :=
      fun h => hab ((D.contact_periodic u a b).mp h)
    simp only [halfArc, ite_eq_right hab, ite_eq_right hn, Set.image_empty]

private theorem tile_closed :
    (by
      classical
      exact
        ∀ (T : ProtoTile), IsClosed (TileRealization T) ) := by
  classical
  intro T
  classical
  unfold TileRealization
  apply isClosed_biUnion_finset
  intro x hx
  exact isClosed_Icc

private theorem compact_cells_finite :
    (by
      classical
      exact
        ∀ (K : Set (Real × Real)), (IsCompact K) → (Set.Finite {x : GaussianInt | ∃ p ∈ K, p ∈
            ClosedSquareRealization x}) ) := by
  classical
  intro K hK
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hK.isBounded
    have hCpos : 0 ≤ C := by
      have := hC hp₀ hp₀
      simpa using this
    let B := max (abs p₀.1) (abs p₀.2) + C + 2
    obtain ⟨N, hN⟩ := exists_nat_gt (B + 1)
    let box : Set (Int × Int) :=
      Set.Icc (-(N : Int)) (N : Int) ×ˢ Set.Icc (-(N : Int)) (N : Int)
    let cells : Set GaussianInt :=
      (fun z : Int × Int => Zsqrtd.mk z.1 z.2) '' box
    have hboxfinite : box.Finite := by
      dsimp [box]
      exact (Set.finite_Icc (-(N : Int)) (N : Int)).prod
        (Set.finite_Icc (-(N : Int)) (N : Int))
    have hcfinite : cells.Finite := hboxfinite.image _
    apply hcfinite.subset
    intro x hx
    obtain ⟨p, hpK, hpsq⟩ := hx
    have hdist := hC hpK hp₀
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hdist
    have hd1 := abs_le.mp hdist.1
    have hd2 := abs_le.mp hdist.2
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpsq
    change x ∈ (fun z : Int × Int => Zsqrtd.mk z.1 z.2) '' box
    simp only [Set.mem_image]
    refine ⟨(x.re, x.im), ?_, ?_⟩
    · change (x.re, x.im) ∈
        (Set.Icc (-(N : Int)) (N : Int) ×ˢ Set.Icc (-(N : Int)) (N : Int))
      rw [Set.mem_prod]
      simp only [Set.mem_Icc]
      constructor
      · constructor
        · have hpbound : -B ≤ p.1 := by
            dsimp [B]
            have hp0 : -abs p₀.1 ≤ p₀.1 := neg_abs_le _
            have hm : abs p₀.1 ≤ max (abs p₀.1) (abs p₀.2) := le_max_left _ _
            linarith [hd1.1, hm]
          have hxlow : ((x.re : Int) : Real) ≥ p.1 - 1 := by linarith [hpsq.2.1]
          have : -(N : Real) < ((x.re : Int) : Real) := by linarith [hN]
          exact_mod_cast (le_of_lt this)
        · have hpbound : p.1 ≤ B := by
            dsimp [B]
            have hp0 : p₀.1 ≤ abs p₀.1 := le_abs_self _
            have hm : abs p₀.1 ≤ max (abs p₀.1) (abs p₀.2) := le_max_left _ _
            linarith [hd1.2, hm]
          have hxhigh : ((x.re : Int) : Real) ≤ p.1 := hpsq.1.1
          have : ((x.re : Int) : Real) < (N : Real) := by linarith [hN]
          exact_mod_cast (le_of_lt this)
      · constructor
        · have hpbound : -B ≤ p.2 := by
            dsimp [B]
            have hp0 : -abs p₀.2 ≤ p₀.2 := neg_abs_le _
            have hm : abs p₀.2 ≤ max (abs p₀.1) (abs p₀.2) := le_max_right _ _
            linarith [hd2.1, hm]
          have hxlow : ((x.im : Int) : Real) ≥ p.2 - 1 := by linarith [hpsq.2.2]
          have : -(N : Real) < ((x.im : Int) : Real) := by linarith [hN]
          exact_mod_cast (le_of_lt this)
        · have hpbound : p.2 ≤ B := by
            dsimp [B]
            have hp0 : p₀.2 ≤ abs p₀.2 := le_abs_self _
            have hm : abs p₀.2 ≤ max (abs p₀.1) (abs p₀.2) := le_max_right _ _
            linarith [hd2.2, hm]
          have hxhigh : ((x.im : Int) : Real) ≤ p.2 := hpsq.1.2
          have : ((x.im : Int) : Real) < (N : Real) := by linarith [hN]
          exact_mod_cast (le_of_lt this)
    · apply Zsqrtd.ext <;> rfl
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hKempty]

private theorem half_range_in_tile :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀
            (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 :
            ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → ((∀ (T : ProtoTile), IsClosed (TileRealization T)) → (∀
                (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x y) → (Set.range (g x y) ⊆
                TileRealization (P.tile x)))) ) := by
  classical
  intro ι P D localStar rep rep_spec period pulled_contact g gproperties tile_closed x y hxy
  obtain ⟨_, _, _, hport, _, hs⟩ := gproperties x y hxy
  intro z hz
  rcases hs hz with hinside | hport'
  · exact interior_subset hinside
  · rw [Set.mem_singleton_iff] at hport'
    have hfront := (D.port_frontier x y (g x y ⟨1, by norm_num⟩) hport).1
    have htile := (tile_closed (P.tile x)).closure_eq ▸ frontier_subset_closure hfront
    rw [hport']
    exact htile

private theorem frontier_no_interior :
    (by
      classical
      exact
        (∀ (T : ProtoTile), IsClosed (TileRealization T)) → (∀ (T : ProtoTile), ∀ (p : Real ×
            Real), (p ∈ frontier (TileRealization T)) → (p ∉ interior (TileRealization T))) ) := by
  classical
  intro tile_closed T p hp
  have hpT : p ∈ TileRealization T :=
    (tile_closed T).closure_eq ▸ frontier_subset_closure hp
  exact (mem_frontier_iff_notMem_interior hpT).mp hp

private theorem half_disjoint :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), (P3723T1EdgeContact P a b) → (∃ p, D.port a b
            = some p)) → (∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → ((∀ (T : ProtoTile), ∀ (p : Real × Real), (p ∈ frontier
                (TileRealization T)) → (p ∉ interior (TileRealization T))) → (∀ (x : ι), ∀ (y :
                    ι), ∀ (u : ι), ∀ (v : ι), (P3723T1EdgeContact P x y) →
                    ((P3723T1EdgeContact P
                u v) → ((({x, y} : Set ι) ≠ {u, v}) → ((x ≠ u) → (Disjoint (Set.range (g x y))
                (Set.range (g u v)))))))))) := by
  classical
  intro ι P D port_exists localStar rep rep_spec period pulled_contact g gproperties
      frontier_no_interior x y u v hxy huv hpair hxu
  obtain ⟨p, hp⟩ := port_exists x y hxy
  obtain ⟨q, hq⟩ := port_exists u v huv
  obtain ⟨_, _, _, hpG, _, hsG⟩ := gproperties x y hxy
  obtain ⟨_, _, _, hqG, _, htG⟩ := gproperties u v huv
  have hp1 : g x y ⟨1, by norm_num⟩ = p := Option.some.inj (hpG.symm.trans hp)
  have hq1 : g u v ⟨1, by norm_num⟩ = q := Option.some.inj (hqG.symm.trans hq)
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rcases hsG hz1 with hzi | hzp
  · rcases htG hz2 with hzu | hzq
    · exact Set.disjoint_left.mp (D.interior_disjoint_tiles x u hxu) hzi (interior_subset hzu)
    · have hzq' : z = q := hzq.trans hq1
      have hqint : q ∈ interior (TileRealization (P.tile x)) := by
        rw [← hzq']
        exact hzi
      by_cases hxv : x = v
      · have hfront := (D.port_frontier u v q hq).2
        exact frontier_no_interior (P.tile v) q hfront (by simpa [hxv] using hqint)
      · have hnot := D.port_no_third u v q hq
        exact hnot x hxu hxv (interior_subset hqint)
  · have hzp' : z = p := hzp.trans hp1
    rcases htG hz2 with hzu | hzq
    · have hfront := D.port_frontier x y p hp
      have hpint : p ∈ interior (TileRealization (P.tile u)) := by
        rw [← hzp']
        exact hzu
      by_cases hux : u = x
      · exact frontier_no_interior (P.tile x) p hfront.1 (by simpa [hux] using hpint)
      · by_cases huy : u = y
        · exact frontier_no_interior (P.tile y) p hfront.2 (by simpa [huy] using hpint)
        · have hnot := D.port_no_third x y p hp u hux huy
          exact hnot (interior_subset hpint)
    · have hzq' : z = q := hzq.trans hq1
      have hpq : p = q := hzp'.symm.trans hzq'
      have hq' : D.port u v = some p := by rw [hq, hpq]
      have howner := D.port_owner_pair x y u v p hp hq'
      exact hpair howner

private theorem half_subset :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, ∀ c, P3723T1EdgeContact P a b → P3723T1EdgeContact P a c → b ≠ c →
            Set.range (g a b) ∩ Set.range (g a c) = {D.position a}) → ((∀ (x : ι), ∀ (y : ι), ∀
                (u : ι), ∀ (v : ι), (P3723T1EdgeContact P x y) → ((P3723T1EdgeContact P u v) →
            ((({x, y} : Set ι) ≠ {u, v}) → ((x ≠ u) → (Disjoint (Set.range (g x y)) (Set.range (g
            u v))))))) → (∀ (x : ι), ∀ (y : ι), ∀ (u : ι), ∀ (v : ι), (P3723T1EdgeContact P x
            y) → ((P3723T1EdgeContact P u v) → ((({x, y} : Set ι) ≠ {u, v}) → (Set.range (g x
            y) ∩ Set.range (g u v) ⊆ D.position '' (({x, y} : Set ι) ∩ {u, v})))))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g gintersections half_disjoint
      x y u v hxy huv hxyuv z hz
  by_cases hxu : x = u
  · subst u
    have hyv : y ≠ v := by
      intro h
      apply hxyuv
      simp [h]
    have huv' : P3723T1EdgeContact P x v := by simpa using huv
    have hstar := gintersections x y v hxy huv' hyv
    have hzpos : z = D.position x := by
      rw [hstar] at hz
      exact Set.mem_singleton_iff.mp hz
    refine ⟨x, ?_, hzpos.symm⟩
    exact ⟨by simp, by simp⟩
  · exfalso
    exact (Set.disjoint_left.mp (half_disjoint x y u v hxy huv hxyuv hxu) hz.1 hz.2)

private theorem hstartAt1216 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact
            P b a) → (∀ (a : ι), ∀ (b : ι), ∀ (localStar : (a : ι) →
            { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        ∀ (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x y) → (D.position x ∈ edgeArc x y))))) := by
  classical
  intro ι P D symmetric a b localStar rep rep_spec period pulled_contact hab g gproperties
      halfArc edgeArc x y hxy
  have hrev := (symmetric x y).mp hxy
  simp only [edgeArc, halfArc, ite_eq_left hxy, ite_eq_left hrev]
  left
  exact ⟨⟨0, by norm_num⟩, (gproperties x y hxy).2.2.1⟩

private theorem hendAt1222 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact
            P b a) → (∀ (a : ι), ∀ (b : ι), ∀ (localStar : (a : ι) →
            { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        ∀ (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x y) → (D.position y ∈ edgeArc x y))))) := by
  classical
  intro ι P D symmetric a b localStar rep rep_spec period pulled_contact hab g gproperties
      halfArc edgeArc x y hxy
  have hrev := (symmetric x y).mp hxy
  simp only [edgeArc, halfArc, ite_eq_left hxy, ite_eq_left hrev]
  right
  exact ⟨⟨0, by norm_num⟩, (gproperties y x hrev).2.2.1⟩

private theorem vertex_mem :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        (∀ (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x y) → (D.position x ∈ edgeArc x y)) → ((∀
            (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x y) → (D.position y ∈ edgeArc x y)) → (∀
            (x : ι), ∀ (y : ι), ∀ (i : ι), (P3723T1EdgeContact P x y) → ((i = x ∨ i = y) →
            (D.position i ∈ edgeArc x y)))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g halfArc edgeArc hstart hend
      x y i hxy hi
  rcases hi with hi | hi
  · rw [hi]
    exact hstart x y hxy
  · rw [hi]
    exact hend x y hxy

private theorem hab_mem :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (∀ (c : ι), ∀ (d : ι), (P3723T1EdgeContact P b a) → (∀
                (i : ι), (i ∈ ({a, b} : Set ι) ∩ {c, d}) → ((i = a ∨ i = b) → ((i = c ∨ i = d) →
                (D.position i ∈ Set.range (g a b) ∪ Set.range (g b a)))))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g gproperties c d hba i hi
      hiab hicd
  rcases hiab with hi | hi
  · subst i
    left
    exact ⟨⟨0, by norm_num⟩, (gproperties a b hab).2.2.1⟩
  · subst i
    right
    exact ⟨⟨0, by norm_num⟩, (gproperties b a hba).2.2.1⟩

private theorem hcd_mem :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), (P3723T1EdgeContact P a
                b) → (
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (∀ (c : ι), ∀ (d : ι), (P3723T1EdgeContact P c d) →
                ((P3723T1EdgeContact P d c) → (∀ (i : ι), (i ∈ ({a, b} : Set ι) ∩ {c, d}) → ((i
                    = a ∨ i =
                b) → ((i = c ∨ i = d) → ((D.position i ∈ Set.range (g a b) ∪ Set.range (g b a)) →
                (D.position i ∈ Set.range (g c d) ∪ Set.range (g d c)))))))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g gproperties c d hcd hdc i hi
      hiab hicd hab_mem
  rcases hicd with hi | hi
  · subst i
    left
    exact ⟨⟨0, by norm_num⟩, (gproperties c d hcd).2.2.1⟩
  · subst i
    right
    exact ⟨⟨0, by norm_num⟩, (gproperties d c hdc).2.2.1⟩

private theorem owner_unique :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let owner : GaussianInt → ι := fun x =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P x).exists
        (∀ (x : GaussianInt), x ∈ (P.tile (owner x)).cells) → (∀ (x : GaussianInt), ∀ (a : ι), (x
            ∈ (P.tile a).cells) → (a = owner x)) ) := by
  classical
  intro ι P owner owner_mem x a ha
  exact (PeriodicTileIndexedMultiplicityOne P x).unique ha (owner_mem x)

private theorem arc_endpoint_owner :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact P b a) → (∀ (localStar :
            (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) →
            ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        (∀ (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x y) → (Set.range (g x y) ⊆
            TileRealization (P.tile x))) → (∀ (K : Set (ℝ × ℝ)),
        let cells : Set GaussianInt :=
          {x | ∃ p ∈ K, p ∈ ClosedSquareRealization x}
        let owner : GaussianInt → ι := fun x =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P x).exists
        (∀ (x : GaussianInt), ∀ (a : ι), (x ∈ (P.tile a).cells) → (a = owner x)) → (
        let ownerIndices : Set ι := owner '' cells
        ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) → (∀ (z : Real × Real), (z ∈ edgeArc a
            b) → ((z ∈ K) → (a ∈ ownerIndices ∨ b ∈ ownerIndices)))))) ) := by
  classical
  intro ι P D symmetric localStar rep rep_spec period pulled_contact g halfArc edgeArc
      half_range_in_tile K cells owner owner_unique ownerIndices a b hab z hz hzK
  have hba : P3723T1EdgeContact P b a := (symmetric a b).mp hab
  change z ∈ halfArc a b ∪ halfArc b a at hz
  simp only [halfArc, ite_eq_left hab, ite_eq_left hba] at hz
  rcases hz with hz | hz
  · have htile : z ∈ TileRealization (P.tile a) := half_range_in_tile a b hab hz
    change z ∈ ⋃ x ∈ (P.tile a).cells, ClosedSquareRealization x at htile
    simp only [Set.mem_iUnion] at htile
    obtain ⟨x, hx, hxsq⟩ := htile
    have hxowner : a = owner x := owner_unique x a hx
    have hxmem : x ∈ cells := ⟨z, hzK, hxsq⟩
    left
    change ∃ x, x ∈ cells ∧ owner x = a
    exact ⟨x, hxmem, hxowner.symm⟩
  · have htile : z ∈ TileRealization (P.tile b) := half_range_in_tile b a hba hz
    change z ∈ ⋃ x ∈ (P.tile b).cells, ClosedSquareRealization x at htile
    simp only [Set.mem_iUnion] at htile
    obtain ⟨x, hx, hxsq⟩ := htile
    have hxowner : b = owner x := owner_unique x b hx
    have hxmem : x ∈ cells := ⟨z, hzK, hxsq⟩
    right
    change ∃ x, x ∈ cells ∧ owner x = b
    exact ⟨x, hxmem, hxowner.symm⟩

private theorem houtAt1326 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (K : Set
            (ℝ × ℝ)),
        let cells : Set GaussianInt :=
          {x | ∃ p ∈ K, p ∈ ClosedSquareRealization x}
        let owner : GaussianInt → ι := fun x =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P x).exists
        let ownerIndices : Set ι := owner '' cells
        ∀ (hownerIndices : ownerIndices.Finite),
        let outgoing : Finset (ι × ι) := hownerIndices.toFinset.biUnion fun a =>
          (D.finite_degree a).toFinset.image fun b => (a, b)
        ∀ (e : ι × ι), (e.1 ∈ hownerIndices.toFinset) → ((e.2 ∈ (D.finite_degree e.1).toFinset) →
            (e ∈ outgoing)) ) := by
  classical
  intro ι P D K cells owner ownerIndices hownerIndices outgoing e ha' hb'
  apply Finset.mem_biUnion.mpr
  refine ⟨e.1, ha', ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨e.2, hb', rfl⟩

private theorem ha'At1334 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact P b a) → (∀ (e : ι × ι),
            (P3723T1EdgeContact P e.1 e.2) → (e.1 ∈ (D.finite_degree e.2).toFinset)) ) := by
  classical
  intro ι P D symmetric e hab
  have hsym : P3723T1EdgeContact P e.2 e.1 := (symmetric e.1 e.2).mp hab
  exact (D.finite_degree e.2).mem_toFinset.mpr hsym

private theorem houtAt1337 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (K : Set
            (ℝ × ℝ)),
        let cells : Set GaussianInt :=
          {x | ∃ p ∈ K, p ∈ ClosedSquareRealization x}
        let owner : GaussianInt → ι := fun x =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P x).exists
        let ownerIndices : Set ι := owner '' cells
        ∀ (hownerIndices : ownerIndices.Finite),
        let outgoing : Finset (ι × ι) := hownerIndices.toFinset.biUnion fun a =>
          (D.finite_degree a).toFinset.image fun b => (a, b)
        ∀ (e : ι × ι), (e.2 ∈ hownerIndices.toFinset) → ((e.1 ∈ (D.finite_degree e.2).toFinset) →
            ((e.2, e.1) ∈ outgoing)) ) := by
  classical
  intro ι P D K cells owner ownerIndices hownerIndices outgoing e hb' ha'
  apply Finset.mem_biUnion.mpr
  refine ⟨e.2, hb', ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨e.1, ha', rfl⟩

end ContactDrawingGeometry

namespace ContactDrawingConcatenation

private theorem hpoly :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), ∀ (a : ι),
            ∀ (b : ι), ∀ (localStar : (a : ι) → { b : ι // P3723T1EdgeContact P a b } → (↑(Icc
            (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))), ∀ (hab :
                P3723T1EdgeContact P a b),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        ∀ (polyab : P3723T1PolygonalParameterization (g a b)), ∀ (polyba :
            P3723T1PolygonalParameterization (g b a)),
        let clip (x : Real) : Icc (0 : Real) 1 :=
          ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
        let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
        let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
        let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
        (∀ (s : Icc (0 : Real) 1), (s ∈ A) → ((clip (2 * s) : Real) = 2 * s)) → ((∀ (s : Icc (0 :
            Real) 1), (s ∉ A) → ((clip (2 - 2 * s) : Real) = 2 -
            2 * s)) → (∀ (p : ℝ × ℝ), (g a b ⟨1, by norm_num⟩ = p) → ((g b a ⟨1,
            by norm_num⟩ = p) → (Nonempty (P3723T1PolygonalParameterization f)))))) := by
  classical
  intro ι P D a b localStar rep rep_spec period pulled_contact hab g polyab polyba clip left
      right A f hscale_left hscale_right p hendab hendba
  let m := polyab.count
  let n := polyba.count
  have hmpos : 0 < m := polyab.positive
  have hnpos : 0 < n := polyba.positive
  let tm : Fin (m + n + 1) → Real := fun i =>
    if hi : i.val ≤ m then
      polyab.time ⟨i.val, by omega⟩ / 2
    else
      1 - polyba.time ⟨n + m - i.val, by omega⟩ / 2
  have left_eval (j : Fin (m + 1)) :
      tm ⟨j.val, by omega⟩ = polyab.time j / 2 := ContactDrawingGeometry.left_eval ι P D a b
          localStar rep_spec pulled_contact hab polyab polyba hnpos j
  have right_eval (j : Fin n) := ContactDrawingGeometry.right_eval ι P D a b localStar
      rep_spec pulled_contact hab polyab polyba j
  have htm_strict := ContactDrawingGeometry.htm_strict ι P D a b localStar rep_spec
      pulled_contact hab polyab polyba hnpos left_eval right_eval
  have htm_start := ContactDrawingGeometry.htm_start ι P D a b localStar rep_spec
      pulled_contact hab polyab polyba hmpos hnpos left_eval
  have htm_mid := ContactDrawingGeometry.htm_mid ι P D a b localStar rep_spec pulled_contact
      hab polyab polyba hnpos left_eval
  have htm_finish := ContactDrawingGeometry.htm_finish ι P D a b localStar rep_spec
      pulled_contact hab polyab polyba hnpos right_eval
  refine ⟨{
    count := m + n
    positive := by omega
    time := tm
    strict := htm_strict
    start := htm_start
    finish := htm_finish
    affine_on := ?_
  }⟩
  intro i
  by_cases hleftidx : i.val < m
  · let j : Fin m := ⟨i.val, by omega⟩
    let j' : Fin (m + 1) := j.succ
    obtain ⟨C, V, hpiece⟩ := polyab.affine_on j
    refine ⟨C, 2 • V, ?_⟩
    intro s hlo hhi
    have hcast := ContactDrawingGeometry.hcastAt761 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i
    have hsucc := ContactDrawingGeometry.hsuccAt764 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i
    have hlo' := ContactDrawingGeometry.hlo'At767 ι P D a b localStar rep_spec pulled_contact
        hab polyab polyba i s hlo hcast
    have hhi' := ContactDrawingGeometry.hhi'At770 ι P D a b localStar rep_spec pulled_contact
        hab polyab polyba i s hhi hsucc
    have hstartIndex : (⟨i.val, by omega⟩ : Fin (m + n + 1)) =
        ⟨j.castSucc.val, by omega⟩ := by apply Fin.ext; rfl
    have hendIndex : (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)) =
        ⟨j'.val, by omega⟩ := by apply Fin.ext; rfl
    have hstart : tm ⟨i.val, by omega⟩ = polyab.time j.castSucc / 2 := by
      rw [hstartIndex, left_eval j.castSucc]
    have hend : tm ⟨i.val + 1, by omega⟩ = polyab.time j' / 2 := by
      rw [hendIndex, left_eval j']
    have hlastbound := ContactDrawingGeometry.hlastbound ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hleftidx
    have hsA := ContactDrawingGeometry.hsAAt786 ι P D a b localStar rep_spec pulled_contact
        hab polyab polyba hnpos i hleftidx s hhi' hend hlastbound
    let t : Icc (0 : Real) 1 := ⟨2 * (s : Real), by
      constructor
      · nlinarith [s.property.1]
      · nlinarith⟩
    have htlower := ContactDrawingGeometry.htlowerAt794 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba hnpos i hleftidx s hlo' hhi' hstart hend hlastbound
    have htupper := ContactDrawingGeometry.htupperAt799 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba hnpos i hleftidx s hhi' hend hlastbound
    have htval := ContactDrawingGeometry.htvalAt804 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba hscale_left hnpos i hleftidx s hhi' hend hlastbound hsA
    have hfvalue := ContactDrawingGeometry.hfvalueAt807 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba hnpos i hleftidx s hhi' hend hlastbound hsA htval
    calc
      f s = g a b t := hfvalue
      _ = C + (t : Real) • V := hpiece t htlower htupper
      _ = C + (s : Real) • (2 • V) := by
        have htdef : (t : Real) = 2 * (s : Real) := rfl
        rw [htdef, ← smul_smul]
        ext <;> simp [smul_eq_mul] <;> ring
  · let r : Nat := i.val - m
    have hr : r < n := by dsimp [r]; omega
    let k : Fin n := ⟨n - r - 1, by dsimp [r]; omega⟩
    obtain ⟨C, V, hpiece⟩ := polyba.affine_on k
    refine ⟨C + 2 • V, -2 • V, ?_⟩
    intro s hlo hhi
    have hcast := ContactDrawingGeometry.hcastAt824 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i
    have hsucc := ContactDrawingGeometry.hsuccAt827 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i
    have hlo' : tm ⟨i.val, by omega⟩ ≤ (s : Real)  := ContactDrawingGeometry.hlo'At830 ι P D a b
        localStar rep_spec pulled_contact
        hab polyab polyba i s hlo hcast
    have hhi' : (s : Real) ≤ tm ⟨i.val + 1, by omega⟩  := ContactDrawingGeometry.hhi'At833 ι P D
        a b localStar rep_spec pulled_contact
        hab polyab polyba i s hhi hsucc
    have hcurIndex := ContactDrawingGeometry.hcurIndex ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hr
    have hnextIndex := ContactDrawingGeometry.hnextIndex ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hr
    have hendIndex : (⟨i.val + 1, by omega⟩ : Fin (m + n + 1)) =
        ⟨m + 1 + r, by omega⟩ := ContactDrawingGeometry.hendIndexAt843 ι P D a b localStar
            rep_spec pulled_contact hab polyab polyba i hleftidx hr
    have hstart : tm ⟨i.val, by omega⟩ =
        1 - polyba.time k.succ / 2 := ContactDrawingGeometry.hstartAt848 ι P D a b localStar
            rep_spec pulled_contact hab polyab polyba hnpos right_eval htm_mid i hleftidx hr
    have hend : tm ⟨i.val + 1, by omega⟩ =
        1 - polyba.time k.castSucc / 2 := ContactDrawingGeometry.hendAt880 ι P D a b
            localStar rep_spec pulled_contact hab polyab polyba right_eval i hr hendIndex
    have hA_imp_mid := ContactDrawingGeometry.hA_imp_mid ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba hnpos htm_strict htm_mid i hleftidx hr s hlo'
    have hsRight := ContactDrawingGeometry.hsRight ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba p hendab hendba i s hA_imp_mid
    have hkbound := ContactDrawingGeometry.hkbound ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hr
    have hsHalf := ContactDrawingGeometry.hsHalf ι P D a b localStar rep_spec pulled_contact
        hab polyab polyba i hr s hlo' hstart hkbound
    let t : Icc (0 : Real) 1 := ⟨2 - 2 * (s : Real), by
      constructor
      · have hlow := hlo'
        rw [hstart] at hlow
        nlinarith [s.property.2]
      · nlinarith [s.property.1, hsHalf]⟩
    have htlower := ContactDrawingGeometry.htlowerAt951 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hr s hlo' hhi' hstart hend hkbound hsHalf
    have htupper := ContactDrawingGeometry.htupperAt956 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hr s hlo' hstart hkbound hsHalf
    have htval := ContactDrawingGeometry.htvalAt961 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba hscale_right i hr s hlo' hstart hA_imp_mid hkbound
        hsHalf
    have hfvalue := ContactDrawingGeometry.hfvalueAt970 ι P D a b localStar rep_spec
        pulled_contact hab polyab polyba i hr s hlo' hstart hsRight hkbound hsHalf htval
    calc
      f s = g b a t := hfvalue
      _ = C + (t : Real) • V := hpiece t htlower htupper
      _ = C + 2 • V + (s : Real) • (-2 • V) := by
        change C + (2 - 2 * (s : Real)) • V =
          C + 2 • V + (s : Real) • (-2 • V)
        ext <;> simp [smul_eq_mul] <;> ring

end ContactDrawingConcatenation

namespace ContactDrawingParameterization

private theorem full_parameters :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact
            P b a) → ((∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) → (∃ p,
            D.port a b = some p)) → (∀ (localStar : (a : ι) →
            { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → (
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        ∀ a, ∀ b, P3723T1EdgeContact P a b →
          ∃ f : Icc (0 : Real) 1 → Real × Real,
            Continuous f ∧ Function.Injective f ∧ Set.range f = edgeArc a b ∧
            f ⟨0, by norm_num⟩ = D.position a ∧ f ⟨1, by norm_num⟩ = D.position b ∧
            Nonempty (P3723T1PolygonalParameterization f))))) := by
  classical
  intro ι P D symmetric port_exists localStar rep rep_spec period pulled_contact g gproperties
      halfArc edgeArc a b hab
  obtain ⟨hgab, higab, hg0ab, hg1ab, ⟨polyab⟩, hsab⟩ := gproperties a b hab
  have hba : P3723T1EdgeContact P b a := (symmetric a b).mp hab
  obtain ⟨hgba, higba, hg0ba, hg1ba, ⟨polyba⟩, hsba⟩ := gproperties b a hba
  let clip (x : Real) : Icc (0 : Real) 1 :=
    ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclip_cont := ContactDrawingGeometry.hclip_cont
  let left : Icc (0 : Real) 1 → Real × Real := fun s => g a b (clip (2 * s))
  let right : Icc (0 : Real) 1 → Real × Real := fun s => g b a (clip (2 - 2 * s))
  let A : Set (Icc (0 : Real) 1) := {s | (s : Real) ≤ 1 / 2}
  let f : Icc (0 : Real) 1 → Real × Real := A.piecewise left right
  have hleftc : Continuous left := hgab.comp (hclip_cont.comp (continuous_const.mul
      continuous_subtype_val))
  have hrightc : Continuous right := hgba.comp
    (hclip_cont.comp (continuous_const.sub (continuous_const.mul continuous_subtype_val)))
  have hmeet (s : Icc (0 : Real) 1) (hs : s ∈ (Set.univ : Set (Icc (0 : Real) 1)) ∩ frontier A)
      := ContactDrawingGeometry.hmeet ι P D a b localStar rep_spec pulled_contact hab hg1ab
      hg1ba s hs
  have hfcont := ContactDrawingGeometry.hfcont ι P D a b localStar rep_spec pulled_contact hab
      hleftc hrightc hmeet
  have hscale_left (s : Icc (0 : Real) 1) (hs : s ∈ A) := ContactDrawingGeometry.hscale_left s hs
  have hscale_right (s : Icc (0 : Real) 1) (hs : s ∉ A) := ContactDrawingGeometry.hscale_right
      s hs
  have hf0 := ContactDrawingGeometry.hf0 ι P D a b localStar rep_spec pulled_contact hab hg0ab
  have hf1 := ContactDrawingGeometry.hf1 ι P D a b localStar rep_spec pulled_contact hab hba hg0ba
  obtain ⟨p, hp⟩ := port_exists a b hab
  have hpba : D.port b a = some p := by rw [D.port_symmetric, hp]
  have hendab := ContactDrawingGeometry.hendab ι P D a b localStar rep_spec pulled_contact hab
      gproperties p hp
  have hendba := ContactDrawingGeometry.hendba ι P D a b localStar rep_spec pulled_contact hab
      gproperties hba p hpba
  have hcross := ContactDrawingGeometry.hcross ι P D a b localStar rep_spec pulled_contact hab
      hsab hsba p hendab hendba
  have hfinj := ContactDrawingGeometry.hfinj ι P D a b localStar rep_spec pulled_contact hab
      higab higba hscale_left hscale_right p hendab hendba hcross
  have hrange := ContactDrawingGeometry.hrange ι P D a b localStar rep_spec pulled_contact hab
      hba p hendab hendba
  have hpoly : Nonempty (P3723T1PolygonalParameterization f) :=
      ContactDrawingConcatenation.hpoly ι P D a b localStar rep_spec pulled_contact hab polyab
      polyba hscale_left hscale_right p hendab hendba
  exact ⟨f, hfcont, hfinj, hrange, hf0, hf1, hpoly⟩

end ContactDrawingParameterization

namespace ContactDrawingCertificate

private theorem drawingCertificate :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1ContactPorts P), (∀ (a : ι),
            ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact
            P b a) → ((∀ (a : ι), ∀ (b : ι), ∀ (p : Real × Real), (D.port a b = some p)
            → (P3723T1EdgeContact P a b)) → (∀ (localStar : (a : ι) →
            { b : ι // P3723T1EdgeContact P a b } → (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        ∀ (pulled_contact : ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) →
            (P3723T1EdgeContact P (rep a) (P.shift (-period a) b))),
        let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
          if hab : P3723T1EdgeContact P a b then
            localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
              GaussianRealPoint (period a)
          else D.position a
        (∀ a, ∀ b, P3723T1EdgeContact P a b →
          Continuous (g a b) ∧ Function.Injective (g a b) ∧
          g a b ⟨0, by norm_num⟩ = D.position a ∧
          D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
          Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
          Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
            {g a b ⟨1, by norm_num⟩}) → ((∀ a, ∀ b, ∀ c, P3723T1EdgeContact P
                a b → P3723T1EdgeContact P a c → b ≠ c → Set.range (g a b) ∩ Set.range (g a c)
                = {D.position a}) → (
        let halfArc (a b : ι) : Set (Real × Real) :=
          if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
        let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
        (∀ a, ∀ b, ∀ p, D.port a b = some p →
          ∃ f : Icc (0 : Real) 1 → Real × Real,
            Continuous f ∧ Function.Injective f ∧ Set.range f = halfArc a b ∧
            f ⟨0, by norm_num⟩ = D.position a ∧ f ⟨1, by norm_num⟩ = p ∧
            Nonempty (P3723T1PolygonalParameterization f)) → ((∀ a, ∀ b, P3723T1EdgeContact P a
                b →
          ∃ f : Icc (0 : Real) 1 → Real × Real,
            Continuous f ∧ Function.Injective f ∧ Set.range f = edgeArc a b ∧
            f ⟨0, by norm_num⟩ = D.position a ∧ f ⟨1, by norm_num⟩ = D.position b ∧
            Nonempty (P3723T1PolygonalParameterization f)) → ((∀ (A : Set (Real × Real)), ∀ (f
                : Icc (0 : Real) 1 → Real × Real), (Continuous f) → ((Function.Injective f) →
                ((Set.range f = A) → (∃ h : Icc (0 : Real) 1 ≃ₜ A, ∀ s, (h s : Real × Real) = f
                s)))) → ((∀ u : P.lattice, ∀ a, ∀ b, halfArc (P.shift u a) (P.shift u b) = (fun p
                => p + GaussianRealPoint u) '' halfArc a b) → ((∀ (K : Set (Real × Real)),
                    (IsCompact K) → (Set.Finite {x : GaussianInt | ∃ p ∈ K, p ∈
                ClosedSquareRealization x})) → ((∀ (x : ι), ∀ (y : ι), (P3723T1EdgeContact P x
                y) → (Set.range (g x y) ⊆ TileRealization (P.tile x))) → ((∀ (x : ι), ∀ (y : ι),
                    ∀ (u : ι), ∀ (v : ι), (P3723T1EdgeContact P x y) → ((P3723T1EdgeContact P u
                v) → ((({x, y} : Set ι) ≠ {u, v}) → ((x ≠ u) → (Disjoint (Set.range (g x y))
                (Set.range (g u v))))))) → (∃ R : P3723T1AllContactRouting P,
                R.toP3723T1ContactPorts = D)))))))))))) := by
  classical
  intro ι P D symmetric present localStar rep rep_spec period pulled_contact g gproperties
      gintersections halfArc edgeArc half_parameters full_parameters parameter_homeomorph
      half_periodic compact_cells_finite half_range_in_tile half_disjoint
  refine ⟨{
    toP3723T1ContactPorts := D
    halfArc := halfArc
    edgeArc := edgeArc
    noncontact_has_no_halfArc := ?_
    noncontact_has_no_edgeArc := ?_
    halfArc_homeomorph := ?_
    halfArc_supported := ?_
    incident_halfArc_intersections := ?_
    edgeArc_symmetric := ?_
    edgeArc_from_halfArcs := ?_
    edgeArc_homeomorph := ?_
    edgeArc_intersections := ?_
    compact_local_finiteness := ?_
    halfArc_parameterization := half_parameters
    edgeArc_parameterization := full_parameters
    halfArc_periodic := half_periodic
    edgeArc_periodic := ?_
  }, rfl⟩
  · intro a b hn
    simp only [halfArc, ite_eq_right hn]
  · intro a b hn
    have hba : ¬ P3723T1EdgeContact P b a := fun h => hn ((symmetric a b).mpr h)
    simp only [edgeArc, halfArc, ite_eq_right hn, ite_eq_right hba, Set.union_empty]
  · intro a b p hp
    obtain ⟨f, hc, hi, hr, h0, h1, _hpoly⟩ := half_parameters a b p hp
    obtain ⟨h, hh⟩ := parameter_homeomorph (halfArc a b) f hc hi hr
    exact ⟨h, (hh _).trans h0, (hh _).trans h1⟩
  · intro a b p hp
    have hab := present a b p hp
    obtain ⟨_hc, _hi, _h0, h1, _hpoly, hs⟩ := gproperties a b hab
    have hend : g a b ⟨1, by norm_num⟩ = p := Option.some.inj (h1.symm.trans hp)
    simpa only [halfArc, ite_eq_left hab, hend] using hs
  · intro a b c hab hac hbc
    simpa only [halfArc, ite_eq_left hab, ite_eq_left hac] using gintersections a b c hab hac hbc
  · intro a b
    exact Set.union_comm _ _
  · intro a b p hp
    rfl
  · intro a b hab
    obtain ⟨f, hc, hi, hr, h0, h1, _hpoly⟩ := full_parameters a b hab
    obtain ⟨h, hh⟩ := parameter_homeomorph (edgeArc a b) f hc hi hr
    exact ⟨h, (hh _).trans h0, (hh _).trans h1⟩
  · intro a b c d hab hcd hpair
    have hba : P3723T1EdgeContact P b a := (symmetric a b).mp hab
    have hdc : P3723T1EdgeContact P d c := (symmetric c d).mp hcd
    have half_subset (x y u v : ι) (hxy : P3723T1EdgeContact P x y)
        (huv : P3723T1EdgeContact P u v)
        (hxyuv : ({x, y} : Set ι) ≠ {u, v}) :
        Set.range (g x y) ∩ Set.range (g u v) ⊆
          D.position '' (({x, y} : Set ι) ∩ {u, v}) := ContactDrawingGeometry.half_subset ι P D a
              b localStar rep_spec pulled_contact hab gintersections half_disjoint x y u v hxy
              huv hxyuv
    have hstart (x y : ι) (hxy : P3723T1EdgeContact P x y) :
        D.position x ∈ edgeArc x y := ContactDrawingGeometry.hstartAt1216 ι P D symmetric a b
            localStar rep_spec pulled_contact hab gproperties x y hxy
    have hend (x y : ι) (hxy : P3723T1EdgeContact P x y) :
        D.position y ∈ edgeArc x y := ContactDrawingGeometry.hendAt1222 ι P D symmetric a b
            localStar rep_spec pulled_contact hab gproperties x y hxy
    have vertex_mem (x y i : ι) (hxy : P3723T1EdgeContact P x y)
        (hi : i = x ∨ i = y) := ContactDrawingGeometry.vertex_mem ι P D a b localStar rep_spec
            pulled_contact hab hstart hend x y i hxy hi
    have hfull : edgeArc a b = halfArc a b ∪ halfArc b a := rfl
    have hfull' : edgeArc c d = halfArc c d ∪ halfArc d c := rfl
    simp only [edgeArc, halfArc, ite_eq_left hab, ite_eq_left hba, ite_eq_left hcd, ite_eq_left
        hdc]
    ext z
    constructor
    · rintro ⟨hzab, hzcd⟩
      rcases hzab with hzab | hzba
      · rcases hzcd with hzcd | hzdc
        · exact half_subset a b c d hab hcd hpair ⟨hzab, hzcd⟩
        · simpa [Set.pair_comm] using
            half_subset a b d c hab hdc (by simpa [Set.pair_comm] using hpair) ⟨hzab, hzdc⟩
      · rcases hzcd with hzcd | hzdc
        · simpa [Set.pair_comm] using
            half_subset b a c d hba hcd (by simpa [Set.pair_comm] using hpair) ⟨hzba, hzcd⟩
        · simpa [Set.pair_comm] using
            half_subset b a d c hba hdc (by simpa [Set.pair_comm] using hpair) ⟨hzba, hzdc⟩
    · intro hz
      change ∃ i ∈ ({a, b} : Set ι) ∩ {c, d}, D.position i = z at hz
      obtain ⟨i, hi, hpos⟩ := hz
      subst z
      have hiab : i = a ∨ i = b := by simpa using hi.1
      have hicd : i = c ∨ i = d := by simpa using hi.2
      have hab_mem := ContactDrawingGeometry.hab_mem ι P D a b localStar rep_spec pulled_contact
          hab gproperties c d hba i hi hiab hicd
      have hcd_mem := ContactDrawingGeometry.hcd_mem ι P D a b localStar rep_spec pulled_contact
          hab gproperties c d hcd hdc i hi hiab hicd hab_mem
      exact ⟨hab_mem, hcd_mem⟩
  · intro K hK
    let cells : Set GaussianInt :=
      {x | ∃ p ∈ K, p ∈ ClosedSquareRealization x}
    have hcells : cells.Finite := compact_cells_finite K hK
    let owner : GaussianInt → ι := fun x =>
      Classical.choose (PeriodicTileIndexedMultiplicityOne P x).exists
    have owner_mem (x : GaussianInt) : x ∈ (P.tile (owner x)).cells :=
      Classical.choose_spec (PeriodicTileIndexedMultiplicityOne P x).exists
    have owner_unique (x : GaussianInt) (a : ι)
        (ha : x ∈ (P.tile a).cells) := ContactDrawingGeometry.owner_unique ι P owner_mem x a ha
    let ownerIndices : Set ι := owner '' cells
    have hownerIndices : ownerIndices.Finite := hcells.image owner
    have arc_endpoint_owner (a b : ι) (hab : P3723T1EdgeContact P a b)
        (z : Real × Real) (hz : z ∈ edgeArc a b) (hzK : z ∈ K) :=
            ContactDrawingGeometry.arc_endpoint_owner ι P D symmetric localStar rep_spec
            pulled_contact half_range_in_tile K owner_unique a b hab z hz hzK
    let outgoing : Finset (ι × ι) := hownerIndices.toFinset.biUnion fun a =>
      (D.finite_degree a).toFinset.image fun b => (a, b)
    let pairs : Finset (ι × ι) := outgoing ∪ outgoing.image Prod.swap
    apply pairs.finite_toSet.subset
    intro e he
    rcases he with ⟨hab, hmeet⟩
    obtain ⟨z, hz⟩ := hmeet
    have hendpoint := arc_endpoint_owner e.1 e.2 hab z hz.1 hz.2
    change e ∈ (pairs : Set (ι × ι))
    rcases hendpoint with ha | hb
    · have ha' : e.1 ∈ hownerIndices.toFinset := by
        exact hownerIndices.mem_toFinset.mpr ha
      have hb' : e.2 ∈ (D.finite_degree e.1).toFinset := by
        exact (D.finite_degree e.1).mem_toFinset.mpr hab
      have hout := ContactDrawingGeometry.houtAt1326 ι P D K hownerIndices e ha' hb'
      exact Finset.mem_union_left _ hout
    · have hb' : e.2 ∈ hownerIndices.toFinset := by
        exact hownerIndices.mem_toFinset.mpr hb
      have ha' := ContactDrawingGeometry.ha'At1334 ι P D symmetric e hab
      have hout := ContactDrawingGeometry.houtAt1337 ι P D K hownerIndices e hb' ha'
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(e.2, e.1), hout, by cases e; rfl⟩
  · intro u a b
    simp only [edgeArc, half_periodic, Set.image_union]

end ContactDrawingCertificate

theorem P3723T1AllContactDrawingExists {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1ContactPorts P) :
    ∃ R : P3723T1AllContactRouting P, R.toP3723T1ContactPorts = D := by
-- BODY
  classical
  have symmetric (a b : ι) := ContactDrawingGeometry.symmetric ι P a b
  have present (a b : ι) (p : Real × Real) (hp : D.port a b = some p) :=
      ContactDrawingGeometry.present ι P D a b p hp
  have port_exists (a b : ι) (hab : P3723T1EdgeContact P a b) :=
      ContactDrawingGeometry.port_exists ι P D a b hab
  let q (a : ι) (b : {b // P3723T1EdgeContact P a b}) : Real × Real :=
    Classical.choose (port_exists a b b.property)
  have hq (a : ι) (b : {b // P3723T1EdgeContact P a b}) :
      D.port a b = some (q a b) := Classical.choose_spec (port_exists a b b.property)
  have qfrontier (a : ι) (b : {b // P3723T1EdgeContact P a b}) :
      q a b ∈ frontier (TileRealization (P.tile a)) :=
    (D.port_frontier a b (q a b) (hq a b)).1
  have qinjective (a : ι) := ContactDrawingGeometry.qinjective ι P D port_exists hq a
  choose localStar local_properties local_support local_intersections using
    fun a => P3723T1GridDiskBoundaryStars (P.tile a) (P.tiles_are_disks a)
      (D.position a) (D.position_in_tile_interior a) (q a) (qfrontier a) (qinjective a)
  let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
  have rep_spec (a : ι) : rep a ∈ P.vertexOrbitReps ∧
      ∃ u : P.lattice, a = P.shift u (rep a) :=
    Classical.choose_spec (P.vertex_orbit_representatives a).exists
  let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
  have period_spec (a : ι) : a = P.shift (period a) (rep a) :=
    Classical.choose_spec (rep_spec a).2
  have pulled_contact (a b : ι) (hab : P3723T1EdgeContact P a b) :=
      ContactDrawingGeometry.pulled_contact ι P D rep_spec period_spec a b hab
  let g (a b : ι) (s : Icc (0 : Real) 1) : Real × Real :=
    if hab : P3723T1EdgeContact P a b then
      localStar (rep a) ⟨P.shift (-period a) b, pulled_contact a b hab⟩ s +
        GaussianRealPoint (period a)
    else D.position a
  have gproperties : ∀ a b, P3723T1EdgeContact P a b →
      Continuous (g a b) ∧ Function.Injective (g a b) ∧
      g a b ⟨0, by norm_num⟩ = D.position a ∧
      D.port a b = some (g a b ⟨1, by norm_num⟩) ∧
      Nonempty (P3723T1PolygonalParameterization (g a b)) ∧
      Set.range (g a b) ⊆ interior (TileRealization (P.tile a)) ∪
        {g a b ⟨1, by norm_num⟩}  := ContactDrawingGeometry.gproperties ι P D port_exists hq
            localStar
      local_properties local_support rep_spec period_spec pulled_contact
  have range_form (a b : ι) (hab : P3723T1EdgeContact P a b) :=
      ContactDrawingGeometry.range_form ι P D localStar rep_spec pulled_contact a b hab
  have gintersections : ∀ a b c, P3723T1EdgeContact P a b →
      P3723T1EdgeContact P a c → b ≠ c →
      Set.range (g a b) ∩ Set.range (g a c) = {D.position a} :=
          ContactDrawingGeometry.gintersections ι P D localStar local_intersections rep_spec
          period_spec pulled_contact range_form
  have gperiodic := ContactDrawingGeometry.gperiodic ι P D localStar rep_spec period_spec
      pulled_contact
  let halfArc (a b : ι) : Set (Real × Real) :=
    if P3723T1EdgeContact P a b then Set.range (g a b) else ∅
  let edgeArc (a b : ι) : Set (Real × Real) := halfArc a b ∪ halfArc b a
  have half_parameters := ContactDrawingGeometry.half_parameters ι P D present localStar rep_spec
      pulled_contact gproperties
  have full_parameters : ∀ a b, P3723T1EdgeContact P a b →
      ∃ f : Icc (0 : Real) 1 → Real × Real,
        Continuous f ∧ Function.Injective f ∧ Set.range f = edgeArc a b ∧
        f ⟨0, by norm_num⟩ = D.position a ∧ f ⟨1, by norm_num⟩ = D.position b ∧
        Nonempty (P3723T1PolygonalParameterization f) :=
            ContactDrawingParameterization.full_parameters ι P D symmetric port_exists localStar
            rep_spec pulled_contact gproperties
  have parameter_homeomorph (A : Set (Real × Real))
      (f : Icc (0 : Real) 1 → Real × Real) (hc : Continuous f)
      (hi : Function.Injective f) (hr : Set.range f = A) :=
          ContactDrawingGeometry.parameter_homeomorph A f hc hi hr
  have half_periodic : ∀ u : P.lattice, ∀ a b,
      halfArc (P.shift u a) (P.shift u b) =
        (fun p => p + GaussianRealPoint u) '' halfArc a b := ContactDrawingGeometry.half_periodic
            ι P D localStar rep_spec pulled_contact gperiodic
  have tile_closed (T : ProtoTile) := ContactDrawingGeometry.tile_closed T
  have compact_cells_finite (K : Set (Real × Real)) (hK : IsCompact K) :=
      ContactDrawingGeometry.compact_cells_finite K hK
  have half_range_in_tile (x y : ι) (hxy : P3723T1EdgeContact P x y) :=
      ContactDrawingGeometry.half_range_in_tile ι P D localStar rep_spec pulled_contact
      gproperties tile_closed x y hxy
  have frontier_no_interior (T : ProtoTile) (p : Real × Real)
      (hp : p ∈ frontier (TileRealization T)) := ContactDrawingGeometry.frontier_no_interior
          tile_closed T p hp
  have half_disjoint (x y u v : ι)
      (hxy : P3723T1EdgeContact P x y) (huv : P3723T1EdgeContact P u v)
      (hpair : ({x, y} : Set ι) ≠ {u, v}) (hxu : x ≠ u) := ContactDrawingGeometry.half_disjoint ι
          P D port_exists localStar rep_spec pulled_contact gproperties frontier_no_interior x y
          u v hxy huv hpair hxu
  have drawingCertificate :
    ∃ R : P3723T1AllContactRouting P, R.toP3723T1ContactPorts = D :=
        ContactDrawingCertificate.drawingCertificate ι P D symmetric present localStar rep_spec
        pulled_contact gproperties gintersections half_parameters full_parameters
        parameter_homeomorph half_periodic compact_cells_finite half_range_in_tile half_disjoint
  exact drawingCertificate


end ApollonianSuperharmonic

end
