/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1IndexAction
public import LeanPool.ApollonianSuperharmonic.P4677T2IncidenceLedger

-- [TABLET NODE: P4715T1OrbitRepresentatives]

/-!
# P4715T1OrbitRepresentatives

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1OrbitRepresentatives :
    ∃ (vr : Finset PeriodicSubtileIndex)
      (er : Finset (PeriodicSubtileIndex × PeriodicSubtileIndex))
      (fr : Finset PeriodicSubtileFaceIndex),
    (∀ a, a ∈ vr ↔ a.first = 0 ∧ a.second = 0) ∧
    (∀ r ∈ er, AllowedSubtileIncidence r.1 r.2) ∧
    (∀ f, f ∈ fr ↔ f.first = 0 ∧ f.second = 0) ∧
    (∀ a, ∃! r, r ∈ vr ∧ ∃ k : Int × Int, a = P4715T1VertexShift k r) ∧
    (∀ a b, AllowedSubtileIncidence a b →
      ∃ r ∈ er, ∃ k : Int × Int,
        a = P4715T1VertexShift k r.1 ∧ b = P4715T1VertexShift k r.2) ∧
    ∀ f, ∃ r ∈ fr, ∃ k : Int × Int, f = P4715T1FaceShift k r := by
-- BODY
  classical
  let vr : Finset PeriodicSubtileIndex :=
    {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
      ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
  let fr : Finset PeriodicSubtileFaceIndex :=
    {⟨.I1, 0, 0⟩, ⟨.I2, 0, 0⟩, ⟨.I3, 0, 0⟩, ⟨.I4, 0, 0⟩,
      ⟨.J1, 0, 0⟩, ⟨.J2, 0, 0⟩, ⟨.J3, 0, 0⟩, ⟨.J4, 0, 0⟩,
      ⟨.J5, 0, 0⟩, ⟨.J6, 0, 0⟩, ⟨.J7, 0, 0⟩, ⟨.J8, 0, 0⟩}
  have hvr (a) : a ∈ vr ↔ a.first = 0 ∧ a.second = 0 := by
    rcases a with ⟨l, m, n⟩
    cases l <;> simp [vr, PeriodicSubtileIndex.mk.injEq]
  have hfr (f) : f ∈ fr ↔ f.first = 0 ∧ f.second = 0 := by
    rcases f with ⟨l, m, n⟩
    cases l <;> simp [fr, PeriodicSubtileFaceIndex.mk.injEq]
  have hn := P4677T2IncidenceLedger.2.2.1
  let er0 : Finset (PeriodicSubtileIndex × PeriodicSubtileIndex) :=
    vr.biUnion fun a => (hn a).toFinset.image (fun b => (a, b))
  let er := er0 ∪ er0.image Prod.swap
  have he0 {r} (hr : r ∈ er0) : AllowedSubtileIncidence r.1 r.2 := by
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (hn a).mem_toFinset.mp hb
  have he {r} (hr : r ∈ er) : AllowedSubtileIncidence r.1 r.2 := by
    rcases Finset.mem_union.mp hr with hr | hr
    · exact he0 hr
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      exact (he0 hs).symm
  refine ⟨vr, er, fr, hvr, fun _ => he, hfr, ?_, ?_, ?_⟩
  · intro a
    refine ⟨⟨a.label, 0, 0⟩, ⟨(hvr _).mpr ⟨rfl, rfl⟩,
      (a.first, a.second), ?_⟩, ?_⟩
    · simp [P4715T1VertexShift]
    · rintro ⟨l, m, n⟩ ⟨hs, k, hk⟩
      obtain ⟨hm, hn⟩ := (hvr _).mp hs
      change m = 0 at hm
      change n = 0 at hn
      subst m
      subst n
      have hl := congrArg PeriodicSubtileIndex.label hk
      change a.label = l at hl
      cases hl
      rfl
  · intro a b hab
    let k : Int × Int := (a.first, a.second)
    let x := P4715T1VertexShift (-k) a
    let y := P4715T1VertexShift (-k) b
    have hx : x ∈ vr := (hvr x).mpr (by simp [x, k, P4715T1VertexShift])
    have hxy : AllowedSubtileIncidence x y :=
      (P4715T1IndexAction.2.2.2.2.1 (-k) a b).mpr hab
    have hr : (x, y) ∈ er0 := by
      apply Finset.mem_biUnion.mpr
      exact ⟨x, hx, Finset.mem_image.mpr ⟨y, (hn x).mem_toFinset.mpr hxy, rfl⟩⟩
    refine ⟨(x, y), Finset.mem_union.mpr (Or.inl hr), k, ?_, ?_⟩
    · simp [x, k, P4715T1VertexShift]
    · simp [y, k, P4715T1VertexShift]
  · intro f
    refine ⟨⟨f.label, 0, 0⟩, (hfr _).mpr ⟨rfl, rfl⟩,
      (f.first, f.second), ?_⟩
    simp [P4715T1FaceShift]

end ApollonianSuperharmonic

end
