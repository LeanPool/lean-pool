/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4733T1FacePairOrbit
public import LeanPool.ApollonianSuperharmonic.P4733T1EdgeOrbit
public import LeanPool.ApollonianSuperharmonic.P4733T1RowIncidence
public import LeanPool.ApollonianSuperharmonic.P4733T1RowLabelRigidity
public import LeanPool.ApollonianSuperharmonic.P4677T2IncidenceLedger

-- [TABLET NODE: P4733T1FacePairNormalForm]

/-!
# P4733T1FacePairNormalForm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1FacePairNormalForm {u v : GaussianInt}
    {L : AddSubgroup GaussianInt} (D : P4677T2DrawingData u v L) :
    Function.Injective (P4733T1FacePairOrbit D) ∧
    ∀ a b, AllowedSubtileIncidence a b →
      ∀ f g, f ≠ g →
      (∃ i, SixSubtileFaceVertices f i = a) →
      (∃ i, SixSubtileFaceVertices f i = b) →
      (∃ i, SixSubtileFaceVertices g i = a) →
      (∃ i, SixSubtileFaceVertices g i = b) →
      ∃ t : Fin 18 × L × Bool,
        P4733T1FacePairOrbit D t = (f, g) ∧
        ((a = D.shift t.2.1 (P4733T1EdgeRow t.1).1.1 ∧
          b = D.shift t.2.1 (P4733T1EdgeRow t.1).1.2) ∨
        (a = D.shift t.2.1 (P4733T1EdgeRow t.1).1.2 ∧
          b = D.shift t.2.1 (P4733T1EdgeRow t.1).1.1)) := by
-- BODY
  have face_inj (w : L) : Function.Injective (D.faceShift w) := by
    intro f g h
    have h' := congrArg (D.faceShift (-w)) h
    simpa only [← D.faceShift_add, neg_add_cancel, D.faceShift_zero] using h'
  constructor
  · rintro ⟨r, w, s⟩ ⟨r', w', s'⟩ h
    have hl := congrArg (fun p => (p.1.label, p.2.label)) h
    have hrs : (r, s) = (r', s') := P4733T1RowLabelRigidity (by
      cases s <;> cases s' <;>
        simpa [P4733T1FacePairOrbit, D.faceShift_eq] using hl)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrs
    have hw : w = w' := by
      apply (P4733T1Coordinates D).1
      have hfirst := congrArg (fun p => p.1.first) h
      have hsecond := congrArg (fun p => p.1.second) h
      cases s <;> simp only [P4733T1FacePairOrbit, Bool.false_eq_true,
        ite_false, ite_true, D.faceShift_eq] at hfirst hsecond
      all_goals exact Prod.ext (add_left_cancel hfirst) (add_left_cancel hsecond)
    subst w'
    rfl
  · intro a b hab f g hfg hfa hfb hga hgb
    obtain ⟨r, w, he⟩ := P4733T1EdgeOrbit D a b hab
    let row := P4733T1EdgeRow r
    let F := D.faceShift w row.2.1
    let G := D.faceShift w row.2.2
    let c := D.shift w row.1.1
    let d := D.shift w row.1.2
    have hr := P4733T1RowIncidence r
    have hFG : F ≠ G := fun h => hr.2.1 (face_inj w h)
    have hc : AllowedSubtileIncidence c d := (D.edge_periodic w _ _).mpr hr.1
    have memshift (h : PeriodicSubtileFaceIndex) (z : PeriodicSubtileIndex)
        (hz : ∃ i, SixSubtileFaceVertices h i = z) :
        ∃ i, SixSubtileFaceVertices (D.faceShift w h) i = D.shift w z := by
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, by rw [D.face_vertices_periodic, hi]⟩
    have hF : (∃ i, SixSubtileFaceVertices F i = c) ∧
        (∃ i, SixSubtileFaceVertices F i = d) :=
      ⟨memshift _ _ hr.2.2.1, memshift _ _ hr.2.2.2.1⟩
    have hG : (∃ i, SixSubtileFaceVertices G i = c) ∧
        (∃ i, SixSubtileFaceVertices G i = d) :=
      ⟨memshift _ _ hr.2.2.2.2.1, memshift _ _ hr.2.2.2.2.2⟩
    obtain ⟨f₀, g₀, h₀, hf₀, hg₀, unique⟩ :=
      P4677T2IncidenceLedger.2.2.2.2.2 c d hc
    have exhaust (h : PeriodicSubtileFaceIndex)
        (hh : (∃ i, SixSubtileFaceVertices h i = c) ∧
          (∃ i, SixSubtileFaceVertices h i = d)) : h = F ∨ h = G := by
      have hF' := unique F hF
      have hG' := unique G hG
      have hh' := unique h hh
      rcases hF' with hF' | hF' <;> rcases hG' with hG' | hG' <;>
        rcases hh' with hh' | hh' <;> aesop
    have hf : f = F ∨ f = G := by
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact exhaust f ⟨⟨_, hfa.choose_spec.trans ha⟩, ⟨_, hfb.choose_spec.trans hb⟩⟩
      · exact exhaust f ⟨⟨_, hfb.choose_spec.trans hb⟩, ⟨_, hfa.choose_spec.trans ha⟩⟩
    have hg : g = F ∨ g = G := by
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact exhaust g ⟨⟨_, hga.choose_spec.trans ha⟩, ⟨_, hgb.choose_spec.trans hb⟩⟩
      · exact exhaust g ⟨⟨_, hgb.choose_spec.trans hb⟩, ⟨_, hga.choose_spec.trans ha⟩⟩
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
    · exact (hfg rfl).elim
    · exact ⟨(r, w, true), rfl, he⟩
    · exact ⟨(r, w, false), rfl, he⟩
    · exact (hfg rfl).elim

end ApollonianSuperharmonic

end
