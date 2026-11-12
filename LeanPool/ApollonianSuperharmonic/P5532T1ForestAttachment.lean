/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.RootedFourNeighborForest
public import LeanPool.ApollonianSuperharmonic.P4062T1RankedAttachment

-- [TABLET NODE: P5532T1ForestAttachment]

/-!
# P5532T1ForestAttachment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1ForestAttachment (D P R : Finset GaussianInt)
    (σ : GaussianInt → ℤ) (hP : P ⊆ D)
    (o : AcyclicIndegreeOrientation P σ)
    (hf : RootedFourNeighborForest (D \ P) R)
    (hres : ∀ x ∈ D \ P,
      σ x - ((P.filter fun y => @decide (FourNeighborAdjacent y x)
        (Classical.propDecidable _)).card : ℤ) = 1 - if x ∈ R then 1 else 0) :
    ∃ t : AcyclicIndegreeOrientation D σ,
      (∀ x ∈ P, ∀ y ∈ P, t.edge x y ↔ o.edge x y) ∧
      (∀ x ∈ P, ∀ y ∈ D \ P, FourNeighborAdjacent x y → t.edge x y) ∧
      (∀ x ∈ P, t.rank x = o.rank x) ∧
      ∀ x ∈ D \ P, P.sup o.rank < t.rank x := by
-- BODY
  classical
  obtain ⟨hR, parent, d, hroot, hparent, hzero, hedge⟩ := hf
  have hstrict : ∀ x ∈ D \ P, ∀ y ∈ D \ P,
      FourNeighborAdjacent x y → d x ≠ d y := by
    intro x hx y hy ha heq
    rcases hedge x hx y hy ha with hp | hp
    · have hn : y ∉ R := by
        intro hr
        have hsame : x = y := hp.trans (hroot y hr)
        rw [hsame] at ha
        simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at ha
        omega
      have hd := (hparent y hy hn).2.2
      rw [← hp] at hd
      omega
    · have hn : x ∉ R := by
        intro hr
        have hsame : y = x := hp.trans (hroot x hr)
        rw [hsame] at ha
        simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at ha
        omega
      have hd := (hparent x hx hn).2.2
      rw [← hp] at hd
      omega
  have hcount : ∀ x ∈ D \ P,
      (((D \ P).filter fun y => FourNeighborAdjacent y x ∧ d y < d x).card : ℤ) =
        1 - if x ∈ R then 1 else 0 := by
    intro x hx
    by_cases hr : x ∈ R
    · have hd := (hzero x hx).mp hr
      simp [hd, hr]
    · have hp := hparent x hx hr
      have heq : (D \ P).filter (fun y => FourNeighborAdjacent y x ∧ d y < d x) =
          {parent x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hy, ha, hd⟩
          rcases hedge y hy x hx ha with hh | hh
          · exact hh
          · have hyr : y ∉ R := by
              intro hyr
              rw [hroot y hyr] at hh
              rw [hh] at hd
              omega
            have hh' := (hparent y hy hyr).2.2
            rw [← hh] at hh'
            omega
        · rintro rfl
          exact ⟨hp.1, hp.2⟩
      simp [heq, hr]
  have hsum : ∀ x ∈ D \ P,
      ((P.filter fun y => FourNeighborAdjacent y x).card : ℤ) +
        (((D \ P).filter fun y => FourNeighborAdjacent y x ∧ d y < d x).card : ℤ) =
          σ x := by
    intro x hx
    have hr := hres x hx
    simp only [decide_eq_true_eq] at hr
    rw [hcount x hx]
    omega
  obtain ⟨t, ht, hcross, hW, hrP, hrW⟩ :=
    P4062T1RankedAttachment D P σ d hP o (by
      intro x hx
      convert hsum x hx using 1;
        congr 3; ext y; simp only [Finset.mem_filter]) hstrict
  refine ⟨t, ht, hcross, hrP, ?_⟩
  intro x hx
  rw [hrW x hx]
  omega

end ApollonianSuperharmonic

end
