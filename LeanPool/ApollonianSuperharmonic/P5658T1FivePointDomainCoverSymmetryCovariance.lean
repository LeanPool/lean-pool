/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction

-- [TABLET NODE: P5658T1FivePointDomainCoverSymmetryCovariance]

/-!
# P5658T1FivePointDomainCoverSymmetryCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5658T1FivePointDomainCoverSymmetryCovariance
    (g : BandPackingSymmetry) (h k : PartialOdometer) (x : GaussianInt)
    (hstar : ∀ y,
      y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h.domain ∨ y ∈ k.domain) :
    ∀ y,
      y = BandPackingSymmetryVectorAction g x ∨
      y = BandPackingSymmetryVectorAction g x + 1 ∨
      y = BandPackingSymmetryVectorAction g x - 1 ∨
      y = BandPackingSymmetryVectorAction g x + ⟨0, 1⟩ ∨
      y = BandPackingSymmetryVectorAction g x - ⟨0, 1⟩ →
      y ∈ (BandPackingSymmetryPartialOdometerAction g h).domain ∨
        y ∈ (BandPackingSymmetryPartialOdometerAction g k).domain := by
-- BODY
  let hbar := BandPackingSymmetryPartialOdometerAction g h
  let kbar := BandPackingSymmetryPartialOdometerAction g k
  let xbar := BandPackingSymmetryVectorAction g x
  let Axial : GaussianInt → Prop := fun d =>
    d = 0 ∨ d = 1 ∨ d = -1 ∨
      d = ⟨0, 1⟩ ∨ d = -⟨0, 1⟩
  have vector_add : ∀ (a : BandPackingSymmetry) (u v : GaussianInt),
      BandPackingSymmetryVectorAction a (u + v) =
        BandPackingSymmetryVectorAction a u +
          BandPackingSymmetryVectorAction a v := by
    intro a
    induction a with
    | identity => intro u v; rfl
    | shift w => intro u v; rfl
    | negate =>
        intro u v
        rcases u with ⟨ur, ui⟩
        rcases v with ⟨vr, vi⟩
        apply Zsqrtd.ext_iff.mpr
        constructor <;> simp [BandPackingSymmetryVectorAction,
          GaussianQuarterTurn]; ring
    | conjugate =>
        intro u v
        rcases u with ⟨ur, ui⟩
        rcases v with ⟨vr, vi⟩
        apply Zsqrtd.ext_iff.mpr
        constructor <;> simp [BandPackingSymmetryVectorAction,
          GaussianReflection]; ring
    | comp a b iha ihb =>
        intro u v
        simp only [BandPackingSymmetryVectorAction]
        rw [ihb, iha]
  have axial_preimage : ∀ (a : BandPackingSymmetry) (d : GaussianInt),
      Axial d → ∃ d₀, Axial d₀ ∧
        BandPackingSymmetryVectorAction a d₀ = d := by
    intro a
    induction a with
    | identity =>
        intro d hd
        exact ⟨d, hd, rfl⟩
    | shift w =>
        intro d hd
        exact ⟨d, hd, rfl⟩
    | negate =>
        intro d hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, Or.inl rfl, by rfl⟩
        · exact ⟨-⟨0, 1⟩, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianQuarterTurn]⟩
        · exact ⟨⟨0, 1⟩, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianQuarterTurn]⟩
        · exact ⟨1, Or.inr (Or.inl rfl), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianQuarterTurn]⟩
        · exact ⟨-1, Or.inr (Or.inr (Or.inl rfl)), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianQuarterTurn]⟩
    | conjugate =>
        intro d hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, Or.inl rfl, by rfl⟩
        · exact ⟨-1, Or.inr (Or.inr (Or.inl rfl)), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianReflection]⟩
        · exact ⟨1, Or.inr (Or.inl rfl), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianReflection]⟩
        · exact ⟨⟨0, 1⟩, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianReflection]⟩
        · exact ⟨-⟨0, 1⟩, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by
            ext <;> norm_num [BandPackingSymmetryVectorAction,
              GaussianReflection]⟩
    | comp a b iha ihb =>
        intro d hd
        obtain ⟨d₁, hd₁, ha⟩ := iha d hd
        obtain ⟨d₀, hd₀, hb⟩ := ihb d₁ hd₁
        refine ⟨d₀, hd₀, ?_⟩
        simp only [BandPackingSymmetryVectorAction, hb, ha]
  have action_domain_mem (a : BandPackingSymmetry) (f : PartialOdometer)
      (z : GaussianInt) (hz : z ∈ f.domain) :
      BandPackingSymmetryVectorAction a z ∈
        (BandPackingSymmetryPartialOdometerAction a f).domain := by
    have hd := (BandPackingSymmetryPartialOdometerActionFormulas a f f).1
    have hzset : BandPackingSymmetryVectorAction a z ∈
        ((BandPackingSymmetryPartialOdometerAction a f).domain :
          Set GaussianInt) := by
      rw [hd]
      exact ⟨z, hz, rfl⟩
    exact hzset
  have hstarBarDomain : ∀ y,
      y = xbar ∨ y = xbar + 1 ∨ y = xbar - 1 ∨
        y = xbar + ⟨0, 1⟩ ∨ y = xbar - ⟨0, 1⟩ →
      y ∈ hbar.domain ∨ y ∈ kbar.domain := by
    intro y hy
    have hdelta : ∃ d, Axial d ∧ y = xbar + d := by
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, Or.inl rfl, by simp⟩
      · exact ⟨1, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨-1, Or.inr (Or.inr (Or.inl rfl)), by ring⟩
      · exact ⟨⟨0, 1⟩, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
      · exact ⟨-⟨0, 1⟩, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by ring⟩
    obtain ⟨d, hd, rfl⟩ := hdelta
    obtain ⟨d₀, hd₀, hgd⟩ := axial_preimage g d hd
    have hsource : x + d₀ ∈ h.domain ∨ x + d₀ ∈ k.domain := by
      apply hstar (x + d₀)
      rcases hd₀ with rfl | rfl | rfl | rfl | rfl
      · left; simp
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl (by ring)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by ring))))
    have hsum := vector_add g x d₀
    rcases hsource with hh | hk
    · left
      change BandPackingSymmetryVectorAction g x + d ∈
        (BandPackingSymmetryPartialOdometerAction g h).domain
      rw [← hgd, ← hsum]
      exact action_domain_mem g h (x + d₀) hh
    · right
      change BandPackingSymmetryVectorAction g x + d ∈
        (BandPackingSymmetryPartialOdometerAction g k).domain
      rw [← hgd, ← hsum]
      exact action_domain_mem g k (x + d₀) hk
  exact hstarBarDomain

end ApollonianSuperharmonic

end
