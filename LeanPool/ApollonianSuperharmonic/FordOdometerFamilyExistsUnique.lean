/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParentsExist
public import LeanPool.ApollonianSuperharmonic.P5130T5DomainCover
public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.P5130T5MixedOverlaps
public import LeanPool.ApollonianSuperharmonic.P5130T5SameParentOverlaps
public import LeanPool.ApollonianSuperharmonic.P5130T5BoundaryConsistency
public import LeanPool.ApollonianSuperharmonic.P5130T5PeriodicExtension
public import LeanPool.ApollonianSuperharmonic.P5130T5UnitCase

-- [TABLET NODE: FordOdometerFamilyExistsUnique]

/-!
# FordOdometerFamilyExistsUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordOdometerFamilyExistsUnique :
    ∃! G : FordFareyParameter -> IntegerLatticeFunction,
      (∀ P x, P.q = 1 ->
        G P x = x.re * (x.re - 1) / 2 + P.p * x.re * x.im) ∧
      (∀ P x, x ∈ FordDoubledBoundary P.q ->
        G P x = IntegerCeilDiv (P.p * x.re * x.im) P.q
          (by exact_mod_cast P.q_pos.ne')) ∧
      (∀ P x, G P (x + ⟨0, -(P.q : Int)⟩) =
        G P x - P.p * x.re) ∧
      (∀ P x, G P (x + ⟨(P.q : Int), (P.q₁ : Int)⟩) =
        G P x + P.p₁ * x.re + P.p * x.im + (P.q₁ : Int) * P.p) ∧
      (∀ P x, G P (x + ⟨-(P.q : Int), (P.q₂ : Int)⟩) =
        G P x + P.p₂ * x.re - P.p * x.im - (P.q : Int) * P.p₂) ∧
      (∀ P P₁ P₂, 1 < P.q ->
        P₁.p = P.p₁ -> P₁.q = P.q₁ -> P₂.p = P.p₂ -> P₂.q = P.q₂ ->
        (∀ x, x ∈ FordRecursiveVertexDomains P 0 -> G P x = G P₁ x) ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 1 ->
          G P x = G P₁ (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
            P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1) ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 2 ->
          G P x = G P₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im) ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 3 ->
          G P x = G P₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re)) := by
-- BODY
  classical
  let S (P : FordFareyParameter) (K : FordFareyParameter → IntegerLatticeFunction)
      (g : IntegerLatticeFunction) : Prop :=
    (∀ x, P.q = 1 → g x = x.re * (x.re - 1) / 2 + P.p * x.re * x.im) ∧
    (∀ x ∈ FordDoubledBoundary P.q,
      g x = IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne')) ∧
    (∀ x, g (x + ⟨0, -(P.q : Int)⟩) = g x - P.p * x.re) ∧
    (∀ x, g (x + ⟨(P.q : Int), (P.q₁ : Int)⟩) =
      g x + P.p₁ * x.re + P.p * x.im + (P.q₁ : Int) * P.p) ∧
    (∀ x, g (x + ⟨-(P.q : Int), (P.q₂ : Int)⟩) =
      g x + P.p₂ * x.re - P.p * x.im - (P.q : Int) * P.p₂) ∧
    (∀ A B, 1 < P.q → A.p = P.p₁ → A.q = P.q₁ → B.p = P.p₂ → B.q = P.q₂ →
      ∀ i x, x ∈ FordRecursiveVertexDomains P i →
        g x = P5130T5Prescription P (K A) (K B) i x)
  have param_eq (A B : FordFareyParameter) (hp : A.p = B.p) (hq : A.q = B.q) : A = B := by
    obtain ⟨R, _, hu⟩ := FordFareyParentsExist A.p A.q A.q_pos A.reduced
    exact (hu A ⟨rfl, rfl⟩).trans (hu B ⟨hp.symm, hq.symm⟩).symm
  have congrS (P : FordFareyParameter) (K H : FordFareyParameter → IntegerLatticeFunction)
      (g : IntegerLatticeFunction) (heq : ∀ Q, Q.q < P.q → K Q = H Q)
      (h : S P K g) : S P H g := by
    rcases h with ⟨hu, hb, ha, hbb, hc, hr⟩
    refine ⟨hu, hb, ha, hbb, hc, ?_⟩
    intro A B hq hpA hqA hpB hqB i x hx
    have hbds := P5130T5ParentArithmetic P hq
    rw [← heq A (by omega), ← heq B (by omega)]
    exact hr A B hq hpA hqA hpB hqB i x hx
  have make (P : FordFareyParameter) (K : FordFareyParameter → IntegerLatticeFunction)
      (ih : ∀ Q, Q.q < P.q → S Q K (K Q)) : ∃ g, S P K g := by
    by_cases hunit : P.q = 1
    · obtain ⟨hb, ha, hbb, hc⟩ := P5130T5UnitCase P hunit
      refine ⟨(fun x => x.re * (x.re - 1) / 2 + P.p * x.re * x.im),
        (by intros; rfl), hb, ha, hbb, hc, ?_⟩
      intro A B hq
      omega
    have hq : 1 < P.q := by have := P.q_pos; omega
    obtain ⟨haPos, haLt, hbPos, hbLt, haRed, hbRed, _⟩ := P5130T5ParentArithmetic P hq
    obtain ⟨A, hA, _⟩ := FordFareyParentsExist P.p₁ P.q₁ haPos haRed
    obtain ⟨B, hB, _⟩ := FordFareyParentsExist P.p₂ P.q₂ hbPos hbRed
    have haLt' : A.q < P.q := by omega
    have hbLt' : B.q < P.q := by omega
    have hAB := (ih A haLt').2.1
    have hBB := (ih B hbLt').2.1
    have hm := P5130T5MixedOverlaps P A B hq hA.1 hA.2 hB.1 hB.2 (K A) (K B) hAB hBB
    have hs := P5130T5SameParentOverlaps P A B hq hA.1 hA.2 hB.1 hB.2 K
      (fun Q hQ => (ih Q hQ).2.1)
      (fun Q C D hQ => (ih Q hQ).2.2.2.2.2 C D)
    have hbc := P5130T5BoundaryConsistency P A B hq hA.1 hA.2 hB.1 hB.2
      (K A) (K B) hAB hBB
    let F := P5130T5Prescription P (K A) (K B)
    have pair : ∀ i j x, x ∈ FordRecursiveVertexDomains P i →
        x ∈ FordRecursiveVertexDomains P j → F i x = F j x := by
      intro i j x hi hj
      fin_cases i <;> fin_cases j
      · rfl
      · exact hs.1 x hi hj
      · exact hm.1 x hi hj
      · exact hm.2.1 x hi hj
      · exact (hs.1 x hj hi).symm
      · rfl
      · exact hm.2.2.1 x hi hj
      · exact hm.2.2.2 x hi hj
      · exact (hm.1 x hj hi).symm
      · exact (hm.2.2.1 x hj hi).symm
      · rfl
      · exact hs.2 x hi hj
      · exact (hm.2.1 x hj hi).symm
      · exact (hm.2.2.2 x hj hi).symm
      · exact (hs.2 x hj hi).symm
      · rfl
    let pick (x : GaussianInt) (hx : x ∈ FordVertexDomain P.q) : Fin 4 :=
      Classical.choose ((P5130T5DomainCover P).1 x hx)
    have hpick (x : GaussianInt) (hx : x ∈ FordVertexDomain P.q) :
        x ∈ FordRecursiveVertexDomains P (pick x hx) :=
      Classical.choose_spec ((P5130T5DomainCover P).1 x hx)
    let f : IntegerLatticeFunction := fun x =>
      if hx : x ∈ FordVertexDomain P.q then F (pick x hx) x else 0
    have hf (i : Fin 4) (x : GaussianInt) (hx : x ∈ FordRecursiveVertexDomains P i) :
        f x = F i x := by
      have hsq := (P5130T5DomainCover P).2 i x hx
      dsimp only [f]
      rw [dite_eq_left hsq]
      exact pair _ i x (hpick x hsq) hx
    have hfB : ∀ x ∈ FordDoubledBoundary P.q,
        f x = IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne') := by
      intro x hx
      dsimp only [f]
      rw [dite_eq_left hx.1]
      exact hbc _ x (hpick x hx.1) hx
    obtain ⟨g, hg, _⟩ := P5130T5PeriodicExtension P f hfB
    refine ⟨g, ?_, ?_, hg.2.1, hg.2.2.1, hg.2.2.2, ?_⟩
    · intro x hx
      exact (hunit hx).elim
    · intro x hx
      exact (hg.1 x hx.1).trans (hfB x hx)
    · intro A' B' _ hpA hqA hpB hqB i x hx
      have eA : A' = A := param_eq A' A (hpA.trans hA.1.symm) (hqA.trans hA.2.symm)
      have eB : B' = B := param_eq B' B (hpB.trans hB.1.symm) (hqB.trans hB.2.symm)
      subst A'
      subst B'
      exact (hg.1 x ((P5130T5DomainCover P).2 i x hx)).trans (hf i x hx)
  have unique (P : FordFareyParameter) (K : FordFareyParameter → IntegerLatticeFunction)
      (g h : IntegerLatticeFunction) (hg : S P K g) (hh : S P K h) : g = h := by
    by_cases hunit : P.q = 1
    · funext x
      exact (hg.1 x hunit).trans (hh.1 x hunit).symm
    have hq : 1 < P.q := by have := P.q_pos; omega
    obtain ⟨haPos, _, hbPos, _, haRed, hbRed, _⟩ := P5130T5ParentArithmetic P hq
    obtain ⟨A, hA, _⟩ := FordFareyParentsExist P.p₁ P.q₁ haPos haRed
    obtain ⟨B, hB, _⟩ := FordFareyParentsExist P.p₂ P.q₂ hbPos hbRed
    have agree : ∀ x ∈ FordVertexDomain P.q, g x = h x := by
      intro x hx
      obtain ⟨i, hi⟩ := (P5130T5DomainCover P).1 x hx
      exact (hg.2.2.2.2.2 A B hq hA.1 hA.2 hB.1 hB.2 i x hi).trans
        (hh.2.2.2.2.2 A B hq hA.1 hA.2 hB.1 hB.2 i x hi).symm
    obtain ⟨e, _, he⟩ := P5130T5PeriodicExtension P h hh.2.1
    exact (he g ⟨agree, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1⟩).trans
      (he h ⟨(by intros; rfl), hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩).symm
  let wf := (measure (fun P : FordFareyParameter => P.q)).wf
  let step (P : FordFareyParameter)
      (rec : ∀ Q : FordFareyParameter, Q.q < P.q → IntegerLatticeFunction) :
      IntegerLatticeFunction :=
    Classical.epsilon (S P (fun Q => if h : Q.q < P.q then rec Q h else fun _ => 0))
  let G : FordFareyParameter → IntegerLatticeFunction := wf.fix step
  have hG : ∀ P, S P G (G P) := by
    intro P₀
    apply wf.induction P₀
    intro P ih
    let H : FordFareyParameter → IntegerLatticeFunction :=
      fun Q => if h : Q.q < P.q then G Q else fun _ => 0
    have eqH (Q : FordFareyParameter) (hQ : Q.q < P.q) : H Q = G Q := by
      simp only [H, dite_eq_left hQ]
    have small : ∀ Q, Q.q < P.q → S Q H (H Q) := by
      intro Q hQ
      rw [eqH Q hQ]
      exact congrS Q G H (G Q) (fun R hR => (eqH R (lt_trans hR hQ)).symm) (ih Q hQ)
    have hex := make P H small
    have heps := congrS P H G (Classical.epsilon (S P H)) eqH (Classical.epsilon_spec hex)
    have hfix : G P = Classical.epsilon (S P H) := wf.fix_eq step P
    rw [hfix]
    exact heps
  refine ⟨G, ?_, ?_⟩
  · refine ⟨(fun P x h => (hG P).1 x h), (fun P => (hG P).2.1),
      (fun P => (hG P).2.2.1), (fun P => (hG P).2.2.2.1),
      (fun P => (hG P).2.2.2.2.1), ?_⟩
    intro P A B hq hpA hqA hpB hqB
    have hr := (hG P).2.2.2.2.2 A B hq hpA hqA hpB hqB
    exact ⟨hr 0, hr 1, hr 2, hr 3⟩
  · intro K hK
    have HK : ∀ P, S P K (K P) := by
      intro P
      refine ⟨(fun x h => hK.1 P x h), hK.2.1 P, hK.2.2.1 P,
        hK.2.2.2.1 P, hK.2.2.2.2.1 P, ?_⟩
      intro A B hq hpA hqA hpB hqB i x hx
      have hr := hK.2.2.2.2.2 P A B hq hpA hqA hpB hqB
      fin_cases i
      · exact hr.1 x hx
      · exact hr.2.1 x hx
      · exact hr.2.2.1 x hx
      · exact hr.2.2.2 x hx
    have eq : ∀ P, K P = G P := by
      intro P₀
      apply wf.induction P₀
      intro P ih
      exact unique P G (K P) (G P) (congrS P K G (K P) ih (HK P)) (hG P)
    exact funext eq

end ApollonianSuperharmonic

end
