/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Algebra.BigOperators.Fin

-- [TABLET NODE: P4194T1DiamondBoundaryLedger]

/-!
# P4194T1DiamondBoundaryLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondBoundaryProof

/-- Classical decidability of membership in a tile's boundary vertices. -/
@[instance_reducible] noncomputable def boundaryVertexDecidability
    (T : ProtoTile) (z : GaussianInt) : Decidable (z ∈ BoundaryFootprintVertices T) := by
  classical
  infer_instance

attribute [local instance] boundaryVertexDecidability

private theorem hrow :
    ∀ (m : Nat), ∀ (z : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈
        DiamondCellDomain m) → ((1 : ℤ) ≤ z.im ∧
  z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧
    -(z.im - (1 : ℤ)) ≤ z.re ∧
      z.re ≤ z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) *
          (↑m : ℤ) - z.im - (1 : ℤ)) := by
  classical
  intro m z hz
  exact (P4194T1DiamondCellRows m z).2.mp hz

private theorem hdesclow :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → ((b < m) → (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈
        DiamondCellDomain (m - 1)))) := by
  classical
  intro m hm z b hrow hb
  apply (P4194T1DiamondCellRows (m - 1) z).2.mpr
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

private theorem hdeschi :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → (((m : Int) < b) → (∀ j : Fin 4,
        LatticeVertexIncidentCell z j ∈
          (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells))) := by
  classical
  intro m hm z b hrow hb
  let w := z - ⟨0, 2⟩
  have hwrow := (P4194T1DiamondCellRows (m - 1) w).2
  have hw : ∀ j : Fin 4, LatticeVertexIncidentCell w j ∈
      DiamondCellDomain (m - 1) := by
    apply hwrow.mpr
    rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
    dsimp [w]
    simp []
    omega
  have hu := (TileTranslationFormulas (DiamondTile (m - 1)) ⟨0, 2⟩).1
  intro j
  rw [hu]
  apply Finset.mem_image.mpr
  refine ⟨LatticeVertexIncidentCell w j, hw j, ?_⟩
  fin_cases j <;>
    simp [GaussianTranslation, LatticeVertexIncidentCell, w,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private theorem hloFourAtMid :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → ((b = m) → ((∀ j : Fin 4, LatticeVertexIncidentCell z j ∈
        DiamondCellDomain (m - 1)) ↔
        -(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3))) := by
  classical
  intro m hm z a b hrow hmid
  rw [(P4194T1DiamondCellRows (m - 1) z).2]
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  omega

private theorem hsomeLoMid :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → ((b = m) → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈
        DiamondCellDomain (m - 1)))) := by
  classical
  intro m hm z b hrow hmid
  let a := z.re
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  by_cases ha : a ≤ (m : Int) - 2
  · refine ⟨3, ?_⟩
    have heq : LatticeVertexIncidentCell z 3 = z - ⟨0, 1⟩ := by
      simp [LatticeVertexIncidentCell]
    rw [heq]
    apply (P4194T1DiamondCellRows (m - 1) (z - ⟨0, 1⟩)).1.mpr
    simp []
    omega
  · refine ⟨2, ?_⟩
    have heq : LatticeVertexIncidentCell z 2 = z - 1 - ⟨0, 1⟩ := by
      simp [LatticeVertexIncidentCell]
    rw [heq]
    apply (P4194T1DiamondCellRows (m - 1) (z - 1 - ⟨0, 1⟩)).1.mpr
    simp []
    omega

private theorem hsomeHiMid :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → ((b = m) → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells))) := by
  classical
  intro m hm z b hrow hmid
  let a := z.re
  let w := z - ⟨0, 2⟩
  have hu := (TileTranslationFormulas (DiamondTile (m - 1)) ⟨0, 2⟩).1
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  by_cases ha : a ≤ (m : Int) - 2
  · have hc : w ∈ DiamondCellDomain (m - 1) := by
      apply (P4194T1DiamondCellRows (m - 1) w).1.mpr
      simp [w]
      omega
    refine ⟨0, ?_⟩
    rw [hu]
    refine Finset.mem_image.mpr ⟨w, hc, ?_⟩
    simp [GaussianTranslation, LatticeVertexIncidentCell, w]
  · have hc : w - 1 ∈ DiamondCellDomain (m - 1) := by
      apply (P4194T1DiamondCellRows (m - 1) (w - 1)).1.mpr
      simp [w]
      omega
    refine ⟨1, ?_⟩
    rw [hu]
    refine Finset.mem_image.mpr ⟨w - 1, hc, ?_⟩
    simp [GaussianTranslation, LatticeVertexIncidentCell, w,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private theorem hhiFourAtMid :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → ((b = m) → ((∀ j : Fin 4, LatticeVertexIncidentCell (z - ⟨0, 2⟩) j ∈
        DiamondCellDomain (m - 1)) ↔
        -(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3))) := by
  classical
  intro m hm z a b hrow hmid
  let w := z - ⟨0, 2⟩
  rw [(P4194T1DiamondCellRows (m - 1) w).2]
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  simp [w]
  omega

private theorem translationBoundary :
    ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt), GaussianTranslation u x ∈
        BoundaryFootprintVertices (TileTranslation T u) ↔
        x ∈ BoundaryFootprintVertices T := by
  classical
  intro T u x
  rcases TileTranslationFormulas T u with ⟨_, _, _, _, _, _, _, hbound, _⟩
  rw [hbound]
  simp [GaussianTranslation]

private theorem translationCell :
    ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt), ∀ (j : Fin 4),
        LatticeVertexIncidentCell (GaussianTranslation u x) j ∈
          (TileTranslation T u).cells ↔
        LatticeVertexIncidentCell x j ∈ T.cells := by
  classical
  intro T u x j
  have hcalc : LatticeVertexIncidentCell (GaussianTranslation u x) j =
      GaussianTranslation u (LatticeVertexIncidentCell x j) := by
    fin_cases j <;>
      simp [GaussianTranslation, LatticeVertexIncidentCell,
        sub_eq_add_neg, add_assoc, add_comm]
  rw [(TileTranslationFormulas T u).1, hcalc]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have heq' : y = LatticeVertexIncidentCell x j := by
      have hh := congrArg (fun q : GaussianInt => q - u)
        (by simpa [GaussianTranslation] using heq)
      simpa using hh
    simpa [heq'] using hy
  · intro hy
    exact ⟨LatticeVertexIncidentCell x j, hy, rfl⟩

private theorem boundaryIffMissing :
    ∀ (n : Nat), (0 < n) → (∀ (x : GaussianInt), (∃ j : Fin 4,
        LatticeVertexIncidentCell x j ∈ DiamondCellDomain n) → (x ∈ BoundaryFootprintVertices
            (DiamondTile n) ↔
        ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ DiamondCellDomain n)) := by
  classical
  intro n hn x hsome
  rw [(P4194T1DiamondVertexIncidence n hn x).2]
  exact ⟨fun h => h.2, fun h => ⟨hsome, h⟩⟩

private theorem hpredFalseMid :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((b = m) → ((∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1)) ↔ -(m :
        Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3)) → (((b = m) → (∃ j : Fin 4, LatticeVertexIncidentCell
        z j ∈ DiamondCellDomain (m - 1))) → ((∀ (n : Nat), (0 < n) → (∀ (x : GaussianInt), (∃ j :
        Fin 4, LatticeVertexIncidentCell x j ∈ DiamondCellDomain n) → (x ∈
        BoundaryFootprintVertices (DiamondTile n) ↔ ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉
        DiamondCellDomain n))) → ((b = m) → (z ∈ BoundaryFootprintVertices (DiamondTile (m - 1)) ↔
        ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3)))))) := by
  classical
  intro m hm z a b hloFourAtMid hsomeLoMid boundaryIffMissing hmid
  have hn : 0 < m - 1 := by omega
  rw [boundaryIffMissing (m - 1) hn z (hsomeLoMid hmid)]
  rw [← not_forall]
  rw [hloFourAtMid hmid]

private theorem hpredTrueMid :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((b = m) → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ (TileTranslation (DiamondTile (m -
        1)) ⟨0, 2⟩).cells)) → (((b = m) → ((∀ j : Fin 4, LatticeVertexIncidentCell (z - ⟨0, 2⟩) j
        ∈ DiamondCellDomain (m - 1)) ↔ -(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3)) → ((∀ (T :
        ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt), GaussianTranslation u x ∈
        BoundaryFootprintVertices (TileTranslation T u) ↔ x ∈ BoundaryFootprintVertices T) → ((∀
        (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x : GaussianInt), ∀ (j : Fin 4),
        LatticeVertexIncidentCell (GaussianTranslation u x) j ∈ (TileTranslation T u).cells ↔
        LatticeVertexIncidentCell x j ∈ T.cells) → ((∀ (n : Nat), (0 < n) → (∀ (x : GaussianInt),
        (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ DiamondCellDomain n) → (x ∈
        BoundaryFootprintVertices (DiamondTile n) ↔ ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉
        DiamondCellDomain n))) → ((b = m) → (z ∈ BoundaryFootprintVertices
          (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) ↔
        ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3)))))))) := by
  classical
  intro m hm z a b hsomeHiMid hhiFourAtMid translationBoundary translationCell boundaryIffMissing
      hmid
  let w := z - ⟨0, 2⟩
  have hshift : GaussianTranslation ⟨0, 2⟩ w = z := by
    simp [GaussianTranslation, w]
  have hsomeW : ∃ j : Fin 4, LatticeVertexIncidentCell w j ∈
      DiamondCellDomain (m - 1) := by
    rcases hsomeHiMid hmid with ⟨j, hj⟩
    have hj' : LatticeVertexIncidentCell
        (GaussianTranslation ⟨0, 2⟩ w) j ∈
          (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells := by
      simpa [hshift] using hj
    exact ⟨j, (translationCell (DiamondTile (m - 1)) ⟨0, 2⟩ w j).mp hj'⟩
  have hmissCore : (∃ j : Fin 4,
      LatticeVertexIncidentCell w j ∉ DiamondCellDomain (m - 1)) ↔
      ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) := by
    rw [← not_forall]
    rw [hhiFourAtMid hmid]
  rw [← hshift, translationBoundary (DiamondTile (m - 1)) ⟨0, 2⟩ w]
  rw [boundaryIffMissing (m - 1) (by omega) w hsomeW, hmissCore]

private theorem unitBoundary :
    ∀ (c : GaussianInt),
      ∀ (x : GaussianInt),
        x ∈ BoundaryFootprintVertices (⟨{ c }, c⟩ : ProtoTile) ↔
          x = c ∨ x = c + 1 ∨ x = c + ⟨0, 1⟩ ∨ x = c + 1 + ⟨0, 1⟩ := by
  classical
  intro c x
  classical
  have ht : ({c} : Finset GaussianInt).Nonempty := ⟨c, by simp⟩
  have hmissI : c - ⟨0, 1⟩ ∉ ({c} : Finset GaussianInt) := by
    simp only [Finset.mem_singleton]
    intro he
    have him := congrArg Zsqrtd.im he
    simp at him
  have hmissR : c - 1 ∉ ({c} : Finset GaussianInt) := by
    simp only [Finset.mem_singleton]
    intro he
    have hre := congrArg Zsqrtd.re he
    simp at hre
  have hbottom : x = c ∨ x = c + 1 →
      x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) := by
    intro hx
    rcases hx with hx | hx
    · rw [hx]
      simp only [BoundaryFootprintVertices, ite_eq_left ht, Set.mem_ofPred_eq]
      refine ⟨{c, c + 1}, ?_, by simp⟩
      exact ⟨c, Or.inl ⟨rfl, Or.inl ⟨by simp, hmissI⟩⟩⟩
    · rw [hx]
      simp only [BoundaryFootprintVertices, ite_eq_left ht, Set.mem_ofPred_eq]
      refine ⟨{c, c + 1}, ?_, by simp⟩
      exact ⟨c, Or.inl ⟨rfl, Or.inl ⟨by simp, hmissI⟩⟩⟩
  have hleft : x = c + ⟨0, 1⟩ →
      x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) := by
    intro hx
    rw [hx]
    simp only [BoundaryFootprintVertices, ite_eq_left ht, Set.mem_ofPred_eq]
    refine ⟨{c, c + ⟨0, 1⟩}, ?_, by simp⟩
    exact ⟨c, Or.inr ⟨rfl, Or.inl ⟨by simp, hmissR⟩⟩⟩
  have htop : x = c + 1 + ⟨0, 1⟩ →
      x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) := by
    intro hx
    rw [hx]
    simp only [BoundaryFootprintVertices, ite_eq_left ht, Set.mem_ofPred_eq]
    refine ⟨{c + ⟨0, 1⟩, c + ⟨0, 1⟩ + 1}, ?_, ?_⟩
    · simp only [BoundaryFootprintEdges, Set.mem_ofPred_eq]
      refine ⟨c + ⟨0, 1⟩, Or.inl ⟨rfl, Or.inr ⟨?_, ?_⟩⟩⟩
      · simp [Zsqrtd.ext_iff]
      · simp [sub_eq_add_neg, add_assoc]
    · simp [add_assoc, add_comm, add_left_comm]
  constructor
  · intro hx
    simp only [BoundaryFootprintVertices, Finset.singleton_nonempty, ↓reduceIte,
        BoundaryFootprintEdges, Finset.mem_singleton, Zsqrtd.ext_iff, Int.reduceNeg,
        sub_eq_add_neg, Zsqrtd.re_add, Zsqrtd.re_neg, neg_zero, add_zero, Zsqrtd.im_add,
        Zsqrtd.im_neg, not_and, Zsqrtd.re_one, Zsqrtd.im_one, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨e, ⟨w, hEdge⟩, hv⟩
    rcases hEdge with ⟨he, hc⟩ | ⟨he, hc⟩
    · subst e
      cases w with
      | mk wr wi =>
          simp_all [Finset.mem_insert, Finset.mem_singleton,
            Zsqrtd.ext_iff, sub_eq_add_neg, add_assoc, add_comm]
          omega
    · subst e
      cases w with
      | mk wr wi =>
          simp_all [Finset.mem_insert, Finset.mem_singleton,
            Zsqrtd.ext_iff, sub_eq_add_neg, add_assoc, add_comm]
          omega
  · rintro (hx | hx | hx | hx)
    · exact hbottom (Or.inl hx)
    · exact hbottom (Or.inr hx)
    · exact hleft hx
    · exact htop hx

private theorem hunit00 :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), (C 0 true = ⟨{⟨-(m : Int), (m : Int) - 1⟩},
        ⟨-(m : Int), (m : Int) - 1⟩⟩) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    (∀ (c : GaussianInt), ∀ (x : GaussianInt), x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ :
        ProtoTile) ↔ x = c ∨ x = c + 1 ∨ x = c + ⟨0, 1⟩ ∨ x = c + 1 + ⟨0, 1⟩) → (z ∈
        BoundaryFootprintVertices (C 0 true) ↔
      (a = -(m : Int) ∧ b = (m : Int) - 1) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int) - 1) ∨
      (a = -(m : Int) ∧ b = (m : Int)) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int)))) := by
  classical
  intro m C h00 z a b unitBoundary
  rw [h00, unitBoundary]
  simp [Zsqrtd.ext_iff, Zsqrtd.add_def, a, b]

private theorem hunit01 :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), (C 0 false = ⟨{⟨(m : Int) - 1, (m : Int)⟩},
        ⟨(m : Int) - 1, (m : Int)⟩⟩) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    (∀ (c : GaussianInt), ∀ (x : GaussianInt), x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ :
        ProtoTile) ↔ x = c ∨ x = c + 1 ∨ x = c + ⟨0, 1⟩ ∨ x = c + 1 + ⟨0, 1⟩) → (z ∈
        BoundaryFootprintVertices (C 0 false) ↔
      (a = (m : Int) - 1 ∧ b = (m : Int)) ∨
      (a = (m : Int) ∧ b = (m : Int)) ∨
      (a = (m : Int) - 1 ∧ b = (m : Int) + 1) ∨
      (a = (m : Int) ∧ b = (m : Int) + 1))) := by
  classical
  intro m C h01 z a b unitBoundary
  rw [h01, unitBoundary]
  simp [Zsqrtd.ext_iff, Zsqrtd.add_def, a, b]

private theorem hunit10 :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), (C 1 true = ⟨{⟨(m : Int) - 1, (m : Int) - 1⟩},
        ⟨(m : Int) - 1, (m : Int) - 1⟩⟩) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    (∀ (c : GaussianInt), ∀ (x : GaussianInt), x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ :
        ProtoTile) ↔ x = c ∨ x = c + 1 ∨ x = c + ⟨0, 1⟩ ∨ x = c + 1 + ⟨0, 1⟩) → (z ∈
        BoundaryFootprintVertices (C 1 true) ↔
      (a = (m : Int) - 1 ∧ b = (m : Int) - 1) ∨
      (a = (m : Int) ∧ b = (m : Int) - 1) ∨
      (a = (m : Int) - 1 ∧ b = (m : Int)) ∨
      (a = (m : Int) ∧ b = (m : Int)))) := by
  classical
  intro m C h10 z a b unitBoundary
  rw [h10, unitBoundary]
  simp [Zsqrtd.ext_iff, Zsqrtd.add_def, a, b]

private theorem hunit11 :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), (C 1 false = ⟨{⟨-(m : Int), (m : Int)⟩}, ⟨-(m
        : Int), (m : Int)⟩⟩) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    (∀ (c : GaussianInt), ∀ (x : GaussianInt), x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ :
        ProtoTile) ↔ x = c ∨ x = c + 1 ∨ x = c + ⟨0, 1⟩ ∨ x = c + 1 + ⟨0, 1⟩) → (z ∈
        BoundaryFootprintVertices (C 1 false) ↔
      (a = -(m : Int) ∧ b = (m : Int)) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int)) ∨
      (a = -(m : Int) ∧ b = (m : Int) + 1) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int) + 1))) := by
  classical
  intro m C h11 z a b unitBoundary
  rw [h11, unitBoundary]
  simp [Zsqrtd.ext_iff, Zsqrtd.add_def, a, b]

private theorem hunitOff :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → ((z ∈ BoundaryFootprintVertices (C 0 true) ↔ (a = -(m : Int) ∧ b =
        (m : Int) - 1) ∨ (a = -(m : Int) + 1 ∧ b = (m : Int) - 1) ∨ (a = -(m : Int) ∧ b = (m :
        Int)) ∨ (a = -(m : Int) + 1 ∧ b = (m : Int))) → ((z ∈ BoundaryFootprintVertices (C 0
        false) ↔ (a = (m : Int) - 1 ∧ b = (m : Int)) ∨ (a = (m : Int) ∧ b = (m : Int)) ∨ (a = (m
        : Int) - 1 ∧ b = (m : Int) + 1) ∨ (a = (m : Int) ∧ b = (m : Int) + 1)) → ((z ∈
        BoundaryFootprintVertices (C 1 true) ↔ (a = (m : Int) - 1 ∧ b = (m : Int) - 1) ∨ (a = (m
        : Int) ∧ b = (m : Int) - 1) ∨ (a = (m : Int) - 1 ∧ b = (m : Int)) ∨ (a = (m : Int) ∧ b =
        (m : Int))) → ((z ∈ BoundaryFootprintVertices (C 1 false) ↔ (a = -(m : Int) ∧ b = (m :
        Int)) ∨ (a = -(m : Int) + 1 ∧ b = (m : Int)) ∨ (a = -(m : Int) ∧ b = (m : Int) + 1) ∨ (a
        = -(m : Int) + 1 ∧ b = (m : Int) + 1)) → ((b ≠ m) → (z ∉ BoundaryFootprintVertices (C 0
        true) ∧
      z ∉ BoundaryFootprintVertices (C 0 false) ∧
      z ∉ BoundaryFootprintVertices (C 1 true) ∧
      z ∉ BoundaryFootprintVertices (C 1 false))))))) := by
  classical
  intro m C z a b hrow hunit00 hunit01 hunit10 hunit11 hnot
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  constructor
  · rw [hunit00]
    omega
  constructor
  · rw [hunit01]
    omega
  constructor
  · rw [hunit10]
    omega
  · rw [hunit11]
    omega

private theorem hpredFalseOff :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let b := z.im
    ((b < m) → (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1))) → ((∀ (n
        : Nat), (0 < n) → (∀ (x : GaussianInt), (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
        DiamondCellDomain n) → (x ∈ BoundaryFootprintVertices (DiamondTile n) ↔ ∃ j : Fin 4,
        LatticeVertexIncidentCell x j ∉ DiamondCellDomain n))) → ((b < m) → (z ∉
        BoundaryFootprintVertices (DiamondTile (m - 1)))))) := by
  classical
  intro m hm z b hdesclow boundaryIffMissing hbelow
  have hn : 0 < m - 1 := by omega
  have hall := hdesclow hbelow
  have hsome : ∃ j : Fin 4,
      LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1) := ⟨0, hall 0⟩
  rw [boundaryIffMissing (m - 1) hn z hsome]
  rintro ⟨j, hj⟩
  exact hj (hall j)

private theorem hpredTrueOff :
    ∀ (m : Nat), (1 < m) → (∀ (z : GaussianInt),
    let b := z.im
    (((m : Int) < b) → (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ (TileTranslation
        (DiamondTile (m - 1)) ⟨0, 2⟩).cells)) → ((∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x :
        GaussianInt), GaussianTranslation u x ∈ BoundaryFootprintVertices (TileTranslation T u) ↔
        x ∈ BoundaryFootprintVertices T) → ((∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (x :
        GaussianInt), ∀ (j : Fin 4), LatticeVertexIncidentCell (GaussianTranslation u x) j ∈
        (TileTranslation T u).cells ↔ LatticeVertexIncidentCell x j ∈ T.cells) → ((∀ (n : Nat),
        (0 < n) → (∀ (x : GaussianInt), (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
        DiamondCellDomain n) → (x ∈ BoundaryFootprintVertices (DiamondTile n) ↔ ∃ j : Fin 4,
        LatticeVertexIncidentCell x j ∉ DiamondCellDomain n))) → (((m : Int) < b) → (z ∉
        BoundaryFootprintVertices
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩))))))) := by
  classical
  intro m hm z b hdeschi translationBoundary translationCell boundaryIffMissing habove
  let w := z - ⟨0, 2⟩
  have hshift : GaussianTranslation ⟨0, 2⟩ w = z := by
    simp [GaussianTranslation, w]
  have hall : ∀ j : Fin 4,
      LatticeVertexIncidentCell w j ∈ DiamondCellDomain (m - 1) := by
    intro j
    have htranslated := hdeschi habove j
    have htranslated' : LatticeVertexIncidentCell
        (GaussianTranslation ⟨0, 2⟩ w) j ∈
          (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells := by
      simpa [hshift] using htranslated
    exact (translationCell (DiamondTile (m - 1)) ⟨0, 2⟩ w j).mp htranslated'
  have hn : 0 < m - 1 := by omega
  have hsome : ∃ j : Fin 4,
      LatticeVertexIncidentCell w j ∈ DiamondCellDomain (m - 1) := ⟨0, hall 0⟩
  have hnot : w ∉ BoundaryFootprintVertices (DiamondTile (m - 1)) := by
    rw [boundaryIffMissing (m - 1) hn w hsome]
    rintro ⟨j, hj⟩
    exact hj (hall j)
  intro hz
  have hz' : GaussianTranslation ⟨0, 2⟩ w ∈
      BoundaryFootprintVertices (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) := by
    simpa [hshift] using hz
  exact hnot ((translationBoundary (DiamondTile (m - 1)) ⟨0, 2⟩ w).mp hz')

private theorem hpredOff :
    ∀ (m : Nat), ∀ (z : GaussianInt),
    let b := z.im
    ((b < m) → (z ∉ BoundaryFootprintVertices (DiamondTile (m - 1)))) → ((((m : Int) < b) → (z ∉
        BoundaryFootprintVertices (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩))) → ((b ≠ m) →
        (z ∉ BoundaryFootprintVertices (DiamondTile (m - 1)) ∨
      z ∉ BoundaryFootprintVertices
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩)))) := by
  classical
  intro m z b hpredFalseOff hpredTrueOff hnot
  by_cases hbelow : b < m
  · exact Or.inl (hpredFalseOff hbelow)
  · have habove : (m : Int) < b := by omega
    exact Or.inr (hpredTrueOff habove)

private theorem hmidcore :
    ∀ (m : Nat), ∀ (z : GaussianInt),
    let a := z.re
    (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) ↔
        -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3 := by
  classical
  intro m z a
  omega

private theorem hk :
    ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    k =
      (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 0 false) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 1 true) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 2 false) then 1 else 0) := by
  classical
  intro C z k
  dsimp [k]
  simp only [Nat.card_eq_fintype_card, Finset.card_eq_sum_ones,
    Fintype.card_subtype, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
  ring

private theorem hcardOff :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), (C 2 false = DiamondTile (m - 1)) → ((C 2 true
        = TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) → (∀ (z : GaussianInt),
    let b := z.im
    ((b ≠ m) → (z ∉ BoundaryFootprintVertices (C 0 true) ∧ z ∉ BoundaryFootprintVertices (C 0
        false) ∧ z ∉ BoundaryFootprintVertices (C 1 true) ∧ z ∉ BoundaryFootprintVertices (C 1
        false))) → (((b ≠ m) → (z ∉ BoundaryFootprintVertices (DiamondTile (m - 1)) ∨ z ∉
        BoundaryFootprintVertices (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩))) → (
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    (k = (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 0 false) then 1 else 0) + (if z ∈ BoundaryFootprintVertices
        (C 1 true) then 1 else 0) + (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0)
        + (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 2 false) then 1 else 0)) → ((b ≠ m) → (k ≤ 1)))))) := by
  classical
  intro m C h2f h2t z b hunitOff hpredOff k hk hnot
  rw [hk, h2t, h2f]
  rcases hunitOff hnot with ⟨hu00, hu01, hu10, hu11⟩
  simp only [hu00, hu01, hu10, hu11]
  rcases hpredOff hnot with hp | hp
  · simp [hp]
    split_ifs <;> omega
  · simp [hp]
    split_ifs <;> omega

private theorem hcardMid :
    ∀ (m : Nat), (1 < m) → (∀ (C : Fin 3 → Bool → ProtoTile), (C 2 false = DiamondTile (m - 1)) →
        ((C 2 true = TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → (((b = m) → (z ∈ BoundaryFootprintVertices (DiamondTile (m - 1)) ↔
        ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3))) → (((b = m) → (z ∈ BoundaryFootprintVertices
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) ↔ ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) -
        3))) → ((z ∈ BoundaryFootprintVertices (C 0 true) ↔ (a = -(m : Int) ∧ b = (m : Int) - 1)
        ∨ (a = -(m : Int) + 1 ∧ b = (m : Int) - 1) ∨ (a = -(m : Int) ∧ b = (m : Int)) ∨ (a = -(m
        : Int) + 1 ∧ b = (m : Int))) → ((z ∈ BoundaryFootprintVertices (C 0 false) ↔ (a = (m :
        Int) - 1 ∧ b = (m : Int)) ∨ (a = (m : Int) ∧ b = (m : Int)) ∨ (a = (m : Int) - 1 ∧ b = (m
        : Int) + 1) ∨ (a = (m : Int) ∧ b = (m : Int) + 1)) → ((z ∈ BoundaryFootprintVertices (C 1
        true) ↔ (a = (m : Int) - 1 ∧ b = (m : Int) - 1) ∨ (a = (m : Int) ∧ b = (m : Int) - 1) ∨
        (a = (m : Int) - 1 ∧ b = (m : Int)) ∨ (a = (m : Int) ∧ b = (m : Int))) → ((z ∈
        BoundaryFootprintVertices (C 1 false) ↔ (a = -(m : Int) ∧ b = (m : Int)) ∨ (a = -(m :
        Int) + 1 ∧ b = (m : Int)) ∨ (a = -(m : Int) ∧ b = (m : Int) + 1) ∨ (a = -(m : Int) + 1 ∧
        b = (m : Int) + 1)) → (
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    (k = (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 0 false) then 1 else 0) + (if z ∈ BoundaryFootprintVertices
        (C 1 true) then 1 else 0) + (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0)
        + (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 2 false) then 1 else 0)) → ((b = m) → (k = 2 * (if a = -(m :
        Int) + 1 then 1 else 0) +
        2 * (if a = (m : Int) - 1 then 1 else 0) +
        2 * (if ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3)
          then 1 else 0))))))))))))) := by
  classical
  intro m hm C h2f h2t z a b hrow hpredFalseMid hpredTrueMid hunit00 hunit01 hunit10 hunit11 k hk
      hmid
  simp only [hk, hunit00, hunit01, hunit10, hunit11]
  rw [h2t, h2f]
  simp only [hpredTrueMid hmid, hpredFalseMid hmid]
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  simp [hmid]
  split_ifs <;> omega

private theorem hmidClass :
    ∀ (m : Nat), (1 < m) → (∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → (
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    ((b = m) → (k = 2 * (if a = -(m : Int) + 1 then 1 else 0) + 2 * (if a = (m : Int) - 1 then 1
        else 0) + 2 * (if ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) then 1 else 0))) → ((b = m)
        → ((k = 2 ↔ a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) ∧
      k ≠ 3 ∧
      (k = 4 ↔ a = (m : Int) - 1 ∨ a = -((m : Int) - 1)) ∧
      (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))))) := by
  classical
  intro m hm C z a b hrow k hcardMid hmid
  rw [hcardMid hmid]
  rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
  have hmid' : z.im = (m : Int) := by simpa [b] using hmid
  rw [hmid'] at h1 h2 h3 h4 h5 h6
  dsimp [a] at *
  by_cases hl : z.re = -(m : Int) + 1
  · by_cases hr : z.re = (m : Int) - 1
    · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
        simp only [Int.reduceNeg, hl, ↓reduceIte, mul_one, mul_ite, mul_zero,
            le_neg_add_iff_add_le, add_neg_cancel_left, Nat.not_ofNat_le_one,
            neg_add_le_iff_le_add, false_and, not_false_eq_true, Nat.add_eq_right,
            Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, ite_eq_right_iff, imp_false, neg_sub,
            false_iff, not_or, Nat.reduceEqDiff, Nat.add_eq_left, and_self, add_sub_cancel,
            and_true] <;> (try split_ifs) <;> omega
    · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
        simp only [Int.reduceNeg, hl, ↓reduceIte, mul_one, mul_ite, mul_zero,
            le_neg_add_iff_add_le, add_neg_cancel_left, Nat.not_ofNat_le_one,
            neg_add_le_iff_le_add, false_and, not_false_eq_true, Nat.add_eq_right,
            Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, ite_eq_right_iff, imp_false, neg_sub,
            false_iff, not_or, Nat.reduceEqDiff, Nat.add_eq_left, and_self, add_sub_cancel,
            and_true] <;> (try split_ifs) <;> omega
  · by_cases hr : z.re = (m : Int) - 1
    · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
        simp only [Int.reduceNeg, hr, mul_ite, mul_one, mul_zero, ↓reduceIte,
            neg_add_le_iff_le_add, tsub_le_iff_right, not_and, not_le, sub_right_inj,
            OfNat.one_ne_ofNat, neg_sub, false_or, true_or, iff_true, Nat.add_eq_zero_iff,
            ite_eq_right_iff, OfNat.ofNat_ne_zero, imp_false, and_false, not_imp, not_lt,
            false_and, false_iff] <;> (try split_ifs) <;> omega
    · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
        simp only [Int.reduceNeg, hl, ↓reduceIte, mul_zero, hr, add_zero, hc, and_self,
            not_true_eq_false, OfNat.zero_ne_ofNat, neg_sub, false_iff, not_or,
            not_false_eq_true, false_or, tsub_le_iff_right, and_true, true_iff, true_and,
            neg_add_le_iff_le_add, not_and, not_le, mul_ite, mul_one, zero_add,
            ite_eq_left_iff, not_imp, not_lt, imp_false, ite_eq_right_iff,
            OfNat.ofNat_ne_zero, and_congr_left_iff] <;> (try split_ifs) <;> omega

private theorem htwoOff :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    (k = (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 0 false) then 1 else 0) + (if z ∈ BoundaryFootprintVertices
        (C 1 true) then 1 else 0) + (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0)
        + (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 2 false) then 1 else 0)) → (((b ≠ m) → (k ≤ 1)) → ((b ≠ m) →
        ((k = 2 ↔ b = m ∧
        (a = (m : Int) - 2 ∨ a = -((m : Int) - 2)))))) := by
  classical
  intro m C z a b k hk hcardOff hnot
  constructor
  · intro hk2
    have := hcardOff hnot
    omega
  · intro hh
    exact (hnot hh.1).elim

private theorem hfourOff :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    (k = (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 0 false) then 1 else 0) + (if z ∈ BoundaryFootprintVertices
        (C 1 true) then 1 else 0) + (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0)
        + (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 2 false) then 1 else 0)) → (((b ≠ m) → (k ≤ 1)) → ((b ≠ m) →
        ((k = 4 ↔ b = m ∧
        (a = (m : Int) - 1 ∨ a = -((m : Int) - 1)))))) := by
  classical
  intro m C z a b k hk hcardOff hnot
  constructor
  · intro hk4
    have := hcardOff hnot
    omega
  · intro hh
    exact (hnot hh.1).elim

private theorem htwo :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    ((b = m) → ((k = 2 ↔ a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) ∧ k ≠ 3 ∧ (k = 4 ↔ a = (m :
        Int) - 1 ∨ a = -((m : Int) - 1)) ∧ (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) →
        (((b ≠ m) → ((k = 2 ↔ b = m ∧ (a = (m : Int) - 2 ∨ a = -((m : Int) - 2))))) → (k = 2 ↔ b
        = m ∧
      (a = (m : Int) - 2 ∨ a = -((m : Int) - 2)))) := by
  classical
  intro m C z a b k hmidClass htwoOff
  by_cases hmid : b = m
  · simpa [hmid] using (hmidClass hmid).1
  · exact htwoOff hmid

private theorem hfour :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    ((b = m) → ((k = 2 ↔ a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) ∧ k ≠ 3 ∧ (k = 4 ↔ a = (m :
        Int) - 1 ∨ a = -((m : Int) - 1)) ∧ (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) →
        (((b ≠ m) → ((k = 4 ↔ b = m ∧ (a = (m : Int) - 1 ∨ a = -((m : Int) - 1))))) → (k = 4 ↔ b
        = m ∧
      (a = (m : Int) - 1 ∨ a = -((m : Int) - 1)))) := by
  classical
  intro m C z a b k hmidClass hfourOff
  by_cases hmid : b = m
  · simpa [hmid] using (hmidClass hmid).2.2.1
  · exact hfourOff hmid

private theorem hnotThree :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    (k = (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 0 false) then 1 else 0) + (if z ∈ BoundaryFootprintVertices
        (C 1 true) then 1 else 0) + (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0)
        + (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) + (if z ∈
        BoundaryFootprintVertices (C 2 false) then 1 else 0)) → (((b ≠ m) → (k ≤ 1)) → (((b = m)
        → ((k = 2 ↔ a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) ∧ k ≠ 3 ∧ (k = 4 ↔ a = (m : Int) -
        1 ∨ a = -((m : Int) - 1)) ∧ (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) → (k ≠
        3))) := by
  classical
  intro m C z a b k hk hcardOff hmidClass
  by_cases hmid : b = m
  · exact (hmidClass hmid).2.1
  · have := hcardOff hmid
    omega

private theorem hzeroMid :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    ((b = m) → ((k = 2 ↔ a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) ∧ k ≠ 3 ∧ (k = 4 ↔ a = (m :
        Int) - 1 ∨ a = -((m : Int) - 1)) ∧ (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) →
        ((b = m) → ((k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) := by
  classical
  intro m C z a b k hmidClass hmid
  exact (hmidClass hmid).2.2.2

private theorem hzero :
    ∀ (m : Nat), ∀ (C : Fin 3 → Bool → ProtoTile), ∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    ((b = m) → ((k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) → (b = m →
      (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3)) := by
  classical
  intro m C z a b k hzeroMid hmid
  exact hzeroMid hmid

private theorem hdescent :
    ∀ (m : Nat), (1 < m) → (∀ (C : Fin 3 → Bool → ProtoTile), (C 2 false = DiamondTile (m - 1)) →
        ((C 2 true = TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) → (∀ (z : GaussianInt),
    let a := z.re
    let b := z.im
    ((1 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) ∧ -(z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤
        z.im - (1 : ℤ) ∧ -((2 : ℤ) * (↑m : ℤ) - z.im - (1 : ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑m :
        ℤ) - z.im - (1 : ℤ)) → (((b < m) → (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈
        DiamondCellDomain (m - 1))) → ((((m : Int) < b) → (∀ j : Fin 4, LatticeVertexIncidentCell
        z j ∈ (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells)) → (((b = m) → ((∀ j : Fin 4,
        LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1)) ↔ -(m : Int) + 3 ≤ a ∧ a ≤ (m
        : Int) - 3)) → (((-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m
        : Int) - 3) → (
    let k := Nat.card {a : Fin 3 × Bool //
      z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    ((b = m) → (k = 2 * (if a = -(m : Int) + 1 then 1 else 0) + 2 * (if a = (m : Int) - 1 then 1
        else 0) + 2 * (if ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) then 1 else 0))) → (((b = m)
        → ((k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3))) → ((k = 2 ∨ k = 4) ∨
      ∃ s : Bool, ∀ j : Fin 4,
        LatticeVertexIncidentCell z j ∈ (C 2 s).cells)))))))))) := by
  classical
  intro m hm C h2f h2t z a b hrow hdesclow hdeschi hloFourAtMid hmidcore k hcardMid hzeroMid
  by_cases hmid : b = m
  · by_cases hlarge : k = 2 ∨ k = 4
    · exact Or.inl hlarge
    · have hknot2 : k ≠ 2 := fun h => hlarge (Or.inl h)
      have hknot4 : k ≠ 4 := fun h => hlarge (Or.inr h)
      have hcore : -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3 := by
        have hzero' := (hzeroMid hmid).2
        by_contra hn
        have hnzero : k ≠ 0 := by
          intro hzero
          exact hn ((hzeroMid hmid).1 hzero)
        rcases hrow with ⟨h1, h2, h3, h4, h5, h6⟩
        have hformula := hcardMid hmid
        have hmid' : z.im = (m : Int) := by simpa [b] using hmid
        rw [hmid'] at h1 h2 h3 h4 h5 h6
        dsimp [a] at *
        by_cases hl : z.re = -(m : Int) + 1
        · by_cases hr : z.re = (m : Int) - 1
          · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
              simp only [Int.reduceNeg, hl, ↓reduceIte, mul_one, mul_ite, mul_zero,
                  le_neg_add_iff_add_le, add_neg_cancel_left, Nat.not_ofNat_le_one,
                  neg_add_le_iff_le_add, false_and, not_false_eq_true] at hformula <;> (try
                      split_ifs at hformula) <;> omega
          · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
              simp only [Int.reduceNeg, hl, ↓reduceIte, mul_one, mul_ite, mul_zero,
                  le_neg_add_iff_add_le, add_neg_cancel_left, Nat.not_ofNat_le_one,
                  neg_add_le_iff_le_add, false_and, not_false_eq_true] at hformula <;> (try
                      split_ifs at hformula) <;> omega
        · by_cases hr : z.re = (m : Int) - 1
          · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
              simp only [Int.reduceNeg, hr, mul_ite, mul_one, mul_zero, ↓reduceIte,
                  neg_add_le_iff_le_add, tsub_le_iff_right, not_and, not_le] at hformula <;> (try
                      split_ifs at hformula) <;> omega
          · by_cases hc : -(m : Int) + 3 ≤ z.re ∧ z.re ≤ (m : Int) - 3 <;>
              simp only [Int.reduceNeg, hl, ↓reduceIte, mul_zero, hr, add_zero, hc, and_self,
                  not_true_eq_false, neg_add_le_iff_le_add, not_and, not_le, mul_ite, mul_one,
                  zero_add] at hformula <;> (try split_ifs at hformula) <;> omega
      have hfourlo := (hloFourAtMid hmid).2 ((hmidcore).2 hcore)
      refine Or.inr ⟨false, ?_⟩
      intro j
      rw [h2f]
      exact hfourlo j
  · have hbelowOrAbove : b < m ∨ (m : Int) < b := by omega
    rcases hbelowOrAbove with hbelow | habove
    · refine Or.inr ⟨false, ?_⟩
      intro j
      rw [h2f]
      exact hdesclow hbelow j
    · refine Or.inr ⟨true, ?_⟩
      intro j
      rw [h2t]
      exact hdeschi habove j

end DiamondBoundaryProof

theorem P4194T1DiamondBoundaryLedger
    (m : Nat) (hm : 1 < m) (C : Fin 3 → Bool → ProtoTile)
    (h00 : C 0 true = ⟨{⟨-(m : Int), (m : Int) - 1⟩}, ⟨-(m : Int), (m : Int) - 1⟩⟩)
    (h01 : C 0 false = ⟨{⟨(m : Int) - 1, (m : Int)⟩}, ⟨(m : Int) - 1, (m : Int)⟩⟩)
    (h10 : C 1 true = ⟨{⟨(m : Int) - 1, (m : Int) - 1⟩}, ⟨(m : Int) - 1, (m : Int) - 1⟩⟩)
    (h11 : C 1 false = ⟨{⟨-(m : Int), (m : Int)⟩}, ⟨-(m : Int), (m : Int)⟩⟩)
    (h2f : C 2 false = DiamondTile (m - 1))
    (h2t : C 2 true = TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩)
    (z : GaussianInt)
    (hz : ∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain m) :
    let k := Nat.card {a : Fin 3 × Bool // z ∈ BoundaryFootprintVertices (C a.1 a.2)}
    (k = 2 ↔ z.im = (m : Int) ∧
      (z.re = (m : Int) - 2 ∨ z.re = -((m : Int) - 2))) ∧
    k ≠ 3 ∧
    (k = 4 ↔ z.im = (m : Int) ∧
      (z.re = (m : Int) - 1 ∨ z.re = -((m : Int) - 1))) ∧
    (z.im ≠ (m : Int) → k ≤ 1) ∧
    (z.im = (m : Int) →
      (k = 0 ↔ -((m : Int) - 3) ≤ z.re ∧ z.re ≤ (m : Int) - 3)) ∧
    ((k = 2 ∨ k = 4) ∨
      ∃ s : Bool, ∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ (C 2 s).cells) := by
-- BODY
  classical
  let a := z.re
  let b := z.im
  have hrow := DiamondBoundaryProof.hrow m z hz
  have hdesclow (hb : b < m) :
      ∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1) :=
          DiamondBoundaryProof.hdesclow m hm z hrow hb
  have hdeschi (hb : (m : Int) < b) :
      ∀ j : Fin 4,
        LatticeVertexIncidentCell z j ∈
          (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells := DiamondBoundaryProof.hdeschi m
              hm z hrow hb
  have hloFourAtMid (hmid : b = m) :
      (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1)) ↔
        -(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3 := DiamondBoundaryProof.hloFourAtMid m hm z hrow hmid
  have hsomeLoMid (hmid : b = m) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain (m - 1) :=
          DiamondBoundaryProof.hsomeLoMid m hm z hrow hmid
  have hsomeHiMid (hmid : b = m) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩).cells := DiamondBoundaryProof.hsomeHiMid m
            hm z hrow hmid
  have hhiFourAtMid (hmid : b = m) :
      (∀ j : Fin 4, LatticeVertexIncidentCell (z - ⟨0, 2⟩) j ∈
        DiamondCellDomain (m - 1)) ↔
        -(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3 := DiamondBoundaryProof.hhiFourAtMid m hm z hrow hmid
  have translationBoundary (T : ProtoTile) (u x : GaussianInt) :
      GaussianTranslation u x ∈ BoundaryFootprintVertices (TileTranslation T u) ↔
        x ∈ BoundaryFootprintVertices T := DiamondBoundaryProof.translationBoundary T u x
  have translationCell (T : ProtoTile) (u x : GaussianInt) (j : Fin 4) :
      LatticeVertexIncidentCell (GaussianTranslation u x) j ∈
          (TileTranslation T u).cells ↔
        LatticeVertexIncidentCell x j ∈ T.cells := DiamondBoundaryProof.translationCell T u x j
  have boundaryIffMissing (n : Nat) (hn : 0 < n) (x : GaussianInt)
      (hsome : ∃ j : Fin 4,
        LatticeVertexIncidentCell x j ∈ DiamondCellDomain n) :
      x ∈ BoundaryFootprintVertices (DiamondTile n) ↔
        ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ DiamondCellDomain n :=
            DiamondBoundaryProof.boundaryIffMissing n hn x hsome
  have hpredFalseMid (hmid : b = m) :
      z ∈ BoundaryFootprintVertices (DiamondTile (m - 1)) ↔
        ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) := DiamondBoundaryProof.hpredFalseMid m hm z
            hloFourAtMid hsomeLoMid boundaryIffMissing hmid
  have hpredTrueMid (hmid : b = m) :
      z ∈ BoundaryFootprintVertices
          (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) ↔
        ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) := DiamondBoundaryProof.hpredTrueMid m hm z
            hsomeHiMid hhiFourAtMid translationBoundary translationCell boundaryIffMissing hmid
  have unitBoundary (c x : GaussianInt) :
      x ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) ↔
        x = c ∨ x = c + 1 ∨ x = c + ⟨0, 1⟩ ∨ x = c + 1 + ⟨0, 1⟩ :=
            DiamondBoundaryProof.unitBoundary c x
  have hunit00 : z ∈ BoundaryFootprintVertices (C 0 true) ↔
      (a = -(m : Int) ∧ b = (m : Int) - 1) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int) - 1) ∨
      (a = -(m : Int) ∧ b = (m : Int)) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int)) := DiamondBoundaryProof.hunit00 m C h00 z unitBoundary
  have hunit01 : z ∈ BoundaryFootprintVertices (C 0 false) ↔
      (a = (m : Int) - 1 ∧ b = (m : Int)) ∨
      (a = (m : Int) ∧ b = (m : Int)) ∨
      (a = (m : Int) - 1 ∧ b = (m : Int) + 1) ∨
      (a = (m : Int) ∧ b = (m : Int) + 1) := DiamondBoundaryProof.hunit01 m C h01 z unitBoundary
  have hunit10 : z ∈ BoundaryFootprintVertices (C 1 true) ↔
      (a = (m : Int) - 1 ∧ b = (m : Int) - 1) ∨
      (a = (m : Int) ∧ b = (m : Int) - 1) ∨
      (a = (m : Int) - 1 ∧ b = (m : Int)) ∨
      (a = (m : Int) ∧ b = (m : Int)) := DiamondBoundaryProof.hunit10 m C h10 z unitBoundary
  have hunit11 : z ∈ BoundaryFootprintVertices (C 1 false) ↔
      (a = -(m : Int) ∧ b = (m : Int)) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int)) ∨
      (a = -(m : Int) ∧ b = (m : Int) + 1) ∨
      (a = -(m : Int) + 1 ∧ b = (m : Int) + 1) := DiamondBoundaryProof.hunit11 m C h11 z
          unitBoundary
  have hunitOff (hnot : b ≠ m) :
      z ∉ BoundaryFootprintVertices (C 0 true) ∧
      z ∉ BoundaryFootprintVertices (C 0 false) ∧
      z ∉ BoundaryFootprintVertices (C 1 true) ∧
      z ∉ BoundaryFootprintVertices (C 1 false) := DiamondBoundaryProof.hunitOff m C z hrow
          hunit00 hunit01 hunit10 hunit11 hnot
  have hpredFalseOff (hbelow : b < m) :
      z ∉ BoundaryFootprintVertices (DiamondTile (m - 1)) := DiamondBoundaryProof.hpredFalseOff m
          hm z hdesclow boundaryIffMissing hbelow
  have hpredTrueOff (habove : (m : Int) < b) :
      z ∉ BoundaryFootprintVertices
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) := DiamondBoundaryProof.hpredTrueOff m hm
            z hdeschi translationBoundary translationCell boundaryIffMissing habove
  have hpredOff (hnot : b ≠ m) :
      z ∉ BoundaryFootprintVertices (DiamondTile (m - 1)) ∨
      z ∉ BoundaryFootprintVertices
        (TileTranslation (DiamondTile (m - 1)) ⟨0, 2⟩) := DiamondBoundaryProof.hpredOff m z
            hpredFalseOff hpredTrueOff hnot
  have hmidcore :
      (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3) ↔
        -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3 := DiamondBoundaryProof.hmidcore m z
  let k := Nat.card {a : Fin 3 × Bool //
    z ∈ BoundaryFootprintVertices (C a.1 a.2)}
  have hk : k =
      (if z ∈ BoundaryFootprintVertices (C 0 true) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 0 false) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 1 true) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 1 false) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 2 true) then 1 else 0) +
      (if z ∈ BoundaryFootprintVertices (C 2 false) then 1 else 0) := DiamondBoundaryProof.hk C z
  have hcardOff (hnot : b ≠ m) : k ≤ 1 := DiamondBoundaryProof.hcardOff m C h2f h2t z hunitOff
      hpredOff hk hnot
  have hcardMid (hmid : b = m) :
      k = 2 * (if a = -(m : Int) + 1 then 1 else 0) +
        2 * (if a = (m : Int) - 1 then 1 else 0) +
        2 * (if ¬ (-(m : Int) + 3 ≤ a ∧ a ≤ (m : Int) - 3)
          then 1 else 0) := DiamondBoundaryProof.hcardMid m hm C h2f h2t z hrow hpredFalseMid
              hpredTrueMid hunit00 hunit01 hunit10 hunit11 hk hmid
  have hmidClass (hmid : b = m) :
      (k = 2 ↔ a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) ∧
      k ≠ 3 ∧
      (k = 4 ↔ a = (m : Int) - 1 ∨ a = -((m : Int) - 1)) ∧
      (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3) := DiamondBoundaryProof.hmidClass m hm C
          z hrow hcardMid hmid
  have htwoOff (hnot : b ≠ m) :
      (k = 2 ↔ b = m ∧
        (a = (m : Int) - 2 ∨ a = -((m : Int) - 2))) := DiamondBoundaryProof.htwoOff m C z hk
            hcardOff hnot
  have hfourOff (hnot : b ≠ m) :
      (k = 4 ↔ b = m ∧
        (a = (m : Int) - 1 ∨ a = -((m : Int) - 1))) := DiamondBoundaryProof.hfourOff m C z hk
            hcardOff hnot
  have htwo : k = 2 ↔ b = m ∧
      (a = (m : Int) - 2 ∨ a = -((m : Int) - 2)) := DiamondBoundaryProof.htwo m C z hmidClass
          htwoOff
  have hfour : k = 4 ↔ b = m ∧
      (a = (m : Int) - 1 ∨ a = -((m : Int) - 1)) := DiamondBoundaryProof.hfour m C z hmidClass
          hfourOff
  have hnotThree : k ≠ 3 := DiamondBoundaryProof.hnotThree m C z hk hcardOff hmidClass
  have hzeroMid (hmid : b = m) :
      (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3) := DiamondBoundaryProof.hzeroMid m C z
          hmidClass hmid
  have hzero : b = m →
      (k = 0 ↔ -((m : Int) - 3) ≤ a ∧ a ≤ (m : Int) - 3) := DiamondBoundaryProof.hzero m C z
          hzeroMid
  have hdescent : (k = 2 ∨ k = 4) ∨
      ∃ s : Bool, ∀ j : Fin 4,
        LatticeVertexIncidentCell z j ∈ (C 2 s).cells := DiamondBoundaryProof.hdescent m hm C h2f
            h2t z hrow hdesclow hdeschi hloFourAtMid hmidcore hcardMid hzeroMid
  dsimp [a, b]
  exact ⟨htwo, hnotThree, hfour, hcardOff, hzero, hdescent⟩

end ApollonianSuperharmonic

end
