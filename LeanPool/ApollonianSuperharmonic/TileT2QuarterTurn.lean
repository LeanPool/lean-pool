/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandTwelveParentSurround
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate

-- [TABLET NODE: TileT2QuarterTurn]

/-!
# TileT2QuarterTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace QuarterTurnTileGeometry

private theorem turn_back :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        ∀ (x : GaussianInt), back (turn x) = x ) := by
  classical
  intro u turn back x
  rcases x with ⟨a, b⟩
  simp [turn, back]
  ring

private theorem back_turn :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        ∀ (x : GaussianInt), turn (back x) = x ) := by
  classical
  intro u turn back x
  rcases x with ⟨a, b⟩
  simp [turn, back]
  ring

private theorem hRingImage :
    (by
      classical
      exact
        ∀ (ring : ProtoTile), ∀ (u : GaussianInt), ((TileTranslation (TileQuarterTurn ring)
            u).cells = ring.cells) → (
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        (ring.cells.image turn : Set GaussianInt) = (ring.cells : Set GaussianInt)) ) := by
  classical
  intro ring u hRingCells turn
  have h := hRingCells
  rw [TileTranslationFormulas (TileQuarterTurn ring) u |>.1,
    TileQuarterTurnFormulas ring |>.1] at h
  have hfun : ∀ x : GaussianInt,
      GaussianTranslation u (GaussianQuarterTurn x - 1) = turn x := by
    intro x
    rcases x with ⟨a, b⟩
    apply Zsqrtd.ext_iff.mpr;
      simp [GaussianTranslation, GaussianQuarterTurn, turn]
  have hf : (GaussianTranslation u) ∘ (fun x => GaussianQuarterTurn x - 1) = turn := by
    funext x
    exact hfun x
  rw [Finset.image_image, hf] at h
  exact congrArg (fun s : Finset GaussianInt => (s : Set GaussianInt)) h

private theorem turn_neighbor :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a
            - ⟨0, 1⟩) → (turn b = turn a + ⟨0, 1⟩ ∨ turn b = turn a - ⟨0, 1⟩ ∨ turn b = turn a -
            1 ∨ turn b = turn a + 1) ) := by
  classical
  intro u turn a b h
  rcases h with h | h | h | h
  · subst b; left; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [turn]; ring
  · subst b; right; left; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [turn]; ring
  · subst b; right; right; left; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [turn]; ring
  · subst b; right; right; right; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [turn]; ring

private theorem back_neighbor :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a
            - ⟨0, 1⟩) → (back b = back a - ⟨0, 1⟩ ∨ back b = back a + ⟨0, 1⟩ ∨ back b = back a +
            1 ∨ back b = back a - 1) ) := by
  classical
  intro u back a b h
  rcases h with h | h | h | h
  · subst b; left; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [back]; ring
  · subst b; right; left; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [back]; ring
  · subst b; right; right; left; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [back]; ring
  · subst b; right; right; right; rcases a with ⟨a, c⟩
    apply Zsqrtd.ext_iff.mpr; constructor <;> simp [back]; ring

private theorem hDcomp :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (ring : ProtoTile), ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        (∀ (x : GaussianInt), back (turn x) = x) → (((ring.cells.image turn : Set GaussianInt) =
            (ring.cells : Set GaussianInt)) → (((T.cells : Set GaussianInt) ⊆ (ring.cells : Set
            GaussianInt)ᶜ) → (
        let D : Set GaussianInt := turn '' (T.cells : Set GaussianInt)
        D ⊆ (ring.cells : Set GaussianInt)ᶜ))) ) := by
  classical
  intro T ring u turn back turn_back hRingImage hTComp D x hx
  rcases hx with ⟨y, hy, rfl⟩
  intro hxs
  have hxs' : turn y ∈ (ring.cells.image turn : Set GaussianInt) := by
    rw [hRingImage]
    exact hxs
  change turn y ∈ ring.cells.image turn at hxs'
  rcases Finset.mem_image.mp hxs' with ⟨z, hz, hzy⟩
  have hzy' : z = y := by
    apply_fun back at hzy
    simpa [back_turn, turn_back] using hzy
  exact hTComp hy (by simpa [hzy'] using hz)

private theorem hDConnected :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        (∀ (x : GaussianInt), back (turn x) = x) → ((∀ (x : GaussianInt), turn (back x) = x) → (
        let gridConnected := fun S : Set GaussianInt =>
          S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ p : List GaussianInt,
            p.head? = some x ∧ p.getLast? = some y ∧
            (∀ z ∈ p, z ∈ S) ∧
            ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
              p = l₁ ++ a :: b :: l₂ →
                b = a + 1 ∨ b = a - 1 ∨
                  b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩
        (gridConnected (T.cells : Set GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (turn b = turn a + ⟨0, 1⟩
            ∨ turn b = turn a - ⟨0, 1⟩ ∨ turn b = turn a - 1 ∨ turn b = turn a + 1)) → (
        let D : Set GaussianInt := turn '' (T.cells : Set GaussianInt)
        gridConnected D)))) ) := by
  classical
  intro T u turn back turn_back back_turn gridConnected hTConnected turn_neighbor D
  constructor
  · rcases hTConnected.1 with ⟨x, hx⟩
    exact ⟨turn x, ⟨x, hx, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨x₀, hx₀, rfl⟩
    rcases hy with ⟨y₀, hy₀, rfl⟩
    rcases hTConnected.2 x₀ hx₀ y₀ hy₀ with ⟨p, hp, hlast, hmem, hadj⟩
    refine ⟨p.map turn, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg (Option.map turn) hp
    · simpa using congrArg (Option.map turn) hlast
    · intro z hz
      simp only [List.mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, hmem w hw, rfl⟩
    · intro a b l₁ l₂ he
      have he' : p = l₁.map back ++ back a :: back b :: l₂.map back := by
        have hh := congrArg (List.map back) he
        simpa [List.map_append, Function.comp_def, turn_back] using hh
      have hadj' := hadj (back a) (back b) (l₁.map back) (l₂.map back) he'
      rcases turn_neighbor (back a) (back b) hadj' with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by simpa [back_turn, turn_back] using h)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [back_turn, turn_back] using h)))
      · exact Or.inr (Or.inl (by simpa [back_turn, turn_back] using h))
      · exact Or.inl (by simpa [back_turn, turn_back] using h)

private theorem mapBackConnected :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        (∀ (x : GaussianInt), back (turn x) = x) → ((∀ (x : GaussianInt), turn (back x) = x) → (
        let gridConnected := fun S : Set GaussianInt =>
          S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ p : List GaussianInt,
            p.head? = some x ∧ p.getLast? = some y ∧
            (∀ z ∈ p, z ∈ S) ∧
            ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
              p = l₁ ++ a :: b :: l₂ →
                b = a + 1 ∨ b = a - 1 ∨
                  b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b =
            a - ⟨0, 1⟩) → (back b = back a - ⟨0, 1⟩ ∨ back b = back a + ⟨0, 1⟩ ∨ back b = back a
            + 1 ∨ back b = back a - 1)) → (∀ (S : Set GaussianInt), (gridConnected S) →
            (gridConnected (S.image back))))) ) := by
  classical
  intro u turn back turn_back back_turn gridConnected back_neighbor S hS
  constructor
  · rcases hS.1 with ⟨x, hx⟩
    exact ⟨back x, ⟨x, hx, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨x₀, hx₀, rfl⟩
    rcases hy with ⟨y₀, hy₀, rfl⟩
    rcases hS.2 x₀ hx₀ y₀ hy₀ with ⟨p, hp, hlast, hmem, hadj⟩
    refine ⟨p.map back, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg (Option.map back) hp
    · simpa using congrArg (Option.map back) hlast
    · intro z hz
      simp only [List.mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, hmem w hw, rfl⟩
    · intro a b l₁ l₂ he
      have he' : p = l₁.map turn ++ turn a :: turn b :: l₂.map turn := by
        have hh := congrArg (List.map turn) he
        simpa [List.map_append, Function.comp_def, back_turn] using hh
      have hadj' := hadj (turn a) (turn b) (l₁.map turn) (l₂.map turn) he'
      rcases back_neighbor (turn a) (turn b) hadj' with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (by simpa [back_turn, turn_back] using h)))
      · exact Or.inr (Or.inr (Or.inl (by simpa [back_turn, turn_back] using h)))
      · exact Or.inl (by simpa [back_turn, turn_back] using h)
      · exact Or.inr (Or.inl (by simpa [back_turn, turn_back] using h))

private theorem hDmax :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (ring : ProtoTile), ((↑T.cells : Set GaussianInt).Finite ∧ (↑T.cells
            : Set GaussianInt) ⊆ (↑ring.cells : Set GaussianInt)ᶜ ∧ ((↑T.cells : Set
            GaussianInt).Nonempty ∧ ∀ x ∈ (↑T.cells : Set GaussianInt), ∀ y ∈ (↑T.cells : Set
            GaussianInt), ∃ (p : List GaussianInt), p.head? = some x ∧ p.getLast? = some y ∧ (∀ z
            ∈ p, z ∈ (↑T.cells : Set GaussianInt)) ∧ ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀
            (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ → b = a +
            (1 : GaussianInt) ∨ b = a - (1 : GaussianInt) ∨ b = a + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∨ b = a - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∧ (∀ (D : Set
            GaussianInt), (D.Nonempty ∧ ∀ x ∈ D, ∀ y ∈ D, ∃ (p : List GaussianInt), p.head? =
            some x ∧ p.getLast? = some y ∧ (∀ z ∈ p, z ∈ D) ∧ ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b
            :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 : GaussianInt) ∨ b = a + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∨ b = a - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (↑T.cells : Set
            GaussianInt) ⊆ D → D ⊆ (↑ring.cells : Set GaussianInt)ᶜ → D = (↑T.cells : Set
            GaussianInt)) ∧ ∀ (D : Set GaussianInt), D.Finite → D ⊆ (↑ring.cells : Set
            GaussianInt)ᶜ → (D.Nonempty ∧ ∀ x ∈ D, ∀ y ∈ D, ∃ (p : List GaussianInt), p.head? =
            some x ∧ p.getLast? = some y ∧ (∀ z ∈ p, z ∈ D) ∧ ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b
            :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 : GaussianInt) ∨ b = a + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∨ b = a - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (∀ (E : Set
            GaussianInt), (E.Nonempty ∧ ∀ x ∈ E, ∀ y ∈ E, ∃ (p : List GaussianInt), p.head? =
            some x ∧ p.getLast? = some y ∧ (∀ z ∈ p, z ∈ E) ∧ ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b
            :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 : GaussianInt) ∨ b = a + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∨ b = a - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → D ⊆ E → E ⊆
            (↑ring.cells : Set GaussianInt)ᶜ → E = D) → D = (↑T.cells : Set GaussianInt)) → (∀ (u
            : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let back (x : GaussianInt) : GaussianInt :=
          ⟨x.im - u.im, -x.re - 1 + u.re⟩
        (∀ (x : GaussianInt), back (turn x) = x) → ((∀ (x : GaussianInt), turn (back x) = x) →
            (((ring.cells.image turn : Set GaussianInt) = (ring.cells : Set GaussianInt)) → (
        let gridConnected := fun S : Set GaussianInt =>
          S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ p : List GaussianInt,
            p.head? = some x ∧ p.getLast? = some y ∧
            (∀ z ∈ p, z ∈ S) ∧
            ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
              p = l₁ ++ a :: b :: l₂ →
                b = a + 1 ∨ b = a - 1 ∨
                  b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩
        let D : Set GaussianInt := turn '' (T.cells : Set GaussianInt)
        (∀ (S : Set GaussianInt), (gridConnected S) → (gridConnected (S.image back))) → (∀ E :
            Set GaussianInt, gridConnected E → D ⊆ E → E ⊆ (ring.cells : Set GaussianInt)ᶜ → E =
            D))))) ) := by
  classical
  intro T ring hUnique u turn back turn_back back_turn hRingImage gridConnected D
      mapBackConnected E hE hDE hEcomp
  let E' : Set GaussianInt := E.image back
  have hEconn : gridConnected E' := mapBackConnected E hE
  have hEcomp' : E' ⊆ (ring.cells : Set GaussianInt)ᶜ := by
    intro x hx hxr
    rcases hx with ⟨y, hy, rfl⟩
    have htr : turn (back y) ∈ (ring.cells : Set GaussianInt) := by
      rw [← hRingImage]
      exact Finset.mem_image.mpr ⟨back y, hxr, rfl⟩
    apply hEcomp hy
    simpa [back_turn] using htr
  have hTsub : (T.cells : Set GaussianInt) ⊆ E' := by
    intro x hx
    have htx : turn x ∈ D := by
      change turn x ∈ turn '' (T.cells : Set GaussianInt)
      exact ⟨x, hx, rfl⟩
    have hex : turn x ∈ E := hDE htx
    exact ⟨turn x, hex, by simp [turn_back]⟩
  have hEq : E' = (T.cells : Set GaussianInt) :=
    hUnique.2.2.2.1 E' hEconn hTsub hEcomp'
  ext x
  constructor
  · intro hx
    have hx' : back x ∈ E' := ⟨x, hx, rfl⟩
    have hb : back x ∈ (T.cells : Set GaussianInt) := by rw [← hEq]; exact hx'
    exact ⟨back x, hb, by simp [back_turn]⟩
  · intro hx
    exact hDE hx

private theorem hCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let turn (x : GaussianInt) : GaussianInt :=
          ⟨-x.im - 1 + u.re, x.re + u.im⟩
        let D : Set GaussianInt := turn '' (T.cells : Set GaussianInt)
        (D = (T.cells : Set GaussianInt)) → ((TileTranslation (TileQuarterTurn T) u).cells =
            T.cells) ) := by
  classical
  intro T u turn D hD_eq
  rw [TileTranslationFormulas (TileQuarterTurn T) u |>.1,
    TileQuarterTurnFormulas T |>.1]
  have hfin : T.cells.image turn = T.cells := by
    apply Finset.ext
    intro x
    have hx := Set.ext_iff.mp hD_eq x
    change x ∈ turn '' (T.cells : Set GaussianInt) ↔ x ∈ (T.cells : Set GaussianInt) at hx
    simpa using hx
  rw [Finset.image_image]
  have hfun : (GaussianTranslation u) ∘ (fun x => GaussianQuarterTurn x - 1) = turn := by
    funext x
    rcases x with ⟨a, b⟩
    apply Zsqrtd.ext_iff.mpr; simp [GaussianTranslation, GaussianQuarterTurn, turn]
  rw [hfun, hfin]

private theorem hcent :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ((TileTranslation (TileQuarterTurn T) u).cells =
            T.cells) → ((Finset.Nonempty T.cells) → (TileCentroid (TileTranslation
            (TileQuarterTurn T) u) = TileCentroid T)) ) := by
  classical
  intro T u hCells hne
  simp [TileCentroid, hne, hCells]

private theorem hu_re :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), (TileCentroid (TileTranslation (TileQuarterTurn
            T) u) = TileCentroid T) → ((u.re : Real) = (TileCentroid T).1 + (TileCentroid T).2) )
            := by
  classical
  intro T u hcent
  have h := congrArg Prod.fst hcent
  rw [TileTranslationFormulas (TileQuarterTurn T) u |>.2.2.2.2.1] at h
  rw [TileQuarterTurnFormulas T |>.2.2.2.2.1] at h
  dsimp at h
  linarith

private theorem hu_im :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), (TileCentroid (TileTranslation (TileQuarterTurn
            T) u) = TileCentroid T) → ((u.im : Real) = (TileCentroid T).2 - (TileCentroid T).1) )
            := by
  classical
  intro T u hcent
  have h := congrArg Prod.snd hcent
  rw [TileTranslationFormulas (TileQuarterTurn T) u |>.2.2.2.2.1] at h
  rw [TileQuarterTurnFormulas T |>.2.2.2.2.1] at h
  dsimp at h
  linarith

private theorem hreal :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ((TileTranslation (TileQuarterTurn T) u).cells =
            T.cells) → (TileRealization (TileTranslation (TileQuarterTurn T) u) = TileRealization
            T) ) := by
  classical
  intro T u hCells
  rw [TileRealization, hCells, TileRealization]

private theorem hset :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let rotate (p : Real × Real) : Real × Real :=
          (-(p.2) + (u.re : Real), p.1 + (u.im : Real))
        (TileRealization (TileTranslation (TileQuarterTurn T) u) = TileRealization T) →
            (TileRealization T = rotate '' TileRealization T) ) := by
  classical
  intro T u rotate hreal
  have hf : (fun p : Real × Real =>
      ((-p.2, p.1).1 + (u.re : Real), (-p.2, p.1).2 + (u.im : Real))) =
      rotate := by
    funext p
    simp [rotate]
  calc
    TileRealization T = TileRealization (TileTranslation (TileQuarterTurn T) u) := hreal.symm
    _ = (fun p : Real × Real => (p.1 + (u.re : Real), p.2 + (u.im : Real))) ''
        ((fun p : Real × Real => (-p.2, p.1)) '' TileRealization T) := by
          rw [TileTranslationFormulas (TileQuarterTurn T) u |>.2.2.2.1,
            TileQuarterTurnFormulas T |>.2.2.2.1]
    _ = rotate '' TileRealization T := by
          rw [Set.image_image, hf]

private theorem hrotate :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ((u.re : Real) = (TileCentroid T).1 +
            (TileCentroid T).2) → (((u.im : Real) = (TileCentroid T).2 - (TileCentroid T).1) → (
        let rotate (p : Real × Real) : Real × Real :=
          (-(p.2) + (u.re : Real), p.1 + (u.im : Real))
        ∀ (p : Real × Real), rotate p = ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
            (TileCentroid T).2 + (p.1 - (TileCentroid T).1)))) ) := by
  classical
  intro T u hu_re hu_im rotate p
  apply Prod.ext <;> dsimp [rotate]
  · rw [hu_re]
    ring
  · rw [hu_im]
    ring

private theorem hleft :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
        let rotate (p : Real × Real) : Real × Real :=
          (-(p.2) + (u.re : Real), p.1 + (u.im : Real))
        let unrotate (p : Real × Real) : Real × Real :=
          (p.2 - (u.im : Real), -p.1 + (u.re : Real))
        ∀ (p : Real × Real), unrotate (rotate p) = p ) := by
  classical
  intro u rotate unrotate p
  apply Prod.ext <;> dsimp [rotate, unrotate]
  · linarith [hu_re, hu_im]
  · linarith [hu_re, hu_im]

private theorem hforward :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let rotate (p : Real × Real) : Real × Real :=
          (-(p.2) + (u.re : Real), p.1 + (u.im : Real))
        (TileRealization T = rotate '' TileRealization T) → (∀ (p : Real × Real), (p ∈
            TileRealization T) → (rotate p ∈ TileRealization T)) ) := by
  classical
  intro T u rotate hset p hp
  rw [hset]
  exact ⟨p, hp, rfl⟩

private theorem hback :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let rotate (p : Real × Real) : Real × Real :=
          (-(p.2) + (u.re : Real), p.1 + (u.im : Real))
        (TileRealization T = rotate '' TileRealization T) → (
        let unrotate (p : Real × Real) : Real × Real :=
          (p.2 - (u.im : Real), -p.1 + (u.re : Real))
        (∀ (p : Real × Real), unrotate (rotate p) = p) → (∀ (p : Real × Real), (p ∈
            TileRealization T) → (unrotate p ∈ TileRealization T))) ) := by
  classical
  intro T u rotate hset unrotate hleft p hp
  have hp' : p ∈ rotate '' TileRealization T := hset ▸ hp
  rcases hp' with ⟨z, hz, hzp⟩
  have heq : unrotate p = z := by
    rw [← hzp]
    exact hleft z
  rw [heq]
  exact hz

end QuarterTurnTileGeometry

theorem TileT2QuarterTurn (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    QuarterTurnSymmetric T := by
-- BODY
  classical
  obtain ⟨R, ring, h00, h01, h02, h03, h10, h11, h12, h13,
    h20, h21, h22, h23, hUnion, hRing, hUnique⟩ :=
    BandTwelveParentSurround q cfg C₀ T cert
  obtain ⟨u, hu, hRingCells, hRingEmpty, hRingVertices, hRingCentroid⟩ :=
    QuarterTurnSymmetricCenteredTransport ring hRing
  let turn (x : GaussianInt) : GaussianInt :=
    ⟨-x.im - 1 + u.re, x.re + u.im⟩
  have turn_back (x : GaussianInt) := QuarterTurnTileGeometry.turn_back u x
  have back_turn (x : GaussianInt) := QuarterTurnTileGeometry.back_turn u x
  have hRingImage := QuarterTurnTileGeometry.hRingImage ring u hRingCells
  dsimp [UniqueBoundedGridComplementComponent] at hUnique
  let gridConnected := fun S : Set GaussianInt =>
    S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ p : List GaussianInt,
      p.head? = some x ∧ p.getLast? = some y ∧
      (∀ z ∈ p, z ∈ S) ∧
      ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ →
          b = a + 1 ∨ b = a - 1 ∨
            b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩
  have hTFinite : (T.cells : Set GaussianInt).Finite := hUnique.1
  have hTComp : (T.cells : Set GaussianInt) ⊆ (ring.cells : Set GaussianInt)ᶜ := hUnique.2.1
  have hTConnected : gridConnected (T.cells : Set GaussianInt) := hUnique.2.2.1
  have turn_neighbor (a b : GaussianInt)
      (h : b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) :=
          QuarterTurnTileGeometry.turn_neighbor u a b h
  have back_neighbor (a b : GaussianInt)
      (h : b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) :=
          QuarterTurnTileGeometry.back_neighbor u a b h
  let D : Set GaussianInt := turn '' (T.cells : Set GaussianInt)
  have hDfinite : D.Finite := by
    simpa [D] using hTFinite.image turn
  have hDcomp := QuarterTurnTileGeometry.hDcomp T ring u turn_back hRingImage hTComp
  have hDConnected := QuarterTurnTileGeometry.hDConnected T u turn_back back_turn hTConnected
      turn_neighbor
  have mapBackConnected (S : Set GaussianInt) (hS : gridConnected S) :=
      QuarterTurnTileGeometry.mapBackConnected u turn_back back_turn back_neighbor S hS
  have hDmax := QuarterTurnTileGeometry.hDmax T ring hUnique u turn_back back_turn hRingImage
      mapBackConnected
  have hD_eq : D = (T.cells : Set GaussianInt) :=
    hUnique.2.2.2.2 D hDfinite hDcomp hDConnected hDmax
  have hCells := QuarterTurnTileGeometry.hCells T u hD_eq
  by_cases hne : T.cells.Nonempty
  · have hcent := QuarterTurnTileGeometry.hcent T u hCells hne
    have hu_re := QuarterTurnTileGeometry.hu_re T u hcent
    have hu_im := QuarterTurnTileGeometry.hu_im T u hcent
    let rotate (p : Real × Real) : Real × Real :=
      (-(p.2) + (u.re : Real), p.1 + (u.im : Real))
    have hreal := QuarterTurnTileGeometry.hreal T u hCells
    have hset := QuarterTurnTileGeometry.hset T u hreal
    have hrotate (p : Real × Real) :
        rotate p = ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
          (TileCentroid T).2 + (p.1 - (TileCentroid T).1)) := QuarterTurnTileGeometry.hrotate T u
              hu_re hu_im p
    have hleft (p : Real × Real) := QuarterTurnTileGeometry.hleft u p
    have hforward (p : Real × Real) (hp : p ∈ TileRealization T) :=
        QuarterTurnTileGeometry.hforward T u hset p hp
    have hback (p : Real × Real) (hp : p ∈ TileRealization T) := QuarterTurnTileGeometry.hback T
        u hset hleft p hp
    intro p
    change p ∈ TileRealization T ↔
      ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
        (TileCentroid T).2 + (p.1 - (TileCentroid T).1)) ∈ TileRealization T
    rw [← hrotate]
    constructor
    · intro hp
      exact hforward p hp
    · intro hp
      have := hback (rotate p) hp
      convert this using 1
      exact (hleft p).symm
  · have hzero : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    intro p
    simp [TileRealization, hzero]

end ApollonianSuperharmonic

end
