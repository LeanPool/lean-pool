/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.P5203T1IncreasingInterface
public import LeanPool.ApollonianSuperharmonic.P5203T1DecreasingInterface
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.P4055T1GridPathImage
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.DiamondBaseT2
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCentroid

-- [TABLET NODE: P5290T1EqualDiamondPaths]

/-!
# P5290T1EqualDiamondPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondPathComparison

private theorem staircaseBetween :
    (by
      classical
      exact
        (Nat) → (∀ (z : GaussianInt), ∀ (h : Bool), ∀ (s : Int), (s = 1 ∨ s = -1) → (∀ (N : Nat),
            (0 < N) → (
        let p := P5157T1StaircasePoint z h s;
          SimpleGridPathBetween {v | ∃ j ≤ N, v = p j}
            {e | ∃ j < N, e = {p j, p (j + 1)}} (p 0) (p N)))) ) := by
  classical
  intro k z h s hs N hN
  dsimp only
  let p := P5157T1StaircasePoint z h s;
  have inj := (P5157T1AlternatingStaircase z h s hs N hN).1
  have step (j : Nat) :
      p (j + 1) = p j + 1 ∨ p (j + 1) = p j - 1 ∨
      p (j + 1) = p j + ⟨0, 1⟩ ∨ p (j + 1) = p j - ⟨0, 1⟩ := by
    rcases hs with rfl | rfl <;> cases h <;>
      simp [p, P5157T1StaircasePoint, Zsqrtd.ext_iff] <;> omega
  let l := List.ofFn (fun j : Fin (N + 1) => p j)
  have hl : l.length = N + 1 := List.length_ofFn
  have chain : l.IsChain (fun a b => ∃ j < N, a = p j ∧ b = p (j + 1)) := by
    apply List.isChain_ofFn.mpr
    intro j hj
    exact ⟨j, by omega, rfl, rfl⟩
  have consecutive (a b : GaussianInt) (l₁ l₂ : List GaussianInt)
      (heq : l = l₁ ++ a :: b :: l₂) :
      ∃ j < N, a = p j ∧ b = p (j + 1) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp chain heq
  refine ⟨l, List.nodup_ofFn.mpr ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.ext (inj hab)
  · rw [hl]
    omega
  · simp [l]
    rfl
  · change (List.ofFn (fun j : Fin (N + 1) => p j)).getLast? = some (p N)
    rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
    rw [List.getLast_ofFn_succ]
    rfl
  · ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset,
      l, List.mem_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, by omega, rfl⟩
  · intro a b l₁ l₂ heq
    obtain ⟨j, hj, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
    exact step j
  · intro e
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjl : j < l.length := by rw [hl]; omega
      have hlen : j + 1 < l.length := by rw [hl]; omega
      refine ⟨p j, p (j + 1), l.take j, l.drop (j + 2), ?_, rfl⟩
      have hd := List.getElem_cons_drop hjl
      have hd' := List.getElem_cons_drop hlen
      have heq : l = l.take j ++ l[j] :: l[j + 1] :: l.drop (j + 2) := by
        rw [show j + 2 = j + 1 + 1 by omega, hd', hd, List.take_append_drop]
      simpa only [l, List.getElem_ofFn] using heq
    · rintro ⟨a, b, l₁, l₂, heq, rfl⟩
      obtain ⟨j, hj, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
      exact ⟨j, hj, rfl⟩

private abbrev reversePath := @SimpleGridPathBetween.reverse

private theorem qstep :
    (by
      classical
      exact
        (Nat) → (∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
            GaussianQuarterTurn b = GaussianQuarterTurn a + 1 ∨ GaussianQuarterTurn b =
            GaussianQuarterTurn a - 1 ∨ GaussianQuarterTurn b = GaussianQuarterTurn a + ⟨0, 1⟩ ∨
            GaussianQuarterTurn b = GaussianQuarterTurn a - ⟨0, 1⟩) ) := by
  classical
  intro k a b hh
  rcases hh with h | h | h | h
  · subst b; right; right; left; apply Zsqrtd.ext <;>
      simp [GaussianQuarterTurn]
  · subst b; right; right; right; apply Zsqrtd.ext <;>
      simp [GaussianQuarterTurn]
  · subst b; right; left; apply Zsqrtd.ext <;>
      simp [GaussianQuarterTurn]; omega
  · subst b; left; apply Zsqrtd.ext <;>
      simp [GaussianQuarterTurn]; omega

private theorem qinj :
    (by
      classical
      exact
        (Nat) → (Function.Injective GaussianQuarterTurn) ) := by
  classical
  intro k a b hab
  apply Zsqrtd.ext
  · have h := congrArg (fun z : GaussianInt => z.im) hab
    simpa [GaussianQuarterTurn] using h
  · have h := congrArg (fun z : GaussianInt => z.re) hab
    have h' : -a.im = -b.im := by simpa [GaussianQuarterTurn] using h
    omega

private theorem qenum :
    (by
      classical
      exact
        ∀ (k : Nat),
        let q : Nat → GaussianInt :=
          P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
        ∀ (j : ℕ), GaussianQuarterTurn (q j) = ⟨(↑k : ℤ) - (↑(j / (2 : ℕ)) : ℤ), (↑k : ℤ) + (↑((j
            + (1 : ℕ)) / (2 : ℕ)) : ℤ)⟩ ) := by
  classical
  intro k q j
  apply Zsqrtd.ext <;>
    simp [q, P5157T1StaircasePoint, GaussianQuarterTurn]; omega

private theorem qendpoint₀ :
    (by
      classical
      exact
        ∀ (k : Nat),
        let q : Nat → GaussianInt :=
          P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
        (∀ (j : Nat), GaussianQuarterTurn (q j) = ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j +
            1) / 2 : Nat)⟩) → (GaussianQuarterTurn (q 0) = ⟨(k : Int), (k : Int)⟩) ) := by
  classical
  intro k q qenum
  rw [qenum]
  norm_num

private theorem qendpoint₁ :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (
        let q : Nat → GaussianInt :=
          P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
        let N : Nat := 2 * k - 1
        (∀ (j : Nat), GaussianQuarterTurn (q j) = ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j +
            1) / 2 : Nat)⟩) → (GaussianQuarterTurn (q N) = ⟨1, 2 * (k : Int)⟩)) ) := by
  classical
  intro k hk q N qenum
  rw [qenum]
  dsimp [N]
  have heven : (2 * k - 1) / 2 = k - 1 := by omega
  have hceil : (2 * k - 1 + 1) / 2 = k := by omega
  apply Zsqrtd.ext <;> simp <;> omega

private theorem dVenum :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (
        let N : Nat := 2 * k - 1
        (0 < N) → (
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        dV = {z | ∃ j ≤ N, z = dP j})) ) := by
  classical
  intro k hk N hN dV dP
  ext z
  constructor
  · intro hz
    have hz' : 1 ≤ z.re ∧ z.re ≤ k ∧
        2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1 := by
      simpa [dV] using hz
    let j := (z.im - z.re).toNat
    have hj : (j : Int) = z.im - z.re :=
      Int.toNat_of_nonneg (by omega)
    refine ⟨j, ?_, ?_⟩
    · change j ≤ 2 * k - 1
      omega
    · apply Zsqrtd.ext
      · simp [dP]
        omega
      · simp [dP]
        omega
  · rintro ⟨j, hj, rfl⟩
    simp only [dV, Set.mem_ofPred_eq, dP]
    omega

private theorem dVimage :
    (by
      classical
      exact
        ∀ (k : Nat),
        let q : Nat → GaussianInt :=
          P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
        let N : Nat := 2 * k - 1
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        (∀ (j : Nat), GaussianQuarterTurn (q j) = dP j) → ((dV = {z | ∃ j ≤ N, z = dP j}) →
            (GaussianQuarterTurn '' {z | ∃ j ≤ N, z = q j} = dV)) ) := by
  classical
  intro k q N dV dP dq dVenum
  rw [dVenum]
  ext z
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, dq j⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨q j, ⟨j, hj, rfl⟩, dq j⟩

private theorem dEimage :
    (by
      classical
      exact
        ∀ (k : Nat),
        let q : Nat → GaussianInt :=
          P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
        let N : Nat := 2 * k - 1
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        let dE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {dP j, dP (j + 1)}}
        (∀ (j : Nat), GaussianQuarterTurn (q j) = dP j) → ((fun e : Finset GaussianInt => e.image
            GaussianQuarterTurn) '' {e | ∃ j < N, e = {q j, q (j + 1)}} = dE) ) := by
  classical
  intro k q N dP dE dq
  ext e
  constructor
  · rintro ⟨f, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by simp [dq]⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨{q j, q (j + 1)}, ⟨j, hj, rfl⟩, ?_⟩
    simp [dq]

private theorem decPath :
    (by
      classical
      exact
        ∀ (k : Nat),
        let q : Nat → GaussianInt :=
          P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
        let N : Nat := 2 * k - 1
        (SimpleGridPathBetween (GaussianQuarterTurn '' {v : GaussianInt | ∃ j ≤ N, v =
            P5157T1StaircasePoint ⟨(↑k : ℤ), -(↑k : ℤ)⟩ true (1 : ℤ) j}) ((fun (e : Finset
            GaussianInt) => Finset.image GaussianQuarterTurn e) '' {e : Finset GaussianInt | ∃ j
            < N, e = {P5157T1StaircasePoint ⟨(↑k : ℤ), -(↑k : ℤ)⟩ true (1 : ℤ) j,
            P5157T1StaircasePoint ⟨(↑k : ℤ), -(↑k : ℤ)⟩ true (1 : ℤ) (j + (1 : ℕ))}})
            (GaussianQuarterTurn (P5157T1StaircasePoint ⟨(↑k : ℤ), -(↑k : ℤ)⟩ true (1 : ℤ) (0 :
            ℕ))) (GaussianQuarterTurn (P5157T1StaircasePoint ⟨(↑k : ℤ), -(↑k : ℤ)⟩ true (1 : ℤ)
            N))) → ((GaussianQuarterTurn (q 0) = ⟨(k : Int), (k : Int)⟩) → ((GaussianQuarterTurn
            (q N) = ⟨1, 2 * (k : Int)⟩) → (
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        let dE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {dP j, dP (j + 1)}}
        (GaussianQuarterTurn '' {z | ∃ j ≤ N, z = q j} = dV) → (((fun e : Finset GaussianInt =>
            e.image GaussianQuarterTurn) '' {e | ∃ j < N, e = {q j, q (j + 1)}} = dE) →
            (SimpleGridPathBetween dV dE ⟨(k : Int), (k : Int)⟩ ⟨1, 2 * (k : Int)⟩))))) ) := by
  classical
  intro k q N qImagePath qendpoint₀ qendpoint₁ dV dP dE dVimage dEimage
  have h := qImagePath
  rw [dVimage, dEimage, qendpoint₀, qendpoint₁] at h
  exact h

private theorem dzero :
    (by
      classical
      exact
        ∀ (k : Nat), TileTranslation (DiamondTile k) 0 = DiamondTile k ) := by
  classical
  intro k
  change (⟨(DiamondCellDomain k).image (GaussianTranslation 0),
      GaussianTranslation 0 0⟩ : ProtoTile) = ⟨DiamondCellDomain k, 0⟩
  simp only [ProtoTile.mk.injEq]
  constructor
  · have hfun : GaussianTranslation 0 = id := by
      funext z
      simp [GaussianTranslation]
    rw [hfun, Finset.image_id]
  · simp [GaussianTranslation]

private theorem decVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) ((0 : GaussianInt) + ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩)) = {z :
            GaussianInt | (1 : ℤ) ≤ (z - (0 : GaussianInt)).re ∧ (z - (0 : GaussianInt)).re ≤ (↑k
            : ℤ) ∧ (2 : ℤ) * (↑k : ℤ) ≤ (z - (0 : GaussianInt)).re + (z - (0 : GaussianInt)).im ∧
            (z - (0 : GaussianInt)).re + (z - (0 : GaussianInt)).im ≤ (2 : ℤ) * (↑k : ℤ) + (1 :
            ℤ)}) → (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩) = dV) ) := by
  classical
  intro k dV dvertices
  simpa [dV] using dvertices

private theorem decEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        let dE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {dP j, dP (j + 1)}}
        (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ((0 : GaussianInt) + ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩)) = {e : Finset
            GaussianInt | ∃ j < (2 : ℕ) * k - (1 : ℕ), e =
            {(0 : GaussianInt) + ⟨(↑k : ℤ) - (↑(j / (2 : ℕ)) : ℤ),
            (↑k : ℤ) + (↑((j + (1 : ℕ)) / (2 : ℕ)) : ℤ)⟩, (0 : GaussianInt) + ⟨(↑k : ℤ) - (↑((j +
            (1 : ℕ)) / (2 : ℕ)) : ℤ), (↑k : ℤ) + (↑((j + (1 : ℕ) + (1 : ℕ)) / (2 : ℕ)) : ℤ)⟩}}) →
            (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩) = dE) ) := by
  classical
  intro k N dP dE dedges
  simpa [dE, dP, N] using dedges

private theorem decBetween :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        let dE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {dP j, dP (j + 1)}}
        (SimpleGridPathBetween dV dE ⟨(k : Int), (k : Int)⟩ ⟨1, 2 * (k : Int)⟩) →
            ((BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩) = dV) →
            ((BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩) = dE) → (SimpleGridPathBetween
            (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩)) (BoundaryFootprintEdges
            (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation (DiamondTile k) ⟨(k : Int)
            + 1, (k : Int)⟩)) ⟨(k : Int), (k : Int)⟩ ⟨1, 2 * (k : Int)⟩))) ) := by
  classical
  intro k N dV dP dE decPath decVertices decEdges
  rw [decVertices, decEdges]
  exact decPath

private theorem iVenum :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (
        let N : Nat := 2 * k - 1
        (0 < N) → (
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        iV = {z | ∃ j ≤ N, z = iP j})) ) := by
  classical
  intro k hk N hN iV iP
  ext z
  constructor
  · intro hz
    have hz' : 1 ≤ z.re ∧ z.re ≤ k ∧
        z.re - 1 ≤ z.im ∧ z.im ≤ z.re := by simpa [iV] using hz
    let j := (z.re + z.im - 1).toNat
    have hj : (j : Int) = z.re + z.im - 1 :=
      Int.toNat_of_nonneg (by omega)
    refine ⟨j, ?_, ?_⟩
    · change j ≤ 2 * k - 1
      omega
    · apply Zsqrtd.ext
      · simp [iP]
        omega
      · simp [iP]
        omega
  · rintro ⟨j, hj, rfl⟩
    simp only [iV, Set.mem_ofPred_eq, iP]
    omega

private theorem iEeq :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        let iq : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
        (∀ (j : Nat), iq j = iP j) → (iE = {e | ∃ j < N, e = {iq j, iq (j + 1)}}) ) := by
  classical
  intro k N iP iE iq iqenum
  ext e
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, by simp [iqenum]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, by simp [iqenum]⟩

private theorem incEnumPath :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → ((∀ (z : GaussianInt), ∀ (h : Bool), ∀ (s : Int), (s = 1 ∨ s
            = -1) → (∀ (N : Nat), (0 < N) → (
        let p := P5157T1StaircasePoint z h s;
          SimpleGridPathBetween {v | ∃ j ≤ N, v = p j}
            {e | ∃ j < N, e = {p j, p (j + 1)}} (p 0) (p N)))) → (
        let N : Nat := 2 * k - 1
        (0 < N) → (
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        (iV = {z | ∃ j ≤ N, z = iP j}) → (SimpleGridPathBetween iV iE ⟨1, 0⟩ ⟨(k : Int), (k :
            Int)⟩)))) ) := by
  classical
  intro k hk staircaseBetween N hN iV iP iE iVenum
  have hpi (j : Nat) : P5157T1StaircasePoint 1 false 1 j = iP j := by
    apply Zsqrtd.ext <;> simp [P5157T1StaircasePoint, iP]
  have hp := staircaseBetween 1 false 1 (Or.inl rfl) N hN
  have hp' : SimpleGridPathBetween {v | ∃ j ≤ N, v = iP j}
      {e | ∃ j < N, e = {iP j, iP (j + 1)}} (iP 0) (iP N) := by
    simpa only [hpi] using hp
  have hEi : iE = {e | ∃ j < N, e = {iP j, iP (j + 1)}} := by
    rfl
  have iend : iP N = ⟨(k : Int), (k : Int)⟩ := by
    apply Zsqrtd.ext <;> simp [iP, N] <;> omega
  rw [← iVenum, ← hEi] at hp'
  rw [iend] at hp'
  simpa [iP] using hp'

private theorem incVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) ((0 : GaussianInt) + ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩)) = {z :
            GaussianInt | (1 : ℤ) ≤ (z - (0 : GaussianInt)).re ∧ (z - (0 : GaussianInt)).re ≤ (↑k
            : ℤ) ∧ (z - (0 : GaussianInt)).re - (1 : ℤ) ≤ (z - (0 : GaussianInt)).im ∧ (z - (0 :
            GaussianInt)).im ≤ (z - (0 : GaussianInt)).re}) → (BoundaryFootprintVertices
            (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile k) ⟨(k :
            Int) + 1, -(k : Int)⟩) = iV) ) := by
  classical
  intro k iV ivertex0
  simpa [iV] using ivertex0

private theorem incEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ((0 : GaussianInt) + ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩)) = {e : Finset
            GaussianInt | ∃ j < (2 : ℕ) * k - (1 : ℕ), e =
            {(0 : GaussianInt) + ⟨(1 : ℤ) + (↑(j / (2 : ℕ)) : ℤ),
            (↑((j + (1 : ℕ)) / (2 : ℕ)) : ℤ)⟩, (0 : GaussianInt) + ⟨(1 : ℤ) + (↑((j + (1 : ℕ)) /
            (2 : ℕ)) : ℤ), (↑((j + (1 : ℕ) + (1 : ℕ)) / (2 : ℕ)) : ℤ)⟩}}) →
            (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩) = iE) ) := by
  classical
  intro k N iP iE iedge0
  simpa [iE, iP, N] using iedge0

private theorem incBetween :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        (SimpleGridPathBetween iV iE ⟨1, 0⟩ ⟨(k : Int), (k : Int)⟩) → ((BoundaryFootprintVertices
            (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile k) ⟨(k :
            Int) + 1, -(k : Int)⟩) = iV) → ((BoundaryFootprintEdges (DiamondTile k) ∩
            BoundaryFootprintEdges (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩)
            = iE) → (SimpleGridPathBetween (BoundaryFootprintVertices (DiamondTile k) ∩
            BoundaryFootprintVertices (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, -(k :
            Int)⟩)) (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩)) ⟨1, 0⟩ ⟨(k : Int), (k
            : Int)⟩))) ) := by
  classical
  intro k N iV iP iE incEnumPath incVertices incEdges
  rw [incVertices, incEdges]
  exact incEnumPath

private theorem dzeroD' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        TileTranslation D ⟨0, 0⟩ = D ) := by
  classical
  intro k D
  change (⟨(DiamondCellDomain k).image
      (GaussianTranslation ⟨0, 0⟩),
      GaussianTranslation ⟨0, 0⟩ 0⟩ : ProtoTile) =
    ⟨DiamondCellDomain k, 0⟩
  simp only [ProtoTile.mk.injEq]
  have hzero : (⟨0, 0⟩ : GaussianInt) = 0 := rfl
  constructor
  · have hfun : GaussianTranslation ⟨0, 0⟩ = id := by
      funext z
      simp [GaussianTranslation, hzero]
    rw [hfun, Finset.image_id]
  · simp [GaussianTranslation, hzero]

private theorem hcEq :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (
        let D := DiamondTile k
        ∀ (c : GaussianInt), (GaussianRealPoint c = ((TileCentroid D).1 + (TileCentroid D).2,
            (TileCentroid D).2 - (TileCentroid D).1)) → (c = ⟨(k : Int), (k : Int)⟩)) ) := by
  classical
  intro k hk D c hc
  have hcent := P4194T1DiamondCentroid k hk
  rw [hcent] at hc
  simp only [GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
      zero_add, sub_zero, Prod.mk.injEq] at hc
  rcases hc with ⟨hr, hi⟩
  apply Zsqrtd.ext
  · rw [← GaussianInt.intCast_re c] at hr
    exact_mod_cast hr
  · rw [← GaussianInt.intCast_im c] at hi
    exact_mod_cast hi

private theorem F_inj :
    (by
      classical
      exact
        (Function.Injective GaussianQuarterTurn) → (
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        Function.Injective F) ) := by
  classical
  intro qinj Q c F a b hab
  apply qinj
  exact add_right_cancel hab

private theorem F_cell_inj :
    (by
      classical
      exact
        (Function.Injective GaussianQuarterTurn) → (
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        Function.Injective Fc) ) := by
  classical
  intro qinj Q c Fc a b hab
  have hq : Q a = Q b := by
    have := add_right_cancel (show Q a - 1 + c = Q b - 1 + c from hab)
    exact add_right_cancel (show Q a - 1 = Q b - 1 from this)
  exact qinj hq

private theorem F_step :
    (by
      classical
      exact
        (Nat) → (
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        ∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → F b = F
            a + 1 ∨ F b = F a - 1 ∨ F b = F a + ⟨0, 1⟩ ∨ F b = F a - ⟨0, 1⟩) ) := by
  classical
  intro k Q c F a b hh
  rcases hh with h | h | h | h
  · subst b; right; right; left; apply Zsqrtd.ext <;>
      simp [F, Q, GaussianQuarterTurn]; omega
  · subst b; right; right; right; apply Zsqrtd.ext <;>
      simp [F, Q, GaussianQuarterTurn]; omega
  · subst b; right; left; apply Zsqrtd.ext <;>
      simp [F, Q, GaussianQuarterTurn]; omega
  · subst b; left; apply Zsqrtd.ext <;>
      simp [F, Q, GaussianQuarterTurn]; omega

private theorem translateCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (TileTranslation T (u +
            v)).cells = (TileTranslation (TileTranslation T u) v).cells ) := by
  classical
  intro T u v
  rw [(TileTranslationFormulas T (u + v)).1,
    (TileTranslationFormulas (TileTranslation T u) v).1,
    (TileTranslationFormulas T u).1]
  rw [Finset.image_image]
  congr 1
  funext z
  simp [GaussianTranslation, add_comm, add_left_comm]

private theorem quarterCells :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt), ((TileTranslation (TileQuarterTurn D) ⟨(↑k : ℤ), (↑k : ℤ)⟩).cells =
            D.cells) → ((c = ⟨(↑k : ℤ), (↑k : ℤ)⟩) → ((∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀
            (v : GaussianInt), (TileTranslation T (u + v)).cells = (TileTranslation
            (TileTranslation T u) v).cells) → (∀ (d : GaussianInt), (TileTranslation D (Q
            d)).cells = (TileTranslation (TileQuarterTurn D) (c + Q d)).cells))) ) := by
  classical
  intro k D Q c hcCells hcEq translateCells d
  rw [translateCells (TileQuarterTurn D) c (Q d)]
  rw [(TileTranslationFormulas D (Q d)).1,
    (TileTranslationFormulas (TileTranslation (TileQuarterTurn D) c) (Q d)).1,
    hcEq, hcCells]

private theorem quarterCellMap :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells = (TileTranslation (TileQuarterTurn
            D) (c + Q d)).cells) → (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells =
            Finset.image Fc (TileTranslation D d).cells) ) := by
  classical
  intro k D Q c Fc quarterCells d
  rw [quarterCells d,
    (TileTranslationFormulas (TileQuarterTurn D) (c + Q d)).1,
    (TileQuarterTurnFormulas D).1,
    (TileTranslationFormulas D d).1]
  simp only [Finset.image_image]
  congr 1
  funext z
  apply Zsqrtd.ext <;>
    simp [Fc, Q, GaussianTranslation, GaussianQuarterTurn] <;> ring

private theorem edgeCellsEq :
    (by
      classical
      exact
        ∀ {A : ProtoTile}, ∀ {B : ProtoTile}, A.cells = B.cells → BoundaryFootprintEdges A =
            BoundaryFootprintEdges B ) := by
  classical
  intro A B hab
  unfold BoundaryFootprintEdges
  rw [hab]

private theorem vertexCellsEq :
    (by
      classical
      exact
        ∀ {A : ProtoTile}, ∀ {B : ProtoTile}, A.cells = B.cells → Finset.Nonempty B.cells →
            BoundaryFootprintVertices A = BoundaryFootprintVertices B ) := by
  classical
  intro A B hab hne
  have hneA : A.cells.Nonempty := by rw [hab]; exact hne
  simp only [BoundaryFootprintVertices, ite_eq_left hneA, ite_eq_left hne]
  unfold BoundaryFootprintEdges
  rw [hab]

private theorem hDne :
    (by
      classical
      exact
        ∀ (k : Nat), (Finset.Nonempty (TileTranslation (DiamondTile k) (0 : GaussianInt)).cells)
            → ((TileTranslation (DiamondTile k) (0 : GaussianInt) = DiamondTile k) → (
        let D := DiamondTile k
        D.cells.Nonempty)) ) := by
  classical
  intro k dne dzero D
  have hn := dne
  rw [dzero] at hn
  exact hn

private theorem translatedDne :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (D.cells.Nonempty) → (∀ (d : GaussianInt), Finset.Nonempty (TileTranslation D d).cells) )
            := by
  classical
  intro k D hDne d
  rw [(TileTranslationFormulas D d).1]
  exact hDne.image _

private theorem quarterTranslatedDne :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt), (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells =
            (TileTranslation (TileQuarterTurn D) (c + Q d)).cells) → ((∀ (d : GaussianInt),
            (TileTranslation D d).cells.Nonempty) → (∀ (d : GaussianInt), Finset.Nonempty
            (TileTranslation (TileQuarterTurn D) (c + Q d)).cells)) ) := by
  classical
  intro k D Q c quarterCells translatedDne d
  rw [← quarterCells d]
  exact translatedDne (Q d)

private theorem quarterVerticesAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells = (TileTranslation (TileQuarterTurn
            D) (c + Q d)).cells) → ((∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (A.cells = B.cells) →
            ((B.cells.Nonempty) → (BoundaryFootprintVertices A = BoundaryFootprintVertices B))) →
            ((∀ (d : GaussianInt), (TileTranslation (TileQuarterTurn D) (c + Q
            d)).cells.Nonempty) → (∀ (d : GaussianInt), BoundaryFootprintVertices
            (TileTranslation D (Q d)) = F '' BoundaryFootprintVertices (TileTranslation D d)))) )
            := by
  classical
  intro k D Q c F quarterCells vertexCellsEq quarterTranslatedDne d
  rw [vertexCellsEq (quarterCells d) (quarterTranslatedDne d),
    (TileTranslationFormulas (TileQuarterTurn D) (c + Q d)).2.2.2.2.2.2.2.1,
    (TileQuarterTurnFormulas D).2.2.2.2.2.2.2.1,
    (TileTranslationFormulas D d).2.2.2.2.2.2.2.1]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  simp [F, GaussianTranslation, GaussianQuarterTurn, Q, add_assoc,
    add_comm]

private theorem quarterEdgesAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells = (TileTranslation (TileQuarterTurn
            D) (c + Q d)).cells) → ((∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (A.cells = B.cells) →
            (BoundaryFootprintEdges A = BoundaryFootprintEdges B)) → (∀ (d : GaussianInt),
            BoundaryFootprintEdges (TileTranslation D (Q d)) = (fun (e : Finset GaussianInt) =>
            Finset.image F e) '' BoundaryFootprintEdges (TileTranslation D d))) ) := by
  classical
  intro k D Q c F quarterCells edgeCellsEq d
  rw [edgeCellsEq (quarterCells d),
    (TileTranslationFormulas (TileQuarterTurn D) (c + Q d)).2.2.2.2.2.2.2.2,
    (TileQuarterTurnFormulas D).2.2.2.2.2.2.2.2,
    (TileTranslationFormulas D d).2.2.2.2.2.2.2.2]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext e
  ext z
  simp [F, GaussianTranslation, GaussianQuarterTurn, Q,
    Finset.image_image, add_assoc, add_comm]

private theorem dShift :
    (by
      classical
      exact
        ∀ (k : Nat),
        let Q := GaussianQuarterTurn
        Q ⟨(k : Int) + 1, (k : Int)⟩ = ⟨-(k : Int), (k : Int) + 1⟩ ) := by
  classical
  intro k Q
  apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn]

private theorem firstTurn :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt),
            (Function.Injective f) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0,
            1⟩ ∨ b = a - ⟨0, 1⟩) → f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a
            - ⟨0, 1⟩) → ((SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun
            e : Finset GaussianInt => e.image f) '' E) (f x) (f y))))) → ((SimpleGridPathBetween
            (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩)) (BoundaryFootprintEdges
            (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation (DiamondTile k) ⟨(k : Int)
            + 1, (k : Int)⟩)) ⟨(k : Int), (k : Int)⟩ ⟨1, 2 * (k : Int)⟩) → (
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        (TileTranslation D 0 = D) → (∀ (c : GaussianInt), (c = ⟨(↑k : ℤ), (↑k : ℤ)⟩) → (
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (Function.Injective F) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨
            b = a - ⟨0, 1⟩) → F b = F a + 1 ∨ F b = F a - 1 ∨ F b = F a + ⟨0, 1⟩ ∨ F b = F a -
            ⟨0, 1⟩) → ((∀ (d : GaussianInt), BoundaryFootprintVertices (TileTranslation D (Q d))
            = F '' BoundaryFootprintVertices (TileTranslation D d)) → ((∀ (d : GaussianInt),
            BoundaryFootprintEdges (TileTranslation D (Q d)) = (fun e : Finset GaussianInt =>
            e.image F) '' BoundaryFootprintEdges (TileTranslation D d)) → ((Q ⟨(k : Int) + 1, (k
            : Int)⟩ = ⟨-(k : Int), (k : Int) + 1⟩) → (SimpleGridPathBetween
            (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D ⟨-(k :
            Int), (k : Int) + 1⟩)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩)) ⟨0, 2 * (k : Int)⟩ ⟨-(k : Int), (k :
            Int) + 1⟩))))))))) ) := by
  classical
  intro k imagePath decBetween D Q dzeroD c hcEq F F_inj F_step quarterVerticesAt quarterEdgesAt
      dShift
  have h := imagePath F F_inj F_step decBetween
  have eF : Function.Injective
      (fun e : Finset GaussianInt => e.image F) := Finset.image_injective F_inj
  have q0 : Q 0 = (0 : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn]
  have qv0 : BoundaryFootprintVertices D =
      F '' BoundaryFootprintVertices D := by
    simpa [D, Q, GaussianQuarterTurn, dzeroD, dzeroD', q0] using quarterVerticesAt 0
  have qe0 : BoundaryFootprintEdges D =
      (fun e : Finset GaussianInt => e.image F) ''
        BoundaryFootprintEdges D := by
    simpa [D, Q, GaussianQuarterTurn, dzeroD, dzeroD', q0] using quarterEdgesAt 0
  have qvA : BoundaryFootprintVertices
      (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) =
      F '' BoundaryFootprintVertices
        (TileTranslation D ⟨(k : Int) + 1, (k : Int)⟩) := by
    rw [← dShift]
    exact quarterVerticesAt _
  have qeA : BoundaryFootprintEdges
      (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) =
      (fun e : Finset GaussianInt => e.image F) ''
        BoundaryFootprintEdges
          (TileTranslation D ⟨(k : Int) + 1, (k : Int)⟩) := by
    rw [← dShift]
    exact quarterEdgesAt _
  rw [Set.image_inter F_inj, Set.image_inter eF,
    ← qv0, ← qvA, ← qe0, ← qeA] at h
  have hstart : F ⟨(k : Int), (k : Int)⟩ = ⟨0, 2 * (k : Int)⟩ := by
    apply Zsqrtd.ext <;> simp [F, Q, GaussianQuarterTurn, hcEq]; ring
  have hend : F ⟨1, 2 * (k : Int)⟩ =
      ⟨-(k : Int), (k : Int) + 1⟩ := by
    apply Zsqrtd.ext <;> simp [F, Q, GaussianQuarterTurn, hcEq] <;> ring
  rw [hstart, hend] at h
  exact h

private theorem G_inj :
    (by
      classical
      exact
        ∀ (k : Nat),
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (∀ (z : GaussianInt), F (G z) = z) → (Function.Injective G) ) := by
  classical
  intro k Q c F G FG a b hab
  calc
    a = F (G a) := (FG a).symm
    _ = F (G b) := congrArg F hab
    _ = b := FG b

private theorem Gc_inj :
    (by
      classical
      exact
        ∀ (k : Nat),
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        let Gc : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - 1 - z.re⟩
        (∀ (z : GaussianInt), Fc (Gc z) = z) → (Function.Injective Gc) ) := by
  classical
  intro k Q c Fc Gc FcGc a b hab
  calc
    a = Fc (Gc a) := (FcGc a).symm
    _ = Fc (Gc b) := congrArg Fc hab
    _ = b := FcGc b

private theorem G_step :
    (by
      classical
      exact
        ∀ (k : Nat),
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        ∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → G b = G
            a + 1 ∨ G b = G a - 1 ∨ G b = G a + ⟨0, 1⟩ ∨ G b = G a - ⟨0, 1⟩ ) := by
  classical
  intro k G a b hh
  rcases hh with h | h | h | h
  · subst b; right; right; right; apply Zsqrtd.ext <;> simp [G]; ring
  · subst b; right; right; left; apply Zsqrtd.ext <;> simp [G]; ring
  · subst b; left; apply Zsqrtd.ext <;> simp [G]; ring
  · subst b; right; left; apply Zsqrtd.ext <;> simp [G]; ring

private theorem inverseVerticesAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), BoundaryFootprintVertices (TileTranslation D (Q d)) = F ''
            BoundaryFootprintVertices (TileTranslation D d)) → (
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (∀ (z : GaussianInt), Q (Qinv z) = z) → ((∀ (z : GaussianInt), G (F z) = z) → (∀ (d :
            GaussianInt), G '' BoundaryFootprintVertices (TileTranslation D d) =
            BoundaryFootprintVertices (TileTranslation D (Qinv d))))) ) := by
  classical
  intro k D Q c F quarterVerticesAt Qinv G qInvLeft GF d
  have h := quarterVerticesAt (Qinv d)
  rw [qInvLeft d] at h
  have hi := congrArg (Set.image G) h
  rw [Set.image_image] at hi
  simpa [Function.comp_def, GF] using hi

private theorem inverseEdgesAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), BoundaryFootprintEdges (TileTranslation D (Q d)) = (fun e : Finset
            GaussianInt => e.image F) '' BoundaryFootprintEdges (TileTranslation D d)) → (
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (∀ (z : GaussianInt), Q (Qinv z) = z) → ((∀ (z : GaussianInt), G (F z) = z) → (∀ (d :
            GaussianInt), (fun (e : Finset GaussianInt) => Finset.image G e) ''
            BoundaryFootprintEdges (TileTranslation D d) = BoundaryFootprintEdges
            (TileTranslation D (Qinv d))))) ) := by
  classical
  intro k D Q c F quarterEdgesAt Qinv G qInvLeft GF d
  have h := quarterEdgesAt (Qinv d)
  rw [qInvLeft d] at h
  have hi := congrArg
    (Set.image (fun e : Finset GaussianInt => e.image G)) h
  rw [Set.image_image] at hi
  have himage : (fun e : Finset GaussianInt => (e.image F).image G) = id := by
    funext e
    rw [Finset.image_image]
    simp [Function.comp_def, GF]
  rw [himage] at hi
  simpa using hi

private theorem inverseCellAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells = ((TileTranslation D
            d).cells.image Fc)) → (
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let Gc : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - 1 - z.re⟩
        (∀ (z : GaussianInt), Q (Qinv z) = z) → ((∀ (z : GaussianInt), Gc (Fc z) = z) → (∀ (d :
            GaussianInt), (TileTranslation D (Qinv d)).cells = Finset.image Gc (TileTranslation D
            d).cells))) ) := by
  classical
  intro k D Q c Fc quarterCellMap Qinv Gc qInvLeft GcFc d
  have h := quarterCellMap (Qinv d)
  rw [qInvLeft d] at h
  have hi := congrArg (fun s : Finset GaussianInt => s.image Gc) h
  rw [Finset.image_image] at hi
  have hcomp : Gc ∘ Fc = id := by funext z; exact GcFc z
  rw [hcomp, Finset.image_id] at hi
  simpa using hi.symm

private theorem inverseVerticesZero :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (TileTranslation D 0 = D) → (
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (∀ (d : GaussianInt), G '' BoundaryFootprintVertices (TileTranslation D d) =
            BoundaryFootprintVertices (TileTranslation D (Qinv d))) → ((Qinv 0 = 0) → (G ''
            BoundaryFootprintVertices D = BoundaryFootprintVertices D))) ) := by
  classical
  intro k D dzeroD Qinv G inverseVerticesAt qInvZero
  simpa [Qinv, qInvZero, dzeroD, dzeroD', D] using inverseVerticesAt 0

private theorem inverseEdgesZero :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (TileTranslation D 0 = D) → (
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (∀ (d : GaussianInt), (fun e : Finset GaussianInt => e.image G) '' BoundaryFootprintEdges
            (TileTranslation D d) = BoundaryFootprintEdges (TileTranslation D (Qinv d))) → ((Qinv
            0 = 0) → ((fun e : Finset GaussianInt => e.image G) '' BoundaryFootprintEdges D =
            BoundaryFootprintEdges D))) ) := by
  classical
  intro k D dzeroD Qinv G inverseEdgesAt qInvZero
  simpa [Qinv, qInvZero, dzeroD, dzeroD', D] using inverseEdgesAt 0

private theorem thirdTurn :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt),
            (Function.Injective f) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0,
            1⟩ ∨ b = a - ⟨0, 1⟩) → f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a
            - ⟨0, 1⟩) → ((SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun
            e : Finset GaussianInt => e.image f) '' E) (f x) (f y))))) → ((SimpleGridPathBetween
            (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩))
            (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩)) ⟨1, 0⟩ ⟨(k : Int), (k : Int)⟩) → (
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (Function.Injective G) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨
            b = a - ⟨0, 1⟩) → G b = G a + 1 ∨ G b = G a - 1 ∨ G b = G a + ⟨0, 1⟩ ∨ G b = G a -
            ⟨0, 1⟩) → ((∀ (d : GaussianInt), G '' BoundaryFootprintVertices (TileTranslation D d)
            = BoundaryFootprintVertices (TileTranslation D (Qinv d))) → ((∀ (d : GaussianInt),
            (fun e : Finset GaussianInt => e.image G) '' BoundaryFootprintEdges (TileTranslation
            D d) = BoundaryFootprintEdges (TileTranslation D (Qinv d))) → ((G ''
            BoundaryFootprintVertices D = BoundaryFootprintVertices D) → (((fun e : Finset
            GaussianInt => e.image G) '' BoundaryFootprintEdges D = BoundaryFootprintEdges D) →
            (SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D (Qinv ⟨(k : Int) + 1, -(k : Int)⟩))) (BoundaryFootprintEdges D ∩
            BoundaryFootprintEdges (TileTranslation D (Qinv ⟨(k : Int) + 1, -(k : Int)⟩))) ⟨-(k :
            Int), (k : Int) - 1⟩ 0)))))))) ) := by
  classical
  intro k imagePath incBetween D Qinv G G_inj G_step inverseVerticesAt inverseEdgesAt
      inverseVerticesZero inverseEdgesZero
  have h := imagePath G G_inj G_step incBetween
  have eG : Function.Injective
      (fun e : Finset GaussianInt => e.image G) := Finset.image_injective G_inj
  rw [Set.image_inter G_inj, Set.image_inter eG,
    inverseVerticesZero,
    inverseVerticesAt ⟨(k : Int) + 1, -(k : Int)⟩,
    inverseEdgesZero, inverseEdgesAt ⟨(k : Int) + 1, -(k : Int)⟩] at h
  have hstart : G ⟨1, 0⟩ = ⟨-(k : Int), (k : Int) - 1⟩ := by
    apply Zsqrtd.ext <;> simp [G]
  have hend : G ⟨(k : Int), (k : Int)⟩ = 0 := by
    apply Zsqrtd.ext <;> simp [G]
  rw [hstart, hend] at h
  simpa [Qinv, GaussianQuarterTurn] using h

private theorem cellMapRight :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        (∀ (d : GaussianInt), (TileTranslation D (Q d)).cells = ((TileTranslation D
            d).cells.image Fc)) → ((Q ⟨(k : Int) + 1, (k : Int)⟩ = ⟨-(k : Int), (k : Int) + 1⟩) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩).cells = (TileTranslation D
            da).cells.image Fc)) ) := by
  classical
  intro k D Q c Fc quarterCellMap dShift da
  rw [← dShift]
  exact quarterCellMap da

private theorem ddisjD :
    (by
      classical
      exact
        ∀ (k : Nat), (Disjoint (TileTranslation (DiamondTile k) (0 : GaussianInt)).cells
            (TileTranslation (DiamondTile k) ((0 : GaussianInt) + ⟨(↑k : ℤ) + (1 : ℤ), (↑k :
            ℤ)⟩)).cells) → (
        let D := DiamondTile k
        (TileTranslation D 0 = D) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        Disjoint D.cells (TileTranslation D da).cells)) ) := by
  classical
  intro k ddisj D dzeroD da
  have h := ddisj
  rw [dzeroD] at h
  simpa only [zero_add] using h

private theorem disjointImage :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ [inst : DecidableEq α], ∀ {s : Finset α}, ∀ {t : Finset α}, ∀ (f : α →
            α), Function.Injective f → Disjoint s t → Disjoint (Finset.image f s) (Finset.image f
            t) ) := by
  classical
  intro α typeclassInstance0 s t f hf hdis
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  rcases Finset.mem_image.mp hz₁ with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hz₂ with ⟨b, hb, hab⟩
  have hab' : b = a := hf hab
  subst b
  exact (Finset.disjoint_left.mp hdis) ha hb

private theorem firstCells₁ :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        ((TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩).cells = (TileTranslation D
            da).cells.image Fc) → (((TileTranslation D da).cells.Nonempty) → ((TileTranslation D
            ⟨-(k : Int), (k : Int) + 1⟩).cells.Nonempty)) ) := by
  classical
  intro k D Q c Fc da cellMapRight dneDright
  rw [cellMapRight]
  exact dneDright.image _

private theorem firstCellsDisj :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        (Function.Injective Fc) → ((D.cells = D.cells.image Fc) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        ((TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩).cells = (TileTranslation D
            da).cells.image Fc) → ((Disjoint D.cells (TileTranslation D da).cells) → ((∀
            {α : Type}, ∀ [DecidableEq α], ∀ {s : Finset α}, ∀ {t : Finset α}, ∀ (f : α → α),
            (Function.Injective f) → ((Disjoint s t) → (Disjoint (s.image f) (t.image f)))) →
            (Disjoint D.cells (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩).cells))))) ) := by
  classical
  intro k D Q c Fc F_cell_inj cellMapZero da cellMapRight ddisjD disjointImage
  rw [cellMapZero, cellMapRight]
  exact disjointImage Fc F_cell_inj ddisjD

private theorem idisjD :
    (by
      classical
      exact
        ∀ (k : Nat), (Disjoint (TileTranslation (DiamondTile k) (0 : GaussianInt)).cells
            (TileTranslation (DiamondTile k) ((0 : GaussianInt) + ⟨(↑k : ℤ) + (1 : ℤ), -(↑k :
            ℤ)⟩)).cells) → (
        let D := DiamondTile k
        (TileTranslation D 0 = D) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        Disjoint D.cells (TileTranslation D ia).cells)) ) := by
  classical
  intro k idisj D dzeroD ia
  have h := idisj
  rw [dzeroD] at h
  simpa only [zero_add] using h

private theorem thirdCells₁ :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let Gc : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - 1 - z.re⟩
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        ((TileTranslation D (Qinv ia)).cells = (TileTranslation D ia).cells.image Gc) →
            (((TileTranslation D ia).cells.Nonempty) → ((TileTranslation D (Qinv
            ia)).cells.Nonempty)) ) := by
  classical
  intro k D Qinv Gc ia inverseCellRight ineDright
  rw [inverseCellRight]
  exact ineDright.image _

private theorem thirdCellsDisj :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let Gc : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - 1 - z.re⟩
        (Function.Injective Gc) → ((∀ {α : Type}, ∀ [DecidableEq α], ∀ {s : Finset α}, ∀
            {t : Finset α}, ∀ (f : α → α), (Function.Injective f) → ((Disjoint s t) → (Disjoint
            (s.image f) (t.image f)))) → ((D.cells = D.cells.image Gc) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        ((TileTranslation D (Qinv ia)).cells = (TileTranslation D ia).cells.image Gc) →
            ((Disjoint D.cells (TileTranslation D ia).cells) → (Disjoint D.cells (TileTranslation
            D (Qinv ia)).cells))))) ) := by
  classical
  intro k D Qinv Gc Gc_inj disjointImage inverseCellZero ia inverseCellRight idisjD
  rw [inverseCellZero, inverseCellRight]
  exact disjointImage Gc Gc_inj idisjD

private theorem translateStep :
    (by
      classical
      exact
        ∀ (u : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), b = a + (1 : GaussianInt)
            ∨ b = a - (1 : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩
            → GaussianTranslation u b = GaussianTranslation u a + (1 : GaussianInt) ∨
            GaussianTranslation u b = GaussianTranslation u a - (1 : GaussianInt) ∨
            GaussianTranslation u b = GaussianTranslation u a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨
            GaussianTranslation u b = GaussianTranslation u a - ⟨(0 : ℤ), (1 : ℤ)⟩ ) := by
  classical
  intro u a b hh
  rcases hh with h | h | h | h
  · subst b; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; ring
  · subst b; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; ring
  · subst b; right; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; ring
  · subst b; right; right; right; apply Zsqrtd.ext <;> simp [GaussianTranslation]; ring

private theorem translateInj :
    (by
      classical
      exact
        ∀ (u : GaussianInt), Function.Injective (GaussianTranslation u) ) := by
  classical
  intro u a b hab
  exact add_right_cancel hab

private theorem shiftPath :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt),
            (Function.Injective f) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0,
            1⟩ ∨ b = a - ⟨0, 1⟩) → f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a
            - ⟨0, 1⟩) → ((SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun
            e : Finset GaussianInt => e.image f) '' E) (f x) (f y))))) → ((SimpleGridPathBetween
            (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩))
            (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩)) ⟨1, 0⟩ ⟨(k : Int), (k : Int)⟩) → (
        let D := DiamondTile k
        (TileTranslation D 0 = D) → ((∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
            GaussianInt), (TileTranslation T (u + v)).cells = (TileTranslation (TileTranslation T
            u) v).cells) → ((∀ {A : ProtoTile}, ∀ {B : ProtoTile}, (A.cells = B.cells) →
            (BoundaryFootprintEdges A = BoundaryFootprintEdges B)) → ((∀ {A : ProtoTile}, ∀
            {B : ProtoTile}, (A.cells = B.cells) → ((B.cells.Nonempty) →
            (BoundaryFootprintVertices A = BoundaryFootprintVertices B))) → ((D.cells.Nonempty) → (
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (∀ (u : GaussianInt), ∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b =
            a - ⟨0, 1⟩) → GaussianTranslation u b = GaussianTranslation u a + 1 ∨
            GaussianTranslation u b = GaussianTranslation u a - 1 ∨ GaussianTranslation u b =
            GaussianTranslation u a + ⟨0, 1⟩ ∨ GaussianTranslation u b = GaussianTranslation u a
            - ⟨0, 1⟩) → ((∀ (u : GaussianInt), Function.Injective (GaussianTranslation u)) →
            (SimpleGridPathBetween (BoundaryFootprintVertices (TileTranslation D shift) ∩
            BoundaryFootprintVertices D) (BoundaryFootprintEdges (TileTranslation D shift) ∩
            BoundaryFootprintEdges D) ⟨-(k : Int), (k : Int)⟩ ⟨-1, 2 * (k : Int)⟩))))))))) ) := by
  classical
  intro k imagePath incBetween D dzeroD translateCells edgeCellsEq vertexCellsEq hDne shift
      translateStep translateInj
  let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
  have h := imagePath (GaussianTranslation shift) (translateInj shift)
    (translateStep shift) incBetween
  have eT : Function.Injective
      (fun e : Finset GaussianInt => e.image (GaussianTranslation shift)) :=
    Finset.image_injective (translateInj shift)
  have hsum : shift + ia = 0 := by
    apply Zsqrtd.ext <;> simp [shift, ia]
  have hsum' : ia + shift = 0 := by rw [add_comm]; exact hsum
  have hnested : (TileTranslation (TileTranslation D ia) shift).cells = D.cells := by
    rw [← translateCells D ia shift, hsum', dzeroD]
  have hnestedV : BoundaryFootprintVertices
      (TileTranslation (TileTranslation D ia) shift) = BoundaryFootprintVertices D :=
    vertexCellsEq hnested hDne
  have hnestedE : BoundaryFootprintEdges
      (TileTranslation (TileTranslation D ia) shift) = BoundaryFootprintEdges D :=
    edgeCellsEq hnested
  rw [Set.image_inter (translateInj shift), Set.image_inter eT] at h
  rw [← (TileTranslationFormulas D shift).2.2.2.2.2.2.2.1,
    ← (TileTranslationFormulas D shift).2.2.2.2.2.2.2.2,
    ← (TileTranslationFormulas (TileTranslation D ia) shift).2.2.2.2.2.2.2.1,
    ← (TileTranslationFormulas (TileTranslation D ia) shift).2.2.2.2.2.2.2.2,
    hnestedV, hnestedE] at h
  have hs : GaussianTranslation shift ⟨1, 0⟩ = ⟨-(k : Int), (k : Int)⟩ := by
    apply Zsqrtd.ext <;> simp [GaussianTranslation, shift]
  have he : GaussianTranslation shift ⟨(k : Int), (k : Int)⟩ =
      ⟨-1, 2 * (k : Int)⟩ := by
    apply Zsqrtd.ext <;> simp [GaussianTranslation, shift] <;> ring
  have h' : SimpleGridPathBetween
      (BoundaryFootprintVertices (TileTranslation D shift) ∩
        BoundaryFootprintVertices D)
      (BoundaryFootprintEdges (TileTranslation D shift) ∩
        BoundaryFootprintEdges D)
      (GaussianTranslation shift ⟨1, 0⟩)
      (GaussianTranslation shift ⟨(k : Int), (k : Int)⟩) := h
  rw [hs, he] at h'
  exact h'

private theorem shiftCellsOne :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (TileTranslation D shift).cells = (D.cells.image (GaussianTranslation shift)) ) := by
  classical
  intro k D shift
  exact (TileTranslationFormulas D shift).1

private theorem shiftCellsTwo :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (TileTranslation D 0 = D) → ((∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
            GaussianInt), (TileTranslation T (u + v)).cells = (TileTranslation (TileTranslation T
            u) v).cells) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        D.cells = ((TileTranslation D ia).cells.image (GaussianTranslation shift)))) ) := by
  classical
  intro k D dzeroD translateCells ia shift
  have hsum : ia + shift = 0 := by
    apply Zsqrtd.ext <;> simp [ia, shift]
  have h := translateCells D ia shift
  rw [hsum, dzeroD] at h
  rw [(TileTranslationFormulas (TileTranslation D ia) shift).1] at h
  exact h

private theorem shiftCellsNonempty :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (D.cells.Nonempty) → (
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        ((TileTranslation D shift).cells = (D.cells.image (GaussianTranslation shift))) →
            ((TileTranslation D shift).cells.Nonempty)) ) := by
  classical
  intro k D hDne shift shiftCellsOne
  rw [shiftCellsOne]
  exact hDne.image _

private theorem shiftCellsDisjoint :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (∀ {α : Type}, ∀ [DecidableEq α], ∀ {s : Finset α}, ∀ {t : Finset α}, ∀ (f : α → α),
            (Function.Injective f) → ((Disjoint s t) → (Disjoint (s.image f) (t.image f)))) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        (Disjoint D.cells (TileTranslation D ia).cells) → (
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (∀ (u : GaussianInt), Function.Injective (GaussianTranslation u)) → (((TileTranslation D
            shift).cells = (D.cells.image (GaussianTranslation shift))) → ((D.cells =
            ((TileTranslation D ia).cells.image (GaussianTranslation shift))) → (Disjoint D.cells
            (TileTranslation D shift).cells))))) ) := by
  classical
  intro k D disjointImage ia idisjD shift translateInj shiftCellsOne shiftCellsTwo
  rw [shiftCellsOne]
  have h := (disjointImage (GaussianTranslation shift) (translateInj shift) idisjD).symm
  simpa only [← shiftCellsTwo] using h

private theorem shiftVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩) = iV) → (
        let D := DiamondTile k
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (∀ (u : GaussianInt), Function.Injective (GaussianTranslation u)) →
            ((BoundaryFootprintVertices (TileTranslation (TileTranslation D ia) shift) =
            BoundaryFootprintVertices D) → (BoundaryFootprintVertices (TileTranslation D shift) ∩
            BoundaryFootprintVertices D = GaussianTranslation shift '' iV))) ) := by
  classical
  intro k iV incVertices D ia shift translateInj hnestedV
  rw [← hnestedV,
    (TileTranslationFormulas D shift).2.2.2.2.2.2.2.1,
    (TileTranslationFormulas (TileTranslation D ia) shift).2.2.2.2.2.2.2.1,
    ← Set.image_inter (translateInj shift), incVertices]

private theorem shiftEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩) = iE) → (
        let D := DiamondTile k
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (∀ (u : GaussianInt), Function.Injective (GaussianTranslation u)) →
            ((BoundaryFootprintEdges (TileTranslation (TileTranslation D ia) shift) =
            BoundaryFootprintEdges D) → (BoundaryFootprintEdges (TileTranslation D shift) ∩
            BoundaryFootprintEdges D = (fun e : Finset GaussianInt => e.image
            (GaussianTranslation shift)) '' iE))) ) := by
  classical
  intro k N iP iE incEdges D ia shift translateInj hnestedE
  let et : Finset GaussianInt → Finset GaussianInt :=
    fun e => e.image (GaussianTranslation shift)
  have eti : Function.Injective et := Finset.image_injective (translateInj shift)
  rw [← hnestedE,
    (TileTranslationFormulas D shift).2.2.2.2.2.2.2.2,
    (TileTranslationFormulas (TileTranslation D ia) shift).2.2.2.2.2.2.2.2,
    ← Set.image_inter eti, incEdges]

private theorem fourthPath :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (SimpleGridPathBetween (BoundaryFootprintVertices (TileTranslation D shift) ∩
            BoundaryFootprintVertices D) (BoundaryFootprintEdges (TileTranslation D shift) ∩
            BoundaryFootprintEdges D) ⟨-(k : Int), (k : Int)⟩ ⟨-1, 2 * (k : Int)⟩) →
            (SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D shift)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D shift)) ⟨-(k : Int), (k : Int)⟩ ⟨-1, 2 * (k : Int)⟩) ) := by
  classical
  intro k D shift shiftPath
  simpa only [Set.inter_comm] using shiftPath

private theorem zeroFvertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        (TileTranslation D 0 = D) → (∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), BoundaryFootprintVertices (TileTranslation D (Q d)) = F ''
            BoundaryFootprintVertices (TileTranslation D d)) → ((Q 0 = 0) →
            (BoundaryFootprintVertices D = F '' BoundaryFootprintVertices D))) ) := by
  classical
  intro k D Q dzeroD c F quarterVerticesAt zeroQ
  simpa [D, Q, GaussianQuarterTurn, dzeroD, dzeroD', zeroQ] using quarterVerticesAt 0

private theorem zeroFedges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        (TileTranslation D 0 = D) → (∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), BoundaryFootprintEdges (TileTranslation D (Q d)) = (fun e : Finset
            GaussianInt => e.image F) '' BoundaryFootprintEdges (TileTranslation D d)) → ((Q 0 =
            0) → (BoundaryFootprintEdges D = (fun e : Finset GaussianInt => e.image F) ''
            BoundaryFootprintEdges D))) ) := by
  classical
  intro k D Q dzeroD c F quarterEdgesAt zeroQ
  simpa [D, Q, GaussianQuarterTurn, dzeroD, dzeroD', zeroQ] using quarterEdgesAt 0

private theorem rightFvertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), BoundaryFootprintVertices (TileTranslation D (Q d)) = F ''
            BoundaryFootprintVertices (TileTranslation D d)) → ((Q ⟨(k : Int) + 1, (k : Int)⟩ =
            ⟨-(k : Int), (k : Int) + 1⟩) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        BoundaryFootprintVertices (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) = F ''
            BoundaryFootprintVertices (TileTranslation D da))) ) := by
  classical
  intro k D Q c F quarterVerticesAt dShift da
  rw [← dShift]
  exact quarterVerticesAt da

private theorem rightFedges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (∀ (d : GaussianInt), BoundaryFootprintEdges (TileTranslation D (Q d)) = (fun e : Finset
            GaussianInt => e.image F) '' BoundaryFootprintEdges (TileTranslation D d)) → ((Q ⟨(k
            : Int) + 1, (k : Int)⟩ = ⟨-(k : Int), (k : Int) + 1⟩) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        BoundaryFootprintEdges (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) = (fun e : Finset
            GaussianInt => e.image F) '' BoundaryFootprintEdges (TileTranslation D da))) ) := by
  classical
  intro k D Q c F quarterEdgesAt dShift da
  rw [← dShift]
  exact quarterEdgesAt da

private theorem firstVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩) = dV) → (
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (Function.Injective F) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (BoundaryFootprintVertices D = F '' BoundaryFootprintVertices D) →
            ((BoundaryFootprintVertices (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) = F ''
            BoundaryFootprintVertices (TileTranslation D da)) → (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) = F ''
            dV)))) ) := by
  classical
  intro k dV decVertices D Q c F F_inj da zeroFvertices rightFvertices
  rw [zeroFvertices, rightFvertices, ← Set.image_inter F_inj, decVertices]

private theorem thirdVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩) = iV) → (
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (Function.Injective G) → ((∀ (d : GaussianInt), G '' BoundaryFootprintVertices
            (TileTranslation D d) = BoundaryFootprintVertices (TileTranslation D (Qinv d))) → ((G
            '' BoundaryFootprintVertices D = BoundaryFootprintVertices D) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D (Qinv ia)) = G
            '' iV)))) ) := by
  classical
  intro k iV incVertices D Qinv G G_inj inverseVerticesAt inverseVerticesZero ia
  rw [← inverseVerticesZero, ← inverseVerticesAt ia,
    ← Set.image_inter G_inj, incVertices]

private theorem fourthVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let D := DiamondTile k
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (BoundaryFootprintVertices (TileTranslation D shift) ∩ BoundaryFootprintVertices D =
            GaussianTranslation shift '' iV) → (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D shift) = GaussianTranslation shift ''
            iV) ) := by
  classical
  intro k iV D shift shiftVertices
  rw [Set.inter_comm, shiftVertices]

private theorem firstSet :
    (by
      classical
      exact
        ∀ (k : Nat),
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt), (c = ⟨(↑k : ℤ), (↑k : ℤ)⟩) → (
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        F '' dV = {z : GaussianInt | -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ (k : Int) + 1 ≤ z.im ∧ z.im ≤
            2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧ z.im - z.re ≤ 2 * (k : Int) + 1}) ) := by
  classical
  intro k dV Q c hcEq F
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq, dV] at hw ⊢
    simp [F, Q, GaussianQuarterTurn, hcEq]
    omega
  · intro hz
    simp only [Set.mem_ofPred_eq] at hz
    let w : GaussianInt := ⟨z.im - (k : Int), (k : Int) - z.re⟩
    have hw : w ∈ dV := by
      simp [w, dV]
      omega
    refine ⟨w, hw, ?_⟩
    apply Zsqrtd.ext <;> simp [w, F, Q, GaussianQuarterTurn, hcEq]

private theorem secondSet :
    (by
      classical
      exact
        ∀ (k : Nat),
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        dV = {z : GaussianInt | 1 ≤ z.re ∧ z.re ≤ (k : Int) ∧ (k : Int) ≤ z.im ∧ z.im ≤ 2 * (k :
            Int) ∧ 2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1} ) := by
  classical
  intro k dV
  ext z
  simp only [dV, Set.mem_ofPred_eq]
  constructor <;> omega

private theorem thirdSet :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        G '' iV = {z : GaussianInt | -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ (k : Int) -
            1 ∧ -1 ≤ z.re + z.im ∧ z.re + z.im ≤ 0} ) := by
  classical
  intro k iV G
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq, iV] at hw ⊢
    simp [G]
    omega
  · intro hz
    simp only [Set.mem_ofPred_eq] at hz
    let w : GaussianInt := ⟨(k : Int) - z.im, z.re + (k : Int)⟩
    have hw : w ∈ iV := by
      simp [w, iV]
      omega
    refine ⟨w, hw, ?_⟩
    apply Zsqrtd.ext <;> simp [w, G]

private theorem fourthSet :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        GaussianTranslation shift '' iV = {z : GaussianInt | -(k : Int) ≤ z.re ∧ z.re ≤ -1 ∧ (k :
            Int) ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧ z.im - z.re ≤ 2 *
            (k : Int) + 1} ) := by
  classical
  intro k iV shift
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq, iV] at hw ⊢
    simp [GaussianTranslation, shift]
    omega
  · intro hz
    simp only [Set.mem_ofPred_eq] at hz
    let w : GaussianInt := ⟨z.re + (k : Int) + 1, z.im - (k : Int)⟩
    have hw : w ∈ iV := by
      simp [w, iV]
      omega
    refine ⟨w, hw, ?_⟩
    apply Zsqrtd.ext <;> simp [w, GaussianTranslation, shift]

private theorem firstEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let dP : Nat → GaussianInt := fun j =>
          ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
        let dE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {dP j, dP (j + 1)}}
        (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, (k : Int)⟩) = dE) → (
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        (Function.Injective F) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (BoundaryFootprintEdges D = (fun e : Finset GaussianInt => e.image F) ''
            BoundaryFootprintEdges D) → ((BoundaryFootprintEdges (TileTranslation D ⟨-(k : Int),
            (k : Int) + 1⟩) = (fun e : Finset GaussianInt => e.image F) '' BoundaryFootprintEdges
            (TileTranslation D da)) → (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) = (fun e : Finset GaussianInt =>
            e.image F) '' dE)))) ) := by
  classical
  intro k N dP dE decEdges D Q c F F_inj da zeroFedges rightFedges
  rw [zeroFedges, rightFedges, ← Set.image_inter (Finset.image_injective F_inj), decEdges]

private theorem thirdEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(k : Int) + 1, -(k : Int)⟩) = iE) → (
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        (Function.Injective G) → ((∀ (d : GaussianInt), (fun e : Finset GaussianInt => e.image G)
            '' BoundaryFootprintEdges (TileTranslation D d) = BoundaryFootprintEdges
            (TileTranslation D (Qinv d))) → (((fun e : Finset GaussianInt => e.image G) ''
            BoundaryFootprintEdges D = BoundaryFootprintEdges D) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D (Qinv ia)) = (fun e
            : Finset GaussianInt => e.image G) '' iE)))) ) := by
  classical
  intro k N iP iE incEdges D Qinv G G_inj inverseEdgesAt inverseEdgesZero ia
  rw [← inverseEdgesZero, ← inverseEdgesAt ia,
    ← Set.image_inter (Finset.image_injective G_inj), incEdges]

private theorem fourthEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * k - 1
        let iP : Nat → GaussianInt := fun j =>
          ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
        let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
        let D := DiamondTile k
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (BoundaryFootprintEdges (TileTranslation D shift) ∩ BoundaryFootprintEdges D = (fun e :
            Finset GaussianInt => e.image (GaussianTranslation shift)) '' iE) →
            (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D shift) = (fun e
            : Finset GaussianInt => e.image (GaussianTranslation shift)) '' iE) ) := by
  classical
  intro k N iP iE D shift shiftEdges
  rw [Set.inter_comm, shiftEdges]

private theorem rows0 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D ⟨-(k : Int), (k : Int) +
            1⟩).cells ∧ Disjoint D.cells (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩).cells ∧
            SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩)) (BoundaryFootprintEdges D ∩
            BoundaryFootprintEdges (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩)) ⟨0, 2 * (k :
            Int)⟩ ⟨-(k : Int), (k : Int) + 1⟩) → ((Finset.Nonempty D.cells ∧ Finset.Nonempty
            (TileTranslation D da).cells ∧ Disjoint D.cells (TileTranslation D da).cells ∧
            SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D da)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D da)) ⟨1, 2 * (k : Int)⟩ ⟨(k : Int), (k : Int)⟩) → (∀ T, ∀ U, ∀ a,
            ∀ e, (T, U, a, e) ∈ [(D, TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩, (⟨0, 2 * (k :
            Int)⟩ : GaussianInt), ⟨-(k : Int), (k : Int) + 1⟩), (D, TileTranslation D da, (⟨1, 2
            * (k : Int)⟩ : GaussianInt), ⟨(k : Int), (k : Int)⟩)] → Finset.Nonempty T.cells ∧
            Finset.Nonempty U.cells ∧ Disjoint T.cells U.cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges T
            ∩ BoundaryFootprintEdges U) a e)) ) := by
  classical
  intro k D da rowFirst0 rowSecond0 T U a e hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm
  · simp only [Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩
    exact rowFirst0
  · simp only [Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩
    exact rowSecond0

private theorem rows1 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D (Qinv ia)).cells ∧ Disjoint
            D.cells (TileTranslation D (Qinv ia)).cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D (Qinv
            ia))) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D (Qinv
            ia))) ⟨-(k : Int), (k : Int) - 1⟩ 0) → ((Finset.Nonempty D.cells ∧ Finset.Nonempty
            (TileTranslation D shift).cells ∧ Disjoint D.cells (TileTranslation D shift).cells ∧
            SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D shift)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D shift)) ⟨-(k : Int), (k : Int)⟩ ⟨-1, 2 * (k : Int)⟩) → (∀ T, ∀ U,
            ∀ a, ∀ e, (T, U, a, e) ∈ [(D, TileTranslation D (Qinv ia), (⟨-(k : Int), (k : Int) -
            1⟩ : GaussianInt), 0), (D, TileTranslation D shift, (⟨-(k : Int), (k : Int)⟩ :
            GaussianInt), ⟨-1, 2 * (k : Int)⟩)] → Finset.Nonempty T.cells ∧ Finset.Nonempty
            U.cells ∧ Disjoint T.cells U.cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices
            T ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges
            U) a e)) ) := by
  classical
  intro k D Qinv ia shift rowFirst1 rowSecond1 T U a e hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm
  · simp only [Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩
    exact rowFirst1
  · simp only [Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩
    exact rowSecond1

private theorem h0 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let F : GaussianInt → GaussianInt := fun z => Q z + c
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D ⟨-(k : Int),
            (k : Int) + 1⟩) = F '' dV) → ((BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D da) = dV) → ((F '' dV = {z : GaussianInt
            | -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ (k : Int) + 1 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k
            : Int) ≤ z.im - z.re ∧ z.im - z.re ≤ 2 * (k : Int) + 1}) → ((dV = {z : GaussianInt |
            1 ≤ z.re ∧ z.re ≤ (k : Int) ∧ (k : Int) ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int)
            ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}) → ((∀ T, ∀ U, ∀ a, ∀ e, (T, U, a,
            e) ∈ [(D, TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩, (⟨0, 2 * (k : Int)⟩ :
            GaussianInt), ⟨-(k : Int), (k : Int) + 1⟩), (D, TileTranslation D da, (⟨1, 2 * (k :
            Int)⟩ : GaussianInt), ⟨(k : Int), (k : Int)⟩)] → Finset.Nonempty T.cells ∧
            Finset.Nonempty U.cells ∧ Disjoint T.cells U.cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges T
            ∩ BoundaryFootprintEdges U) a e) → ((∀ T, ∀ U, ∀ a, ∀ e, (T, U, a, e) ∈ [(D,
            TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩, (⟨0, 2 * (k : Int)⟩ : GaussianInt),
            ⟨-(k : Int), (k : Int) + 1⟩), (D, TileTranslation D da, (⟨1, 2 * (k : Int)⟩ :
            GaussianInt), ⟨(k : Int), (k : Int)⟩)] → Finset.Nonempty T.cells ∧ Finset.Nonempty
            U.cells ∧ Disjoint T.cells U.cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices
            T ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges
            U) a e) ∧ (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D
            ⟨-(k : Int), (k : Int) + 1⟩) = {z | -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ (k : Int) + 1 ≤
            z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧ z.im - z.re ≤ 2 * (k :
            Int) + 1}) ∧ (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D da) = {z | 1 ≤ z.re ∧ z.re ≤ (k : Int) ∧ (k : Int) ≤ z.im ∧ z.im ≤
            2 * (k : Int) ∧ 2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}))))))
            ) := by
  classical
  intro k dV D Q c F da firstVertices secondVertices firstSet secondSet rows0
  exact ⟨rows0, by rw [firstVertices, firstSet], by rw [secondVertices, secondSet]⟩

private theorem h1 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let G : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - z.re⟩
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D (Qinv ia)) =
            G '' iV) → ((BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation
            D shift) = GaussianTranslation shift '' iV) → ((G '' iV = {z : GaussianInt | -(k :
            Int) ≤ z.re ∧ z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ (k : Int) - 1 ∧ -1 ≤ z.re + z.im ∧ z.re +
            z.im ≤ 0}) → ((GaussianTranslation shift '' iV = {z : GaussianInt | -(k : Int) ≤ z.re
            ∧ z.re ≤ -1 ∧ (k : Int) ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧
            z.im - z.re ≤ 2 * (k : Int) + 1}) → ((∀ T, ∀ U, ∀ a, ∀ e, (T, U, a, e) ∈ [(D,
            TileTranslation D (Qinv ia), (⟨-(k : Int), (k : Int) - 1⟩ : GaussianInt), 0), (D,
            TileTranslation D shift, (⟨-(k : Int), (k : Int)⟩ : GaussianInt), ⟨-1, 2 * (k :
            Int)⟩)] → Finset.Nonempty T.cells ∧ Finset.Nonempty U.cells ∧ Disjoint T.cells
            U.cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices T ∩
            BoundaryFootprintVertices U) (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a
            e) → ((∀ T, ∀ U, ∀ a, ∀ e, (T, U, a, e) ∈ [(D, TileTranslation D (Qinv ia), (⟨-(k :
            Int), (k : Int) - 1⟩ : GaussianInt), 0), (D, TileTranslation D shift, (⟨-(k : Int),
            (k : Int)⟩ : GaussianInt), ⟨-1, 2 * (k : Int)⟩)] → Finset.Nonempty T.cells ∧
            Finset.Nonempty U.cells ∧ Disjoint T.cells U.cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges T
            ∩ BoundaryFootprintEdges U) a e) ∧ (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D (Qinv ia)) = {z | -(k : Int) ≤ z.re ∧
            z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ (k : Int) - 1 ∧ -1 ≤ z.re + z.im ∧ z.re + z.im ≤ 0}) ∧
            (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D shift) =
            {z | -(k : Int) ≤ z.re ∧ z.re ≤ -1 ∧ (k : Int) ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k
            : Int) ≤ z.im - z.re ∧ z.im - z.re ≤ 2 * (k : Int) + 1})))))) ) := by
  classical
  intro k iV D Qinv G ia shift thirdVertices fourthVertices thirdSet fourthSet rows1
  exact ⟨rows1, by rw [thirdVertices, thirdSet], by rw [fourthVertices, fourthSet]⟩

end DiamondPathComparison

namespace DiamondRowConclusions

private theorem imagePath :
    (by
      classical
      exact
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt), Function.Injective f → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), b = a + (1 : GaussianInt) ∨ b = a - (1 :
            GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩ → f b = f a +
            (1 : GaussianInt) ∨ f b = f a - (1 : GaussianInt) ∨ f b = f a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨
            f b = f a - ⟨(0 : ℤ), (1 : ℤ)⟩) → SimpleGridPathBetween V E x y →
            SimpleGridPathBetween (f '' V) ((fun (e : Finset GaussianInt) => Finset.image f e) ''
            E) (f x) (f y) ) := by
  classical
  intro V E x y f hf hstep hp
  exact P4055T1GridPathImage f hf hstep V E x y hp

private theorem rowFirst0 :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt),
            (Function.Injective f) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0,
            1⟩ ∨ b = a - ⟨0, 1⟩) → f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a
            - ⟨0, 1⟩) → ((SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun
            e : Finset GaussianInt => e.image f) '' E) (f x) (f y))))) → ((Function.Injective
            GaussianQuarterTurn) → ((SimpleGridPathBetween (BoundaryFootprintVertices
            (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile k) ⟨(↑k :
            ℤ) + (1 : ℤ), (↑k : ℤ)⟩)) (BoundaryFootprintEdges (DiamondTile k) ∩
            BoundaryFootprintEdges (TileTranslation (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), (↑k :
            ℤ)⟩)) ⟨(↑k : ℤ), (↑k : ℤ)⟩ ⟨(1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩) → (
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        (TileTranslation D 0 = D) → (∀ (c : GaussianInt), (c = ⟨(↑k : ℤ), (↑k : ℤ)⟩) → (
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        (
        let F := fun (z : GaussianInt) => GaussianQuarterTurn z + c; Function.Injective F) → ((
        let D := DiamondTile k; Finset.Nonempty D.cells) → ((∀ (d : GaussianInt),
            BoundaryFootprintVertices (TileTranslation (DiamondTile k) (GaussianQuarterTurn d)) =
            (fun (z : GaussianInt) => GaussianQuarterTurn z + c) '' BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) d)) → ((∀ (d : GaussianInt), BoundaryFootprintEdges
            (TileTranslation (DiamondTile k) (GaussianQuarterTurn d)) = (fun (e : Finset
            GaussianInt) => Finset.image (fun (z : GaussianInt) => GaussianQuarterTurn z + c) e)
            '' BoundaryFootprintEdges (TileTranslation (DiamondTile k) d)) → ((
        let Q := GaussianQuarterTurn; Q ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩ = ⟨-(↑k : ℤ), (↑k : ℤ) +
            (1 : ℤ)⟩) → ((D.cells = D.cells.image Fc) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (
        let da := ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩; (TileTranslation (DiamondTile k) ⟨-(↑k : ℤ),
            (↑k : ℤ) + (1 : ℤ)⟩).cells = Finset.image (fun (z : GaussianInt) =>
            GaussianQuarterTurn z - (1 : GaussianInt) + c) (TileTranslation (DiamondTile k)
            da).cells) → ((
        let da := ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩; Disjoint (DiamondTile k).cells (TileTranslation
            (DiamondTile k) da).cells) → (((TileTranslation D da).cells.Nonempty) → ((∀
            {α : Type}, ∀ [inst : DecidableEq α], ∀ {s : Finset α}, ∀ {t : Finset α}, ∀ (f : α →
            α), Function.Injective f → Disjoint s t → Disjoint (Finset.image f s) (Finset.image f
            t)) → (Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D ⟨-(k : Int), (k :
            Int) + 1⟩).cells ∧ Disjoint D.cells (TileTranslation D ⟨-(k : Int), (k : Int) +
            1⟩).cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩))
            (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D ⟨-(k : Int), (k
            : Int) + 1⟩)) ⟨0, 2 * (k : Int)⟩ ⟨-(k : Int), (k : Int) + 1⟩))))))))))))))) ) := by
  classical
  intro k imagePath qinj decBetween D Q dzeroD c hcEq Fc F_inj hDne quarterVerticesAt
      quarterEdgesAt dShift cellMapZero da cellMapRight ddisjD dneDright disjointImage
  let F : GaussianInt → GaussianInt := fun z => Q z + c
  exact ⟨hDne, (DiamondPathComparison.firstCells₁ k c cellMapRight dneDright),
        (DiamondPathComparison.firstCellsDisj k c (DiamondPathComparison.F_cell_inj qinj c)
        cellMapZero cellMapRight ddisjD disjointImage), (DiamondPathComparison.firstTurn k
        imagePath decBetween dzeroD c hcEq F_inj (DiamondPathComparison.F_step k c)
        quarterVerticesAt quarterEdgesAt dShift)⟩

private theorem rowFirst1 :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt),
            (Function.Injective f) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0,
            1⟩ ∨ b = a - ⟨0, 1⟩) → f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a
            - ⟨0, 1⟩) → ((SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun
            e : Finset GaussianInt => e.image f) '' E) (f x) (f y))))) → ((SimpleGridPathBetween
            (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩))
            (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩)) ⟨(1 : ℤ), (0 : ℤ)⟩ ⟨(↑k : ℤ), (↑k :
            ℤ)⟩) → (
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        ∀ (c : GaussianInt),
        let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
        (
        let D := DiamondTile k; Finset.Nonempty D.cells) → (
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        let Gc : GaussianInt → GaussianInt := fun z =>
          ⟨z.im - (k : Int), (k : Int) - 1 - z.re⟩
        (∀ (z : GaussianInt), Fc (Gc z) = z) → ((Function.Injective fun (z : GaussianInt) =>
            (⟨z.im - (↑k : ℤ), (↑k : ℤ) - z.re⟩ : GaussianInt)) → ((∀ (d : GaussianInt), (fun (z
            : GaussianInt) => (⟨z.im - (↑k : ℤ), (↑k : ℤ) - z.re⟩ : GaussianInt)) ''
            BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) d) = BoundaryFootprintVertices (TileTranslation (DiamondTile k) ((fun
                (z : GaussianInt) => (⟨z.im, -z.re⟩ : GaussianInt)) d))) → ((∀ (d : GaussianInt),
                (fun (e : Finset
            GaussianInt) => Finset.image (fun (z : GaussianInt) => (⟨z.im - (↑k : ℤ), (↑k : ℤ) -
            z.re⟩ : GaussianInt)) e) '' BoundaryFootprintEdges (TileTranslation (DiamondTile k) d) =
            BoundaryFootprintEdges (TileTranslation (DiamondTile k) ((fun (z : GaussianInt) =>
                (⟨z.im, -z.re⟩ : GaussianInt)) d))) → (((fun (z : GaussianInt) => (⟨z.im - (↑k :
                ℤ), (↑k : ℤ) - z.re⟩ : GaussianInt))
            '' BoundaryFootprintVertices (DiamondTile k) = BoundaryFootprintVertices (DiamondTile
            k)) → (((fun (e : Finset GaussianInt) => Finset.image (fun (z : GaussianInt) => (⟨z.im
            - (↑k : ℤ), (↑k : ℤ) - z.re⟩ : GaussianInt)) e) '' BoundaryFootprintEdges
                (DiamondTile k) =
            BoundaryFootprintEdges (DiamondTile k)) → ((∀ {α : Type}, ∀ [inst : DecidableEq α], ∀
            {s : Finset α}, ∀ {t : Finset α}, ∀ (f : α → α), Function.Injective f → Disjoint s t
            → Disjoint (Finset.image f s) (Finset.image f t)) → ((D.cells = D.cells.image Gc) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        ((TileTranslation D (Qinv ia)).cells = (TileTranslation D ia).cells.image Gc) → ((
        let ia := ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩; Disjoint (DiamondTile k).cells
            (TileTranslation (DiamondTile k) ia).cells) → (((TileTranslation D
            ia).cells.Nonempty) → (Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D
            (Qinv ia)).cells ∧ Disjoint D.cells (TileTranslation D (Qinv ia)).cells ∧
            SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D (Qinv ia))) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D (Qinv ia))) ⟨-(k : Int), (k : Int) - 1⟩ 0)))))))))))))) ) := by
  classical
  intro k imagePath incBetween D Q c Fc hDne Qinv Gc FcGc G_inj inverseVerticesAt inverseEdgesAt
      inverseVerticesZero inverseEdgesZero disjointImage inverseCellZero ia inverseCellRight
      idisjD ineDright
  exact ⟨hDne, (DiamondPathComparison.thirdCells₁ k inverseCellRight ineDright),
        (DiamondPathComparison.thirdCellsDisj k (DiamondPathComparison.Gc_inj k c FcGc)
        disjointImage inverseCellZero inverseCellRight idisjD), (DiamondPathComparison.thirdTurn
        k imagePath incBetween G_inj (DiamondPathComparison.G_step k) inverseVerticesAt
        inverseEdgesAt inverseVerticesZero inverseEdgesZero)⟩

private theorem rowSecond1 :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ (f : GaussianInt → GaussianInt),
            (Function.Injective f) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0,
            1⟩ ∨ b = a - ⟨0, 1⟩) → f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a
            - ⟨0, 1⟩) → ((SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (f '' V) ((fun
            e : Finset GaussianInt => e.image f) '' E) (f x) (f y))))) → ((SimpleGridPathBetween
            (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩))
            (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩)) ⟨(1 : ℤ), (0 : ℤ)⟩ ⟨(↑k : ℤ), (↑k :
            ℤ)⟩) → (
        let D := DiamondTile k
        (TileTranslation D 0 = D) → ((∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
            GaussianInt), (TileTranslation T (u + v)).cells = (TileTranslation (TileTranslation T
            u) v).cells) → ((∀ {A : ProtoTile}, ∀ {B : ProtoTile}, A.cells = B.cells →
            BoundaryFootprintEdges A = BoundaryFootprintEdges B) → ((∀ {A : ProtoTile}, ∀
            {B : ProtoTile}, A.cells = B.cells → Finset.Nonempty B.cells →
            BoundaryFootprintVertices A = BoundaryFootprintVertices B) → ((
        let D := DiamondTile k; Finset.Nonempty D.cells) → (
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (∀ (u : GaussianInt), Function.Injective (GaussianTranslation u)) → (((TileTranslation D
            shift).cells.Nonempty) → ((Disjoint D.cells (TileTranslation D shift).cells) →
            (Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D shift).cells ∧ Disjoint
            D.cells (TileTranslation D shift).cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D shift))
            (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D shift)) ⟨-(k :
            Int), (k : Int)⟩ ⟨-1, 2 * (k : Int)⟩)))))))))) ) := by
  classical
  intro k imagePath incBetween D dzeroD translateCells edgeCellsEq vertexCellsEq hDne shift
      translateInj fourthCells₂ fourthCellsDisj
  exact ⟨hDne, fourthCells₂, fourthCellsDisj, (DiamondPathComparison.fourthPath k
        (DiamondPathComparison.shiftPath k imagePath incBetween dzeroD translateCells edgeCellsEq
        vertexCellsEq hDne (DiamondPathComparison.translateStep) translateInj))⟩

private theorem h0 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
          2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩) = {z : GaussianInt | (1 : ℤ) ≤ z.re ∧
            z.re ≤ (↑k : ℤ) ∧ (2 : ℤ) * (↑k : ℤ) ≤ z.re + z.im ∧ z.re + z.im ≤ (2 : ℤ) * (↑k : ℤ)
            + (1 : ℤ)}) → (
        let D := DiamondTile k
        let Q := GaussianQuarterTurn
        (TileTranslation D 0 = D) → (∀ (c : GaussianInt), (c = ⟨(↑k : ℤ), (↑k : ℤ)⟩) → (
        (
        let F := fun (z : GaussianInt) => GaussianQuarterTurn z + c; Function.Injective F) → ((∀
            (d : GaussianInt), BoundaryFootprintVertices (TileTranslation (DiamondTile k)
            (GaussianQuarterTurn d)) = (fun (z : GaussianInt) => GaussianQuarterTurn z + c) ''
            BoundaryFootprintVertices (TileTranslation (DiamondTile k) d)) → ((
        let Q := GaussianQuarterTurn; Q ⟨(↑k : ℤ) + (1 : ℤ), (↑k : ℤ)⟩ = ⟨-(↑k : ℤ), (↑k : ℤ) +
            (1 : ℤ)⟩) → ((Q 0 = 0) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D da) = dV) →
            ((Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D ⟨-(k : Int), (k : Int)
            + 1⟩).cells ∧ Disjoint D.cells (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩).cells
            ∧ SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩)) (BoundaryFootprintEdges D ∩
            BoundaryFootprintEdges (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩)) ⟨0, 2 * (k :
            Int)⟩ ⟨-(k : Int), (k : Int) + 1⟩) → ((Finset.Nonempty D.cells ∧ Finset.Nonempty
            (TileTranslation D da).cells ∧ Disjoint D.cells (TileTranslation D da).cells ∧
            SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D da)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D da)) ⟨1, 2 * (k : Int)⟩ ⟨(k : Int), (k : Int)⟩) → ((∀ T, ∀ U, ∀ a,
            ∀ e, (T, U, a, e) ∈ [(D, TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩, (⟨0, 2 * (k :
            Int)⟩ : GaussianInt), ⟨-(k : Int), (k : Int) + 1⟩), (D, TileTranslation D da, (⟨1, 2
            * (k : Int)⟩ : GaussianInt), ⟨(k : Int), (k : Int)⟩)] → Finset.Nonempty T.cells ∧
            Finset.Nonempty U.cells ∧ Disjoint T.cells U.cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges T
            ∩ BoundaryFootprintEdges U) a e) ∧ (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D ⟨-(k : Int), (k : Int) + 1⟩) = {z | -(k
            : Int) ≤ z.re ∧ z.re ≤ 0 ∧ (k : Int) + 1 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k :
            Int) ≤ z.im - z.re ∧ z.im - z.re ≤ 2 * (k : Int) + 1}) ∧ (BoundaryFootprintVertices D
            ∩ BoundaryFootprintVertices (TileTranslation D da) = {z | 1 ≤ z.re ∧ z.re ≤ (k : Int)
            ∧ (k : Int) ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im
            ≤ 2 * (k : Int) + 1}))))))))))) ) := by
  classical
  intro k dV decVertices D Q dzeroD c hcEq F_inj quarterVerticesAt dShift zeroQ da secondVertices
      rowFirst0 rowSecond0
  let F : GaussianInt → GaussianInt := fun z => Q z + c
  exact DiamondPathComparison.h0 k c
                (DiamondPathComparison.firstVertices k decVertices c F_inj
                (DiamondPathComparison.zeroFvertices k dzeroD c quarterVerticesAt zeroQ)
                (DiamondPathComparison.rightFvertices k c quarterVerticesAt dShift))
                secondVertices (DiamondPathComparison.firstSet k c hcEq)
                    (DiamondPathComparison.secondSet k) (DiamondPathComparison.rows0 k
                    rowFirst0 rowSecond0)

private theorem h1 :
    (by
      classical
      exact
        ∀ (k : Nat), (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices
            (TileTranslation (DiamondTile k) ⟨(↑k : ℤ) + (1 : ℤ), -(↑k : ℤ)⟩) = {z : GaussianInt
            | (1 : ℤ) ≤ z.re ∧ z.re ≤ (↑k : ℤ) ∧ z.re - (1 : ℤ) ≤ z.im ∧ z.im ≤ z.re}) → (
        let D := DiamondTile k
        let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
        (Function.Injective fun (z : GaussianInt) => (⟨z.im - (↑k : ℤ), (↑k : ℤ) - z.re⟩ :
            GaussianInt)) → ((∀ (d
            : GaussianInt), (fun (z : GaussianInt) => (⟨z.im - (↑k : ℤ), (↑k : ℤ) - z.re⟩ :
                GaussianInt)) ''
            BoundaryFootprintVertices (TileTranslation (DiamondTile k) d) =
            BoundaryFootprintVertices (TileTranslation (DiamondTile k) ((fun (z : GaussianInt) =>
                (⟨z.im, -z.re⟩ : GaussianInt)) d))) → (((fun (z : GaussianInt) => (⟨z.im - (↑k :
                ℤ), (↑k : ℤ) - z.re⟩ : GaussianInt))
            '' BoundaryFootprintVertices (DiamondTile k) = BoundaryFootprintVertices (DiamondTile
            k)) → (
        let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
        let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
        (∀ (u : GaussianInt), Function.Injective (GaussianTranslation u)) →
            ((BoundaryFootprintVertices (TileTranslation (TileTranslation D ia) shift) =
            BoundaryFootprintVertices D) → ((Finset.Nonempty D.cells ∧ Finset.Nonempty
            (TileTranslation D (Qinv ia)).cells ∧ Disjoint D.cells (TileTranslation D (Qinv
            ia)).cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D (Qinv ia))) (BoundaryFootprintEdges D ∩
            BoundaryFootprintEdges (TileTranslation D (Qinv ia))) ⟨-(k : Int), (k : Int) - 1⟩ 0)
            → ((Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D shift).cells ∧
            Disjoint D.cells (TileTranslation D shift).cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D shift))
            (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D shift)) ⟨-(k :
            Int), (k : Int)⟩ ⟨-1, 2 * (k : Int)⟩) → ((∀ T, ∀ U, ∀ a, ∀ e, (T, U, a, e) ∈ [(D,
            TileTranslation D (Qinv ia), (⟨-(k : Int), (k : Int) - 1⟩ : GaussianInt), 0), (D,
            TileTranslation D shift, (⟨-(k : Int), (k : Int)⟩ : GaussianInt), ⟨-1, 2 * (k :
            Int)⟩)] → Finset.Nonempty T.cells ∧ Finset.Nonempty U.cells ∧ Disjoint T.cells
            U.cells ∧ SimpleGridPathBetween (BoundaryFootprintVertices T ∩
            BoundaryFootprintVertices U) (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a
            e) ∧ (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D
            (Qinv ia)) = {z | -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ (k : Int) - 1 ∧ -1
            ≤ z.re + z.im ∧ z.re + z.im ≤ 0}) ∧ (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices (TileTranslation D shift) = {z | -(k : Int) ≤ z.re ∧ z.re ≤
            -1 ∧ (k : Int) ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧ z.im -
            z.re ≤ 2 * (k : Int) + 1}))))))))) ) := by
  classical
  intro k incVertices D Qinv G_inj inverseVerticesAt inverseVerticesZero ia shift translateInj
      hnestedV rowFirst1 rowSecond1
  exact DiamondPathComparison.h1 k
                (DiamondPathComparison.thirdVertices k incVertices G_inj inverseVerticesAt
                inverseVerticesZero)
                (DiamondPathComparison.fourthVertices k (DiamondPathComparison.shiftVertices k
                    incVertices translateInj hnestedV)) (DiamondPathComparison.thirdSet k)
                    (DiamondPathComparison.fourthSet k) (DiamondPathComparison.rows1 k
                    rowFirst1 rowSecond1)

end DiamondRowConclusions

namespace DiamondRowPaths

private theorem secondPath :
    (by
      classical
      exact
        ∀ (k : Nat), (SimpleGridPathBetween (BoundaryFootprintVertices (DiamondTile k) ∩
            BoundaryFootprintVertices (TileTranslation (DiamondTile k) (⟨(↑k : ℤ) + (1 : ℤ), (↑k
            : ℤ)⟩ : GaussianInt))) (BoundaryFootprintEdges (DiamondTile k) ∩
            BoundaryFootprintEdges (TileTranslation (DiamondTile k) (⟨(↑k : ℤ) + (1 : ℤ), (↑k :
            ℤ)⟩ : GaussianInt))) (⟨(↑k : ℤ), (↑k : ℤ)⟩ : GaussianInt) (⟨(1 : ℤ), (2 : ℤ) * (↑k :
            ℤ)⟩ : GaussianInt)) → (
        let D := DiamondTile k
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D da)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D da)) ⟨1, 2 * (k : Int)⟩ ⟨(k : Int), (k : Int)⟩) ) := by
  classical
  intro k decBetween D da
  exact (DiamondPathComparison.reversePath) decBetween

private theorem rowSecond0 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (
        let D := DiamondTile k; Finset.Nonempty D.cells) → (
        let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        (SimpleGridPathBetween (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices
            (TileTranslation D da)) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges
            (TileTranslation D da)) ⟨1, 2 * (k : Int)⟩ ⟨(k : Int), (k : Int)⟩) → ((Disjoint
            D.cells (TileTranslation D da).cells) → (((TileTranslation D da).cells.Nonempty) →
            (Finset.Nonempty D.cells ∧ Finset.Nonempty (TileTranslation D da).cells ∧ Disjoint
            D.cells (TileTranslation D da).cells ∧ SimpleGridPathBetween
            (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (TileTranslation D da))
            (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges (TileTranslation D da)) ⟨1, 2 * (k
            : Int)⟩ ⟨(k : Int), (k : Int)⟩)))) ) := by
  classical
  intro k D hDne da secondPath secondCellsDisj secondCells₂
  exact ⟨hDne, secondCells₂, secondCellsDisj, secondPath⟩

end DiamondRowPaths

theorem P5290T1EqualDiamondPaths (k : Nat) (hk : 0 < k)
    (i : Fin 3) (hi : i ≠ 2) :
    let M := P5260T1PlacementLedger k i false
    let D := DiamondTile k
    let x := M.2.2.1
    let y := M.2.2.2
    let eR : GaussianInt := if i = 0 then ⟨-(k : Int), (k : Int) + 1⟩ else 0
    let eI : GaussianInt := if i = 0 then ⟨(k : Int), (k : Int)⟩ else ⟨-1, 2 * (k : Int)⟩
    let rows : List (ProtoTile × ProtoTile × GaussianInt × GaussianInt) :=
      [(D, TileTranslation D M.2.1.1, x, eR),
       (D, TileTranslation D M.2.1.2, y, eI)]
    (∀ T U a c, (T, U, a, c) ∈ rows →
      T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
      SimpleGridPathBetween
        (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
        (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) a c) ∧
    BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices (TileTranslation D M.2.1.1) =
      {z | if i = 0 then
        -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ (k : Int) + 1 ≤ z.im ∧
          z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧
          z.im - z.re ≤ 2 * (k : Int) + 1
      else
        -(k : Int) ≤ z.re ∧ z.re ≤ 0 ∧ 0 ≤ z.im ∧
          z.im ≤ (k : Int) - 1 ∧ -1 ≤ z.re + z.im ∧ z.re + z.im ≤ 0} ∧
    BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices (TileTranslation D M.2.1.2) =
      {z | if i = 0 then
        1 ≤ z.re ∧ z.re ≤ (k : Int) ∧ (k : Int) ≤ z.im ∧
          z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.re + z.im ∧
          z.re + z.im ≤ 2 * (k : Int) + 1
      else
        -(k : Int) ≤ z.re ∧ z.re ≤ -1 ∧ (k : Int) ≤ z.im ∧
          z.im ≤ 2 * (k : Int) ∧ 2 * (k : Int) ≤ z.im - z.re ∧
          z.im - z.re ≤ 2 * (k : Int) + 1} := by
-- BODY
  classical
  have staircaseBetween (z : GaussianInt) (h : Bool) (s : Int)
      (hs : s = 1 ∨ s = -1) (N : Nat) (hN : 0 < N) := DiamondPathComparison.staircaseBetween k z
          h s hs N hN
  have imagePath {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {x y : GaussianInt} (f : GaussianInt → GaussianInt)
      (hf : Function.Injective f)
      (hstep : ∀ a b : GaussianInt,
        (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
        f b = f a + 1 ∨ f b = f a - 1 ∨
          f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)
      (hp : SimpleGridPathBetween V E x y) := DiamondRowConclusions.imagePath (V := V) (E := E)
          (x := x) (y := y) f hf hstep hp
  let q : Nat → GaussianInt :=
    P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
  let N : Nat := 2 * k - 1
  have hN : 0 < N := by dsimp [N]; omega
  have qbase := staircaseBetween ⟨(k : Int), -(k : Int)⟩ true 1
    (Or.inl rfl) N hN
  have qinj := DiamondPathComparison.qinj k
  have qImagePath := imagePath GaussianQuarterTurn qinj (DiamondPathComparison.qstep k) qbase
  have qenum (j : Nat) := DiamondPathComparison.qenum k j
  let dV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
    2 * (k : Int) ≤ z.re + z.im ∧ z.re + z.im ≤ 2 * (k : Int) + 1}
  let dP : Nat → GaussianInt := fun j =>
    ⟨(k : Int) - (j / 2 : Nat), (k : Int) + ((j + 1) / 2 : Nat)⟩
  let dE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {dP j, dP (j + 1)}}
  have dq (j : Nat) : GaussianQuarterTurn (q j) = dP j := by
    exact qenum j
  have dec := P5203T1DecreasingInterface k hk 0
  dsimp only at dec
  rcases dec with ⟨dne, dne', ddisj, dvertices, dedges, _⟩
  have dzero : TileTranslation (DiamondTile k) 0 = DiamondTile k := DiamondPathComparison.dzero k
  rw [dzero] at dvertices dedges
  have decVertices := DiamondPathComparison.decVertices k dvertices
  have decEdges := DiamondPathComparison.decEdges k dedges
  have decBetween := DiamondPathComparison.decBetween k (DiamondPathComparison.decPath k
      qImagePath (DiamondPathComparison.qendpoint₀ k qenum) (DiamondPathComparison.qendpoint₁ k
      hk qenum) (DiamondPathComparison.dVimage k dq (DiamondPathComparison.dVenum k hk hN))
      (DiamondPathComparison.dEimage k dq)) decVertices decEdges
  let iV : Set GaussianInt := {z | 1 ≤ z.re ∧ z.re ≤ k ∧
    z.re - 1 ≤ z.im ∧ z.im ≤ z.re}
  let iP : Nat → GaussianInt := fun j =>
    ⟨1 + (j / 2 : Nat), ((j + 1) / 2 : Nat)⟩
  let iE : Set (Finset GaussianInt) := {e | ∃ j < N, e = {iP j, iP (j + 1)}}
  let iq : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
  have iqenum (j : Nat) : iq j = iP j := by
    apply Zsqrtd.ext <;> simp [iq, iP, P5157T1StaircasePoint]
  have iEeq := DiamondPathComparison.iEeq k iqenum
  have inc := P5203T1IncreasingInterface k hk 0
  dsimp only at inc
  rcases inc with ⟨ine, ine', idisj, ivertex0, iedge0, _⟩
  have izero : TileTranslation (DiamondTile k) 0 = DiamondTile k := dzero
  rw [izero] at ivertex0 iedge0
  have incVertices := DiamondPathComparison.incVertices k ivertex0
  have incEdges := DiamondPathComparison.incEdges k iedge0
  have incBetween := DiamondPathComparison.incBetween k (DiamondPathComparison.incEnumPath k hk
      staircaseBetween hN (DiamondPathComparison.iVenum k hk hN)) incVertices incEdges
  let D := DiamondTile k
  let Q := GaussianQuarterTurn
  have dzeroD : TileTranslation D 0 = D := by
    simpa [D] using dzero
  have dzeroD' : TileTranslation D ⟨0, 0⟩ = D := DiamondPathComparison.dzeroD' k
  obtain ⟨c, hc, hcCells, _, _, _⟩ :=
    QuarterTurnSymmetricCenteredTransport D (DiamondBaseT2 ⟨k, hk⟩)
  have hcEq : c = ⟨(k : Int), (k : Int)⟩ := DiamondPathComparison.hcEq k hk c hc
  rw [hcEq] at hcCells
  let F : GaussianInt → GaussianInt := fun z => Q z + c
  let Fc : GaussianInt → GaussianInt := fun z => Q z - 1 + c
  have F_inj := DiamondPathComparison.F_inj qinj c
  have translateCells (T : ProtoTile) (u v : GaussianInt) :
      (TileTranslation T (u + v)).cells =
        (TileTranslation (TileTranslation T u) v).cells := DiamondPathComparison.translateCells T
            u v
  have quarterCells (d : GaussianInt) := DiamondPathComparison.quarterCells k c hcCells hcEq
      translateCells d
  have quarterCellMap (d : GaussianInt) :
      (TileTranslation D (Q d)).cells =
        ((TileTranslation D d).cells.image Fc) := DiamondPathComparison.quarterCellMap k c
            quarterCells d
  have edgeCellsEq {A B : ProtoTile} (hab : A.cells = B.cells) :=
      DiamondPathComparison.edgeCellsEq (A := A) (B := B) hab
  have vertexCellsEq {A B : ProtoTile} (hab : A.cells = B.cells)
      (hne : B.cells.Nonempty) := DiamondPathComparison.vertexCellsEq (A := A) (B := B) hab hne
  have hDne := DiamondPathComparison.hDne k dne dzero
  have quarterVerticesAt (d : GaussianInt) := DiamondPathComparison.quarterVerticesAt k c
      quarterCells vertexCellsEq (DiamondPathComparison.quarterTranslatedDne k c quarterCells
          (DiamondPathComparison.translatedDne k hDne)) d
  have quarterEdgesAt (d : GaussianInt) := DiamondPathComparison.quarterEdgesAt k c quarterCells
      edgeCellsEq d
  have dShift := DiamondPathComparison.dShift k
  let Qinv : GaussianInt → GaussianInt := fun z => ⟨z.im, -z.re⟩
  let G : GaussianInt → GaussianInt := fun z =>
    ⟨z.im - (k : Int), (k : Int) - z.re⟩
  let Gc : GaussianInt → GaussianInt := fun z =>
    ⟨z.im - (k : Int), (k : Int) - 1 - z.re⟩
  have qInvLeft (z : GaussianInt) : Q (Qinv z) = z := by
    apply Zsqrtd.ext <;> simp [Q, Qinv, GaussianQuarterTurn]
  have qInvRight (z : GaussianInt) : Qinv (Q z) = z := by
    apply Zsqrtd.ext <;> simp [Q, Qinv, GaussianQuarterTurn]
  have GF (z : GaussianInt) : G (F z) = z := by
    apply Zsqrtd.ext <;> simp [G, F, Q, GaussianQuarterTurn, hcEq]
  have FG (z : GaussianInt) : F (G z) = z := by
    apply Zsqrtd.ext <;> simp [G, F, Q, GaussianQuarterTurn, hcEq]
  have GcFc (z : GaussianInt) : Gc (Fc z) = z := by
    apply Zsqrtd.ext <;> simp [Gc, Fc, Q, GaussianQuarterTurn, hcEq]; ring
  have FcGc (z : GaussianInt) : Fc (Gc z) = z := by
    apply Zsqrtd.ext <;> simp [Gc, Fc, Q, GaussianQuarterTurn, hcEq]; ring
  have G_inj := DiamondPathComparison.G_inj k c FG
  have inverseVerticesAt (d : GaussianInt) := DiamondPathComparison.inverseVerticesAt k c
      quarterVerticesAt qInvLeft GF d
  have inverseEdgesAt (d : GaussianInt) := DiamondPathComparison.inverseEdgesAt k c
      quarterEdgesAt qInvLeft GF d
  have inverseCellAt (d : GaussianInt) :
      (TileTranslation D (Qinv d)).cells =
        ((TileTranslation D d).cells.image Gc) := DiamondPathComparison.inverseCellAt k c
            quarterCellMap qInvLeft GcFc d
  have qInvZero : Qinv 0 = 0 := by
    apply Zsqrtd.ext <;> simp [Qinv]
  have inverseVerticesZero := DiamondPathComparison.inverseVerticesZero k dzeroD
      inverseVerticesAt qInvZero
  have inverseEdgesZero := DiamondPathComparison.inverseEdgesZero k dzeroD inverseEdgesAt qInvZero
  have zeroQ : Q 0 = 0 := by
    apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn]
  have cellMapZero : D.cells = D.cells.image Fc := by
    simpa [zeroQ, dzeroD, dzeroD', D] using quarterCellMap 0
  let da : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
  have cellMapRight := DiamondPathComparison.cellMapRight k c quarterCellMap dShift
  have ddisjD := DiamondPathComparison.ddisjD k ddisj dzeroD
  have dneDright : (TileTranslation D da).cells.Nonempty := by
    simpa only [zero_add] using dne'
  have disjointImage {α : Type} [DecidableEq α] {s t : Finset α} (f : α → α)
      (hf : Function.Injective f) (hdis : Disjoint s t) := DiamondPathComparison.disjointImage (α
          := α) (s := s) (t := t) f hf hdis
  have inverseCellZero : D.cells = D.cells.image Gc := by
    simpa [Qinv, qInvZero, dzeroD, dzeroD', D] using inverseCellAt 0
  let ia : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
  have inverseCellRight : (TileTranslation D (Qinv ia)).cells =
      (TileTranslation D ia).cells.image Gc := inverseCellAt ia
  have idisjD := DiamondPathComparison.idisjD k idisj dzeroD
  have ineDright : (TileTranslation D ia).cells.Nonempty := by
    simpa only [zero_add] using ine'
  have iaTurn : Qinv ia = ⟨-(k : Int), -(k : Int) - 1⟩ := by
    apply Zsqrtd.ext <;> simp [Qinv, ia]; ring
  have iaNeg : ⟨-(k : Int) - 1, (k : Int)⟩ + ia = 0 := by
    apply Zsqrtd.ext <;> simp [ia]
  let shift : GaussianInt := ⟨-(k : Int) - 1, (k : Int)⟩
  have translateInj (u : GaussianInt) := DiamondPathComparison.translateInj u
  have shiftCellsOne := DiamondPathComparison.shiftCellsOne k
  have hsum : ia + shift = 0 := by
    apply Zsqrtd.ext <;> simp [ia, shift]
  have hnested : (TileTranslation (TileTranslation D ia) shift).cells = D.cells := by
    rw [← translateCells D ia shift, hsum, dzeroD]
  have hnestedV : BoundaryFootprintVertices
      (TileTranslation (TileTranslation D ia) shift) = BoundaryFootprintVertices D :=
    vertexCellsEq hnested hDne
  have hnestedE : BoundaryFootprintEdges
      (TileTranslation (TileTranslation D ia) shift) = BoundaryFootprintEdges D :=
    edgeCellsEq hnested
  have secondPath := DiamondRowPaths.secondPath k decBetween
  have secondCellsDisj : Disjoint D.cells (TileTranslation D da).cells := ddisjD
  have secondCells₂ : (TileTranslation D da).cells.Nonempty := dneDright
  have fourthCells₂ : (TileTranslation D shift).cells.Nonempty :=
      (DiamondPathComparison.shiftCellsNonempty k hDne shiftCellsOne)
  have fourthCellsDisj : Disjoint D.cells (TileTranslation D shift).cells :=
    (DiamondPathComparison.shiftCellsDisjoint k disjointImage idisjD translateInj shiftCellsOne
        (DiamondPathComparison.shiftCellsTwo k dzeroD translateCells))
  have secondVertices : BoundaryFootprintVertices D ∩
      BoundaryFootprintVertices (TileTranslation D da) = dV := decVertices
  have firstEdges := DiamondPathComparison.firstEdges k decEdges c F_inj
      (DiamondPathComparison.zeroFedges k dzeroD c quarterEdgesAt zeroQ)
      (DiamondPathComparison.rightFedges k c quarterEdgesAt dShift)
  have thirdEdges := DiamondPathComparison.thirdEdges k incEdges G_inj inverseEdgesAt
      inverseEdgesZero
  have fourthEdges := DiamondPathComparison.fourthEdges k (DiamondPathComparison.shiftEdges k
      incEdges translateInj hnestedE)
  have rowFirst0 := DiamondRowConclusions.rowFirst0 k imagePath qinj decBetween dzeroD c hcEq
      F_inj hDne quarterVerticesAt quarterEdgesAt dShift cellMapZero cellMapRight ddisjD
      dneDright disjointImage
  have rowSecond0 := DiamondRowPaths.rowSecond0 k hDne secondPath secondCellsDisj secondCells₂
  have rowFirst1 := DiamondRowConclusions.rowFirst1 k imagePath incBetween c hDne FcGc G_inj
      inverseVerticesAt inverseEdgesAt inverseVerticesZero inverseEdgesZero disjointImage
      inverseCellZero inverseCellRight idisjD ineDright
  have rowSecond1 := DiamondRowConclusions.rowSecond1 k imagePath incBetween dzeroD
      translateCells edgeCellsEq vertexCellsEq hDne translateInj fourthCells₂ fourthCellsDisj
  fin_cases i
  · have h0 := DiamondRowConclusions.h0 k decVertices dzeroD
                  c hcEq F_inj quarterVerticesAt dShift zeroQ secondVertices rowFirst0 rowSecond0
    simpa [P5260T1PlacementLedger] using h0
  · have h1 := DiamondRowConclusions.h1 k incVertices G_inj
                  inverseVerticesAt inverseVerticesZero translateInj hnestedV rowFirst1 rowSecond1
    simpa [P5260T1PlacementLedger, iaTurn, shift, Qinv, sub_eq_add_neg, add_comm] using h1
  · exact (hi rfl).elim

end ApollonianSuperharmonic

end
