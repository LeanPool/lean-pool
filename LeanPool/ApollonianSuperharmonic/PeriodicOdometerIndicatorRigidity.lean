/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FootprintFiniteness

public import LeanPool.ApollonianSuperharmonic.BandTileAcyclicIndegree
public import LeanPool.ApollonianSuperharmonic.FiniteAcyclicOrientationObstruction
public import LeanPool.ApollonianSuperharmonic.PeriodicBoundaryWebConnected

-- [TABLET NODE: PeriodicOdometerIndicatorRigidity]

/-!
# PeriodicOdometerIndicatorRigidity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PeriodicIndicatorGeometry

private theorem hmeet :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (X : Set GaussianInt), (X.Infinite) →
            ((FourNeighborConnected X) → ((∀ (X : Set GaussianInt), FourNeighborConnected X →
            Disjoint X {x : GaussianInt | ∃ v ∈ TilingLattice C, x ∈ BoundaryFootprintVertices
            (TileTranslation T v)} → ∃ v ∈ TilingLattice C, X ⊆ FootprintVertices
            (TileTranslation T v) \ {x : GaussianInt | ∃ v ∈ TilingLattice C, x ∈
            BoundaryFootprintVertices (TileTranslation T v)}) → ((∀ (U : ProtoTile),
            (FootprintVertices U).Finite) → ((X ∩ {x | ∃ v, v ∈ TilingLattice C ∧ x ∈
            BoundaryFootprintVertices (TileTranslation T v)}).Nonempty)))) ) := by
  classical
  intro C T X hXin hXconn hWcontain finiteFoot
  by_contra hn
  have hd : Disjoint X {x | ∃ v, v ∈ TilingLattice C ∧
      x ∈ BoundaryFootprintVertices (TileTranslation T v)} := by
    rw [Set.disjoint_left]
    intro x hx hwx
    exact hn ⟨x, hx, hwx⟩
  obtain ⟨v, hv, hs⟩ := hWcontain X hXconn hd
  exact hXin.not_finite ((finiteFoot _).subset (fun z hz => (hs hz).1))

private theorem noCross :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (g : IntegerLatticeFunction), (∀ x, (∃ v, v ∈
            TilingLattice C ∧ x ∈ BoundaryFootprintVertices (TileTranslation T v)) →
            FourNeighborLaplacian g x = 1) → (∀ (X : Set GaussianInt), (∀ (x : GaussianInt),
                FourNeighborLaplacian (fun (y : GaussianInt) => g y + X.indicator (fun (_ :
            GaussianInt) => (1 : ℤ)) y) x ≤ (1 : ℤ)) → (∀ a ∈ {x | ∃ v, v ∈ TilingLattice C ∧ x ∈
            BoundaryFootprintVertices (TileTranslation T v)}, ∀ b, FourNeighborAdjacent a b → b ∈
            X → a ∈ X))) := by
  classical
  intro C T g hweb X hle a ha b hab hb
  rcases hab with rfl | rfl | rfl | rfl
  all_goals
    by_contra hna
    obtain ⟨v, hv, hav⟩ := ha
    have hga := hweb a ⟨v, hv, hav⟩
    have hh := hle a
    simp only [FourNeighborLaplacian, Set.indicator_apply] at hh hga ⊢
    simp_all only [ite_true, ite_false]
    omega

private theorem hWsub :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (X : Set GaussianInt), (FourNeighborConnected {x
            : GaussianInt | ∃ v ∈ TilingLattice C, x ∈ BoundaryFootprintVertices (TileTranslation
            T v)}) → (((X ∩ {x | ∃ v, v ∈ TilingLattice C ∧ x ∈ BoundaryFootprintVertices
            (TileTranslation T v)}).Nonempty) → ((∀ a ∈ {x | ∃ v, v ∈ TilingLattice C ∧ x ∈
            BoundaryFootprintVertices (TileTranslation T v)}, ∀ b, FourNeighborAdjacent a b → b ∈
            X → a ∈ X) → ({x | ∃ v, v ∈ TilingLattice C ∧ x ∈ BoundaryFootprintVertices
            (TileTranslation T v)} ⊆ X))) ) := by
  classical
  intro C T X hWconn hmeet noCross w hw
  obtain ⟨x0, hx0, hx0W⟩ := hmeet
  obtain ⟨p, hp, hpend, hpall, hadj⟩ := hWconn.2 x0 hx0W w hw
  have symmetry : ∀ a b, FourNeighborAdjacent a b →
      FourNeighborAdjacent b a := by
    intro a b hab
    rcases hab with rfl | rfl | rfl | rfl <;>
      simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
  have walk : ∀ (q : List GaussianInt), ∀ a, q.head? = some a → a ∈ X →
      (∀ z ∈ q, z ∈ {x | ∃ v, v ∈ TilingLattice C ∧
        x ∈ BoundaryFootprintVertices (TileTranslation T v)}) →
      (∀ a b l₁ l₂, q = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b) → ∀ z ∈ q, z ∈ X := by
    intro q
    induction q with
    | nil => intro a hq; simp at hq
    | cons z q ih =>
      intro a hq haX hwq hstep
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst a
      intro b hb
      simp only [List.mem_cons] at hb
      cases q with
      | nil =>
        rcases hb with rfl | hb
        · exact haX
        · simp at hb
      | cons y q =>
        have hzy : FourNeighborAdjacent z y := by
          apply hstep z y [] q
          simp
        have hzW := hwq z (by simp)
        have hyW := hwq y (by simp)
        have hyX : y ∈ X := by
          exact noCross y hyW z (symmetry z y hzy) haX
        rcases hb with rfl | hb
        · exact haX
        · have htail := ih y (by rfl) hyX (by
            intro t ht
            exact hwq t (by simp [ht])) (by
            intro c d l₁ l₂ hq
            apply hstep c d (z :: l₁) l₂
            simp [hq])
          exact htail b hb
  have hall := walk p x0 hp hx0 hpall hadj
  have hne : p ≠ [] := by intro he; simp [he] at hp
  have hwmem : w ∈ p := by
    rw [← List.getLast_of_getLast?_eq_some hpend]
    exact List.getLast_mem hne
  exact hall w hwmem

private theorem xY :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt), (x ∉ X) → (
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        x ∈ Y) ) := by
  classical
  intro X x hxX reachable Y
  refine ⟨[x], ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro z hz
    have hz' : z = x := by simpa using hz
    simpa [hz'] using hxX
  · exact List.isChain_singleton _

private theorem Yout :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        Y ⊆ Xᶜ ) := by
  classical
  intro X x reachable Y y hy
  rcases hy with ⟨p, hp, hlast, hpout, hchain⟩
  intro hyX
  have hmem : y ∈ p := by
    rw [← List.getLast_of_getLast?_eq_some hlast]
    exact List.getLast_mem (by intro he; simp [he] at hp)
  exact hpout y hmem hyX

private theorem Yconn :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        (x ∈ Y) → (FourNeighborConnected Y) ) := by
  classical
  intro X x reachable Y xY
  refine ⟨⟨x, xY⟩, ?_⟩
  intro y hy z hz
  rcases hy with ⟨p, hp, hpy, hpout, hpc⟩
  rcases hz with ⟨q, hq, hqz, hqout, hqc⟩
  have hsym : ∀ a b, FourNeighborAdjacent a b →
      FourNeighborAdjacent b a := by
    intro a b hab
    rcases hab with rfl | rfl | rfl | rfl <;>
      simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
  have prefixReach : ∀ (r : List GaussianInt), r.head? = some x →
      (∀ t ∈ r, t ∉ X) → r.IsChain FourNeighborAdjacent →
      ∀ t ∈ r, t ∈ Y := by
    intro r hr hout hchain t ht
    obtain ⟨l₁, l₂, heq⟩ := List.mem_iff_append.mp ht
    subst r
    refine ⟨l₁ ++ [t], ?_, ?_, ?_, ?_⟩
    · simpa using hr
    · simp
    · intro u hu
      simp only [List.mem_append, List.mem_cons] at hu
      rcases hu with hu | rfl | hu
      · exact hout u (by simp [hu])
      · exact hout u (by simp)
      · simp at hu
    · exact (List.isChain_split.mp hchain).1
  have hpc' : p.IsChain (fun a b => FourNeighborAdjacent b a) :=
    hpc.imp (fun a b hab => hsym a b hab)
  have hrev : p.reverse.IsChain FourNeighborAdjacent :=
    List.isChain_reverse.mpr hpc'
  have hqtail : q.tail.IsChain FourNeighborAdjacent := hqc.tail
  have hqn : q ≠ [] := by intro he; simp [he] at hq
  have hjoin : (p.reverse ++ q.tail).IsChain FourNeighborAdjacent := by
    apply hrev.append hqtail
    intro a ha b hb
    have ha' : a = x := by
      simpa [hp] using ha.symm
    subst a
    cases q with
    | nil => simp at hq
    | cons u s =>
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst u
      cases s with
      | nil => simp at hb
      | cons u s =>
        have hfirst : FourNeighborAdjacent x u :=
          (List.isChain_cons_cons.mp hqc).1
        rcases (by simpa using hb : u = b) with rfl
        exact hfirst
  have hreach : ∀ a ∈ p.reverse ++ q.tail, a ∈ Y := by
    intro a ha
    simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · apply prefixReach p hp hpout hpc a
      simpa using ha
    · apply prefixReach q hq hqout hqc a
      exact List.mem_of_mem_tail (l := q) ha
  refine ⟨p.reverse ++ q.tail, ?_, ?_, hreach,
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hjoin⟩
  · simp [List.head?_append, hpy]
  · cases q with
    | nil => simp at hq
    | cons u s =>
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst u
      cases s with
      | nil =>
        have hz : x = z := by simpa using hqz
        simpa [hz] using hp
      | cons u s => simpa [List.getLast?_append] using hqz

private theorem Ydis :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (X : Set GaussianInt), ({x | ∃ v, v ∈
            TilingLattice C ∧ x ∈ BoundaryFootprintVertices (TileTranslation T v)} ⊆ X) → (∀ (x :
            GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        (Y ⊆ Xᶜ) → (Disjoint Y {x | ∃ v, v ∈ TilingLattice C ∧ x ∈ BoundaryFootprintVertices
            (TileTranslation T v)})) ) := by
  classical
  intro C T X hWsub x reachable Y Yout
  rw [Set.disjoint_left]
  intro y hy hyW
  exact False.elim ((Yout hy) (hWsub hyW))

private theorem Znonempty :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        (x ∈ Y) → (∀ (v : GaussianInt), ∀ (hYfin : Y.Finite),
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        Z.Nonempty) ) := by
  classical
  intro X x reachable Y xY v hYfin Z
  refine ⟨x - v, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨x, hYfin.mem_toFinset.mpr xY, rfl⟩

private theorem Zsub :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ((h.domain : Set
            GaussianInt) = FootprintVertices T) → (∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        ∀ (v : GaussianInt), (v ∈ TilingLattice C) → ((Y ⊆ FootprintVertices (TileTranslation T
            v) \ {x : GaussianInt | ∃ v ∈ TilingLattice C, x ∈ BoundaryFootprintVertices
            (TileTranslation T v)}) → (∀ (hYfin : Y.Finite),
        let D := h.domain.filter fun p =>
          @decide (p ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        Z ⊆ D))) ) := by
  classical
  intro C T h hdom X x reachable Y v hv hYsub hYfin D Z p hp
  rcases Finset.mem_image.mp hp with ⟨y, hy, rfl⟩
  have hyY : y ∈ Y := hYfin.mem_toFinset.mp hy
  have hyfp := (hYsub hyY).1
  have forms := TileTranslationFormulas T v
  rcases forms with ⟨hcells, hanchor, hempty, hreal, hcent, hfp, hed, hb, hbe⟩
  rw [hfp] at hyfp
  rcases hyfp with ⟨p, hp, hpy⟩
  have hpeq : p = y - v := by
    rw [← hpy]
    simp [GaussianTranslation]
  subst p
  have hpdom : y - v ∈ h.domain := by
    change y - v ∈ (h.domain : Set GaussianInt)
    rw [hdom]
    exact hp
  have hpbd : y - v ∉ BoundaryFootprintVertices T := by
    intro hpbd
    have hybd : y ∈ BoundaryFootprintVertices (TileTranslation T v) := by
      rw [hb]
      exact ⟨y - v, hpbd, by simp [GaussianTranslation]
      ⟩
    exact (hYsub hyY).2 ⟨v, hv, hybd⟩
  exact Finset.mem_filter.mpr ⟨hpdom, by simp [hpbd]
  ⟩

private theorem htrans :
    (by
      classical
      exact
        ∀ (v : GaussianInt), ∀ (p : GaussianInt), ∀ (y : GaussianInt), (y - v = p) → (y = p + v)
            ) := by
  classical
  intro v p y hpy
  rw [← hpy]
  simp [sub_eq_add_neg, add_comm]

private theorem memZ :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        ∀ (v : GaussianInt), ∀ (hYfin : Y.Finite),
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        ∀ (a : GaussianInt), a ∈ Z ↔ a + v ∈ Y ) := by
  classical
  intro X x reachable Y v hYfin Z a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨b, hb, hab⟩
    have hbY : b ∈ Y := hYfin.mem_toFinset.mp hb
    have : b = a + v := by
      rw [← hab]
      simp [sub_eq_add_neg, add_comm]
    simpa [this] using hbY
  · intro ha
    apply Finset.mem_image.mpr
    exact ⟨a + v, hYfin.mem_toFinset.mpr ha, by
      simp [sub_eq_add_neg, add_assoc, add_comm]⟩

private theorem stepReach :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        ∀ (v : GaussianInt), ∀ (p : GaussianInt), ∀ (y : GaussianInt), (y ∈ Y) → ((y = p + v) →
            (∀ (z : GaussianInt), (FourNeighborAdjacent (p + v) z) → ((z ∉ X) → (z ∈ Y)))) ) := by
  classical
  intro X x reachable Y v p y hyY htrans z hz hzX
  rcases hyY with ⟨r, hr, hrlast, hrout, hrc⟩
  refine ⟨r ++ [z], ?_, ?_, ?_, ?_⟩
  · simp [hr]
  · simp [htrans, hrlast]
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hrout a ha
    · exact hzX
  · apply hrc.append (List.isChain_singleton _)
    intro a ha b hb
    have ha' : a = p + v := by simpa [hrlast, htrans] using ha.symm
    subst a
    rcases (by simpa using hb : z = b) with rfl
    exact hz

private theorem neighborMem :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        (Y ⊆ Xᶜ) → (∀ (v : GaussianInt), ∀ (hYfin : Y.Finite),
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        ∀ (p : GaussianInt), (∀ (a : GaussianInt), a ∈ Z ↔ a + v ∈ Y) → ((∀ (z : GaussianInt),
            (FourNeighborAdjacent (p + v) z) → ((z ∉ X) → (z ∈ Y))) → (∀ (z : GaussianInt),
            (FourNeighborAdjacent (p + v) z) → (z ∈ X ↔ z - v ∉ Z)))) ) := by
  classical
  intro X x reachable Y Yout v hYfin Z p memZ stepReach z hz
  constructor
  · intro hzX hzZ
    rcases (memZ (z - v)).mp hzZ with hzY
    have : z ∉ X := by simpa [sub_add_cancel] using (Yout hzY)
    exact this hzX
  · intro hzZ
    by_contra hzX
    have hzY := stepReach z hz hzX
    exact hzZ ((memZ (z - v)).mpr (by simpa [sub_add_cancel] using hzY))

private theorem hlapInd :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        (Y ⊆ Xᶜ) → (∀ (v : GaussianInt), ∀ (hYfin : Y.Finite),
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        ∀ (p : GaussianInt), (p ∈ Z) → (∀ (y : GaussianInt), (y ∈ Y) → ((y = p + v) → ((∀ (z :
            GaussianInt), (FourNeighborAdjacent (p + v) z) → (z ∈ X ↔ z - v ∉ Z)) →
            (FourNeighborLaplacian (fun z => (1 : ℤ) - if z ∈ Z then 1 else 0) p =
            FourNeighborLaplacian (fun z => if z ∈ X then (1 : ℤ) else 0) (p + v)))))) ) := by
  classical
  intro X x reachable Y Yout v hYfin Z p hpZ y hyY htrans neighborMem
  have h1 := neighborMem (p + v + 1) (by simp [FourNeighborAdjacent])
  have h2 := neighborMem (p + v - 1) (by simp [FourNeighborAdjacent])
  have h3 := neighborMem (p + v + ⟨0, 1⟩) (by simp [FourNeighborAdjacent])
  have h4 := neighborMem (p + v - ⟨0, 1⟩) (by simp [FourNeighborAdjacent])
  have hc : p ∈ Z := hpZ
  have hcx : p + v ∉ X := by simpa [htrans] using (Yout hyY)
  have h1' : p + 1 ∈ Z ↔ p + v + 1 ∉ X := by
    have hh := (not_congr h1).symm
    rw [show p + v + 1 - v = p + 1 by abel] at hh
    simp only [not_not] at hh
    exact hh
  have h2' : p - 1 ∈ Z ↔ p + v - 1 ∉ X := by
    have hh := (not_congr h2).symm
    rw [show p + v - 1 - v = p - 1 by abel] at hh
    simp only [not_not] at hh
    exact hh
  have h3' : p + ⟨0, 1⟩ ∈ Z ↔ p + v + ⟨0, 1⟩ ∉ X := by
    have hh := (not_congr h3).symm
    rw [show p + v + ⟨0, 1⟩ - v = p + ⟨0, 1⟩ by abel] at hh
    simp only [not_not] at hh
    exact hh
  have h4' : p - ⟨0, 1⟩ ∈ Z ↔ p + v - ⟨0, 1⟩ ∉ X := by
    have hh := (not_congr h4).symm
    rw [show p + v - ⟨0, 1⟩ - v = p - ⟨0, 1⟩ by abel] at hh
    simp only [not_not] at hh
    exact hh
  have e3 : p + v + ⟨0, 1⟩ ∉ X ↔ p + ⟨0, 1⟩ ∈ Z := h3'.symm
  have e4 : p + v - ⟨0, 1⟩ ∉ X ↔ p - ⟨0, 1⟩ ∈ Z := h4'.symm
  simp only [FourNeighborLaplacian]
  have d1 : p + v + 1 ∉ X ↔ p + 1 ∈ Z := h1'.symm
  have d2 : p + v - 1 ∉ X ↔ p - 1 ∈ Z := h2'.symm
  have d3 : p + v + ⟨0, 1⟩ ∉ X ↔ p + ⟨0, 1⟩ ∈ Z := e3
  have d4 : p + v - ⟨0, 1⟩ ∉ X ↔ p - ⟨0, 1⟩ ∈ Z := e4
  have c1 : (if p + 1 ∈ Z then (1 : ℤ) else 0) =
      1 - (if p + v + 1 ∈ X then (1 : ℤ) else 0) := by
    by_cases hz : p + 1 ∈ Z
    · have hn := d1.mpr hz
      simp [hz, hn]
    · have hx : p + v + 1 ∈ X := by
        by_contra hn
        exact hz (d1.mp hn)
      simp [hz, hx]
  have c2 : (if p - 1 ∈ Z then (1 : ℤ) else 0) =
      1 - (if p + v - 1 ∈ X then (1 : ℤ) else 0) := by
    by_cases hz : p - 1 ∈ Z
    · have hn := d2.mpr hz
      simp [hz, hn]
    · have hx : p + v - 1 ∈ X := by
        by_contra hn
        exact hz (d2.mp hn)
      simp [hz, hx]
  have c3 : (if p + ⟨0, 1⟩ ∈ Z then (1 : ℤ) else 0) =
      1 - (if p + v + ⟨0, 1⟩ ∈ X then (1 : ℤ) else 0) := by
    by_cases hz : p + ⟨0, 1⟩ ∈ Z
    · have hn := d3.mpr hz
      simp [hz, hn]
    · have hx : p + v + ⟨0, 1⟩ ∈ X := by
        by_contra hn
        exact hz (d3.mp hn)
      simp [hz, hx]
  have c4 : (if p - ⟨0, 1⟩ ∈ Z then (1 : ℤ) else 0) =
      1 - (if p + v - ⟨0, 1⟩ ∈ X then (1 : ℤ) else 0) := by
    by_cases hz : p - ⟨0, 1⟩ ∈ Z
    · have hn := d4.mpr hz
      simp [hz, hn]
    · have hx : p + v - ⟨0, 1⟩ ∈ X := by
        by_contra hn
        exact hz (d4.mp hn)
      simp [hz, hx]
  rw [c1, c2]
  rw [c3, c4]
  simp [hc, hcx]

private theorem hcompare :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        ∀ (v : GaussianInt), ∀ (hYfin : Y.Finite),
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        ∀ (p : GaussianInt), (FourNeighborLaplacian (fun z => (1 : ℤ) - if z ∈ Z then 1 else 0) p
            = FourNeighborLaplacian (fun z => if z ∈ X then (1 : ℤ) else 0) (p + v)) →
            ((FourNeighborLaplacian g (p + v) = FourNeighborLaplacian g p) →
            (FourNeighborLaplacian (fun z => g z + 1 - if z ∈ Z then 1 else 0) p =
            FourNeighborLaplacian (fun z => g z + Set.indicator X (fun _ => (1 : ℤ)) z) (p + v)))
            ) := by
  classical
  intro g X x reachable Y v hYfin Z p hlapInd hlapg
  simp only [FourNeighborLaplacian, Set.indicator_apply]
  have hg := hlapg
  simp only [FourNeighborLaplacian] at hg
  have hi := hlapInd
  simp only [FourNeighborLaplacian] at hi
  linarith

private theorem hconst :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), ∀ (X : Set GaussianInt), ∀ (x : GaussianInt),
        let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
          p.head? = some a ∧ p.getLast? = some b ∧
            (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
        let Y : Set GaussianInt := {y | reachable x y}
        ∀ (v : GaussianInt), ∀ (hYfin : Y.Finite),
        let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
        ∀ (p : GaussianInt), FourNeighborLaplacian (fun z => g z + 1 - if z ∈ Z then 1 else 0) p
            = FourNeighborLaplacian (fun z => g z - if z ∈ Z then 1 else 0) p ) := by
  classical
  intro g X x reachable Y v hYfin Z p
  simp only [FourNeighborLaplacian]
  ring

end PeriodicIndicatorGeometry

theorem PeriodicOdometerIndicatorRigidity (C : BandCircle)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hT : BandPrototile C.1.1 T) (hlat : LatticeTile T)
    (hodo : TileOdometer C.1.1 T h)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hext : GlobalOdometerExtends g h)
    (htile : ExactTileTiling (RegularTileFamily T (TilingLattice C)))
    (hperiodic : ∀ v, v ∈ TilingLattice C → ∀ x,
      FourNeighborLaplacian g (x + v) = FourNeighborLaplacian g x)
    (hweb : ∀ x, (∃ v, v ∈ TilingLattice C ∧
      x ∈ BoundaryFootprintVertices (TileTranslation T v)) →
      FourNeighborLaplacian g x = 1) :
    ∀ X : Set GaussianInt, X.Infinite → FourNeighborConnected X →
      (∀ x, FourNeighborLaplacian
        (fun y => g y + Set.indicator X (fun _ => (1 : ℤ)) y) x ≤ 1) →
      X = Set.univ := by
-- BODY
  classical
  intro X hXin hXconn hle
  have web := PeriodicBoundaryWebConnected C T hT hlat htile
  dsimp at web
  obtain ⟨hWconn, hWcontain⟩ := web
  have finiteFoot := FootprintVertices.finite
  apply Set.eq_univ_of_forall
  intro x
  by_contra hxX
  let reachable (a b : GaussianInt) : Prop := ∃ p : List GaussianInt,
    p.head? = some a ∧ p.getLast? = some b ∧
      (∀ z ∈ p, z ∉ X) ∧ p.IsChain FourNeighborAdjacent
  let Y : Set GaussianInt := {y | reachable x y}
  have xY := PeriodicIndicatorGeometry.xY X x hxX
  have Yout := PeriodicIndicatorGeometry.Yout X x
  have Yconn := PeriodicIndicatorGeometry.Yconn X x xY
  have Ydis := PeriodicIndicatorGeometry.Ydis C T X (PeriodicIndicatorGeometry.hWsub C T X hWconn
      (PeriodicIndicatorGeometry.hmeet C T X hXin hXconn hWcontain finiteFoot)
      (PeriodicIndicatorGeometry.noCross C T g hweb X hle)) x Yout
  obtain ⟨v, hv, hYsub⟩ := hWcontain Y Yconn Ydis
  have hYfin : Y.Finite := (finiteFoot _).subset (fun y hy => (hYsub hy).1)
  let D := h.domain.filter fun p =>
    @decide (p ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
  have ho0 := BandTileAcyclicIndegree C T h g hT hodo hdom hext
  dsimp at ho0
  obtain ⟨o⟩ := ho0
  let Z : Finset GaussianInt := hYfin.toFinset.image (fun y => y - v)
  have hobs := FiniteAcyclicOrientationObstruction D g o Z (PeriodicIndicatorGeometry.Znonempty X
      x xY v hYfin) (PeriodicIndicatorGeometry.Zsub C T h hdom X x v hv hYsub hYfin)
  rcases hobs with ⟨p, hpZ, hpobs⟩
  rcases Finset.mem_image.mp (show p ∈ hYfin.toFinset.image (fun y => y - v) from hpZ) with
    ⟨y, hy, hpy⟩
  have hyY : y ∈ Y := hYfin.mem_toFinset.mp hy
  have htrans := PeriodicIndicatorGeometry.htrans v p y hpy
  have hlapg := hperiodic v hv p
  have hcompare : FourNeighborLaplacian
      (fun z => g z + 1 - if z ∈ Z then 1 else 0) p =
      FourNeighborLaplacian
        (fun z => g z + Set.indicator X (fun _ => (1 : ℤ)) z) (p + v) :=
            PeriodicIndicatorGeometry.hcompare g X x v hYfin p (PeriodicIndicatorGeometry.hlapInd
            X x Yout v hYfin p hpZ y hyY htrans (PeriodicIndicatorGeometry.neighborMem X x Yout v
            hYfin p (PeriodicIndicatorGeometry.memZ X x v hYfin)
            (PeriodicIndicatorGeometry.stepReach X x v p y hyY htrans))) hlapg
  have hle' := hle (p + v)
  rw [← hcompare] at hle'
  have hconst : FourNeighborLaplacian
      (fun z => g z + 1 - if z ∈ Z then 1 else 0) p =
      FourNeighborLaplacian (fun z => g z - if z ∈ Z then 1 else 0) p :=
          PeriodicIndicatorGeometry.hconst g X x v hYfin p
  rw [hconst] at hle'
  linarith

end ApollonianSuperharmonic

end
