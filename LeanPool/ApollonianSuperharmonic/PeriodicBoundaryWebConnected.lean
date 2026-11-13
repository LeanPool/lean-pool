/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandPrototileSingleton
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.RegularTileFamily

-- [TABLET NODE: PeriodicBoundaryWebConnected]

/-!
# PeriodicBoundaryWebConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundaryWebGeometry

private theorem gridWalk :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∃ p : List GaussianInt, p.head? = some x ∧
            p.getLast? = some y ∧ List.IsChain FourNeighborAdjacent p ) := by
  classical
  intro x y
  let dist (a b : GaussianInt) : Nat :=
    (b.re - a.re).natAbs + (b.im - a.im).natAbs
  have aux : ∀ n (a b : GaussianInt), dist a b = n →
      ∃ p : List GaussianInt,
        p.head? = some a ∧ p.getLast? = some b ∧
        List.IsChain FourNeighborAdjacent p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b hab
        by_cases hre : a.re < b.re
        · let c := a + 1
          have hdist : dist c b < n := by
            dsimp [dist] at hab ⊢
            have h1 : 0 ≤ b.re - a.re := by omega
            have h2 : 0 ≤ b.re - a.re - 1 := by omega
            have hc : b.re - c.re = b.re - a.re - 1 := by simp [c]; omega
            have hcast : ((dist c b : Nat) : Int) < n := by
              dsimp [dist]
              have hIm : b.im - c.im = b.im - a.im := by simp [c]
              rw [hc, Int.natAbs_of_nonneg h2, hIm]
              have habcast : ((dist a b : Nat) : Int) = n := by exact_mod_cast hab
              dsimp [dist] at habcast
              rw [Int.natAbs_of_nonneg h1] at habcast
              rw [← habcast]
              omega
            exact_mod_cast hcast
          obtain ⟨p, hp, hlast, hchain⟩ := ih (dist c b) hdist c b rfl
          refine ⟨a :: p, ?_, ?_, ?_⟩
          · simp
          · cases p with
            | nil => simp at hp
            | cons q qs =>
                cases qs with
                | nil => simpa using hlast
                | cons r rs => simpa using hlast
          · apply List.isChain_cons.2
            refine ⟨?_, hchain⟩
            rw [hp]
            simp [FourNeighborAdjacent, c]
        · by_cases hge : a.re > b.re
          · let c := a - 1
            have hdist : dist c b < n := by
              dsimp [dist] at hab ⊢
              have h1 : 0 ≤ a.re - b.re := by omega
              have h2 : 0 ≤ a.re - b.re - 1 := by omega
              have hc : (b.re - c.re).natAbs = (a.re - b.re - 1).natAbs := by
                simp [c]; omega
              have hcast : ((dist c b : Nat) : Int) < n := by
                dsimp [dist]
                have hIm : b.im - c.im = b.im - a.im := by simp [c]
                rw [hc, Int.natAbs_of_nonneg h2, hIm]
                have habcast : ((dist a b : Nat) : Int) = n := by exact_mod_cast hab
                dsimp [dist] at habcast
                rw [show b.re - a.re = -(a.re - b.re) by omega,
                  Int.natAbs_neg, Int.natAbs_of_nonneg h1] at habcast
                rw [← habcast]
                omega
              exact_mod_cast hcast
            obtain ⟨p, hp, hlast, hchain⟩ := ih (dist c b) hdist c b rfl
            refine ⟨a :: p, ?_, ?_, ?_⟩
            · simp
            · cases p with
              | nil => simp at hp
              | cons q qs =>
                  cases qs with
                  | nil => simpa using hlast
                  | cons r rs => simpa using hlast
            · apply List.isChain_cons.2
              refine ⟨?_, hchain⟩
              rw [hp]
              simp [FourNeighborAdjacent, c]
          · by_cases him : a.im < b.im
            · let c := a + ⟨0, 1⟩
              have hdist : dist c b < n := by
                dsimp [dist] at hab ⊢
                have h1 : 0 ≤ b.im - a.im := by omega
                have h2 : 0 ≤ b.im - a.im - 1 := by omega
                have hc : b.im - c.im = b.im - a.im - 1 := by simp [c]; omega
                have hcast : ((dist c b : Nat) : Int) < n := by
                  dsimp [dist]
                  have hRe : b.re - c.re = b.re - a.re := by simp [c]
                  rw [hRe, hc, Int.natAbs_of_nonneg h2]
                  have habcast : ((dist a b : Nat) : Int) = n := by exact_mod_cast hab
                  dsimp [dist] at habcast
                  rw [Int.natAbs_of_nonneg (show 0 ≤ b.re - a.re by omega)] at habcast
                  rw [← habcast]
                  omega
                exact_mod_cast hcast
              obtain ⟨p, hp, hlast, hchain⟩ := ih (dist c b) hdist c b rfl
              refine ⟨a :: p, ?_, ?_, ?_⟩
              · simp
              · cases p with
                | nil => simp at hp
                | cons q qs =>
                    cases qs with
                    | nil => simpa using hlast
                    | cons r rs => simpa using hlast
              · apply List.isChain_cons.2
                refine ⟨?_, hchain⟩
                rw [hp]
                simp [FourNeighborAdjacent, c]
            · by_cases hmi : a.im > b.im
              · let c := a - ⟨0, 1⟩
                have hdist : dist c b < n := by
                  dsimp [dist] at hab ⊢
                  have h1 : 0 ≤ a.im - b.im := by omega
                  have h2 : 0 ≤ a.im - b.im - 1 := by omega
                  have hc : (b.im - c.im).natAbs = (a.im - b.im - 1).natAbs := by
                    simp [c]; omega
                  have hcast : ((dist c b : Nat) : Int) < n := by
                    dsimp [dist]
                    have hRe : b.re - c.re = b.re - a.re := by simp [c]
                    rw [hRe, hc, Int.natAbs_of_nonneg h2]
                    have habcast : ((dist a b : Nat) : Int) = n := by exact_mod_cast hab
                    dsimp [dist] at habcast
                    rw [show b.im - a.im = -(a.im - b.im) by omega,
                      Int.natAbs_neg, Int.natAbs_of_nonneg h1] at habcast
                    rw [← habcast]
                    omega
                  exact_mod_cast hcast
                obtain ⟨p, hp, hlast, hchain⟩ := ih (dist c b) hdist c b rfl
                refine ⟨a :: p, ?_, ?_, ?_⟩
                · simp
                · cases p with
                  | nil => simp at hp
                  | cons q qs =>
                      cases qs with
                      | nil => simpa using hlast
                      | cons r rs => simpa using hlast
                · apply List.isChain_cons.2
                  refine ⟨?_, hchain⟩
                  rw [hp]
                  simp [FourNeighborAdjacent, c]
              · have heq : a = b := by
                  simpa [Zsqrtd.ext_iff] using
                    And.intro (show a.re = b.re by omega)
                      (show a.im = b.im by omega)
                subst b
                exact ⟨[a], by simp, by simp, List.isChain_singleton _⟩
  exact aux (dist x y) x y rfl

private theorem hW :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (a : GaussianInt), (T.cells = {a}) →
            ((TilingLattice C = ⊤) → ((({x | ∃ v, v ∈ TilingLattice C ∧ x ∈
            BoundaryFootprintVertices (TileTranslation T v)} : Set GaussianInt)) = Set.univ)) )
            := by
  classical
  intro C T a ha hlatC
  ext x
  constructor
  · intro _
    simp
  · intro _
    refine ⟨x - a, ?_, ?_⟩
    · rw [hlatC]
      simp
    · rw [((TileTranslationFormulas T (x - a)).2.2.2.2.2.2.2.1)]
      have hboundary : a ∈ BoundaryFootprintVertices T := by
        rw [BoundaryFootprintVertices, ite_eq_left]
        · refine ⟨{a, a + 1}, ?_, by simp⟩
          refine ⟨a, Or.inl ⟨rfl, ?_⟩⟩
          rw [ha]
          simp [Zsqrtd.ext_iff]
        · rw [ha]
          simp
      exact ⟨a, hboundary, by simp [GaussianTranslation, sub_eq_add_neg,
        ]⟩

private theorem hproper :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (SemiProperQuadruple q) →
            ((q (0 : Fin (4 : ℕ)) = C.1.1) → ((∀ (j : Fin (3 : ℕ)), (q j.succ).1 < C.1.1.1) →
            (ProperBandQuadruple q))) ) := by
  classical
  intro C q hsemi hqC hlt
  refine ⟨hsemi, ?_⟩
  intro j
  simpa [hqC] using hlt j

private theorem indexWalk :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (a : TilingLattice
            C), ∀ (b : TilingLattice C), ∃ p : List (TilingLattice C), p.head? = some a ∧
            p.getLast? = some b ∧ List.IsChain P.plane.adjacent p ) := by
  classical
  intro C P a b
  obtain ⟨p, hhead, hlast, _, hstep⟩ :=
    P.plane.three_connected ∅ (by simp) a (by simp) b (by simp)
  exact ⟨p, hhead, hlast,
    List.isChain_iff_forall_rel_of_append_cons_cons.mpr hstep⟩

private theorem listPrefix :
    (by
      classical
      exact
        ∀ (R : GaussianInt → GaussianInt → Prop), ∀ (p : List GaussianInt), ∀ (x : GaussianInt),
            (x ∈ p) → ((List.IsChain R p) → (∃ q : List GaussianInt, q.head? = p.head? ∧
            q.getLast? = some x ∧ (∀ z ∈ q, z ∈ p) ∧ List.IsChain R q)) ) := by
  classical
  intro R p x hx hc
  induction p with
  | nil => simp at hx
  | cons a p ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨[x], by simp, by simp,
          by intro z hz; simp at hz; subst z; simp,
          List.isChain_singleton _⟩
      · obtain ⟨q, hqhead, hqlast, hqmem, hqchain⟩ := ih hx hc.tail
        cases q with
        | nil =>
            cases p with
            | nil => simp at hx
            | cons b p => simp at hqhead
        | cons b q =>
            refine ⟨a :: b :: q, by simp, ?_, ?_, ?_⟩
            · simpa using hqlast
            · intro z hz
              simp only [List.mem_cons] at hz
              rcases hz with hza | hz
              · subst z
                exact List.mem_cons_self
              · rcases hz with hzb | hz
                · subst z
                  have hb : b ∈ p := by
                    cases p with
                    | nil => simp at hqhead
                    | cons c p =>
                        have hcb : c = b := by simpa using hqhead.symm
                        subst c
                        simp
                  exact List.mem_cons_of_mem a hb
                · exact List.mem_cons_of_mem a
                    (hqmem z (List.mem_cons_of_mem b hz))
            · apply List.isChain_cons.mpr
              refine ⟨?_, hqchain⟩
              intro z hz
              have hz' : z ∈ p.head? := by rw [← hqhead]; exact hz
              exact (List.isChain_cons.mp hc).1 z hz'

private theorem listLoopRoute :
    (by
      classical
      exact
        (∀ (R : GaussianInt → GaussianInt → Prop), ∀ (p : List GaussianInt), ∀ (x : GaussianInt),
            (x ∈ p) → ((List.IsChain R p) → (∃ q : List GaussianInt, q.head? = p.head? ∧
            q.getLast? = some x ∧ (∀ z ∈ q, z ∈ p) ∧ List.IsChain R q))) → (∀ (R : GaussianInt →
            GaussianInt → Prop), (∀ a, ∀ b, R a b → R b a) → (∀ (p : List GaussianInt), (p ≠ [])
            → ((List.IsChain R p) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ p) → ((y ∈ p)
            → (∃ q : List GaussianInt, q.head? = some x ∧ q.getLast? = some y ∧ (∀ z ∈ q, z ∈ p)
            ∧ List.IsChain R q)))))) ) := by
  classical
  intro listPrefix R hsymm p hpne hc x y hx hy
  obtain ⟨px, hpxhead, hpxlast, hpxmem, hpxchain⟩ :=
    listPrefix R p x hx hc
  obtain ⟨py, hpyhead, hpyLast, hpyMem, hpyChain⟩ :=
    listPrefix R p y hy hc
  let q := px.reverse ++ py.tail
  have phead : p.head? ≠ none := by
    cases p with
    | nil => exact (hpne rfl).elim
    | cons a p => simp
  have hrev : List.IsChain R px.reverse := by
    apply List.isChain_reverse.mpr
    exact (List.IsChain.iff (by
      intro a b
      exact ⟨hsymm a b, hsymm b a⟩)).mp hpxchain
  have hqchain : List.IsChain R q := by
    change List.IsChain R (px.reverse ++ py.tail)
    rw [List.isChain_append]
    refine ⟨hrev, hpyChain.tail, ?_⟩
    intro a ha b hb
    cases py with
    | nil => exact False.elim (phead hpyhead.symm)
    | cons r rs =>
        cases rs with
        | nil => simp at hb
        | cons s ss =>
            have hroot : p.head? = some r := by simpa using hpyhead.symm
            have ha' : r = a := by
              simpa [List.getLast?_reverse, hpxhead, hroot] using ha
            have hb' : b = s := by simpa using hb.symm
            rw [← ha', hb']
            exact (List.isChain_cons.mp hpyChain).1 s (by simp)
  have hqhead : q.head? = some x := by
    simp [q, List.head?_reverse, hpxlast]
  have hqLast : q.getLast? = some y := by
    cases py with
    | nil => exact False.elim (phead hpyhead.symm)
    | cons r rs =>
        cases rs with
        | nil =>
            have hroot : p.head? = some r := by simpa using hpyhead.symm
            have hry : r = y := by simpa using hpyLast
            simp [q, List.getLast?_reverse, hpxhead, hroot, hry]
        | cons s ss =>
            have hlast : (s :: ss).getLast? = some y := by simpa using hpyLast
            simpa [q] using hlast
  have hqmem : ∀ z ∈ q, z ∈ p := by
    intro z hz
    simp only [q, List.mem_append, List.mem_reverse] at hz
    rcases hz with hz | hz
    · exact hpxmem z hz
    · exact hpyMem z (List.mem_of_mem_tail hz)
  exact ⟨q, hqhead, hqLast, hqmem, hqchain⟩

private theorem adjacentSymm :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a) ) := by
  classical
  intro a b h
  rcases h with h | h | h | h <;> subst b
  all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem cyclePath :
    (by
      classical
      exact
        (∀ (R : GaussianInt → GaussianInt → Prop), (∀ a, ∀ b, R a b → R b a) → (∀ (p : List
            GaussianInt), (p ≠ []) → ((List.IsChain R p) → (∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (x ∈ p) → ((y ∈ p) → (∃ q : List GaussianInt, q.head? = some x ∧
            q.getLast? = some y ∧ (∀ z ∈ q, z ∈ p) ∧ List.IsChain R q)))))) → ((∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → (FourNeighborAdjacent
            b a)) → (∀ (U : ProtoTile), (LatticeTile U) → (∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (x ∈ BoundaryFootprintVertices U) → ((y ∈ BoundaryFootprintVertices U)
            → (∃ p : List GaussianInt, p.head? = some x ∧ p.getLast? = some y ∧ (∀ z ∈ p, z ∈
            BoundaryFootprintVertices U) ∧ List.IsChain FourNeighborAdjacent p))))) ) := by
  classical
  intro listLoopRoute adjacentSymm U hU x y hx hy
  obtain ⟨p, x₀, y₀, _, hlen, _, _, hverts, _, hsteps, _⟩ :=
    LatticeTileGridStructure U hU |>.2.2
  have hpne : p ≠ [] := by
    intro he
    simp [he] at hlen
  have hchain : List.IsChain FourNeighborAdjacent p :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mpr hsteps
  have hxmem : x ∈ p := by
    rw [hverts] at hx
    simpa using hx
  have hymem : y ∈ p := by
    rw [hverts] at hy
    simpa using hy
  obtain ⟨l, hhead, hlast, hmem, hpath⟩ :=
    listLoopRoute FourNeighborAdjacent (fun a b h => adjacentSymm a b h)
      p hpne hchain x y hxmem hymem
  exact ⟨l, hhead, hlast, fun z hz => by
    rw [hverts]
    simpa using hmem z hz, hpath⟩

private theorem pathConcat :
    (by
      classical
      exact
        ∀ (S : Set GaussianInt), ∀ (p : List GaussianInt), ∀ (q : List GaussianInt), ∀ (x :
            GaussianInt), ∀ (z : GaussianInt), ∀ (y : GaussianInt), (p.head? = some x) →
            ((p.getLast? = some z) → ((∀ w ∈ p, w ∈ S) → ((List.IsChain FourNeighborAdjacent p) →
            ((q.head? = some z) → ((q.getLast? = some y) → ((∀ w ∈ q, w ∈ S) → ((List.IsChain
            FourNeighborAdjacent q) → (∃ r : List GaussianInt, r.head? = some x ∧ r.getLast? =
            some y ∧ (∀ w ∈ r, w ∈ S) ∧ List.IsChain FourNeighborAdjacent r)))))))) ) := by
  classical
  intro S p q x z y hphead hplast hpmem hpchain hqhead hqlast hqmem hqchain
  let r := p ++ q.tail
  have hchain : List.IsChain FourNeighborAdjacent r := by
    change List.IsChain FourNeighborAdjacent (p ++ q.tail)
    rw [List.isChain_append]
    refine ⟨hpchain, hqchain.tail, ?_⟩
    intro a ha b hb
    cases q with
    | nil => simp at hqhead
    | cons z' qs =>
        cases qs with
        | nil => simp at hb
        | cons w ws =>
            have hz' : z' = z := Option.some.inj (by simpa using hqhead)
            have ha' : z = a := by simpa [hplast] using ha
            have hb' : b = w := by simpa using hb.symm
            have hza : a = z' := (hz'.trans ha').symm
            rw [hza, hb']
            exact (List.isChain_cons.mp hqchain).1 w (by simp)
  have hhead : r.head? = some x := by
    cases p with
    | nil => simp at hphead
    | cons a p => simpa [r] using hphead
  have hlast : r.getLast? = some y := by
    cases q with
    | nil => simp at hqhead
    | cons z' qs =>
        cases qs with
        | nil =>
            have hzy : z' = y := Option.some.inj (by simpa using hqlast)
            have hzz : z' = z := Option.some.inj (by simpa using hqhead)
            have hzy' : z = y := hzz.symm.trans hzy
            simp only [List.tail_cons, List.append_nil, hplast, Option.some.injEq, r]
            rw [hzy']
        | cons w ws =>
            have hqs : (w :: ws).getLast? = some y := by simpa using hqlast
            simpa [r] using hqs
  have hmem : ∀ w ∈ r, w ∈ S := by
    intro w hw
    simp only [r, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hpmem w hw
    · exact hqmem w (List.mem_of_mem_tail hw)
  exact ⟨r, hhead, hlast, hmem, hchain⟩

private theorem tileBoundarySubsetWeb :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile u =
            TileTranslation T (↑u : GaussianInt)) → (∀ (a : TilingLattice C),
            BoundaryFootprintVertices (P.tile a) ⊆ W) ) := by
  classical
  intro C T W P hPtile a z hz
  exact ⟨a, a.property, by simpa [hPtile] using hz⟩

private theorem boundaryEndpoint :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (∀ (z :
            GaussianInt), (z ∈ e) → (z ∈ BoundaryFootprintVertices U)) ) := by
  classical
  intro U e he z hz
  have hne : U.cells.Nonempty := by
    rcases he with ⟨w, hw | hw⟩
    · rcases hw.2 with ⟨hcell, _⟩ | ⟨_, hcell⟩
      · exact ⟨w, hcell⟩
      · exact ⟨w - ⟨0, 1⟩, hcell⟩
    · rcases hw.2 with ⟨hcell, _⟩ | ⟨_, hcell⟩
      · exact ⟨w, hcell⟩
      · exact ⟨w - 1, hcell⟩
  rw [BoundaryFootprintVertices, ite_eq_left hne]
  exact ⟨e, he, hz⟩

private theorem indexedDisjointEarly :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (a : TilingLattice
            C), ∀ (b : TilingLattice C), (P.plane.adjacent a b) → (Disjoint (P.tile a).cells
            (P.tile b).cells) ) := by
  classical
  intro C P a b hab
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨owner, howner, hunique⟩ := PeriodicTileIndexedMultiplicityOne P x
  have ha : a = owner := hunique a hxa
  have hb : b = owner := hunique b hxb
  have hne : a ≠ b := by
    intro hab'
    rw [← hab'] at hab
    exact P.plane.adjacent_irreflexive a hab
  exact hne (ha.trans hb.symm)

private theorem edgeBoundaryEarly :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (a : TilingLattice
            C), ∀ (b : TilingLattice C), (P.plane.adjacent a b) → (Disjoint (P.tile a).cells
            (P.tile b).cells)) → (∀ (a : TilingLattice C), ∀ (b : TilingLattice C),
            (P.plane.adjacent a b) → (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges (P.tile a)
            ∩ FootprintEdges (P.tile b)) → (e ∈ BoundaryFootprintEdges (P.tile a) ∩
            BoundaryFootprintEdges (P.tile b)))) ) := by
  classical
  intro C P indexedDisjointEarly a b hab e he
  have he' := he
  rw [CellDisjointCommonEdgesBoundary (P.tile a) (P.tile b)
    (indexedDisjointEarly a b hab)] at he'
  exact he'

private theorem commonBoundaryVertex :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (U : ProtoTile), ∀
            (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (∀ (z : GaussianInt), (z ∈
            e) → (z ∈ BoundaryFootprintVertices U))) → ((∀ (a : TilingLattice C), ∀ (b :
            TilingLattice C), (P.plane.adjacent a b) → (∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) → (e ∈ BoundaryFootprintEdges
            (P.tile a) ∩ BoundaryFootprintEdges (P.tile b)))) → (∀ (a : TilingLattice C), ∀ (b :
            TilingLattice C), (P.plane.adjacent a b) → (∃ z, z ∈ BoundaryFootprintVertices
            (P.tile a) ∧ z ∈ BoundaryFootprintVertices (P.tile b)))) ) := by
  classical
  intro C P boundaryEndpoint edgeBoundaryEarly a b hab
  obtain ⟨e, he⟩ := P.adjacent_has_common_edge a b hab
  have heB := edgeBoundaryEarly a b hab e he
  have hne : e.Nonempty := by
    rcases he.1 with ⟨c, hc, hshape⟩
    rcases hshape with h | h | h | h <;> subst e <;> simp
  obtain ⟨z, hz⟩ := hne
  exact ⟨z,
    boundaryEndpoint (P.tile a) e heB.1 z hz,
    boundaryEndpoint (P.tile b) e heB.2 z hz⟩

private theorem indexBoundaryPath :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (U : ProtoTile), (LatticeTile U) → (∀
            (x : GaussianInt), ∀ (y : GaussianInt), (x ∈ BoundaryFootprintVertices U) → ((y ∈
            BoundaryFootprintVertices U) → (∃ p : List GaussianInt, p.head? = some x ∧ p.getLast?
            = some y ∧ (∀ z ∈ p, z ∈ BoundaryFootprintVertices U) ∧ List.IsChain
            FourNeighborAdjacent p)))) → ((∀ (S : Set GaussianInt), ∀ (p : List GaussianInt), ∀
            (q : List GaussianInt), ∀ (x : GaussianInt), ∀ (z : GaussianInt), ∀ (y :
            GaussianInt), (p.head? = some x) → ((p.getLast? = some z) → ((∀ w ∈ p, w ∈ S) →
            ((List.IsChain FourNeighborAdjacent p) → ((q.head? = some z) → ((q.getLast? = some y)
            → ((∀ w ∈ q, w ∈ S) → ((List.IsChain FourNeighborAdjacent q) → (∃ r : List
            GaussianInt, r.head? = some x ∧ r.getLast? = some y ∧ (∀ w ∈ r, w ∈ S) ∧ List.IsChain
            FourNeighborAdjacent r))))))))) → ((∀ (a : TilingLattice C),
            BoundaryFootprintVertices (P.tile a) ⊆ W) → ((∀ (a : TilingLattice C), ∀ (b :
            TilingLattice C), (P.plane.adjacent a b) → (∃ z, z ∈ BoundaryFootprintVertices
            (P.tile a) ∧ z ∈ BoundaryFootprintVertices (P.tile b))) → (∀ (p : List (TilingLattice
            C)), ∀ (a : TilingLattice C), ∀ (b : TilingLattice C), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), p.head? = some a → p.getLast? = some b → List.IsChain P.plane.adjacent
            p → x ∈ BoundaryFootprintVertices (P.tile a) → y ∈ BoundaryFootprintVertices (P.tile
            b) → ∃ l : List GaussianInt, l.head? = some x ∧ l.getLast? = some y ∧ (∀ z ∈ l, z ∈
            W) ∧ List.IsChain FourNeighborAdjacent l)))) ) := by
  classical
  intro C T W P cyclePath pathConcat tileBoundarySubsetWeb commonBoundaryVertex p
  induction p with
  | nil =>
      intro a b x y hp _ _ _ _
      simp at hp
  | cons a' p ih =>
      intro a b x y hp hl hchain hx hy
      have haa : a' = a := Option.some.inj hp
      subst a'
      cases p with
      | nil =>
          have hab : a = b := by simpa using hl
          subst b
          obtain ⟨l, hhead, hlast, hmem, hpath⟩ :=
            cyclePath (P.tile a) (P.tiles_are_disks a) x y hx hy
          exact ⟨l, hhead, hlast,
            fun z hz => tileBoundarySubsetWeb a (hmem z hz), hpath⟩
      | cons c p =>
          have hac : P.plane.adjacent a c :=
            (List.isChain_cons.mp hchain).1 c (by simp)
          have htail : List.IsChain P.plane.adjacent (c :: p) :=
            (List.isChain_cons.mp hchain).2
          have hlast : (c :: p).getLast? = some b := by simpa using hl
          obtain ⟨z, hza, hzc⟩ := commonBoundaryVertex a c hac
          obtain ⟨l₁, h1head, h1last, h1mem, h1chain⟩ :=
            cyclePath (P.tile a) (P.tiles_are_disks a) x z hx hza
          obtain ⟨l₂, h2head, h2last, h2mem, h2chain⟩ :=
            ih c b z y (by simp) hlast htail hzc hy
          obtain ⟨l, hhead, hlast, hmem, hchain⟩ :=
            pathConcat W l₁ l₂ x z y h1head h1last
              (fun w hw => tileBoundarySubsetWeb a (h1mem w hw)) h1chain
              h2head h2last h2mem h2chain
          exact ⟨l, hhead, hlast, hmem, hchain⟩

private theorem noBoundaryIncident :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∉
            BoundaryFootprintVertices U) → (∀ (e : Finset GaussianInt), (e ∈
            BoundaryFootprintEdges U) → ((x ∈ e) → (False)))) ) := by
  classical
  intro U x hne hx e he hxe
  apply hx
  rw [BoundaryFootprintVertices, ite_eq_left hne]
  exact ⟨e, he, hxe⟩

private theorem horizontalStatus :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (({z, z + 1} : Finset GaussianInt) ∉
            BoundaryFootprintEdges U) → ((z ∈ U.cells ↔ z - I ∈ U.cells)) ) := by
  classical
  intro I U z hnot
  constructor
  · intro hz
    by_contra hbelow
    apply hnot
    exact ⟨z, Or.inl ⟨rfl, Or.inl ⟨hz, hbelow⟩⟩⟩
  · intro hbelow
    by_contra hz
    apply hnot
    exact ⟨z, Or.inl ⟨rfl, Or.inr ⟨hz, hbelow⟩⟩⟩

private theorem verticalStatus :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), (({z, z + I} : Finset GaussianInt) ∉
            BoundaryFootprintEdges U) → ((z ∈ U.cells ↔ z - 1 ∈ U.cells)) ) := by
  classical
  intro I U z hnot
  constructor
  · intro hz
    by_contra hleft
    apply hnot
    exact ⟨z, Or.inr ⟨rfl, Or.inl ⟨hz, hleft⟩⟩⟩
  · intro hleft
    by_contra hz
    apply hnot
    exact ⟨z, Or.inr ⟨rfl, Or.inr ⟨hz, hleft⟩⟩⟩

private theorem incidentCellsOwned :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∉
            BoundaryFootprintVertices U) → (∀ (e : Finset GaussianInt), (e ∈
            BoundaryFootprintEdges U) → ((x ∈ e) → (False))))) → (
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (U : ProtoTile), ∀ (z : GaussianInt), (({z, z + 1} : Finset GaussianInt) ∉
            BoundaryFootprintEdges U) → ((z ∈ U.cells ↔ z - I ∈ U.cells))) → ((∀ (U : ProtoTile),
            ∀ (z : GaussianInt), (({z, z + I} : Finset GaussianInt) ∉ BoundaryFootprintEdges U) →
            ((z ∈ U.cells ↔ z - 1 ∈ U.cells))) → (∀ (U : ProtoTile), ∀ (x : GaussianInt), (x ∈
            U.cells) → ((x ∉ BoundaryFootprintVertices U) → (x ∈ U.cells ∧ x - 1 ∈ U.cells ∧ x -
            I ∈ U.cells ∧ x - 1 - I ∈ U.cells))))) ) := by
  classical
  intro noBoundaryIncident I horizontalStatus verticalStatus U x hxcell hxnot
  have hne : U.cells.Nonempty := ⟨x, hxcell⟩
  have htop : ({x, x + 1} : Finset GaussianInt) ∉
      BoundaryFootprintEdges U := by
    intro he
    exact noBoundaryIncident U x hne hxnot {x, x + 1} he (by simp)
  have hleft : ({x, x + I} : Finset GaussianInt) ∉
      BoundaryFootprintEdges U := by
    intro he
    exact noBoundaryIncident U x hne hxnot {x, x + I} he (by simp)
  have hbottom : ({x - 1, x - 1 + 1} : Finset GaussianInt) ∉
      BoundaryFootprintEdges U := by
    intro he
    exact noBoundaryIncident U x hne hxnot {x - 1, x - 1 + 1} he (by
      simp [Zsqrtd.ext_iff])
  have hbelowCell : x - I ∈ U.cells :=
    (horizontalStatus U x htop) |>.mp hxcell
  have hleftCell : x - 1 ∈ U.cells :=
    (verticalStatus U x hleft) |>.mp hxcell
  exact ⟨hxcell, hleftCell, hbelowCell,
    (horizontalStatus U (x - 1) hbottom).mp hleftCell⟩

private theorem tileCellsNonempty :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (a : TilingLattice
            C), (P.tile a).cells.Nonempty ) := by
  classical
  intro C P a
  have hreal : (TileRealization (P.tile a)).Nonempty := by
    rcases P.tiles_are_disks a with ⟨e⟩
    let z : Metric.closedBall (0 : Real × Real) 1 := ⟨0, by simp⟩
    exact ⟨e z, (e z).property⟩
  rcases hreal with ⟨z, hz⟩
  simp only [TileRealization, Set.mem_iUnion] at hz
  rcases hz with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

private theorem ownerExists :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (x : GaussianInt),
            ∃ a : TilingLattice C, x ∈ (P.tile a).cells ) := by
  classical
  intro C P x
  exact (PeriodicTileIndexedMultiplicityOne P x).exists

private theorem ownerUnique :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (ownerExists : ∀ (x
            : GaussianInt), ∃ a : TilingLattice C, x ∈ (P.tile a).cells),
        let owner : GaussianInt → TilingLattice C := fun x =>
          Classical.choose (ownerExists x)
        (∀ (x : GaussianInt), x ∈ (P.tile (owner x)).cells) → (∀ (x : GaussianInt), ∀ (a :
            TilingLattice C), (x ∈ (P.tile a).cells) → (owner x = a)) ) := by
  classical
  intro C P ownerExists owner ownerCell x a ha
  obtain ⟨a₀, ha₀, huniq⟩ := PeriodicTileIndexedMultiplicityOne P x
  have howner : owner x = a₀ := huniq (owner x) (ownerCell x)
  have ha' : a = a₀ := huniq a ha
  exact howner.trans ha'.symm

private theorem ownerBoundaryAbsent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile u =
            TileTranslation T (↑u : GaussianInt)) → (∀ (ownerExists : ∀ (x : GaussianInt), ∃ a :
            TilingLattice C, x ∈ (P.tile a).cells),
        let owner : GaussianInt → TilingLattice C := fun x =>
          Classical.choose (ownerExists x)
        ∀ (x : GaussianInt), (x ∉ W) → (x ∉ BoundaryFootprintVertices (P.tile (owner x)))) ) := by
  classical
  intro C T W P hPtile ownerExists owner x hx h
  apply hx
  refine ⟨owner x, (owner x).property, ?_⟩
  simpa [hPtile] using h

private theorem ownerFootprint :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (ownerExists : ∀ (x
            : GaussianInt), ∃ a : TilingLattice C, x ∈ (P.tile a).cells),
        let owner : GaussianInt → TilingLattice C := fun x =>
          Classical.choose (ownerExists x)
        (∀ (x : GaussianInt), x ∈ (P.tile (owner x)).cells) → (∀ (x : GaussianInt), x ∈
            FootprintVertices (P.tile (owner x))) ) := by
  classical
  intro C P ownerExists owner ownerCell x
  have hx := ownerCell x
  by_cases hcells : (P.tile (owner x)).cells.Nonempty
  · rw [FootprintVertices, ite_eq_left hcells]
    exact ⟨x, hx, Or.inl rfl⟩
  · exact (hcells ⟨x, hx⟩).elim

private theorem ownerEqAdjacent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (U : ProtoTile), ∀ (x : GaussianInt), (x ∈ U.cells) → ((x ∉ BoundaryFootprintVertices
            U) → (x ∈ U.cells ∧ x - 1 ∈ U.cells ∧ x - I ∈ U.cells ∧ x - 1 - I ∈ U.cells))) → (∀
            (ownerExists : ∀ (x : GaussianInt), ∃ a : TilingLattice C, x ∈ (P.tile a).cells),
        let owner : GaussianInt → TilingLattice C := fun x =>
          Classical.choose (ownerExists x)
        (∀ (x : GaussianInt), x ∈ (P.tile (owner x)).cells) → ((∀ (x : GaussianInt), ∀ (a :
            TilingLattice C), (x ∈ (P.tile a).cells) → (owner x = a)) → ((∀ (x : GaussianInt), (x
            ∉ W) → (x ∉ BoundaryFootprintVertices (P.tile (owner x)))) → (∀ (x : GaussianInt), ∀
            (y : GaussianInt), (FourNeighborAdjacent x y) → ((x ∉ W) → ((y ∉ W) → (owner x =
            owner y))))))) ) := by
  classical
  intro C T W P I incidentCellsOwned ownerExists owner ownerCell ownerUnique ownerBoundaryAbsent
      x y hxy hx hy
  have hcx := incidentCellsOwned (P.tile (owner x)) x (ownerCell x)
    (ownerBoundaryAbsent x hx)
  have hcy := incidentCellsOwned (P.tile (owner y)) y (ownerCell y)
    (ownerBoundaryAbsent y hy)
  rcases hxy with h | h | h | h
  · rw [h]
    apply ownerUnique x (owner (x + 1))
    simpa [h, Zsqrtd.ext_iff] using hcy.2.1
  · rw [h]
    exact (ownerUnique (x - 1) (owner x) hcx.2.1).symm.trans
      (ownerUnique (x - 1) (owner (x - 1))
        (by simpa [h, Zsqrtd.ext_iff] using hcy.1))
  · rw [h]
    apply ownerUnique x (owner (x + I))
    simpa [h, I, Zsqrtd.ext_iff] using hcy.2.2.1
  · rw [h]
    exact (ownerUnique (x - I) (owner x) hcx.2.2.1).symm.trans
      (ownerUnique (x - I) (owner (x - I))
        (by simpa [h, I, Zsqrtd.ext_iff] using hcy.1))

private theorem listOwner :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (ownerExists : ∀ (x
            : GaussianInt), ∃ a : TilingLattice C, x ∈ (P.tile a).cells),
        let owner : GaussianInt → TilingLattice C := fun x =>
          Classical.choose (ownerExists x)
        ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (p.head? = some x) →
            ((p.getLast? = some y) → ((List.IsChain (fun a b : GaussianInt => owner a = owner b)
            p) → (owner y = owner x))) ) := by
  classical
  intro C P ownerExists owner p x y hp hl hc
  revert x y hp hl hc
  induction p with
  | nil => intro x y hp hl hc; simp at hp
  | cons a p ih =>
      intro x y hp hl hc
      have hax : a = x := by simpa using hp
      subst x
      cases p with
      | nil =>
          have hay : a = y := Option.some.inj hl
          subst y
          rfl
      | cons b p =>
          have hfirst : owner a = owner b :=
            (List.isChain_cons.mp hc).1 b (by simp)
          have htail : List.IsChain
              (fun a b : GaussianInt => owner a = owner b) (b :: p) :=
            (List.isChain_cons.mp hc).2
          have hlast : (b :: p).getLast? = some y := by simpa using hl
          exact (ih b y (by simp) hlast htail).trans hfirst.symm

private theorem ownerOnPath :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (ownerExists : ∀ (x : GaussianInt), ∃ a
            : TilingLattice C, x ∈ (P.tile a).cells),
        let owner : GaussianInt → TilingLattice C := fun x =>
          Classical.choose (ownerExists x)
        (∀ (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) → ((x ∉ W) → ((y ∉
            W) → (owner x = owner y)))) → ((∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (p.head? = some x) → ((p.getLast? = some y) → ((List.IsChain (fun a b :
            GaussianInt => owner a = owner b) p) → (owner y = owner x)))) → (∀ (X : Set
            GaussianInt), (FourNeighborConnected X) → ((Disjoint X W) → (∀ (x : GaussianInt), ∀
            (y : GaussianInt), (x ∈ X) → ((y ∈ X) → (owner x = owner y)))))) ) := by
  classical
  intro C T W P ownerExists owner ownerEqAdjacent listOwner X hX hdisj x y hx hy
  obtain ⟨p, hp, hl, hmem, hstep⟩ := hX.2 x hx y hy
  have hadj : List.IsChain FourNeighborAdjacent p :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mpr hstep
  have hnot (z : GaussianInt) (hz : z ∈ X) : z ∉ W := by
    intro hzw
    exact (Set.disjoint_left.mp hdisj) hz hzw
  have howner : List.IsChain
      (fun a b : GaussianInt => owner a = owner b) p :=
    hadj.imp_of_mem_imp (fun a b ha hb hab =>
      ownerEqAdjacent a b hab (hnot a (hmem a ha)) (hnot b (hmem b hb)))
  exact (listOwner p x y hp hl howner).symm

private theorem hx₀ :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
        let a₀ : TilingLattice C := ⟨0, (TilingLattice C).zero_mem⟩
        ∀ (p₀ : List GaussianInt), ∀ (x₀ : GaussianInt), (p₀.head? = some x₀) →
            ((BoundaryFootprintVertices (P.tile a₀) = (↑p₀.toFinset : Set GaussianInt)) → (x₀ ∈
            BoundaryFootprintVertices (P.tile a₀))) ) := by
  classical
  intro C P a₀ p₀ x₀ hhead₀ hverts₀
  rw [hverts₀]
  simp only [Finset.mem_coe, List.mem_toFinset]
  rcases List.head?_eq_some_iff.mp hhead₀ with ⟨l, hl⟩
  rw [hl]
  simp

private theorem hx₀W :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile u =
            TileTranslation T (↑u : GaussianInt)) → (
        let a₀ : TilingLattice C := ⟨0, (TilingLattice C).zero_mem⟩
        ∀ (x₀ : GaussianInt), (x₀ ∈ BoundaryFootprintVertices (P.tile a₀)) → (x₀ ∈ W)) ) := by
  classical
  intro C T W P hPtile a₀ x₀ hx₀
  refine ⟨(a₀ : GaussianInt), a₀.property, ?_⟩
  simpa [hPtile] using hx₀

private theorem hxnot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile),
        let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
          x ∈ BoundaryFootprintVertices (TileTranslation T v)}
        ∀ (X : Set GaussianInt), (Disjoint X W) → (∀ (x : GaussianInt), (x ∈ X) → (x ∉ W)) ) := by
  classical
  intro C T W X hdisj x hx hxw
  exact (Set.disjoint_left.mp hdisj) hx hxw

end BoundaryWebGeometry

theorem PeriodicBoundaryWebConnected :
    ∀ (C : BandCircle), ∀ (T : ProtoTile), (BandPrototile C.1.1 T) → ((LatticeTile T) →
        ((ExactTileTiling (RegularTileFamily T (TilingLattice C))) → (
    let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
      x ∈ BoundaryFootprintVertices (TileTranslation T v)}
    FourNeighborConnected W ∧
      ∀ X : Set GaussianInt, FourNeighborConnected X → Disjoint X W →
        ∃ v, v ∈ TilingLattice C ∧
          X ⊆ FootprintVertices (TileTranslation T v) \ W))) := by
  intro C T hT hlat htile
-- BODY
  let W : Set GaussianInt := {x | ∃ v, v ∈ TilingLattice C ∧
    x ∈ BoundaryFootprintVertices (TileTranslation T v)}
  change FourNeighborConnected W ∧
    ∀ X : Set GaussianInt, FourNeighborConnected X → Disjoint X W →
      ∃ v, v ∈ TilingLattice C ∧
        X ⊆ FootprintVertices (TileTranslation T v) \ W
  classical
  have gridWalk (x y : GaussianInt) :
      ∃ p : List GaussianInt,
        p.head? = some x ∧ p.getLast? = some y ∧
        List.IsChain FourNeighborAdjacent p := BoundaryWebGeometry.gridWalk x y
  by_cases hc : C.1.1.1 = 1
  · obtain ⟨a, ha⟩ := CurvatureOneBandPrototileSingleton C T hc hT
    have hlatC : TilingLattice C = ⊤ := by simp [TilingLattice, hc]
    have hW : (({x | ∃ v, v ∈ TilingLattice C ∧
        x ∈ BoundaryFootprintVertices (TileTranslation T v)} : Set GaussianInt)) =
        Set.univ := BoundaryWebGeometry.hW C T a ha hlatC
    have hWeq : W = Set.univ := by simpa [W] using hW
    constructor
    · rw [hWeq]
      refine ⟨⟨0, by simp⟩, ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, hlast, hchain⟩ := gridWalk x y
      exact ⟨p, hp, hlast, fun z hz => by simp,
        List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain⟩
    · intro X hX hdisj
      exfalso
      obtain ⟨x, hx⟩ := hX.1
      rw [hWeq] at hdisj
      exact (Set.disjoint_left.mp hdisj) hx (Set.mem_univ x)
  · obtain ⟨q, hsemi, hqC, hlt, _⟩ := Or.resolve_left (BandGenealogy C) hc
    have hproper := BoundaryWebGeometry.hproper C q hsemi hqC hlt
    have hT' : BandPrototile (q 0) T := by simpa [hqC] using hT
    obtain ⟨P, hPlattice, hPtile, hPadj, hPposition, hPvertices,
      hPedges, hPfaces, hPchart⟩ :=
      BandRegularTranslatePeriodicComplex C q hproper hqC T hT'
    have indexWalk := BoundaryWebGeometry.indexWalk C P
    have indexBoundaryPath := BoundaryWebGeometry.indexBoundaryPath C T P
        (BoundaryWebGeometry.cyclePath (BoundaryWebGeometry.listLoopRoute
        (BoundaryWebGeometry.listPrefix)) (BoundaryWebGeometry.adjacentSymm))
        (BoundaryWebGeometry.pathConcat)
                (BoundaryWebGeometry.tileBoundarySubsetWeb C T P hPtile)
                    (BoundaryWebGeometry.commonBoundaryVertex C P
                    (BoundaryWebGeometry.boundaryEndpoint) (BoundaryWebGeometry.edgeBoundaryEarly
                    C P (BoundaryWebGeometry.indexedDisjointEarly C P)))
    have ownerExists := BoundaryWebGeometry.ownerExists C P
    let owner : GaussianInt → TilingLattice C := fun x =>
      Classical.choose (ownerExists x)
    have ownerCell (x : GaussianInt) : x ∈ (P.tile (owner x)).cells :=
      Classical.choose_spec (ownerExists x)
    have ownerFootprint (x : GaussianInt) :
        x ∈ FootprintVertices (P.tile (owner x)) := BoundaryWebGeometry.ownerFootprint C P
            ownerExists ownerCell x
    have ownerOnPath := BoundaryWebGeometry.ownerOnPath C T P ownerExists
        (BoundaryWebGeometry.ownerEqAdjacent C T P (BoundaryWebGeometry.incidentCellsOwned
        (BoundaryWebGeometry.noBoundaryIncident) (BoundaryWebGeometry.horizontalStatus)
        (BoundaryWebGeometry.verticalStatus)) ownerExists ownerCell
        (BoundaryWebGeometry.ownerUnique C P ownerExists ownerCell)
        (BoundaryWebGeometry.ownerBoundaryAbsent C T P hPtile ownerExists))
        (BoundaryWebGeometry.listOwner C P ownerExists)
    refine ⟨?_, ?_⟩
    · let a₀ : TilingLattice C := ⟨0, (TilingLattice C).zero_mem⟩
      obtain ⟨p₀, x₀, y₀, _, _, hhead₀, _, hverts₀, _, _, _⟩ :=
        LatticeTileGridStructure (P.tile a₀) (P.tiles_are_disks a₀) |>.2.2
      have hx₀ := BoundaryWebGeometry.hx₀ C P p₀ x₀
          hhead₀ hverts₀
      refine ⟨⟨x₀, (BoundaryWebGeometry.hx₀W C T P hPtile x₀ hx₀)⟩, ?_⟩
      intro x hx y hy
      obtain ⟨u, hu, hxu⟩ := hx
      obtain ⟨v, hv, hyv⟩ := hy
      let a : TilingLattice C := ⟨u, hu⟩
      let b : TilingLattice C := ⟨v, hv⟩
      have hxa : x ∈ BoundaryFootprintVertices (P.tile a) := by
        simpa [a, hPtile] using hxu
      have hyb : y ∈ BoundaryFootprintVertices (P.tile b) := by
        simpa [b, hPtile] using hyv
      obtain ⟨p, hhead, hlast, hindex⟩ := indexWalk a b
      obtain ⟨l, hlhead, hllast, hlmem, hlchain⟩ :=
        indexBoundaryPath p a b x y hhead hlast hindex hxa hyb
      exact ⟨l, hlhead, hllast, hlmem,
        List.isChain_iff_forall_rel_of_append_cons_cons.mp hlchain⟩
    · intro X hX hdisj
      obtain ⟨x₀, hx₀⟩ := hX.1
      refine ⟨(owner x₀ : GaussianInt), (owner x₀).property, ?_⟩
      intro x hx
      have howner : owner x = owner x₀ :=
        ownerOnPath X hX hdisj x x₀ hx hx₀
      have hfoot : x ∈ FootprintVertices (TileTranslation T (owner x₀ : GaussianInt)) := by
        simpa [hPtile, howner] using ownerFootprint x
      exact ⟨hfoot, (BoundaryWebGeometry.hxnot C T X hdisj x hx)⟩

end ApollonianSuperharmonic

end
