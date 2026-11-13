/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4456T2EdgeInterior
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.LatticeTileBoundarySimpleGridCycle

-- [TABLET NODE: P4456T2CrosscutIndex]

/-!
# P4456T2CrosscutIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CrosscutIndexProof

private theorem hab :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ((x =
            a + (1 : GaussianInt) ∧ y = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = a + (1 :
            GaussianInt) ∧ x = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ b = a + (1 :
            GaussianInt) ∨ (x = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = a + ⟨(0 : ℤ), (1
            : ℤ)⟩ ∨ y = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = a + ⟨(0 : ℤ), (1 : ℤ)⟩)
            ∧ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩) → (a ≠ b) ) := by
  classical
  intro x y a b hform
  rcases hform with ⟨_, hb⟩ | ⟨_, hb⟩
  · rw [hb]
    intro h
    have hh := congrArg Zsqrtd.re h
    simp at hh
  · rw [hb]
    intro h
    have hh := congrArg Zsqrtd.im h
    simp at hh

private theorem hxmem :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices T) → (∀ (p : List
            GaussianInt), (BoundaryFootprintVertices T = (↑p.toFinset : Set GaussianInt)) → (x ∈
            p)) ) := by
  classical
  intro T x hx p hpVerts
  rw [hpVerts] at hx
  simpa using hx

private theorem hymem :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (y : GaussianInt), (y ∈ BoundaryFootprintVertices T) → (∀ (p : List
            GaussianInt), (BoundaryFootprintVertices T = (↑p.toFinset : Set GaussianInt)) → (y ∈
            p)) ) := by
  classical
  intro T y hy p hpVerts
  rw [hpVerts] at hy
  simpa using hy

private theorem hchordBoundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ((x = a + (1 : GaussianInt) ∧ y = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1
            : ℤ)⟩ ∨ y = a + (1 : GaussianInt) ∧ x = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧
            b = a + (1 : GaussianInt) ∨ (x = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = a +
            ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = a + ⟨(0 :
            ℤ), (1 : ℤ)⟩) ∧ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((a ∈ T.cells ∧ b ∈ T.cells) → (({x, y}
            : Finset GaussianInt) ∉ BoundaryFootprintEdges T)) ) := by
  classical
  intro T x y a b hform hboth he
  have hc := (P4397T1UnitEdgeCells.2 x y a b hform T).2.1
  rcases hc.mp he with ⟨_, hbnot⟩ | ⟨hanot, _⟩
  · exact hbnot hboth.2
  · exact hanot hboth.1

private theorem hqHead :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        ∀ (hk : k < p.length), ((p[k]'hk = x) → (
        let q := p.rotate k
        q.head? = some x)) ) := by
  classical
  intro x p k hk hxidx q
  change (p.rotate k).head? = some x
  rw [List.head?_rotate hk, List.getElem?_eq_getElem hk]
  simp [hxidx]

private theorem hxne :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), FourNeighborAdjacent x y → x ≠ y
    ) := by
  classical
  intro x y hxy h
  rw [h] at hxy
  simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hxy
  omega

private theorem hjpos :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt), ((4 : ℕ) ≤ p.length) → (
        let k := p.idxOf x
        let q := p.rotate k
        (q.head? = some x) → ((q.length = p.length) → ((y ∈ q) → (
        let j := q.idxOf y
        ∀ (hj : j < q.length), ((q[j]'hj = y) → ((x ≠ y) → (0 < j))))))) ) := by
  classical
  intro x y p hpLen k q hqHead hqLen hyq j hj hyidx hxne
  by_contra h
  have hzero : j = 0 := by omega
  have hq0 : q[0] = x := by
    have hqne : q ≠ [] := List.ne_nil_of_mem hyq
    rw [← List.head_eq_getElem hqne]
    simpa [List.head?_eq_some_head hqne] using hqHead
  have hqy : q[0] = y := by simpa [hzero] using hyidx
  exact hxne (hq0.symm.trans hqy)

private theorem hqBoundaryChain :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          ∀ (x : GaussianInt),
            ∀ (p : List GaussianInt),
              ∀ (u : GaussianInt),
                ∀ (v : GaussianInt),
                  p.head? = some u →
                    p.getLast? = some v →
                      (∀ (e : Finset GaussianInt),
                          e ∈ BoundaryFootprintEdges T ↔
                            e = { v, u } ∨
                              ∃ (a : GaussianInt) (b : GaussianInt) (l₁ :
                                List GaussianInt) (l₂ : List GaussianInt),
                                p = l₁ ++ a :: b :: l₂ ∧ e = { a, b }) →
                        let k := p.idxOf x
                        k < p.length →
                          let q := p.rotate k
                          q.length = p.length →
                            List.IsChain
                              (fun s t =>
                                ({ s, t } : Finset GaussianInt) ∈
                                BoundaryFootprintEdges T)
                              q
    ) := by
  classical
  intro T x p u v hpHead hpLast hpEdges k hk q hqLen
  have hchain : List.IsChain (fun s t => ({s, t} : Finset GaussianInt) ∈
      BoundaryFootprintEdges T) p := by
    apply (List.isChain_iff_getElem).2
    intro i hi
    have hpair : p = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by
      calc
        p = p.take (i + 1) ++ p.drop (i + 1) := (List.take_append_drop (i + 1) p).symm
        _ = (p.take i ++ [p[i]]) ++ p[i + 1] :: p.drop (i + 2) := by
          have hi0 : i < p.length := by omega
          rw [List.take_succ_eq_append_getElem (i := i) hi0]
          have hdrop : p.drop (i + 1) = p[i + 1] :: p.drop (i + 2) := by
            simp []
          rw [hdrop]
        _ = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by simp []
    rw [hpEdges]
    right
    exact ⟨p[i], p[i + 1], p.take i, p.drop (i + 2), hpair, rfl⟩
  have hrot : q = p.drop k ++ p.take k := List.rotate_eq_drop_append_take hk.le
  rw [hrot]
  apply (List.isChain_append).2
  refine ⟨hchain.drop k, hchain.take k, ?_⟩
  intro s hs t ht
  have hsLast : (p.drop k).getLast? = some v := by
    rw [List.getLast?_drop]
    simp [hpLast, Nat.not_le.mpr hk]
  by_cases hkzero : k = 0
  · simp [hkzero] at ht
  have hkpos : 0 < k := by omega
  have htHead : (p.take k).head? = some u := by
    rw [List.head?_take]
    simp [hpHead, hkpos.ne']
  have hs' : s = v := by
    simp [hsLast] at hs
    exact hs.symm
  have ht' : t = u := by
    simp [htHead] at ht
    exact ht.symm
  subst s t
  simpa [Finset.pair_comm] using (hpEdges {v, u}).2 (Or.inl rfl)

private theorem hrLast :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        ∀ (hj : j < q.length), ((q[j]'hj = y) → ((0 < j) → (
        let r := q.take (j + 1)
        r.getLast? = some y))) ) := by
  classical
  intro x y p k q j hj hyidx hjpos r
  change (q.take (j + 1)).getLast? = some y
  rw [List.getLast?_take]
  have hqj : q[j]? = some y := by
    rw [List.getElem?_eq_getElem hj]
    exact congrArg some hyidx
  rw [ite_eq_right (show j + 1 ≠ 0 by omega)]
  have hj' : j + 1 - 1 = j := by omega
  rw [hj']
  rw [List.getElem?_eq_getElem hj, hyidx]
  simp

private theorem hrLen :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt),
            ((4 : ℕ) ≤ p.length) → ((({x, y} : Finset GaussianInt) ∉ BoundaryFootprintEdges T) → (
        let k := p.idxOf x
        let q := p.rotate k
        (q.head? = some x) → ((q.length = p.length) → ((y ∈ q) → (
        let j := q.idxOf y
        ∀ (hj : j < q.length), ((q[j]'hj = y) → ((0 < j) → ((List.IsChain (fun s t => ({s, t} :
            Finset
            GaussianInt) ∈ BoundaryFootprintEdges T) q) → (
        let r := q.take (j + 1)
        3 ≤ r.length))))))))) ) := by
  classical
  intro T x y p hpLen hchordBoundary k q hqHead hqLen hyq j hj hyidx hjpos hqBoundaryChain r
  by_contra hsmall
  have hjle : j ≤ 1 := by
    dsimp [r] at hsmall
    simp only [List.length_take] at hsmall
    omega
  have hjnot0 : j ≠ 0 := by omega
  have hj1 : j = 1 := by omega
  have hqxy : ({x, y} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    have hqchain := (List.isChain_iff_getElem.mp hqBoundaryChain) 0 (by
      rw [hqLen]
      omega)
    have hq0 : q[0] = x := by
      have hqne : q ≠ [] := List.ne_nil_of_mem hyq
      rw [← List.head_eq_getElem hqne]
      simpa [List.head?_eq_some_head hqne] using hqHead
    have hq1 : q[1] = y := by simpa [hj1] using hyidx
    simpa [hq0, hq1] using hqchain
  exact hchordBoundary hqxy

private theorem boundaryAdj :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (s : GaussianInt), ∀ (t : GaussianInt), {s, t} ∈
            BoundaryFootprintEdges T → FourNeighborAdjacent s t ) := by
  classical
  intro T s t hst
  simp only [BoundaryFootprintEdges, Set.mem_ofPred_eq] at hst
  rcases hst with ⟨z, ⟨heq, _⟩ | ⟨heq, _⟩⟩
  · have hne : s ≠ t := by
      intro h
      subst t
      have hc := congrArg Finset.card heq
      simp [] at hc
    have hs : s ∈ ({z, z + 1} : Finset GaussianInt) := by
      have : s ∈ ({s, t} : Finset GaussianInt) := by simp
      rw [heq] at this
      exact this
    have ht : t ∈ ({z, z + 1} : Finset GaussianInt) := by
      have : t ∈ ({s, t} : Finset GaussianInt) := by simp
      rw [heq] at this
      exact this
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (hne (hs.trans ht.symm)).elim
    · subst s t
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    · subst s t
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    · exact (hne (hs.trans ht.symm)).elim
  · have hne : s ≠ t := by
      intro h
      subst t
      have hc := congrArg Finset.card heq
      simp [Zsqrtd.ext_iff] at hc
    have hs : s ∈ ({z, z + ⟨0, 1⟩} : Finset GaussianInt) := by
      have : s ∈ ({s, t} : Finset GaussianInt) := by simp
      rw [heq] at this
      exact this
    have ht : t ∈ ({z, z + ⟨0, 1⟩} : Finset GaussianInt) := by
      have : t ∈ ({s, t} : Finset GaussianInt) := by simp
      rw [heq] at this
      exact this
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (hne (hs.trans ht.symm)).elim
    · subst s t
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    · subst s t
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    · exact (hne (hs.trans ht.symm)).elim

private theorem hclose :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), (FourNeighborAdjacent x y) →
            (FourNeighborAdjacent y x) ) := by
  classical
  intro x y hxy
  change y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ at hxy
  rcases hxy with h | h | h | h
  · right; left; rw [h]; ext <;> simp []
  · left; rw [h]; ext <;> simp []
  · right; right; right; rw [h]; ext <;> simp []
  · right; right; left; rw [h]; ext <;> simp []

private theorem pathAdj :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        let r := q.take (j + 1)
        (3 ≤ r.length) → ((List.IsChain (fun s t => ({s, t} : Finset GaussianInt) ∈
            BoundaryFootprintEdges T) r) → ((∀ (s : GaussianInt), ∀ (t : GaussianInt), (({s, t} :
            Finset GaussianInt) ∈ BoundaryFootprintEdges T) → (FourNeighborAdjacent s t)) → (∀ s,
            ∀ t, (s, t) ∈ r.zip r.tail → FourNeighborAdjacent s t))) ) := by
  classical
  intro T x y p k q j r hrLen hrBoundaryChain boundaryAdj s t hst
  rw [List.mem_iff_getElem] at hst
  rcases hst with ⟨i, hi, hst⟩
  have hi' : i + 1 < r.length := by
    simp only [List.length_zip, List.length_tail] at hi
    omega
  rw [List.getElem_zip, List.getElem_tail] at hst
  injection hst with hs ht
  subst s t
  exact boundaryAdj _ _ ((List.isChain_iff_getElem.mp hrBoundaryChain) i hi')

private theorem hoccAt342 :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        let r := q.take (j + 1)
        let edges := r.zip r.tail ++ [(y, x)]
        (x = a + (1 : GaussianInt) ∧ y = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = a + (1
            : GaussianInt) ∧ x = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((a + 1, a + 1 +
            ⟨0, 1⟩) ∈ edges ∨ (a + 1 + ⟨0, 1⟩, a + 1) ∈ edges) ) := by
  classical
  intro x y a p k q j r edges hvert
  rcases hvert with ⟨hx', hy'⟩ | ⟨hy', hx'⟩
  · exact Or.inr (by simp [edges, hx', hy'])
  · exact Or.inl (by simp [edges, hx', hy'])

private theorem hoccAt353 :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        let r := q.take (j + 1)
        let edges := r.zip r.tail ++ [(y, x)]
        (x = a + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = a + (1
            : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = a + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((a + 1 + ⟨0, 1⟩,
            a + ⟨0, 1⟩) ∈ edges ∨ (a + ⟨0, 1⟩, a + 1 + ⟨0, 1⟩) ∈ edges) ) := by
  classical
  intro x y a p k q j r edges hhoriz
  rcases hhoriz with ⟨hx', hy'⟩ | ⟨hy', hx'⟩
  · exact Or.inr (by simp [edges, hx', hy'])
  · exact Or.inl (by simp [edges, hx', hy'])

private theorem hcdAdj :
    (by
      classical
      exact
        ∀ (c : LatticeCell),
          ∀ (d : LatticeCell),
            c ≠ d →
              ∀ (f : Finset GaussianInt),
                f ∈ FootprintEdges (⟨{ c }, c⟩ : ProtoTile) →
                  f ∈ FootprintEdges (⟨{ d }, d⟩ : ProtoTile) → FourNeighborAdjacent c d
    ) := by
  classical
  intro c d hcd f hfc hfd
  have pairMatch (u v w z : GaussianInt)
      (heq : ({u, v} : Finset GaussianInt) = {w, z}) (huv : u ≠ v) :
      (u = w ∧ v = z) ∨ (u = z ∧ v = w) := by
    have huwz : u = w ∨ u = z := by
      have hm : u ∈ ({w, z} : Finset GaussianInt) := by rw [← heq]; simp
      simpa using hm
    have hvwz : v = w ∨ v = z := by
      have hm : v ∈ ({w, z} : Finset GaussianInt) := by rw [← heq]; simp
      simpa using hm
    rcases huwz with huw | huz
    · rcases hvwz with hvw | hvz
      · exact False.elim (huv (huw.trans hvw.symm))
      · exact Or.inl ⟨huw, hvz⟩
    · rcases hvwz with hvw | hvz
      · exact Or.inr ⟨huz, hvw⟩
      · exact False.elim (huv (huz.trans hvz.symm))
  change (∃ z ∈ ({c} : Finset GaussianInt),
    f = {z, z + 1} ∨ f = {z, z + ⟨0, 1⟩} ∨
      f = {z + 1, z + 1 + ⟨0, 1⟩} ∨
        f = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩}) at hfc
  change (∃ z ∈ ({d} : Finset GaussianInt),
    f = {z, z + 1} ∨ f = {z, z + ⟨0, 1⟩} ∨
      f = {z + 1, z + 1 + ⟨0, 1⟩} ∨
        f = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩}) at hfd
  simp only [Finset.mem_singleton] at hfc hfd
  rcases hfc with ⟨z, hz, hfc⟩
  have hzc : z = c := by simpa using hz
  rw [hzc] at hfc
  rcases hfd with ⟨w, hw, hfd⟩
  have hwd : w = d := by simpa using hw
  rw [hwd] at hfd
  let edgePair (q : GaussianInt) (i : Fin 4) : GaussianInt × GaussianInt :=
    if i.val = 0 then (q, q + 1) else if i.val = 1 then (q, q + ⟨0, 1⟩)
    else if i.val = 2 then (q + 1, q + 1 + ⟨0, 1⟩)
    else (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩)
  have hcEdge : ∃ i : Fin 4,
      f = {(edgePair c i).1, (edgePair c i).2} := by
    rcases hfc with hfc | hfc | hfc | hfc
    · exact ⟨⟨0, by omega⟩, by simpa [edgePair] using hfc⟩
    · exact ⟨⟨1, by omega⟩, by simpa [edgePair] using hfc⟩
    · exact ⟨⟨2, by omega⟩, by simpa [edgePair] using hfc⟩
    · exact ⟨⟨3, by omega⟩, by simpa [edgePair] using hfc⟩
  have hdEdge : ∃ i : Fin 4,
      f = {(edgePair d i).1, (edgePair d i).2} := by
    rcases hfd with hfd | hfd | hfd | hfd
    · exact ⟨⟨0, by omega⟩, by simpa [edgePair] using hfd⟩
    · exact ⟨⟨1, by omega⟩, by simpa [edgePair] using hfd⟩
    · exact ⟨⟨2, by omega⟩, by simpa [edgePair] using hfd⟩
    · exact ⟨⟨3, by omega⟩, by simpa [edgePair] using hfd⟩
  obtain ⟨i, hi⟩ := hcEdge
  obtain ⟨j, hj⟩ := hdEdge
  have hne : (edgePair c i).1 ≠ (edgePair c i).2 := by
    fin_cases i <;> simp [edgePair, Zsqrtd.ext_iff]
  have hm := pairMatch (edgePair c i).1 (edgePair c i).2
    (edgePair d j).1 (edgePair d j).2 (hi.symm.trans hj) hne
  have hcd' : c.re ≠ d.re ∨ c.im ≠ d.im := by
    by_contra hnot
    push Not at hnot
    apply hcd
    ext <;> omega
  fin_cases i <;> fin_cases j
  all_goals
    simp [edgePair, FourNeighborAdjacent, Zsqrtd.ext_iff] at hm ⊢
    omega

private theorem internalNotBoundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (c : LatticeCell), (c ∈ T.cells) → (∀ (d : LatticeCell), (d ∈
            T.cells) → ((c ≠ d) → (∀ (f : Finset GaussianInt), (f ∈ FootprintEdges (⟨{c}, c⟩ :
                ProtoTile)) → ((f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile)) → (∀ (u :
            GaussianInt), ∀ (v : GaussianInt), f = {u, v} → FourNeighborAdjacent u v → f ∉
            BoundaryFootprintEdges T))))) ) := by
  classical
  intro T c hc d hd hcd f hfcOrig hfdOrig u v heq huv
  obtain ⟨z, w, hgeom⟩ := (P4397T1UnitEdgeCells.1 u v huv)
  have hmemC : ({u, v} : Finset GaussianInt) ∈
      FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
    simpa [heq] using hfcOrig
  have hmemD : ({u, v} : Finset GaussianInt) ∈
      FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
    simpa [heq] using hfdOrig
  have hincC : z = c ∨ w = c := by
    have h := ((P4397T1UnitEdgeCells.2 u v z w hgeom
        (⟨{c}, c⟩ : ProtoTile)).1.mp hmemC)
    simpa [Finset.mem_singleton] using h
  have hincD : z = d ∨ w = d := by
    have h := ((P4397T1UnitEdgeCells.2 u v z w hgeom
        (⟨{d}, d⟩ : ProtoTile)).1.mp hmemD)
    simpa [Finset.mem_singleton] using h
  intro hbound
  have hxor := ((P4397T1UnitEdgeCells.2 u v z w hgeom T).2.1).mp
    (by simpa [heq] using hbound)
  rcases hincC with hzC | hwC <;> rcases hincD with hzD | hwD
  · exact False.elim (hcd (hzC.symm.trans hzD))
  · have hzT : z ∈ T.cells := by simpa [hzC] using hc
    have hwT : w ∈ T.cells := by simpa [hwD] using hd
    rcases hxor with ⟨_, hnw⟩ | ⟨hnz, _⟩
    · exact hnw hwT
    · exact hnz hzT
  · have hwT : w ∈ T.cells := by simpa [hwC] using hc
    have hzT : z ∈ T.cells := by simpa [hzD] using hd
    rcases hxor with ⟨_, hnw⟩ | ⟨hnz, _⟩
    · exact hnw hwT
    · exact hnz hzT
  · exact False.elim (hcd (hwC.symm.trans hwD))

private theorem hnotBoundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (c : LatticeCell), ∀ (f : Finset GaussianInt), (f = {c,
            c + (1 : GaussianInt)} ∨ f = {c, c + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ f =
            {c + (1 : GaussianInt), c + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ f =
            {c + ⟨(0 : ℤ), (1 : ℤ)⟩, c + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩}) → ((∀ (u :
            GaussianInt), ∀ (v : GaussianInt), (f = {u, v}) → ((FourNeighborAdjacent u v) → (f ∉
            BoundaryFootprintEdges T))) → (f ∉ BoundaryFootprintEdges T)) ) := by
  classical
  intro T c f hfc internalNotBoundary
  rcases hfc with hfc | hfc | hfc | hfc
  · exact internalNotBoundary c (c + 1) hfc (by
      change c + 1 = c + 1 ∨ _
      exact Or.inl rfl)
  · exact internalNotBoundary c (c + ⟨0, 1⟩) hfc (by
      change c + ⟨0, 1⟩ = c + 1 ∨ c + ⟨0, 1⟩ = c - 1 ∨
        c + ⟨0, 1⟩ = c + ⟨0, 1⟩ ∨ _
      exact Or.inr (Or.inr (Or.inl rfl)))
  · exact internalNotBoundary (c + 1) (c + 1 + ⟨0, 1⟩) hfc (by
      change c + 1 + ⟨0, 1⟩ = (c + 1) + 1 ∨
        c + 1 + ⟨0, 1⟩ = (c + 1) - 1 ∨
        c + 1 + ⟨0, 1⟩ = (c + 1) + ⟨0, 1⟩ ∨ _
      exact Or.inr (Or.inr (Or.inl (by abel))))
  · exact internalNotBoundary (c + ⟨0, 1⟩) (c + 1 + ⟨0, 1⟩) hfc (by
      change c + 1 + ⟨0, 1⟩ = (c + ⟨0, 1⟩) + 1 ∨ _
      exact Or.inl (by abel))

private theorem internalIncident :
    (by
      classical
      exact
        ∀ (c : LatticeCell), ∀ (d : LatticeCell), (c ≠ d) → (∀ (f : Finset GaussianInt), (f ∈
            FootprintEdges (⟨{c}, c⟩ : ProtoTile)) → ((f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile))
                → (∀ (u : GaussianInt), ∀ (v : GaussianInt), f = {u, v} →
            FourNeighborAdjacent u v → ∃ (z : GaussianInt) (w : GaussianInt), ((u = z + (1 :
            GaussianInt) ∧ v = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ v = z + (1 :
            GaussianInt) ∧ u = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ w = z + (1 :
            GaussianInt) ∨ (u = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ v = z + ⟨(0 : ℤ), (1
            : ℤ)⟩ ∨ v = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ u = z + ⟨(0 : ℤ), (1 : ℤ)⟩)
            ∧ w = z + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ (z = c ∧ w = d ∨ z = d ∧ w = c)))) ) := by
  classical
  intro c d hcd f hfcOrig hfdOrig u v heq huv
  obtain ⟨z, w, hgeom⟩ := (P4397T1UnitEdgeCells.1 u v huv)
  have hmemC : ({u, v} : Finset GaussianInt) ∈
      FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
    simpa [heq] using hfcOrig
  have hmemD : ({u, v} : Finset GaussianInt) ∈
      FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
    simpa [heq] using hfdOrig
  have hincC : z = c ∨ w = c := by
    have h := ((P4397T1UnitEdgeCells.2 u v z w hgeom
        (⟨{c}, c⟩ : ProtoTile)).1.mp hmemC)
    simpa [Finset.mem_singleton] using h
  have hincD : z = d ∨ w = d := by
    have h := ((P4397T1UnitEdgeCells.2 u v z w hgeom
        (⟨{d}, d⟩ : ProtoTile)).1.mp hmemD)
    simpa [Finset.mem_singleton] using h
  rcases hincC with hzC | hwC <;> rcases hincD with hzD | hwD
  · exact False.elim (hcd (hzC.symm.trans hzD))
  · exact ⟨z, w, hgeom, Or.inl ⟨hzC, hwD⟩⟩
  · exact ⟨z, w, hgeom, Or.inr ⟨hzD, hwC⟩⟩
  · exact False.elim (hcd (hwC.symm.trans hwD))

private theorem pathBoundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        let r := q.take (j + 1)
        (3 ≤ r.length) → ((List.IsChain (fun s t => ({s, t} : Finset GaussianInt) ∈
            BoundaryFootprintEdges T) r) → (∀ s, ∀ t, (s, t) ∈ r.zip r.tail → ({s, t} : Finset
            GaussianInt) ∈ BoundaryFootprintEdges T)) ) := by
  classical
  intro T x y p k q j r hrLen hrBoundaryChain s t hst
  rw [List.mem_iff_getElem] at hst
  rcases hst with ⟨i, hi, hst⟩
  have hi' : i + 1 < r.length := by
    simp only [List.length_zip, List.length_tail] at hi
    omega
  rw [List.getElem_zip, List.getElem_tail] at hst
  injection hst with hs ht
  subst s t
  exact (List.isChain_iff_getElem.mp hrBoundaryChain) i hi'

private theorem edgesAbsent :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        let r := q.take (j + 1)
        let edges := r.zip r.tail ++ [(y, x)]
        ∀ (f : Finset GaussianInt), (f ∉ BoundaryFootprintEdges T) → ((∀ s, ∀ t, (s, t) ∈ r.zip
            r.tail → ({s, t} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) → (∀ (u :
            GaussianInt), ∀ (v : GaussianInt), f = {u, v} → f ≠ {x, y} → (u, v) ∉ edges ∧ (v, u)
            ∉ edges)) ) := by
  classical
  intro T x y p k q j r edges f hnotBoundary pathBoundary u v heq hne
  constructor
  · intro hmem
    have hsplit : (u, v) ∈ r.zip r.tail ∨ (u, v) = (y, x) := by
      simpa [edges] using hmem
    rcases hsplit with hArc | hClose
    · apply hnotBoundary
      rw [heq]
      exact pathBoundary u v hArc
    · apply hne
      rw [heq]
      cases hClose
      simp [Finset.pair_comm]
  · intro hmem
    have hsplit : (v, u) ∈ r.zip r.tail ∨ (v, u) = (y, x) := by
      simpa [edges] using hmem
    rcases hsplit with hArc | hClose
    · apply hnotBoundary
      rw [heq]
      simpa [Finset.pair_comm] using pathBoundary v u hArc
    · apply hne
      rw [heq]
      cases hClose
      simp [Finset.pair_comm]

private theorem hunit :
    (by
      classical
      exact
        ∀ (c : LatticeCell), ∀ (f : Finset GaussianInt), (f = {c, c + (1 : GaussianInt)} ∨ f =
            {c, c + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ f = {c + (1 : GaussianInt),
            c + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ f = {c + ⟨(0 : ℤ), (1 : ℤ)⟩,
            c + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩}) → (∃ u v, f = {u, v} ∧
            FourNeighborAdjacent u v) ) := by
  classical
  intro c f hfc
  rcases hfc with h0 | h1 | h2 | h3
  · exact ⟨c, c + 1, h0, Or.inl rfl⟩
  · exact ⟨c, c + ⟨0, 1⟩, h1,
      Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨c + 1, c + 1 + ⟨0, 1⟩, h2, by
      change c + 1 + ⟨0, 1⟩ = (c + 1) + 1 ∨
        c + 1 + ⟨0, 1⟩ = (c + 1) - 1 ∨
        c + 1 + ⟨0, 1⟩ = (c + 1) + ⟨0, 1⟩ ∨ _
      exact Or.inr (Or.inr (Or.inl (by abel)))⟩
  · exact ⟨c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩, h3, by
      change c + 1 + ⟨0, 1⟩ = (c + ⟨0, 1⟩) + 1 ∨ _
      exact Or.inl (by abel)⟩

private theorem hsetAt681 :
    (by
      classical
      exact
        ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (f : Finset GaussianInt), ∀ (z :
            GaussianInt), (f = {u, v}) → ((u = z + (1 : GaussianInt) ∧ v = z + (1 : GaussianInt)
            + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ v = z + (1 : GaussianInt) ∧ u = z + (1 : GaussianInt) + ⟨(0 :
            ℤ), (1 : ℤ)⟩) → (f = {z + 1, z + 1 + ⟨0, 1⟩})) ) := by
  classical
  intro u v f z heq hvertical
  rcases hvertical with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · simpa [hu, hv] using heq
  · simpa [hu, hv, Finset.pair_comm] using heq

private theorem hcdEqAt689 :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (p : List GaussianInt),
        let k := p.idxOf x
        let q := p.rotate k
        let j := q.idxOf y
        let r := q.take (j + 1)
        ∀ (c : LatticeCell), ∀ (d : LatticeCell), ∀ (z : GaussianInt), ∀ (w : GaussianInt), (z =
            c ∧ w = d ∨ z = d ∧ w = c) → ((GridRayCrossingIndex w r = GridRayCrossingIndex z r) →
            (GridRayCrossingIndex c r = GridRayCrossingIndex d r)) ) := by
  classical
  intro x y p k q j r c d z w hincident hzero'
  rcases hincident with ⟨hzc, hwd⟩ | ⟨hzd, hwc⟩
  · simpa [hzc, hwd] using hzero'.symm
  · simpa [hzd, hwc] using hzero'

private theorem hsetAt695 :
    (by
      classical
      exact
        ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (f : Finset GaussianInt), ∀ (z :
            GaussianInt), (f = {u, v}) → ((u = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ v = z
            + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ v = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ u = z + ⟨(0 :
            ℤ), (1 : ℤ)⟩) → (f = {z + 1 + ⟨0, 1⟩, z + ⟨0, 1⟩})) ) := by
  classical
  intro u v f z heq hhorizontal
  rcases hhorizontal with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · simpa [hu, hv] using heq
  · simpa [hu, hv, Finset.pair_comm] using heq

end CrosscutIndexProof

theorem P4456T2CrosscutIndex (T : ProtoTile) (hT : LatticeTile T)
    (x y : GaussianInt) (hxy : FourNeighborAdjacent x y)
    (hx : x ∈ BoundaryFootprintVertices T)
    (hy : y ∈ BoundaryFootprintVertices T)
    (he : OpenLatticeEdge x y ⊆ interior (TileRealization T)) :
    ∃ (side : GaussianInt → Int) (a b : GaussianInt),
      a ∈ T.cells ∧ b ∈ T.cells ∧ a ≠ b ∧ side a ≠ side b ∧
      ({x, y} : Finset GaussianInt) ∈ FootprintEdges ⟨{a}, a⟩ ∧
      ({x, y} : Finset GaussianInt) ∈ FootprintEdges ⟨{b}, b⟩ ∧
      ∀ c ∈ T.cells, ∀ d ∈ T.cells, c ≠ d →
        ∀ f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) ∩
          FootprintEdges (⟨{d}, d⟩ : ProtoTile),
          side c ≠ side d → f = {x, y} := by
-- BODY
  classical
  obtain ⟨a, b, hform⟩ := P4397T1UnitEdgeCells.1 x y hxy
  have hab := CrosscutIndexProof.hab x y a b hform
  have ha : ({x, y} : Finset GaussianInt) ∈ FootprintEdges ⟨{a}, a⟩ :=
    (P4397T1UnitEdgeCells.2 x y a b hform ⟨{a}, a⟩).1.mpr
      (Or.inl (Finset.mem_singleton_self a))
  have hb : ({x, y} : Finset GaussianInt) ∈ FootprintEdges ⟨{b}, b⟩ :=
    (P4397T1UnitEdgeCells.2 x y a b hform ⟨{b}, b⟩).1.mpr
      (Or.inr (Finset.mem_singleton_self b))
  have hboth := (P4456T2EdgeInterior T x y a b hxy hab ha hb).mp he
  suffices hs : ∃ side : GaussianInt → Int, side a ≠ side b ∧
      ∀ c ∈ T.cells, ∀ d ∈ T.cells, c ≠ d →
        ∀ f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) ∩
          FootprintEdges (⟨{d}, d⟩ : ProtoTile),
          side c ≠ side d → f = {x, y} by
    obtain ⟨side, hside, hstep⟩ := hs
    exact ⟨side, a, b, hboth.1, hboth.2, hab, hside, ha, hb, hstep⟩
  classical
  obtain ⟨p, u, v, hpNodup, hpLen, hpHead, hpLast, hpVerts, hvu,
      hpChain, hpEdges⟩ := LatticeTileBoundarySimpleGridCycle T hT
  let k := p.idxOf x
  have hk : k < p.length := List.idxOf_lt_length_of_mem (CrosscutIndexProof.hxmem T x hx p hpVerts)
  have hxidx : p[k] = x := by simp [k]
  let q := p.rotate k
  have hqHead : q.head? = some x := CrosscutIndexProof.hqHead x p hk hxidx
  have hqNodup : q.Nodup := (List.nodup_rotate).2 hpNodup
  have hqLen : q.length = p.length := List.length_rotate _ _
  have hyq : y ∈ q := (List.mem_rotate).2 (CrosscutIndexProof.hymem T y hy p hpVerts)
  let j := q.idxOf y
  have hj : j < q.length := List.idxOf_lt_length_of_mem hyq
  have hyidx : q[j] = y := by simp [j]
  have hjpos : 0 < j := CrosscutIndexProof.hjpos x y p hpLen hqHead hqLen hyq hj hyidx
      (CrosscutIndexProof.hxne x y hxy)
  have hqBoundaryChain := CrosscutIndexProof.hqBoundaryChain T x p u v hpHead hpLast hpEdges hk
      hqLen
  let r := q.take (j + 1)
  have hrHead : r.head? = some x := by
    simp [r, List.head?_take, Nat.ne_of_gt hjpos, hqHead]
  have hrNodup : r.Nodup := by
    exact List.Nodup.sublist (List.take_sublist _ _) hqNodup
  have hrLen := CrosscutIndexProof.hrLen T x y p hpLen (CrosscutIndexProof.hchordBoundary T x y a
      b hform hboth) hqHead hqLen hyq hj hyidx
      hjpos hqBoundaryChain
  have hrBoundaryChain : List.IsChain (fun s t => ({s, t} : Finset GaussianInt) ∈
      BoundaryFootprintEdges T) r := hqBoundaryChain.take _
  let side : GaussianInt → Int := fun c => GridRayCrossingIndex c r
  have hcross := GridRayCrossingIndexAdjacentCell r x y hrHead (CrosscutIndexProof.hrLast x y p
      hj hyidx hjpos) hrNodup hrLen
    (CrosscutIndexProof.pathAdj T x y p hrLen hrBoundaryChain (CrosscutIndexProof.boundaryAdj T))
        (CrosscutIndexProof.hclose x y hxy)
  let edges := r.zip r.tail ++ [(y, x)]
  refine ⟨side, ?_, ?_⟩
  · have hc := hcross a
    rcases hform with ⟨hvert, hbform⟩ | ⟨hhoriz, hbform⟩
    · have hocc : (a + 1, a + 1 + ⟨0, 1⟩) ∈ edges ∨
          (a + 1 + ⟨0, 1⟩, a + 1) ∈ edges := CrosscutIndexProof.hoccAt342 x y a p hvert
      have hnat := hc.2.1 (by simpa [edges] using hocc)
      intro heq
      rw [hbform] at heq
      change GridRayCrossingIndex a r = GridRayCrossingIndex (a + 1) r at heq
      rw [← heq] at hnat
      simp at hnat
    · have hocc : (a + 1 + ⟨0, 1⟩, a + ⟨0, 1⟩) ∈ edges ∨
          (a + ⟨0, 1⟩, a + 1 + ⟨0, 1⟩) ∈ edges := CrosscutIndexProof.hoccAt353 x y a p hhoriz
      have hnat := hc.2.2.2 (by simpa [edges] using hocc)
      intro heq
      rw [hbform] at heq
      change GridRayCrossingIndex a r = GridRayCrossingIndex (a + ⟨0, 1⟩) r at heq
      rw [← heq] at hnat
      simp at hnat
  · -- Every occupied shared side other than the chord is absent from the arc.
    intro c hc d hd hcd f hf hdiff
    rcases hf with ⟨hfc, hfd⟩
    have hfcOrig := hfc
    have hfdOrig := hfd
    have hcdAdj := CrosscutIndexProof.hcdAdj c d hcd f hfc hfd
    change (∃ z ∈ ({c} : Finset GaussianInt),
      f = {z, z + 1} ∨ f = {z, z + ⟨0, 1⟩} ∨
        f = {z + 1, z + 1 + ⟨0, 1⟩} ∨
          f = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩}) at hfc
    change (∃ z ∈ ({d} : Finset GaussianInt),
      f = {z, z + 1} ∨ f = {z, z + ⟨0, 1⟩} ∨
        f = {z + 1, z + 1 + ⟨0, 1⟩} ∨
          f = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩}) at hfd
    simp only [Finset.mem_singleton] at hfc hfd
    rcases hfc with ⟨z, hz, hfc⟩
    have hzc : z = c := by simpa using hz
    rw [hzc] at hfc
    rcases hfd with ⟨w, hw, hfd⟩
    have hwd : w = d := by simpa using hw
    rw [hwd] at hfd
    /-
    let edgePair (q : GaussianInt) (i : Fin 4) : GaussianInt × GaussianInt :=
      if i.val = 0 then (q, q + 1) else if i.val = 1 then (q, q + ⟨0, 1⟩)
      else if i.val = 2 then (q + 1, q + 1 + ⟨0, 1⟩)
      else (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩)
    have hcEdge : ∃ i : Fin 4,
        f = {(edgePair c i).1, (edgePair c i).2} := by
      rcases hfc with hfc | hfc | hfc | hfc
      · exact ⟨⟨0, by omega⟩, by simpa [edgePair] using hfc⟩
      · exact ⟨⟨1, by omega⟩, by simpa [edgePair] using hfc⟩
      · exact ⟨⟨2, by omega⟩, by simpa [edgePair] using hfc⟩
      · exact ⟨⟨3, by omega⟩, by simpa [edgePair] using hfc⟩
    have hdEdge : ∃ i : Fin 4,
        f = {(edgePair d i).1, (edgePair d i).2} := by
      rcases hfd with hfd | hfd | hfd | hfd
      · exact ⟨⟨0, by omega⟩, by simpa [edgePair] using hfd⟩
      · exact ⟨⟨1, by omega⟩, by simpa [edgePair] using hfd⟩
      · exact ⟨⟨2, by omega⟩, by simpa [edgePair] using hfd⟩
      · exact ⟨⟨3, by omega⟩, by simpa [edgePair] using hfd⟩
    obtain ⟨i, hi⟩ := hcEdge
    obtain ⟨j, hj⟩ := hdEdge
    have pairMatch (u v w z : GaussianInt)
        (heq : ({u, v} : Finset GaussianInt) = {w, z}) (huv : u ≠ v) :
        (u = w ∧ v = z) ∨ (u = z ∧ v = w) := by
      have huwz : u = w ∨ u = z := by
        have hm : u ∈ ({w, z} : Finset GaussianInt) := by rw [← heq]; simp
        simpa using hm
      have hvwz : v = w ∨ v = z := by
        have hm : v ∈ ({w, z} : Finset GaussianInt) := by rw [← heq]; simp
        simpa using hm
      rcases huwz with huw | huz <;> rcases hvwz with hvw | hvz
      · exact False.elim (huv (huw.trans hvw.symm))
      · exact Or.inl ⟨huw, hvz⟩
      · exact Or.inr ⟨huz, hvw⟩
      · exact False.elim (huv (huz.trans hvz.symm))
    have hne : (edgePair c i).1 ≠ (edgePair c i).2 := by
      fin_cases i <;> simp [edgePair, Zsqrtd.ext_iff]
    have hm := pairMatch (edgePair c i).1 (edgePair c i).2
      (edgePair d j).1 (edgePair d j).2 (hi.symm.trans hj) hne
    have hshared :
        (d = c + 1 ∧ f = {c + 1, c + 1 + ⟨0, 1⟩}) ∨
        (d = c - 1 ∧ f = {c, c + ⟨0, 1⟩}) ∨
        (d = c + ⟨0, 1⟩ ∧ f = {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}) ∨
        (d = c - ⟨0, 1⟩ ∧ f = {c, c + 1}) := by
      rcases hcdAdj with hd | hd | hd | hd
      · left
        constructor
        · exact hd
        · rw [hd] at hm hj
          fin_cases i <;> fin_cases j
          all_goals
            first
            | simpa [edgePair, Finset.pair_comm] using hi
            | (rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                dsimp [edgePair] at h1 h2 <;>
                simp only [Zsqrtd.ext_iff] at h1 h2 <;>
                (trace_state; omega))
      · right; left
        have hc' : c = d + 1 := by rw [hd]; simp
        constructor
        · exact hd
        ·
          fin_cases i <;> fin_cases j
          all_goals
            rw [hc'] at hm hi ⊢
            first
            | simpa [edgePair, Finset.pair_comm] using hi
            | (rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                dsimp [edgePair] at h1 h2 <;>
                simp only [Zsqrtd.ext_iff] at h1 h2 <;>
                ring_nf at h1 h2 <;> omega)
      · right; right; left
        constructor
        · exact hd
        · rw [hd] at hm hj
          fin_cases i <;> fin_cases j
          all_goals
            first
            | simpa [edgePair, Finset.pair_comm] using hi
            | ((rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                  dsimp [edgePair] at h1 h2 <;>
                  simp only [Zsqrtd.ext_iff] at h1 h2 <;>
                  ring_nf at h1 h2 <;> omega))
      · right; right; right
        have hc' : c = d + ⟨0, 1⟩ := by rw [hd]; simp
        constructor
        · exact hd
        ·
          fin_cases i <;> fin_cases j
          all_goals
            rw [hc'] at hm hi ⊢
            first
            | simpa [edgePair, Finset.pair_comm] using hi
            | (rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
              dsimp [edgePair] at h1 h2 <;>
              simp only [Zsqrtd.ext_iff] at h1 h2 <;>
              ring_nf at h1 h2 <;> omega)
    -/
    have edgesAbsent (u v : GaussianInt) (heq : f = {u, v})
        (hne : f ≠ {x, y}) := CrosscutIndexProof.edgesAbsent T x y p f
            (CrosscutIndexProof.hnotBoundary T c f hfc (CrosscutIndexProof.internalNotBoundary T
            c hc d hd hcd f hfcOrig hfdOrig)) (CrosscutIndexProof.pathBoundary T x y p hrLen
            hrBoundaryChain)
            u v heq hne
    have hsideDiff := hdiff
    by_cases hchord : f = {x, y}
    · exact hchord
    · have hunit : ∃ u v, f = {u, v} ∧ FourNeighborAdjacent u v := CrosscutIndexProof.hunit c f hfc
      obtain ⟨u, v, heq, huv⟩ := hunit
      obtain ⟨z, w, hgeom, hincident⟩ := (CrosscutIndexProof.internalIncident c d hcd f hfcOrig
          hfdOrig) u v heq huv
      rcases hgeom with ⟨hvertical, hwz⟩ | ⟨hhorizontal, hwz⟩
      · have hset : f = {z + 1, z + 1 + ⟨0, 1⟩} := CrosscutIndexProof.hsetAt681 u v f z heq
          hvertical
        have habsent := edgesAbsent (z + 1) (z + 1 + ⟨0, 1⟩) hset hchord
        have hzero := (hcross z).1 (by simpa [edges] using habsent)
        have hzero' : GridRayCrossingIndex w r = GridRayCrossingIndex z r := by
          simpa [hwz] using hzero
        have hcdEq := CrosscutIndexProof.hcdEqAt689 x y p c d z w hincident hzero'
        change GridRayCrossingIndex c r ≠ GridRayCrossingIndex d r at hsideDiff
        exact False.elim (hsideDiff hcdEq)
      · have hset : f = {z + 1 + ⟨0, 1⟩, z + ⟨0, 1⟩} := CrosscutIndexProof.hsetAt695 u v f z heq
          hhorizontal
        have habsent := edgesAbsent (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) hset hchord
        have hzero := (hcross z).2.2.1 (by simpa [edges] using habsent)
        have hzero' : GridRayCrossingIndex w r = GridRayCrossingIndex z r := by
          simpa [hwz] using hzero
        have hcdEq := CrosscutIndexProof.hcdEqAt689 x y p c d z w hincident hzero'
        change GridRayCrossingIndex c r ≠ GridRayCrossingIndex d r at hsideDiff
        exact False.elim (hsideDiff hcdEq)

end ApollonianSuperharmonic

end
