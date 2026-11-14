/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: FiniteConnectedAcyclicDegreeTwoGridPath]

/-!
# FiniteConnectedAcyclicDegreeTwoGridPath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GridPathProof

private theorem hXfinite :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), (E.Finite) → ((X = {x | ∃ e ∈ E, x
        ∈ e}) → (X.Finite)) := by
  classical
  intro X E hEfinite hendpoints
  rw [hendpoints]
  have heq : {x : GaussianInt | ∃ e ∈ E, x ∈ e} =
      ⋃ e ∈ E, (e : Set GaussianInt) := by
    ext x
    simp
  rw [heq]
  exact hEfinite.biUnion (fun e he => e.finite_toSet)

private theorem hXne :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), (E.Nonempty) → ((X = {x | ∃ e ∈ E,
        x ∈ e}) → ((∀ e ∈ E, ∃ a b : GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) →
        (X.Nonempty))) := by
  classical
  intro X E hEne hendpoints hgrid
  obtain ⟨e, he⟩ := hEne
  obtain ⟨a, b, hab, habadj⟩ := hgrid e he
  have ha : a ∈ X := by
    rw [hendpoints]
    exact ⟨e, he, hab ▸ by simp⟩
  exact ⟨a, ha⟩

private theorem vertexNonempty :
    ∀ (X : Set GaussianInt), (X.Nonempty) → (Nonempty X) := by
  classical
  intro X hXne
  exact hXne.to_subtype

private theorem hlengths :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    (X.Finite) → (
    let lengths : Set Nat := {n | ∃ (u v : X) (p : G.Walk u v),
      p.IsPath ∧ p.length = n}
    lengths.Finite) := by
  classical
  intro X E G hXfinite lengths
  let vertexFiniteness : Fintype X := hXfinite.fintype
  let edgeFiniteness : Fintype G.edgeSet := Fintype.ofFinite _
  apply Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
  intro n hn
  obtain ⟨u', v', p', hp', rfl⟩ := hn
  exact hp'.isTrail.length_le_card_edgeFinset

private theorem hmax :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    let lengths : Set Nat := {n | ∃ (u v : X) (p : G.Walk u v),
      p.IsPath ∧ p.length = n}
    ∀ (n : ℕ), (∀ ⦃y : ℕ⦄, (fun (x : ℕ) => x ∈ lengths) y → n ≤ y → y ≤ n) → (∀ (u : (↑X :
        Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (p.length = n) → (∀ (u' : X), ∀ (v' :
        X), ∀ (p' : G.Walk u' v'), (p'.IsPath) → (p'.length ≤ p.length))) := by
  classical
  intro X E G lengths n hnl u v p hp_len u' v' p' hp'
  have hm := hnl ⟨u', v', p', hp', rfl⟩
  lia

private theorem hlong :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), (E.Nonempty) → ((X = {x | ∃ e ∈ E,
        x ∈ e}) → ((∀ e ∈ E, ∃ a b : GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) → (
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (∀ (u' : X), ∀ (v' : X), ∀ (p'
        : G.Walk u' v'), (p'.IsPath) → (p'.length ≤ p.length)) → (0 < p.length)))) := by
  classical
  intro X E hEne hendpoints hgrid G u v p hmax
  obtain ⟨e, he⟩ := hEne
  obtain ⟨a, b, hab, habadj⟩ := hgrid e he
  have ha : a ∈ X := by
    rw [hendpoints]
    exact ⟨e, he, hab ▸ by simp⟩
  have hb : b ∈ X := by
    rw [hendpoints]
    exact ⟨e, he, hab ▸ by simp⟩
  have habne : (⟨a, ha⟩ : X) ≠ ⟨b, hb⟩ := by
    intro heq
    have : a = b := congrArg Subtype.val heq
    subst b
    change a = a + 1 ∨ a = a - 1 ∨ a = a + ⟨0, 1⟩ ∨ a = a - ⟨0, 1⟩ at habadj
    rcases habadj with h | h | h | h
    · have hc : a + 0 = a + 1 := (add_zero a).trans h
      have hz : (0 : GaussianInt) = 1 := add_left_cancel hc
      exact one_ne_zero hz.symm
    · have hc : a + 0 = a + (-1) := (add_zero a).trans (h.trans (sub_eq_add_neg a 1))
      have hz : (0 : GaussianInt) = -1 := add_left_cancel hc
      have hc' := congrArg (fun z : GaussianInt => z + 1) hz
      norm_num at hc'
    · have hc := congrArg (fun z : GaussianInt => z - a) h
      have hi := congrArg Zsqrtd.im hc
      norm_num at hi
    · have hc := congrArg (fun z : GaussianInt => z - a) h
      have hi := congrArg Zsqrtd.im hc
      norm_num at hi
  have hadj : G.Adj (⟨a, ha⟩ : X) ⟨b, hb⟩ := by
    change (⟨a, ha⟩ : X) ≠ ⟨b, hb⟩ ∧
      (({a, b} : Finset GaussianInt) ∈ E ∨ ({b, a} : Finset GaussianInt) ∈ E)
    exact ⟨habne, Or.inl (by simpa [← hab] using he)⟩
  have hpath : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
    SimpleGraph.Walk.IsPath.of_adj hadj
  have hm := hmax _ _ _ hpath
  simpa [Nat.lt_iff_add_one_le] using hm

private theorem hboundary :
    ∀ (X : Set GaussianInt),
      ∀ (E : Set (Finset GaussianInt)),
        (∀ v : X,
            Set.ncard
                ((SimpleGraph.fromRel fun a b : X =>
                      ({ a.1, b.1 } : Finset GaussianInt) ∈ E).neighborSet
                  v) ≤
              2) →
          let G : SimpleGraph X :=
            SimpleGraph.fromRel fun a b : X => ({ a.1, b.1 } : Finset GaussianInt) ∈ E;
          X.Finite →
            ∀ (u : (↑X : Type)),
              ∀ (v : (↑X : Type)),
                ∀ (p : G.Walk u v),
                  p.IsPath →
                    (∀ (u' : X),
                        ∀ (v' : X),
                          ∀ (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length) →
                      ∀ z : X, z ∈ p.support → ∀ w : X, G.Adj z w → w ∈ p.support := by
  classical
  intro X E hdegree G hXfinite u v p hp hmax
  let vertexFiniteness : Fintype X := hXfinite.fintype
  intro z hz w hzw
  by_contra hwo
  obtain ⟨q, r, hq, hr, hpqr⟩ := hp.mem_support_iff_exists_append.mp hz
  by_cases hqn : q.Nil
  · have hzu : z = u := by exact (hq.nil_iff_eq.mp hqn).symm
    subst z
    have hpc : (p.cons hzw.symm).IsPath := hp.cons hwo
    have hm := hmax w v (p.cons hzw.symm) hpc
    simp only [SimpleGraph.Walk.length_cons] at hm
    omega
  · by_cases hrn : r.Nil
    · have hzv : z = v := hr.nil_iff_eq.mp hrn
      subst z
      have hpc : (p.concat hzw).IsPath := hp.concat hwo hzw
      have hm := hmax u w (p.concat hzw) hpc
      simp only [SimpleGraph.Walk.length_concat] at hm
      omega
    · have hleft : G.Adj q.penultimate z := q.adj_penultimate hqn
      have hright : G.Adj z r.snd := r.adj_snd hrn
      have hqp : q.penultimate ∈ q.support := by
        apply q.getVert_mem_support
      have hrp : r.snd ∈ r.support.tail := r.snd_mem_tail_support hrn
      have hrp' : r.snd ∈ r.tail.support := by
        simpa [SimpleGraph.Walk.support_tail_of_not_nil r hrn] using hrp
      have hne : q.penultimate ≠ r.snd := by
        intro heq
        have happ : (q.append r).IsPath := hpqr ▸ hp
        have hd := happ.disjoint_support_of_append hrn
        apply hd hqp
        simpa only [heq] using hrp'
      have hqp0 : q.penultimate ∈ p.support := by
        rw [hpqr]
        simp [SimpleGraph.Walk.support_append, hqp]
      have hrp0 : r.snd ∈ p.support := by
        rw [hpqr]
        simp [SimpleGraph.Walk.support_append, hrp]
      have hqw : q.penultimate ≠ w := by
        intro heq
        exact hwo (heq ▸ hqp0)
      have hrw : r.snd ≠ w := by
        intro hrw
        exact hwo (hrw ▸ hrp0)
      have hsub : ({q.penultimate, r.snd, w} : Set X) ⊆ G.neighborSet z := by
        intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl | rfl
        · exact show G.Adj z q.penultimate from hleft.symm
        · exact hright
        · exact hzw
      have hcard : Set.ncard ({q.penultimate, r.snd, w} : Set X) = 3 := by
        simp [hne, hqw, hrw]
      have hc := Set.ncard_mono hsub
      rw [hcard] at hc
      have hd := hdegree z
      change (G.neighborSet z).ncard ≤ 2 at hd
      exact (by omega)

private theorem hall :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    (G.Connected) → (∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (∀ z : X, z ∈
        p.support → ∀ w : X, G.Adj z w → w ∈ p.support) → (∀ (x : X), x ∈ p.support)) := by
  classical
  intro X E G hGconn u v p hboundary
  have hwalk : ∀ {a b : X} (q : G.Walk a b),
      a ∈ p.support → ∀ t, t ∈ q.support → t ∈ p.support := by
    intro a b q
    induction q with
    | nil =>
        intro ha t ht
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
        subst t
        exact ha
    | @cons a b c hadj q ih =>
        intro ha t ht
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ha
        · exact ih (hboundary a ha b hadj) t ht
  intro x
  obtain ⟨q⟩ := hGconn u x
  exact hwalk q p.start_mem_support x q.end_mem_support

private theorem hsupport :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (∀ (x : X), x ∈ p.support) →
        ({x : X | x ∈ p.support} = Set.univ) := by
  classical
  intro X E G u v p hall
  apply Set.eq_univ_of_forall
  exact hall

private theorem hLnodup :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (p.IsPath) → (
    let L : List GaussianInt := p.support.map Subtype.val
    L.Nodup) := by
  classical
  intro X E G u v p hp L
  exact hp.support_nodup.map Subtype.val_injective

private theorem hLlen :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v),
    let L : List GaussianInt := p.support.map Subtype.val
    L.length = p.length + 1 := by
  classical
  intro X E G u v p L
  simp [L, SimpleGraph.Walk.length_support]

private theorem hLchain :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v),
    let L : List GaussianInt := p.support.map Subtype.val
    List.IsChain (fun a b : GaussianInt =>
      ({a, b} : Finset GaussianInt) ∈ E) L := by
  classical
  intro X E G u v p L
  rw [List.isChain_map]
  apply p.isChain_adj_support.imp
  intro a b hab
  change a ≠ b ∧
    (({a.1, b.1} : Finset GaussianInt) ∈ E ∨
      ({b.1, a.1} : Finset GaussianInt) ∈ E) at hab
  exact hab.2.elim id (by simp [Finset.pair_comm])

private theorem hgridstep :
    ∀ (X : Set GaussianInt),
      ∀ (E : Set (Finset GaussianInt)),
        X = {x | ∃ e ∈ E, x ∈ e} →
          (∀ e ∈ E, ∃ a b : GaussianInt, e = { a, b } ∧ FourNeighborAdjacent a b) →
            let G : SimpleGraph X :=
              SimpleGraph.fromRel fun a b : X => ({ a.1, b.1 } : Finset GaussianInt) ∈ E;
            ∀ (n : ℕ),
              ∀ (u : (↑X : Type)),
                ∀ (v : (↑X : Type)),
                  ∀ (p : G.Walk u v),
                    p.length = n →
                      0 < p.length →
                        {x : X | x ∈ p.support} = Set.univ →
                          let L : List GaussianInt := p.support.map Subtype.val;
                          L.length = p.length + 1 →
                            ∀ a b : GaussianInt,
                            ({ a, b } : Finset GaussianInt) ∈ E → FourNeighborAdjacent a b := by
  classical
  intro X E hendpoints hgrid G n u v p hp_len hlong hsupport L hLlen
  have hsymm : ∀ a b : GaussianInt, FourNeighborAdjacent a b →
      FourNeighborAdjacent b a := by
    intro a b h
    unfold FourNeighborAdjacent at h ⊢
    rcases h with h | h | h | h
    · right; left
      have hh := congrArg (fun z : GaussianInt => z - 1) h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh.symm
    · left
      have hh := congrArg (fun z : GaussianInt => z + 1) h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh.symm
    · right; right; right
      have hh := congrArg (fun z : GaussianInt => z - ⟨0, 1⟩) h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh.symm
    · right; right; left
      have hh := congrArg (fun z : GaussianInt => z + ⟨0, 1⟩) h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh.symm
  intro a b he
  obtain ⟨c, d, hcd, hfour⟩ := hgrid _ he
  have hpairs : ({a, b} : Finset GaussianInt) = {c, d} := hcd ▸ rfl
  have hpairs' : c = a ∧ d = b ∨ c = b ∧ d = a := by
    simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at hpairs
    have hc := (hpairs c).mpr (by simp)
    have hd := (hpairs d).mpr (by simp)
    have ha := (hpairs a).mp (by simp)
    have hb := (hpairs b).mp (by simp)
    clear hpairs
    rcases hc with hc | hc <;> rcases hd with hd | hd <;>
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      subst_vars <;> simp_all only [or_true, true_or,
        eq_self, and_self]
  rcases hpairs' with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · subst c; subst d; exact hfour
  · subst c; subst d
    exact hsymm _ _ hfour

private theorem hstep :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v),
    let L : List GaussianInt := p.support.map Subtype.val
    (List.IsChain (fun a b : GaussianInt => ({a, b} : Finset GaussianInt) ∈ E) L) → ((∀ a b :
        GaussianInt, ({a, b} : Finset GaussianInt) ∈ E → FourNeighborAdjacent a b) → (∀ a b :
        GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      L = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b)) := by
  classical
  intro X E G u v p L hLchain hgridstep a b l₁ l₂ h
  have hc := (List.isChain_iff_forall_rel_of_append_cons_cons.mp hLchain) h
  exact hgridstep a b hc

private theorem hset :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (∀ (x : X), x ∈ p.support) → (
    let L : List GaussianInt := p.support.map Subtype.val
    (L.toFinset : Set GaussianInt) = X) := by
  classical
  intro X E G u v p hall L
  ext a
  constructor
  · intro ha
    have hz : a ∈ L := by simpa using ha
    obtain ⟨z, hz, hza⟩ := List.mem_map.mp hz
    have haX : a ∈ X := by simpa [hza] using z.property
    exact haX
  · intro ha
    let z : X := ⟨a, ha⟩
    have hz : z ∈ p.support := hall z
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨z, hz, rfl⟩

private theorem hconsecutive :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    (G.IsAcyclic) → (∀ (u : (↑X : Type)), ∀ (v : (↑X : Type)), ∀ (p : G.Walk u v), (p.IsPath) →
        ((∀ (x : X), x ∈ p.support) → (∀ {a : X}, ∀ {b : X}, G.Adj a b →
      ∃ l₁ l₂ : List X, p.support = l₁ ++ a :: b :: l₂ ∨
        p.support = l₁ ++ b :: a :: l₂))) := by
  classical
  intro X E G hGacyc u v p hp hall a b hab
  obtain ⟨q, r, hq, hr, hpqr⟩ :=
    hp.mem_support_iff_exists_append.mp (hall b)
  have haa : a ∈ q.support ∨ a ∈ r.support := by
    have haa' := hall a
    rw [hpqr] at haa'
    have haa'' : a ∈ q.support ∨ a ∈ r.support.tail := by
      simpa [SimpleGraph.Walk.support_append] using haa'
    exact haa''.imp id (fun h => List.mem_of_mem_tail h)
  rcases haa with haa | haa
  · obtain ⟨q₁, q₂, hq₁, hq₂, hqq⟩ :=
      hq.mem_support_iff_exists_append.mp haa
    have heq : q₂ = hab.toWalk := by
      exact congrArg Subtype.val
        ((hGacyc.subsingleton_path a b).elim ⟨q₂, hq₂⟩
          ⟨hab.toWalk, hab.isPath_toWalk⟩)
    refine ⟨q₁.support.dropLast, r.support.tail, Or.inl ?_⟩
    rw [hpqr, hqq, heq]
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      hab.support_toWalk]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ :=
      hr.mem_support_iff_exists_append.mp haa
    have heq : r₁ = hab.symm.toWalk := by
      exact congrArg Subtype.val
        ((hGacyc.subsingleton_path b a).elim ⟨r₁, hr₁⟩
          ⟨hab.symm.toWalk, hab.symm.isPath_toWalk⟩)
    refine ⟨q.support.dropLast, r₂.support.tail, Or.inr ?_⟩
    rw [hpqr, hrr, heq]
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
      hab.symm.support_toWalk]
    have hqend : q.support.dropLast ++ [b] = q.support := by
      simpa only [q.getLast_support] using
        (List.dropLast_append_getLast q.support_ne_nil)
    have htail : ([b, a] ++ r₂.support.tail).tail = a :: r₂.support.tail := by
      rfl
    rw [htail]
    conv_lhs => rw [← hqend]
    simp only [List.cons_append, List.nil_append, List.append_assoc]

end GridPathProof

theorem FiniteConnectedAcyclicDegreeTwoGridPath
    (X : Set GaussianInt) (E : Set (Finset GaussianInt))
    (hEfinite : E.Finite) (hEne : E.Nonempty)
    (hendpoints : X = {x | ∃ e ∈ E, x ∈ e})
    (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
      e = {a, b} ∧ FourNeighborAdjacent a b)
    (hconnected :
      (SimpleGraph.fromRel fun a b : X =>
        ({a.1, b.1} : Finset GaussianInt) ∈ E).Connected)
    (hacyclic :
      (SimpleGraph.fromRel fun a b : X =>
        ({a.1, b.1} : Finset GaussianInt) ∈ E).IsAcyclic)
    (hdegree : ∀ v : X,
      Set.ncard ((SimpleGraph.fromRel fun a b : X =>
        ({a.1, b.1} : Finset GaussianInt) ∈ E).neighborSet v) ≤ 2) :
    ∃ x y : GaussianInt, SimpleGridPathBetween X E x y := by
-- BODY
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b : X =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  have hXfinite : X.Finite := GridPathProof.hXfinite X E hEfinite hendpoints
  have hXne : X.Nonempty := GridPathProof.hXne X E hEne hendpoints hgrid
  let vertexNonempty : Nonempty X := GridPathProof.vertexNonempty X hXne
  have hGconn : G.Connected := hconnected
  have hGacyc : G.IsAcyclic := hacyclic
  let lengths : Set Nat := {n | ∃ (u v : X) (p : G.Walk u v),
    p.IsPath ∧ p.length = n}
  have hlengths : lengths.Finite := GridPathProof.hlengths X E hXfinite
  obtain ⟨n, hn, hnl⟩ := hlengths.exists_maximal
    ⟨0, ⟨Classical.choice (inferInstance : Nonempty X),
      Classical.choice (inferInstance : Nonempty X), SimpleGraph.Walk.nil,
      SimpleGraph.Walk.IsPath.nil, by simp⟩⟩
  obtain ⟨u, v, p, hp, hp_len⟩ := hn
  have hmax : ∀ (u' v' : X) (p' : G.Walk u' v') (_ : p'.IsPath),
      p'.length ≤ p.length := GridPathProof.hmax X E n hnl u v p hp_len
  have hlong : 0 < p.length := GridPathProof.hlong X E hEne hendpoints hgrid u v p hmax
  have hboundary : ∀ z : X, z ∈ p.support →
      ∀ w : X, G.Adj z w → w ∈ p.support := GridPathProof.hboundary X E hdegree hXfinite u v p
          hp hmax
  have hall : ∀ (x : X), x ∈ p.support := GridPathProof.hall X E hGconn u v p hboundary
  have hsupport : {x : X | x ∈ p.support} = Set.univ := GridPathProof.hsupport X E u v p hall
  let L : List GaussianInt := p.support.map Subtype.val
  have hLnodup : L.Nodup := GridPathProof.hLnodup X E u v p hp
  have hLlen : L.length = p.length + 1 := GridPathProof.hLlen X E u v p
  have hLchain : List.IsChain (fun a b : GaussianInt =>
      ({a, b} : Finset GaussianInt) ∈ E) L := GridPathProof.hLchain X E u v p
  have hgridstep : ∀ a b : GaussianInt,
      ({a, b} : Finset GaussianInt) ∈ E → FourNeighborAdjacent a b := GridPathProof.hgridstep X E
          hendpoints hgrid n
          u v p hp_len hlong hsupport hLlen
  have hstep : ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      L = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b := GridPathProof.hstep X E u v p hLchain
          hgridstep
  have hset : (L.toFinset : Set GaussianInt) = X := GridPathProof.hset X E u v p hall
  have hconsecutive : ∀ {a b : X}, G.Adj a b →
      ∃ l₁ l₂ : List X, p.support = l₁ ++ a :: b :: l₂ ∨
        p.support = l₁ ++ b :: a :: l₂ := GridPathProof.hconsecutive X E hGacyc u v p hp hall
  refine ⟨u.1, v.1, ?_⟩
  refine ⟨L, hLnodup, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLlen]
    omega
  · change (p.support.map Subtype.val).head? = some u.1
    rw [List.head?_map, List.head?_eq_some_head p.support_ne_nil, p.head_support]
    rfl
  · have hLn : L ≠ [] := by
      intro hnil
      have hz : L.length = 0 := by simp [hnil]
      rw [hLlen] at hz
      omega
    have hlast : L.getLast hLn = Subtype.val (p.support.getLast p.support_ne_nil) := by
      exact List.getLast_map hLn
    rw [List.getLast?_eq_some_getLast hLn, hlast]
    exact congrArg (fun z => some z) (congrArg Subtype.val p.getLast_support)
  · exact hset.symm
  · refine ⟨hstep, ?_⟩
    intro e
    constructor
    · intro he
      obtain ⟨a, b, hab, hfour⟩ := hgrid e he
      have ha : a ∈ X := by
        rw [hendpoints]
        exact ⟨e, he, hab ▸ by simp⟩
      have hb : b ∈ X := by
        rw [hendpoints]
        exact ⟨e, he, hab ▸ by simp⟩
      let a' : X := ⟨a, ha⟩
      let b' : X := ⟨b, hb⟩
      have habne : a ≠ b := by
        intro hz
        subst b
        unfold FourNeighborAdjacent at hfour
        rcases hfour with h | h | h | h
        · have hc : a + 0 = a + 1 := (add_zero a).trans h
          have hz' : (0 : GaussianInt) = 1 := add_left_cancel hc
          exact one_ne_zero hz'.symm
        · have hc : a + 0 = a + (-1) := (add_zero a).trans (h.trans (sub_eq_add_neg a 1))
          have hz' : (0 : GaussianInt) = -1 := add_left_cancel hc
          have hc' := congrArg (fun z : GaussianInt => z + 1) hz'
          norm_num at hc'
        · have hc := congrArg (fun z : GaussianInt => z - a) h
          have hi := congrArg Zsqrtd.im hc
          norm_num at hi
        · have hc := congrArg (fun z : GaussianInt => z - a) h
          have hi := congrArg Zsqrtd.im hc
          norm_num at hi
      have hadj : G.Adj a' b' := by
        change a' ≠ b' ∧ _
        have he' : ({a, b} : Finset GaussianInt) ∈ E := by
          simpa [← hab] using he
        exact ⟨by
          intro heq
          exact habne (congrArg Subtype.val heq),
          Or.inl (by simpa [a', b'] using he')⟩
      obtain ⟨l₁, l₂, hs | hs⟩ := hconsecutive hadj
      · refine ⟨a, b, l₁.map Subtype.val, l₂.map Subtype.val, ?_, hab⟩
        simp [a', b', L, hs, List.map_append]
      · refine ⟨b, a, l₁.map Subtype.val, l₂.map Subtype.val, ?_, ?_⟩
        · simp [a', b', L, hs, List.map_append]
        · simpa [Finset.pair_comm] using hab
    · intro he
      obtain ⟨a, b, l₁, l₂, hs, he⟩ := he
      rw [he]
      exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp hLchain) hs

end ApollonianSuperharmonic

end
