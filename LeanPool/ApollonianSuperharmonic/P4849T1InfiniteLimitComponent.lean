/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4849T1Component

-- [TABLET NODE: P4849T1InfiniteLimitComponent]

/-!
# P4849T1InfiniteLimitComponent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InfiniteLimitProof

private theorem hconnX :
    ∀ (L : Set GaussianInt), ∀ (a : GaussianInt),
    let reachable (x : GaussianInt) : Prop :=
      ∃ p : List GaussianInt, p.head? = some a ∧ p.getLast? = some x ∧
        (∀ w ∈ p, w ∈ L) ∧ p.IsChain FourNeighborAdjacent
    let X : Set GaussianInt := {x | reachable x}
    (a ∈ X) → (FourNeighborConnected X) := by
  classical
  intro L a reachable X haX
  refine ⟨⟨a, haX⟩, ?_⟩
  intro x hx y hy
  rcases hx with ⟨p, hp, hpx, hpmem, hpc⟩
  rcases hy with ⟨q, hq, hqy, hqmem, hqc⟩
  have symm : ∀ u v, FourNeighborAdjacent u v → FourNeighborAdjacent v u := by
    intro u v huv
    rcases huv with rfl | rfl | rfl | rfl <;>
      simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
  have prefixReach : ∀ (r : List GaussianInt), r.head? = some a →
      (∀ t ∈ r, t ∈ L) → r.IsChain FourNeighborAdjacent →
      ∀ t ∈ r, t ∈ X := by
    intro r hr hmem hchain t ht
    obtain ⟨l₁, l₂, heq⟩ := List.mem_iff_append.mp ht
    subst r
    refine ⟨l₁ ++ [t], ?_, ?_, ?_, ?_⟩
    · simpa using hr
    · simp
    · intro u hu
      simp only [List.mem_append, List.mem_cons] at hu
      rcases hu with hu | rfl | hu
      · exact hmem u (by simp [hu])
      · exact hmem u (by simp)
      · simp at hu
    · exact (List.isChain_split.mp hchain).1
  have hpc' : p.IsChain (fun u v => FourNeighborAdjacent v u) :=
    hpc.imp (fun u v huv => symm u v huv)
  have hrev : p.reverse.IsChain FourNeighborAdjacent :=
    List.isChain_reverse.mpr hpc'
  have hqtail : q.tail.IsChain FourNeighborAdjacent := hqc.tail
  have hpn : p ≠ [] := by intro he; simp [he] at hp
  have hqn : q ≠ [] := by intro he; simp [he] at hq
  have hjoin : (p.reverse ++ q.tail).IsChain FourNeighborAdjacent := by
    apply hrev.append hqtail
    intro u hu v hv
    have hu' : u = a := by simpa [hp] using hu.symm
    subst u
    cases q with
    | nil => simp at hq
    | cons u s =>
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst u
      cases s with
      | nil => simp at hv
      | cons u s =>
        have hfirst : FourNeighborAdjacent a u := (List.isChain_cons_cons.mp hqc).1
        rcases (by simpa using hv : u = v) with rfl
        exact hfirst
  have hjoinmem : ∀ w ∈ p.reverse ++ q.tail, w ∈ X := by
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with hw | hw
    · apply prefixReach p hp hpmem hpc w
      simpa using hw
    · apply prefixReach q hq hqmem hqc w
      exact List.mem_of_mem_tail hw
  have hpne' : p.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hpn
  have hhead : (p.reverse ++ q.tail).head? = some x := by
    simp [List.head?_append, List.head?_reverse, hpx]
  have hlast : (p.reverse ++ q.tail).getLast? = some y := by
    cases q with
    | nil => simp at hq
    | cons u s =>
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst u
      cases s with
      | nil =>
        simp at hqy
        subst y
        simp [hp]
      | cons u s =>
        simpa [List.getLast?_append] using hqy
  refine ⟨p.reverse ++ q.tail, hhead, hlast, hjoinmem, ?_⟩
  exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hjoin

private theorem hadjClose :
    ∀ (L : Set GaussianInt), ∀ (a : GaussianInt),
    let reachable (x : GaussianInt) : Prop :=
      ∃ p : List GaussianInt, p.head? = some a ∧ p.getLast? = some x ∧
        (∀ w ∈ p, w ∈ L) ∧ p.IsChain FourNeighborAdjacent
    let X : Set GaussianInt := {x | reachable x}
    ∀ x ∈ X, ∀ y ∈ L, FourNeighborAdjacent x y → y ∈ X := by
  classical
  intro L a reachable X x hx y hy hxy
  rcases hx with ⟨p, hp, hpx, hpmem, hpc⟩
  have hchain : p.IsChain FourNeighborAdjacent := hpc
  have hpn : p ≠ [] := by intro he; simp [he] at hp
  refine ⟨p ++ [y], ?_, ?_, ?_, ?_⟩
  · simp [List.head?_append, hp]
  · simp [hpx]
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hpmem w hw
    · exact hy
  · apply List.isChain_append.mpr
    refine ⟨hchain, List.isChain_singleton _, ?_⟩
    intro u hu v hv
    have hu' : u = x := by simpa [hpx] using hu.symm
    have hv' : y = v := by simpa using hv
    subst u
    subst v
    exact hxy

private theorem hXinf :
    ∀ (C : ℕ → Set GaussianInt), ∀ (L : Set GaussianInt), ∀ (a : GaussianInt), (∀ (n : ℕ), a ∈ C
        n) → ((∀ (n : ℕ), FourNeighborConnected (C n)) → ((∀ (n : ℕ), ∃ (F : Finset GaussianInt),
        (↑F : Set GaussianInt) ⊆ C n ∧ n < F.card) → ((∀ (F : Finset GaussianInt), ∃ (N : ℕ), ∀ n
        ≥ N, ∀ x ∈ F, x ∈ C n ↔ x ∈ L) → (
    let reachable (x : GaussianInt) : Prop :=
      ∃ p : List GaussianInt, p.head? = some a ∧ p.getLast? = some x ∧
        (∀ w ∈ p, w ∈ L) ∧ p.IsChain FourNeighborAdjacent
    let X : Set GaussianInt := {x | reachable x}
    (a ∈ X) → ((∀ x ∈ X, ∀ y ∈ L, FourNeighborAdjacent x y → y ∈ X) → (X.Infinite)))))) := by
  classical
  intro C L a hanchor hconn hlarge hlocal reachable X haX hadjClose
  by_contra hnot
  change ¬ ¬ X.Finite at hnot
  have hXfin : X.Finite := not_not.mp hnot
  let shell : Set GaussianInt := X ∪ (fun x : GaussianInt => x + 1) '' X ∪
    (fun x : GaussianInt => x - 1) '' X ∪
    (fun x : GaussianInt => x + ⟨0, 1⟩) '' X ∪
    (fun x : GaussianInt => x - ⟨0, 1⟩) '' X
  have hshellfin : shell.Finite := by
    dsimp [shell]
    exact (((hXfin.union (hXfin.image (fun x : GaussianInt => x + 1))).union
      (hXfin.image (fun x : GaussianInt => x - 1))).union
      (hXfin.image (fun x : GaussianInt => x + ⟨0, 1⟩))).union
      (hXfin.image (fun x : GaussianInt => x - ⟨0, 1⟩))
  obtain ⟨N, hN⟩ := hlocal hshellfin.toFinset
  let n := max N hshellfin.toFinset.card
  obtain ⟨F, hFsub, hFcard⟩ := hlarge n
  have hFn : ¬ (F : Set GaussianInt) ⊆ shell := by
    intro hsubset
    have hcard : F.card ≤ hshellfin.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have hxShell : (x : GaussianInt) ∈ shell := hsubset (by simpa using hx)
      simpa using hshellfin.mem_toFinset.mpr hxShell
    have : n < hshellfin.toFinset.card := by omega
    omega
  obtain ⟨b, hbF, hbnot⟩ := Set.not_subset.mp hFn
  have hbC : b ∈ C n := hFsub (by simpa using hbF)
  have hbnotX : b ∉ X := by
    intro hbX
    exact hbnot (by simp [shell, hbX])
  rcases (hconn n).2 a (hanchor n) b hbC with ⟨p, hp, hpb, hpmem, hpadj⟩
  have firstExit : ∀ (p : List GaussianInt) (x : GaussianInt),
      p.head? = some x → p.getLast? = some b →
      (∀ w ∈ p, w ∈ C n) → p.IsChain FourNeighborAdjacent →
      x ∈ X → b ∉ X →
      ∃ u v, u ∈ p ∧ v ∈ p ∧ u ∈ X ∧ v ∉ X ∧ FourNeighborAdjacent u v := by
    intro p
    induction p with
    | nil =>
      intro x hhead _ _ _ _ _
      simp at hhead
    | cons u rest ih =>
      intro x hhead hlast hmem hchain huX hbX
      have hux : u = x := by simpa using hhead
      subst x
      cases rest with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst b
        exact (hbX huX).elim
      | cons v tail =>
        have htailLast : (v :: tail).getLast? = some b := by simpa using hlast
        have htailMem : ∀ w ∈ v :: tail, w ∈ C n := by
          intro w hw
          exact hmem w (by simp [hw])
        have htailChain : List.IsChain FourNeighborAdjacent (v :: tail) :=
          hchain.tail
        have huv : FourNeighborAdjacent u v := (List.isChain_cons_cons.mp hchain).1
        by_cases hvX : v ∈ X
        · obtain ⟨s, t, hsP, htP, hsX, htX, hst⟩ :=
            ih v (by rfl) htailLast htailMem htailChain hvX hbX
          exact ⟨s, t, by simp [hsP], by simp [htP], hsX, htX, hst⟩
        · exact ⟨u, v, by simp, by simp, huX, hvX, huv⟩
  obtain ⟨x, y, hxP, hyP, hxX, hyX, hxy⟩ :=
    firstExit p a hp hpb hpmem
      (List.isChain_iff_forall_rel_of_append_cons_cons.mpr hpadj)
      haX hbnotX
  have hxC : x ∈ C n := hpmem x hxP
  have hyC : y ∈ C n := hpmem y hyP
  have hxShell : x ∈ shell := by simp [shell, hxX]
  have hyShell : y ∈ shell := by
    rcases hxy with rfl | rfl | rfl | rfl <;> simp [shell, hxX]
  have hnN : n ≥ N := by dsimp [n]; omega
  have hxL : x ∈ L := (hN n hnN x (hshellfin.mem_toFinset.mpr hxShell)).mp hxC
  have hyL : y ∈ L := (hN n hnN y (hshellfin.mem_toFinset.mpr hyShell)).mp hyC
  exact hyX (hadjClose x hxX y hyL hxy)

end InfiniteLimitProof

theorem P4849T1InfiniteLimitComponent :
    ∀ (C : ℕ → Set GaussianInt), ∀ (L : Set GaussianInt), ∀ (z : GaussianInt), ∀ (a :
        GaussianInt), (FourNeighborAdjacent z a) → ((∀ n, z ∉ C n) → ((∀ n, a ∈ C n) → ((∀ n,
        FourNeighborConnected (C n)) → ((∀ n, ∃ F : Finset GaussianInt, (↑F : Set GaussianInt) ⊆
        C n ∧ n < F.card) → ((∀ F : Finset GaussianInt, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F,
      (x ∈ C n ↔ x ∈ L)) → (∃ X : Set GaussianInt, P4849T1Component L X ∧ X.Infinite ∧ a ∈ X ∧
          z ∉ X)))))) := by
  intro C L z a hadj hzero hanchor hconn hlarge hlocal
-- BODY
  classical
  have haL : a ∈ L := by
    obtain ⟨N, hN⟩ := hlocal {a}
    exact (hN N le_rfl a (by simp)).mp (hanchor N)
  have hzL : z ∉ L := by
    obtain ⟨N, hN⟩ := hlocal {z}
    intro hz
    exact hzero N ((hN N le_rfl z (by simp)).mpr hz)
  let reachable (x : GaussianInt) : Prop :=
    ∃ p : List GaussianInt, p.head? = some a ∧ p.getLast? = some x ∧
      (∀ w ∈ p, w ∈ L) ∧ p.IsChain FourNeighborAdjacent
  let X : Set GaussianInt := {x | reachable x}
  have haX : a ∈ X := by
    refine ⟨[a], rfl, rfl, ?_, List.isChain_singleton _⟩
    intro w hw
    have hwa : w = a := by simpa using hw
    simpa [hwa] using haL
  have hsub : X ⊆ L := by
    intro x hx
    rcases hx with ⟨p, hp, hlast, hpmem, hchain⟩
    have hne : p ≠ [] := by intro he; simp [he] at hp
    have hxmem : x ∈ p := by
      rw [← List.getLast_of_getLast?_eq_some hlast]
      exact List.getLast_mem hne
    exact hpmem x hxmem
  have hconnX : FourNeighborConnected X := InfiniteLimitProof.hconnX L a haX
  have hadjClose : ∀ x ∈ X, ∀ y ∈ L, FourNeighborAdjacent x y → y ∈ X :=
      InfiniteLimitProof.hadjClose L a
  have hcomp : P4849T1Component L X := by
    exact ⟨hconnX, hsub, hadjClose⟩
  have hzX : z ∉ X := by
    intro hz
    exact hzL (hsub hz)
  have hXinf : X.Infinite := InfiniteLimitProof.hXinf C L a hanchor hconn hlarge hlocal haX
      hadjClose
  exact ⟨X, hcomp, hXinf, haX, hzX⟩

end ApollonianSuperharmonic

end
