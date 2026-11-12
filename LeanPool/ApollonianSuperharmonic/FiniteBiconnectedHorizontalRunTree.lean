/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndexAdjacentCell

/-!
# FiniteBiconnectedHorizontalRunTree

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open scoped BigOperators

-- [TABLET NODE: FiniteBiconnectedHorizontalRunTree]
namespace HorizontalRunTreeProof

private theorem edgeOf_injective :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let HF : Finset GaussianInt := S.filter fun z => z - 1 ∈ S
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (horizontal_adj : ∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hz1 : z + 1 ∈ S), G.Adj ⟨z, hz⟩
        ⟨z + 1, hz1⟩), ∀ (selected_vertical_adj : ∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hzI : z
        + I ∈ S), (z ∈ JF) → (G.Adj ⟨z, hz⟩ ⟨z + I, hzI⟩)),
    let D := {z : GaussianInt // z ∈ HF} ⊕ {z : GaussianInt // z ∈ JF}
    let edgeOf : D → G.edgeSet := fun d => match d with
      | Sum.inl z =>
          let hz : z.1 ∈ S := (Finset.mem_filter.mp z.2).1
          let hz1 : z.1 - 1 ∈ S := (Finset.mem_filter.mp z.2).2
          ⟨s(⟨z.1 - 1, hz1⟩, ⟨z.1, hz⟩), by
            rw [SimpleGraph.mem_edgeSet]
            have h := horizontal_adj (z := z.1 - 1) hz1
              (by simpa [Zsqrtd.ext_iff] using hz)
            simpa [Zsqrtd.ext_iff] using h⟩
      | Sum.inr z =>
          let hzV : z.1 ∈ VF := (Finset.mem_filter.mp z.2).1
          let hz : z.1 ∈ S := (Finset.mem_filter.mp hzV).1
          let hzI : z.1 + I ∈ S := (Finset.mem_filter.mp hzV).2
          ⟨s(⟨z.1, hz⟩, ⟨z.1 + I, hzI⟩), by
            rw [SimpleGraph.mem_edgeSet]
            exact selected_vertical_adj hz hzI z.2⟩
    Function.Injective edgeOf := by
  classical
  intro S I HF VF JF X rel G horizontal_adj selected_vertical_adj D edgeOf a b hab
  rcases a with a | a <;> rcases b with b | b
  · apply congrArg Sum.inl
    apply Subtype.ext
    dsimp [edgeOf] at hab
    have hs := congrArg Subtype.val hab
    rcases Sym2.eq_iff.mp hs with h | h
    · exact congrArg (fun z : X => z.1) h.2
    · have h1 := congrArg (fun z : X => z.1.re) h.1
      have h2 := congrArg (fun z : X => z.1.re) h.2
      simp at h1 h2
      omega
  · dsimp [edgeOf] at hab
    have hs := congrArg Subtype.val hab
    rcases Sym2.eq_iff.mp hs with h | h
    · exfalso
      have hi1 := congrArg (fun z : X => z.1.im) h.1
      have hi2 := congrArg (fun z : X => z.1.im) h.2
      simp [I] at hi1 hi2
      omega
    · exfalso
      have hi1 := congrArg (fun z : X => z.1.im) h.1
      have hi2 := congrArg (fun z : X => z.1.im) h.2
      simp [I] at hi1 hi2
      omega
  · dsimp [edgeOf] at hab
    have hs := congrArg Subtype.val hab
    rcases Sym2.eq_iff.mp hs with h | h
    · exfalso
      have hi1 := congrArg (fun z : X => z.1.im) h.1
      have hi2 := congrArg (fun z : X => z.1.im) h.2
      simp [I] at hi1 hi2
      omega
    · exfalso
      have hi1 := congrArg (fun z : X => z.1.im) h.1
      have hi2 := congrArg (fun z : X => z.1.im) h.2
      simp [I] at hi1 hi2
      omega
  · apply congrArg Sum.inr
    apply Subtype.ext
    dsimp [edgeOf] at hab
    have hs := congrArg Subtype.val hab
    rcases Sym2.eq_iff.mp hs with h | h
    · exact congrArg (fun z : X => z.1) h.1
    · have hi1 := congrArg (fun z : X => z.1.im) h.1
      have hi2 := congrArg (fun z : X => z.1.im) h.2
      simp [I] at hi1 hi2
      omega

private theorem edgeOf_surjective :
    ∀ (S : Finset GaussianInt), let I : GaussianInt := ⟨0, 1⟩
    let HF : Finset GaussianInt := S.filter fun z => z - 1 ∈ S
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ (a : X), ∀ (b : X), G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a)) → (∀ (horizontal_adj : ∀
        {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hz1 : z + 1 ∈ S), G.Adj ⟨z, hz⟩
        ⟨z + 1, hz1⟩), ∀ (selected_vertical_adj : ∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hzI : z
        + I ∈ S), (z ∈ JF) → (G.Adj ⟨z, hz⟩ ⟨z + I, hzI⟩)), let D := {z : GaussianInt // z ∈ HF}
            ⊕ {z : GaussianInt // z ∈ JF}
    let edgeOf : D → G.edgeSet := fun d => match d with
      | Sum.inl z =>
          let hz : z.1 ∈ S := (Finset.mem_filter.mp z.2).1
          let hz1 : z.1 - 1 ∈ S := (Finset.mem_filter.mp z.2).2
          ⟨s(⟨z.1 - 1, hz1⟩, ⟨z.1, hz⟩), by
            rw [SimpleGraph.mem_edgeSet]
            have h := horizontal_adj (z := z.1 - 1) hz1
              (by simpa [Zsqrtd.ext_iff] using hz)
            simpa [Zsqrtd.ext_iff] using h⟩
      | Sum.inr z =>
          let hzV : z.1 ∈ VF := (Finset.mem_filter.mp z.2).1
          let hz : z.1 ∈ S := (Finset.mem_filter.mp hzV).1
          let hzI : z.1 + I ∈ S := (Finset.mem_filter.mp hzV).2
          ⟨s(⟨z.1, hz⟩, ⟨z.1 + I, hzI⟩), by
            rw [SimpleGraph.mem_edgeSet]
            exact selected_vertical_adj hz hzI z.2⟩
    Function.Surjective edgeOf) := by
  classical
  intro S I HF VF JF X rel G graph_adj horizontal_adj selected_vertical_adj D edgeOf
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, graph_adj] at he
    rcases he with ⟨hne, hab | hba⟩
    · rcases hab with hab | hab
      · have hbS : b.1 ∈ S := b.2
        have haS : b.1 - 1 ∈ S := by simp [hab]
        have hbH : b.1 ∈ HF := by simp [HF, hbS, haS]
        refine ⟨Sum.inl ⟨b.1, hbH⟩, ?_⟩
        apply Subtype.ext
        dsimp [edgeOf]
        rw [Sym2.eq_iff]
        left
        refine ⟨?_, rfl⟩
        apply Subtype.ext
        ext <;> simp [Zsqrtd.ext_iff] at hab ⊢ <;> omega
      · have haJ : a.1 ∈ JF := hab.2
        refine ⟨Sum.inr ⟨a.1, haJ⟩, ?_⟩
        apply Subtype.ext
        dsimp [edgeOf]
        rw [Sym2.eq_iff]
        left
        exact ⟨rfl, Subtype.ext hab.1.symm⟩
    · rcases hba with hba | hba
      · have haS : a.1 ∈ S := a.2
        have hbS : a.1 - 1 ∈ S := by simp [hba]
        have haH : a.1 ∈ HF := by simp [HF, haS, hbS]
        refine ⟨Sum.inl ⟨a.1, haH⟩, ?_⟩
        apply Subtype.ext
        dsimp [edgeOf]
        rw [Sym2.eq_iff]
        right
        refine ⟨?_, rfl⟩
        apply Subtype.ext
        ext <;> simp [Zsqrtd.ext_iff] at hba ⊢ <;> omega
      · have hbJ : b.1 ∈ JF := hba.2
        refine ⟨Sum.inr ⟨b.1, hbJ⟩, ?_⟩
        apply Subtype.ext
        dsimp [edgeOf]
        rw [Sym2.eq_iff]
        right
        exact ⟨rfl, Subtype.ext hba.1.symm⟩

private theorem vertical_reachable :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hz1 : z + 1 ∈ S), G.Adj ⟨z, hz⟩ ⟨z + 1, hz1⟩) → ((∀
        {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hzI : z + I ∈ S), (z ∈ JF) → (G.Adj ⟨z, hz⟩ ⟨z + I,
        hzI⟩)) → (∀ (leftmost : GaussianInt), (∀ x' ∈ S, leftmost.re ≤ x'.re) → (∀ (z :
            GaussianInt), ∀ (hz : z ∈ S), ∀ (hzI : z + I ∈ S), G.Reachable ⟨z, hz⟩ ⟨z + I,
            hzI⟩))) := by
  classical
  intro S I VF JF X rel G horizontal_adj selected_vertical_adj leftmost hmin z hz hzI
  induction hmeasure : Int.toNat (z.re - leftmost.re) using
      Nat.strong_induction_on generalizing z with
  | h n ih =>
    by_cases hzJ : z ∈ JF
    · exact (selected_vertical_adj hz hzI hzJ).reachable
    · have hzV : z ∈ VF := by simp [VF, hz, hzI]
      have hpair : z - 1 ∈ S ∧ z - 1 + I ∈ S := by
        simp only [JF, Finset.mem_filter, hzV, true_and] at hzJ
        exact not_not.mp hzJ
      have hminLeft : leftmost.re ≤ (z - 1).re := hmin (z - 1) hpair.1
      change leftmost.re ≤ z.re - 1 at hminLeft
      have hminZ : leftmost.re ≤ z.re := hmin z hz
      have hdec : Int.toNat ((z - 1).re - leftmost.re) < n := by
        change Int.toNat (z.re - 1 - leftmost.re) < n
        rw [← hmeasure]
        exact (Int.toNat_lt_toNat (by omega)).2 (by omega)
      have hvert := ih _ hdec (z - 1) hpair.1
        (by simpa [I, Zsqrtd.ext_iff] using hpair.2) rfl
      have hleft : G.Reachable ⟨z, hz⟩ ⟨z - 1, hpair.1⟩ := by
        apply SimpleGraph.Reachable.symm
        have h := horizontal_adj (z := z - 1) hpair.1
          (by simpa [Zsqrtd.ext_iff] using hz)
        simpa [Zsqrtd.ext_iff] using h.reachable
      have hright : G.Reachable
          ⟨z - 1 + I, hpair.2⟩ ⟨z + I, hzI⟩ := by
        have h := horizontal_adj (z := z - 1 + I) hpair.2
          (by convert hzI using 1; ext <;> simp [I])
        convert h.reachable using 1; apply Subtype.ext;
          ext <;> simp [I]
      exact hleft.trans (hvert.trans hright)

private theorem four_reachable :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hz1 : z + 1 ∈ S), G.Adj ⟨z, hz⟩ ⟨z + 1, hz1⟩) → ((∀
        (z : GaussianInt), ∀ (hz : z ∈ S), ∀ (hzI : z + I ∈ S), G.Reachable ⟨z, hz⟩ ⟨z + I, hzI⟩)
        → (∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ (ha : a ∈ S), ∀ (hb : b ∈ S),
            (FourNeighborAdjacent a b) → (G.Reachable ⟨a, ha⟩ ⟨b, hb⟩))) := by
  classical
  intro S I VF JF X rel G horizontal_adj vertical_reachable a b ha hb hab
  rcases hab with rfl | rfl | rfl | rfl
  · exact (horizontal_adj ha hb).reachable
  · apply SimpleGraph.Reachable.symm
    have h := horizontal_adj (z := a - 1) hb
      (by simpa [Zsqrtd.ext_iff] using ha)
    simpa [Zsqrtd.ext_iff] using h.reachable
  · exact vertical_reachable a ha hb
  · apply SimpleGraph.Reachable.symm
    have h := vertical_reachable (a - I) hb
      (by simpa [I, Zsqrtd.ext_iff] using ha)
    simpa [I, Zsqrtd.ext_iff] using h

private theorem hconnected :
    ∀ (S : Finset GaussianInt), (FourNeighborConnected (↑S : Set LatticeCell)) → (
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (base : LatticeCell), (base ∈ (↑S : Set LatticeCell)) → ((∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, ∀ (ha : a ∈ S), ∀ (hb : b ∈ S), (FourNeighborAdjacent a b) →
        (G.Reachable ⟨a, ha⟩ ⟨b, hb⟩)) → (G.Connected))) := by
  classical
  intro S hinside I VF JF X rel G base hbase four_reachable
  refine { nonempty := ⟨⟨base, hbase⟩⟩, preconnected := ?_ }
  intro a b
  obtain ⟨p, hphead, hplast, hpmem, hpadj⟩ :=
    hinside.2 a.1 a.2 b.1 b.2
  have hpne : p ≠ [] := by intro hp; simp [hp] at hphead
  have hpchain : List.IsChain FourNeighborAdjacent p := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    exact hpadj
  let toX : GaussianInt → X := fun z =>
    if hz : z ∈ S then ⟨z, hz⟩ else ⟨base, hbase⟩
  have toX_eq (z : GaussianInt) (hz : z ∈ S) : (toX z).1 = z := by
    simp [toX, hz]
  have hpchain' : List.IsChain (fun x y : GaussianInt =>
      G.Reachable (toX x) (toX y)) p := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro x y l₁ l₂ heq
    have hx : x ∈ S := hpmem x (by rw [heq]; simp)
    have hy : y ∈ S := hpmem y (by rw [heq]; simp)
    have h := four_reachable hx hy (hpadj x y l₁ l₂ heq)
    convert h using 1 <;> apply Subtype.ext <;> simp [toX, hx, hy]
  have hreachRaw : G.Reachable (toX (p.head hpne))
      (toX (p.getLast hpne)) := by
    have hr := List.relationReflTransGen_of_exists_isChain p hpchain' hpne
    exact hr.trans_induction_on
      (motive := fun {a b} _ => G.Reachable (toX a) (toX b))
      (fun _ => SimpleGraph.Reachable.rfl) (fun h => h)
      (fun _ _ h₁ h₂ => h₁.trans h₂)
  have hhead : p.head hpne = a.1 := by
    exact (List.head_eq_iff_head?_eq_some hpne).2 hphead
  have hlast : p.getLast hpne = b.1 := by
    exact (List.getLast_eq_iff_getLast?_eq_some hpne).2 hplast
  convert hreachRaw using 1 <;> apply Subtype.ext <;>
    simp [toX, hhead, hlast, a.2, b.2]

private theorem neighbor_options :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ (a : X), ∀ (b : X), G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a)) → (∀ (u : X), ∀ (c : G.Walk u
        u), ∀ (v : X), (∀ (w : X), (w ∈ c.support) → (w.1.im ≤ v.1.im)) → ((∀ (w : X), (w ∈
        c.support) → ((w.1.im = v.1.im) → (w.1.re ≤ v.1.re))) → (∀ (w : X), (c.toSubgraph.Adj v
        w) → (w.1 = v.1 - 1 ∨ w.1 = v.1 - I)))) := by
  classical
  intro S I VF JF X rel G graph_adj u c v hv_im_max hv_re_max w hvw
  have hwmem : w ∈ c.support :=
    c.mem_verts_toSubgraph.mp (c.toSubgraph.edge_vert hvw.symm)
  have hadj : G.Adj v w := hvw.adj_sub
  rw [graph_adj] at hadj
  rcases hadj.2 with hvwrel | hwvrel
  · rcases hvwrel with hright | hup
    · exfalso
      have him : w.1.im = v.1.im := by rw [hright]; simp
      have hre := hv_re_max w hwmem him
      rw [hright] at hre
      simp at hre
    · exfalso
      have him := hv_im_max w hwmem
      rw [hup.1] at him
      simp [I] at him
  · rcases hwvrel with hleft | hdown
    · left
      rw [hleft]
      ext <;> simp
    · right
      rw [hdown.1]
      ext <;> simp [I]

private theorem hdownJ :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ (a : X), ∀ (b : X), G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a)) → (∀ (u : X), ∀ (c : G.Walk u
        u), ∀ (v : X), ∀ (hdownX : v.1 - I ∈ S), (c.toSubgraph.Adj v ⟨v.1 - I, hdownX⟩) → (v.1 -
        I ∈ JF)) := by
  classical
  intro S I VF JF X rel G graph_adj u c v hdownX hdownEdge
  have h := hdownEdge.adj_sub
  rw [graph_adj] at h
  rcases h.2 with h | h
  · rcases h with h | h
    · have hi := congrArg Zsqrtd.im h
      simp [I] at hi
    · have hi := congrArg Zsqrtd.im h.1
      simp [I] at hi
      omega
  · rcases h with h | h
    · have hr := congrArg Zsqrtd.re h
      simp [I] at hr
    · have heq : (v.1 - I : GaussianInt) + I = v.1 := by
        ext <;> simp [I]
      exact h.2

private theorem path_zip :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (3 ≤ path.length) → ((List.IsChain FourNeighborAdjacent path) → (∀ a b, (a, b) ∈ path.zip
        path.tail →
      FourNeighborAdjacent a b)) := by
  classical
  intro S I VF JF X rel G u c path path_length path_chain a b hab
  rw [List.mem_iff_getElem] at hab
  rcases hab with ⟨i, hi, hab⟩
  have hi' : i < path.tail.length := by
    simpa [List.length_zip] using hi
  have hip : i + 1 < path.length := by
    simp only [List.length_tail] at hi'
    omega
  rw [List.getElem_zip, List.getElem_tail] at hab
  injection hab with ha hb
  rw [List.isChain_iff_getElem] at path_chain
  simpa [ha, hb] using path_chain i hip

private theorem cycle_edge_oriented :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    let cyclicEdges := path.zip path.tail ++ [(u.1, c.snd.1)]
    ∀ {x : X}, ∀ {y : X}, (c.toSubgraph.Adj x y) → ((x.1, y.1) ∈ cyclicEdges ∨ (y.1, x.1) ∈
        cyclicEdges) := by
  classical
  intro S I VF JF X rel G u c path cyclicEdges x y hxy
  rw [c.toSubgraph_adj_iff] at hxy
  rcases hxy with ⟨i, heq, hi⟩
  rcases i with _ | i
  · rcases Sym2.eq_iff.mp heq with heq | heq
    · left
      simp only [cyclicEdges, List.mem_append, List.mem_singleton]
      right
      apply Prod.ext
      · simpa using congrArg (fun z : X => z.1) heq.1.symm
      · simpa using congrArg (fun z : X => z.1) heq.2.symm
    · right
      simp only [cyclicEdges, List.mem_append, List.mem_singleton]
      right
      apply Prod.ext
      · simpa using congrArg (fun z : X => z.1) heq.1.symm
      · simpa using congrArg (fun z : X => z.1) heq.2.symm
  · have hpair :
        (c.getVert (i + 1) |>.1, c.getVert (i + 2) |>.1) ∈
          path.zip path.tail := by
      rw [List.mem_iff_getElem]
      refine ⟨i, ?_, ?_⟩
      · simp [path, List.length_zip, List.length_tail,
          SimpleGraph.Walk.length_support]
        omega
      · rw [List.getElem_zip, List.getElem_tail]
        apply Prod.ext
        · simp [path, c.support_getElem_eq_getVert]
        · simp only [path, List.getElem_map, List.getElem_tail,
            ]
          congr 1
          convert c.support_getElem_eq_getVert (n := i + 2) _ using 1;
    rcases Sym2.eq_iff.mp heq with heq | heq
    · left
      dsimp only [cyclicEdges]
      apply List.mem_append_left
      simpa [congrArg (fun z : X => z.1) heq.1,
        congrArg (fun z : X => z.1) heq.2] using hpair
    · right
      dsimp only [cyclicEdges]
      apply List.mem_append_left
      simpa [congrArg (fun z : X => z.1) heq.1,
        congrArg (fun z : X => z.1) heq.2] using hpair

private theorem crossing_step_zero :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), (G.Walk u u) → (∀ (v : X),
    let q : GaussianInt := v.1 - 1 - I
    ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a.im ≤ v.1.im) → ((b.im ≤ v.1.im) → ((if b = a +
        ⟨0, 1⟩ ∧ a.im = (q + I).im ∧ a.re ≤ (q + I).re then 1
        else if b = a - ⟨0, 1⟩ ∧ b.im = (q + I).im ∧
          a.re ≤ (q + I).re then -1 else 0) = 0))) := by
  classical
  intro S I VF JF X rel G u c v q a b ha hb
  split_ifs with hup hdown
  · have habim := congrArg Zsqrtd.im hup.1
    have haeq := hup.2.1
    simp [q, I] at habim haeq
    omega
  · have habim := congrArg Zsqrtd.im hdown.1
    have hbeq := hdown.2.1
    simp [q, I] at habim hbeq
    omega
  · rfl

private theorem htopzero :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), (c.IsCycle) → (∀ (v : X), (∀ (w : X), (w ∈ c.support) →
        (w.1.im ≤ v.1.im)) → (
    let q : GaussianInt := v.1 - 1 - I
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (path.head? = some c.snd.1) → ((path.getLast? = some u.1) → ((∀ {z : GaussianInt}, (z ∈ path)
        → (z.im ≤ v.1.im)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), (a.im ≤ v.1.im) → ((b.im
        ≤ v.1.im) → ((if b = a + ⟨0, 1⟩ ∧ a.im = (q + I).im ∧ a.re ≤ (q + I).re then 1 else if b
        = a - ⟨0, 1⟩ ∧ b.im = (q + I).im ∧ a.re ≤ (q + I).re then -1 else 0) = 0))) →
        (GridRayCrossingIndex (q + I) path = 0)))))) := by
  classical
  intro S I VF JF X rel G u c hc v hv_im_max q path path_head path_last path_vertex_im_le
      crossing_step_zero
  rw [GridRayCrossingIndex]
  dsimp only
  rw [path_last, path_head]
  have hzip (f : GaussianInt → GaussianInt → Int)
      (as bs : List GaussianInt) :
      List.zipWith f as bs = (as.zip bs).map fun e => f e.1 e.2 := by
    induction as generalizing bs with
    | nil => simp
    | cons a as ih => cases bs <;> simp [ih]
  rw [hzip]
  have hsum :
      (path.zip path.tail |>.map fun e =>
        if e.2 = e.1 + ⟨0, 1⟩ ∧ e.1.im = (q + I).im ∧
            e.1.re ≤ (q + I).re then 1
        else if e.2 = e.1 - ⟨0, 1⟩ ∧ e.2.im = (q + I).im ∧
            e.1.re ≤ (q + I).re then -1 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro n hn
    rw [List.mem_map] at hn
    rcases hn with ⟨e, he, rfl⟩
    rw [List.mem_iff_getElem] at he
    rcases he with ⟨i, hi, he⟩
    have hit : i < path.tail.length := by
      simpa [List.length_zip] using hi
    have hip : i < path.length :=
      lt_of_lt_of_le hi (by simp [List.length_zip])
    rw [List.getElem_zip, List.getElem_tail] at he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    apply crossing_step_zero
    · apply path_vertex_im_le
      simp [← he1]
    · apply path_vertex_im_le
      simp [← he2]
  rw [hsum, zero_add]
  apply crossing_step_zero
  · exact hv_im_max u (by simp)
  · exact hv_im_max c.snd
      (List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil))

private theorem htarget :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X), ∀ (hleftX : v.1 - 1 ∈ S), (c.toSubgraph.Adj v ⟨v.1
        - 1, hleftX⟩) → (
    let q : GaussianInt := v.1 - 1 - I
    let path : List GaussianInt := c.support.tail.map Subtype.val
    let cyclicEdges := path.zip path.tail ++ [(u.1, c.snd.1)]
    (∀ {x : X}, ∀ {y : X}, (c.toSubgraph.Adj x y) → ((x.1, y.1) ∈ cyclicEdges ∨ (y.1, x.1) ∈
        cyclicEdges)) → ((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ cyclicEdges ∨
        (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges)) := by
  classical
  intro S I VF JF X rel G u c v hleftX hleftEdge q path cyclicEdges cycle_edge_oriented
  have h := cycle_edge_oriented hleftEdge
  have heast : q + 1 + ⟨0, 1⟩ = v.1 := by
    ext <;> simp [q, I]
  have hnorth : q + ⟨0, 1⟩ = v.1 - 1 := by
    ext <;> simp [q, I]
  rw [heast, hnorth]
  exact h

private theorem cyclic_edge_occupied :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), (X) → (
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (3 ≤ path.length) → (
    let cyclicEdges := path.zip path.tail ++ [(u.1, c.snd.1)]
    (∀ {z : GaussianInt}, (z ∈ path) → (z ∈ S)) → (∀ {r : GaussianInt}, ∀ {s : GaussianInt}, ((r,
        s) ∈ cyclicEdges) → (r ∈ S ∧ s ∈ S)))) := by
  classical
  intro S I VF JF X rel G u c v path path_length cyclicEdges path_vertex_mem r s hrs
  rcases List.mem_append.mp hrs with hrs | hrs
  · rw [List.mem_iff_getElem] at hrs
    rcases hrs with ⟨i, hi, hrs⟩
    have hit : i < path.tail.length := by
      simpa [List.length_zip] using hi
    have hip : i < path.length :=
      lt_of_lt_of_le hi (by simp [List.length_zip])
    rw [List.getElem_zip, List.getElem_tail] at hrs
    have hrs1 := congrArg Prod.fst hrs
    have hrs2 := congrArg Prod.snd hrs
    have hip1 : i + 1 < path.length := by
      simp only [List.length_tail] at hit
      omega
    have hrs1' : path[i] = r := by simpa using hrs1
    have hrs2' : path[i + 1] = s := by simpa using hrs2
    constructor
    · apply path_vertex_mem
      rw [← hrs1']
      exact List.getElem_mem (l := path) hip
    · apply path_vertex_mem
      rw [← hrs2']
      exact List.getElem_mem (l := path) hip1
  · simp only [List.mem_singleton] at hrs
    injection hrs with hrs1 hrs2
    simpa [← hrs1, ← hrs2] using And.intro u.2 c.snd.2

private theorem index_eq_of_outside_adj :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (have cyclicEdges := path.zip path.tail ++ [((↑u : GaussianInt), (↑c.snd : GaussianInt))]; ∀
        (q : LatticeCell), ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
        cyclicEdges ∧ (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∉
        cyclicEdges → GridRayCrossingIndex (q + (1 : LatticeCell)) path = GridRayCrossingIndex q
        path) ∧ ((q + (1 : LatticeCell), q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
        cyclicEdges ∨ (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∈
        cyclicEdges → (GridRayCrossingIndex (q + (1 : LatticeCell)) path - GridRayCrossingIndex q
        path).natAbs = (1 : ℕ)) ∧ ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1
        : ℤ)⟩) ∉ cyclicEdges ∧ (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 :
        ℤ)⟩) ∉ cyclicEdges → GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) path =
        GridRayCrossingIndex q path) ∧ ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 :
        ℤ), (1 : ℤ)⟩) ∈ cyclicEdges ∨ (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell) + ⟨(0 : ℤ),
        (1 : ℤ)⟩) ∈ cyclicEdges → (GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) path -
        GridRayCrossingIndex q path).natAbs = (1 : ℕ))) → (
    let cyclicEdges := path.zip path.tail ++ [(u.1, c.snd.1)]
    (∀ {r : GaussianInt}, ∀ {s : GaussianInt}, ((r, s) ∈ cyclicEdges) → (r ∈ S ∧ s ∈ S)) → (∀
        {r : GaussianInt}, ∀ {s : GaussianInt}, (r ∉ S) → ((s ∉ S) → ((FourNeighborAdjacent r s)
        → (GridRayCrossingIndex r path = GridRayCrossingIndex s path))))) := by
  classical
  intro S I VF JF X rel G u c path index_control cyclicEdges cyclic_edge_occupied r s hr hs hrs
  rcases hrs with rfl | rfl | rfl | rfl
  · exact ((index_control r).1 ⟨
      fun he => hs (cyclic_edge_occupied he).1,
      fun he => hs (cyclic_edge_occupied he).2⟩).symm
  · have h := (index_control (r - 1)).1
      ⟨fun he => hr (by simpa [Zsqrtd.ext_iff] using
          (cyclic_edge_occupied he).1),
        fun he => hr (by simpa [Zsqrtd.ext_iff] using
          (cyclic_edge_occupied he).2)⟩
    simpa [Zsqrtd.ext_iff] using h
  · have h := (index_control r).2.2.1
      ⟨fun he => hs (cyclic_edge_occupied he).2,
        fun he => hs (cyclic_edge_occupied he).1⟩
    simpa [I, Zsqrtd.ext_iff] using h.symm
  · have h := (index_control (r - I)).2.2.1
      ⟨fun he => hr (by simpa [I, Zsqrtd.ext_iff] using
          (cyclic_edge_occupied he).2),
        fun he => hr (by simpa [I, Zsqrtd.ext_iff] using
          (cyclic_edge_occupied he).1)⟩
    simpa [I, Zsqrtd.ext_iff] using h

private theorem hqfar :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (leftmost : GaussianInt), ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X),
    let q : GaussianInt := v.1 - 1 - I
    let path : List GaussianInt := c.support.tail.map Subtype.val
    let far : GaussianInt := leftmost - 1
    ∀ (outsidePath : List LatticeCell), (outsidePath.head? = some q) → ((outsidePath.getLast? =
        some far) → ((outsidePath ≠ []) → ((List.IsChain (fun r s => GridRayCrossingIndex r path
        = GridRayCrossingIndex s path) outsidePath) → (GridRayCrossingIndex q path =
      GridRayCrossingIndex far path)))) := by
  classical
  intro S I VF JF X rel G leftmost u c v q path far outsidePath houtHead houtLast houtNe houtChain
  have hraw := List.relationReflTransGen_of_exists_isChain
    outsidePath houtChain houtNe
  have heq : outsidePath.head houtNe = q :=
    (List.head_eq_iff_head?_eq_some houtNe).2 houtHead
  have heqLast : outsidePath.getLast houtNe = far :=
    (List.getLast_eq_iff_getLast?_eq_some houtNe).2 houtLast
  let reachRel : GaussianInt → GaussianInt → Prop := fun r s =>
    GridRayCrossingIndex r path = GridRayCrossingIndex s path
  let : Std.Refl reachRel := ⟨fun _ => rfl⟩
  let : IsTrans GaussianInt reachRel :=
    ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  have h := Relation.reflTransGen_le_of_le
    (r := reachRel) (r' := reachRel) (fun _ _ h => h) _ _ hraw
  simpa [reachRel, heq, heqLast] using h

private theorem far_step_zero :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (leftmost : GaussianInt), ∀ (u : X), (G.Walk u u) → ((X) → (
    let far : GaussianInt := leftmost - 1
    ∀ (a : GaussianInt), ∀ (b : GaussianInt), (leftmost.re ≤ a.re) → ((if b = a + ⟨0, 1⟩ ∧ a.im =
        far.im ∧ a.re ≤ far.re then 1
        else if b = a - ⟨0, 1⟩ ∧ b.im = far.im ∧ a.re ≤ far.re
          then -1 else 0) = 0))) := by
  classical
  intro S I VF JF X rel G leftmost u c v far a b ha
  split_ifs with hup hdown
  · simp [far] at hup
    omega
  · simp [far] at hdown
    omega
  · rfl

private theorem hfarzero :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (leftmost : GaussianInt), (∀ x' ∈ S, leftmost.re ≤ x'.re) → (∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (path.head? = some c.snd.1) → ((path.getLast? = some u.1) → (
    let far : GaussianInt := leftmost - 1
    (∀ {z : GaussianInt}, (z ∈ path) → (leftmost.re ≤ z.re)) → ((∀ (a : GaussianInt), ∀ (b :
        GaussianInt), (leftmost.re ≤ a.re) → ((if b = a + ⟨0, 1⟩ ∧ a.im = far.im ∧ a.re ≤ far.re
        then 1 else if b = a - ⟨0, 1⟩ ∧ b.im = far.im ∧ a.re ≤ far.re then -1 else 0) = 0)) →
        (GridRayCrossingIndex far path = 0))))) := by
  classical
  intro S I VF JF X rel G leftmost hmin u c path path_head path_last far path_vertex_re_min
      far_step_zero
  rw [GridRayCrossingIndex]
  dsimp only
  rw [path_last, path_head]
  have hzip (f : GaussianInt → GaussianInt → Int)
      (as bs : List GaussianInt) :
      List.zipWith f as bs = (as.zip bs).map fun e => f e.1 e.2 := by
    induction as generalizing bs with
    | nil => simp
    | cons a as ih => cases bs <;> simp [ih]
  rw [hzip]
  have hsum :
      (path.zip path.tail |>.map fun e =>
        if e.2 = e.1 + ⟨0, 1⟩ ∧ e.1.im = far.im ∧ e.1.re ≤ far.re
          then 1
        else if e.2 = e.1 - ⟨0, 1⟩ ∧ e.2.im = far.im ∧
            e.1.re ≤ far.re then -1 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro n hn
    rw [List.mem_map] at hn
    rcases hn with ⟨e, he, rfl⟩
    apply far_step_zero
    apply path_vertex_re_min
    rw [List.mem_iff_getElem] at he
    rcases he with ⟨i, hi, he⟩
    have hip : i < path.length :=
      lt_of_lt_of_le hi (by simp [List.length_zip])
    rw [List.getElem_zip] at he
    have he1 := congrArg Prod.fst he
    simp [← he1]
  rw [hsum, zero_add]
  apply far_step_zero
  exact hmin u.1 u.2

end HorizontalRunTreeProof

namespace HorizontalRunDetails

private theorem hpartition :
    ∀ (S : Finset GaussianInt),
    let HF : Finset GaussianInt := S.filter fun z => z - 1 ∈ S
    let RF : Finset GaussianInt := S.filter fun z => z - 1 ∉ S
    S.card = HF.card + RF.card := by
  classical
  intro S HF RF
  simpa [HF, RF] using
    (Finset.card_filter_add_card_filter_not
      (s := S) (fun z => z - 1 ∈ S)).symm

private theorem graph_adj :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (a : X), ∀ (b : X), G.Adj a b ↔
      a ≠ b ∧ (rel a b ∨ rel b a) := by
  classical
  intro S I VF JF X rel G a b
  simp [G]

private theorem horizontal_adj :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ (a : X), ∀ (b : X), G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a)) → (∀ {z : GaussianInt}, ∀ (hz
        : z ∈ S), ∀ (hz1 : z + 1 ∈ S), G.Adj ⟨z, hz⟩ ⟨z + 1, hz1⟩) := by
  classical
  intro S I VF JF X rel G graph_adj z hz hz1
  rw [graph_adj]
  refine ⟨?_, Or.inl (Or.inl rfl)⟩
  intro h
  have := congrArg (fun w : X => (w.1.re : Int)) h
  simp at this

private theorem selected_vertical_adj :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ (a : X), ∀ (b : X), G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a)) → (∀ {z : GaussianInt}, ∀ (hz
        : z ∈ S), ∀ (hzI : z + I ∈ S), (z ∈ JF) → (G.Adj ⟨z, hz⟩ ⟨z + I, hzI⟩)) := by
  classical
  intro S I VF JF X rel G graph_adj z hz hzI hzJ
  rw [graph_adj]
  refine ⟨?_, Or.inl (Or.inr ⟨rfl, hzJ⟩)⟩
  intro h
  have := congrArg (fun w : X => (w.1.im : Int)) h
  simp [I] at this

private theorem hedgecard :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let HF : Finset GaussianInt := S.filter fun z => z - 1 ∈ S
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (horizontal_adj : ∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hz1 : z + 1 ∈ S), G.Adj ⟨z, hz⟩
        ⟨z + 1, hz1⟩), ∀ (selected_vertical_adj : ∀ {z : GaussianInt}, ∀ (hz : z ∈ S), ∀ (hzI : z
        + I ∈ S), (z ∈ JF) → (G.Adj ⟨z, hz⟩ ⟨z + I, hzI⟩)),
    let D := {z : GaussianInt // z ∈ HF} ⊕ {z : GaussianInt // z ∈ JF}
    let edgeOf : D → G.edgeSet := fun d => match d with
      | Sum.inl z =>
          let hz : z.1 ∈ S := (Finset.mem_filter.mp z.2).1
          let hz1 : z.1 - 1 ∈ S := (Finset.mem_filter.mp z.2).2
          ⟨s(⟨z.1 - 1, hz1⟩, ⟨z.1, hz⟩), by
            rw [SimpleGraph.mem_edgeSet]
            have h := horizontal_adj (z := z.1 - 1) hz1
              (by simpa [Zsqrtd.ext_iff] using hz)
            simpa [Zsqrtd.ext_iff] using h⟩
      | Sum.inr z =>
          let hzV : z.1 ∈ VF := (Finset.mem_filter.mp z.2).1
          let hz : z.1 ∈ S := (Finset.mem_filter.mp hzV).1
          let hzI : z.1 + I ∈ S := (Finset.mem_filter.mp hzV).2
          ⟨s(⟨z.1, hz⟩, ⟨z.1 + I, hzI⟩), by
            rw [SimpleGraph.mem_edgeSet]
            exact selected_vertical_adj hz hzI z.2⟩
    (Function.Injective edgeOf) → ((Function.Surjective edgeOf) → (Nat.card G.edgeSet = HF.card +
        JF.card)) := by
  classical
  intro S I HF VF JF X rel G horizontal_adj selected_vertical_adj D edgeOf edgeOf_injective
      edgeOf_surjective
  let e : D ≃ G.edgeSet := Equiv.ofBijective edgeOf
    ⟨edgeOf_injective, edgeOf_surjective⟩
  rw [← Nat.card_congr e]
  simp [D]

private theorem htopsne :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (top : X), (top ∈ c.support.toFinset) → (
    let tops : Finset X := c.support.toFinset.filter fun z => z.1.im = top.1.im
    tops.Nonempty) := by
  classical
  intro S I VF JF X rel G u c top htop tops
  refine ⟨top, ?_⟩
  simp [tops, htop]

private theorem hvmem :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (top : X),
    let tops : Finset X := c.support.toFinset.filter fun z => z.1.im = top.1.im
    ∀ (v : X), (v ∈ tops) → (v ∈ c.support) := by
  classical
  intro S I VF JF X rel G u c top tops v hvtop
  have := (Finset.mem_filter.mp hvtop).1
  simpa using this

private theorem hv_im_max :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (top : X), (∀ x' ∈ c.support.toFinset, (↑x' :
        GaussianInt).im ≤ (↑top : GaussianInt).im) → (
    let tops : Finset X := c.support.toFinset.filter fun z => z.1.im = top.1.im
    ∀ (v : X), (v ∈ tops) → (∀ (w : X), (w ∈ c.support) → (w.1.im ≤ v.1.im))) := by
  classical
  intro S I VF JF X rel G u c top htopmax tops v hvtop w hw
  have hvim : v.1.im = top.1.im := (Finset.mem_filter.mp hvtop).2
  rw [hvim]
  exact htopmax w (by simpa using hw)

private theorem hv_re_max :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (top : X),
    let tops : Finset X := c.support.toFinset.filter fun z => z.1.im = top.1.im
    ∀ (v : X), (v ∈ tops) → ((∀ x' ∈ tops, (↑x' : GaussianInt).re ≤ (↑v : GaussianInt).re) → (∀
        (w : X), (w ∈ c.support) → ((w.1.im = v.1.im) → (w.1.re ≤ v.1.re)))) := by
  classical
  intro S I VF JF X rel G u c top tops v hvtop hvright w hw him
  apply hvright w
  rw [Finset.mem_filter]
  refine ⟨by simpa using hw, ?_⟩
  exact him.trans (Finset.mem_filter.mp hvtop).2

private theorem haedge :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X), ∀ (a : X), ∀ (b : X), (c.toSubgraph.neighborSet v =
        {a, b}) → (c.toSubgraph.Adj v a) := by
  classical
  intro S I VF JF X rel G u c v a b hneighbors
  have : a ∈ c.toSubgraph.neighborSet v := by rw [hneighbors]; simp
  exact this

private theorem hbedge :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X), ∀ (a : X), ∀ (b : X), (c.toSubgraph.neighborSet v =
        {a, b}) → (c.toSubgraph.Adj v b) := by
  classical
  intro S I VF JF X rel G u c v a b hneighbors
  have : b ∈ c.toSubgraph.neighborSet v := by rw [hneighbors]; simp
  exact this

private theorem hpairs :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let X := {z : GaussianInt // z ∈ S}
    ∀ (v : X), ∀ (a : X), ∀ (b : X), (a ≠ b) → (((↑a : GaussianInt) = (↑v : GaussianInt) - (1 :
        GaussianInt) ∨ (↑a : GaussianInt) = (↑v : GaussianInt) - I) → (((↑b : GaussianInt) = (↑v
        : GaussianInt) - (1 : GaussianInt) ∨ (↑b : GaussianInt) = (↑v : GaussianInt) - I) → ((a.1
        = v.1 - 1 ∧ b.1 = v.1 - I) ∨
        (b.1 = v.1 - 1 ∧ a.1 = v.1 - I)))) := by
  classical
  intro S I X v a b hab haopt hbopt
  rcases haopt with ha | ha <;> rcases hbopt with hb | hb
  · exact (hab (Subtype.ext (ha.trans hb.symm))).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩
  · exact (hab (Subtype.ext (ha.trans hb.symm))).elim

private theorem hleftX :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let X := {z : GaussianInt // z ∈ S}
    ∀ (v : X), ∀ (a : X), ∀ (b : X), ((a.1 = v.1 - 1 ∧ b.1 = v.1 - I) ∨ (b.1 = v.1 - 1 ∧ a.1 =
        v.1 - I)) → (v.1 - 1 ∈ S) := by
  classical
  intro S I X v a b hpairs
  rcases hpairs with hp | hp
  · simpa [hp.1] using a.2
  · simpa [hp.1] using b.2

private theorem hdownX :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let X := {z : GaussianInt // z ∈ S}
    ∀ (v : X), ∀ (a : X), ∀ (b : X), ((a.1 = v.1 - 1 ∧ b.1 = v.1 - I) ∨ (b.1 = v.1 - 1 ∧ a.1 =
        v.1 - I)) → (v.1 - I ∈ S) := by
  classical
  intro S I X v a b hpairs
  rcases hpairs with hp | hp
  · simpa [hp.2] using b.2
  · simpa [hp.2] using a.2

private theorem hleftEdge :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X), ∀ (a : X), ∀ (b : X), (c.toSubgraph.Adj v a) →
        ((c.toSubgraph.Adj v b) → (((a.1 = v.1 - 1 ∧ b.1 = v.1 - I) ∨ (b.1 = v.1 - 1 ∧ a.1 = v.1
        - I)) → (∀ (hleftX : v.1 - 1 ∈ S), c.toSubgraph.Adj v ⟨v.1 - 1, hleftX⟩))) := by
  classical
  intro S I VF JF X rel G u c v a b haedge hbedge hpairs hleftX
  rcases hpairs with hp | hp
  · convert haedge using 1; apply Subtype.ext; simp [hp.1]
  · convert hbedge using 1; apply Subtype.ext; simp [hp.1]

private theorem hdownEdge :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X), ∀ (a : X), ∀ (b : X), (c.toSubgraph.Adj v a) →
        ((c.toSubgraph.Adj v b) → (((a.1 = v.1 - 1 ∧ b.1 = v.1 - I) ∨ (b.1 = v.1 - 1 ∧ a.1 = v.1
        - I)) → (∀ (hdownX : v.1 - I ∈ S), c.toSubgraph.Adj v ⟨v.1 - I, hdownX⟩))) := by
  classical
  intro S I VF JF X rel G u c v a b haedge hbedge hpairs hdownX
  rcases hpairs with hp | hp
  · convert hbedge using 1; apply Subtype.ext; simp [hp.2]
  · convert haedge using 1; apply Subtype.ext; simp [hp.2]

private theorem hqout :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    ∀ (v : X), (v.1 - 1 ∈ S) → ((v.1 - I ∈ JF) → (
    let q : GaussianInt := v.1 - 1 - I
    q ∉ S)) := by
  classical
  intro S I VF JF X v hleftX hdownJ q hq
  have hnot := (Finset.mem_filter.mp hdownJ).2
  apply hnot
  constructor
  · simpa [q, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hq
  · convert hleftX using 1; ext <;> simp [I]

private theorem graph_adj_four :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    (∀ (a : X), ∀ (b : X), G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a)) → (∀ (a : X), ∀ (b : X),
        (G.Adj a b) → (FourNeighborAdjacent a.1 b.1)) := by
  classical
  intro S I VF JF X rel G graph_adj a b hab
  rw [graph_adj] at hab
  rcases hab.2 with h | h <;> rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inl (by rw [h]; ext <;> simp))
  · exact Or.inr (Or.inr (Or.inr (by rw [h.1]; ext <;> simp [I])))

private theorem path_head :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (3 ≤ path.length) → (path.head? = some c.snd.1) := by
  classical
  intro S I VF JF X rel G u c path path_length
  have hlen : 1 < c.support.length := by
    simp only [path, List.length_map, List.length_tail] at path_length
    omega
  simp only [path, List.head?_map, List.head?_tail]
  rw [List.getElem?_eq_getElem hlen, c.support_getElem_one]
  rfl

private theorem path_last :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (3 ≤ path.length) → (path.getLast? = some u.1) := by
  classical
  intro S I VF JF X rel G u c path path_length
  have hlen : c.support.length ≠ 1 := by
    simp only [path, List.length_map, List.length_tail] at path_length
    omega
  simp only [path, List.getLast?_map, List.getLast?_tail, hlen, ite_false]
  rw [List.getLast?_eq_getLast_of_ne_nil c.support_ne_nil,
    c.getLast_support]
  rfl

private theorem path_chain :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), (∀ (a : X), ∀ (b : X), (G.Adj a b) → (FourNeighborAdjacent a.1
        b.1)) → (
    let path : List GaussianInt := c.support.tail.map Subtype.val
    List.IsChain FourNeighborAdjacent path) := by
  classical
  intro S I VF JF X rel G u c graph_adj_four path
  change List.IsChain FourNeighborAdjacent
    (c.support.tail.map Subtype.val)
  rw [List.isChain_map]
  exact c.isChain_adj_support.tail.imp fun _ _ h => graph_adj_four _ _ h

private theorem path_vertex_im_le :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X), (∀ (w : X), (w ∈ c.support) → (w.1.im ≤ v.1.im)) → (
    let path : List GaussianInt := c.support.tail.map Subtype.val
    ∀ {z : GaussianInt}, (z ∈ path) → (z.im ≤ v.1.im)) := by
  classical
  intro S I VF JF X rel G u c v hv_im_max path z hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  exact hv_im_max w (List.mem_of_mem_tail hw)

private theorem hqnonzero :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u), ∀ (v : X),
    let q : GaussianInt := v.1 - 1 - I
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (GridRayCrossingIndex (q + I) path = 0) → (((GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩)
        path - GridRayCrossingIndex q path).natAbs = (1 : ℕ)) → (GridRayCrossingIndex q path ≠
        0)) := by
  classical
  intro S I VF JF X rel G u c v q path htopzero hjump
  rw [htopzero] at hjump
  omega

private theorem path_vertex_mem :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    ∀ {z : GaussianInt}, (z ∈ path) → (z ∈ S) := by
  classical
  intro S I VF JF X rel G u c path z hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  exact w.2

private theorem hfarout :
    ∀ (S : Finset GaussianInt), ∀ (leftmost : GaussianInt), (∀ x' ∈ S, leftmost.re ≤ x'.re) → (
    let far : GaussianInt := leftmost - 1
    far ∉ S) := by
  classical
  intro S leftmost hmin far hfar
  have h := hmin far hfar
  simp [far] at h

private theorem houtNe :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let X := {z : GaussianInt // z ∈ S}
    ∀ (v : X),
    let q : GaussianInt := v.1 - 1 - I
    ∀ (outsidePath : List LatticeCell), (outsidePath.head? = some q) → (outsidePath ≠ []) := by
  classical
  intro S I X v q outsidePath houtHead h
  simp [h] at houtHead

private theorem houtChain :
    ∀ (S : Finset GaussianInt),
    let I : GaussianInt := ⟨0, 1⟩
    let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
    let JF : Finset GaussianInt := VF.filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
    let X := {z : GaussianInt // z ∈ S}
    let rel : X → X → Prop := fun a b =>
      b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
    let G : SimpleGraph X := SimpleGraph.fromRel rel
    ∀ (u : X), ∀ (c : G.Walk u u),
    let path : List GaussianInt := c.support.tail.map Subtype.val
    (∀ {r : GaussianInt}, ∀ {s : GaussianInt}, (r ∉ S) → ((s ∉ S) → ((FourNeighborAdjacent r s) →
        (GridRayCrossingIndex r path = GridRayCrossingIndex s path)))) → (∀ (outsidePath : List
        LatticeCell), (∀ z ∈ outsidePath, z ∈ (↑S : Set LatticeCell)ᶜ) → ((∀ (a : LatticeCell), ∀
        (b : LatticeCell), ∀ (l₁ : List LatticeCell), ∀ (l₂ : List LatticeCell), outsidePath = l₁
        ++ a :: b :: l₂ → FourNeighborAdjacent a b) → (List.IsChain (fun r s =>
      GridRayCrossingIndex r path = GridRayCrossingIndex s path) outsidePath))) := by
  classical
  intro S I VF JF X rel G u c path index_eq_of_outside_adj outsidePath houtMem houtAdj
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro r s l₁ l₂ heq
  apply index_eq_of_outside_adj
  · exact houtMem r (by rw [heq]; simp)
  · exact houtMem s (by rw [heq]; simp)
  · exact houtAdj r s l₁ l₂ heq

end HorizontalRunDetails

theorem FiniteBiconnectedHorizontalRunTree (S : Finset GaussianInt)
    (hinside : FourNeighborConnected (S : Set LatticeCell))
    (houtside : FourNeighborConnected ((S : Set LatticeCell)ᶜ)) :
    let I : GaussianInt := ⟨0, 1⟩
    let R := (S.filter fun z => z - 1 ∉ S).card
    let J := ((S.filter fun z => z + I ∈ S).filter fun z =>
      ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)).card
    R = J + 1 := by
-- BODY
  classical
  dsimp only
  let I : GaussianInt := ⟨0, 1⟩
  let HF : Finset GaussianInt := S.filter fun z => z - 1 ∈ S
  let RF : Finset GaussianInt := S.filter fun z => z - 1 ∉ S
  let VF : Finset GaussianInt := S.filter fun z => z + I ∈ S
  let JF : Finset GaussianInt := VF.filter fun z =>
    ¬ (z - 1 ∈ S ∧ z - 1 + I ∈ S)
  have hpartition : S.card = HF.card + RF.card := HorizontalRunDetails.hpartition S
  let X := {z : GaussianInt // z ∈ S}
  let rel : X → X → Prop := fun a b =>
    b.1 = a.1 + 1 ∨ (b.1 = a.1 + I ∧ a.1 ∈ JF)
  let G : SimpleGraph X := SimpleGraph.fromRel rel
  have graph_adj (a b : X) : G.Adj a b ↔
      a ≠ b ∧ (rel a b ∨ rel b a) := HorizontalRunDetails.graph_adj S a b
  have horizontal_adj {z : GaussianInt} (hz : z ∈ S) (hz1 : z + 1 ∈ S) :
      G.Adj ⟨z, hz⟩ ⟨z + 1, hz1⟩ := HorizontalRunDetails.horizontal_adj S graph_adj (z := z) hz hz1
  have selected_vertical_adj {z : GaussianInt} (hz : z ∈ S)
      (hzI : z + I ∈ S) (hzJ : z ∈ JF) :
      G.Adj ⟨z, hz⟩ ⟨z + I, hzI⟩ := HorizontalRunDetails.selected_vertical_adj S graph_adj (z :=
          z) hz hzI hzJ
  let D := {z : GaussianInt // z ∈ HF} ⊕ {z : GaussianInt // z ∈ JF}
  let edgeOf : D → G.edgeSet := fun d => match d with
    | Sum.inl z =>
        let hz : z.1 ∈ S := (Finset.mem_filter.mp z.2).1
        let hz1 : z.1 - 1 ∈ S := (Finset.mem_filter.mp z.2).2
        ⟨s(⟨z.1 - 1, hz1⟩, ⟨z.1, hz⟩), by
          rw [SimpleGraph.mem_edgeSet]
          have h := horizontal_adj (z := z.1 - 1) hz1
            (by simpa [Zsqrtd.ext_iff] using hz)
          simpa [Zsqrtd.ext_iff] using h⟩
    | Sum.inr z =>
        let hzV : z.1 ∈ VF := (Finset.mem_filter.mp z.2).1
        let hz : z.1 ∈ S := (Finset.mem_filter.mp hzV).1
        let hzI : z.1 + I ∈ S := (Finset.mem_filter.mp hzV).2
        ⟨s(⟨z.1, hz⟩, ⟨z.1 + I, hzI⟩), by
          rw [SimpleGraph.mem_edgeSet]
          exact selected_vertical_adj hz hzI z.2⟩
  have edgeOf_injective : Function.Injective edgeOf := HorizontalRunTreeProof.edgeOf_injective S
      horizontal_adj selected_vertical_adj
  have edgeOf_surjective : Function.Surjective edgeOf := HorizontalRunTreeProof.edgeOf_surjective
      S graph_adj horizontal_adj selected_vertical_adj
  have hedgecard : Nat.card G.edgeSet = HF.card + JF.card := HorizontalRunDetails.hedgecard S
      horizontal_adj selected_vertical_adj edgeOf_injective edgeOf_surjective
  rcases hinside.1 with ⟨base, hbase⟩
  rcases Finset.exists_min_image S (fun z : GaussianInt => z.re)
      ⟨base, hbase⟩ with ⟨leftmost, hleftmost, hmin⟩
  have vertical_reachable : ∀ (z : GaussianInt) (hz : z ∈ S)
      (hzI : z + I ∈ S), G.Reachable ⟨z, hz⟩ ⟨z + I, hzI⟩ :=
          HorizontalRunTreeProof.vertical_reachable S horizontal_adj selected_vertical_adj
          leftmost hmin
  have four_reachable {a b : GaussianInt} (ha : a ∈ S) (hb : b ∈ S)
      (hab : FourNeighborAdjacent a b) : G.Reachable ⟨a, ha⟩ ⟨b, hb⟩ :=
          HorizontalRunTreeProof.four_reachable S horizontal_adj vertical_reachable (a := a) (b
          := b) ha hb hab
  have hconnected : G.Connected := HorizontalRunTreeProof.hconnected S hinside base hbase
      four_reachable
  have hacyclic : G.IsAcyclic := by
    intro u c hc
    have hsuppne : c.support.toFinset.Nonempty := by
      exact ⟨u, by simp⟩
    obtain ⟨top, htop, htopmax⟩ :=
      Finset.exists_max_image c.support.toFinset (fun z : X => z.1.im) hsuppne
    let tops : Finset X := c.support.toFinset.filter fun z => z.1.im = top.1.im
    have htopsne : tops.Nonempty := HorizontalRunDetails.htopsne S u c top htop
    obtain ⟨v, hvtop, hvright⟩ :=
      Finset.exists_max_image tops (fun z : X => z.1.re) htopsne
    have hvmem : v ∈ c.support := HorizontalRunDetails.hvmem S u c top v hvtop
    have hv_im_max (w : X) (hw : w ∈ c.support) : w.1.im ≤ v.1.im :=
        HorizontalRunDetails.hv_im_max S u c top htopmax v hvtop w hw
    have hv_re_max (w : X) (hw : w ∈ c.support)
        (him : w.1.im = v.1.im) : w.1.re ≤ v.1.re := HorizontalRunDetails.hv_re_max S u c top v
            hvtop hvright w hw him
    have neighbor_options (w : X) (hvw : c.toSubgraph.Adj v w) :
        w.1 = v.1 - 1 ∨ w.1 = v.1 - I := HorizontalRunTreeProof.neighbor_options S graph_adj u c
            v hv_im_max hv_re_max w hvw
    obtain ⟨a, b, hab, hneighbors⟩ := Set.ncard_eq_two.mp
      (hc.ncard_neighborSet_toSubgraph_eq_two hvmem)
    have haedge : c.toSubgraph.Adj v a := HorizontalRunDetails.haedge S u c v a b hneighbors
    have hbedge : c.toSubgraph.Adj v b := HorizontalRunDetails.hbedge S u c v a b hneighbors
    have haopt := neighbor_options a haedge
    have hbopt := neighbor_options b hbedge
    have hpairs :
        (a.1 = v.1 - 1 ∧ b.1 = v.1 - I) ∨
          (b.1 = v.1 - 1 ∧ a.1 = v.1 - I) := HorizontalRunDetails.hpairs S v a b hab haopt hbopt
    have hleftX : v.1 - 1 ∈ S := HorizontalRunDetails.hleftX S v a b hpairs
    have hdownX : v.1 - I ∈ S := HorizontalRunDetails.hdownX S v a b hpairs
    have hleftEdge : c.toSubgraph.Adj v ⟨v.1 - 1, hleftX⟩ := HorizontalRunDetails.hleftEdge S u c
        v a b haedge hbedge hpairs hleftX
    have hdownEdge : c.toSubgraph.Adj v ⟨v.1 - I, hdownX⟩ := HorizontalRunDetails.hdownEdge S u c
        v a b haedge hbedge hpairs hdownX
    have hdownJ : v.1 - I ∈ JF := HorizontalRunTreeProof.hdownJ S graph_adj u c v hdownX hdownEdge
    let q : GaussianInt := v.1 - 1 - I
    have hqout : q ∉ S := HorizontalRunDetails.hqout S v hleftX hdownJ
    have graph_adj_four (a b : X) (hab : G.Adj a b) :
        FourNeighborAdjacent a.1 b.1 := HorizontalRunDetails.graph_adj_four S graph_adj a b hab
    let path : List GaussianInt := c.support.tail.map Subtype.val
    have path_nodup : path.Nodup :=
      hc.support_nodup.map Subtype.val_injective
    have path_length : 3 ≤ path.length := by
      simpa [path] using hc.three_le_length
    have path_head : path.head? = some c.snd.1 := HorizontalRunDetails.path_head S u c path_length
    have path_last : path.getLast? = some u.1 := HorizontalRunDetails.path_last S u c path_length
    have path_chain : List.IsChain FourNeighborAdjacent path := HorizontalRunDetails.path_chain S
        u c graph_adj_four
    have path_close : FourNeighborAdjacent u.1 c.snd.1 := by
      exact graph_adj_four _ _ (c.adj_snd hc.not_nil)
    have path_zip : ∀ a b, (a, b) ∈ path.zip path.tail →
        FourNeighborAdjacent a b := HorizontalRunTreeProof.path_zip S u c path_length path_chain
    have index_control := GridRayCrossingIndexAdjacentCell path c.snd.1 u.1
      path_head path_last path_nodup path_length path_zip path_close
    let cyclicEdges := path.zip path.tail ++ [(u.1, c.snd.1)]
    have cycle_edge_oriented {x y : X} (hxy : c.toSubgraph.Adj x y) :
        (x.1, y.1) ∈ cyclicEdges ∨ (y.1, x.1) ∈ cyclicEdges :=
            HorizontalRunTreeProof.cycle_edge_oriented S u c (x := x) (y := y) hxy
    have path_vertex_im_le {z : GaussianInt} (hz : z ∈ path) :
        z.im ≤ v.1.im := HorizontalRunDetails.path_vertex_im_le S u c v hv_im_max (z := z) hz
    have crossing_step_zero (a b : GaussianInt)
        (ha : a.im ≤ v.1.im) (hb : b.im ≤ v.1.im) :
        (if b = a + ⟨0, 1⟩ ∧ a.im = (q + I).im ∧ a.re ≤ (q + I).re then 1
          else if b = a - ⟨0, 1⟩ ∧ b.im = (q + I).im ∧
            a.re ≤ (q + I).re then -1 else 0) = 0 := HorizontalRunTreeProof.crossing_step_zero S
                u c v a b ha hb
    have htopzero : GridRayCrossingIndex (q + I) path = 0 := HorizontalRunTreeProof.htopzero S u
        c hc v hv_im_max path_head path_last path_vertex_im_le crossing_step_zero
    have htarget :
        (q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ cyclicEdges ∨
          (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges := HorizontalRunTreeProof.htarget S u c v
              hleftX hleftEdge cycle_edge_oriented
    have hjump := (index_control q).2.2.2 htarget
    have hqnonzero : GridRayCrossingIndex q path ≠ 0 := HorizontalRunDetails.hqnonzero S u c v
        htopzero hjump
    have path_vertex_mem {z : GaussianInt} (hz : z ∈ path) : z ∈ S :=
        HorizontalRunDetails.path_vertex_mem S u c (z := z) hz
    have cyclic_edge_occupied {r s : GaussianInt}
        (hrs : (r, s) ∈ cyclicEdges) : r ∈ S ∧ s ∈ S :=
            HorizontalRunTreeProof.cyclic_edge_occupied S u c v path_length path_vertex_mem (r :=
            r) (s := s) hrs
    have index_eq_of_outside_adj {r s : GaussianInt}
        (hr : r ∉ S) (hs : s ∉ S) (hrs : FourNeighborAdjacent r s) :
        GridRayCrossingIndex r path = GridRayCrossingIndex s path :=
            HorizontalRunTreeProof.index_eq_of_outside_adj S u c index_control
            cyclic_edge_occupied (r := r) (s := s) hr hs hrs
    let far : GaussianInt := leftmost - 1
    have hfarout : far ∉ S := HorizontalRunDetails.hfarout S leftmost hmin
    obtain ⟨outsidePath, houtHead, houtLast, houtMem, houtAdj⟩ :=
      houtside.2 q (by simpa using hqout) far (by simpa using hfarout)
    have houtNe : outsidePath ≠ [] := HorizontalRunDetails.houtNe S v outsidePath houtHead
    have houtChain : List.IsChain (fun r s =>
        GridRayCrossingIndex r path = GridRayCrossingIndex s path) outsidePath :=
            HorizontalRunDetails.houtChain S u c index_eq_of_outside_adj outsidePath houtMem houtAdj
    have hqfar : GridRayCrossingIndex q path =
        GridRayCrossingIndex far path := HorizontalRunTreeProof.hqfar S leftmost u c v
            outsidePath houtHead houtLast houtNe houtChain
    have path_vertex_re_min {z : GaussianInt} (hz : z ∈ path) :
        leftmost.re ≤ z.re := hmin z (path_vertex_mem hz)
    have far_step_zero (a b : GaussianInt) (ha : leftmost.re ≤ a.re) :
        (if b = a + ⟨0, 1⟩ ∧ a.im = far.im ∧ a.re ≤ far.re then 1
          else if b = a - ⟨0, 1⟩ ∧ b.im = far.im ∧ a.re ≤ far.re
            then -1 else 0) = 0 := HorizontalRunTreeProof.far_step_zero S leftmost u c v a b ha
    have hfarzero : GridRayCrossingIndex far path = 0 := HorizontalRunTreeProof.hfarzero S
        leftmost hmin u c path_head path_last path_vertex_re_min far_step_zero
    exact hqnonzero (hqfar.trans hfarzero)
  have htree : G.IsTree := ⟨hconnected, hacyclic⟩
  have hcard := htree.card_edgeFinset
  have hedgecard' : Fintype.card G.edgeSet = HF.card + JF.card := by
    simpa [Nat.card_eq_fintype_card] using hedgecard
  rw [SimpleGraph.edgeFinset_card, hedgecard'] at hcard
  have hvertexcard : Fintype.card X = S.card := by simp [X]
  rw [hvertexcard] at hcard
  change RF.card = JF.card + 1
  omega

end ApollonianSuperharmonic

end
