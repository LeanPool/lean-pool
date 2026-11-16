/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildren
public import LeanPool.ApollonianSuperharmonic.P3544T1LocalParity
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P3650T1LocalCoherence]

/-!
# P3650T1LocalCoherence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LocalCoherenceProof

private theorem hOL_Cp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), (Disjoint (P3544T1BoundaryCarrier
            C.right \ segment ℝ (p.vertex a) (p.vertex b)) (P3544T1RayParity C.left)) → (
        let Cp := P3544T1BoundaryCarrier p
        let OL := P3544T1RayParity C.left
        Disjoint OL Cp) ) := by
  classical
  intro n p a b C hright Cp OL
  let CL := P3544T1BoundaryCarrier C.left
  let CR := P3544T1BoundaryCarrier C.right
  let e := segment Real (p.vertex a) (p.vertex b)
  apply Set.disjoint_left.mpr
  intro x hxL hxP
  have hxU : x ∈ CL ∪ CR ∪ e := by
    rw [C.carrier_union]
    exact Or.inl (Or.inl hxP)
  rcases hxU with hxCC | hxe
  · rcases hxCC with hxCL | hxCR
    · exact hxL.1 hxCL
    · have hxDiff : x ∈ CR \ e := ⟨hxCR, fun hxe => by
          have hxCL' : x ∈ CL := by
            have hsub : e ⊆ CL := by
              intro y hy
              have hy' : y ∈ CL ∩ CR := by
                rw [C.carrier_intersection]
                exact hy
              exact hy'.1
            exact hsub hxe
          exact hxL.1 hxCL'⟩
      exact (Set.disjoint_left.mp hright) hxDiff hxL
  · have hxCL : x ∈ CL := by
      have hsub : e ⊆ CL := by
        intro y hy
        have hy' : y ∈ CL ∩ CR := by
          rw [C.carrier_intersection]
          exact hy
        exact hy'.1
      exact hsub hxe
    exact hxL.1 hxCL

private theorem hOR_Cp :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), (Disjoint (P3544T1BoundaryCarrier
            C.left \ segment ℝ (p.vertex a) (p.vertex b)) (P3544T1RayParity C.right)) → (
        let Cp := P3544T1BoundaryCarrier p
        let OR := P3544T1RayParity C.right
        Disjoint OR Cp) ) := by
  classical
  intro n p a b C hleft Cp OR
  let CL := P3544T1BoundaryCarrier C.left
  let CR := P3544T1BoundaryCarrier C.right
  let e := segment Real (p.vertex a) (p.vertex b)
  apply Set.disjoint_left.mpr
  intro x hxR hxP
  have hxU : x ∈ CL ∪ CR ∪ e := by
    rw [C.carrier_union]
    exact Or.inl (Or.inl hxP)
  rcases hxU with hxCC | hxe
  · rcases hxCC with hxCL | hxCR
    · have hxDiff : x ∈ CL \ e := ⟨hxCL, fun hxe => by
        have hxCR : x ∈ CR := by
          have hsub : e ⊆ CR := by
            intro y hy
            have hy' : y ∈ CL ∩ CR := by
              rw [C.carrier_intersection]
              exact hy
            exact hy'.2
          exact hsub hxe
        exact hxR.1 hxCR⟩
      exact (Set.disjoint_left.mp hleft) hxDiff hxR
    · exact hxR.1 hxCR
  · have hxCR : x ∈ CR := by
      have hsub : e ⊆ CR := by
        intro y hy
        have hy' : y ∈ CL ∩ CR := by
          rw [C.carrier_intersection]
          exact hy
        exact hy'.2
      exact hsub hxe
    exact hxR.1 hxCR

private theorem hpropagate :
    (by
      classical
      exact
        ∀ (O : Set (ℝ × ℝ)), ∀ (K : Set (ℝ × ℝ)), closure O = O ∪ K → IsOpen O → ∀ (S : Set (ℝ ×
            ℝ)), IsPreconnected S → Disjoint S K → (S ∩ O).Nonempty → S ⊆ O ) := by
  classical
  intro O K hclosure hopen S hpre hdisj hseed
  have houtside : IsOpen (closure O)ᶜ := isClosed_closure.isOpen_compl
  have hdisjoint' : Disjoint O (closure O)ᶜ := by
    apply Set.disjoint_left.mpr
    intro x hxO hxoutside
    exact hxoutside (subset_closure hxO)
  have hsplit := hpre.subset_or_subset hopen houtside hdisjoint' (by
    intro x hx
    by_cases hxO : x ∈ O
    · exact Or.inl hxO
    · exact Or.inr (by
        intro hxcl
        have hxOK : x ∈ O ∪ K := by simpa only [hclosure] using hxcl
        rcases hxOK with hxO' | hxK
        · exact hxO hxO'
        · exact (Set.disjoint_left.mp hdisj) hx hxK))
  rcases hseed with ⟨x, hxS, hxO⟩
  rcases hsplit with hS | hS
  · exact hS
  · exact False.elim ((hS hxS) (subset_closure hxO))

private theorem hzclosure :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (z : ℝ × ℝ), (z = p.vertex a ∨ z = p.vertex b) → (z ∈ closure (openSegment
            Real (p.vertex a) (p.vertex b))) ) := by
  classical
  intro n p a b z hzab
  rcases hzab with hza | hzb
  · rw [hza]
    exact segment_subset_closure_openSegment (left_mem_segment Real _ _)
  · rw [hzb, openSegment_symm]
    exact segment_subset_closure_openSegment (left_mem_segment Real _ _)

private theorem hidxL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), ∀ t : Fin (n + 3), t ∈ ({a, b} : Set (Fin
            (n + 3))) → ∃ i : Fin (C.leftParameter + 3), C.left.vertex i = p.vertex t ) := by
  classical
  intro n p a b C t ht
  have ht' : t ∈ Set.range C.il ∩ Set.range C.ir := by
    rw [C.common_indices]
    simpa using ht
  obtain ⟨i, hi⟩ := Set.mem_range.mp ht'.1
  refine ⟨i, ?_⟩
  rw [C.left_vertex]
  simp [hi]

private theorem hidxR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), ∀ t : Fin (n + 3), t ∈ ({a, b} : Set (Fin
            (n + 3))) → ∃ i : Fin (C.rightParameter + 3), C.right.vertex i = p.vertex t ) := by
  classical
  intro n p a b C t ht
  have ht' : t ∈ Set.range C.il ∩ Set.range C.ir := by
    rw [C.common_indices]
    simpa using ht
  obtain ⟨i, hi⟩ := Set.mem_range.mp ht'.2
  refine ⟨i, ?_⟩
  rw [C.right_vertex]
  simp [hi]

private theorem hidxLz :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), ∀ (z : ℝ × ℝ), (z = p.vertex a ∨ z =
            p.vertex b) → ((∀ t : Fin (n + 3), t ∈ ({a, b} : Set (Fin (n + 3))) → ∃ i : Fin
            (C.leftParameter + 3), C.left.vertex i = p.vertex t) → (∃ i : Fin (C.leftParameter + 3),
            C.left.vertex i = z)) ) := by
  classical
  intro n p a b C z hzab hidxL
  rcases hzab with hza | hzb
  · obtain ⟨i, hi⟩ := hidxL a (by simp)
    exact ⟨i, hi.trans hza.symm⟩
  · obtain ⟨i, hi⟩ := hidxL b (by simp)
    exact ⟨i, hi.trans hzb.symm⟩

private theorem hidxRz :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), ∀ (z : ℝ × ℝ), (z = p.vertex a ∨ z =
            p.vertex b) → ((∀ t : Fin (n + 3), t ∈ ({a, b} : Set (Fin (n + 3))) → ∃ i : Fin
            (C.rightParameter + 3), C.right.vertex i = p.vertex t) → (∃ i : Fin (C.rightParameter
                + 3),
            C.right.vertex i = z)) ) := by
  classical
  intro n p a b C z hzab hidxR
  rcases hzab with hza | hzb
  · obtain ⟨i, hi⟩ := hidxR a (by simp)
    exact ⟨i, hi.trans hza.symm⟩
  · obtain ⟨i, hi⟩ := hidxR b (by simp)
    exact ⟨i, hi.trans hzb.symm⟩

private theorem hseedL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), (openSegment ℝ (p.vertex a) (p.vertex b)
            ⊆ P3544T1RayParity p) → (
        let CL := P3544T1BoundaryCarrier C.left
        let Op := P3544T1RayParity p
        let OL := P3544T1RayParity C.left
        ∀ (z : ℝ × ℝ), (z ∈ closure (openSegment Real (p.vertex a) (p.vertex b))) → (∀ (rL : ℝ),
            ((0 : ℝ) < rL) → ((IsOpen Op) → ((closure OL = OL ∪ CL) → (((Metric.ball z rL ∩ OL) ∩
            Op).Nonempty))))) ) := by
  classical
  intro n p a b C hodd CL Op OL z hzclosure rL hrL hopenP hclosureL
  let CR := P3544T1BoundaryCarrier C.right
  let e := segment Real (p.vertex a) (p.vertex b)
  obtain ⟨x, hx⟩ := (mem_closure_iff_nhds.mp hzclosure)
    (Metric.ball z rL) (Metric.ball_mem_nhds z hrL)
  have hxseg : x ∈ openSegment Real (p.vertex a) (p.vertex b) := hx.2
  have hxop : x ∈ Op := hodd hxseg
  have hxCL : x ∈ CL := by
    have hxe : x ∈ e := openSegment_subset_segment Real (p.vertex a) (p.vertex b) hxseg
    have hboth : x ∈ CL ∩ CR := by
      rw [C.carrier_intersection]
      exact hxe
    exact hboth.1
  have hxclosure : x ∈ closure OL := by
    rw [hclosureL]
    exact Or.inr hxCL
  have hopenN : IsOpen (Metric.ball z rL ∩ Op) := Metric.isOpen_ball.inter hopenP
  obtain ⟨y, hy, hyL⟩ := (mem_closure_iff_nhds.mp hxclosure)
    (Metric.ball z rL ∩ Op) (hopenN.mem_nhds ⟨hx.1, hxop⟩)
  exact ⟨y, ⟨hy.1, hyL⟩, hy.2⟩

private theorem hseedR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), (openSegment ℝ (p.vertex a) (p.vertex b)
            ⊆ P3544T1RayParity p) → (
        let CR := P3544T1BoundaryCarrier C.right
        let Op := P3544T1RayParity p
        let OR := P3544T1RayParity C.right
        ∀ (z : ℝ × ℝ), (z ∈ closure (openSegment Real (p.vertex a) (p.vertex b))) → (∀ (rR : ℝ),
            ((0 : ℝ) < rR) → ((IsOpen Op) → ((closure OR = OR ∪ CR) → (((Metric.ball z rR ∩ OR) ∩
            Op).Nonempty))))) ) := by
  classical
  intro n p a b C hodd CR Op OR z hzclosure rR hrR hopenP hclosureR
  let CL := P3544T1BoundaryCarrier C.left
  let e := segment Real (p.vertex a) (p.vertex b)
  obtain ⟨x, hx⟩ := (mem_closure_iff_nhds.mp hzclosure)
    (Metric.ball z rR) (Metric.ball_mem_nhds z hrR)
  have hxseg : x ∈ openSegment Real (p.vertex a) (p.vertex b) := hx.2
  have hxop : x ∈ Op := hodd hxseg
  have hxCR : x ∈ CR := by
    have hxe : x ∈ e := openSegment_subset_segment Real (p.vertex a) (p.vertex b) hxseg
    have hboth : x ∈ CL ∩ CR := by
      rw [C.carrier_intersection]
      exact hxe
    exact hboth.2
  have hxclosure : x ∈ closure OR := by
    rw [hclosureR]
    exact Or.inr hxCR
  have hopenN : IsOpen (Metric.ball z rR ∩ Op) := Metric.isOpen_ball.inter hopenP
  obtain ⟨y, hy, hyR⟩ := (mem_closure_iff_nhds.mp hxclosure)
    (Metric.ball z rR ∩ Op) (hopenN.mem_nhds ⟨hx.1, hxop⟩)
  exact ⟨y, ⟨hy.1, hyR⟩, hy.2⟩

private theorem hOLin :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let Cp := P3544T1BoundaryCarrier p
        let Op := P3544T1RayParity p
        let OL := P3544T1RayParity C.left
        (Disjoint OL Cp) → ((∀ (O : Set (Real × Real)), ∀ (K : Set (Real × Real)), (closure O = O
            ∪ K) → ((IsOpen O) → (∀ (S : Set (Real × Real)), (IsPreconnected S) → ((Disjoint S K)
            → (((S ∩ O).Nonempty) → (S ⊆ O)))))) → (∀ (z : ℝ × ℝ), ∀ (iL : Fin (C.leftParameter +
                (3 :
            ℕ))), (C.left.vertex iL = z) → (∀ (rL : ℝ), (IsPathConnected (Metric.ball
            (C.left.vertex iL) rL ∩ P3544T1RayParity C.left)) → ((IsOpen Op) → ((closure Op =
            Op ∪ Cp) → ((((Metric.ball z rL ∩ OL) ∩ Op).Nonempty) → (Metric.ball z rL ∩ OL ⊆
            Op))))))) ) := by
  classical
  intro n p a b C Cp Op OL hOL_Cp hpropagate z iL hiL rL hpathL hopenP hclosureP hseedL
  apply hpropagate Op Cp hclosureP hopenP (Metric.ball z rL ∩ OL)
  · have hpathLz : IsPathConnected (Metric.ball z rL ∩ OL) := by
      simpa [OL, hiL] using hpathL
    exact hpathLz.isConnected.isPreconnected
  · apply Set.disjoint_left.mpr
    intro x hx hc
    exact (Set.disjoint_left.mp hOL_Cp) hx.2 hc
  · exact hseedL

private theorem hORin :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let Cp := P3544T1BoundaryCarrier p
        let Op := P3544T1RayParity p
        let OR := P3544T1RayParity C.right
        (Disjoint OR Cp) → ((∀ (O : Set (Real × Real)), ∀ (K : Set (Real × Real)), (closure O = O
            ∪ K) → ((IsOpen O) → (∀ (S : Set (Real × Real)), (IsPreconnected S) → ((Disjoint S K)
            → (((S ∩ O).Nonempty) → (S ⊆ O)))))) → (∀ (z : ℝ × ℝ), ∀ (iR : Fin (C.rightParameter
                + (3 :
            ℕ))), (C.right.vertex iR = z) → (∀ (rR : ℝ), (IsPathConnected (Metric.ball
            (C.right.vertex iR) rR ∩ P3544T1RayParity C.right)) → ((IsOpen Op) → ((closure Op =
            Op ∪ Cp) → ((((Metric.ball z rR ∩ OR) ∩ Op).Nonempty) → (Metric.ball z rR ∩ OR ⊆
            Op))))))) ) := by
  classical
  intro n p a b C Cp Op OR hOR_Cp hpropagate z iR hiR rR hpathR hopenP hclosureP hseedR
  apply hpropagate Op Cp hclosureP hopenP (Metric.ball z rR ∩ OR)
  · have hpathRz : IsPathConnected (Metric.ball z rR ∩ OR) := by
      simpa [OR, hiR] using hpathR
    exact hpathRz.isConnected.isPreconnected
  · apply Set.disjoint_left.mpr
    intro x hx hc
    exact (Set.disjoint_left.mp hOR_Cp) hx.2 hc
  · exact hseedR

private theorem hnotA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)),
        let Cp := P3544T1BoundaryCarrier p
        ∀ (y : ℝ × ℝ), (y ∉ Cp) → (y ≠ p.vertex a) ) := by
  classical
  intro n p a Cp y hyCp h
  apply hyCp
  have : p.vertex a ∈ Cp := by
    change p.vertex a ∈ ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
    exact Set.mem_iUnion.mpr ⟨a, left_mem_segment Real _ _⟩
  simpa [h] using this

private abbrev hnotB :=
  ApollonianSuperharmonic.LocalCoherenceProof.hnotA

private theorem hmem :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
        let e := segment Real (p.vertex a) (p.vertex b)
        ∀ (y : ℝ × ℝ), (y ∈ e) → (y = p.vertex a ∨ y = p.vertex b ∨ y ∈ openSegment Real
            (p.vertex a) (p.vertex b)) ) := by
  classical
  intro n p a b e y hye
  have hseg : y ∈ segment Real (p.vertex a) (p.vertex b) := by
    simpa [e] using hye
  rw [← insert_endpoints_openSegment] at hseg
  simpa using hseg

private theorem hyLcar :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let Cp := P3544T1BoundaryCarrier p
        let CL := P3544T1BoundaryCarrier C.left
        let e := segment Real (p.vertex a) (p.vertex b)
        ∀ (y : ℝ × ℝ), (y ∉ Cp) → ((y ∉ e) → (y ∉ CL)) ) := by
  classical
  intro n p a b C Cp CL e y hyCp hye hy
  let CR := P3544T1BoundaryCarrier C.right
  have hyin : y ∈ Cp ∪ e := by
    have hycc : y ∈ CL ∪ CR := Or.inl hy
    rw [C.carrier_union] at hycc
    exact hycc
  rcases hyin with hyCp' | hyE
  · exact hyCp hyCp'
  · exact hye hyE

private theorem hyRcar :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let Cp := P3544T1BoundaryCarrier p
        let CR := P3544T1BoundaryCarrier C.right
        let e := segment Real (p.vertex a) (p.vertex b)
        ∀ (y : ℝ × ℝ), (y ∉ Cp) → ((y ∉ e) → (y ∉ CR)) ) := by
  classical
  intro n p a b C Cp CR e y hyCp hye hy
  let CL := P3544T1BoundaryCarrier C.left
  have hyin : y ∈ Cp ∪ e := by
    have hycc : y ∈ CL ∪ CR := Or.inr hy
    rw [C.carrier_union] at hycc
    exact hycc
  rcases hyin with hyCp' | hyE
  · exact hyCp hyCp'
  · exact hye hyE

private theorem hfirstL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), C.il 0 = a ) := by
  classical
  intro n p a b C
  have h := congrArg (fun l : List (Fin (n + 3)) => l[0]?) C.left_order
  simpa using h

private theorem hfirstR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), C.ir 0 = b ) := by
  classical
  intro n p a b C
  have h := congrArg (fun l : List (Fin (n + 3)) => l[0]?) C.right_order
  simpa using h

private theorem hlastL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let ilast : Fin (C.leftParameter + 3) := Fin.last (C.leftParameter + 2)
        C.il ilast = b ) := by
  classical
  intro n p a b C ilast
  have hfn : (List.ofFn C.il).getLast? = some (C.il ilast) := by
    calc
      (List.ofFn C.il).getLast? =
          some ((List.ofFn C.il).getLast (by simp)) :=
        List.getLast?_eq_getLast_of_ne_nil (by simp)
      _ = some (C.il (Fin.last (C.leftParameter + 2))) :=
        congrArg some (List.getLast_ofFn_succ C.il)
      _ = some (C.il ilast) := by simp [ilast]
  have ho : (List.ofFn C.il).getLast? = some b := by
    rw [C.left_order, ← List.cons_append,
      List.getLast?_append_of_ne_nil (a :: C.u) (by simp)]
    simp
  rw [hfn] at ho
  injection ho

private theorem hlastR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let irlast : Fin (C.rightParameter + 3) := Fin.last (C.rightParameter + 2)
        C.ir irlast = a ) := by
  classical
  intro n p a b C irlast
  have hfn : (List.ofFn C.ir).getLast? = some (C.ir irlast) := by
    calc
      (List.ofFn C.ir).getLast? =
          some ((List.ofFn C.ir).getLast (by simp)) :=
        List.getLast?_eq_getLast_of_ne_nil (by simp)
      _ = some (C.ir (Fin.last (C.rightParameter + 2))) :=
        congrArg some (List.getLast_ofFn_succ C.ir)
      _ = some (C.ir irlast) := by simp [irlast]
  have ho : (List.ofFn C.ir).getLast? = some a := by
    rw [C.right_order, ← List.cons_append,
      List.getLast?_append_of_ne_nil (b :: C.v) (by simp)]
    simp
  rw [hfn] at ho
  injection ho

private theorem hwrapL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let ilast : Fin (C.leftParameter + 3) := Fin.last (C.leftParameter + 2)
        ilast + 1 = 0 ) := by
  classical
  intro n p a b C ilast
  apply Fin.ext
  simp [ilast]

private theorem hwrapR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let irlast : Fin (C.rightParameter + 3) := Fin.last (C.rightParameter + 2)
        irlast + 1 = 0 ) := by
  classical
  intro n p a b C irlast
  apply Fin.ext
  simp [irlast]

private theorem hleftB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let ilast : Fin (C.leftParameter + 3) := Fin.last (C.leftParameter + 2)
        (C.il ilast = b) → (C.left.vertex ilast = p.vertex b) ) := by
  classical
  intro n p a b C ilast hlastL
  rw [C.left_vertex]
  change p.vertex (C.il ilast) = p.vertex b
  rw [hlastL]

private theorem hleftA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let ilast : Fin (C.leftParameter + 3) := Fin.last (C.leftParameter + 2)
        (C.il 0 = a) → ((ilast + 1 = 0) → (C.left.vertex (ilast + 1) = p.vertex a)) ) := by
  classical
  intro n p a b C ilast hfirstL hwrapL
  rw [C.left_vertex]
  change p.vertex (C.il (ilast + 1)) = p.vertex a
  rw [hwrapL, hfirstL]

private theorem hrightA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let irlast : Fin (C.rightParameter + 3) := Fin.last (C.rightParameter + 2)
        (C.ir irlast = a) → (C.right.vertex irlast = p.vertex a) ) := by
  classical
  intro n p a b C irlast hlastR
  rw [C.right_vertex]
  change p.vertex (C.ir irlast) = p.vertex a
  rw [hlastR]

private theorem hrightB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let irlast : Fin (C.rightParameter + 3) := Fin.last (C.rightParameter + 2)
        (C.ir 0 = b) → ((irlast + 1 = 0) → (C.right.vertex (irlast + 1) = p.vertex b)) ) := by
  classical
  intro n p a b C irlast hfirstR hwrapR
  rw [C.right_vertex]
  change p.vertex (C.ir (irlast + 1)) = p.vertex b
  rw [hwrapR, hfirstR]

private theorem hreverse :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
        let H : Real × Real → Real := fun y =>
          P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
        ∀ (y : ℝ × ℝ), P3381T1TriangleDeterminant ![p.vertex b, p.vertex a, y] = -H y ) := by
  classical
  intro n p a b H y
  simp [H, P3381T1TriangleDeterminant]
  ring

private theorem hcanonL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let OL := P3544T1RayParity C.left
        ∀ (x : ℝ × ℝ),
        let ilast : Fin (C.leftParameter + 3) := Fin.last (C.leftParameter + 2)
        (C.left.vertex ilast = p.vertex b) → ((C.left.vertex (ilast + 1) = p.vertex a) → (∀ (rL :
            ℝ), ∀ (sL : Bool), (∀ y ∈ Metric.ball x rL, y ∈ P3544T1RayParity C.left ↔ if sL =
            true then (0 : ℝ) < P3381T1TriangleDeterminant ![C.left.vertex ilast, C.left.vertex
            (ilast + (1 : Fin (C.leftParameter + (3 : ℕ)))), y] else P3381T1TriangleDeterminant
            ![C.left.vertex ilast, C.left.vertex (ilast + (1 : Fin (C.leftParameter + (3 : ℕ)))),
                y] <
            (0 : ℝ)) → (
        let H : Real × Real → Real := fun y =>
          P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
        (∀ (y : Real × Real), P3381T1TriangleDeterminant ![p.vertex b, p.vertex a, y] = -H y) →
            (∀ y ∈ Metric.ball x rL, (y ∈ OL ↔ if !sL then 0 < H y else H y < 0))))) ) := by
  classical
  intro n p a b C OL x ilast hleftB hleftA rL sL hsideL H hreverse y hy
  have h := hsideL y hy
  rw [hleftB, hleftA] at h
  rw [hreverse y] at h
  cases sL <;> simpa [H, neg_pos, neg_lt_zero] using h

private theorem hcanonR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let OR := P3544T1RayParity C.right
        ∀ (x : ℝ × ℝ),
        let irlast : Fin (C.rightParameter + 3) := Fin.last (C.rightParameter + 2)
        (C.right.vertex irlast = p.vertex a) → ((C.right.vertex (irlast + 1) = p.vertex b) → (∀
            (rR : ℝ), ∀ (sR : Bool), (∀ y ∈ Metric.ball x rR, y ∈ P3544T1RayParity C.right ↔ if
            sR = true then (0 : ℝ) < P3381T1TriangleDeterminant ![C.right.vertex irlast,
            C.right.vertex (irlast + (1 : Fin (C.rightParameter + (3 : ℕ)))), y] else
            P3381T1TriangleDeterminant ![C.right.vertex irlast, C.right.vertex (irlast + (1 :
            Fin (C.rightParameter + (3 : ℕ)))), y] < (0 : ℝ)) → (
        let H : Real × Real → Real := fun y =>
          P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
        ∀ y ∈ Metric.ball x rR, (y ∈ OR ↔ if sR then 0 < H y else H y < 0)))) ) := by
  classical
  intro n p a b C OR x irlast hrightA hrightB rR sR hsideR H y hy
  have h := hsideR y hy
  rw [hrightA, hrightB] at h
  simpa [H] using h

private theorem hABne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), (a ≠ b) → (p.vertex a ≠ p.vertex b) ) := by
  classical
  intro n p a b hab h
  exact hab (p.injective h)

private theorem hcoord :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), (p.vertex a ≠ p.vertex b) → (
        let dx := (p.vertex b).1 - (p.vertex a).1
        let dy := (p.vertex b).2 - (p.vertex a).2
        dx ≠ 0 ∨ dy ≠ 0) ) := by
  classical
  intro n p a b hABne dx dy
  by_contra h
  push Not at h
  apply hABne
  apply Prod.ext <;> dsimp [dx, dy] at * <;> linarith

private theorem hxdet :
    (by
      classical
      exact
        ∀ (n : ℕ) (p : P3381T1PolygonBoundary n)
          (a b : Fin (n + (3 : ℕ))),
          ∀ x ∈ openSegment ℝ (p.vertex a) (p.vertex b),
            let H := fun (y : ℝ × ℝ) =>
              P3381T1TriangleDeterminant
                ![p.vertex a, p.vertex b, y];
            H x = (0 : ℝ)) := by
  classical
  intro n p a b x hx H
  have hxseg : x ∈ segment Real (p.vertex a) (p.vertex b) :=
    openSegment_subset_segment Real (p.vertex a) (p.vertex b) hx
  rw [segment_eq_image] at hxseg
  rcases hxseg with ⟨t, ht, rfl⟩
  simp [H, P3381T1TriangleDeterminant, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ring

private theorem hshift :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (x : ℝ × ℝ),
        let H : Real × Real → Real := fun y =>
          P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
        let dx := (p.vertex b).1 - (p.vertex a).1
        let dy := (p.vertex b).2 - (p.vertex a).2
        ∀ (u : ℝ), ∀ (v : ℝ), H (x.1 + u, x.2 + v) = H x + dx * v - dy * u ) := by
  classical
  intro n p a b x H dx dy u v
  simp [H, P3381T1TriangleDeterminant, dx, dy]
  ring

private theorem hrho :
    (by
      classical
      exact
        ∀ (rL : ℝ), ((0 : ℝ) < rL) → (∀ (rR : ℝ), ((0 : ℝ) < rR) → (∀ (rp : ℝ), (rp > (0 : ℝ)) → (
        let rho := min (min rL rR) rp
        0 < rho))) ) := by
  classical
  intro rL hrL rR hrR rp hrp rho
  dsimp [rho]
  exact lt_min (lt_min hrL hrR) hrp

private theorem hballV :
    (by
      classical
      exact
        ∀ (x : ℝ × ℝ), ∀ (rL : ℝ), ∀ (rR : ℝ), ∀ (rp : ℝ),
        let rho := min (min rL rR) rp
        ∀ (t : ℝ), |t| < rho → (x.1, x.2 + t) ∈ Metric.ball x rho ) := by
  classical
  intro x rL rR rp rho t ht
  simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq,
    add_comm, add_left_comm, add_assoc] using ht

private theorem hballH :
    (by
      classical
      exact
        ∀ (x : ℝ × ℝ), ∀ (rL : ℝ), ∀ (rR : ℝ), ∀ (rp : ℝ),
        let rho := min (min rL rR) rp
        ∀ (t : ℝ), |t| < rho → (x.1 + t, x.2) ∈ Metric.ball x rho ) := by
  classical
  intro x rL rR rp rho t ht
  simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq,
    add_comm, add_left_comm, add_assoc] using ht

private theorem hballNegDelta :
    (by
      classical
      exact
        ∀ (rL : ℝ), ∀ (rR : ℝ), ∀ (rp : ℝ),
        let rho := min (min rL rR) rp
        let delta := rho / 2
        (0 < delta) → ((delta < rho) → (|-delta| < rho)) ) := by
  classical
  intro rL rR rp rho delta hdelta hdelta_lt
  rw [abs_neg, abs_of_pos hdelta]
  exact hdelta_lt

private theorem htransverse :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (x : ℝ × ℝ), ∀ (rL : ℝ), ∀ (sL : Bool), ∀ (rR : ℝ),
        let H : Real × Real → Real := fun y =>
          P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
        ∀ (rp : ℝ),
        let rho := min (min rL rR) rp
        let dx := (p.vertex b).1 - (p.vertex a).1
        let dy := (p.vertex b).2 - (p.vertex a).2
        (dx ≠ 0 ∨ dy ≠ 0) → ((H x = 0) → ((∀ (v : Real), H (x.1, x.2 + v) = H x + dx * v) → ((∀
            (u : Real), H (x.1 + u, x.2) = H x - dy * u) → (
        let delta := rho / 2
        (0 < delta) → ((∀ (t : Real), (|t| < rho) → ((x.1, x.2 + t) ∈ Metric.ball x rho)) → ((∀
            (t : Real), (|t| < rho) → ((x.1 + t, x.2) ∈ Metric.ball x rho)) → ((|delta| < rho) →
            ((|-delta| < rho) → (∃ y ∈ Metric.ball x rho, if sL then H y < 0 else 0 < H
            y))))))))) ) := by
  classical
  intro n p a b x rL sL rR H rp rho dx dy hcoord hxdet hshiftV hshiftH delta hdelta hballV hballH
      hballDelta hballNegDelta
  by_cases hdx : dx ≠ 0
  · by_cases hsL : sL
    · by_cases hdxpos : 0 < dx
      · refine ⟨(x.1, x.2 + -delta), hballV (-delta) hballNegDelta, ?_⟩
        rw [ite_eq_left hsL]
        rw [hshiftV, hxdet]
        simpa [neg_mul] using (neg_lt_zero.mpr (mul_pos hdxpos hdelta))
      · have hdxneg : dx < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hdxpos) hdx
        refine ⟨(x.1, x.2 + delta), hballV delta hballDelta, ?_⟩
        rw [ite_eq_left hsL]
        rw [hshiftV, hxdet]
        simpa using (mul_neg_of_neg_of_pos hdxneg hdelta)
    · by_cases hdxpos : 0 < dx
      · refine ⟨(x.1, x.2 + delta), hballV delta hballDelta, ?_⟩
        rw [ite_eq_right hsL]
        rw [hshiftV, hxdet]
        simpa using mul_pos hdxpos hdelta
      · have hdxneg : dx < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hdxpos) hdx
        refine ⟨(x.1, x.2 + -delta), hballV (-delta) hballNegDelta, ?_⟩
        rw [ite_eq_right hsL]
        rw [hshiftV, hxdet]
        simpa [neg_mul] using (neg_pos.mpr (mul_neg_of_neg_of_pos hdxneg hdelta))
  · have hdy : dy ≠ 0 := hcoord.resolve_left hdx
    by_cases hsL : sL
    · by_cases hdypos : 0 < dy
      · refine ⟨(x.1 + delta, x.2), hballH delta hballDelta, ?_⟩
        rw [ite_eq_left hsL]
        rw [hshiftH, hxdet]
        simpa [sub_eq_add_neg] using (neg_lt_zero.mpr (mul_pos hdypos hdelta))
      · have hdyneg : dy < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hdypos) hdy
        refine ⟨(x.1 + -delta, x.2), hballH (-delta) hballNegDelta, ?_⟩
        rw [ite_eq_left hsL]
        rw [hshiftH, hxdet]
        simpa [neg_mul, sub_eq_add_neg] using (mul_neg_of_neg_of_pos hdyneg hdelta)
    · by_cases hdypos : 0 < dy
      · refine ⟨(x.1 + -delta, x.2), hballH (-delta) hballNegDelta, ?_⟩
        rw [ite_eq_right hsL]
        rw [hshiftH, hxdet]
        simpa [neg_mul, sub_eq_add_neg] using (mul_pos hdypos hdelta)
      · have hdyneg : dy < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hdypos) hdy
        refine ⟨(x.1 + delta, x.2), hballH delta hballDelta, ?_⟩
        rw [ite_eq_right hsL]
        rw [hshiftH, hxdet]
        simpa [sub_eq_add_neg] using (neg_pos.mpr (mul_neg_of_neg_of_pos hdyneg hdelta))

private theorem hsignsOpp :
    (by
      classical
      exact
        ∀ (n : Nat),
          ∀ (p : P3381T1PolygonBoundary n),
            ∀ (a : Fin (n + 3)),
              ∀ (b : Fin (n + 3)),
                ∀ (C : P3650T1CyclicChildren p a b),
                  (∀ x ∉ P3544T1BoundaryCarrier C.left,
                      x ∉ P3544T1BoundaryCarrier C.right →
                        (x ∈ P3544T1RayParity p ↔
                          x ∈ P3544T1RayParity C.left ∧ x ∉ P3544T1RayParity C.right ∨
                            x ∉ P3544T1RayParity C.left ∧ x ∈ P3544T1RayParity C.right)) →
                    let Op := P3544T1RayParity p;
                    let OL := P3544T1RayParity C.left;
                    let OR := P3544T1RayParity C.right;
                    ∀ (x : ℝ × ℝ),
                      ∀ (rL : ℝ),
                        ∀ (sL : Bool),
                          ∀ (rR : ℝ),
                            ∀ (sR : Bool),
                              let H : Real × Real → Real := fun y =>
                                P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
                              (∀ y ∈ Metric.ball x rL,
                                y ∈ OL ↔ if !sL then 0 < H y else H y < 0) →
                                (∀ y ∈ Metric.ball x rR,
                                y ∈ OR ↔ if sR then 0 < H y else H y < 0) →
                                ∀ (rp : ℝ),
                                Metric.ball x rp ⊆ Op →
                                let rho := min (min rL rR) rp
                              (∃ y ∈ Metric.ball x rho, if sL then H y < 0 else 0 < H y) →
                                sR = sL
    ) := by
  classical
  intro n p a b C hsum Op OL OR x rL sL rR sR H hcanonL hcanonR rp hparentball rho htransverse
  cases sL <;> cases sR
  · rfl
  · exfalso
    obtain ⟨y, hyball, hysign⟩ := htransverse
    have hyLball : y ∈ Metric.ball x rL :=
      Metric.ball_subset_ball (le_trans (min_le_left (min rL rR) rp) (min_le_left rL rR)) hyball
    have hyRball : y ∈ Metric.ball x rR :=
      Metric.ball_subset_ball (le_trans (min_le_left (min rL rR) rp) (min_le_right rL rR)) hyball
    have hyparent : y ∈ Metric.ball x rp :=
      Metric.ball_subset_ball (min_le_right (min rL rR) rp) hyball
    have hyL : y ∈ OL := by
      apply (hcanonL y hyLball).2
      simpa using hysign
    have hyR : y ∈ OR := by
      apply (hcanonR y hyRball).2
      simpa using hysign
    have hyOp : y ∈ Op := hparentball hyparent
    rcases (hsum y hyL.1 hyR.1).mp hyOp with ⟨_, hn⟩ | ⟨hn, _⟩
    · exact hn hyR
    · exact hn hyL
  · exfalso
    obtain ⟨y, hyball, hysign⟩ := htransverse
    have hyLball : y ∈ Metric.ball x rL :=
      Metric.ball_subset_ball (le_trans (min_le_left (min rL rR) rp) (min_le_left rL rR)) hyball
    have hyRball : y ∈ Metric.ball x rR :=
      Metric.ball_subset_ball (le_trans (min_le_left (min rL rR) rp) (min_le_right rL rR)) hyball
    have hyparent : y ∈ Metric.ball x rp :=
      Metric.ball_subset_ball (min_le_right (min rL rR) rp) hyball
    have hyL : y ∈ OL := by
      apply (hcanonL y hyLball).2
      simpa using hysign
    have hyR : y ∈ OR := by
      apply (hcanonR y hyRball).2
      simpa using hysign
    have hyOp : y ∈ Op := hparentball hyparent
    rcases (hsum y hyL.1 hyR.1).mp hyOp with ⟨_, hn⟩ | ⟨hn, _⟩
    · exact hn hyR
    · exact hn hyL
  · rfl

end LocalCoherenceProof

theorem P3650T1LocalCoherence {n : Nat} (p : P3381T1PolygonBoundary n)
    (a b : Fin (n + 3)) (hab : a ≠ b) (C : P3650T1CyclicChildren p a b)
    (hodd : openSegment Real (p.vertex a) (p.vertex b) ⊆ P3544T1RayParity p)
    (hleft : Disjoint
      (P3544T1BoundaryCarrier C.left \ segment Real (p.vertex a) (p.vertex b))
      (P3544T1RayParity C.right))
    (hright : Disjoint
      (P3544T1BoundaryCarrier C.right \ segment Real (p.vertex a) (p.vertex b))
      (P3544T1RayParity C.left))
    (hsum : ∀ x, x ∉ P3544T1BoundaryCarrier C.left →
      x ∉ P3544T1BoundaryCarrier C.right →
      (x ∈ P3544T1RayParity p ↔
        (x ∈ P3544T1RayParity C.left ∧ x ∉ P3544T1RayParity C.right) ∨
        (x ∉ P3544T1RayParity C.left ∧ x ∈ P3544T1RayParity C.right))) :
    (∀ x, x ∈ openSegment Real (p.vertex a) (p.vertex b) →
      ∃ r : Real, 0 < r ∧ ∃ s : Bool, ∀ y ∈ Metric.ball x r,
        (y ∈ P3544T1RayParity C.left ↔
          if s then 0 < P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
          else P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y] < 0) ∧
        (y ∈ P3544T1RayParity C.right ↔
          if s then P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y] < 0
          else 0 < P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y])) ∧
    (∀ z ∈ ({p.vertex a, p.vertex b} : Set (Real × Real)),
      ∃ r : Real, 0 < r ∧
        Metric.ball z r ∩ P3544T1RayParity p =
          Metric.ball z r ∩ (P3544T1RayParity C.left ∪
            P3544T1RayParity C.right ∪ openSegment Real (p.vertex a) (p.vertex b))) := by
-- BODY
  classical
  let Cp := P3544T1BoundaryCarrier p
  let CL := P3544T1BoundaryCarrier C.left
  let CR := P3544T1BoundaryCarrier C.right
  let Op := P3544T1RayParity p
  let OL := P3544T1RayParity C.left
  let OR := P3544T1RayParity C.right
  let e := segment Real (p.vertex a) (p.vertex b)
  have hOL_Cp : Disjoint OL Cp := LocalCoherenceProof.hOL_Cp n p a b C hright
  have hOR_Cp : Disjoint OR Cp := LocalCoherenceProof.hOR_Cp n p a b C hleft
  have hpropagate (O : Set (Real × Real)) (K : Set (Real × Real))
      (hclosure : closure O = O ∪ K) (hopen : IsOpen O)
      (S : Set (Real × Real)) (hpre : IsPreconnected S)
      (hdisj : Disjoint S K) (hseed : (S ∩ O).Nonempty) : S ⊆ O := LocalCoherenceProof.hpropagate
          O K hclosure hopen S hpre hdisj hseed
  have hfirst : ∀ z ∈ ({p.vertex a, p.vertex b} : Set (Real × Real)),
      ∃ r : Real, 0 < r ∧ Metric.ball z r ∩ Op =
        Metric.ball z r ∩ (OL ∪ OR ∪ openSegment Real (p.vertex a) (p.vertex b)) := by
    intro z hz
    have hzab : z = p.vertex a ∨ z = p.vertex b := by simpa using hz
    have hzclosure : z ∈ closure (openSegment Real (p.vertex a) (p.vertex b)) :=
        LocalCoherenceProof.hzclosure n p a b z hzab
    have hidxL : ∀ t : Fin (n + 3), t ∈ ({a, b} : Set (Fin (n + 3))) →
        ∃ i : Fin (C.leftParameter + 3), C.left.vertex i = p.vertex t :=
            LocalCoherenceProof.hidxL n p a
            b C
    have hidxR : ∀ t : Fin (n + 3), t ∈ ({a, b} : Set (Fin (n + 3))) →
        ∃ i : Fin (C.rightParameter + 3), C.right.vertex i = p.vertex t :=
            LocalCoherenceProof.hidxR n p
            a b C
    have hidxLz : ∃ i : Fin (C.leftParameter + 3), C.left.vertex i = z :=
        LocalCoherenceProof.hidxLz n p
        a b C z hzab hidxL
    have hidxRz : ∃ i : Fin (C.rightParameter + 3), C.right.vertex i = z :=
        LocalCoherenceProof.hidxRz n
        p a b C z hzab hidxR
    obtain ⟨iL, hiL⟩ := hidxLz
    obtain ⟨iR, hiR⟩ := hidxRz
    obtain ⟨rL, hrL, hpathL, _⟩ := (P3544T1LocalParity C.left).2.2.2.2.2.2.2.1 iL
    obtain ⟨rR, hrR, hpathR, _⟩ := (P3544T1LocalParity C.right).2.2.2.2.2.2.2.1 iR
    have hopenP : IsOpen Op := (P3544T1LocalParity p).2.1
    have hclosureL : closure OL = OL ∪ CL := by
      simpa [OL, CL] using (P3544T1LocalParity C.left).1
    have hclosureR : closure OR = OR ∪ CR := by
      simpa [OR, CR] using (P3544T1LocalParity C.right).1
    have hclosureP : closure Op = Op ∪ Cp := by
      simpa [Op, Cp] using (P3544T1LocalParity p).1
    have hseedL : ((Metric.ball z rL ∩ OL) ∩ Op).Nonempty := LocalCoherenceProof.hseedL n p a b C
        hodd z hzclosure rL hrL hopenP hclosureL
    have hseedR : ((Metric.ball z rR ∩ OR) ∩ Op).Nonempty := LocalCoherenceProof.hseedR n p a b C
        hodd z hzclosure rR hrR hopenP hclosureR
    have hOLin : Metric.ball z rL ∩ OL ⊆ Op := LocalCoherenceProof.hOLin n p a b C hOL_Cp
        hpropagate z iL hiL rL hpathL hopenP hclosureP hseedL
    have hORin : Metric.ball z rR ∩ OR ⊆ Op := LocalCoherenceProof.hORin n p a b C hOR_Cp
        hpropagate z iR hiR rR hpathR hopenP hclosureP hseedR
    refine ⟨min rL rR, lt_min hrL hrR, ?_⟩
    ext y
    constructor
    · rintro ⟨hyball, hyop⟩
      have hyCp : y ∉ Cp := hyop.1
      by_cases hye : y ∈ e
      · have hnotA : y ≠ p.vertex a := LocalCoherenceProof.hnotA n p a y hyCp
        have hnotB : y ≠ p.vertex b := LocalCoherenceProof.hnotB n p b y hyCp
        have hmem : y = p.vertex a ∨ y = p.vertex b ∨
            y ∈ openSegment Real (p.vertex a) (p.vertex b) := LocalCoherenceProof.hmem n p a b y hye
        rcases hmem with h | h | hyseg
        · exact False.elim (hnotA h)
        · exact False.elim (hnotB h)
        · exact ⟨hyball, Or.inr hyseg⟩
      · have hyLcar : y ∉ CL := LocalCoherenceProof.hyLcar n p a b C y hyCp hye
        have hyRcar : y ∉ CR := LocalCoherenceProof.hyRcar n p a b C y hyCp hye
        have hxsum := (hsum y hyLcar hyRcar).mp hyop
        rcases hxsum with hx | hx
        · exact ⟨hyball, Or.inl (Or.inl hx.1)⟩
        · exact ⟨hyball, Or.inl (Or.inr hx.2)⟩
    · rintro ⟨hyball, hy⟩
      have hballL : Metric.ball z (min rL rR) ⊆ Metric.ball z rL :=
        Metric.ball_subset_ball (min_le_left rL rR)
      have hballR : Metric.ball z (min rL rR) ⊆ Metric.ball z rR :=
        Metric.ball_subset_ball (min_le_right rL rR)
      rcases hy with hyLR | hyseg
      · rcases hyLR with hyL | hyR
        · exact ⟨hyball, hOLin ⟨hballL hyball, hyL⟩⟩
        · exact ⟨hyball, hORin ⟨hballR hyball, hyR⟩⟩
      · have hyop : y ∈ Op := hodd hyseg
        exact ⟨hyball, hyop⟩
  have hinterior : ∀ x ∈ openSegment Real (p.vertex a) (p.vertex b),
      ∃ r : Real, 0 < r ∧ ∃ s : Bool, ∀ y ∈ Metric.ball x r,
        (y ∈ OL ↔ if s then 0 < P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
          else P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y] < 0) ∧
        (y ∈ OR ↔ if s then P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y] < 0
          else 0 < P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]) := by
    intro x hx
    let ilast : Fin (C.leftParameter + 3) := Fin.last (C.leftParameter + 2)
    let irlast : Fin (C.rightParameter + 3) := Fin.last (C.rightParameter + 2)
    have hfirstL : C.il 0 = a := LocalCoherenceProof.hfirstL n p a b C
    have hfirstR : C.ir 0 = b := LocalCoherenceProof.hfirstR n p a b C
    have hlastL : C.il ilast = b := LocalCoherenceProof.hlastL n p a b C
    have hlastR : C.ir irlast = a := LocalCoherenceProof.hlastR n p a b C
    have hwrapL : ilast + 1 = 0 := LocalCoherenceProof.hwrapL n p a b C
    have hwrapR : irlast + 1 = 0 := LocalCoherenceProof.hwrapR n p a b C
    have hleftB : C.left.vertex ilast = p.vertex b := LocalCoherenceProof.hleftB n p a b C hlastL
    have hleftA : C.left.vertex (ilast + 1) = p.vertex a := LocalCoherenceProof.hleftA n p a b C
        hfirstL hwrapL
    have hrightA : C.right.vertex irlast = p.vertex a := LocalCoherenceProof.hrightA n p a b C
        hlastR
    have hrightB : C.right.vertex (irlast + 1) = p.vertex b := LocalCoherenceProof.hrightB n p a
        b C hfirstR hwrapR
    have hxL : x ∈ openSegment Real (C.left.vertex ilast) (C.left.vertex (ilast + 1)) := by
      simpa [hleftA, hleftB, openSegment_symm] using hx
    have hxR : x ∈ openSegment Real (C.right.vertex irlast) (C.right.vertex (irlast + 1)) := by
      simpa [hrightA, hrightB] using hx
    obtain ⟨rL, hrL, sL, hsideL⟩ :=
      (P3544T1LocalParity C.left).2.2.2.2.2.2.2.2 ilast x hxL
    obtain ⟨rR, hrR, sR, hsideR⟩ :=
      (P3544T1LocalParity C.right).2.2.2.2.2.2.2.2 irlast x hxR
    let H : Real × Real → Real := fun y =>
      P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
    have hreverse (y : Real × Real) :
        P3381T1TriangleDeterminant ![p.vertex b, p.vertex a, y] = -H y :=
            LocalCoherenceProof.hreverse n p a b y
    have hcanonL : ∀ y ∈ Metric.ball x rL,
        (y ∈ OL ↔ if !sL then 0 < H y else H y < 0) := LocalCoherenceProof.hcanonL n p a b C x
            hleftB hleftA rL sL hsideL hreverse
    have hcanonR : ∀ y ∈ Metric.ball x rR,
        (y ∈ OR ↔ if sR then 0 < H y else H y < 0) := LocalCoherenceProof.hcanonR n p a b C x
            hrightA hrightB rR sR hsideR
    have hxop : x ∈ Op := hodd hx
    have hopenP : IsOpen Op := (P3544T1LocalParity p).2.1
    obtain ⟨rp, hrp, hparentball⟩ := (Metric.isOpen_iff.mp hopenP) x hxop
    let rho := min (min rL rR) rp
    have hABne : p.vertex a ≠ p.vertex b := LocalCoherenceProof.hABne n p a b hab
    let dx := (p.vertex b).1 - (p.vertex a).1
    let dy := (p.vertex b).2 - (p.vertex a).2
    have hcoord : dx ≠ 0 ∨ dy ≠ 0 := LocalCoherenceProof.hcoord n p a b hABne
    have hxdet : H x = 0 := LocalCoherenceProof.hxdet n p a b x hx
    have hshift (u v : Real) : H (x.1 + u, x.2 + v) = H x + dx * v - dy * u :=
        LocalCoherenceProof.hshift n p a b x u v
    have hshiftV (v : Real) : H (x.1, x.2 + v) = H x + dx * v := by
      simpa using hshift 0 v
    have hshiftH (u : Real) : H (x.1 + u, x.2) = H x - dy * u := by
      simpa using hshift u 0
    have hrho : 0 < rho := LocalCoherenceProof.hrho rL hrL rR hrR rp hrp
    let delta := rho / 2
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hdelta_lt : delta < rho := by dsimp [delta]; linarith
    have hballV (t : Real) (ht : |t| < rho) :
        (x.1, x.2 + t) ∈ Metric.ball x rho := LocalCoherenceProof.hballV x rL rR rp t ht
    have hballH (t : Real) (ht : |t| < rho) :
        (x.1 + t, x.2) ∈ Metric.ball x rho := LocalCoherenceProof.hballH x rL rR rp t ht
    have hballDelta : |delta| < rho := by rw [abs_of_pos hdelta]; exact hdelta_lt
    have hballNegDelta : |-delta| < rho := LocalCoherenceProof.hballNegDelta rL rR rp hdelta
        hdelta_lt
    have htransverse : ∃ y ∈ Metric.ball x rho, if sL then H y < 0 else 0 < H y :=
        LocalCoherenceProof.htransverse n p a b x rL sL rR rp hcoord hxdet hshiftV hshiftH hdelta
        hballV hballH hballDelta hballNegDelta
    have hsignsOpp : sR = sL := LocalCoherenceProof.hsignsOpp n p a b C hsum x rL sL rR sR hcanonL
        hcanonR rp hparentball htransverse
    let s := !sL
    let r := min (min rL rR) rp
    refine ⟨r, lt_min (lt_min hrL hrR) hrp, s, ?_⟩
    intro y hy
    have hsmallL : Metric.ball x r ⊆ Metric.ball x rL :=
      Metric.ball_subset_ball (le_trans (min_le_left (min rL rR) rp) (min_le_left rL rR))
    have hsmallR : Metric.ball x r ⊆ Metric.ball x rR :=
      Metric.ball_subset_ball (le_trans (min_le_left (min rL rR) rp) (min_le_right rL rR))
    have hyL : y ∈ Metric.ball x rL := hsmallL hy
    have hyR : y ∈ Metric.ball x rR := hsmallR hy
    have hL := hcanonL y hyL
    have hR := hcanonR y hyR
    simpa [H, s, hsignsOpp] using And.intro hL hR
  exact ⟨hinterior, hfirst⟩

end ApollonianSuperharmonic

end
