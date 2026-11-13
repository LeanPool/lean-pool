/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3650T1VisibleDiagonal
public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildren
public import LeanPool.ApollonianSuperharmonic.P3544T1TriangleRayGeometry
public import LeanPool.ApollonianSuperharmonic.P5667T1CyclicChildrenOldArcsPreconnected
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

-- [TABLET NODE: P3650T1OldArcEven]

/-!
# P3650T1OldArcEven

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OldArcParityProof

private theorem hLoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let CR := P3544T1BoundaryCarrier C.right
        Disjoint (CL \ e) CR ) := by
  classical
  intro n p E D C e CL CR
  rw [Set.disjoint_left]
  intro x hxL hxR
  have hi : x ∈ CL ∩ CR := ⟨hxL.1, hxR⟩
  change x ∈ P3544T1BoundaryCarrier C.left ∩
    P3544T1BoundaryCarrier C.right at hi
  rw [C.carrier_intersection] at hi
  exact hxL.2 hi

private theorem hRoff :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let CR := P3544T1BoundaryCarrier C.right
        Disjoint (CR \ e) CL ) := by
  classical
  intro n p E D C e CL CR
  rw [Set.disjoint_left]
  intro x hxR hxL
  have hi : x ∈ CL ∩ CR := ⟨hxL, hxR.1⟩
  change x ∈ P3544T1BoundaryCarrier C.left ∩
    P3544T1BoundaryCarrier C.right at hi
  rw [C.carrier_intersection] at hi
  exact hxR.2 hi

private theorem hLparent :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let CP := P3544T1BoundaryCarrier p
        CL \ e ⊆ CP ) := by
  classical
  intro n p E D C e CL CP x hx
  let CR := P3544T1BoundaryCarrier C.right
  have hmem : x ∈ CL ∪ CR := Or.inl hx.1
  change x ∈ P3544T1BoundaryCarrier C.left ∪
    P3544T1BoundaryCarrier C.right at hmem
  rw [C.carrier_union] at hmem
  rcases hmem with hparent | hdiag
  · exact hparent
  · exact (hx.2 hdiag).elim

private theorem hRparent :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CR := P3544T1BoundaryCarrier C.right
        let CP := P3544T1BoundaryCarrier p
        CR \ e ⊆ CP ) := by
  classical
  intro n p E D C e CR CP x hx
  let CL := P3544T1BoundaryCarrier C.left
  have hmem : x ∈ CL ∪ CR := Or.inr hx.1
  change x ∈ P3544T1BoundaryCarrier C.left ∪
    P3544T1BoundaryCarrier C.right at hmem
  rw [C.carrier_union] at hmem
  rcases hmem with hparent | hdiag
  · exact hparent
  · exact (hx.2 hdiag).elim

private theorem oldArcEvenOnPreconnected :
    (by
      classical
      exact
        ∀ {X : Type}, ∀ [TopologicalSpace X], ∀ (O : Set X), ∀ (K : Set X), ∀ (S : Set X),
            (IsOpen O) → ((closure O = O ∪ K) → ((IsPreconnected S) → ((Disjoint S K) → (∀ (x :
            X), (x ∈ S) → ((x ∉ O) → (Disjoint S O)))))) ) := by
  classical
  intro X typeclassInstance0 O K S hO hclosure hS hSK x hx hxO
  classical
  have hE : IsOpen (O ∪ K)ᶜ := by
    rw [← hclosure]
    exact isClosed_closure.isOpen_compl
  have hOE : Disjoint O (O ∪ K)ᶜ :=
    Set.disjoint_left.mpr (fun y hy hye => hye (Or.inl hy))
  have hcover : S ⊆ O ∪ (O ∪ K)ᶜ := by
    intro y hy
    by_cases hyO : y ∈ O
    · exact Or.inl hyO
    · refine Or.inr ?_
      rintro (hyO' | hyK)
      · exact hyO hyO'
      · exact Set.disjoint_left.mp hSK hy hyK
  rcases IsPreconnected.subset_or_subset hO hE hOE hcover hS with hSO | hSE
  · exact False.elim (hxO (hSO hx))
  · exact Set.disjoint_left.mpr (fun y hy hyO => hSE hy (Or.inl hyO))

private theorem oldArcOddOnPreconnected :
    (by
      classical
      exact
        (∀ {X : Type}, ∀ [TopologicalSpace X], ∀ (O : Set X), ∀ (K : Set X), ∀ (S : Set X),
            (IsOpen O) → ((closure O = O ∪ K) → ((IsPreconnected S) → ((Disjoint S K) → (∀ (x :
            X), (x ∈ S) → ((x ∉ O) → (Disjoint S O))))))) → (∀ {X : Type}, ∀ [TopologicalSpace
            X], ∀ (O : Set X), ∀ (K : Set X), ∀ (S : Set X), (IsOpen O) → ((closure O = O ∪ K) →
            ((IsPreconnected S) → ((Disjoint S K) → (∀ (x : X), (x ∈ S) → ((x ∈ O) → (S ⊆
            O))))))) ) := by
  classical
  intro oldArcEvenOnPreconnected X typeclassInstance0 O K S hO hclosure hS hSK x hx hxO y hy
  by_contra hyO
  have hEven := oldArcEvenOnPreconnected O K S hO hclosure hS hSK y hy hyO
  exact Set.disjoint_left.mp hEven hx hxO

private theorem oldArcEvenClosure :
    (by
      classical
      exact
        ∀ {X : Type}, ∀ [TopologicalSpace X], ∀ (O : Set X), ∀ (S : Set X), (IsOpen O) →
            ((Disjoint S O) → (Disjoint (closure S) O)) ) := by
  classical
  intro X typeclassInstance0 O S hO hSO
  have hsub : S ⊆ Oᶜ := fun y hy hyO => Set.disjoint_left.mp hSO hy hyO
  have hclosed : closure S ⊆ Oᶜ := closure_minimal hsub hO.isClosed_compl
  exact Set.disjoint_left.mpr (fun y hy hyO => hclosed hy hyO)

private theorem leftFirstIndex :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), C.il 1 =
            D.a + 1 ) := by
  classical
  intro n p E D C
  have hN : 0 < n + 3 := by omega
  have hlen : (List.ofFn (fun i : Fin (n + 3) => i)).length = n + 3 := by simp
  have hrot0 := List.getElem?_rotate
      (l := List.ofFn (fun i : Fin (n + 3) => i)) (n := C.rotation) (m := 0) (by simp)
  rw [C.parent_order] at hrot0
  simp only [List.getElem?_cons_zero] at hrot0
  conv_rhs at hrot0 =>
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by simp []))]
    rw [List.getElem_ofFn]
  have hrotval : C.rotation % (n + 3) = D.a.val := by
    have heq := Option.some.inj hrot0
    have hv := congrArg Fin.val heq.symm
    simpa [hlen] using hv
  have hrot1 := List.getElem?_rotate
      (l := List.ofFn (fun i : Fin (n + 3) => i)) (n := C.rotation) (m := 1) (by omega)
  rw [C.parent_order] at hrot1
  have hidxNat : (1 + C.rotation) % (n + 3) = (D.a.val + 1) % (n + 3) := by
    calc
      (1 + C.rotation) % (n + 3) = (1 + C.rotation % (n + 3)) % (n + 3) := by
        rw [Nat.add_mod]
        simp []
      _ = (1 + D.a.val) % (n + 3) := by rw [hrotval]
      _ = (D.a.val + 1) % (n + 3) := by rw [Nat.add_comm]
  have hidx : (⟨(1 + C.rotation) %
      (List.ofFn (fun i : Fin (n + 3) => i)).length,
      by rw [hlen]; exact Nat.mod_lt _ hN⟩ : Fin (n + 3)) = D.a + 1 := by
    apply Fin.ext
    simpa only [Fin.val_add, Fin.val_one, hlen] using hidxNat
  have hsource : (List.ofFn (fun i : Fin (n + 3) => i))[
      (1 + C.rotation) % (List.ofFn (fun i : Fin (n + 3) => i)).length]? =
      some (D.a + 1) := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by simp []))]
    rw [List.getElem_ofFn]
    exact congrArg some hidx
  rw [hsource] at hrot1
  have hu0 : C.u[0]? = some (D.a + 1) := by
    simpa [List.getElem?_append, C.hu] using hrot1
  have hleft1 := congrArg (fun l => l[1]?) C.left_order
  simp only [List.ofFn_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.length_cons,
      List.length_ofFn, lt_add_iff_pos_left, add_pos_iff, Order.lt_two_iff, zero_le, or_true,
      getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, List.length_append,
      List.length_nil, zero_add, Order.lt_add_one_iff, Option.some.injEq] at hleft1
  have hu0val : C.u[0]'C.hu = D.a + 1 := by
    have hopt := hu0
    rw [List.getElem?_eq_getElem C.hu] at hopt
    exact Option.some.inj hopt
  have hleft1' : C.il 1 = C.u[0]'C.hu := by
    simpa only [List.getElem_append_left C.hu] using hleft1
  exact hleft1'.trans hu0val

private theorem propagateRight :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let CR := P3544T1BoundaryCarrier C.right
        let OR := P3544T1RayParity C.right
        (Disjoint (CL \ e) CR) → ((∀ {X : Type}, ∀ [TopologicalSpace X], ∀ (O : Set X), ∀ (K :
            Set X), ∀ (S : Set X), (IsOpen O) → ((closure O = O ∪ K) → ((IsPreconnected S) →
            ((Disjoint S K) → (∀ (x : X), (x ∈ S) → ((x ∉ O) → (Disjoint S O))))))) →
            ((IsPreconnected (P3544T1BoundaryCarrier C.left \ segment ℝ (p.vertex D.a)
            (p.vertex D.b))) → ((IsOpen OR) → ((closure OR = OR ∪ CR) → ((∃ x, x ∈ CL \ e ∧ x ∉
            OR) → Disjoint (CL \ e) OR))))) ) := by
  classical
  intro n p E D C e CL CR OR hLoff oldArcEvenOnPreconnected leftArcPreconnected hRopen hRclosure
  rintro ⟨x, hx, hxO⟩
  exact oldArcEvenOnPreconnected OR CR (CL \ e) hRopen hRclosure
    leftArcPreconnected hLoff x hx hxO

private theorem propagateLeft :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let CR := P3544T1BoundaryCarrier C.right
        let OL := P3544T1RayParity C.left
        (Disjoint (CR \ e) CL) → ((∀ {X : Type}, ∀ [TopologicalSpace X], ∀ (O : Set X), ∀ (K :
            Set X), ∀ (S : Set X), (IsOpen O) → ((closure O = O ∪ K) → ((IsPreconnected S) →
            ((Disjoint S K) → (∀ (x : X), (x ∈ S) → ((x ∉ O) → (Disjoint S O))))))) →
            ((IsPreconnected (P3544T1BoundaryCarrier C.right \ segment ℝ (p.vertex D.a)
            (p.vertex D.b))) → ((IsOpen OL) → ((closure OL = OL ∪ CL) → ((∃ x, x ∈ CR \ e ∧ x ∉
            OL) → Disjoint (CR \ e) OL))))) ) := by
  classical
  intro n p E D C e CL CR OL hRoff oldArcEvenOnPreconnected rightArcPreconnected hLopen hLclosure
  rintro ⟨x, hx, hxO⟩
  exact oldArcEvenOnPreconnected OL CL (CR \ e) hLopen hLclosure
    rightArcPreconnected hRoff x hx hxO

private theorem cyclicStep :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), (P3650T1CyclicChildren p D.a D.b) → (∀ {m : Nat}, ∀
            (i : Fin (m + 3)), (i - 1) + 2 = i + 1) ) := by
  classical
  intro n p E D C m i
  have hsub : (i - 1).val = if i.val = 0 then m + 2 else i.val - 1 := by
    by_cases hz : i.val = 0
    · have hi : i = 0 := Fin.ext hz
      subst i
      simp []
    · rw [ite_eq_right hz]
      have hi : i ≠ 0 := by intro he; exact hz (congrArg Fin.val he)
      exact Fin.val_sub_one_of_ne_zero hi
  apply Fin.ext
  rw [Fin.val_add, Fin.val_add]
  simp only [Fin.val_one]
  rw [hsub]
  by_cases hz : i.val = 0
  · rw [ite_eq_left hz]
    have hmod : m + 2 + (2 : Nat) = m + 3 + 1 := by omega
    norm_num [hmod, hz]
  · simp only [hz, ↓reduceIte, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod]
    have hwrap : i.val + 1 = m + 3 ∨ i.val + 1 < m + 3 := by omega
    rcases hwrap with hwrap | hlt
    · have hleft : i.val - 1 + 2 = m + 3 := by omega
      simp [hleft, hwrap]
    · have hleft : i.val - 1 + 2 < m + 3 := by omega
      simp [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hlt]
      omega

private theorem parityEvenAlongPath :
    (by
      classical
      exact
        (∀ {X : Type}, ∀ [TopologicalSpace X], ∀ (O : Set X), ∀ (K : Set X), ∀ (S : Set X),
            (IsOpen O) → ((closure O = O ∪ K) → ((IsPreconnected S) → ((Disjoint S K) → (∀ (x :
            X), (x ∈ S) → ((x ∉ O) → (Disjoint S O))))))) → (∀ {m : Nat}, ∀ (q :
            P3381T1PolygonBoundary m), ∀ (γ : Real → Real × Real), (ContinuousOn γ (Set.Icc (0
            : Real) 1)) → ((∀ t ∈ Set.Icc (0 : Real) 1,
            γ t ∉ P3544T1BoundaryCarrier q) → ((γ 0 ∉ P3544T1RayParity q) → (∀ t ∈ Set.Icc (0
                : Real) 1, γ t ∉ P3544T1RayParity q)))) ) := by
  classical
  intro oldArcEvenOnPreconnected m q γ hcont havoid hstart
  classical
  let S : Set (Real × Real) := γ '' Set.Icc (0 : Real) 1
  have hpre : IsPreconnected S := isPreconnected_Icc.image γ hcont
  have hSK : Disjoint S (P3544T1BoundaryCarrier q) := by
    rw [Set.disjoint_left]
    rintro x ⟨t, ht, rfl⟩ hxK
    exact havoid t ht hxK
  have hzero : γ 0 ∈ S := ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hdisj := oldArcEvenOnPreconnected
    (P3544T1RayParity q) (P3544T1BoundaryCarrier q) S
    (P3544T1LocalParity q).2.1 (P3544T1LocalParity q).1 hpre hSK
    (γ 0) hzero hstart
  intro t ht hodd
  exact Set.disjoint_left.mp hdisj ⟨t, ht, rfl⟩ hodd

private theorem upperHalfplaneEven :
    (by
      classical
      exact
        ∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (ell : (Real × Real) →ₗ[Real] Real), ∀
            (H : Real), (∀ i, ell (q.vertex i) ≤ H) → (∀ (x : Real × Real), (H < ell x) → (x ∉
            P3544T1RayParity q)) ) := by
  classical
  intro m q ell H hbound x hx
  classical
  have hsegment : ∀ i y,
      y ∈ segment Real (q.vertex i) (q.vertex (i + 1)) → ell y ≤ H := by
    intro i y hy
    rw [segment_eq_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hbound i)
      (show 0 ≤ 1 - t by linarith [ht.2])
    have h2 := mul_le_mul_of_nonneg_left (hbound (i + 1)) ht.1
    nlinarith
  have hxC : x ∉ P3544T1BoundaryCarrier q := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact (not_le_of_gt hx) (hsegment i x hi)
  obtain ⟨d, hdv, hde⟩ :=
    (P3544T1LocalParity q).2.2.2.2.2.1 x hxC
  have use_direction : ∀ e : Real × Real, 0 ≤ ell e →
      (∀ i, e.1 * (q.vertex i - x).2 - e.2 * (q.vertex i - x).1 ≠ 0) →
      (∀ i, e.1 * (q.vertex (i + 1) - q.vertex i).2 -
        e.2 * (q.vertex (i + 1) - q.vertex i).1 ≠ 0) →
      x ∉ P3544T1RayParity q := by
    intro e he hev hee hxO
    have hno : ∀ i : Fin (m + 3), ¬ ∃ t : Real, 0 < t ∧
        x + t • e ∈ segment Real (q.vertex i) (q.vertex (i + 1)) := by
      intro i hi
      obtain ⟨t, ht, hseg⟩ := hi
      have hle := hsegment i (x + t • e) hseg
      rw [map_add, map_smul] at hle
      simp only [smul_eq_mul] at hle
      have hp := mul_nonneg ht.le he
      linarith
    have hset : {i : Fin (m + 3) | ∃ t : Real, 0 < t ∧
        x + t • e ∈ segment Real (q.vertex i) (q.vertex (i + 1))} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hno i
    have hchar := (P3544T1LocalParity q).2.2.2.2.2.2.1 x e hxC hev hee
    have hc := hchar.mp hxO
    rw [hset] at hc
    norm_num at hc
  by_cases hd : 0 ≤ ell d
  · exact use_direction d hd hdv hde
  · apply use_direction (-d)
    · rw [map_neg]
      linarith
    · intro i
      have heq : (-d).1 * (q.vertex i - x).2 -
          (-d).2 * (q.vertex i - x).1 =
          -(d.1 * (q.vertex i - x).2 - d.2 * (q.vertex i - x).1) := by
        simp only [Prod.fst_neg, Prod.snd_neg]
        ring
      rw [heq]
      exact neg_ne_zero.mpr (hdv i)
    · intro i
      have heq : (-d).1 * (q.vertex (i + 1) - q.vertex i).2 -
          (-d).2 * (q.vertex (i + 1) - q.vertex i).1 =
          -(d.1 * (q.vertex (i + 1) - q.vertex i).2 -
            d.2 * (q.vertex (i + 1) - q.vertex i).1) := by
        simp only [Prod.fst_neg, Prod.snd_neg]
        ring
      rw [heq]
      exact neg_ne_zero.mpr (hde i)

private theorem triangleHull :
    (by
      classical
      exact
        ∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), (m = 0) → (convexHull Real (Set.range
            q.vertex) = P3544T1RayParity q ∪ P3544T1BoundaryCarrier q) ) := by
  classical
  intro m q hm
  subst m
  exact (P3544T1TriangleRayGeometry q).2.1

private theorem middleNotSegment :
    (by
      classical
      exact
        ∀ {a : Real × Real}, ∀ {b : Real × Real}, ∀ {c : Real × Real},
            (P3381T1TriangleDeterminant ![a, b, c] ≠ 0) → (b ∉ segment Real a c) ) := by
  classical
  intro a b c hdet hb
  rw [segment_eq_image] at hb
  obtain ⟨t, ht, hpoint⟩ := hb
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  have hx' : b.1 = (1 - t) * a.1 + t * c.1 := by
    simpa [smul_eq_mul] using hx.symm
  have hy' : b.2 = (1 - t) * a.2 + t * c.2 := by
    simpa [smul_eq_mul] using hy.symm
  apply hdet
  simp only [P3381T1TriangleDeterminant, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  change (b.1 - a.1) * (c.2 - a.2) -
    (c.1 - a.1) * (b.2 - a.2) = 0
  rw [hx', hy']
  ring

private theorem prevIndexNe :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), (P3650T1CyclicChildren p D.a D.b) → (∀ {m : Nat}, ∀
            (i : Fin (m + 3)), i - 1 ≠ i) ) := by
  classical
  intro n p E D C m i h
  have hv := congrArg Fin.val h
  by_cases hi : i = 0
  · subst i
    simp at hv
  · have hsub := Fin.val_sub_one_of_ne_zero hi
    rw [hsub] at hv
    have hpos : 0 < i.val := by
      by_contra hnot
      have hz : i.val = 0 := by omega
      exact hi (Fin.ext hz)
    omega

private theorem nextIndexNe :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), (P3650T1CyclicChildren p D.a D.b) → (∀ {m : Nat}, ∀
            (i : Fin (m + 3)), i + 1 ≠ i) ) := by
  classical
  intro n p E D C m i h
  have hv := congrArg Fin.val h
  have hval : (i + 1).val = if i = Fin.last (m + 2) then 0 else i.val + 1 :=
    Fin.val_add_one i
  rw [hval] at hv
  split_ifs at hv with hi
  · have hvlast := congrArg Fin.val hi
    simp at hvlast
    omega
  · omega

private theorem nonincidentBall :
    (by
      classical
      exact
        ∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (i : Fin (m + 3)), ∃ r : Real, 0 < r ∧
            ∀ x ∈ Metric.ball (q.vertex i) r, x ∉ ⋃ j : Fin (m + 3), (if j ≠ i ∧ j + 1 ≠ i then
            segment Real (q.vertex j) (q.vertex (j + 1)) else ∅) ) := by
  classical
  intro m q i
  classical
  let J : Set (Fin (m + 3)) := {j | j ≠ i ∧ j + 1 ≠ i}
  let K : Set (Real × Real) := ⋃ j ∈ J,
    segment Real (q.vertex j) (q.vertex (j + 1))
  have hsegcompact (j : Fin (m + 3)) :
      IsCompact (segment Real (q.vertex j) (q.vertex (j + 1))) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (Set.toFinite J).isCompact_biUnion fun j hj => hsegcompact j
  have hvnot : q.vertex i ∉ K := by
    intro hvK
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hvK
    obtain ⟨hjJ, hvseg⟩ := Set.mem_iUnion.mp hj
    have hleft : q.vertex i ∈ segment Real (q.vertex i) (q.vertex (i + 1)) :=
      left_mem_segment Real _ _
    have hmem : q.vertex i ∈ segment Real (q.vertex i) (q.vertex (i + 1)) ∩
        segment Real (q.vertex j) (q.vertex (j + 1)) := ⟨hleft, hvseg⟩
    rw [q.edge_intersection i j hjJ.1.symm] at hmem
    have hend : (q.vertex i = q.vertex i ∨ q.vertex i = q.vertex (i + 1)) ∧
        (q.vertex i = q.vertex j ∨ q.vertex i = q.vertex (j + 1)) := by
      simpa only [Set.mem_ofPred_eq] using hmem
    rcases hend.2 with hji | hjnext
    · have heq : i = j := q.injective hji
      exact hjJ.1 heq.symm
    · have heq : i = j + 1 := q.injective hjnext
      exact hjJ.2 heq.symm
  have hopen : IsOpen Kᶜ := hKcompact.isClosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (q.vertex i) hvnot
  refine ⟨r, hr, ?_⟩
  intro x hx hmem
  have hxK : x ∈ K := by
    dsimp [K]
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    by_cases hjJ : j ≠ i ∧ j + 1 ≠ i
    · exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, by simpa [hjJ] using hj⟩⟩
    · simp [hjJ] at hj
  exact hball hx hxK

private theorem rightPreviousParent :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), (P3650T1CyclicChildren p D.a D.b) → (∀ {m : Nat}, ∀
            (q : P3381T1PolygonBoundary m), ∀ (a : Fin (m + 3)), ∀ (b : Fin (m +
            3)), ∀ (K : P3650T1CyclicChildren q a b), (K.rotation % (m + 3) = a.val) → (K.ir
                ⟨K.rightParameter + 1, by omega⟩ = a - 1))) := by
  classical
  intro n p E D C m q a b K hrot
  have hidx : (m + 2 + K.rotation) % (m + 3) = (a - 1).val := by
    by_cases ha0 : a.val = 0
    · have ha : a = 0 := Fin.ext ha0
      subst a
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show m + 2 < m + 3 by omega), hrot]
    · have hsub : (a - 1).val = a.val - 1 :=
        Fin.val_sub_one_of_ne_zero (by intro he; exact ha0 (congrArg Fin.val he))
      rw [hsub, Nat.add_mod, Nat.mod_eq_of_lt (show m + 2 < m + 3 by omega), hrot]
      have hsum : m + 2 + a.val = (m + 3) + (a.val - 1) := by omega
      rw [hsum]
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (show a.val - 1 < m + 3 by omega)]
  have hrotlast := List.getElem?_rotate
    (l := List.ofFn (fun i : Fin (m + 3) => i)) (n := K.rotation) (m := m+2) (by simp)
  have hsource : (List.ofFn (fun i : Fin (m + 3) => i))[(m+2 + K.rotation) % (m+3)]? =
      some (a-1) := by
    have hbound : (m+2 + K.rotation) % (m+3) <
        (List.ofFn (fun i : Fin (m+3) => i)).length := by simp; omega
    rw [List.getElem?_eq_getElem hbound, List.getElem_ofFn hbound]
    congr 1
    exact Fin.ext hidx
  have hlenBase : (List.ofFn (fun i : Fin (m+3) => i)).length = m+3 := by simp
  rw [hlenBase] at hrotlast
  rw [hsource] at hrotlast
  have hrotlast? :
      ((List.ofFn (fun i : Fin (m+3) => i)).rotate K.rotation).getLast? = some (a-1) := by
    rw [List.getLast?_eq_getElem?]
    have hlen : ((List.ofFn (fun i : Fin (m+3) => i)).rotate K.rotation).length = m+3 := by simp
    rw [show ((List.ofFn (fun i : Fin (m+3) => i)).rotate K.rotation).length - 1 = m+2 by omega]
    exact hrotlast
  have hparentlast : (a :: (K.u ++ b :: K.v)).getLast? = K.v.getLast? := by
    rw [show a :: (K.u ++ b :: K.v) = [a] ++ (K.u ++ b :: K.v) by simp]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    change (([b] ++ K.v).getLast? = K.v.getLast?)
    exact List.getLast?_append_of_ne_nil [b] (List.ne_nil_of_length_pos K.hv)
  rw [K.parent_order, hparentlast] at hrotlast?
  have hvlast : K.v.getLast? = some (a-1) := hrotlast?
  have hlenV : K.v.length = K.rightParameter + 1 := by
    have h := congrArg List.length K.right_order
    simp at h
    omega
  have hget : (List.ofFn K.ir)[K.rightParameter+1]? =
      some (K.ir ⟨K.rightParameter+1, by omega⟩) := by
    have hbnd : K.rightParameter+1 < (List.ofFn K.ir).length := by simp
    rw [List.getElem?_eq_getElem hbnd, List.getElem_ofFn hbnd]
  rw [K.right_order] at hget
  simp only [List.getElem?_cons_succ] at hget
  rw [List.getElem?_append_left (by omega : K.rightParameter < K.v.length)] at hget
  have hvget : K.v.getLast? = some (K.ir ⟨K.rightParameter+1, by omega⟩) := by
    rw [List.getLast?_eq_getElem?]
    rw [show K.v.length - 1 = K.rightParameter by omega]
    exact hget
  have hright : some (a - 1) = some (K.ir ⟨K.rightParameter+1, by omega⟩) :=
    hvlast.symm.trans hvget
  have hne : K.v ≠ [] := List.ne_nil_of_length_pos K.hv
  have hright' := hright
  exact (Option.some.inj hright').symm

private theorem hbaseChild :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (C.il 1 =
            D.a + 1) → ((∀ {m : Nat}, ∀ (i : Fin (m + 3)), (i - 1) + 2 = i + 1) → ((D.a = E.b -
            (1 : Fin (n + (3 : ℕ)))) → ((D.b = E.b + (1 : Fin (n + (3 : ℕ)))) → (C.u = [E.b] ∧
            C.leftParameter = 0)))) ) := by
  classical
  intro n p E D C leftFirstIndex cyclicStep ha hb
  have hN : 0 < n + 3 := by omega
  have hrotLen : (List.ofFn (fun i : Fin (n + 3) => i)).length = n + 3 := by simp
  have hrot0 := List.getElem?_rotate (l := List.ofFn (fun i : Fin (n + 3) => i))
    (n := C.rotation) (m := 0) (by simp)
  rw [C.parent_order] at hrot0
  conv_rhs at hrot0 =>
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by simp []))]
    rw [List.getElem_ofFn]
  simp only [List.length_cons, List.length_append, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le, getElem?_pos, List.getElem_cons_zero, zero_add, List.ofFn_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.length_ofFn, Option.some.injEq] at hrot0
  have hrLen : C.rotation % (List.ofFn (fun i : Fin (n + 3) => i)).length = D.a.val := by
    simpa only [hrotLen] using (congrArg Fin.val hrot0).symm
  have hr : C.rotation % (n + 3) = D.a.val := by simpa [hrotLen] using hrLen
  have hpos2 : 2 < n + 3 := by omega
  have hrot2 := List.getElem?_rotate (l := List.ofFn (fun i : Fin (n + 3) => i))
    (n := C.rotation) (m := 2) (by omega)
  rw [C.parent_order] at hrot2
  rw [hrotLen] at hrot2
  have habFin : D.a + 2 = D.b := by rw [ha, hb]; exact cyclicStep E.b
  have htwo : (2 : Fin (n + 3)).val = 2 := by norm_num
  have hmod2 : (2 + C.rotation) % (n + 3) =
      (2 + C.rotation % (n + 3)) % (n + 3) := by
    rw [Nat.add_mod]
    simp []
  rw [hr] at hmod2
  have hmodB : (2 + C.rotation) % (n + 3) = D.b.val := by
    calc
      (2 + C.rotation) % (n + 3) = (2 + D.a.val) % (n + 3) := hmod2
      _ = D.b.val := by
        have hv := congrArg Fin.val habFin
        simpa only [Fin.val_add, htwo, Nat.add_comm] using hv
  have hidxB : (⟨(2 + C.rotation % (List.ofFn (fun i : Fin (n + 3) => i)).length) %
      (List.ofFn (fun i : Fin (n + 3) => i)).length, by
        have hlt : (2 + C.rotation % (n + 3)) % (n + 3) < n + 3 := Nat.mod_lt _ hN
        simpa only [List.length_ofFn] using hlt⟩ : Fin (n + 3)) = D.b := by
    apply Fin.ext
    have hmod : (2 + C.rotation % (n + 3)) % (n + 3) =
        (2 + C.rotation) % (n + 3) := by
      have h2lt : 2 < n + 3 := by omega
      calc
        (2 + C.rotation % (n + 3)) % (n + 3) =
            (2 % (n + 3) + C.rotation % (n + 3)) % (n + 3) := by
          rw [Nat.mod_eq_of_lt h2lt]
        _ = (2 + C.rotation) % (n + 3) := by
          rw [Nat.add_mod]
          simp [Nat.mod_eq_of_lt h2lt]
    simpa only [List.length_ofFn] using hmod.trans hmodB
  have hsource : (List.ofFn (fun i : Fin (n + 3) => i))[
      (2 + C.rotation) % (n + 3)]? = some D.b := by
    have hidxlt : (2 + C.rotation) % (n + 3) <
        (List.ofFn (fun i : Fin (n + 3) => i)).length := by
      rw [hrotLen]
      exact Nat.mod_lt _ hN
    rw [List.getElem?_eq_getElem hidxlt]
    simp only [List.getElem_ofFn]
    apply congrArg some
    exact Fin.ext hmodB
  have hparLen : 2 < (D.a :: (C.u ++ D.b :: C.v)).length := by
    have hu := C.hu
    have hv := C.hv
    simp
    omega
  have hrot2' : (D.a :: (C.u ++ D.b :: C.v))[2]? = some D.b := by
    rw [hsource] at hrot2
    exact hrot2
  have hparentCell : (D.a :: (C.u ++ D.b :: C.v))[2]'hparLen = D.b := by
    rw [List.getElem?_eq_getElem hparLen] at hrot2'
    exact Option.some.inj hrot2'
  have hprefix : (D.a :: (C.u ++ D.b :: C.v))[2]'
      (by have hu := C.hu; simp; omega) =
      (D.a :: (C.u ++ [D.b]))[2]'(by have hu := C.hu; simp; omega) := by
    by_cases hu2 : 1 < C.u.length
    · simp only [List.getElem_cons_succ]
      rw [List.getElem_append_left (by omega : 1 < C.u.length)]
      rw [List.getElem_append_left (by omega : 1 < C.u.length)]
    · have hu1 : C.u.length = 1 := by have := C.hu; omega
      simp [hu1]
  have hleftCell : (D.a :: (C.u ++ [D.b]))[2]'
      (by have hu := C.hu; simp; omega) = D.b := hprefix.symm.trans hparentCell
  have huLen : C.u.length = 1 := by
    by_contra hn
    have hu2 : 1 < C.u.length := by have hu := C.hu; omega
    have hcell : (C.u)[1]'(by omega) = D.b := by
      simpa only [List.getElem_cons_succ,
        List.getElem_append_left (by omega : 1 < C.u.length)] using hleftCell
    have hnd : (D.a :: (C.u ++ [D.b])).Nodup := by
      rw [← C.left_order]
      exact List.nodup_ofFn_ofInjective C.il_injective
    have hlast : (D.a :: (C.u ++ [D.b]))[C.u.length + 1]'(by simp) = D.b := by
      simp [List.getElem_append_right]
    have hposeq := (hnd.getElem_inj_iff).mp (hleftCell.trans hlast.symm)
    omega
  have huval : (C.u)[0]'(by omega) = E.b := by
    have hleftn : 1 < C.leftParameter + 3 := by omega
    have hleftOrder := congrArg (fun l => l[1]?) C.left_order
    simp only [List.getElem?_ofFn, dite_eq_left hleftn] at hleftOrder
    simp only [List.getElem?_cons_succ,
      List.getElem?_append_left (by have := C.hu; omega : 0 < C.u.length)] at hleftOrder
    rw [List.getElem?_eq_getElem C.hu] at hleftOrder
    have hu0 : C.u[0]'(by omega) = C.il 1 := Option.some.inj hleftOrder.symm
    calc
      C.u[0]'(by omega) = C.il 1 := hu0
      _ = D.a + 1 := leftFirstIndex
      _ = (E.b - 1) + 1 := by rw [ha]
      _ = E.b := sub_add_cancel _ _
  constructor
  · apply List.ext_getElem
    · simp [huLen]
    · intro i hi₁ hi₂
      have hi : i = 0 := by omega
      simpa [hi] using huval
  · have hlen := congrArg List.length C.left_order
    simp [huLen] at hlen
    omega

private theorem hleftIndices :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (D.a = E.b
            - (1 : Fin (n + (3 : ℕ)))) → ((C.u = [E.b] ∧ C.leftParameter = 0) → (List.ofFn C.il =
                [D.a,
            E.b, D.b])) ) := by
  classical
  intro n p E D C ha hbaseChild
  rw [C.left_order]
  simp [hbaseChild.1, ha]

private theorem hleftIndexRange :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (List.ofFn
            C.il = [D.a, E.b, D.b]) → (Set.range C.il = {D.a, E.b, D.b}) ) := by
  classical
  intro n p E D C hleftIndices
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    have hj : C.il j ∈ List.ofFn C.il := List.mem_ofFn.mpr ⟨j, rfl⟩
    rw [hleftIndices] at hj
    simpa using hj
  · intro hi
    have hi' : i ∈ [D.a, E.b, D.b] := by simpa using hi
    rw [← hleftIndices] at hi'
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi'
    exact ⟨j, hj⟩

private theorem hleftVertexRange :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (D.a = E.b
            - (1 : Fin (n + (3 : ℕ)))) → ((D.b = E.b + (1 : Fin (n + (3 : ℕ)))) → ((Set.range
            C.il = {D.a, E.b, D.b}) → (Set.range C.left.vertex = {p.vertex (E.b - 1),
            p.vertex E.b, p.vertex (E.b + 1)}))) ) := by
  classical
  intro n p E D C ha hb hleftIndexRange
  rw [C.left_vertex, Set.range_comp, hleftIndexRange]
  rw [ha, hb]
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨E.b - 1, by simp, rfl⟩
    · exact ⟨E.b, by simp, rfl⟩
    · exact ⟨E.b + 1, by simp, rfl⟩

private theorem hseedRAt680 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let OR := P3544T1RayParity C.right
        (∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (ell : (Real × Real) →ₗ[Real] Real),
            ∀ (H : Real), (∀ i, ell (q.vertex i) ≤ H) → (∀ (x : Real × Real), (H < ell x) → (x ∉
            P3544T1RayParity q))) → ((∀ {a : Real × Real}, ∀ {b : Real × Real}, ∀
            {c : Real × Real}, (P3381T1TriangleDeterminant ![a, b, c] ≠ 0) → (b ∉ segment Real
            a c)) → ((∀ {m : Nat}, ∀ (i : Fin (m + 3)), i - 1 ≠ i) → ((∀ {m : Nat}, ∀ (i : Fin (m
            + 3)), i + 1 ≠ i) → ((D.a = E.b - (1 : Fin (n + (3 : ℕ)))) → ((D.b = E.b + (1 : Fin
            (n + (3 : ℕ)))) → ((Set.range C.il = {D.a, E.b, D.b}) → ((Set.range C.left.vertex =
            {p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)}) → (∃ x, x ∈ CL \ e ∧ x ∉
            OR)))))))) ) := by
  classical
  intro n p E D C e CL OR upperHalfplaneEven middleNotSegment prevIndexNe nextIndexNe ha hb
      hleftIndexRange hleftVertexRange
  refine ⟨p.vertex E.b, ?_, ?_⟩
  · constructor
    · change p.vertex E.b ∈ P3544T1BoundaryCarrier C.left
      change p.vertex E.b ∈ ⋃ i, segment Real (C.left.vertex i) (C.left.vertex (i + 1))
      have hmem : p.vertex E.b ∈ Set.range C.left.vertex := by
        rw [hleftVertexRange]
        simp
      obtain ⟨i, hi⟩ := hmem
      exact Set.mem_iUnion.mpr ⟨i, hi ▸ left_mem_segment Real _ _⟩
    · intro hdiag
      exact middleNotSegment (by simpa [ha, hb, P3381T1TriangleDeterminant] using
          E.nondegenerate) hdiag
  · let S : Finset Real := Finset.univ.image (fun i : Fin (C.rightParameter + 3) =>
      E.ell (C.right.vertex i))
    have hS : S.Nonempty := by
      refine ⟨E.ell (C.right.vertex 0), ?_⟩
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    let H := S.max' hS
    have hbound (i : Fin (C.rightParameter + 3)) : E.ell (C.right.vertex i) <
        E.ell (p.vertex E.b) := by
      have hirne : C.ir i ≠ E.b := by
        intro heq
        have hmemR : E.b ∈ Set.range C.ir := ⟨i, heq⟩
        have hmemL : E.b ∈ Set.range C.il := by rw [hleftIndexRange]; simp
        have hcommon : E.b ∈ ({D.a, D.b} : Set (Fin (n + 3))) := by
          rw [← C.common_indices]
          exact ⟨hmemL, hmemR⟩
        rcases (by simpa using hcommon) with hh | hh
        · have hp := prevIndexNe E.b
          have hh' : E.b = E.b - 1 := by rw [ha] at hh; exact hh
          exact hp hh'.symm
        · have hp := nextIndexNe E.b
          have hh' : E.b = E.b + 1 := by rw [hb] at hh; exact hh
          exact hp hh'.symm
      rw [C.right_vertex]
      exact E.maximum (C.ir i) hirne
    have hH : H < E.ell (p.vertex E.b) := by
      apply (Finset.max'_lt_iff S hS).2
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
      exact hbound i
    have hbelow (i : Fin (C.rightParameter + 3)) : E.ell (C.right.vertex i) ≤ H := by
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hB : H < E.ell (p.vertex E.b) := hH
    exact upperHalfplaneEven C.right E.ell H hbelow
      (p.vertex E.b) hB

private theorem hseedLAt728 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CR := P3544T1BoundaryCarrier C.right
        let OL := P3544T1RayParity C.left
        (∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), (m = 0) → (convexHull Real (Set.range
            q.vertex) = P3544T1RayParity q ∪ P3544T1BoundaryCarrier q)) → ((∀ {m : Nat}, ∀ (i
            : Fin (m + 3)), i - 1 ≠ i) → ((∀ {m : Nat}, ∀ (i : Fin (m + 3)), i + 1 ≠ i) → ((D.a =
            E.b - (1 : Fin (n + (3 : ℕ)))) → ((D.b = E.b + (1 : Fin (n + (3 : ℕ)))) → ((∀ (i :
            Fin (n + (3 : ℕ))), p.vertex i ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            {p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))} → i = E.b - (1 : Fin (n + (3 : ℕ))) ∨ i =
            E.b ∨ i = E.b + (1 : Fin (n + (3 : ℕ)))) → ((C.u = [E.b] ∧ C.leftParameter = 0) →
            ((Set.range C.il = {D.a, E.b, D.b}) → ((Set.range C.left.vertex =
            {p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)}) → (∃ x, x ∈ CR \ e ∧ x ∉
            OL))))))))) ) := by
  classical
  intro n p E D C e CR OL triangleHull prevIndexNe nextIndexNe ha hb hempty hbaseChild
      hleftIndexRange hleftVertexRange
  let j : Fin (n + 3) := C.ir 1
  have hjrange : j ∈ Set.range C.ir := ⟨1, rfl⟩
  have hjneA : j ≠ D.a := by
    intro heq
    have hfirst : C.ir 0 = D.b := by
      have h := congrArg List.head? C.right_order
      simpa using h
    have hlast : C.ir (Fin.last (C.rightParameter + 2)) = D.a := by
      have hlast? : (List.ofFn C.ir).getLast? =
          some (C.ir (Fin.last (C.rightParameter + 2))) := by
        rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
        rw [List.getLast_ofFn_succ]
      have h := congrArg List.getLast? C.right_order
      rw [hlast?] at h
      have hrhs : (D.b :: (C.v ++ [D.a])).getLast? = some D.a := by
        rw [show D.b :: (C.v ++ [D.a]) = [D.b] ++ (C.v ++ [D.a]) by simp]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        simp
      rw [hrhs] at h
      exact Option.some.inj h
    have hii : (1 : Fin (C.rightParameter + 3)) ≠ Fin.last (C.rightParameter + 2) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have heq' : C.ir 1 = C.ir (Fin.last (C.rightParameter + 2)) := heq.trans hlast.symm
    exact hii (C.ir_injective heq')
  have hjneB : j ≠ D.b := by
    intro heq
    have hfirst : C.ir 0 = D.b := by
      have h := congrArg List.head? C.right_order
      simpa using h
    have hi' : (1 : Fin (C.rightParameter + 3)) ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      norm_num at hv
    have heq' : C.ir 1 = C.ir 0 := heq.trans hfirst.symm
    exact hi' (C.ir_injective heq')
  have hjneTop : j ≠ E.b := by
    intro heq
    have hmemL : E.b ∈ Set.range C.il := by rw [hleftIndexRange]; simp
    have hcommon : E.b ∈ ({D.a, D.b} : Set (Fin (n + 3))) := by
      simpa only [C.common_indices] using
        (show E.b ∈ Set.range C.il ∩ Set.range C.ir from ⟨hmemL, ⟨1, heq⟩⟩)
    rcases (by simpa using hcommon) with hh | hh
    · have hp := prevIndexNe E.b
      have hh' : E.b = E.b - 1 := by rw [ha] at hh; exact hh
      exact hp hh'.symm
    · have hp := nextIndexNe E.b
      have hh' : E.b = E.b + 1 := by rw [hb] at hh; exact hh
      exact hp hh'.symm
  have hjnotHull : p.vertex j ∉ convexHull Real
      ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real)) := by
    intro hmem
    have hallowed := hempty j hmem
    rcases hallowed with h | h | h
    · exact hjneA (by simpa [ha] using h)
    · exact hjneTop h
    · exact hjneB (by simpa [ha, hb] using h)
  have hjnotDiag : p.vertex j ∉ e := by
    intro hmem
    have hseg : e ⊆ convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} : Set (Real × Real)) := by
      intro x hx
      exact segment_subset_convexHull (by simp [ha]) (by simp [hb]) hx
    exact hjnotHull (hseg hmem)
  refine ⟨p.vertex j, ?_, ?_⟩
  · constructor
    · change p.vertex j ∈ P3544T1BoundaryCarrier C.right
      change p.vertex j ∈ ⋃ i, segment Real (C.right.vertex i) (C.right.vertex (i + 1))
      have hmem : p.vertex j ∈ Set.range C.right.vertex := by
        refine ⟨1, ?_⟩
        rw [C.right_vertex]
        rfl
      obtain ⟨i, hi⟩ := hmem
      exact Set.mem_iUnion.mpr ⟨i, hi ▸ left_mem_segment Real _ _⟩
    · exact hjnotDiag
  · intro hodd
    have htri := triangleHull C.left hbaseChild.2
    have hnotHull : p.vertex j ∉ convexHull Real (Set.range C.left.vertex) := by
      rw [hleftVertexRange]
      simpa using hjnotHull
    have hsub : OL ⊆ convexHull Real (Set.range C.left.vertex) := by
      intro x hx
      rw [htri]
      exact Or.inl hx
    exact hnotHull (hsub hodd)

private theorem hdet :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        (vb.1 - va.1) * (vc.2 - va.2) - (vc.1 - va.1) * (vb.2 - va.2) ≠ 0 ) := by
  classical
  intro n p E va vb vc
  simpa [P3381T1TriangleDeterminant, va, vb, vc] using E.nondegenerate

private theorem hind :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ((vb.1 - va.1) * (vc.2 - va.2) - (vc.1 - va.1) * (vb.2 - va.2) ≠ 0) → (AffineIndependent
            Real vv) ) := by
  classical
  intro n p E va vb vc vv hdet
  apply (affineIndependent_iff_of_fintype Real vv).mpr
  intro z hz hsum i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hz] at hsum
  have hzsum : z 0 + z 1 + z 2 = 0 := by
    simpa [Fin.sum_univ_succ, ← add_assoc] using hz
  have hx : z 0 * va.1 + z 1 * vb.1 + z 2 * vc.1 = 0 := by
    simpa [Fin.sum_univ_succ, vv, ← add_assoc] using congrArg Prod.fst hsum
  have hy : z 0 * va.2 + z 1 * vb.2 + z 2 * vc.2 = 0 := by
    simpa [Fin.sum_univ_succ, vv, ← add_assoc] using congrArg Prod.snd hsum
  have hx' : z 1 * (vb.1 - va.1) + z 2 * (vc.1 - va.1) = 0 := by
    linear_combination hx - va.1 * hzsum
  have hy' : z 1 * (vb.2 - va.2) + z 2 * (vc.2 - va.2) = 0 := by
    linear_combination hy - va.2 * hzsum
  have hz1 : z 1 = 0 := by
    have hmul : z 1 * ((vb.1 - va.1) * (vc.2 - va.2) -
        (vc.1 - va.1) * (vb.2 - va.2)) = 0 := by
      linear_combination (vc.2 - va.2) * hx' - (vc.1 - va.1) * hy'
    exact (mul_eq_zero.mp hmul).resolve_right hdet
  have hz2 : z 2 = 0 := by
    have hmul : z 2 * ((vb.1 - va.1) * (vc.2 - va.2) -
        (vc.1 - va.1) * (vb.2 - va.2)) = 0 := by
      linear_combination (vb.1 - va.1) * hy' - (vb.2 - va.2) * hx'
    exact (mul_eq_zero.mp hmul).resolve_right hdet
  fin_cases i
  · change z 0 = 0
    linarith
  · change z 1 = 0
    exact hz1
  · change z 2 = 0
    exact hz2

private theorem hspan :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        (AffineIndependent Real vv) → (affineSpan Real (Set.range vv) = ⊤) ) := by
  classical
  intro n p E va vb vc vv hind
  apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  norm_num [Module.finrank_prod]

private theorem hcoord_nonneg :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (p.vertex D.b ∈ convexHull Real (Set.range A)) → (∀ i : Fin 3, 0 ≤ A.coord i (p.vertex
            D.b)) ) := by
  classical
  intro n p E D va vb vc vv hind hspan A htriangle
  have hmem := (Set.ext_iff.mp A.convexHull_eq_nonneg_coord) (p.vertex D.b)
  exact (hmem.mp htriangle)

private theorem hcoord_sum :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 0 (p.vertex D.b) + A.coord 1 (p.vertex D.b) + A.coord 2 (p.vertex D.b) = 1 ) := by
  classical
  intro n p E D va vb vc vv hind hspan A
  simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one (p.vertex D.b)

private theorem hside0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        ∀ (x : Real × Real), (x ∈ convexHull Real (Set.range A)) → ((A.coord 0 x = 0) → (x ∈
            segment Real vb vc)) ) := by
  classical
  intro n p E va vb vc vv hind hspan A x hx h0
  have h0b : A.coord 0 vb = 0 := by
    change A.coord 0 (A 1) = 0
    exact A.coord_apply_ne (by decide)
  have h0c : A.coord 0 vc = 0 := by
    change A.coord 0 (A 2) = 0
    exact A.coord_apply_ne (by decide)
  have hn := (Set.ext_iff.mp A.convexHull_eq_nonneg_coord x).mp hx
  have hsum : A.coord 0 x + A.coord 1 x + A.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one x
  rw [segment_eq_image_lineMap]
  refine ⟨A.coord 2 x, ⟨hn 2, ?_⟩, ?_⟩
  · linarith [hn 1]
  · apply A.ext_elem
    intro i
    rw [(A.coord i).apply_lineMap]
    rw [AffineMap.lineMap_apply_ring]
    fin_cases i
    · change (1 - A.coord 2 x) * A.coord 0 (A 1) +
          A.coord 2 x * A.coord 0 (A 2) = A.coord 0 x
      rw [A.coord_apply_ne (by decide : (0 : Fin 3) ≠ 1),
        A.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2)]
      simpa using h0.symm
    · change (1 - A.coord 2 x) * A.coord 1 (A 1) +
          A.coord 2 x * A.coord 1 (A 2) = A.coord 1 x
      rw [A.coord_apply_eq 1,
        A.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2)]
      linarith [h0, hsum]
    · change (1 - A.coord 2 x) * A.coord 2 (A 1) +
          A.coord 2 x * A.coord 2 (A 2) = A.coord 2 x
      rw [A.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1),
        A.coord_apply_eq 2]
      ring

private theorem hside2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        ∀ (x : Real × Real), (x ∈ convexHull Real (Set.range A)) → ((A.coord 2 x = 0) → (x ∈
            segment Real va vb)) ) := by
  classical
  intro n p E va vb vc vv hind hspan A x hx h2
  have h2a : A.coord 2 va = 0 := by
    change A.coord 2 (A 0) = 0
    exact A.coord_apply_ne (by decide)
  have h2b : A.coord 2 vb = 0 := by
    change A.coord 2 (A 1) = 0
    exact A.coord_apply_ne (by decide)
  have hn := (Set.ext_iff.mp A.convexHull_eq_nonneg_coord x).mp hx
  have hsum : A.coord 0 x + A.coord 1 x + A.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using A.sum_coord_apply_eq_one x
  rw [segment_eq_image_lineMap]
  refine ⟨A.coord 1 x, ⟨hn 1, ?_⟩, ?_⟩
  · linarith [hn 0]
  · apply A.ext_elem
    intro i
    rw [(A.coord i).apply_lineMap]
    rw [AffineMap.lineMap_apply_ring]
    fin_cases i
    · change (1 - A.coord 1 x) * A.coord 0 (A 0) +
          A.coord 1 x * A.coord 0 (A 1) = A.coord 0 x
      rw [A.coord_apply_eq 0,
        A.coord_apply_ne (by decide : (0 : Fin 3) ≠ 1)]
      linarith [h2, hsum]
    · change (1 - A.coord 1 x) * A.coord 1 (A 0) +
          A.coord 1 x * A.coord 1 (A 1) = A.coord 1 x
      rw [A.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
        A.coord_apply_eq 1]
      ring
    · change (1 - A.coord 1 x) * A.coord 2 (A 0) +
          A.coord 1 x * A.coord 2 (A 1) = A.coord 2 x
      rw [A.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
        A.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1)]
      simpa using h2.symm

private theorem hcoord0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), (D.a = E.b) → ((D.b ≠ E.b + (1 : Fin (n + (3 : ℕ)))) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (p.vertex D.b ∈ convexHull Real (Set.range A)) → ((∀ i : Fin 3, 0 ≤ A.coord i (p.vertex
            D.b)) → ((∀ (x : Real × Real), (x ∈ convexHull Real (Set.range A)) → ((A.coord 0 x =
            0) → (x ∈ segment Real vb vc))) → (0 < A.coord 0 (p.vertex D.b)))))) ) := by
  classical
  intro n p E D ha hbnext va vb vc vv hind hspan A htriangle hcoord_nonneg hside0
  have hn := hcoord_nonneg 0
  by_contra hnot
  have hz : A.coord 0 (p.vertex D.b) = 0 := by linarith
  have hs := hside0 (p.vertex D.b) htriangle hz
  have hi : D.b ≠ E.b := by
    intro he
    have := D.distinct
    rw [ha, he] at this
    exact this rfl
  have hp : p.vertex D.b ∈ segment Real (p.vertex E.b) (p.vertex (E.b + 1)) := by
    simpa [vb, vc] using hs
  have hpair : p.vertex D.b ∈ segment Real (p.vertex E.b) (p.vertex (E.b + 1)) ∩
      segment Real (p.vertex D.b) (p.vertex (D.b + 1)) :=
    ⟨hp, left_mem_segment Real _ _⟩
  rw [p.edge_intersection E.b D.b hi.symm] at hpair
  rcases hpair.1 with heq | heq
  · exact hi (p.injective heq)
  · exact hbnext (p.injective heq)

private theorem hcoord2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), (D.a = E.b) → ((D.b ≠ E.b - (1 : Fin (n + (3 : ℕ)))) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (p.vertex D.b ∈ convexHull Real (Set.range A)) → ((∀ i : Fin 3, 0 ≤ A.coord i (p.vertex
            D.b)) → ((∀ (x : Real × Real), (x ∈ convexHull Real (Set.range A)) → ((A.coord 2 x =
            0) → (x ∈ segment Real va vb))) → (0 < A.coord 2 (p.vertex D.b)))))) ) := by
  classical
  intro n p E D ha hbprev va vb vc vv hind hspan A htriangle hcoord_nonneg hside2
  have hn := hcoord_nonneg 2
  by_contra hnot
  have hz : A.coord 2 (p.vertex D.b) = 0 := by linarith
  have hs := hside2 (p.vertex D.b) htriangle hz
  have hi : E.b - 1 ≠ D.b := by
    intro he
    have := hbprev
    exact this he.symm
  have hp : p.vertex D.b ∈ segment Real (p.vertex (E.b - 1)) (p.vertex E.b) := by
    simpa [va, vb] using hs
  have hpair : p.vertex D.b ∈ segment Real (p.vertex (E.b - 1)) (p.vertex ((E.b - 1) + 1)) ∩
      segment Real (p.vertex D.b) (p.vertex (D.b + 1)) := by
    exact ⟨by simpa only [sub_add_cancel] using hp, left_mem_segment Real _ _⟩
  rw [p.edge_intersection (E.b - 1) D.b hi] at hpair
  rcases hpair.1 with heq | heq
  · exact hbprev (p.injective heq)
  · exact (by
      have heq' : p.vertex D.b = p.vertex E.b := by
        simpa only [sub_add_cancel] using heq
      have hd : D.b = E.b := p.injective heq'
      have hne : D.b ≠ E.b := by
        intro he
        have := D.distinct
        rw [ha, he] at this
        exact this rfl
      exact hne hd)

private theorem hrotvalAt999 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (some D.a =
            some ⟨((0 : ℕ) + C.rotation) % (List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).length,
            (by simp only [List.length_ofFn]; exact Nat.mod_lt _ (by omega))⟩) → (C.rotation % (n
                + 3) = D.a.val) ) := by
  classical
  intro n p E D C hrot0
  have heq := Option.some.inj hrot0
  have hv := congrArg Fin.val heq.symm
  simpa using hv

private theorem hrightLast :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), C.ir
            (Fin.last (C.rightParameter + 2)) = D.a ) := by
  classical
  intro n p E D C
  have hlast? : (List.ofFn C.ir).getLast? = some (C.ir (Fin.last _)) := by
    rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
    rw [List.getLast_ofFn_succ]
  have h := congrArg List.getLast? C.right_order
  rw [hlast?] at h
  have hrhs : (D.b :: (C.v ++ [D.a])).getLast? = some D.a := by
    rw [show D.b :: (C.v ++ [D.a]) = [D.b] ++ (C.v ++ [D.a]) by simp]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  rw [hrhs] at h
  exact Option.some.inj h

private theorem hrightFirst :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), C.ir 0 =
            D.b ) := by
  classical
  intro n p E D C
  have h := congrArg List.head? C.right_order
  simpa using h

private theorem hleftLast :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), C.il
            (Fin.last (C.leftParameter + 2)) = D.b ) := by
  classical
  intro n p E D C
  have hlast? : (List.ofFn C.il).getLast? = some (C.il (Fin.last _)) := by
    rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
    rw [List.getLast_ofFn_succ]
  have h := congrArg List.getLast? C.left_order
  rw [hlast?] at h
  have hrhs : (D.a :: (C.u ++ [D.b])).getLast? = some D.b := by
    rw [show D.a :: (C.u ++ [D.b]) = [D.a] ++ (C.u ++ [D.b]) by simp]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  rw [hrhs] at h
  exact Option.some.inj h

private theorem hleftFirst :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), C.il 0 =
            D.a ) := by
  classical
  intro n p E D C
  have h := congrArg List.head? C.left_order
  simpa using h

private theorem hcoordA0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 0 va = 1 ) := by
  classical
  intro n p E va vb vc vv hind hspan A
  change A.coord 0 (A 0) = 1
  exact A.coord_apply_eq 0

private theorem hcoordA2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 2 va = 0 ) := by
  classical
  intro n p E va vb vc vv hind hspan A
  change A.coord 2 (A 0) = 0
  exact A.coord_apply_ne (by decide)

private theorem hcoordB0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 0 vb = 0 ) := by
  classical
  intro n p E va vb vc vv hind hspan A
  change A.coord 0 (A 1) = 0
  exact A.coord_apply_ne (by decide)

private theorem hcoordB2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 2 vb = 0 ) := by
  classical
  intro n p E va vb vc vv hind hspan A
  change A.coord 2 (A 1) = 0
  exact A.coord_apply_ne (by decide)

private theorem hcoordC0 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 0 vc = 0 ) := by
  classical
  intro n p E va vb vc vv hind hspan A
  change A.coord 0 (A 2) = 0
  exact A.coord_apply_ne (by decide)

private theorem hcoordC2 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        A.coord 2 vc = 1 ) := by
  classical
  intro n p E va vb vc vv hind hspan A
  change A.coord 2 (A 2) = 1
  exact A.coord_apply_eq 2

private theorem hcoordLine :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        ∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), A.coord i
            (AffineMap.lineMap x y t) = (1 - t) * A.coord i x + t * A.coord i y ) := by
  classical
  intro n p E va vb vc vv hind hspan A i x y t
  rw [(A.coord i).apply_lineMap]
  rw [AffineMap.lineMap_apply_ring]

private theorem lineMapSub :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), AffineMap.lineMap x y t - x = t •
            (y - x) ) := by
  classical
  intro x y t
  apply Prod.ext <;> simp [AffineMap.lineMap_apply_ring, smul_eq_mul] <;> ring

private theorem hscaleAt1080 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        (0 < r) → (
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        δ₀ * (2 * (‖va - vb‖ + ‖vc - vb‖ + 1)) = r) ) := by
  classical
  intro n p E va vb vc r₀ r hr δ₀
  change (r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))) *
    (2 * (‖va - vb‖ + ‖vc - vb‖ + 1)) = r
  field_simp

private theorem hδaAt1084 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        (0 < δ₀) → ((δ₀ * (2 * (‖va - vb‖ + ‖vc - vb‖ + 1)) = r) → (δ * ‖va - vb‖ < r)) ) := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ hδ₀ hscale
  have hbound : ‖va - vb‖ < 2 * (‖va - vb‖ + ‖vc - vb‖ + 1) := by
    linarith only [norm_nonneg (va - vb), norm_nonneg (vc - vb)]
  calc
    δ * ‖va - vb‖ ≤ δ₀ * ‖va - vb‖ :=
      mul_le_mul_of_nonneg_right (min_le_left δ₀ (1/2)) (norm_nonneg _)
    _ < δ₀ * (2 * (‖va - vb‖ + ‖vc - vb‖ + 1)) :=
      mul_lt_mul_of_pos_left hbound hδ₀
    _ = r := hscale

private theorem hδcAt1093 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        (0 < δ₀) → ((δ₀ * (2 * (‖va - vb‖ + ‖vc - vb‖ + 1)) = r) → (δ * ‖vc - vb‖ < r)) ) := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ hδ₀ hscale
  have hbound : ‖vc - vb‖ < 2 * (‖va - vb‖ + ‖vc - vb‖ + 1) := by
    linarith only [norm_nonneg (va - vb), norm_nonneg (vc - vb)]
  calc
    δ * ‖vc - vb‖ ≤ δ₀ * ‖vc - vb‖ :=
      mul_le_mul_of_nonneg_right (min_le_left δ₀ (1/2)) (norm_nonneg _)
    _ < δ₀ * (2 * (‖va - vb‖ + ‖vc - vb‖ + 1)) :=
      mul_lt_mul_of_pos_left hbound hδ₀
    _ = r := hscale

private theorem hUdiffAt1102 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), AffineMap.lineMap x y t - x = t
            • (y - x)) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        U - vb = (-δ) • (va - vb)) ) := by
  classical
  intro n p E va vb vc lineMapSub r₀ r δ₀ δ U
  change AffineMap.lineMap vb va (-δ) - vb = (-δ) • (va - vb)
  exact lineMapSub vb va (-δ)

private theorem hXdiffAt1105 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), AffineMap.lineMap x y t - x = t
            • (y - x)) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        X - vb = δ • (vc - vb)) ) := by
  classical
  intro n p E va vb vc lineMapSub r₀ r δ₀ δ X
  change AffineMap.lineMap vb vc δ - vb = δ • (vc - vb)
  exact lineMapSub vb vc δ

private theorem hUballAt1108 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        (0 < δ) → ((δ * ‖va - vb‖ < r) → ((U - vb = (-δ) • (va - vb)) → (U ∈ Metric.ball vb r)))
            ) := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ U hδ hδa hUdiff
  rw [Metric.mem_ball, dist_eq_norm, hUdiff, norm_smul]
  simp only [Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
  exact hδa

private theorem hXballAt1112 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        (0 < δ) → ((δ * ‖vc - vb‖ < r) → ((X - vb = δ • (vc - vb)) → (X ∈ Metric.ball vb r))) )
            := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ X hδ hδc hXdiff
  rw [Metric.mem_ball, dist_eq_norm, hXdiff, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos hδ]
  exact hδc

private theorem hUhighAt1116 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀
            {m : Nat}, ∀ (i : Fin (m + 3)), i - 1 ≠ i) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        (0 < δ) → ((U - vb = (-δ) • (va - vb)) → (E.ell vb < E.ell U))) ) := by
  classical
  intro n p E prevIndexNe va vb vc r₀ r δ₀ δ U hδ hUdiff
  have hmap : E.ell (U - vb) = E.ell U - E.ell vb := map_sub E.ell U vb
  rw [hUdiff, map_smul] at hmap
  have hprev := E.maximum (E.b - 1) (prevIndexNe E.b)
  have hlin : E.ell (va - vb) = E.ell va - E.ell vb := map_sub E.ell va vb
  rw [hlin] at hmap
  simp only [smul_eq_mul] at hmap
  have hprod : 0 < (-δ) * (E.ell va - E.ell vb) :=
    mul_pos_of_neg_of_neg (neg_lt_zero.mpr hδ) (sub_neg.mpr hprev)
  have hmap' : E.ell U - E.ell vb = (-δ) * (E.ell va - E.ell vb) := by
    exact hmap.symm
  linarith only [hmap', hprod]

private theorem hbelowAt1128 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let vb := p.vertex E.b
        ∀ i, E.ell (C.right.vertex i) ≤ E.ell vb ) := by
  classical
  intro n p E D C vb i
  rw [C.right_vertex]
  change E.ell (p.vertex (C.ir i)) ≤ E.ell (p.vertex E.b)
  by_cases hi : C.ir i = E.b
  · simp [hi]
  · have hm := E.maximum (C.ir i) hi
    simpa [vb] using le_of_lt hm

private theorem hU0At1138 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 0 va = 1) → ((A.coord 0 vb = 0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        A.coord 0 U = -δ))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordA0 hcoordB0 hcoordLine r₀ r δ₀ δ U
  rw [hcoordLine 0 vb va (-δ), hcoordB0, hcoordA0]
  ring

private theorem hU2At1141 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 2 va = 0) → ((A.coord 2 vb = 0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        A.coord 2 U = 0))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordA2 hcoordB2 hcoordLine r₀ r δ₀ δ U
  rw [hcoordLine 2 vb va (-δ), hcoordB2, hcoordA2]
  ring

private theorem hX0At1144 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 0 vb = 0) → ((A.coord 0 vc = 0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        A.coord 0 X = 0))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordB0 hcoordC0 hcoordLine r₀ r δ₀ δ X
  rw [hcoordLine 0 vb vc δ, hcoordB0, hcoordC0]
  ring

private theorem hX2At1147 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 2 vb = 0) → ((A.coord 2 vc = 1) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        A.coord 2 X = δ))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordB2 hcoordC2 hcoordLine r₀ r δ₀ δ X
  rw [hcoordLine 2 vb vc δ, hcoordB2, hcoordC2]
  ring

private theorem hrightCenterAt1156 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (D.a = E.b)
            → (
        let vb := p.vertex E.b
        (C.ir (Fin.last (C.rightParameter + 2)) = D.a) → (C.right.vertex (Fin.last
            (C.rightParameter + 2)) =
            vb)) ) := by
  classical
  intro n p E D C ha vb hrightLast
  rw [C.right_vertex]
  simp [hrightLast, ha, vb]

private theorem hrightZero :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (C.ir 0 =
            D.b) → (C.right.vertex 0 = p.vertex D.b) ) := by
  classical
  intro n p E D C hrightFirst
  rw [C.right_vertex]
  simp [hrightFirst]

private theorem hrightWrap :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), Fin.last
            (C.rightParameter + 2) + 1 = (0 : Fin (C.rightParameter + 3)) ) := by
  classical
  intro n p E D C
  apply Fin.ext
  simp

private theorem hrightIncidentPrevAt1166 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let va := p.vertex (E.b - 1)
        (C.ir ⟨C.rightParameter+1, by omega⟩ = E.b - 1) → (C.right.vertex ⟨C.rightParameter + 1,
            by omega⟩ = va)) := by
  classical
  intro n p E D C va hrightPrev
  rw [C.right_vertex]
  exact congrArg p.vertex hrightPrev

private theorem hballPathAt1170 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
        (U ∈ Metric.ball vb r) → ((X ∈ Metric.ball vb r) → (∀ (t : Real), (t ∈ Set.Icc (0 : Real)
            1) → (γ t ∈ Metric.ball vb r))) ) := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ U X γ hUball hXball t ht
  have hseg := (convex_ball vb r).segment_subset hUball hXball
  apply hseg
  rw [segment_eq_image_lineMap]
  exact ⟨t, ht, rfl⟩

private theorem havoidAt1176 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let CR := P3544T1BoundaryCarrier C.right
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (0 < A.coord 0 (p.vertex D.b)) → ((A.coord 0 va = 1) → ((A.coord 2 va = 0) → ((A.coord 0
            vb = 0) → ((A.coord 2 vb =
            0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), A.coord
                i (AffineMap.lineMap x y t) = (1 - t) * A.coord i x + t * A.coord i
            y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        (∀ x ∈ Metric.ball (C.right.vertex (Fin.last (C.rightParameter + (2 : ℕ)))) r, x ∉ ⋃
            (j : Fin (C.rightParameter + (3 : ℕ))), if j ≠ Fin.last (C.rightParameter + (2 : ℕ))
                ∧ j + (1 : Fin
            (C.rightParameter + (3 : ℕ))) ≠ Fin.last (C.rightParameter + (2 : ℕ)) then segment ℝ
            (C.right.vertex j) (C.right.vertex (j + (1 : Fin (C.rightParameter + (3 : ℕ))))) else
                ∅) → (
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
        (0 < δ) → ((∀ (t : Real), A.coord 0 (γ t) = -(1-t)*δ) → ((∀ (t : Real), A.coord 2 (γ t) =
            t*δ) → ((C.right.vertex (Fin.last (C.rightParameter
            + 2)) = vb) → ((C.right.vertex 0 = p.vertex D.b) → ((Fin.last (C.rightParameter + 2)
                + 1 =
                (0 : Fin (C.rightParameter + 3))) → ((C.right.vertex ⟨C.rightParameter
            + 1, by omega⟩ = va) → ((∀ (t : Real), (t ∈ Set.Icc (0 : Real) 1) → (γ t ∈
            Metric.ball vb r)) → (∀ t ∈ Set.Icc (0 : Real) 1, γ t ∉ CR)))))))))))))))) := by
  classical
  intro n p E D C CR va vb vc vv hind hspan A hcoord0 hcoordA0 hcoordA2 hcoordB0 hcoordB2
      hcoordLine r₀ r hnear δ₀ δ U X γ hδ hγ0 hγ2 hrightCenter hrightZero hrightWrap
      hrightIncidentPrev hballPath t ht hcarrier
  have hnear' := hnear (γ t) (by rw [hrightCenter]; exact hballPath t ht)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcarrier
  have hinc : i = Fin.last (C.rightParameter + 2) ∨
      i + 1 = Fin.last (C.rightParameter + 2) := by
    by_contra hn
    have hnot : i ≠ Fin.last (C.rightParameter + 2) ∧
        i + 1 ≠ Fin.last (C.rightParameter + 2) := by
      constructor
      · intro he
        exact hn (Or.inl he)
      · intro he
        exact hn (Or.inr he)
    have hsegment :
        γ t ∈ (if i ≠ Fin.last (C.rightParameter + 2) ∧
            i + 1 ≠ Fin.last (C.rightParameter + 2) then
          segment Real (C.right.vertex i) (C.right.vertex (i + 1)) else ∅) := by
      rw [ite_eq_left hnot]
      exact hi
    exact hnear' (Set.mem_iUnion.mpr ⟨i, hsegment⟩)
  rcases hinc with htopEdge | hprevEdge
  · subst i
    have hseg : γ t ∈ segment Real vb (p.vertex D.b) := by
      simpa [hrightCenter, hrightWrap, hrightZero] using hi
    rw [segment_eq_image_lineMap] at hseg
    obtain ⟨s, hs, heq⟩ := hseg
    have h0 := congrArg (A.coord 0) heq
    rw [hγ0, hcoordLine 0 vb (p.vertex D.b) s, hcoordB0] at h0
    have hprod : 0 ≤ s * A.coord 0 (p.vertex D.b) :=
      mul_nonneg hs.1 hcoord0.le
    have hγle : -(1-t)*δ ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hδ.le
      linarith [ht.2]
    have hsprod : s * A.coord 0 (p.vertex D.b) = 0 := by
      linarith only [h0, hγle, hprod]
    have hmul : (1-t)*δ = 0 := by linarith only [h0, hsprod]
    have hs0 : s = 0 := (mul_eq_zero.mp hsprod).resolve_right (ne_of_gt hcoord0)
    have ht1 : t = 1 := by
      have ht' := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hδ)
      linarith only [ht']
    have h2 := congrArg (A.coord 2) heq
    rw [hγ2, hcoordLine 2 vb (p.vertex D.b) s, hcoordB2] at h2
    subst s
    rw [ht1] at h2
    simp at h2
    exact (ne_of_gt hδ) h2.symm
  · have hidx : i = ⟨C.rightParameter + 1, by omega⟩ := by
      have hv0 := congrArg Fin.val hprevEdge
      have hnotlast : i ≠ Fin.last (C.rightParameter + 2) := by
        intro he
        rw [he, Fin.val_add_one] at hv0
        simp at hv0
      have hv : i.val + 1 = C.rightParameter + 2 := by
        simpa [Fin.val_add_one, hnotlast] using hv0
      have hv' : i.val + 1 = (C.rightParameter + 1) + 1 := by
        simpa [Nat.add_assoc] using hv
      exact Fin.ext (Nat.add_right_cancel hv')
    rw [hidx] at hi
    have hnextLast :
        (⟨C.rightParameter + 1, by omega⟩ : Fin (C.rightParameter + 3)) + 1 =
          Fin.last (C.rightParameter + 2) := by
      apply Fin.ext
      have hne : (⟨C.rightParameter + 1, by omega⟩ : Fin (C.rightParameter + 3)) ≠
          Fin.last (C.rightParameter + 2) := by
        intro he
        have hv := congrArg Fin.val he
        simp at hv
      rw [Fin.val_add_one]
      simp [hne]
    have hseg : γ t ∈ segment Real va vb := by
      simpa [hrightIncidentPrev, hrightCenter, hnextLast] using hi
    rw [segment_eq_image_lineMap] at hseg
    obtain ⟨s, hs, heq⟩ := hseg
    have h2 := congrArg (A.coord 2) heq
    rw [hγ2, hcoordLine 2 va vb s, hcoordA2, hcoordB2] at h2
    have ht0 : t = 0 := by
      have htprod : t * δ = 0 := by simpa using h2
      exact (mul_eq_zero.mp htprod).resolve_right (ne_of_gt hδ)
    have h0 := congrArg (A.coord 0) heq
    rw [hγ0, hcoordLine 0 va vb s, hcoordA0, hcoordB0] at h0
    rw [ht0] at h0
    have hnonneg : 0 ≤ 1-s := by linarith only [hs.2]
    have h0' : -δ = 1-s := by simpa using h0.symm
    have : -δ < 0 := neg_lt_zero.mpr hδ
    linarith only [h0', hnonneg, this]

private theorem hXnotAt1265 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let OR := P3544T1RayParity C.right
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb va (-δ)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
        (∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), γ t ∉ P3544T1RayParity C.right) → (X ∉ OR) ) := by
  classical
  intro n p E D C OR va vb vc r₀ r δ₀ δ U X γ hXeven
  have h := hXeven 1 ⟨by norm_num, by norm_num⟩
  simpa [γ, AffineMap.lineMap_apply_one] using h

private theorem hleftStart :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (D.a = E.b)
            → (
        let vb := p.vertex E.b
        (C.il 0 = D.a) → (C.left.vertex 0 = vb)) ) := by
  classical
  intro n p E D C ha vb hleftFirst
  rw [C.left_vertex]
  simp [hleftFirst, ha, vb]

private theorem hleftStartNext :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let vc := p.vertex (E.b + 1)
        (C.il 1 = E.b + 1) → (C.left.vertex 1 = vc) ) := by
  classical
  intro n p E D C vc hleftNext
  rw [C.left_vertex]
  simp [hleftNext, vc]

private theorem hXcarrierAt1274 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let CL := P3544T1BoundaryCarrier C.left
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        (0 < δ) → ((δ < 1) → ((C.left.vertex 0 = vb) → ((C.left.vertex 1 = vc) → (X ∈ CL)))) ) := by
  classical
  intro n p E D C CL va vb vc r₀ r δ₀ δ X hδ hδlt1 hleftStart hleftStartNext
  change X ∈ P3544T1BoundaryCarrier C.left
  change X ∈ ⋃ i, segment Real (C.left.vertex i) (C.left.vertex (i + 1))
  refine Set.mem_iUnion.mpr ⟨0, ?_⟩
  simp only [zero_add]
  rw [hleftStart, hleftStartNext, segment_eq_image_lineMap]
  exact ⟨δ, ⟨le_of_lt hδ, le_of_lt hδlt1⟩, rfl⟩

private theorem hXnotDiagAt1281 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        (D.a = E.b) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (0 < A.coord 0 (p.vertex D.b)) → ((A.coord 0 vb = 0) → ((A.coord 2 vb = 0) → ((∀ (i : Fin
            3), ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), A.coord i
            (AffineMap.lineMap x y t) = (1 - t) * A.coord i x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb vc δ
        (0 < δ) → ((A.coord 0 X = 0) → ((A.coord 2 X = δ) → (X ∉ e)))))))) ) := by
  classical
  intro n p E D e ha va vb vc vv hind hspan A hcoord0 hcoordB0 hcoordB2 hcoordLine r₀ r δ₀ δ X hδ
      hX0 hX2 hmem
  change X ∈ segment Real (p.vertex D.a) (p.vertex D.b) at hmem
  rw [ha] at hmem
  change X ∈ segment Real vb (p.vertex D.b) at hmem
  rw [segment_eq_image_lineMap] at hmem
  obtain ⟨s, hs, heq⟩ := hmem
  have h0 := congrArg (A.coord 0) heq
  rw [hcoordLine 0 vb (p.vertex D.b) s, hcoordB0, hX0] at h0
  have h0' : s * A.coord 0 (p.vertex D.b) = 0 := by
    simpa only [mul_zero, zero_add] using h0
  have hs0 : s = 0 :=
    (mul_eq_zero.mp h0').resolve_right (ne_of_gt hcoord0)
  have h2 := congrArg (A.coord 2) heq
  rw [hcoordLine 2 vb (p.vertex D.b) s, hcoordB2, hX2] at h2
  rw [hs0] at h2
  simp at h2
  exact (ne_of_gt hδ) h2.symm

private theorem hUdiffAt1346 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), AffineMap.lineMap x y t - x = t
            • (y - x)) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        U - vb = (-δ) • (vc - vb)) ) := by
  classical
  intro n p E va vb vc lineMapSub r₀ r δ₀ δ U
  change AffineMap.lineMap vb vc (-δ) - vb = (-δ) • (vc - vb)
  exact lineMapSub vb vc (-δ)

private theorem hXdiffAt1349 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), AffineMap.lineMap x y t - x = t
            • (y - x)) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb va δ
        X - vb = δ • (va - vb)) ) := by
  classical
  intro n p E va vb vc lineMapSub r₀ r δ₀ δ X
  change AffineMap.lineMap vb va δ - vb = δ • (va - vb)
  exact lineMapSub vb va δ

private theorem hUballAt1352 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        (0 < δ) → ((δ * ‖vc - vb‖ < r) → ((U - vb = (-δ) • (vc - vb)) → (U ∈ Metric.ball vb r)))
            ) := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ U hδ hδc hUdiff
  rw [Metric.mem_ball, dist_eq_norm, hUdiff, norm_smul]
  simp only [Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
  exact hδc

private theorem hXballAt1356 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb va δ
        (0 < δ) → ((δ * ‖va - vb‖ < r) → ((X - vb = δ • (va - vb)) → (X ∈ Metric.ball vb r))) )
            := by
  classical
  intro n p E va vb vc r₀ r δ₀ δ X hδ hδa hXdiff
  rw [Metric.mem_ball, dist_eq_norm, hXdiff, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos hδ]
  exact hδa

private theorem hUhighAt1360 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), (∀
            {m : Nat}, ∀ (i : Fin (m + 3)), i + 1 ≠ i) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        (0 < δ) → ((U - vb = (-δ) • (vc - vb)) → (E.ell vb < E.ell U))) ) := by
  classical
  intro n p E nextIndexNe va vb vc r₀ r δ₀ δ U hδ hUdiff
  have hmap : E.ell (U - vb) = E.ell U - E.ell vb := map_sub E.ell U vb
  rw [hUdiff, map_smul] at hmap
  have hnext := E.maximum (E.b + 1) (nextIndexNe E.b)
  have hlin : E.ell (vc - vb) = E.ell vc - E.ell vb := map_sub E.ell vc vb
  rw [hlin] at hmap
  simp only [smul_eq_mul] at hmap
  have hprod : 0 < (-δ) * (E.ell vc - E.ell vb) :=
    mul_pos_of_neg_of_neg (neg_lt_zero.mpr hδ) (sub_neg.mpr hnext)
  have hmap' : E.ell U - E.ell vb = (-δ) * (E.ell vc - E.ell vb) :=
    hmap.symm
  linarith only [hmap', hprod]

private theorem hbelowAt1372 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let vb := p.vertex E.b
        ∀ i, E.ell (C.left.vertex i) ≤ E.ell vb ) := by
  classical
  intro n p E D C vb i
  rw [C.left_vertex]
  change E.ell (p.vertex (C.il i)) ≤ E.ell (p.vertex E.b)
  by_cases hi : C.il i = E.b
  · simp [hi]
  · have hm := E.maximum (C.il i) hi
    simpa [vb] using le_of_lt hm

private theorem hU0At1382 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 0 vb = 0) → ((A.coord 0 vc = 0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        A.coord 0 U = 0))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordB0 hcoordC0 hcoordLine r₀ r δ₀ δ U
  rw [hcoordLine 0 vb vc (-δ), hcoordB0, hcoordC0]
  ring

private theorem hU2At1385 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 2 vb = 0) → ((A.coord 2 vc = 1) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        A.coord 2 U = -δ))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordB2 hcoordC2 hcoordLine r₀ r δ₀ δ U
  rw [hcoordLine 2 vb vc (-δ), hcoordB2, hcoordC2]
  ring

private theorem hX0At1388 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 0 va = 1) → ((A.coord 0 vb = 0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb va δ
        A.coord 0 X = δ))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordA0 hcoordB0 hcoordLine r₀ r δ₀ δ X
  rw [hcoordLine 0 vb va δ, hcoordB0, hcoordA0]
  ring

private theorem hX2At1391 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (A.coord 2 va = 0) → ((A.coord 2 vb = 0) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y :
            Real × Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i
            x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb va δ
        A.coord 2 X = 0))) ) := by
  classical
  intro n p E va vb vc vv hind hspan A hcoordA2 hcoordB2 hcoordLine r₀ r δ₀ δ X
  rw [hcoordLine 2 vb va δ, hcoordB2, hcoordA2]
  ring

private theorem hleftCenter :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (D.a = E.b)
            → (
        let vb := p.vertex E.b
        (C.il 0 = D.a) → (C.left.vertex 0 = vb)) ) := by
  classical
  intro n p E D C ha vb hleftFirst
  rw [C.left_vertex]
  simp [hleftFirst, ha, vb]

private theorem hleftOne :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let vc := p.vertex (E.b + 1)
        (C.il 1 = E.b + 1) → (C.left.vertex 1 = vc) ) := by
  classical
  intro n p E D C vc hleftNext
  rw [C.left_vertex]
  simp [hleftNext, vc]

private theorem hleftWrap :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), Fin.last
            (C.leftParameter + 2) + 1 = (0 : Fin (C.leftParameter + 3)) ) := by
  classical
  intro n p E D C
  apply Fin.ext
  simp

private theorem hleftEnd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (C.il
            (Fin.last (C.leftParameter + 2)) = D.b) → (C.left.vertex (Fin.last (C.leftParameter +
                2)) =
            p.vertex D.b) ) := by
  classical
  intro n p E D C hleftLast
  rw [C.left_vertex]
  simp [hleftLast]

private theorem hballPathAt1412 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        let X : Real × Real := AffineMap.lineMap vb va δ
        let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
        (U ∈ Metric.ball vb r) → ((X ∈ Metric.ball vb r) → ((C.left.vertex 0 = vb) → (∀ (t :
            Real), (t ∈ Set.Icc (0 : Real) 1) → (γ t ∈ Metric.ball (C.left.vertex 0) r)))) ) := by
  classical
  intro n p E D C va vb vc r₀ r δ₀ δ U X γ hUball hXball hleftCenter t ht
  have hseg := (convex_ball vb r).segment_subset hUball hXball
  rw [hleftCenter]
  apply hseg
  rw [segment_eq_image_lineMap]
  exact ⟨t, ht, rfl⟩

private theorem havoidAt1419 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let CL := P3544T1BoundaryCarrier C.left
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (0 < A.coord 2 (p.vertex D.b)) → ((A.coord 0 vb = 0) → ((A.coord 2 vb = 0) → ((A.coord 0
            vc = 0) → ((A.coord 2 vc = 1) → ((∀ (i : Fin 3), ∀ (x : Real × Real), ∀ (y : Real ×
            Real), ∀ (t : Real), A.coord i (AffineMap.lineMap x y t) = (1 - t) * A.coord i x + t
            * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        (∀ x ∈ Metric.ball (C.left.vertex (0 : Fin (C.leftParameter + (3 : ℕ)))) r, x ∉ ⋃ (j : Fin
            (C.leftParameter + (3 : ℕ))), if j ≠ (0 : Fin (C.leftParameter + (3 : ℕ))) ∧ j + (1 :
                Fin (C.leftParameter
            + (3 : ℕ))) ≠ (0 : Fin (C.leftParameter + (3 : ℕ))) then segment ℝ (C.left.vertex j)
            (C.left.vertex (j + (1 : Fin (C.leftParameter + (3 : ℕ))))) else ∅) → (
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        let X : Real × Real := AffineMap.lineMap vb va δ
        let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
        (0 < δ) → ((∀ (t : Real), A.coord 0 (γ t) = t*δ) → ((∀ (t : Real), A.coord 2 (γ t) =
            -(1-t)*δ) → ((C.left.vertex 0 = vb) → ((C.left.vertex 1 = vc) → ((Fin.last
                (C.leftParameter
            + 2) + 1 = (0 : Fin (C.leftParameter + 3))) → ((C.left.vertex (Fin.last
                (C.leftParameter + 2)) =
            p.vertex D.b) → ((∀ (t : Real), (t ∈ Set.Icc (0 : Real) 1) → (γ t ∈ Metric.ball
            (C.left.vertex 0) r)) → (∀ t ∈ Set.Icc (0 : Real) 1, γ t ∉ CL))))))))))))))) ) := by
  classical
  intro n p E D C CL va vb vc vv hind hspan A hcoord2 hcoordB0 hcoordB2 hcoordC0 hcoordC2
      hcoordLine r₀ r hnear δ₀ δ U X γ hδ hγ0 hγ2 hleftCenter hleftOne hleftWrap hleftEnd
      hballPath t ht hcarrier
  have hnear' := hnear (γ t) (hballPath t ht)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcarrier
  have hinc : i = 0 ∨ i + 1 = 0 := by
    by_contra hn
    have hnot : i ≠ 0 ∧ i + 1 ≠ 0 := by
      constructor
      · intro he
        exact hn (Or.inl he)
      · intro he
        exact hn (Or.inr he)
    have hsegment :
        γ t ∈ (if i ≠ 0 ∧ i + 1 ≠ 0 then
          segment Real (C.left.vertex i) (C.left.vertex (i + 1)) else ∅) := by
      rw [ite_eq_left hnot]
      exact hi
    exact hnear' (Set.mem_iUnion.mpr ⟨i, hsegment⟩)
  rcases hinc with hfirstEdge | hlastEdge
  · subst i
    have hseg : γ t ∈ segment Real vb vc := by
      simpa [hleftCenter, hleftOne] using hi
    rw [segment_eq_image_lineMap] at hseg
    obtain ⟨s, hs, heq⟩ := hseg
    have h0 := congrArg (A.coord 0) heq
    rw [hγ0, hcoordLine 0 vb vc s, hcoordB0, hcoordC0] at h0
    have ht0 : t = 0 := by
      have htprod : t * δ = 0 := by
        simpa only [mul_zero, zero_mul, zero_add] using h0.symm
      exact (mul_eq_zero.mp htprod).resolve_right (ne_of_gt hδ)
    have h2 := congrArg (A.coord 2) heq
    rw [hγ2, hcoordLine 2 vb vc s, hcoordB2, hcoordC2] at h2
    rw [ht0] at h2
    have h2' : s = -δ := by
      norm_num at h2
      exact h2
    have hsnonneg : 0 ≤ s := hs.1
    have hδneg : -δ < 0 := neg_lt_zero.mpr hδ
    linarith only [h2', hsnonneg, hδneg]
  · have hidx : i = Fin.last (C.leftParameter + 2) := by
      have hv := congrArg Fin.val hlastEdge
      rw [Fin.val_add_one] at hv
      split_ifs at hv with hwrap
      · exact hwrap
      · simp at hv
    rw [hidx] at hi
    have hseg : γ t ∈ segment Real (p.vertex D.b) vb := by
      simpa [hleftEnd, hleftWrap, hleftCenter] using hi
    rw [segment_eq_image_lineMap] at hseg
    obtain ⟨s, hs, heq⟩ := hseg
    have h2 := congrArg (A.coord 2) heq
    rw [hγ2, hcoordLine 2 (p.vertex D.b) vb s, hcoordB2] at h2
    have hprod : 0 ≤ (1-s) * A.coord 2 (p.vertex D.b) :=
      mul_nonneg (by linarith [hs.2]) hcoord2.le
    have hγle : -(1-t)*δ ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (by linarith only [ht.2]) hδ.le
    have h2' : -(1-t)*δ = (1-s) * A.coord 2 (p.vertex D.b) := by
      simpa only [mul_zero, add_zero] using h2.symm
    have hγge : 0 ≤ -(1-t)*δ := by rw [h2']; exact hprod
    have hz : -(1-t)*δ = 0 :=
      le_antisymm hγle hγge
    have hprod0 : (1-s) * A.coord 2 (p.vertex D.b) = 0 := by
      rw [← h2']
      exact hz
    have hmul : (1-t)*δ = 0 := by
      have hneg : -((1-t)*δ) = 0 := by simpa only [neg_mul] using hz
      exact neg_eq_zero.mp hneg
    have hs1 : s = 1 := by
      have hs' := (mul_eq_zero.mp hprod0).resolve_right (ne_of_gt hcoord2)
      linarith only [hs']
    have ht1 : t = 1 := by
      have ht' := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hδ)
      linarith only [ht']
    have h0 := congrArg (A.coord 0) heq
    rw [hγ0, hcoordLine 0 (p.vertex D.b) vb s] at h0
    rw [ht1, hs1, hcoordB0] at h0
    simp only [one_mul, zero_mul, mul_zero, add_zero, sub_self] at h0
    exact (ne_of_gt hδ) h0.symm

private theorem hXnotAt1500 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let OL := P3544T1RayParity C.left
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let U : Real × Real := AffineMap.lineMap vb vc (-δ)
        let X : Real × Real := AffineMap.lineMap vb va δ
        let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
        (∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), γ t ∉ P3544T1RayParity C.left) → (X ∉ OL) ) := by
  classical
  intro n p E D C OL va vb vc r₀ r δ₀ δ U X γ hXeven
  have h := hXeven 1 ⟨by norm_num, by norm_num⟩
  simpa only [γ, AffineMap.lineMap_apply_one] using h

private theorem hrightNextLast :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b), (⟨C.rightParameter
            + 1, by omega⟩ : Fin (C.rightParameter + 3)) + 1 =
            Fin.last (C.rightParameter + 2) ) := by
  classical
  intro n p E D C
  apply Fin.ext
  have hne : (⟨C.rightParameter + 1, by omega⟩ : Fin (C.rightParameter + 3)) ≠
      Fin.last (C.rightParameter + 2) := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  rw [Fin.val_add_one]
  simp [hne]

private theorem hXcarrierAt1521 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let CR := P3544T1BoundaryCarrier C.right
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        ∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb va δ
        (0 < δ) → ((δ < 1) → ((C.right.vertex (Fin.last (C.rightParameter
            + 2)) = vb) → ((C.right.vertex ⟨C.rightParameter + 1, by omega⟩ = va) →
                (((⟨C.rightParameter + 1,
                by omega⟩ : Fin (C.rightParameter + 3)) + 1 =
            Fin.last (C.rightParameter + 2)) → (X ∈ CR)))))) := by
  classical
  intro n p E D C CR va vb vc r₀ r δ₀ δ X hδ hδlt1 hrightCenter hrightIncidentPrev hrightNextLast
  change X ∈ P3544T1BoundaryCarrier C.right
  change X ∈ ⋃ i, segment Real (C.right.vertex i) (C.right.vertex (i + 1))
  refine Set.mem_iUnion.mpr ⟨⟨C.rightParameter + 1, by omega⟩, ?_⟩
  rw [hrightNextLast, hrightIncidentPrev, hrightCenter]
  rw [segment_symm]
  rw [segment_eq_image_lineMap]
  exact ⟨δ, ⟨le_of_lt hδ, le_of_lt hδlt1⟩, rfl⟩

private theorem hXnotDiagAt1529 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        (D.a = E.b) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent Real vv), ∀ (hspan : affineSpan Real (Set.range vv) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        (0 < A.coord 2 (p.vertex D.b)) → ((A.coord 0 vb = 0) → ((A.coord 2 vb = 0) → ((∀ (i : Fin
            3), ∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (t : Real), A.coord i
            (AffineMap.lineMap x y t) = (1 - t) * A.coord i x + t * A.coord i y) → (∀ (r₀ : ℝ),
        let r : Real := min r₀ 1
        let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
        let δ : Real := min δ₀ (1/2)
        let X : Real × Real := AffineMap.lineMap vb va δ
        (0 < δ) → ((A.coord 0 X = δ) → ((A.coord 2 X = 0) → (X ∉ e)))))))) ) := by
  classical
  intro n p E D e ha va vb vc vv hind hspan A hcoord2 hcoordB0 hcoordB2 hcoordLine r₀ r δ₀ δ X hδ
      hX0 hX2 hmem
  change X ∈ segment Real (p.vertex D.a) (p.vertex D.b) at hmem
  rw [ha] at hmem
  change X ∈ segment Real vb (p.vertex D.b) at hmem
  rw [segment_eq_image_lineMap] at hmem
  obtain ⟨s, hs, heq⟩ := hmem
  have h2 := congrArg (A.coord 2) heq
  rw [hcoordLine 2 vb (p.vertex D.b) s, hcoordB2, hX2] at h2
  have h2' : s * A.coord 2 (p.vertex D.b) = 0 := by
    simpa only [mul_zero, zero_add] using h2
  have hs0 : s = 0 :=
    (mul_eq_zero.mp h2').resolve_right (ne_of_gt hcoord2)
  have h0 := congrArg (A.coord 0) heq
  rw [hcoordLine 0 vb (p.vertex D.b) s, hcoordB0, hX0] at h0
  rw [hs0] at h0
  simp only [zero_mul, mul_zero, add_zero] at h0
  exact (ne_of_gt hδ) h0.symm

end OldArcParityProof

namespace OldArcAssembly

private theorem strictUpperHalfplaneEven :
    (by
      classical
      exact
        (∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (ell : (Real × Real) →ₗ[Real] Real),
            ∀ (H : Real), (∀ i, ell (q.vertex i) ≤ H) → (∀ (x : Real × Real), (H < ell x) → (x ∉
            P3544T1RayParity q))) → (∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (ell :
            (Real × Real) →ₗ[Real] Real), ∀ (H : Real), (∀ i, ell (q.vertex i) < H) → (∀ (x :
            Real × Real), (H < ell x) → (x ∉ P3544T1RayParity q))) ) := by
  classical
  intro upperHalfplaneEven m q ell H hbound x hx
  exact upperHalfplaneEven q ell H (fun i => le_of_lt (hbound i)) x hx

private theorem hseedRAt3047 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CL := P3544T1BoundaryCarrier C.left
        let OR := P3544T1RayParity C.right
        (∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (γ : Real →
            Real × Real), (ContinuousOn γ (Set.Icc (0 : Real) 1)) → ((∀ t ∈ Set.Icc (0 : Real) 1,
            γ t ∉ P3544T1BoundaryCarrier q) → ((γ 0 ∉ P3544T1RayParity q) → (∀ t ∈ Set.Icc (0
            : Real) 1, γ t ∉ P3544T1RayParity q)))) → ((∀ {m : Nat}, ∀ (q :
                P3381T1PolygonBoundary m), ∀ (ell : (Real × Real) →ₗ[Real] Real), ∀ (H : Real),
                (∀ i, ell (q.vertex i) ≤ H) → (∀ (x : Real × Real), (H < ell x) → (x ∉
            P3544T1RayParity q))) → ((∀ {m : ℕ}, ∀ (i : Fin (m + (3 : ℕ))), i -
            (1 : Fin (m + (3 : ℕ))) ≠ i) → ((∀ {m : ℕ}, ∀ (q : P3381T1PolygonBoundary m), ∀ (i
                : Fin (m + (3 : ℕ))), ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ x
            ∈ Metric.ball (q.vertex i) r, x ∉ ⋃ (j : Fin (m + (3 : ℕ))), if j ≠ i ∧ j + (1 : Fin
            (m + (3 : ℕ))) ≠ i then segment ℝ (q.vertex j) (q.vertex (j + (1 : Fin (m + (3 :
            ℕ))))) else ∅) → ((D.a = E.b) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent ℝ ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))]), ∀ (hspan : affineSpan ℝ (Set.range
            ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b, p.vertex (E.b + (1 : Fin (n
            + (3 : ℕ))))]) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        ((0 : ℝ) < (A.coord
            (0 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex D.b)) → ((C.ir (Fin.last
            (C.rightParameter + (2 : ℕ))) = D.a) → ((C.ir ⟨C.rightParameter+1, by omega⟩ = E.b -
                1) → ((C.ir (0 :
            Fin (C.rightParameter + (3 : ℕ))) = D.b) → ((C.il (0 : Fin (C.leftParameter + (3 :
                ℕ))) = D.a) →
            ((C.il 1 = E.b + 1) → ((
         (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) = (1 : ℝ)) → ((
         (A.coord (2 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ)) → ((
         (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex E.b) = (0 : ℝ)) → ((
         (A.coord (2 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex E.b) = (0 : ℝ)) → ((
         (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ)) → ((
         (A.coord (2 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) = (1 : ℝ)) → ((∀ (i :
                Fin (3 : ℕ)), ∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (t : ℝ), (A.coord i : ℝ × ℝ → ℝ)
                ((AffineMap.lineMap x y : ℝ → ℝ ×
            ℝ) t) = ((1 : ℝ) - t) * (A.coord i : ℝ × ℝ → ℝ) x + t * (A.coord i : ℝ × ℝ → ℝ) y) →
                ((∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (t : ℝ), (AffineMap.lineMap x y : ℝ → ℝ × ℝ) t
                    - x = t • (y - x)) → (∃ x, x ∈ CL \ e ∧ x ∉
            OR)))))))))))))))))))) := by
  classical
  intro n p E D C e CL OR parityEvenAlongPath upperHalfplaneEven prevIndexNe nonincidentBall ha
      va vb vc vv hind hspan A hcoord0 hrightLast hrightPrev hrightFirst hleftFirst hleftNext
      hcoordA0 hcoordA2 hcoordB0 hcoordB2 hcoordC0 hcoordC2 hcoordLine lineMapSub
  let CR := P3544T1BoundaryCarrier C.right
  obtain ⟨r₀, hr₀, hnear₀⟩ := nonincidentBall C.right (Fin.last (C.rightParameter + 2))
  let r : Real := min r₀ 1
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hnear (x : Real × Real) (hx : x ∈
      Metric.ball (C.right.vertex (Fin.last (C.rightParameter + 2))) r) :=
    hnear₀ x (Metric.ball_subset_ball (min_le_left r₀ 1) hx)
  let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
  let δ : Real := min δ₀ (1/2)
  let U : Real × Real := AffineMap.lineMap vb va (-δ)
  let X : Real × Real := AffineMap.lineMap vb vc δ
  let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδlt1 : δ < 1 := lt_of_le_of_lt (min_le_right δ₀ (1/2)) (by norm_num)
  have hscale := OldArcParityProof.hscaleAt1080 n p E r₀ hr
  have hδa := OldArcParityProof.hδaAt1084 n p E r₀ hδ₀ hscale
  have hδc := OldArcParityProof.hδcAt1093 n p E r₀ hδ₀ hscale
  have hUdiff := OldArcParityProof.hUdiffAt1102 n p E lineMapSub r₀
  have hXdiff := OldArcParityProof.hXdiffAt1105 n p E lineMapSub r₀
  have hUball := OldArcParityProof.hUballAt1108 n p E r₀ hδ hδa hUdiff
  have hXball := OldArcParityProof.hXballAt1112 n p E r₀ hδ hδc hXdiff
  have hUhigh : E.ell vb < E.ell U := OldArcParityProof.hUhighAt1116 n p E prevIndexNe r₀ hδ
      hUdiff
  have hbelow : ∀ i, E.ell (C.right.vertex i) ≤ E.ell vb := OldArcParityProof.hbelowAt1128 n
      p E D C
  have hUeven : U ∉ OR := by
    simpa [OR] using upperHalfplaneEven C.right E.ell (E.ell vb) hbelow U hUhigh
  have hU0 := OldArcParityProof.hU0At1138 n p E hind hspan hcoordA0 hcoordB0 hcoordLine r₀
  have hU2 := OldArcParityProof.hU2At1141 n p E hind hspan hcoordA2 hcoordB2 hcoordLine r₀
  have hX0 := OldArcParityProof.hX0At1144 n p E hind hspan hcoordB0 hcoordC0 hcoordLine r₀
  have hX2 := OldArcParityProof.hX2At1147 n p E hind hspan hcoordB2 hcoordC2 hcoordLine r₀
  have hγ0 (t : Real) := (show
      A.coord 0 (γ t) = -(1-t)*δ
    from by
      classical
      rw [hcoordLine 0 U X t, hU0, hX0]
      ring)
  have hγ2 (t : Real) := (show
      A.coord 2 (γ t) = t*δ
    from by
      classical
      rw [hcoordLine 2 U X t, hU2, hX2]
      ring)
  have hrightCenter := OldArcParityProof.hrightCenterAt1156 n p E D C ha hrightLast
  have hrightZero := OldArcParityProof.hrightZero n p E D C hrightFirst
  have hrightWrap := OldArcParityProof.hrightWrap n p E D C
  have hrightIncidentPrev := OldArcParityProof.hrightIncidentPrevAt1166 n p E D C hrightPrev
  have hballPath (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :=
      OldArcParityProof.hballPathAt1170 n p E r₀ hUball hXball t ht
  have havoid : ∀ t ∈ Set.Icc (0 : Real) 1, γ t ∉ CR := OldArcParityProof.havoidAt1176 n p E
      D C hind hspan hcoord0 hcoordA0 hcoordA2 hcoordB0 hcoordB2 hcoordLine r₀ hnear hδ hγ0
      hγ2 hrightCenter hrightZero hrightWrap hrightIncidentPrev hballPath
  have hcont : ContinuousOn γ (Set.Icc (0 : Real) 1) := by
    exact continuousOn_const.lineMap continuousOn_const continuousOn_id
  have hXeven := parityEvenAlongPath C.right γ hcont havoid (by simpa [γ, OR] using hUeven)
  have hXnot := OldArcParityProof.hXnotAt1265 n p E D C r₀ hXeven
  have hleftStart := OldArcParityProof.hleftStart n p E D C ha hleftFirst
  have hleftStartNext := OldArcParityProof.hleftStartNext n p E D C hleftNext
  have hXcarrier := OldArcParityProof.hXcarrierAt1274 n p E D C r₀ hδ hδlt1 hleftStart
      hleftStartNext
  have hXnotDiag := OldArcParityProof.hXnotDiagAt1281 n p E D ha hind hspan hcoord0 hcoordB0
      hcoordB2 hcoordLine r₀ hδ hX0 hX2
  exact ⟨X, ⟨hXcarrier, hXnotDiag⟩, hXnot⟩

private theorem hseedLAt3101 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∀ (D :
            P3650T1VisibleDiagonal p E), ∀ (C : P3650T1CyclicChildren p D.a D.b),
        let e := segment Real (p.vertex D.a) (p.vertex D.b)
        let CR := P3544T1BoundaryCarrier C.right
        let OL := P3544T1RayParity C.left
        (∀ {m : Nat}, ∀ (q : P3381T1PolygonBoundary m), ∀ (γ : Real →
            Real × Real), (ContinuousOn γ (Set.Icc (0 : Real) 1)) → ((∀ t ∈ Set.Icc (0 : Real) 1,
            γ t ∉ P3544T1BoundaryCarrier q) → ((γ 0 ∉ P3544T1RayParity q) → (∀ t ∈ Set.Icc (0
            : Real) 1, γ t ∉ P3544T1RayParity q)))) → ((∀ {m : Nat}, ∀ (q :
                P3381T1PolygonBoundary m), ∀ (ell : (Real × Real) →ₗ[Real] Real), ∀ (H : Real),
                (∀ i, ell (q.vertex i) ≤ H) → (∀ (x : Real × Real), (H < ell x) → (x ∉
            P3544T1RayParity q))) → ((∀ {m : ℕ}, ∀ (i : Fin (m + (3 : ℕ))), i +
            (1 : Fin (m + (3 : ℕ))) ≠ i) → ((∀ {m : ℕ}, ∀ (q : P3381T1PolygonBoundary m), ∀ (i
                : Fin (m + (3 : ℕ))), ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ x
            ∈ Metric.ball (q.vertex i) r, x ∉ ⋃ (j : Fin (m + (3 : ℕ))), if j ≠ i ∧ j + (1 : Fin
            (m + (3 : ℕ))) ≠ i then segment ℝ (q.vertex j) (q.vertex (j + (1 : Fin (m + (3 :
            ℕ))))) else ∅) → ((D.a = E.b) → (
        let va := p.vertex (E.b - 1)
        let vb := p.vertex E.b
        let vc := p.vertex (E.b + 1)
        let vv : Fin 3 → Real × Real := ![va, vb, vc]
        ∀ (hind : AffineIndependent ℝ ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b,
            p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))]), ∀ (hspan : affineSpan ℝ (Set.range
            ![p.vertex (E.b - (1 : Fin (n + (3 : ℕ)))), p.vertex E.b, p.vertex (E.b + (1 : Fin (n
            + (3 : ℕ))))]) = ⊤),
        let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
        ((0 : ℝ) < (A.coord
            (2 : Fin (3 : ℕ)) : ℝ × ℝ → ℝ) (p.vertex D.b)) → ((C.ir (Fin.last
            (C.rightParameter + (2 : ℕ))) = D.a) → ((C.ir ⟨C.rightParameter+1, by omega⟩ = E.b -
                1) → ((C.il
            (Fin.last (C.leftParameter + (2 : ℕ))) = D.b) → ((C.il (0 : Fin (C.leftParameter + (3
                : ℕ))) = D.a)
            → ((C.il 1 = E.b + 1) → ((
         (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) = (1 : ℝ)) → ((
         (A.coord (2 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b - (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ)) → ((
         (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex E.b) = (0 : ℝ)) → ((
         (A.coord (2 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex E.b) = (0 : ℝ)) → ((
         (A.coord (0 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) = (0 : ℝ)) → ((
         (A.coord (2 : Fin (3
            : ℕ)) : ℝ × ℝ → ℝ) (p.vertex (E.b + (1 : Fin (n + (3 : ℕ))))) = (1 : ℝ)) → ((∀ (i :
                Fin (3 : ℕ)), ∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (t : ℝ), (A.coord i : ℝ × ℝ → ℝ)
                ((AffineMap.lineMap x y : ℝ → ℝ ×
            ℝ) t) = ((1 : ℝ) - t) * (A.coord i : ℝ × ℝ → ℝ) x + t * (A.coord i : ℝ × ℝ → ℝ) y) →
                ((∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (t : ℝ), (AffineMap.lineMap x y : ℝ → ℝ × ℝ) t
                    - x = t • (y - x)) → (∃ x, x ∈ CR \ e ∧ x ∉
            OL)))))))))))))))))))) := by
  classical
  intro n p E D C e CR OL parityEvenAlongPath upperHalfplaneEven nextIndexNe nonincidentBall ha
      va vb vc vv hind hspan A hcoord2 hrightLast hrightPrev hleftLast hleftFirst hleftNext
      hcoordA0 hcoordA2 hcoordB0 hcoordB2 hcoordC0 hcoordC2 hcoordLine lineMapSub
  let CL := P3544T1BoundaryCarrier C.left
  obtain ⟨r₀, hr₀, hnear₀⟩ := nonincidentBall C.left 0
  let r : Real := min r₀ 1
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hnear (x : Real × Real) (hx : x ∈ Metric.ball (C.left.vertex 0) r) :=
    hnear₀ x (Metric.ball_subset_ball (min_le_left r₀ 1) hx)
  let δ₀ : Real := r / (2 * (‖va - vb‖ + ‖vc - vb‖ + 1))
  let δ : Real := min δ₀ (1/2)
  let U : Real × Real := AffineMap.lineMap vb vc (-δ)
  let X : Real × Real := AffineMap.lineMap vb va δ
  let γ : Real → Real × Real := fun t => AffineMap.lineMap U X t
  have hcont : ContinuousOn γ (Set.Icc (0 : Real) 1) := by
    exact continuousOn_const.lineMap continuousOn_const continuousOn_id
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδlt1 : δ < 1 := lt_of_le_of_lt (min_le_right δ₀ (1/2)) (by norm_num)
  have hscale := OldArcParityProof.hscaleAt1080 n p E r₀ hr
  have hδa := OldArcParityProof.hδaAt1084 n p E r₀ hδ₀ hscale
  have hδc := OldArcParityProof.hδcAt1093 n p E r₀ hδ₀ hscale
  have hUdiff := OldArcParityProof.hUdiffAt1346 n p E lineMapSub r₀
  have hXdiff := OldArcParityProof.hXdiffAt1349 n p E lineMapSub r₀
  have hUball := OldArcParityProof.hUballAt1352 n p E r₀ hδ hδc hUdiff
  have hXball := OldArcParityProof.hXballAt1356 n p E r₀ hδ hδa hXdiff
  have hUhigh : E.ell vb < E.ell U := OldArcParityProof.hUhighAt1360 n p E nextIndexNe r₀ hδ
      hUdiff
  have hbelow : ∀ i, E.ell (C.left.vertex i) ≤ E.ell vb := OldArcParityProof.hbelowAt1372 n p
      E D C
  have hUeven : U ∉ OL := by
    simpa [OL] using upperHalfplaneEven C.left E.ell (E.ell vb) hbelow U hUhigh
  have hU0 := OldArcParityProof.hU0At1382 n p E hind hspan hcoordB0 hcoordC0 hcoordLine r₀
  have hU2 := OldArcParityProof.hU2At1385 n p E hind hspan hcoordB2 hcoordC2 hcoordLine r₀
  have hX0 := OldArcParityProof.hX0At1388 n p E hind hspan hcoordA0 hcoordB0 hcoordLine r₀
  have hX2 := OldArcParityProof.hX2At1391 n p E hind hspan hcoordA2 hcoordB2 hcoordLine r₀
  have hγ0 (t : Real) := (show
      A.coord 0 (γ t) = t*δ
    from by
      classical
      rw [hcoordLine 0 U X t, hU0, hX0]
      ring)
  have hγ2 (t : Real) := (show
      A.coord 2 (γ t) = -(1-t)*δ
    from by
      classical
      rw [hcoordLine 2 U X t, hU2, hX2]
      ring)
  have hleftCenter := OldArcParityProof.hleftCenter n p E D C ha hleftFirst
  have hleftOne := OldArcParityProof.hleftOne n p E D C hleftNext
  have hleftWrap := OldArcParityProof.hleftWrap n p E D C
  have hleftEnd := OldArcParityProof.hleftEnd n p E D C hleftLast
  have hballPath (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :=
      OldArcParityProof.hballPathAt1412 n p E D C r₀ hUball hXball hleftCenter t ht
  have havoid : ∀ t ∈ Set.Icc (0 : Real) 1, γ t ∉ CL := OldArcParityProof.havoidAt1419 n p E
      D C hind hspan hcoord2 hcoordB0 hcoordB2 hcoordC0 hcoordC2 hcoordLine r₀ hnear hδ hγ0
      hγ2 hleftCenter hleftOne hleftWrap hleftEnd hballPath
  have hXeven := parityEvenAlongPath C.left γ hcont havoid
    (by simpa only [γ, AffineMap.lineMap_apply_zero] using hUeven)
  have hXnot := OldArcParityProof.hXnotAt1500 n p E D C r₀ hXeven
  have hrightCenter := OldArcParityProof.hrightCenterAt1156 n p E D C ha hrightLast
  have hrightIncidentPrev := OldArcParityProof.hrightIncidentPrevAt1166 n p E D C hrightPrev
  have hrightNextLast := OldArcParityProof.hrightNextLast n p E D C
  have hXcarrier := OldArcParityProof.hXcarrierAt1521 n p E D C r₀ hδ hδlt1 hrightCenter
      hrightIncidentPrev hrightNextLast
  have hXnotDiag := OldArcParityProof.hXnotDiagAt1529 n p E D ha hind hspan hcoord2 hcoordB0
      hcoordB2 hcoordLine r₀ hδ hX0 hX2
  exact ⟨X, ⟨hXcarrier, hXnotDiag⟩, hXnot⟩

end OldArcAssembly

theorem P3650T1OldArcEven {n : Nat} (p : P3381T1PolygonBoundary n)
    (E : P3650T1ExposedCorner p) (D : P3650T1VisibleDiagonal p E)
    (C : P3650T1CyclicChildren p D.a D.b) :
    Disjoint
      (P3544T1BoundaryCarrier C.left \ segment Real (p.vertex D.a) (p.vertex D.b))
      (P3544T1RayParity C.right) ∧
    Disjoint
      (P3544T1BoundaryCarrier C.right \ segment Real (p.vertex D.a) (p.vertex D.b))
      (P3544T1RayParity C.left) := by
-- BODY
  classical
  let e := segment Real (p.vertex D.a) (p.vertex D.b)
  let CL := P3544T1BoundaryCarrier C.left
  let CR := P3544T1BoundaryCarrier C.right
  let CP := P3544T1BoundaryCarrier p
  let OL := P3544T1RayParity C.left
  let OR := P3544T1RayParity C.right
  have hLoff := OldArcParityProof.hLoff n p E D C
  have hRoff := OldArcParityProof.hRoff n p E D C
  have hLparent := OldArcParityProof.hLparent n p E D C
  have hRparent := OldArcParityProof.hRparent n p E D C
  have oldArcEvenOnPreconnected {X : Type} [TopologicalSpace X]
      (O K S : Set X) (hO : IsOpen O) (hclosure : closure O = O ∪ K)
      (hS : IsPreconnected S) (hSK : Disjoint S K)
      (x : X) (hx : x ∈ S) (hxO : x ∉ O) := OldArcParityProof.oldArcEvenOnPreconnected (X := X) O K
          S hO hclosure hS hSK x hx hxO
  have oldArcOddOnPreconnected {X : Type} [TopologicalSpace X]
      (O K S : Set X) (hO : IsOpen O) (hclosure : closure O = O ∪ K)
      (hS : IsPreconnected S) (hSK : Disjoint S K)
      (x : X) (hx : x ∈ S) (hxO : x ∈ O) := OldArcParityProof.oldArcOddOnPreconnected
          oldArcEvenOnPreconnected (X := X) O K S hO hclosure hS hSK x hx hxO
  have oldArcEvenClosure {X : Type} [TopologicalSpace X]
      (O S : Set X) (hO : IsOpen O) (hSO : Disjoint S O) := OldArcParityProof.oldArcEvenClosure (X
          := X) O S hO hSO
  obtain ⟨leftArcPreconnected, rightArcPreconnected⟩ :=
    P5667T1CyclicChildrenOldArcsPreconnected p D.a D.b C
  have leftFirstIndex : C.il 1 = D.a + 1 := OldArcParityProof.leftFirstIndex n p E D C
  have hRopen : IsOpen OR := (P3544T1LocalParity C.right).2.1
  have hLopen : IsOpen OL := (P3544T1LocalParity C.left).2.1
  have hRclosure : closure OR = OR ∪ CR := (P3544T1LocalParity C.right).1
  have hLclosure : closure OL = OL ∪ CL := (P3544T1LocalParity C.left).1
  have propagateRight := OldArcParityProof.propagateRight n p E D C hLoff
      oldArcEvenOnPreconnected leftArcPreconnected hRopen hRclosure
  have propagateLeft := OldArcParityProof.propagateLeft n p E D C hRoff oldArcEvenOnPreconnected
      rightArcPreconnected hLopen hLclosure
  have cyclicStep {m : Nat} (i : Fin (m + 3)) := OldArcParityProof.cyclicStep n p E D C (m := m) i
  have parityEvenAlongPath {m : Nat} (q : P3381T1PolygonBoundary m)
      (γ : Real → Real × Real) (hcont : ContinuousOn γ (Set.Icc (0 : Real) 1))
      (havoid : ∀ t ∈ Set.Icc (0 : Real) 1,
        γ t ∉ P3544T1BoundaryCarrier q)
      (hstart : γ 0 ∉ P3544T1RayParity q) := OldArcParityProof.parityEvenAlongPath
          oldArcEvenOnPreconnected (m := m) q γ hcont havoid hstart
  have upperHalfplaneEven {m : Nat} (q : P3381T1PolygonBoundary m)
      (ell : (Real × Real) →ₗ[Real] Real) (H : Real)
      (hbound : ∀ i, ell (q.vertex i) ≤ H)
      (x : Real × Real) (hx : H < ell x) := OldArcParityProof.upperHalfplaneEven (m := m) q ell H
          hbound x hx
  have triangleHull {m : Nat} (q : P3381T1PolygonBoundary m)
      (hm : m = 0) := OldArcParityProof.triangleHull (m := m) q hm
  have middleNotSegment {a b c : Real × Real}
      (hdet : P3381T1TriangleDeterminant ![a, b, c] ≠ 0) := OldArcParityProof.middleNotSegment (a
          := a) (b := b) (c := c) hdet
  have prevIndexNe {m : Nat} (i : Fin (m + 3)) := OldArcParityProof.prevIndexNe n p E D C (m := m) i
  have nextIndexNe {m : Nat} (i : Fin (m + 3)) := OldArcParityProof.nextIndexNe n p E D C (m := m) i
  have strictUpperHalfplaneEven {m : Nat} (q : P3381T1PolygonBoundary m)
      (ell : (Real × Real) →ₗ[Real] Real) (H : Real)
      (hbound : ∀ i, ell (q.vertex i) < H)
      (x : Real × Real) (hx : H < ell x) := OldArcAssembly.strictUpperHalfplaneEven
          upperHalfplaneEven (m := m) q ell H hbound x hx
  have nonincidentBall {m : Nat} (q : P3381T1PolygonBoundary m)
      (i : Fin (m + 3)) := OldArcParityProof.nonincidentBall (m := m) q i
  have rightPreviousParent {m : Nat} (q : P3381T1PolygonBoundary m)
      (a b : Fin (m + 3)) (K : P3650T1CyclicChildren q a b)
      (hrot : K.rotation % (m + 3) = a.val) :
      K.ir ⟨K.rightParameter + 1, by omega⟩ = a - 1 := OldArcParityProof.rightPreviousParent n p E D
          C (m
          := m) q a b K hrot
  rcases D.route with hbase | htop
  · rcases hbase with ⟨ha, hb, hempty⟩
    have hbaseChild := OldArcParityProof.hbaseChild n p E D C leftFirstIndex cyclicStep ha hb
    have hleftIndices := OldArcParityProof.hleftIndices n p E D C ha hbaseChild
    have hleftIndexRange := OldArcParityProof.hleftIndexRange n p E D C hleftIndices
    have hleftVertexRange := OldArcParityProof.hleftVertexRange n p E D C ha hb hleftIndexRange
    have hseedR := OldArcParityProof.hseedRAt680 n p E D C upperHalfplaneEven middleNotSegment
        prevIndexNe nextIndexNe ha hb hleftIndexRange hleftVertexRange
    have hseedL := OldArcParityProof.hseedLAt728 n p E D C triangleHull prevIndexNe nextIndexNe
        ha hb hempty hbaseChild hleftIndexRange hleftVertexRange
    exact ⟨propagateRight hseedR, propagateLeft hseedL⟩
  · rcases htop with ⟨ha, hbprev, hbnext, hvertex⟩
    let va := p.vertex (E.b - 1)
    let vb := p.vertex E.b
    let vc := p.vertex (E.b + 1)
    let vv : Fin 3 → Real × Real := ![va, vb, vc]
    have hdet := OldArcParityProof.hdet n p E
    have hind := OldArcParityProof.hind n p E hdet
    have hspan := OldArcParityProof.hspan n p E hind
    let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨vv, hind, hspan⟩
    have hrange : Set.range A = ({va, vb, vc} : Set (Real × Real)) := (show
        Set.range A = ({va, vb, vc} : Set (Real × Real))
      from by
        classical
        rw [show (A : Fin 3 → Real × Real) = ![va, vb, vc] from funext (by
          intro i
          fin_cases i <;> rfl)]
        ext x
        simp
        tauto)
    have htriangle : p.vertex D.b ∈ convexHull Real (Set.range A) := by
      simpa [hrange, va, vb, vc] using hvertex
    have hcoord_nonneg := OldArcParityProof.hcoord_nonneg n p E D hind hspan htriangle
    have hcoord_sum := OldArcParityProof.hcoord_sum n p E D hind hspan
    have hside0 (x : Real × Real) (hx : x ∈ convexHull Real (Set.range A))
        (h0 : A.coord 0 x = 0) := OldArcParityProof.hside0 n p E hind hspan x hx h0
    have hside2 (x : Real × Real) (hx : x ∈ convexHull Real (Set.range A))
        (h2 : A.coord 2 x = 0) := OldArcParityProof.hside2 n p E hind hspan x hx h2
    have hcoord0 := OldArcParityProof.hcoord0 n p E D ha hbnext hind hspan htriangle
        hcoord_nonneg hside0
    have hcoord2 := OldArcParityProof.hcoord2 n p E D ha hbprev hind hspan htriangle
        hcoord_nonneg hside2
    have hrot0 := List.getElem?_rotate
      (l := List.ofFn (fun i : Fin (n + 3) => i)) (n := C.rotation) (m := 0) (by simp)
    rw [C.parent_order] at hrot0
    simp only [List.getElem?_cons_zero] at hrot0
    conv_rhs at hrot0 =>
      rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by simp))]
      rw [List.getElem_ofFn]
    have hrotval : C.rotation % (n + 3) = D.a.val := OldArcParityProof.hrotvalAt999 n p E D C hrot0
    have hrightLast := OldArcParityProof.hrightLast n p E D C
    have hrightPrev : C.ir ⟨C.rightParameter+1, by omega⟩ = E.b - 1 := by
      rw [rightPreviousParent p D.a D.b C hrotval, ha]
    have hrightFirst := OldArcParityProof.hrightFirst n p E D C
    have hleftLast := OldArcParityProof.hleftLast n p E D C
    have hleftFirst := OldArcParityProof.hleftFirst n p E D C
    have hleftNext : C.il 1 = E.b + 1 := by
      rw [leftFirstIndex, ha]
    have hcoordA0 := OldArcParityProof.hcoordA0 n p E hind hspan
    have hcoordA2 := OldArcParityProof.hcoordA2 n p E hind hspan
    have hcoordB0 := OldArcParityProof.hcoordB0 n p E hind hspan
    have hcoordB2 := OldArcParityProof.hcoordB2 n p E hind hspan
    have hcoordC0 := OldArcParityProof.hcoordC0 n p E hind hspan
    have hcoordC2 := OldArcParityProof.hcoordC2 n p E hind hspan
    have hcoordLine (i : Fin 3) (x y : Real × Real) (t : Real) := OldArcParityProof.hcoordLine n
        p E hind hspan i x y t
    have lineMapSub (x y : Real × Real) (t : Real) := OldArcParityProof.lineMapSub x y t
    have hseedR := OldArcAssembly.hseedRAt3047 n p E D C parityEvenAlongPath upperHalfplaneEven
        prevIndexNe nonincidentBall ha hind hspan hcoord0 hrightLast hrightPrev hrightFirst
        hleftFirst hleftNext hcoordA0 hcoordA2 hcoordB0 hcoordB2 hcoordC0 hcoordC2 hcoordLine
        lineMapSub
    have hseedL := OldArcAssembly.hseedLAt3101 n p E D C parityEvenAlongPath upperHalfplaneEven
        nextIndexNe nonincidentBall ha hind hspan hcoord2 hrightLast hrightPrev hleftLast
        hleftFirst hleftNext hcoordA0 hcoordA2 hcoordB0 hcoordB2 hcoordC0 hcoordC2 hcoordLine
        lineMapSub
    exact ⟨propagateRight hseedR, propagateLeft hseedL⟩

end ApollonianSuperharmonic

end
