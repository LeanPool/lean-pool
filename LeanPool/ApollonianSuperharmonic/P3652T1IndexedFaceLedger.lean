/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3544T1DiagonalSplit
public import LeanPool.ApollonianSuperharmonic.P3511T1SourceDissection
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P3652T1IndexedFaceLedger]

/-!
# P3652T1IndexedFaceLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace IndexedFaceLedgerProof

private theorem hlist :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        List.ofFn f = List.ofFn (fun k => S.il ∘ L.face k) ++ List.ofFn (fun k => S.ir ∘ R.face
            k) ) := by
  classical
  intro n p S XL XR L R f
  exact List.ofFn_fin_append _ _

private theorem hmap :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ (e : α → β), ∀ {b : List α}, ∀
            {fs : List (Fin (3 : ℕ) → α)}, P3511T1CyclicDissection α b fs →
            P3511T1CyclicDissection β (List.map e b) (List.map (fun (t : Fin (3 : ℕ) → α) => e
            ∘ t) fs) ) := by
  classical
  intro α β e b fs h
  induction h with
  | triangle a b c =>
    have ht : e ∘ ![a, b, c] = ![e a, e b, e c] := by
      funext i
      fin_cases i <;> rfl
    simpa only [List.map_cons, List.map_nil, ht] using
      P3511T1CyclicDissection.triangle (e a) (e b) (e c)
  | split a b u v left right hu hv hleft hright ihL ihR =>
    simp only [List.map_cons, List.map_append, List.map_nil] at ihL ihR
    simpa only [List.map_cons, List.map_append, List.map_nil] using
      P3511T1CyclicDissection.split (e a) (e b) (u.map e) (v.map e)
        (left.map (fun t => e ∘ t)) (right.map (fun t => e ∘ t))
        (by simpa using hu) (by simpa using hv) ihL ihR
  | rotate b fs k h ih =>
    apply P3511T1CyclicDissection.rotate _ _ k
    simpa only [List.map_rotate] using ih

private theorem hdissection :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        (List.ofFn f = List.ofFn (fun k => S.il ∘ L.face k) ++ List.ofFn (fun k => S.ir ∘ R.face
            k)) → ((∀ {α : Type}, ∀ {β : Type}, ∀ (e : α → β), ∀ {b : List α}, ∀
            {fs : List (Fin 3 → α)}, (P3511T1CyclicDissection α b fs) →
            (P3511T1CyclicDissection β (b.map e) (fs.map (fun t => e ∘ t)))) →
            (P3511T1CyclicDissection (Fin (n + 3)) (List.ofFn (fun i : Fin (n + 3) => i))
            (List.ofFn f))) ) := by
  classical
  intro n p S XL XR L R f hlist hmap
  have hl := hmap S.il L.dissection
  have hr := hmap S.ir R.dissection
  simp only [List.map_ofFn, Function.comp_def] at hl hr
  rw [S.left_order] at hl
  rw [S.right_order] at hr
  rw [hlist]
  apply P3511T1CyclicDissection.rotate _ _ S.rotation
  rw [S.parent_order]
  exact P3511T1CyclicDissection.split _ _ _ _ _ _ S.hu S.hv hl hr

private theorem hinjective :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        ∀ k, Function.Injective (f k) ) := by
  classical
  intro n p S XL XR L R f k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [f, Fin.addCases_left] using S.il_injective.comp (L.face_injective i)
  · simpa only [f, Fin.addCases_right] using S.ir_injective.comp (R.face_injective j)

private theorem hnondegenerate :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        ∀ k, P3381T1TriangleDeterminant (p.vertex ∘ f k) ≠ 0 ) := by
  classical
  intro n p S XL XR L R f k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [f, Fin.addCases_left, ← Function.comp_assoc, ← S.left_vertex]
      using L.nondegenerate i
  · simpa only [f, Fin.addCases_right, ← Function.comp_assoc, ← S.right_vertex]
      using R.nondegenerate j

private theorem hcrossAt176 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR), ∀ (i : Fin L.count), ∀ (j :
            Fin R.count), Set.range (S.il ∘ L.face i) ≠ Set.range (S.ir ∘ R.face j) ) := by
  classical
  intro n p S XL XR L R i j heq
  have hsub : Set.range (S.il ∘ L.face i) ⊆ ({S.a, S.b} : Set (Fin (n + 3))) := by
    intro x hx
    rw [← S.common_indices]
    constructor
    · obtain ⟨z, rfl⟩ := hx
      exact ⟨L.face i z, rfl⟩
    · rw [heq] at hx
      obtain ⟨z, rfl⟩ := hx
      exact ⟨R.face j z, rfl⟩
  have hcard : (Set.range (S.il ∘ L.face i)).ncard = 3 := by
    rw [Set.ncard_range_of_injective (S.il_injective.comp (L.face_injective i))]
    simp
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, Set.ncard_pair S.a_ne_b] at hle
  omega

private theorem hiAt215 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (i :
            Fin (n + (3 : ℕ))), i ∈ (List.ofFn (fun j : Fin (n + 3) => j)).rotate S.rotation ) := by
  classical
  intro n p S i
  rw [List.mem_rotate, List.mem_ofFn]
  exact ⟨i, rfl⟩

private theorem hmemAt219 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (i :
            Fin (n + (3 : ℕ))), (i ∈ S.a :: (S.u ++ S.b :: S.v)) → (i ∈ List.ofFn S.il ∨ i ∈
            List.ofFn S.ir) ) := by
  classical
  intro n p S i hi
  rw [S.left_order, S.right_order]
  simp only [List.mem_cons, List.mem_append] at hi ⊢
  tauto

private theorem hblock :
    (by
      classical
      exact
        ∀ {l : ℕ}, ∀ {r : ℕ}, ∀ (P : Fin l → Prop), ∀ (Q : Fin r → Prop), {k : Fin (l + r) |
            Fin.addCases P Q k}.ncard = {i : Fin l | P i}.ncard + {j : Fin r | Q j}.ncard ) := by
  classical
  intro l r P Q
  have hleft : Function.Injective (Fin.castAdd r : Fin l → Fin (l + r)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    simpa only [Fin.val_castAdd] using hv
  have hright : Function.Injective (Fin.natAdd l : Fin r → Fin (l + r)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    simp only [Fin.val_natAdd] at hv
    omega
  have hdisj : Disjoint
      ((Fin.castAdd r) '' {i : Fin l | P i})
      ((Fin.natAdd l) '' {j : Fin r | Q j}) := by
    apply Set.disjoint_left.mpr
    rintro k ⟨i, hi, rfl⟩ ⟨j, hj, heq⟩
    have hv := congrArg Fin.val heq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hset : {k : Fin (l + r) | Fin.addCases P Q k} =
      ((Fin.castAdd r) '' {i : Fin l | P i}) ∪
        ((Fin.natAdd l) '' {j : Fin r | Q j}) := by
    ext k
    constructor
    · refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) k
      · exact Or.inl ⟨i, by simpa using hi, rfl⟩
      · exact Or.inr ⟨j, by simpa using hj, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
      · simpa using hi
      · simpa using hj
  rw [hset, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ hleft, Set.ncard_image_of_injective _ hright]

private theorem hblockCount :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        (∀ {l : Nat}, ∀ {r : Nat}, ∀ (P : Fin l → Prop), ∀ (Q : Fin r → Prop), Set.ncard {k : Fin
            (l + r) | Fin.addCases P Q k} = Set.ncard {i : Fin l | P i} + Set.ncard {j : Fin r |
            Q j}) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), {k : Fin (L.count +
            R.count) | i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)}.ncard = {k : Fin L.count | i ∈
            Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)}.ncard + {k : Fin
            R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)}.ncard) )
            := by
  classical
  intro n p S XL XR L R f hblock i j
  let P : Fin L.count → Prop := fun k =>
    i ∈ Set.range (f (Fin.castAdd R.count k)) ∧
      j ∈ Set.range (f (Fin.castAdd R.count k))
  let Q : Fin R.count → Prop := fun k =>
    i ∈ Set.range (f (Fin.natAdd L.count k)) ∧
      j ∈ Set.range (f (Fin.natAdd L.count k))
  have hc := hblock P Q
  have hpred : {k : Fin (L.count + R.count) | Fin.addCases P Q k} =
      {k | i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · simp only [Set.mem_ofPred_eq, Fin.addCases_left, P, f]
    · simp only [Set.mem_ofPred_eq, Fin.addCases_right, Q, f]
  rw [← hpred]
  simpa only [P, Q, f, Fin.addCases_left, Fin.addCases_right] using hc

private theorem hlenP :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), n + 3
            = S.u.length + S.v.length + 2 ) := by
  classical
  intro n p S
  have h := congrArg List.length S.parent_order
  simp only [List.length_rotate, List.length_ofFn, List.length_cons,
    List.length_append] at h
  omega

private theorem hlenL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p),
            S.leftParameter + 3 = S.u.length + 2 ) := by
  classical
  intro n p S
  have h := congrArg List.length S.left_order
  simp only [List.length_ofFn, List.length_cons, List.length_append] at h
  omega

private theorem hlenR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p),
            S.rightParameter + 3 = S.v.length + 2 ) := by
  classical
  intro n p S
  have h := congrArg List.length S.right_order
  simp only [List.length_ofFn, List.length_cons, List.length_append] at h
  omega

private theorem hleftcoord :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → (∀ (x : Fin (S.leftParameter + (3 : ℕ))), (↑(S.il x) : ℕ) = ((↑x :
                ℕ) +
            S.rotation) % (n + (3 : ℕ))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR x
  have hx : x.val < S.u.length + 2 := by rw [← hlenL]; exact x.isLt
  have hpre : x.val < (S.a :: (S.u ++ [S.b])).length := by simp; omega
  have hfullVal : x.val < n + 3 := by omega
  have hidx? : (List.ofFn S.il)[x.val]? = (S.a :: (S.u ++ [S.b]))[x.val]? := by
    exact congrArg (fun l : List (Fin (n + 3)) => l[x.val]?) S.left_order
  have hrotbound : x.val < ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation).length
      := by
    simpa only [List.length_rotate, List.length_ofFn] using hfullVal
  have hpar? : ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[x.val]? =
      (S.a :: (S.u ++ S.b :: S.v))[x.val]? := by
    exact congrArg (fun l : List (Fin (n + 3)) => l[x.val]?) S.parent_order
  have hprefix? : (S.a :: (S.u ++ [S.b]))[x.val]? =
      (S.a :: (S.u ++ S.b :: S.v))[x.val]? := by
    have happend : S.a :: (S.u ++ S.b :: S.v) =
        (S.a :: (S.u ++ [S.b])) ++ S.v := by simp [List.cons_append]
    rw [happend, List.getElem?_append, ite_eq_left hpre]
  have hcoord : ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[x.val]? =
      some ⟨(x.val + S.rotation) % (n + 3), Nat.mod_lt _ (by omega)⟩ := by
    rw [List.getElem?_eq_some_iff]
    refine ⟨hrotbound, ?_⟩
    rw [List.getElem_rotate, List.getElem_ofFn]
    simp only [List.length_ofFn]
  have hsome : some (S.il x) =
      some ⟨(x.val + S.rotation) % (n + 3), Nat.mod_lt _ (by omega)⟩ := by
    calc
      some (S.il x) = (List.ofFn S.il)[x.val]? := by
        symm
        rw [List.getElem?_eq_some_iff]
        refine ⟨by simpa only [List.length_ofFn] using x.isLt, ?_⟩
        rw [List.getElem_ofFn]
      _ = (S.a :: (S.u ++ [S.b]))[x.val]? := hidx?
      _ = (S.a :: (S.u ++ S.b :: S.v))[x.val]? := hprefix?
      _ = ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[x.val]? := hpar?.symm
      _ = _ := hcoord
  exact congrArg Fin.val (Option.some.inj hsome)

private theorem haCoord :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → (S.a.val = S.rotation % (n + 3)))) ) := by
  classical
  intro n p S hlenP hlenL hlenR
  have hpar0 : ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[0]? =
      (S.a :: (S.u ++ S.b :: S.v))[0]? :=
    congrArg (fun l : List (Fin (n + 3)) => l[0]?) S.parent_order
  have hright0 : (S.a :: (S.u ++ S.b :: S.v))[0]? = some S.a := by rfl
  have hcoord0 : ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[0]? =
      some ⟨S.rotation % (n + 3), Nat.mod_lt _ (by omega)⟩ := by
    rw [List.getElem?_eq_some_iff]
    refine ⟨by simp, ?_⟩
    rw [List.getElem_rotate, List.getElem_ofFn]
    simp only [List.length_ofFn, Nat.zero_add]
  have heq := hcoord0.symm.trans (hpar0.trans hright0)
  exact (congrArg Fin.val (Option.some.inj heq)).symm

private theorem hrightcoord :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → ((S.a.val = S.rotation % (n + 3)) → (∀ (y : Fin (S.rightParameter +
                (3 :
            ℕ))), (↑(S.ir y) : ℕ) = (S.u.length + (1 : ℕ) + (↑y : ℕ) + S.rotation) % (n + (3 :
            ℕ)))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR haCoord y
  have hyBound : y.val ≤ S.v.length + 1 := by omega
  have hlenA : (S.a :: S.u).length = S.u.length + 1 := by simp
  have hlenB : (S.b :: S.v).length = S.v.length + 1 := by simp
  have hshapeR : S.b :: (S.v ++ [S.a]) = (S.b :: S.v) ++ [S.a] := by simp
  have hshapeP : S.a :: (S.u ++ S.b :: S.v) = (S.a :: S.u) ++ (S.b :: S.v) := by simp
  have hidx? : (List.ofFn S.ir)[y.val]? = (S.b :: (S.v ++ [S.a]))[y.val]? := by
    exact congrArg (fun l : List (Fin (n + 3)) => l[y.val]?) S.right_order
  have hiy? : (List.ofFn S.ir)[y.val]? = some (S.ir y) := by
    rw [List.getElem?_eq_some_iff]
    refine ⟨by simpa only [List.length_ofFn] using y.isLt, ?_⟩
    rw [List.getElem_ofFn]
  by_cases hyEnd : y.val = S.v.length + 1
  · have hlast? : (S.b :: (S.v ++ [S.a]))[y.val]? = some S.a := by
      rw [hshapeR, List.getElem?_append]
      have hnot : ¬ y.val < (S.b :: S.v).length := by rw [hlenB, hyEnd]; omega
      rw [ite_eq_right hnot]
      have hsub : y.val - (S.b :: S.v).length = 0 := by rw [hlenB, hyEnd]; omega
      rw [hsub]
      rfl
    have hlast : S.ir y = S.a := by
      have hh := hiy?.symm.trans (hidx?.trans hlast?)
      exact Option.some.inj hh
    rw [hlast, haCoord, hyEnd]
    have hM : S.u.length + 1 + (S.v.length + 1) = n + 3 := by omega
    rw [hM, Nat.add_mod, Nat.mod_self, zero_add]
    simp only [Nat.mod_mod]
  · have hyB : y.val < (S.b :: S.v).length := by rw [hlenB]; omega
    let q := S.u.length + 1 + y.val
    have hq : q < n + 3 := by dsimp [q]; omega
    have hseg? : (S.b :: (S.v ++ [S.a]))[y.val]? =
        (S.a :: (S.u ++ S.b :: S.v))[q]? := by
      rw [hshapeR, hshapeP, List.getElem?_append, List.getElem?_append]
      have hnot : ¬ q < (S.a :: S.u).length := by simp [q, hlenA]; omega
      rw [ite_eq_left hyB, ite_eq_right hnot]
      have hsub : q - (S.a :: S.u).length = y.val := by simp [q, hlenA]
      rw [hsub]
    have hparq? : ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[q]? =
        (S.a :: (S.u ++ S.b :: S.v))[q]? :=
      congrArg (fun l : List (Fin (n + 3)) => l[q]?) S.parent_order
    have hcoord : ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[q]? =
        some ⟨(q + S.rotation) % (n + 3), Nat.mod_lt _ (by omega)⟩ := by
      rw [List.getElem?_eq_some_iff]
      refine ⟨by simpa only [List.length_rotate, List.length_ofFn] using hq, ?_⟩
      rw [List.getElem_rotate, List.getElem_ofFn]
      simp only [List.length_ofFn]
    have hsome : some (S.ir y) =
        some ⟨(q + S.rotation) % (n + 3), Nat.mod_lt _ (by omega)⟩ := by
      calc
        some (S.ir y) = (List.ofFn S.ir)[y.val]? := hiy?.symm
        _ = (S.b :: (S.v ++ [S.a]))[y.val]? := hidx?
        _ = (S.a :: (S.u ++ S.b :: S.v))[q]? := hseg?
        _ = ((List.ofFn (fun i : Fin (n + 3) => i)).rotate S.rotation)[q]? := hparq?.symm
        _ = _ := hcoord
    have hv := congrArg Fin.val (Option.some.inj hsome)
    dsimp [q] at hv ⊢
    omega

private theorem hmodShift :
    (by
      classical
      exact
        ∀ {m : ℕ},
          ∀ {r : ℕ},
            ∀ {x : ℕ},
              ∀ {y : ℕ}, (0 : ℕ) < m → x < m → y < m → (r + x) % m = (r + y) % m → x = y
    ) := by
  classical
  intro m r x y hm hx hy he
  have hrx : (r + x) % m = (r % m + x) % m := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hx]
  have hry : (r + y) % m = (r % m + y) % m := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hy]
  have h' : (r % m + x) % m = (r % m + y) % m := hrx.symm.trans (he.trans hry)
  let a := r % m
  have ha : a < m := Nat.mod_lt _ hm
  have hxq : (a + x) / m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have hyq : (a + y) / m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have hxrep := Nat.mod_add_div (a + x) m
  have hyrep := Nat.mod_add_div (a + y) m
  have hxq' : (a + x) / m = 0 ∨ (a + x) / m = 1 := by
    rcases Nat.eq_zero_or_pos ((a + x) / m) with hz | hp
    · exact Or.inl hz
    · exact Or.inr (by omega)
  have hyq' : (a + y) / m = 0 ∨ (a + y) / m = 1 := by
    rcases Nat.eq_zero_or_pos ((a + y) / m) with hz | hp
    · exact Or.inl hz
    · exact Or.inr (by omega)
  rcases hxq' with hxq' | hxq' <;> rcases hyq' with hyq' | hyq'
  all_goals
    rw [hxq'] at hxrep
    rw [hyq'] at hyrep
    dsimp [a] at h' hxrep hyrep
    omega

private theorem hmodSucc :
    (by
      classical
      exact
        ∀ {m : ℕ}, ∀ {r : ℕ}, ∀ {x : ℕ}, (1 : ℕ) < m → ((r + x) % m + (1 : ℕ)) % m = (r + (x + (1
            : ℕ))) % m ) := by
  classical
  intro m r x hm
  calc
    ((r + x) % m + 1) % m = ((r + x) % m + 1 % m) % m := by
      rw [Nat.mod_eq_of_lt (by omega : 1 < m)]
    _ = (r + x + 1) % m := by rw [← Nat.add_mod]
    _ = (r + (x + 1)) % m := by congr 1

private theorem hfinAdj :
    (by
      classical
      exact
        ∀ {m : ℕ},
          ∀ (x : Fin (m + (3 : ℕ))),
            ∀ (y : Fin (m + (3 : ℕ))),
              y = x + (1 : Fin (m + (3 : ℕ))) ∨ x = y + (1 : Fin (m + (3 : ℕ))) ↔
                (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ) ∨
                  (↑x : ℕ) = (↑y : ℕ) + (1 : ℕ) ∨
                    (↑x : ℕ) + (1 : ℕ) = m + (3 : ℕ) ∧ (↑y : ℕ) = (0 : ℕ) ∨
                      (↑y : ℕ) + (1 : ℕ) = m + (3 : ℕ) ∧ (↑x : ℕ) = (0 : ℕ)
    ) := by
  classical
  intro m x y
  have hv (z : Fin (m + 3)) : (z + 1).val = (z.val + 1) % (m + 3) := by
    rw [Fin.val_add, Fin.val_one]
  constructor
  · rintro (h | h)
    · have he := congrArg Fin.val h
      rw [hv] at he
      by_cases hlt : x.val + 1 < m + 3
      · left
        simpa [Nat.mod_eq_of_lt hlt] using he
      · right
        right
        left
        have hx : x.val + 1 = m + 3 := by omega
        have hy : y.val = 0 := by rw [hx] at he; simpa using he
        exact ⟨hx, hy⟩
    · have he := congrArg Fin.val h
      rw [hv] at he
      by_cases hlt : y.val + 1 < m + 3
      · right
        left
        simpa [Nat.mod_eq_of_lt hlt] using he
      · right
        right
        right
        have hy : y.val + 1 = m + 3 := by omega
        have hx : x.val = 0 := by rw [hy] at he; simpa using he
        exact ⟨hy, hx⟩
  · rintro (h | h | h | h)
    · left
      apply Fin.ext
      rw [hv, Nat.mod_eq_of_lt (by omega : x.val + 1 < m + 3)]
      omega
    · right
      apply Fin.ext
      rw [hv, Nat.mod_eq_of_lt (by omega : y.val + 1 < m + 3)]
      omega
    · left
      apply Fin.ext
      rw [hv, h.1, Nat.mod_self]
      exact h.2
    · right
      apply Fin.ext
      rw [hv, h.1, Nat.mod_self]
      exact h.2

private theorem hleftA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀ (x
            : Fin (S.leftParameter + 3)), (S.il x).val = (x.val + S.rotation) % (n + 3)) →
                ((S.a.val =
            S.rotation % (n + 3)) → (S.il (0 : Fin (S.leftParameter + 3)) = S.a)) ) := by
  classical
  intro n p S hleftcoord haCoord
  apply Fin.ext
  have h := hleftcoord (0 : Fin (S.leftParameter + 3))
  simpa only [Fin.val_zero, Nat.zero_add, haCoord] using h

private theorem hleftB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), S.il
            (Fin.last (S.leftParameter + 2)) = S.b ) := by
  classical
  intro n p S
  have h := congrArg List.getLast? S.left_order
  rw [List.ofFn_succ_last, ← List.cons_append] at h
  simpa only [List.getLast?_concat, Option.some.injEq] using h

private theorem hrightB :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), S.ir
            (0 : Fin (S.rightParameter + 3)) = S.b ) := by
  classical
  intro n p S
  have h := congrArg List.head? S.right_order
  simpa [List.ofFn_succ] using h

private theorem hrightA :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), S.ir
            (Fin.last (S.rightParameter + 2)) = S.a ) := by
  classical
  intro n p S
  have h := congrArg List.getLast? S.right_order
  rw [List.ofFn_succ_last, ← List.cons_append] at h
  simpa only [List.getLast?_concat, Option.some.injEq] using h

private theorem hleftSucc :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → ((∀ (x : Fin (S.leftParameter + 3)), (S.il x).val = (x.val +
                S.rotation) %
            (n + 3)) → ((∀ {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, ∀ {y : Nat}, (0 < m) → ((x < m) →
            ((y < m) → (((r + x) % m = (r + y) % m) → (x = y))))) → ((∀ {m : Nat}, ∀ {r : Nat}, ∀
            {x : Nat}, (1 < m) → (((r + x) % m + 1) % m = (r + (x + 1)) % m)) → (∀ (x : Fin
            (S.leftParameter + (3 : ℕ))), ∀ (y : Fin (S.leftParameter + (3 : ℕ))), (↑(S.il y) :
                ℕ) = ((↑(S.il
            x) : ℕ) + (1 : ℕ)) % (n + (3 : ℕ)) ↔ (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ))))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR hleftcoord hmodShift hmodSucc x y
  have hxCoord : (S.il x).val = (S.rotation + x.val) % (n + 3) := by
    simpa only [Nat.add_comm] using hleftcoord x
  have hyCoord : (S.il y).val = (S.rotation + y.val) % (n + 3) := by
    simpa only [Nat.add_comm] using hleftcoord y
  rw [hxCoord, hyCoord]
  have hx : x.val + 1 < n + 3 := by omega
  have hy : y.val < n + 3 := by omega
  have hs := hmodSucc (m := n + 3) (by omega) (r := S.rotation) (x := x.val)
  constructor
  · intro h
    have he : (S.rotation + (x.val + 1)) % (n + 3) =
        (S.rotation + y.val) % (n + 3) := hs.symm.trans h.symm
    have hxy := hmodShift (m := n + 3) (r := S.rotation)
      (x := x.val + 1) (y := y.val) (by omega) hx hy he
    omega
  · intro h
    rw [h]
    exact hs.symm

private theorem hleftOrd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀ (z
            : Fin (n + 3)), (z + 1).val = (z.val + 1) % (n + 3)) → ((∀ (x : Fin (S.leftParameter
                + 3)),
            ∀ (y : Fin (S.leftParameter + 3)), (S.il y).val = ((S.il x).val + 1) % (n + 3) ↔ y.val =
            x.val + 1) → (∀ (x : Fin (S.leftParameter + (3 : ℕ))), ∀ (y : Fin (S.leftParameter +
                (3 : ℕ))),
            S.il y = S.il x + (1 : Fin (n + (3 : ℕ))) ∨ S.il x = S.il y + (1 : Fin (n + (3 : ℕ)))
            ↔ (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ) ∨ (↑x : ℕ) = (↑y : ℕ) + (1 : ℕ))) ) := by
  classical
  intro n p S hparentSuccVal hleftSucc x y
  constructor
  · rintro (h | h)
    · have hv := congrArg Fin.val h
      rw [hparentSuccVal] at hv
      exact Or.inl (hleftSucc x y |>.mp hv)
    · have hv := congrArg Fin.val h
      rw [hparentSuccVal] at hv
      exact Or.inr (hleftSucc y x |>.mp hv)
  · rintro (h | h)
    · left
      apply Fin.ext
      rw [hparentSuccVal]
      exact (hleftSucc x y).mpr h
    · right
      apply Fin.ext
      rw [hparentSuccVal]
      exact (hleftSucc y x).mpr h

private theorem hrightSucc :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → ((∀ (y : Fin (S.rightParameter + 3)), (S.ir y).val = (S.u.length + 1 +
            y.val + S.rotation) % (n + 3)) → ((∀ {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, ∀
            {y : Nat}, (0 < m) → ((x < m) → ((y < m) → (((r + x) % m = (r + y) % m) → (x = y)))))
            → ((∀ {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, (1 < m) → (((r + x) % m + 1) % m = (r + (x
            + 1)) % m)) → (∀ (x : Fin (S.rightParameter + (3 : ℕ))), ∀ (y : Fin (S.rightParameter
                + (3 : ℕ))),
            (↑x : ℕ) + (1 : ℕ) < S.rightParameter + (3 : ℕ) → (((↑(S.ir x) : ℕ) + (1 : ℕ)) % (n +
                (3 :
            ℕ)) = (↑(S.ir y) : ℕ) ↔ (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ)))))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR hrightcoord hmodShift hmodSucc x y hx
  have hxCoord : (S.ir x).val =
      (S.rotation + (S.u.length + 1 + x.val)) % (n + 3) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightcoord x
  have hyCoord : (S.ir y).val =
      (S.rotation + (S.u.length + 1 + y.val)) % (n + 3) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightcoord y
  rw [hxCoord, hyCoord]
  let tx := S.u.length + 1 + x.val
  let ty := S.u.length + 1 + y.val
  have htyLe : ty ≤ n + 3 := by dsimp [ty]; omega
  have hs := hmodSucc (m := n + 3) (by omega) (r := S.rotation) (x := tx)
  have hposMin : 2 ≤ tx := by dsimp [tx]; omega
  constructor
  · intro h
    have he : (S.rotation + (tx + 1)) % (n + 3) =
        (S.rotation + ty) % (n + 3) := hs.symm.trans h
    by_cases hyLast : y.val = S.rightParameter + 2
    · have htyM : ty = n + 3 := by dsimp [ty]; omega
      by_cases htxM : tx + 1 = n + 3
      · have hval : y.val = x.val + 1 := by dsimp [tx, ty] at htxM htyM ⊢; omega
        exact hval
      · have htxlt : tx + 1 < n + 3 := by omega
        have hzeroEq : (S.rotation + (tx + 1)) % (n + 3) =
            (S.rotation + 0) % (n + 3) := by
          simpa [htyM] using he
        have hz := hmodShift (m := n + 3) (r := S.rotation)
          (x := tx + 1) (y := 0) (by omega) (by omega) (by omega) hzeroEq
        omega
    · have htylt : ty < n + 3 := by dsimp [ty]; omega
      by_cases htxM : tx + 1 = n + 3
      · have hzeroEq : (S.rotation + 0) % (n + 3) =
            (S.rotation + ty) % (n + 3) := by
          simpa [htxM] using he
        have hz := hmodShift (m := n + 3) (r := S.rotation)
          (x := 0) (y := ty) (by omega) (by omega) (by omega) hzeroEq
        omega
      · have htxlt : tx + 1 < n + 3 := by omega
        have hpos := hmodShift (m := n + 3) (r := S.rotation)
          (x := tx + 1) (y := ty) (by omega) htxlt htylt he
        dsimp [tx, ty] at hpos ⊢
        omega
  · intro h
    have hpos : tx + 1 = ty := by dsimp [tx, ty]; omega
    rw [hs, hpos]

private theorem hrightOrd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → ((∀ (y : Fin (S.rightParameter + 3)), (S.ir y).val = (S.u.length + 1 +
            y.val + S.rotation) % (n + 3)) → ((∀ {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, ∀
            {y : Nat}, (0 < m) → ((x < m) → ((y < m) → (((r + x) % m = (r + y) % m) → (x = y)))))
            → ((∀ {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, (1 < m) → (((r + x) % m + 1) % m = (r + (x
            + 1)) % m)) → ((∀ (z : Fin (n + 3)), (z + 1).val = (z.val + 1) % (n + 3)) → ((∀ (x :
            Fin (S.rightParameter + 3)), ∀ (y : Fin (S.rightParameter + 3)), (x.val + 1 <
                S.rightParameter + 3) →
            (((S.ir x).val + 1) % (n + 3) = (S.ir y).val ↔ y.val = x.val + 1)) → (∀ (x : Fin
            (S.rightParameter + (3 : ℕ))), ∀ (y : Fin (S.rightParameter + (3 : ℕ))), x ≠ y →
                (S.ir y = S.ir x +
            (1 : Fin (n + (3 : ℕ))) ∨ S.ir x = S.ir y + (1 : Fin (n + (3 : ℕ))) ↔ (↑y : ℕ) = (↑x
            : ℕ) + (1 : ℕ) ∨ (↑x : ℕ) = (↑y : ℕ) + (1 : ℕ)))))))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR hrightcoord hmodShift hmodSucc hparentSuccVal hrightSucc x y hxy
  have hxlast : x.val + 1 = S.rightParameter + 3 ∨ x.val + 1 < S.rightParameter + 3 := by omega
  have hylast : y.val + 1 = S.rightParameter + 3 ∨ y.val + 1 < S.rightParameter + 3 := by omega
  constructor
  · rintro (h | h)
    · have hv := congrArg Fin.val h
      rw [hparentSuccVal] at hv
      rcases hxlast with hxlast | hxlt
      · have hylt : y.val + 1 < S.rightParameter + 3 := by
          rcases hylast with hylast | hylt
          · exfalso; exact hxy (Fin.ext (by omega))
          · exact hylt
        have hM : S.u.length + 1 + (S.rightParameter + 2) = n + 3 := by omega
        have hxEndCoord : (S.ir x).val = S.rotation % (n + 3) := by
          have hxl : x.val = S.rightParameter + 2 := by omega
          rw [hrightcoord, hxl]
          calc
            (S.u.length + 1 + (S.rightParameter + 2) + S.rotation) % (n + 3) =
                ((n + 3) + S.rotation) % (n + 3) := by rw [hM]
            _ = S.rotation % (n + 3) := by
              rw [Nat.add_mod, Nat.mod_self, zero_add]
              simp only [Nat.mod_mod]
        have hs0 := hmodSucc (m := n + 3) (by omega) (r := S.rotation) (x := 0)
        have hzero : (S.rotation + 1) % (n + 3) =
            (S.rotation + (S.u.length + 1 + y.val)) % (n + 3) := by
          calc
            (S.rotation + 1) % (n + 3) =
                ((S.rotation % (n + 3) + 1) % (n + 3)) := hs0.symm
            _ = ((S.ir x).val + 1) % (n + 3) := by rw [hxEndCoord]
            _ = (S.ir y).val := hv.symm
            _ = (S.rotation + (S.u.length + 1 + y.val)) % (n + 3) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightcoord y
        have hypos := hmodShift (m := n + 3) (r := S.rotation)
          (x := 1) (y := S.u.length + 1 + y.val) (by omega) (by omega) (by omega) hzero
        omega
      · exact Or.inl (hrightSucc x y hxlt |>.mp hv.symm)
    · have hv := congrArg Fin.val h
      rw [hparentSuccVal] at hv
      rcases hylast with hylast | hylt
      · rcases hxlast with hxlast | hxlt
        · exfalso; exact hxy.symm (Fin.ext (by omega))
        · have hM : S.u.length + 1 + (S.rightParameter + 2) = n + 3 := by omega
          have hyEndCoord : (S.ir y).val = S.rotation % (n + 3) := by
            have hyl : y.val = S.rightParameter + 2 := by omega
            rw [hrightcoord, hyl]
            calc
              (S.u.length + 1 + (S.rightParameter + 2) + S.rotation) % (n + 3) =
                  ((n + 3) + S.rotation) % (n + 3) := by rw [hM]
            _ = S.rotation % (n + 3) := by
              rw [Nat.add_mod, Nat.mod_self, zero_add]
              simp only [Nat.mod_mod]
          have hs0 := hmodSucc (m := n + 3) (by omega) (r := S.rotation) (x := 0)
          have hzero : (S.rotation + 1) % (n + 3) =
              (S.rotation + (S.u.length + 1 + x.val)) % (n + 3) := by
            calc
              (S.rotation + 1) % (n + 3) =
                  ((S.rotation % (n + 3) + 1) % (n + 3)) := hs0.symm
              _ = ((S.ir y).val + 1) % (n + 3) := by rw [hyEndCoord]
              _ = (S.ir x).val := hv.symm
              _ = (S.rotation + (S.u.length + 1 + x.val)) % (n + 3) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightcoord x
          have hxpos := hmodShift (m := n + 3) (r := S.rotation)
            (x := 1) (y := S.u.length + 1 + x.val) (by omega) (by omega) (by omega) hzero
          omega
      · exact Or.inr (hrightSucc y x hylt |>.mp hv.symm)
  · rintro (h | h)
    · have hxlt : x.val + 1 < S.rightParameter + 3 := by omega
      have hv := (hrightSucc x y hxlt).mpr h
      left
      apply Fin.ext
      rw [hparentSuccVal]
      exact hv.symm
    · have hylt : y.val + 1 < S.rightParameter + 3 := by omega
      have hv := (hrightSucc y x hylt).mpr h
      right
      apply Fin.ext
      rw [hparentSuccVal]
      exact hv.symm

private theorem hleftWrap :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (S.il
            (0 : Fin (S.leftParameter + 3)) = S.a) → ((S.il (Fin.last (S.leftParameter + 2)) =
                S.b) → (∀ (x :
            Fin (S.leftParameter + (3 : ℕ))), ∀ (y : Fin (S.leftParameter + (3 : ℕ))), (↑x : ℕ) +
                (1 : ℕ) =
            S.leftParameter + (3 : ℕ) ∧ (↑y : ℕ) = (0 : ℕ) ∨ (↑y : ℕ) + (1 : ℕ) = S.leftParameter
                + (3 : ℕ) ∧
            (↑x : ℕ) = (0 : ℕ) ↔ S.il x = S.b ∧ S.il y = S.a ∨ S.il y = S.b ∧ S.il x = S.a)) ) := by
  classical
  intro n p S hleftA hleftB x y
  constructor
  · rintro (h | h)
    · have hx : x = Fin.last (S.leftParameter + 2) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      have hy : y = 0 := Fin.ext (by simpa only [Fin.val_zero] using h.2)
      exact Or.inl ⟨by rw [hx, hleftB], by rw [hy, hleftA]⟩
    · have hy : y = Fin.last (S.leftParameter + 2) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      have hx : x = 0 := Fin.ext (by simpa only [Fin.val_zero] using h.2)
      exact Or.inr ⟨by rw [hy, hleftB], by rw [hx, hleftA]⟩
  · rintro (h | h)
    · have hx : x = Fin.last (S.leftParameter + 2) := S.il_injective (h.1.trans hleftB.symm)
      have hy : y = 0 := S.il_injective (h.2.trans hleftA.symm)
      subst x
      subst y
      exact Or.inl ⟨by simp, by simp⟩
    · have hy : y = Fin.last (S.leftParameter + 2) := S.il_injective (h.1.trans hleftB.symm)
      have hx : x = 0 := S.il_injective (h.2.trans hleftA.symm)
      subst x
      subst y
      exact Or.inr ⟨by simp, by simp⟩

private theorem hleftAdj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀
            {m : Nat}, ∀ (x : Fin (m + 3)), ∀ (y : Fin (m + 3)), (y = x + 1 ∨ x = y + 1) ↔ (y.val
            = x.val + 1 ∨ x.val = y.val + 1 ∨ (x.val + 1 = m + 3 ∧ y.val = 0) ∨ (y.val + 1 = m +
            3 ∧ x.val = 0))) → ((∀ (x : Fin (S.leftParameter + 3)), ∀ (y : Fin (S.leftParameter +
                3)), (S.il y
            = S.il x + 1 ∨ S.il x = S.il y + 1) ↔ (y.val = x.val + 1 ∨ x.val = y.val + 1)) → ((∀
            (x : Fin (S.leftParameter + 3)), ∀ (y : Fin (S.leftParameter + 3)), ((x.val + 1 =
                S.leftParameter + 3 ∧
            y.val = 0) ∨ (y.val + 1 = S.leftParameter + 3 ∧ x.val = 0)) ↔ ((S.il x = S.b ∧ S.il y
                = S.a)
            ∨ (S.il y = S.b ∧ S.il x = S.a))) → (∀ (x : Fin (S.leftParameter + (3 : ℕ))), ∀ (y : Fin
            (S.leftParameter + (3 : ℕ))), y = x + (1 : Fin (S.leftParameter + (3 : ℕ))) ∨ x = y +
                (1 : Fin
            (S.leftParameter + (3 : ℕ))) ↔ (S.il y = S.il x + (1 : Fin (n + (3 : ℕ))) ∨ S.il x =
                S.il y
            + (1 : Fin (n + (3 : ℕ)))) ∨ S.il x = S.a ∧ S.il y = S.b ∨ S.il y = S.a ∧ S.il x =
            S.b))) ) := by
  classical
  intro n p S hfinAdj hleftOrd hleftWrap x y
  rw [hfinAdj x y, hleftOrd x y, hleftWrap x y]
  tauto

private theorem hrightWrap :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (S.ir
            (0 : Fin (S.rightParameter + 3)) = S.b) → ((S.ir (Fin.last (S.rightParameter + 2)) =
                S.a) → (∀ (x :
            Fin (S.rightParameter + (3 : ℕ))), ∀ (y : Fin (S.rightParameter + (3 : ℕ))), (↑x : ℕ)
                + (1 : ℕ) =
            S.rightParameter + (3 : ℕ) ∧ (↑y : ℕ) = (0 : ℕ) ∨ (↑y : ℕ) + (1 : ℕ) =
                S.rightParameter + (3 : ℕ) ∧
            (↑x : ℕ) = (0 : ℕ) ↔ S.ir x = S.a ∧ S.ir y = S.b ∨ S.ir y = S.a ∧ S.ir x = S.b)) ) := by
  classical
  intro n p S hrightB hrightA x y
  constructor
  · rintro (h | h)
    · have hx : x = Fin.last (S.rightParameter + 2) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      have hy : y = 0 := Fin.ext (by simpa only [Fin.val_zero] using h.2)
      exact Or.inl ⟨by rw [hx, hrightA], by rw [hy, hrightB]⟩
    · have hy : y = Fin.last (S.rightParameter + 2) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      have hx : x = 0 := Fin.ext (by simpa only [Fin.val_zero] using h.2)
      exact Or.inr ⟨by rw [hy, hrightA], by rw [hx, hrightB]⟩
  · rintro (h | h)
    · have hx : x = Fin.last (S.rightParameter + 2) := S.ir_injective (h.1.trans hrightA.symm)
      have hy : y = 0 := S.ir_injective (h.2.trans hrightB.symm)
      subst x
      subst y
      exact Or.inl ⟨by simp, by simp⟩
    · have hy : y = Fin.last (S.rightParameter + 2) := S.ir_injective (h.1.trans hrightA.symm)
      have hx : x = 0 := S.ir_injective (h.2.trans hrightB.symm)
      subst x
      subst y
      exact Or.inr ⟨by simp, by simp⟩

private theorem hrightAdj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀
            {m : Nat}, ∀ (x : Fin (m + 3)), ∀ (y : Fin (m + 3)), (y = x + 1 ∨ x = y + 1) ↔ (y.val
            = x.val + 1 ∨ x.val = y.val + 1 ∨ (x.val + 1 = m + 3 ∧ y.val = 0) ∨ (y.val + 1 = m +
            3 ∧ x.val = 0))) → ((∀ (x : Fin (S.rightParameter + 3)), ∀ (y : Fin (S.rightParameter
                + 3)), (x ≠
            y) → ((S.ir y = S.ir x + 1 ∨ S.ir x = S.ir y + 1) ↔ (y.val = x.val + 1 ∨ x.val =
            y.val + 1))) → ((∀ (x : Fin (S.rightParameter + 3)), ∀ (y : Fin (S.rightParameter +
                3)), ((x.val +
            1 = S.rightParameter + 3 ∧ y.val = 0) ∨ (y.val + 1 = S.rightParameter + 3 ∧ x.val =
                0)) ↔ ((S.ir x
            = S.a ∧ S.ir y = S.b) ∨ (S.ir y = S.a ∧ S.ir x = S.b))) → (∀ (x : Fin
                (S.rightParameter + (3
            : ℕ))), ∀ (y : Fin (S.rightParameter + (3 : ℕ))), x ≠ y → (y = x + (1 : Fin
                (S.rightParameter + (3
            : ℕ))) ∨ x = y + (1 : Fin (S.rightParameter + (3 : ℕ))) ↔ (S.ir y = S.ir x + (1 : Fin
                (n +
            (3 : ℕ))) ∨ S.ir x = S.ir y + (1 : Fin (n + (3 : ℕ)))) ∨ S.ir x = S.a ∧ S.ir y = S.b
            ∨ S.ir y = S.a ∧ S.ir x = S.b)))) ) := by
  classical
  intro n p S hfinAdj hrightOrd hrightWrap x y hxy
  rw [hfinAdj x y, hrightOrd x y hxy, hrightWrap x y]
  tauto

private theorem hcover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (i :
            Fin (n + (3 : ℕ))), i ∈ Set.range S.il ∨ i ∈ Set.range S.ir ) := by
  classical
  intro n p S i
  have hi : i ∈ (List.ofFn (fun j : Fin (n + 3) => j)).rotate S.rotation := by
    rw [List.mem_rotate, List.mem_ofFn]
    exact ⟨i, rfl⟩
  rw [S.parent_order] at hi
  have hmem : i ∈ List.ofFn S.il ∨ i ∈ List.ofFn S.ir := by
    rw [S.left_order, S.right_order]
    simp only [List.mem_cons, List.mem_append] at hi ⊢
    tauto
  simp only [List.mem_ofFn] at hmem
  rcases hmem with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨y, hy⟩

private theorem hcrossNoAdj :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n + 3
            = S.u.length + S.v.length + 2) → ((S.leftParameter + 3 = S.u.length + 2) →
                ((S.rightParameter + 3 =
            S.v.length + 2) → ((∀ (x : Fin (S.leftParameter + 3)), (S.il x).val = (x.val +
                S.rotation) %
            (n + 3)) → ((∀ (y : Fin (S.rightParameter + 3)), (S.ir y).val = (S.u.length + 1 +
                y.val +
            S.rotation) % (n + 3)) → ((∀ {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, ∀ {y : Nat}, (0 <
            m) → ((x < m) → ((y < m) → (((r + x) % m = (r + y) % m) → (x = y))))) → ((∀
            {m : Nat}, ∀ {r : Nat}, ∀ {x : Nat}, (1 < m) → (((r + x) % m + 1) % m = (r + (x + 1))
            % m)) → ((S.il (0 : Fin (S.leftParameter + 3)) = S.a) → ((S.il (Fin.last
                (S.leftParameter + 2)) =
            S.b) → ((S.ir (0 : Fin (S.rightParameter + 3)) = S.b) → ((S.ir (Fin.last
                (S.rightParameter + 2)) =
            S.a) → ((∀ (z : Fin (n + 3)), (z + 1).val = (z.val + 1) % (n + 3)) → (∀ (x : Fin
            (S.leftParameter + (3 : ℕ))), ∀ (y : Fin (S.rightParameter + (3 : ℕ))), S.il x ∉
                Set.range S.ir →
            S.ir y ∉ Set.range S.il → ¬(S.ir y = S.il x + (1 : Fin (n + (3 : ℕ))) ∨ S.il x = S.ir
            y + (1 : Fin (n + (3 : ℕ)))))))))))))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR hleftcoord hrightcoord hmodShift hmodSucc hleftA hleftB hrightB
      hrightA hparentSuccVal x y hxNot hyNot
  have hx0 : x.val ≠ 0 := by
    intro hx
    apply hxNot
    have hx' : x = 0 := Fin.ext (by simpa only [Fin.val_zero] using hx)
    rw [hx', hleftA]
    exact ⟨Fin.last (S.rightParameter + 2), hrightA⟩
  have hxlast : x.val ≠ S.leftParameter + 2 := by
    intro hx
    apply hxNot
    have hx' : x = Fin.last (S.leftParameter + 2) := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hx', hleftB]
    exact ⟨0, hrightB⟩
  have hxlo : 1 ≤ x.val := by omega
  have hxhi : x.val ≤ S.u.length := by omega
  have hy0 : y.val ≠ 0 := by
    intro hy
    apply hyNot
    have hy' : y = 0 := Fin.ext (by simpa only [Fin.val_zero] using hy)
    rw [hy', hrightB]
    exact ⟨Fin.last (S.leftParameter + 2), hleftB⟩
  have hylast : y.val ≠ S.rightParameter + 2 := by
    intro hy
    apply hyNot
    have hy' : y = Fin.last (S.rightParameter + 2) := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hy', hrightA]
    exact ⟨0, hleftA⟩
  have hylo : 1 ≤ y.val := by omega
  have hyhi : y.val ≤ S.v.length := by omega
  have hxCoord : (S.il x).val = (S.rotation + x.val) % (n + 3) := by
    simpa only [Nat.add_comm] using hleftcoord x
  have hyCoord : (S.ir y).val =
      (S.rotation + (S.u.length + 1 + y.val)) % (n + 3) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrightcoord y
  have hoff : S.u.length + 1 + y.val < n + 3 := by omega
  have hsucc := hmodSucc (m := n + 3) (by omega) (r := S.rotation) (x := x.val)
  intro h
  rcases h with h | h
  · have hv := congrArg Fin.val h
    rw [hparentSuccVal] at hv
    have he : (S.rotation + (x.val + 1)) % (n + 3) =
        (S.rotation + (S.u.length + 1 + y.val)) % (n + 3) := by
      calc
        (S.rotation + (x.val + 1)) % (n + 3) =
            ((S.rotation + x.val) % (n + 3) + 1) % (n + 3) := hsucc.symm
        _ = ((S.il x).val + 1) % (n + 3) := by rw [hxCoord]
        _ = (S.ir y).val := hv.symm
        _ = _ := hyCoord
    have hpos := hmodShift (m := n + 3) (r := S.rotation)
      (x := x.val + 1) (y := S.u.length + 1 + y.val)
      (by omega) (by omega) hoff he
    omega
  · have hv := congrArg Fin.val h
    rw [hparentSuccVal] at hv
    let q := S.u.length + 1 + y.val
    have hsuccQ := hmodSucc (m := n + 3) (by omega) (r := S.rotation) (x := q)
    have he : (S.rotation + (q + 1)) % (n + 3) =
        (S.rotation + x.val) % (n + 3) := by
      calc
        (S.rotation + (q + 1)) % (n + 3) =
            ((S.rotation + q) % (n + 3) + 1) % (n + 3) := hsuccQ.symm
        _ = ((S.ir y).val + 1) % (n + 3) := by rw [hyCoord]
        _ = (S.il x).val := hv.symm
        _ = _ := hxCoord
    by_cases hq : q + 1 < n + 3
    · have hpos := hmodShift (m := n + 3) (r := S.rotation)
        (x := q + 1) (y := x.val) (by omega) hq (by omega) he
      dsimp [q] at hpos
      omega
    · have hqM : q + 1 = n + 3 := by omega
      have hzero : (S.rotation + 0) % (n + 3) =
          (S.rotation + x.val) % (n + 3) := by simpa [hqM] using he
      have hpos := hmodShift (m := n + 3) (r := S.rotation)
        (x := 0) (y := x.val) (by omega) (by omega) (by omega) hzero
      omega

private theorem hparentPairCover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀ (i
            : Fin (n + 3)), i ∈ Set.range S.il ∨ i ∈ Set.range S.ir) → ((∀ (x : Fin
                (S.leftParameter +
            3)), ∀ (y : Fin (S.rightParameter + 3)), (S.il x ∉ Set.range S.ir) → ((S.ir y ∉
                Set.range
            S.il) → (¬(S.ir y = S.il x + 1 ∨ S.il x = S.ir y + 1)))) → (∀ (i : Fin (n + (3 :
            ℕ))), ∀ (j : Fin (n + (3 : ℕ))), j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin
            (n + (3 : ℕ))) → i ∈ Set.range S.il ∧ j ∈ Set.range S.il ∨ i ∈ Set.range S.ir ∧ j ∈
            Set.range S.ir)) ) := by
  classical
  intro n p S hcover hcrossNoAdj i j hij
  rcases hcover i with hiL | hiR <;> rcases hcover j with hjL | hjR
  · exact Or.inl ⟨hiL, hjL⟩
  · by_cases hiR' : i ∈ Set.range S.ir
    · exact Or.inr ⟨hiR', hjR⟩
    · by_cases hjL' : j ∈ Set.range S.il
      · exact Or.inl ⟨hiL, hjL'⟩
      · rcases hiL with ⟨x, rfl⟩
        rcases hjR with ⟨y, rfl⟩
        exact False.elim (hcrossNoAdj x y hiR' hjL' (by
          rcases hij with h | h
          · exact Or.inl h
          · exact Or.inr h))
  · by_cases hiL' : i ∈ Set.range S.il
    · exact Or.inl ⟨hiL', hjL⟩
    · by_cases hjR' : j ∈ Set.range S.ir
      · exact Or.inr ⟨hiR, hjR'⟩
      · rcases hjL with ⟨x, rfl⟩
        rcases hiR with ⟨y, rfl⟩
        have hcross := hcrossNoAdj x y hjR' hiL'
        apply False.elim (hcross ?_)
        rcases hij with h | h
        · exact Or.inr h
        · exact Or.inl h
  · exact Or.inr ⟨hiR, hjR⟩

private theorem hdiagPair :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (S.il
            (0 : Fin (S.leftParameter + 3)) = S.a) → ((S.il (Fin.last (S.leftParameter + 2)) =
                S.b) → ((S.ir (0
            : Fin (S.rightParameter + 3)) = S.b) → ((S.ir (Fin.last (S.rightParameter + 2)) =
                S.a) → (∀ (i :
            Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ≠ j → (i ∈ Set.range S.il ∧ i ∈
            Set.range S.ir ∧ j ∈ Set.range S.il ∧ j ∈ Set.range S.ir ↔ i = S.a ∧ j = S.b ∨ i =
            S.b ∧ j = S.a))))) ) := by
  classical
  intro n p S hleftA hleftB hrightB hrightA i j hij
  constructor
  · rintro ⟨hiL, hiR, hjL, hjR⟩
    have hi : i ∈ ({S.a, S.b} : Set (Fin (n + 3))) := by
      have hh : i ∈ Set.range S.il ∩ Set.range S.ir := ⟨hiL, hiR⟩
      rw [S.common_indices] at hh
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    have hj : j ∈ ({S.a, S.b} : Set (Fin (n + 3))) := by
      have hh : j ∈ Set.range S.il ∩ Set.range S.ir := ⟨hjL, hjR⟩
      rw [S.common_indices] at hh
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    rcases hi with hia | hib <;> rcases hj with hja | hjb
    · subst i
      subst j
      exact False.elim (hij rfl)
    · exact Or.inl ⟨hia, hjb⟩
    · exact Or.inr ⟨hib, hja⟩
    · subst i
      subst j
      exact False.elim (hij rfl)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨0, hleftA⟩, ⟨Fin.last (S.rightParameter + 2), hrightA⟩,
        ⟨Fin.last (S.leftParameter + 2), hleftB⟩, ⟨0, hrightB⟩⟩
    · exact ⟨⟨Fin.last (S.leftParameter + 2), hleftB⟩, ⟨0, hrightB⟩,
        ⟨0, hleftA⟩, ⟨Fin.last (S.rightParameter + 2), hrightA⟩⟩

private theorem hleftCountImage :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), ∀ (x : Fin
            (S.leftParameter + (3 : ℕ))), ∀ (y : Fin (S.leftParameter + (3 : ℕ))), x ≠ y → {k :
                Fin L.count |
            S.il x ∈ Set.range (S.il ∘ L.face k) ∧ S.il y ∈ Set.range (S.il ∘ L.face k)}.ncard =
            if y = x + (1 : Fin (S.leftParameter + (3 : ℕ))) ∨ x = y + (1 : Fin (S.leftParameter
                + (3 : ℕ)))
            then (1 : ℕ) else if ∃ (k : Fin L.count), x ∈ Set.range (L.face k) ∧ y ∈ Set.range
            (L.face k) then (2 : ℕ) else (0 : ℕ) ) := by
  classical
  intro n p S XL L x y hxy
  have hset : {k : Fin L.count |
      S.il x ∈ Set.range (S.il ∘ L.face k) ∧
        S.il y ∈ Set.range (S.il ∘ L.face k)} =
      {k : Fin L.count | x ∈ Set.range (L.face k) ∧ y ∈ Set.range (L.face k)} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hy⟩
      constructor
      · simp only [Set.mem_range] at hx ⊢
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, S.il_injective (by simpa only [Function.comp_apply] using hz)⟩
      · simp only [Set.mem_range] at hy ⊢
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, S.il_injective (by simpa only [Function.comp_apply] using hz)⟩
    · rintro ⟨hx, hy⟩
      constructor
      · simp only [Set.mem_range] at hx ⊢
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, by simpa only [Function.comp_apply] using congrArg S.il hz⟩
      · simp only [Set.mem_range] at hy ⊢
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, by simpa only [Function.comp_apply] using congrArg S.il hz⟩
  rw [hset]
  exact L.edge_count x y hxy

private theorem hrightCountImage :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), ∀ (x : Fin
            (S.rightParameter + (3 : ℕ))), ∀ (y : Fin (S.rightParameter + (3 : ℕ))), x ≠ y → {k :
                Fin R.count |
            S.ir x ∈ Set.range (S.ir ∘ R.face k) ∧ S.ir y ∈ Set.range (S.ir ∘ R.face k)}.ncard =
            if y = x + (1 : Fin (S.rightParameter + (3 : ℕ))) ∨ x = y + (1 : Fin
                (S.rightParameter + (3 : ℕ)))
            then (1 : ℕ) else if ∃ (k : Fin R.count), x ∈ Set.range (R.face k) ∧ y ∈ Set.range
            (R.face k) then (2 : ℕ) else (0 : ℕ) ) := by
  classical
  intro n p S XR R x y hxy
  have hset : {k : Fin R.count |
      S.ir x ∈ Set.range (S.ir ∘ R.face k) ∧
        S.ir y ∈ Set.range (S.ir ∘ R.face k)} =
      {k : Fin R.count | x ∈ Set.range (R.face k) ∧ y ∈ Set.range (R.face k)} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hy⟩
      constructor
      · simp only [Set.mem_range] at hx ⊢
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, S.ir_injective (by simpa only [Function.comp_apply] using hz)⟩
      · simp only [Set.mem_range] at hy ⊢
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, S.ir_injective (by simpa only [Function.comp_apply] using hz)⟩
    · rintro ⟨hx, hy⟩
      constructor
      · simp only [Set.mem_range] at hx ⊢
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, by simpa only [Function.comp_apply] using congrArg S.ir hz⟩
      · simp only [Set.mem_range] at hy ⊢
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, by simpa only [Function.comp_apply] using congrArg S.ir hz⟩
  rw [hset]
  exact R.edge_count x y hxy

private theorem hleftZero :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), ∀ (i : Fin (n + (3
            : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ∉ Set.range S.il → {k : Fin L.count | i ∈
            Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)}.ncard = (0 : ℕ) ) := by
  classical
  intro n p S XL L i j hi
  have hempty : {k : Fin L.count |
      i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨hik, _⟩
      apply hi
      obtain ⟨z, hz⟩ := Set.mem_range.mp hik
      exact ⟨L.face k z, hz⟩
    · intro h
      exact False.elim h
  rw [hempty]
  simp

private theorem hrightZero :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), ∀ (i : Fin (n +
            (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ∉ Set.range S.ir → {k : Fin R.count | i ∈
            Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)}.ncard = (0 : ℕ) ) := by
  classical
  intro n p S XR R i j hi
  have hempty : {k : Fin R.count |
      i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨hik, _⟩
      apply hi
      obtain ⟨z, hz⟩ := Set.mem_range.mp hik
      exact ⟨R.face k z, hz⟩
    · intro h
      exact False.elim h
  rw [hempty]
  simp

private theorem husedSplit :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (∃ (k : Fin (L.count + R.count)), i
            ∈ Set.range (f k) ∧ j ∈ Set.range (f k)) ↔ (∃ (k : Fin L.count), i ∈ Set.range (S.il
            ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)) ∨ ∃ (k : Fin R.count), i ∈ Set.range
            (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k) ) := by
  classical
  intro n p S XL XR L R f i j
  constructor
  · rintro ⟨k, hk⟩
    refine Fin.addCases
      (motive := fun k =>
        (i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)) →
          (∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face
              k)) ∨
          (∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face
              k)))
      (fun a ha => Or.inl ⟨a, by simpa only [f, Fin.addCases_left] using ha⟩)
      (fun b hb => Or.inr ⟨b, by simpa only [f, Fin.addCases_right] using hb⟩) k hk
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Fin.castAdd R.count a, ?_⟩
      simpa only [f, Fin.addCases_left] using ha
    · refine ⟨Fin.natAdd L.count b, ?_⟩
      simpa only [f, Fin.addCases_right] using hb

private theorem hleftFaceMem :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), ∀ (x : Fin
            (S.leftParameter + (3 : ℕ))), ∀ (k : Fin L.count), S.il x ∈ Set.range (S.il ∘ L.face
                k) ↔ x
            ∈ Set.range (L.face k) ) := by
  classical
  intro n p S XL L x k
  simp only [Set.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, S.il_injective (by simpa only [Function.comp_apply] using hz)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa only [Function.comp_apply] using congrArg S.il hz⟩

private theorem hrightFaceMem :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), ∀ (x : Fin
            (S.rightParameter + (3 : ℕ))), ∀ (k : Fin R.count), S.ir x ∈ Set.range (S.ir ∘ R.face
                k) ↔ x
            ∈ Set.range (R.face k) ) := by
  classical
  intro n p S XR R x k
  simp only [Set.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, S.ir_injective (by simpa only [Function.comp_apply] using hz)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa only [Function.comp_apply] using congrArg S.ir hz⟩

private theorem hleftUsedMap :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ (x : Fin
            (S.leftParameter + 3)), ∀ (k : Fin L.count), S.il x ∈ Set.range (S.il ∘ L.face k) ↔ x ∈
            Set.range (L.face k)) → (∀ (x : Fin (S.leftParameter + (3 : ℕ))), ∀ (y : Fin
                (S.leftParameter + (3
            : ℕ))), (∃ (k : Fin L.count), x ∈ Set.range (L.face k) ∧ y ∈ Set.range (L.face k)) ↔
            ∃ (k : Fin L.count), S.il x ∈ Set.range (S.il ∘ L.face k) ∧ S.il y ∈ Set.range (S.il
            ∘ L.face k)) ) := by
  classical
  intro n p S XL L hleftFaceMem x y
  constructor
  · rintro ⟨k, hx, hy⟩
    exact ⟨k, (hleftFaceMem x k).2 hx, (hleftFaceMem y k).2 hy⟩
  · rintro ⟨k, hx, hy⟩
    exact ⟨k, (hleftFaceMem x k).1 hx, (hleftFaceMem y k).1 hy⟩

private theorem hrightUsedMap :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (∀ (x : Fin
            (S.rightParameter + 3)), ∀ (k : Fin R.count), S.ir x ∈ Set.range (S.ir ∘ R.face k) ↔ x ∈
            Set.range (R.face k)) → (∀ (x : Fin (S.rightParameter + (3 : ℕ))), ∀ (y : Fin
                (S.rightParameter +
            (3 : ℕ))), (∃ (k : Fin R.count), x ∈ Set.range (R.face k) ∧ y ∈ Set.range (R.face k))
            ↔ ∃ (k : Fin R.count), S.ir x ∈ Set.range (S.ir ∘ R.face k) ∧ S.ir y ∈ Set.range
            (S.ir ∘ R.face k)) ) := by
  classical
  intro n p S XR R hrightFaceMem x y
  constructor
  · rintro ⟨k, hx, hy⟩
    exact ⟨k, (hrightFaceMem x k).2 hx, (hrightFaceMem y k).2 hy⟩
  · rintro ⟨k, hx, hy⟩
    exact ⟨k, (hrightFaceMem x k).1 hx, (hrightFaceMem y k).1 hy⟩

private theorem hleftCountMapped :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ (x : Fin
            (S.leftParameter + 3)), ∀ (y : Fin (S.leftParameter + 3)), (y = x + 1 ∨ x = y + 1) ↔
                (S.il y = S.il
            x + 1 ∨ S.il x = S.il y + 1) ∨ (S.il x = S.a ∧ S.il y = S.b) ∨ (S.il y = S.a ∧ S.il x
            = S.b)) → ((∀ (x : Fin (S.leftParameter + 3)), ∀ (y : Fin (S.leftParameter + 3)), (x
                ≠ y) →
            (Set.ncard {k : Fin L.count | S.il x ∈ Set.range (S.il ∘ L.face k) ∧ S.il y ∈
            Set.range (S.il ∘ L.face k)} = if y = x + 1 ∨ x = y + 1 then 1 else if ∃ k, x ∈
            Set.range (L.face k) ∧ y ∈ Set.range (L.face k) then 2 else 0)) → ((∀ (x : Fin
            (S.leftParameter + 3)), ∀ (y : Fin (S.leftParameter + 3)), (∃ k : Fin L.count, x ∈
                Set.range
            (L.face k) ∧ y ∈ Set.range (L.face k)) ↔ (∃ k : Fin L.count, S.il x ∈ Set.range (S.il
            ∘ L.face k) ∧ S.il y ∈ Set.range (S.il ∘ L.face k))) → (∀ (i : Fin (n + (3 : ℕ))), ∀
            (j : Fin (n + (3 : ℕ))), i ∈ Set.range S.il → j ∈ Set.range S.il → i ≠ j → {k : Fin
            L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)}.ncard =
            if j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 : ℕ))) ∨ i = S.a ∧ j =
            S.b ∨ j = S.a ∧ i = S.b then (1 : ℕ) else if ∃ (k : Fin L.count), i ∈ Set.range (S.il
            ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k) then (2 : ℕ) else (0 : ℕ)))) ) := by
  classical
  intro n p S XL L hleftAdj hleftCountImage hleftUsedMap i j hi hj hij
  obtain ⟨x, hx⟩ := hi
  obtain ⟨y, hy⟩ := hj
  have hxy : x ≠ y := by
    intro h
    apply hij
    rw [← hx, ← hy, h]
  have hAdj : (y = x + 1 ∨ x = y + 1) ↔
      (j = i + 1 ∨ i = j + 1) ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    simpa only [hx, hy] using hleftAdj x y
  simpa only [hx, hy, hAdj, hleftUsedMap x y, or_assoc] using hleftCountImage x y hxy

private theorem hrightCountMapped :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (∀ (x : Fin
            (S.rightParameter + 3)), ∀ (y : Fin (S.rightParameter + 3)), (x ≠ y) → ((y = x + 1 ∨
                x = y + 1) ↔
            (S.ir y = S.ir x + 1 ∨ S.ir x = S.ir y + 1) ∨ (S.ir x = S.a ∧ S.ir y = S.b) ∨ (S.ir y
            = S.a ∧ S.ir x = S.b))) → ((∀ (x : Fin (S.rightParameter + 3)), ∀ (y : Fin
                (S.rightParameter + 3)),
            (x ≠ y) → (Set.ncard {k : Fin R.count | S.ir x ∈ Set.range (S.ir ∘ R.face k) ∧ S.ir y
            ∈ Set.range (S.ir ∘ R.face k)} = if y = x + 1 ∨ x = y + 1 then 1 else if ∃ k, x ∈
            Set.range (R.face k) ∧ y ∈ Set.range (R.face k) then 2 else 0)) → ((∀ (x : Fin
            (S.rightParameter + 3)), ∀ (y : Fin (S.rightParameter + 3)), (∃ k : Fin R.count, x ∈
                Set.range
            (R.face k) ∧ y ∈ Set.range (R.face k)) ↔ (∃ k : Fin R.count, S.ir x ∈ Set.range (S.ir
            ∘ R.face k) ∧ S.ir y ∈ Set.range (S.ir ∘ R.face k))) → (∀ (i : Fin (n + (3 : ℕ))), ∀
            (j : Fin (n + (3 : ℕ))), i ∈ Set.range S.ir → j ∈ Set.range S.ir → i ≠ j → {k : Fin
            R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)}.ncard =
            if j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 : ℕ))) ∨ i = S.a ∧ j =
            S.b ∨ j = S.a ∧ i = S.b then (1 : ℕ) else if ∃ (k : Fin R.count), i ∈ Set.range (S.ir
            ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k) then (2 : ℕ) else (0 : ℕ)))) ) := by
  classical
  intro n p S XR R hrightAdj hrightCountImage hrightUsedMap i j hi hj hij
  obtain ⟨x, hx⟩ := hi
  obtain ⟨y, hy⟩ := hj
  have hxy : x ≠ y := by
    intro h
    apply hij
    rw [← hx, ← hy, h]
  have hAdj : (y = x + 1 ∨ x = y + 1) ↔
      (j = i + 1 ∨ i = j + 1) ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    simpa only [hx, hy] using hrightAdj x y hxy
  simpa only [hx, hy, hAdj, hrightUsedMap x y, or_assoc] using hrightCountImage x y hxy

private theorem hleftZeroPair :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), ∀ (i : Fin (n + (3
            : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ¬(i ∈ Set.range S.il ∧ j ∈ Set.range S.il) → {k :
            Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face
            k)}.ncard = (0 : ℕ) ) := by
  classical
  intro n p S XL L i j hno
  have hempty : {k : Fin L.count |
      i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨hik, hjk⟩
      apply hno
      constructor
      · obtain ⟨z, hz⟩ := Set.mem_range.mp hik
        exact ⟨L.face k z, by simpa only [Function.comp_apply] using hz⟩
      · obtain ⟨z, hz⟩ := Set.mem_range.mp hjk
        exact ⟨L.face k z, by simpa only [Function.comp_apply] using hz⟩
    · intro h
      exact False.elim h
  rw [hempty]
  simp

private theorem hrightZeroPair :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), ∀ (i : Fin (n +
            (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ¬(i ∈ Set.range S.ir ∧ j ∈ Set.range S.ir) → {k
            : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face
            k)}.ncard = (0 : ℕ) ) := by
  classical
  intro n p S XR R i j hno
  have hempty : {k : Fin R.count |
      i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨hik, hjk⟩
      apply hno
      constructor
      · obtain ⟨z, hz⟩ := Set.mem_range.mp hik
        exact ⟨R.face k z, by simpa only [Function.comp_apply] using hz⟩
      · obtain ⟨z, hz⟩ := Set.mem_range.mp hjk
        exact ⟨R.face k z, by simpa only [Function.comp_apply] using hz⟩
    · intro h
      exact False.elim h
  rw [hempty]
  simp

private theorem hnotDiagBoundary :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (S.il
            (0 : Fin (S.leftParameter + 3)) = S.a) → ((S.il (Fin.last (S.leftParameter + 2)) =
                S.b) → ((∀ (x :
            Fin (S.leftParameter + 3)), ∀ (y : Fin (S.leftParameter + 3)), (S.il y = S.il x + 1 ∨
                S.il x = S.il
            y + 1) ↔ (y.val = x.val + 1 ∨ x.val = y.val + 1)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j
            : Fin (n + (3 : ℕ))), i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b → ¬(j = i + (1 : Fin (n +
            (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 : ℕ))))))) ) := by
  classical
  intro n p S hleftA hleftB hleftOrd i j hdiag
  rcases hdiag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro h
    have hlocal : S.il (Fin.last (S.leftParameter + 2)) =
        S.il (0 : Fin (S.leftParameter + 3)) + 1 ∨
        S.il (0 : Fin (S.leftParameter + 3)) =
          S.il (Fin.last (S.leftParameter + 2)) + 1 := by
      simpa only [hleftA, hleftB] using h
    have hnum := (hleftOrd (0 : Fin (S.leftParameter + 3)) (Fin.last (S.leftParameter + 2))).mp
        hlocal
    have hu : 0 < S.u.length := S.hu
    simp only [Fin.val_zero, Fin.val_last] at hnum
    omega
  · intro h
    have hlocal : S.il (0 : Fin (S.leftParameter + 3)) =
        S.il (Fin.last (S.leftParameter + 2)) + 1 ∨
        S.il (Fin.last (S.leftParameter + 2)) =
          S.il (0 : Fin (S.leftParameter + 3)) + 1 := by
      simpa only [hleftA, hleftB] using h
    have hnum := (hleftOrd (Fin.last (S.leftParameter + 2)) (0 : Fin (S.leftParameter + 3))).mp
        hlocal
    have hu : 0 < S.u.length := S.hu
    simp only [Fin.val_zero, Fin.val_last] at hnum
    omega

private theorem hnotDiag :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀ (i
            : Fin (n + 3)), ∀ (j : Fin (n + 3)), ((i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)) →
            (¬(j = i + 1 ∨ i = j + 1))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))),
            (j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 : ℕ)))) → (¬ ((i = S.a ∧
            j = S.b) ∨ (j = S.a ∧ i = S.b)))) ) := by
  classical
  intro n p S hnotDiagBoundary i j hboundary hd
  exact hnotDiagBoundary i j hd hboundary

private theorem hnoRAt1159 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀ (i
            : Fin (n + 3)), ∀ (j : Fin (n + 3)), (i ≠ j) → ((i ∈ Set.range S.il ∧ i ∈ Set.range
            S.ir ∧ j ∈ Set.range S.il ∧ j ∈ Set.range S.ir) ↔ ((i = S.a ∧ j = S.b) ∨ (i = S.b ∧ j
            = S.a)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i ≠ j) → ((¬ ((i
            = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b))) → ((i ∈ Set.range S.il) → ((j ∈ Set.range
            S.il) → (¬ (i ∈ Set.range S.ir ∧ j ∈ Set.range S.ir)))))) ) := by
  classical
  intro n p S hdiagPair i j hij hnotDiag hiL hjL hboth
  have hd := (hdiagPair i j hij).1 ⟨hiL, hboth.1, hjL, hboth.2⟩
  have hd' : (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  exact hnotDiag hd'

private theorem hcountLAt1167 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.il) → ((j ∈ Set.range S.il) → ((i ≠ j) →
            (Set.ncard {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘
            L.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range
            (S.il ∘ L.face k) then 2 else 0)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
            : ℕ))), (i ≠ j) → ((j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 :
            ℕ)))) → ((i ∈ Set.range S.il) → ((j ∈ Set.range S.il) → (Set.ncard {k : Fin L.count |
            i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 1))))) ) := by
  classical
  intro n p S XL L hleftCountMapped i j hij hboundary hiL hjL
  have h := hleftCountMapped i j hiL hjL hij
  have hs : j = i + 1 ∨ i = j + 1 ∨
      (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    rcases hboundary with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rw [ite_eq_left hs] at h
  exact h

private theorem hnoLAt1180 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (∀ (i
            : Fin (n + 3)), ∀ (j : Fin (n + 3)), (i ≠ j) → ((i ∈ Set.range S.il ∧ i ∈ Set.range
            S.ir ∧ j ∈ Set.range S.il ∧ j ∈ Set.range S.ir) ↔ ((i = S.a ∧ j = S.b) ∨ (i = S.b ∧ j
            = S.a)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i ≠ j) → ((¬ ((i
            = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b))) → ((i ∈ Set.range S.ir) → ((j ∈ Set.range
            S.ir) → (¬ (i ∈ Set.range S.il ∧ j ∈ Set.range S.il)))))) ) := by
  classical
  intro n p S hdiagPair i j hij hnotDiag hiR hjR hboth
  have hd := (hdiagPair i j hij).1 ⟨hboth.1, hiR, hboth.2, hjR⟩
  have hd' : (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  exact hnotDiag hd'

private theorem hcountRAt1188 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.ir) → ((j ∈ Set.range S.ir) → ((i ≠ j) →
            (Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘
            R.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k) then 2 else 0)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
            : ℕ))), (i ≠ j) → ((j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 :
            ℕ)))) → ((i ∈ Set.range S.ir) → ((j ∈ Set.range S.ir) → (Set.ncard {k : Fin R.count |
            i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 1))))) ) := by
  classical
  intro n p S XR R hrightCountMapped i j hij hboundary hiR hjR
  have h := hrightCountMapped i j hiR hjR hij
  have hs : j = i + 1 ∨ i = j + 1 ∨
      (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    rcases hboundary with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rw [ite_eq_left hs] at h
  exact h

private theorem hdiag' :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (i :
            Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i = S.a ∧ j = S.b ∨ j = S.a ∧ i =
            S.b) → ((i = S.a ∧ j = S.b) ∨ (i = S.b ∧ j = S.a)) ) := by
  classical
  intro n p S i j hdiag
  rcases hdiag with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

private theorem hcountLAt1209 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.il) → ((j ∈ Set.range S.il) → ((i ≠ j) →
            (Set.ncard {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘
            L.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range
            (S.il ∘ L.face k) then 2 else 0)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
            : ℕ))), (i ≠ j) → ((i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b) → ((i ∈ Set.range S.il) →
            ((j ∈ Set.range S.il) → (Set.ncard {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face k)
            ∧ j ∈ Set.range (S.il ∘ L.face k)} = 1))))) ) := by
  classical
  intro n p S XL L hleftCountMapped i j hij hdiag hiL hjL
  have h := hleftCountMapped i j hiL hjL hij
  have hs : j = i + 1 ∨ i = j + 1 ∨
      (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    rcases hdiag with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rw [ite_eq_left hs] at h
  exact h

private theorem hcountRAt1219 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.ir) → ((j ∈ Set.range S.ir) → ((i ≠ j) →
            (Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘
            R.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k) then 2 else 0)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
            : ℕ))), (i ≠ j) → ((i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b) → ((i ∈ Set.range S.ir) →
            ((j ∈ Set.range S.ir) → (Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k)
            ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 1))))) ) := by
  classical
  intro n p S XR R hrightCountMapped i j hij hdiag hiR hjR
  have h := hrightCountMapped i j hiR hjR hij
  have hs : j = i + 1 ∨ i = j + 1 ∨
      (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b) := by
    rcases hdiag with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rw [ite_eq_left hs] at h
  exact h

private theorem hcountAt1229 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ({k : Fin (L.count + R.count) | i ∈
            Set.range (f k) ∧ j ∈ Set.range (f k)}.ncard = {k : Fin L.count | i ∈ Set.range (S.il
            ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)}.ncard + {k : Fin R.count | i ∈
            Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)}.ncard) → ((Set.ncard
            {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)}
            = 1) → ((Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k)} = 1) → (Set.ncard {k : Fin (L.count + R.count) | i ∈ Set.range (f
            k) ∧ j ∈ Set.range (f k)} = 2))) ) := by
  classical
  intro n p S XL XR L R f i j htotal hcountL hcountR
  rw [htotal, hcountL, hcountR]

private theorem hused :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (Set.ncard {k : Fin (L.count +
            R.count) | i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} = 2) → (∃ k : Fin (L.count +
            R.count), i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)) ) := by
  classical
  intro n p S XL XR L R f i j hcount
  have hp : 0 < Set.ncard {k : Fin (L.count + R.count) |
      i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} := by rw [hcount]; omega
  obtain ⟨k, hk⟩ := (Set.ncard_pos (Set.toFinite _)).mp hp
  exact ⟨k, hk⟩

private theorem hNoSpecial :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (i :
            Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (¬(j = i + (1 : Fin (n + (3 : ℕ))) ∨ i
            = j + (1 : Fin (n + (3 : ℕ))))) → ((¬(i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b)) → (¬ (j
            = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)))) ) := by
  classical
  intro n p S i j hboundary hdiag hs
  rcases hs with hfirst | hrest
  · exact hboundary (Or.inl hfirst)
  · rcases hrest with hsecond | hrest
    · exact hboundary (Or.inr hsecond)
    · rcases hrest with hthird | hfourth
      · exact hdiag (Or.inl hthird)
      · exact hdiag (Or.inr hfourth)

private theorem hiL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), ∀ (i : Fin (n + (3
            : ℕ))), ∀ (k : Fin L.count), (i ∈ Set.range (S.il ∘ L.face k)) → (i ∈ Set.range S.il)
            ) := by
  classical
  intro n p S XL L i k hik
  obtain ⟨z, hz⟩ := Set.mem_range.mp hik
  exact ⟨L.face k z, by simpa only [Function.comp_apply] using hz⟩

private abbrev hjL := ApollonianSuperharmonic.IndexedFaceLedgerProof.hiL

private abbrev hnoRAt1259 :=
  ApollonianSuperharmonic.IndexedFaceLedgerProof.hnoRAt1159

private theorem hcountLAt1267 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.il) → ((j ∈ Set.range S.il) → ((i ≠ j) →
            (Set.ncard {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘
            L.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range
            (S.il ∘ L.face k) then 2 else 0)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
            : ℕ))), (i ≠ j) → ((¬ (j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i =
            S.b))) → (∀ (k : Fin L.count), (i ∈ Set.range (S.il ∘ L.face k)) → ((j ∈ Set.range
            (S.il ∘ L.face k)) → ((i ∈ Set.range S.il) → ((j ∈ Set.range S.il) → (Set.ncard {k :
            Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} =
            2))))))) ) := by
  classical
  intro n p S XL L hleftCountMapped i j hij hNoSpecial k hik hjk hiL hjL
  have h := hleftCountMapped i j hiL hjL hij
  have hfacePair : ∃ k : Fin L.count,
      i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k) :=
    ⟨k, hik, hjk⟩
  rw [ite_eq_right hNoSpecial, ite_eq_left hfacePair] at h
  exact h

private theorem hiR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), ∀ (i : Fin (n +
            (3 : ℕ))), ∀ (k : Fin R.count), (i ∈ Set.range (S.ir ∘ R.face k)) → (i ∈ Set.range
            S.ir) ) := by
  classical
  intro n p S XR R i k hik
  obtain ⟨z, hz⟩ := Set.mem_range.mp hik
  exact ⟨R.face k z, by simpa only [Function.comp_apply] using hz⟩

private abbrev hjR := ApollonianSuperharmonic.IndexedFaceLedgerProof.hiR

private abbrev hnoLAt1285 :=
  ApollonianSuperharmonic.IndexedFaceLedgerProof.hnoLAt1180

private theorem hcountRAt1293 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.ir) → ((j ∈ Set.range S.ir) → ((i ≠ j) →
            (Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘
            R.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k) then 2 else 0)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
            : ℕ))), (i ≠ j) → ((¬ (j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i =
            S.b))) → (∀ (k : Fin R.count), (i ∈ Set.range (S.ir ∘ R.face k)) → ((j ∈ Set.range
            (S.ir ∘ R.face k)) → ((i ∈ Set.range S.ir) → ((j ∈ Set.range S.ir) → (Set.ncard {k :
            Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} =
            2))))))) ) := by
  classical
  intro n p S XR R hrightCountMapped i j hij hNoSpecial k hik hjk hiR hjR
  have h := hrightCountMapped i j hiR hjR hij
  have hfacePair : ∃ k : Fin R.count,
      i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k) :=
    ⟨k, hik, hjk⟩
  rw [ite_eq_right hNoSpecial, ite_eq_left hfacePair] at h
  exact h

private theorem hnoUsedL :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        (∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), (∃ k : Fin (L.count + R.count), i ∈ Set.range
            (f k) ∧ j ∈ Set.range (f k)) ↔ (∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧
            j ∈ Set.range (S.il ∘ L.face k)) ∨ (∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face
            k) ∧ j ∈ Set.range (S.ir ∘ R.face k))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n +
            (3 : ℕ))), (¬∃ (k : Fin (L.count + R.count)), i ∈ Set.range (f k) ∧ j ∈ Set.range (f
            k)) → (¬ ∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘
            L.face k))) ) := by
  classical
  intro n p S XL XR L R f husedSplit i j hused h
  exact hused ((husedSplit i j).2 (Or.inl h))

private theorem hnoUsedR :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        (∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), (∃ k : Fin (L.count + R.count), i ∈ Set.range
            (f k) ∧ j ∈ Set.range (f k)) ↔ (∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧
            j ∈ Set.range (S.il ∘ L.face k)) ∨ (∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face
            k) ∧ j ∈ Set.range (S.ir ∘ R.face k))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n +
            (3 : ℕ))), (¬∃ (k : Fin (L.count + R.count)), i ∈ Set.range (f k) ∧ j ∈ Set.range (f
            k)) → (¬ ∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘
            R.face k))) ) := by
  classical
  intro n p S XL XR L R f husedSplit i j hused h
  exact hused ((husedSplit i j).2 (Or.inr h))

private theorem hcountLAt1312 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.il) → ((j ∈ Set.range S.il) → ((i ≠ j) →
            (Set.ncard {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘
            L.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin L.count, i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range
            (S.il ∘ L.face k) then 2 else 0)))) → ((∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), (¬
            (i ∈ Set.range S.il ∧ j ∈ Set.range S.il)) → (Set.ncard {k : Fin L.count | i ∈
            Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 0)) → (∀ (i : Fin (n
            + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i ≠ j) → ((¬ (j = i + 1 ∨ i = j + 1 ∨ (i =
            S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b))) → ((¬ ∃ k : Fin L.count, i ∈ Set.range (S.il ∘
            L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)) → (Set.ncard {k : Fin L.count | i ∈
            Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 0))))) ) := by
  classical
  intro n p S XL L hleftCountMapped hleftZeroPair i j hij hNoSpecial hnoUsedL
  by_cases hiL : i ∈ Set.range S.il
  · by_cases hjL : j ∈ Set.range S.il
    · have h := hleftCountMapped i j hiL hjL hij
      rw [ite_eq_right hNoSpecial, ite_eq_right hnoUsedL] at h
      exact h
    · exact hleftZeroPair i j (fun hh => hjL hh.2)
  · exact hleftZeroPair i j (fun hh => hiL hh.1)

private theorem hcountRAt1321 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (∀ (i : Fin (n +
            3)), ∀ (j : Fin (n + 3)), (i ∈ Set.range S.ir) → ((j ∈ Set.range S.ir) → ((i ≠ j) →
            (Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘
            R.face k)} = if j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
            then 1 else if ∃ k : Fin R.count, i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k) then 2 else 0)))) → ((∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), (¬
            (i ∈ Set.range S.ir ∧ j ∈ Set.range S.ir)) → (Set.ncard {k : Fin R.count | i ∈
            Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 0)) → (∀ (i : Fin (n
            + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i ≠ j) → ((¬ (j = i + 1 ∨ i = j + 1 ∨ (i =
            S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b))) → ((¬ ∃ k : Fin R.count, i ∈ Set.range (S.ir ∘
            R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)) → (Set.ncard {k : Fin R.count | i ∈
            Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 0))))) ) := by
  classical
  intro n p S XR R hrightCountMapped hrightZeroPair i j hij hNoSpecial hnoUsedR
  by_cases hiR : i ∈ Set.range S.ir
  · by_cases hjR : j ∈ Set.range S.ir
    · have h := hrightCountMapped i j hiR hjR hij
      rw [ite_eq_right hNoSpecial, ite_eq_right hnoUsedR] at h
      exact h
    · exact hrightZeroPair i j (fun hh => hjR hh.2)
  · exact hrightZeroPair i j (fun hh => hiR hh.1)

private theorem hdiag :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ {m : ℕ}, ∀ {q : P3381T1PolygonBoundary m}, ∀ {X : Set (ℝ × ℝ)}, ∀ (D :
            P3511T1SourceDissection q X), ∀ (e : Fin (m + (3 : ℕ)) → Fin (n + (3 : ℕ))), ∀ (a :
            Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 : ℕ)))),
            List.ofFn e = a :: (u ++ [b]) → ∃ (k : Fin D.count), a ∈ Set.range (e ∘ D.face k) ∧ b
            ∈ Set.range (e ∘ D.face k) ) := by
  classical
  intro n m q X D e a b u horder
  have hfirst : e 0 = a := by
    have h := congrArg List.head? horder
    simpa [List.ofFn_succ] using h
  have hlast : e (Fin.last (m + 2)) = b := by
    have h := congrArg List.getLast? horder
    rw [List.ofFn_succ_last, ← List.cons_append] at h
    simpa only [List.getLast?_concat, Option.some.injEq] using h
  have hne : (0 : Fin (m + 3)) ≠ Fin.last (m + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have hboundary : (0 : Fin (m + 3)) = Fin.last (m + 2) + 1 := by simp
  have hcount := D.edge_count 0 (Fin.last (m + 2)) hne
  rw [ite_eq_left (Or.inr hboundary)] at hcount
  have hpos : 0 < Set.ncard {k : Fin D.count |
      0 ∈ Set.range (D.face k) ∧ Fin.last (m + 2) ∈ Set.range (D.face k)} := by
    rw [hcount]
    omega
  obtain ⟨k, ⟨z, hz⟩, ⟨w, hw⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  exact ⟨k, ⟨z, by simp only [Function.comp_apply, hz, hfirst]⟩,
    ⟨w, by simp only [Function.comp_apply, hw, hlast]⟩⟩

end IndexedFaceLedgerProof

namespace IndexedLedgerAssembly

private theorem hleftOrd :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n +
            (3 : ℕ) = S.u.length + S.v.length + (2 : ℕ)) → ((S.leftParameter + (3 : ℕ) =
                S.u.length + (2
            : ℕ)) → ((S.rightParameter + (3 : ℕ) = S.v.length + (2 : ℕ)) → ((∀ (x : Fin
                (S.leftParameter + (3 :
            ℕ))), (↑(S.il x) : ℕ) = ((↑x : ℕ) + S.rotation) % (n + (3 : ℕ))) → ((∀ {m : ℕ}, ∀
            {r : ℕ}, ∀ {x : ℕ}, ∀ {y : ℕ}, (0 : ℕ) < m → x < m → y < m → (r + x) % m = (r + y) %
            m → x = y) → ((∀ {m : ℕ}, ∀ {r : ℕ}, ∀ {x : ℕ}, (1 : ℕ) < m → ((r + x) % m + (1 : ℕ))
            % m = (r + (x + (1 : ℕ))) % m) → ((∀ (z : Fin (n + 3)), (z + 1).val = (z.val + 1) %
            (n + 3)) → (∀ (x : Fin (S.leftParameter + (3 : ℕ))), ∀ (y : Fin (S.leftParameter + (3
                : ℕ))), S.il
            y = S.il x + (1 : Fin (n + (3 : ℕ))) ∨ S.il x = S.il y + (1 : Fin (n + (3 : ℕ))) ↔
            (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ) ∨ (↑x : ℕ) = (↑y : ℕ) + (1 : ℕ)))))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR hleftcoord hmodShift hmodSucc hparentSuccVal x y
  exact IndexedFaceLedgerProof.hleftOrd n p S
      hparentSuccVal (IndexedFaceLedgerProof.hleftSucc n p S hlenP hlenL hlenR hleftcoord
          hmodShift hmodSucc) x y

private theorem hleftCountMapped :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (L : P3511T1SourceDissection S.left XL), (∀ {m : ℕ}, ∀ (x :
            Fin (m + (3 : ℕ))), ∀ (y : Fin (m + (3 : ℕ))), y = x + (1 : Fin (m + (3 : ℕ))) ∨ x =
            y + (1 : Fin (m + (3 : ℕ))) ↔ (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ) ∨ (↑x : ℕ) = (↑y : ℕ) +
            (1 : ℕ) ∨ (↑x : ℕ) + (1 : ℕ) = m + (3 : ℕ) ∧ (↑y : ℕ) = (0 : ℕ) ∨ (↑y : ℕ) + (1 : ℕ)
            = m + (3 : ℕ) ∧ (↑x : ℕ) = (0 : ℕ)) → ((S.il (0 : Fin (S.leftParameter + (3 : ℕ))) =
                S.a) →
            ((S.il (Fin.last (S.leftParameter + (2 : ℕ))) = S.b) → ((∀ (x : Fin (S.leftParameter
                + (3 : ℕ))), ∀
            (y : Fin (S.leftParameter + (3 : ℕ))), S.il y = S.il x + (1 : Fin (n + (3 : ℕ))) ∨
                S.il x =
            S.il y + (1 : Fin (n + (3 : ℕ))) ↔ (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ) ∨ (↑x : ℕ) = (↑y :
            ℕ) + (1 : ℕ)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ∈ Set.range
            S.il → j ∈ Set.range S.il → i ≠ j → {k : Fin L.count | i ∈ Set.range (S.il ∘ L.face
            k) ∧ j ∈ Set.range (S.il ∘ L.face k)}.ncard = if j = i + (1 : Fin (n + (3 : ℕ))) ∨ i
            = j + (1 : Fin (n + (3 : ℕ))) ∨ i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b then (1 : ℕ)
            else if ∃ (k : Fin L.count), i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘
            L.face k) then (2 : ℕ) else (0 : ℕ))))) ) := by
  classical
  intro n p S XL L hfinAdj hleftA hleftB hleftOrd i j hi hj hij
  exact IndexedFaceLedgerProof.hleftCountMapped n p S XL L (IndexedFaceLedgerProof.hleftAdj n
              p S hfinAdj hleftOrd (IndexedFaceLedgerProof.hleftWrap n p S hleftA hleftB))
              (IndexedFaceLedgerProof.hleftCountImage n p S XL L)
          (IndexedFaceLedgerProof.hleftUsedMap n p S XL L (IndexedFaceLedgerProof.hleftFaceMem
              n p S XL L)) i j hi hj hij

private theorem hrightCountMapped :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XR
            : Set (Real × Real)), ∀ (R : P3511T1SourceDissection S.right XR), (n + (3 : ℕ) =
            S.u.length + S.v.length + (2 : ℕ)) → ((S.leftParameter + (3 : ℕ) = S.u.length + (2 :
                ℕ)) →
            ((S.rightParameter + (3 : ℕ) = S.v.length + (2 : ℕ)) → ((∀ (y : Fin (S.rightParameter
                + (3 : ℕ))),
            (↑(S.ir y) : ℕ) = (S.u.length + (1 : ℕ) + (↑y : ℕ) + S.rotation) % (n + (3 : ℕ))) →
            ((∀ {m : ℕ}, ∀ {r : ℕ}, ∀ {x : ℕ}, ∀ {y : ℕ}, (0 : ℕ) < m → x < m → y < m → (r + x) %
            m = (r + y) % m → x = y) → ((∀ {m : ℕ}, ∀ {r : ℕ}, ∀ {x : ℕ}, (1 : ℕ) < m → ((r + x)
            % m + (1 : ℕ)) % m = (r + (x + (1 : ℕ))) % m) → ((∀ {m : ℕ}, ∀ (x : Fin (m + (3 :
            ℕ))), ∀ (y : Fin (m + (3 : ℕ))), y = x + (1 : Fin (m + (3 : ℕ))) ∨ x = y + (1 : Fin
            (m + (3 : ℕ))) ↔ (↑y : ℕ) = (↑x : ℕ) + (1 : ℕ) ∨ (↑x : ℕ) = (↑y : ℕ) + (1 : ℕ) ∨ (↑x
            : ℕ) + (1 : ℕ) = m + (3 : ℕ) ∧ (↑y : ℕ) = (0 : ℕ) ∨ (↑y : ℕ) + (1 : ℕ) = m + (3 : ℕ)
            ∧ (↑x : ℕ) = (0 : ℕ)) → ((S.ir (0 : Fin (S.rightParameter + (3 : ℕ))) = S.b) → ((S.ir
            (Fin.last (S.rightParameter + (2 : ℕ))) = S.a) → ((∀ (z : Fin (n + 3)), (z + 1).val =
                (z.val
            + 1) % (n + 3)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ∈
            Set.range S.ir → j ∈ Set.range S.ir → i ≠ j → {k : Fin R.count | i ∈ Set.range (S.ir
            ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)}.ncard = if j = i + (1 : Fin (n + (3 :
            ℕ))) ∨ i = j + (1 : Fin (n + (3 : ℕ))) ∨ i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b then
            (1 : ℕ) else if ∃ (k : Fin R.count), i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k) then (2 : ℕ) else (0 : ℕ))))))))))) ) := by
  classical
  intro n p S XR R hlenP hlenL hlenR hrightcoord hmodShift hmodSucc hfinAdj hrightB hrightA
      hparentSuccVal i j hi hj hij
  exact IndexedFaceLedgerProof.hrightCountMapped n p S XR R (IndexedFaceLedgerProof.hrightAdj
              n p S hfinAdj (IndexedFaceLedgerProof.hrightOrd n p S hlenP hlenL hlenR
              hrightcoord hmodShift hmodSucc hparentSuccVal (IndexedFaceLedgerProof.hrightSucc
              n p S hlenP hlenL hlenR hrightcoord hmodShift hmodSucc))
              (IndexedFaceLedgerProof.hrightWrap n p S hrightB hrightA))
              (IndexedFaceLedgerProof.hrightCountImage n p S XR R)
          (IndexedFaceLedgerProof.hrightUsedMap n p S XR R
              (IndexedFaceLedgerProof.hrightFaceMem n p S XR R)) i j hi hj hij

private theorem hcoverPair :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), (n +
            (3 : ℕ) = S.u.length + S.v.length + (2 : ℕ)) → ((S.leftParameter + (3 : ℕ) =
                S.u.length + (2
            : ℕ)) → ((S.rightParameter + (3 : ℕ) = S.v.length + (2 : ℕ)) → ((∀ (x : Fin
                (S.leftParameter + (3 :
            ℕ))), (↑(S.il x) : ℕ) = ((↑x : ℕ) + S.rotation) % (n + (3 : ℕ))) → ((∀ (y : Fin
            (S.rightParameter + (3 : ℕ))), (↑(S.ir y) : ℕ) = (S.u.length + (1 : ℕ) + (↑y : ℕ) +
            S.rotation) % (n + (3 : ℕ))) → ((∀ {m : ℕ}, ∀ {r : ℕ}, ∀ {x : ℕ}, ∀ {y : ℕ}, (0 : ℕ)
            < m → x < m → y < m → (r + x) % m = (r + y) % m → x = y) → ((∀ {m : ℕ}, ∀ {r : ℕ}, ∀
            {x : ℕ}, (1 : ℕ) < m → ((r + x) % m + (1 : ℕ)) % m = (r + (x + (1 : ℕ))) % m) →
            ((S.il (0 : Fin (S.leftParameter + (3 : ℕ))) = S.a) → ((S.il (Fin.last
                (S.leftParameter + (2 : ℕ)))
            = S.b) → ((S.ir (0 : Fin (S.rightParameter + (3 : ℕ))) = S.b) → ((S.ir (Fin.last
                (S.rightParameter
            + (2 : ℕ))) = S.a) → ((∀ (z : Fin (n + 3)), (z + 1).val = (z.val + 1) % (n + 3)) → (∀
            (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (j = i + (1 : Fin (n + (3 : ℕ)))
            ∨ i = j + (1 : Fin (n + (3 : ℕ)))) → (i ∈ Set.range S.il ∧ j ∈ Set.range S.il ∨ i ∈
            Set.range S.ir ∧ j ∈ Set.range S.ir))))))))))))) ) := by
  classical
  intro n p S hlenP hlenL hlenR hleftcoord hrightcoord hmodShift hmodSucc hleftA hleftB hrightB
      hrightA hparentSuccVal i j hboundary
  exact (IndexedFaceLedgerProof.hparentPairCover n p S
    (IndexedFaceLedgerProof.hcover n p S) (IndexedFaceLedgerProof.hcrossNoAdj n p S hlenP
    hlenL hlenR hleftcoord hrightcoord hmodShift hmodSucc hleftA hleftB hrightB hrightA
    hparentSuccVal)) i j hboundary

private theorem hcountRAt2292 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (S : P3544T1DiagonalSplit p), ∀ (XL
            : Set (Real × Real)), ∀ (XR : Set (Real × Real)), ∀ (L : P3511T1SourceDissection
            S.left XL), ∀ (R : P3511T1SourceDissection S.right XR),
        let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
          Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
        (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (∃ (k : Fin (L.count + R.count)),
            i ∈ Set.range ((fun (i : Fin (L.count + R.count)) => Fin.addCases (motive := fun (_ :
            Fin (L.count + R.count)) => Fin (3 : ℕ) → Fin (n + (3 : ℕ))) (fun (k : Fin L.count)
            => S.il ∘ L.face k) (fun (k : Fin R.count) => S.ir ∘ R.face k) i) k) ∧ j ∈ Set.range
            ((fun (i : Fin (L.count + R.count)) => Fin.addCases (motive := fun (_ : Fin (L.count
            + R.count)) => Fin (3 : ℕ) → Fin (n + (3 : ℕ))) (fun (k : Fin L.count) => S.il ∘
            L.face k) (fun (k : Fin R.count) => S.ir ∘ R.face k) i) k)) ↔ (∃ (k : Fin L.count), i
            ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)) ∨ ∃ (k : Fin
            R.count), i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)) → ((∀ (i
                : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ∈ Set.range S.ir → j ∈ Set.range
            S.ir → i ≠ j → {k : Fin R.count | i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range
            (S.ir ∘ R.face k)}.ncard = if j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n +
            (3 : ℕ))) ∨ i = S.a ∧ j = S.b ∨ j = S.a ∧ i = S.b then (1 : ℕ) else if ∃ (k : Fin
            R.count), i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k) then (2 :
            ℕ) else (0 : ℕ)) → ((∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ¬(i ∈
            Set.range S.ir ∧ j ∈ Set.range S.ir) → {k : Fin R.count | i ∈ Set.range (S.ir ∘
            R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)}.ncard = (0 : ℕ)) → (∀ (i : Fin (n + (3 :
            ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (i ≠ j) → ((¬ (j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j
            = S.b) ∨ (j = S.a ∧ i = S.b))) → ((¬∃ (k : Fin (L.count + R.count)), i ∈ Set.range (f
            k) ∧ j ∈ Set.range (f k)) → (Set.ncard {k : Fin R.count | i ∈ Set.range (S.ir ∘
            R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 0))))))) := by
  classical
  intro n p S XL XR L R f husedSplit hrightCountMapped hrightZeroPair i j hij hNoSpecial hused
  exact IndexedFaceLedgerProof.hcountRAt1321 n p S XR R hrightCountMapped
          hrightZeroPair i j hij hNoSpecial (IndexedFaceLedgerProof.hnoUsedR n p S XL XR
              L R husedSplit i j hused)

end IndexedLedgerAssembly

theorem P3652T1IndexedFaceLedger {n : Nat} {p : P3381T1PolygonBoundary n}
    (S : P3544T1DiagonalSplit p) {XL XR : Set (Real × Real)}
    (L : P3511T1SourceDissection S.left XL)
    (R : P3511T1SourceDissection S.right XR) :
    let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
      Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
    List.ofFn f = List.ofFn (fun k => S.il ∘ L.face k) ++
      List.ofFn (fun k => S.ir ∘ R.face k) ∧
    P3511T1CyclicDissection (Fin (n + 3))
      (List.ofFn (fun i : Fin (n + 3) => i)) (List.ofFn f) ∧
    (∀ k, Function.Injective (f k)) ∧
    Function.Injective (fun k => Set.range (f k)) ∧
    (∀ i, ∃ k j, f k j = i) ∧
    (∀ k, P3381T1TriangleDeterminant (p.vertex ∘ f k) ≠ 0) ∧
    (∀ i j : Fin (n + 3), i ≠ j →
      Set.ncard {k : Fin (L.count + R.count) |
        i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} =
      if j = i + 1 ∨ i = j + 1 then 1
      else if ∃ k, i ∈ Set.range (f k) ∧ j ∈ Set.range (f k) then 2 else 0) ∧
    (∃ k, S.a ∈ Set.range (S.il ∘ L.face k) ∧ S.b ∈ Set.range (S.il ∘ L.face k)) ∧
    (∃ k, S.a ∈ Set.range (S.ir ∘ R.face k) ∧ S.b ∈ Set.range (S.ir ∘ R.face k)) := by
-- BODY
  classical
  dsimp only
  let f : Fin (L.count + R.count) → Fin 3 → Fin (n + 3) :=
    Fin.addCases (fun k => S.il ∘ L.face k) (fun k => S.ir ∘ R.face k)
  have hlist := IndexedFaceLedgerProof.hlist n p S XL XR L R
  refine ⟨hlist, (IndexedFaceLedgerProof.hdissection n p S XL XR L R hlist
      (IndexedFaceLedgerProof.hmap)), (IndexedFaceLedgerProof.hinjective n p S XL XR L R), ?_,
      ?_, (IndexedFaceLedgerProof.hnondegenerate n p S XL XR L R), ?_, ?_, ?_⟩
  · have hcross (i : Fin L.count) (j : Fin R.count) :
        Set.range (S.il ∘ L.face i) ≠ Set.range (S.ir ∘ R.face j) :=
            IndexedFaceLedgerProof.hcrossAt176
            n p S XL XR L R i j
    intro k l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) l
      · simp only [Fin.addCases_left]
        intro h
        have hh : Set.range (L.face i) = Set.range (L.face i') :=
          S.il_injective.image_injective (by simpa only [Set.range_comp] using h)
        exact congrArg (Fin.castAdd R.count) (L.face_distinct hh)
      · simp only [Fin.addCases_left, Fin.addCases_right]
        intro h
        exact False.elim (hcross i j' h)
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) l
      · simp only [Fin.addCases_left, Fin.addCases_right]
        intro h
        exact False.elim (hcross i' j h.symm)
      · simp only [Fin.addCases_right]
        intro h
        have hh : Set.range (R.face j) = Set.range (R.face j') :=
          S.ir_injective.image_injective (by simpa only [Set.range_comp] using h)
        exact congrArg (Fin.natAdd L.count) (R.face_distinct hh)
  · intro i
    have hi : i ∈ (List.ofFn (fun j : Fin (n + 3) => j)).rotate S.rotation :=
        IndexedFaceLedgerProof.hiAt215 n p S i
    rw [S.parent_order] at hi
    have hmem : i ∈ List.ofFn S.il ∨ i ∈ List.ofFn S.ir := IndexedFaceLedgerProof.hmemAt219 n p S
        i hi
    simp only [List.mem_ofFn] at hmem
    rcases hmem with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨k, z, hz⟩ := L.vertex_used j
      exact ⟨Fin.castAdd R.count k, z, by simp only [Fin.addCases_left,
        Function.comp_apply, hz]⟩
    · obtain ⟨k, z, hz⟩ := R.vertex_used j
      exact ⟨Fin.natAdd L.count k, z, by simp only [Fin.addCases_right,
        Function.comp_apply, hz]⟩
  · have hblock {l r : Nat} (P : Fin l → Prop) (Q : Fin r → Prop) :
        Set.ncard {k : Fin (l + r) | Fin.addCases P Q k} =
          Set.ncard {i : Fin l | P i} + Set.ncard {j : Fin r | Q j} :=
              IndexedFaceLedgerProof.hblock (l := l) (r := r) P Q
    have hlenP := IndexedFaceLedgerProof.hlenP n p S
    have hlenL := IndexedFaceLedgerProof.hlenL n p S
    have hlenR := IndexedFaceLedgerProof.hlenR n p S
    have hleftcoord (x : Fin (S.leftParameter + 3)) := IndexedFaceLedgerProof.hleftcoord n p S hlenP
        hlenL hlenR x
    have haCoord := IndexedFaceLedgerProof.haCoord n p S hlenP hlenL hlenR
    have hrightcoord (y : Fin (S.rightParameter + 3)) := IndexedFaceLedgerProof.hrightcoord n p S
        hlenP
        hlenL hlenR haCoord y
    have hmodShift {m r x y : Nat} (hm : 0 < m) (hx : x < m) (hy : y < m)
        (he : (r + x) % m = (r + y) % m) := IndexedFaceLedgerProof.hmodShift (m := m) (r :=
            r) (x := x) (y := y) hm hx hy he
    have hmodSucc {m r x : Nat} (hm : 1 < m) := IndexedFaceLedgerProof.hmodSucc (m := m) (r := r)
        (x := x) hm
    have hfinAdj {m : Nat} (x y : Fin (m + 3)) := IndexedFaceLedgerProof.hfinAdj (m := m) x y
    have hleftA := IndexedFaceLedgerProof.hleftA n p S hleftcoord haCoord
    have hleftB := IndexedFaceLedgerProof.hleftB n p S
    have hrightB := IndexedFaceLedgerProof.hrightB n p S
    have hrightA := IndexedFaceLedgerProof.hrightA n p S
    have hparentSuccVal (z : Fin (n + 3)) : (z + 1).val = (z.val + 1) % (n + 3) := by
      rw [Fin.val_add, Fin.val_one]
    have hleftOrd (x y : Fin (S.leftParameter + 3)) := IndexedLedgerAssembly.hleftOrd n p S hlenP
        hlenL
        hlenR hleftcoord hmodShift hmodSucc hparentSuccVal x y
    have hdiagPair (i j : Fin (n + 3)) (hij : i ≠ j) := IndexedFaceLedgerProof.hdiagPair n p S
        hleftA hleftB hrightB hrightA i j hij
    have husedSplit (i j : Fin (n + 3)) := IndexedFaceLedgerProof.husedSplit n p S XL XR L R i j
    have hleftCountMapped (i j : Fin (n + 3))
        (hi : i ∈ Set.range S.il) (hj : j ∈ Set.range S.il) (hij : i ≠ j) :=
            IndexedLedgerAssembly.hleftCountMapped n p S XL L hfinAdj hleftA hleftB hleftOrd i j
            hi hj hij
    have hrightCountMapped (i j : Fin (n + 3))
        (hi : i ∈ Set.range S.ir) (hj : j ∈ Set.range S.ir) (hij : i ≠ j) :=
            IndexedLedgerAssembly.hrightCountMapped n p S XR R hlenP hlenL hlenR hrightcoord
            hmodShift hmodSucc hfinAdj hrightB hrightA hparentSuccVal i j hi hj hij
    have hleftZeroPair (i j : Fin (n + 3))
        (hno : ¬ (i ∈ Set.range S.il ∧ j ∈ Set.range S.il)) :=
            IndexedFaceLedgerProof.hleftZeroPair n p S XL L i j hno
    have hrightZeroPair (i j : Fin (n + 3))
        (hno : ¬ (i ∈ Set.range S.ir ∧ j ∈ Set.range S.ir)) :=
            IndexedFaceLedgerProof.hrightZeroPair n p S XR R i j hno
    have hnotDiagBoundary (i j : Fin (n + 3))
        (hdiag : (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)) :=
            IndexedFaceLedgerProof.hnotDiagBoundary n p S hleftA hleftB hleftOrd i j hdiag
    intro i j hij
    have htotal := (IndexedFaceLedgerProof.hblockCount n p S XL XR L R hblock) i j
    by_cases hboundary : j = i + 1 ∨ i = j + 1
    · have hcoverPair := IndexedLedgerAssembly.hcoverPair n p S hlenP hlenL hlenR hleftcoord
        hrightcoord hmodShift hmodSucc hleftA hleftB hrightB hrightA hparentSuccVal i j hboundary
      have hnotDiag := IndexedFaceLedgerProof.hnotDiag n p S hnotDiagBoundary i j hboundary
      rcases hcoverPair with ⟨hiL, hjL⟩ | ⟨hiR, hjR⟩
      · have hnoR : ¬ (i ∈ Set.range S.ir ∧ j ∈ Set.range S.ir) :=
          IndexedFaceLedgerProof.hnoRAt1159 n p S hdiagPair i j hij hnotDiag hiL hjL
        have hcountL : Set.ncard {k : Fin L.count |
            i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 1 :=
                IndexedFaceLedgerProof.hcountLAt1167 n p S XL L hleftCountMapped i j hij hboundary
                hiL hjL
        have hcountR := hrightZeroPair i j hnoR
        rw [htotal, hcountL, hcountR]
        rw [ite_eq_left hboundary]
      · have hnoL : ¬ (i ∈ Set.range S.il ∧ j ∈ Set.range S.il) :=
          IndexedFaceLedgerProof.hnoLAt1180 n p S hdiagPair i j hij hnotDiag hiR hjR
        have hcountR : Set.ncard {k : Fin R.count |
            i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 1 :=
                IndexedFaceLedgerProof.hcountRAt1188 n p S XR R hrightCountMapped i j hij
                hboundary hiR hjR
        have hcountL := hleftZeroPair i j hnoL
        rw [htotal, hcountL, hcountR]
        rw [ite_eq_left hboundary]
    · by_cases hdiag : (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)
      · have hnotBoundary := hnotDiagBoundary i j hdiag
        have hcommon := (hdiagPair i j hij).2 (IndexedFaceLedgerProof.hdiag' n p S i j hdiag)
        rcases hcommon with ⟨hiL, hiR, hjL, hjR⟩
        have hcountL : Set.ncard {k : Fin L.count |
            i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 1 :=
                IndexedFaceLedgerProof.hcountLAt1209 n p S XL L hleftCountMapped i j hij hdiag hiL
                hjL
        have hcountR : Set.ncard {k : Fin R.count |
            i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 1 :=
                IndexedFaceLedgerProof.hcountRAt1219 n p S XR R hrightCountMapped i j hij hdiag
                hiR hjR
        have hcount : Set.ncard {k : Fin (L.count + R.count) |
            i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} = 2 :=
                IndexedFaceLedgerProof.hcountAt1229 n p S
                XL XR L R i j htotal hcountL hcountR
        have hused : ∃ k : Fin (L.count + R.count),
            i ∈ Set.range (f k) ∧ j ∈ Set.range (f k) := IndexedFaceLedgerProof.hused n p S XL XR
                L R i j hcount
        rw [hcount, ite_eq_right hnotBoundary, ite_eq_left hused]
      · have hNoSpecial :
            ¬ (j = i + 1 ∨ i = j + 1 ∨ (i = S.a ∧ j = S.b) ∨ (j = S.a ∧ i = S.b)) :=
                IndexedFaceLedgerProof.hNoSpecial n p S i j hboundary hdiag
        by_cases hused : ∃ k : Fin (L.count + R.count),
            i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)
        · rcases (husedSplit i j).1 hused with husedL | husedR
          · obtain ⟨k, hik, hjk⟩ := husedL
            have hiL := IndexedFaceLedgerProof.hiL n p S XL L i k hik
            have hjL := IndexedFaceLedgerProof.hjL n p S XL L j k hjk
            have hnoR := IndexedFaceLedgerProof.hnoRAt1259 n p S hdiagPair i j hij hdiag hiL hjL
            have hcountL : Set.ncard {k : Fin L.count |
                i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 2 :=
                    IndexedFaceLedgerProof.hcountLAt1267 n p S XL L hleftCountMapped i j hij
                    hNoSpecial k hik hjk hiL hjL
            have hcountR := hrightZeroPair i j hnoR
            rw [htotal, hcountL, hcountR]
            rw [ite_eq_right hboundary, ite_eq_left hused]
          · obtain ⟨k, hik, hjk⟩ := husedR
            have hiR := IndexedFaceLedgerProof.hiR n p S XR R i k hik
            have hjR := IndexedFaceLedgerProof.hjR n p S XR R j k hjk
            have hnoL := IndexedFaceLedgerProof.hnoLAt1285 n p S hdiagPair i j hij hdiag hiR hjR
            have hcountR : Set.ncard {k : Fin R.count |
                i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 2 :=
                    IndexedFaceLedgerProof.hcountRAt1293 n p S XR R hrightCountMapped i j hij
                    hNoSpecial k hik hjk hiR hjR
            have hcountL := hleftZeroPair i j hnoL
            rw [htotal, hcountL, hcountR]
            rw [ite_eq_right hboundary, ite_eq_left hused]
        · have hnoUsedL : ¬ ∃ k : Fin L.count,
              i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k) :=
                  IndexedFaceLedgerProof.hnoUsedL n p S XL XR L R husedSplit i j hused
          have hcountL : Set.ncard {k : Fin L.count |
              i ∈ Set.range (S.il ∘ L.face k) ∧ j ∈ Set.range (S.il ∘ L.face k)} = 0 :=
                  IndexedFaceLedgerProof.hcountLAt1312 n p S XL L hleftCountMapped hleftZeroPair i
                  j hij hNoSpecial hnoUsedL
          have hcountR : Set.ncard {k : Fin R.count |
              i ∈ Set.range (S.ir ∘ R.face k) ∧ j ∈ Set.range (S.ir ∘ R.face k)} = 0 :=
                  IndexedLedgerAssembly.hcountRAt2292 n p S XL XR L R husedSplit
                  hrightCountMapped hrightZeroPair i j hij hNoSpecial hused
          rw [htotal, hcountL, hcountR]
          rw [ite_eq_right hboundary, ite_eq_right hused]
  all_goals
    have hdiag {m : Nat} {q : P3381T1PolygonBoundary m} {X : Set (Real × Real)}
        (D : P3511T1SourceDissection q X) (e : Fin (m + 3) → Fin (n + 3))
        (a b : Fin (n + 3)) (u : List (Fin (n + 3)))
        (horder : List.ofFn e = a :: (u ++ [b])) := IndexedFaceLedgerProof.hdiag n (m := m) (q :=
            q) (X := X) D e a b u horder
  · exact hdiag L S.il S.a S.b S.u S.left_order
  · obtain ⟨k, hb, ha⟩ := hdiag R S.ir S.b S.a S.v S.right_order
    exact ⟨k, ha, hb⟩

end ApollonianSuperharmonic

end
