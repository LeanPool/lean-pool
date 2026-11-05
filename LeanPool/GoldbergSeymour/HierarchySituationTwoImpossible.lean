/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTerminalCommonMissing
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeNormalization
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseOneTwo
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseThreeOne
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseThreeTwo
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseTwoTwo

/-!
# Hierarchy Situation Two Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch381Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (hsituation : HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C)
  (htail :
   (2 : ℕ) ≤
    T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length)
  (hTtwo : (2 : ℕ) ≤ T.length),
  let lastEdgeIndex : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let penultimateVertexIndex : Fin (T.length + (1 : ℕ)) :=
   (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
  let terminalVertexIndex : Fin (T.length + (1 : ℕ)) := Fin.last T.length;
  ∀ (hlastPos : (↑lastEdgeIndex : ℕ) + (1 : ℕ) = T.length)
   (hpenPos : (↑penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length)
   (htermPos : (↑terminalVertexIndex : ℕ) = T.length) (theta : Fin k)
   (htheta : phi (T.edge lastEdgeIndex) = some theta),
   let hcommon : HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx :=
    {
     tailAtLeastTwo := htail, pathNumberFull := hsituation, lastEdgeIndex := lastEdgeIndex,
     penultimateVertexIndex := penultimateVertexIndex, terminalVertexIndex := terminalVertexIndex,
     lastEdgePosition := hlastPos, penultimateVertexPosition := hpenPos,
     terminalVertexPosition := htermPos,
     lastEdgeNotIncidentPenultimate :=
      fun (hinc : Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex)) =>
      Exists.casesOn (T.attaches lastEdgeIndex)
       fun (i : Fin ((↑lastEdgeIndex : ℕ) + (1 : ℕ)))
        (hi :
         G.ends (T.edge lastEdgeIndex) =
          s(T.vertex lastEdgeIndex.succ,
           T.vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ lastEdgeIndex.isLt))))) =>
       let ii : Fin (T.length + (1 : ℕ)) :=
        i.castLT (Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length + (1 : ℕ)) => by omega);
       have hmem : T.vertex penultimateVertexIndex ∈ s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
        id
         (fun (hinc : T.vertex penultimateVertexIndex ∈ G.ends (T.edge lastEdgeIndex)) =>
          Eq.mpr (id (propext Sym2.mem_iff))
           (Eq.mp (propext Sym2.mem_iff)
            (Eq.mp (congrArg (fun (_a : Sym2 V) => T.vertex penultimateVertexIndex ∈ _a) hi) hinc)))
         hinc;
       have hcases :
        T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ ∨
         T.vertex penultimateVertexIndex = T.vertex ii :=
        Sym2.mem_iff.mp hmem;
       Or.casesOn hcases
        (fun (hcase : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ) =>
         have hv : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ := hcase;
         have hi' : penultimateVertexIndex = lastEdgeIndex.succ := T.vertex_injective hv;
         have hv' : (↑penultimateVertexIndex : ℕ) = (↑lastEdgeIndex.succ : ℕ) :=
          congrArg Fin.val hi';
         False.elim (Eq.mp (Eq.trans (propext Nat.left_eq_add) (eq_false one_ne_zero)) hv'))
        fun (hcase : T.vertex penultimateVertexIndex = T.vertex ii) =>
        have hv : T.vertex penultimateVertexIndex = T.vertex ii := hcase;
        have hi' : penultimateVertexIndex = ii := T.vertex_injective hv;
        have hv' : (↑penultimateVertexIndex : ℕ) = (↑ii : ℕ) := congrArg Fin.val hi';
        have hlast : (↑i : ℕ) < T.length :=
         Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length) => by omega;
        have hii : ii = penultimateVertexIndex := Eq.symm hi';
        have hends : G.ends (T.edge lastEdgeIndex) = s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
         id hi;
        have htarget :
         G.ends (T.edge lastEdgeIndex) =
          s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex) :=
         Eq.mpr
          (id
           (congrArg
            (fun (_a : Sym2 V) =>
             _a = s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
            hends))
          (Eq.mpr
           (id
            (congrArg
             (fun (_a : Fin (T.length + (1 : ℕ))) =>
              s(T.vertex lastEdgeIndex.succ, T.vertex _a) =
               s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
             hii))
           (have hv : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
            congrArg T.vertex (Fin.ext (id hpenPos));
           Eq.mpr
            (id
             (congrArg
              (fun (_a : V) =>
               s(_a, T.vertex penultimateVertexIndex) =
                s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
              hv))
            Sym2.eq_swap));
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
        let ell : ℕ := T.length - A.length;
        let candidates : Finset ℕ :=
         {j ∈ Finset.Icc (1 : ℕ) ell |
          ∀ (r : Fin T.length),
           A.length + j ≤ (↑r : ℕ) → G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)};
        have htailA : (2 : ℕ) ≤ T.length - A.length := id htail;
        have hAle : A.length ≤ T.length :=
         Decidable.byContradiction fun (a : ¬A.length ≤ T.length) => by omega;
        have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAle;
        have hell : ell = T.length - A.length := rfl;
        have hmem : ell - (1 : ℕ) ∈ candidates :=
         Finset.mem_filter.mpr
          (⟨Finset.mem_Icc.mpr
             (⟨Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ ell - (1 : ℕ)) => by omega,
               Decidable.byContradiction fun (a : ¬ell - (1 : ℕ) ≤ ell) => by omega⟩ :
              (1 : ℕ) ≤ ell - (1 : ℕ) ∧ ell - (1 : ℕ) ≤ ell),
            fun (r : Fin T.length) (hr : A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ)) =>
            have hrval : (↑r : ℕ) = T.length - (1 : ℕ) :=
             Decidable.byContradiction fun (a : ¬(↑r : ℕ) = T.length - (1 : ℕ)) => by omega;
            have heq : r = lastEdgeIndex :=
             Fin.ext
              (of_eq_true
               (Eq.trans (congrFun' (congrArg Eq hrval) (T.length - (1 : ℕ)))
                (eq_self (T.length - (1 : ℕ)))));
            Eq.mpr
             (id
              (congrArg
               (fun (_a : Fin T.length) =>
                G.ends (T.edge _a) = s(T.vertex _a.castSucc, T.vertex _a.succ))
               heq))
             (have hv₁ : T.vertex lastEdgeIndex.castSucc = T.vertex penultimateVertexIndex :=
              congrArg T.vertex (Fin.ext (of_eq_true (eq_self (T.length - (1 : ℕ)))));
             have hv₂ : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
              congrArg T.vertex (Fin.ext (id hpenPos));
             Eq.mpr
              (id
               (congrArg
                (fun (_a : V) => G.ends (T.edge lastEdgeIndex) = s(_a, T.vertex lastEdgeIndex.succ))
                hv₁))
              (Eq.mpr
               (id
                (congrArg
                 (fun (_a : V) =>
                  G.ends (T.edge lastEdgeIndex) = s(T.vertex penultimateVertexIndex, _a))
                 hv₂))
               htarget))⟩ :
           ell - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) ell ∧
            ∀ (r : Fin T.length),
             A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ) →
              G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ));
        have hne : candidates.Nonempty := Exists.intro (ell - (1 : ℕ)) hmem;
        have hmin : candidates.min' hne ≤ ell - (1 : ℕ) :=
         Finset.min'_le candidates (ell - (1 : ℕ)) hmem;
        have hpath : HierarchyPathNumber C.hierarchy = candidates.min' hne :=
         of_eq_true
          (Eq.trans
           (congr
            (congrArg Eq
             ((fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
               (fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                  (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
                 dite_eq_left hne)
                x_0 x_1 x_2 x_3)
              Finset.decidableNonempty ℕ
              (fun
                (h :
                 {i ∈
                    Finset.Icc (1 : ℕ)
                     (T.length -
                      (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length) |
                   ∀ (r : Fin T.length),
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                       i ≤
                      (↑r : ℕ) →
                     G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
               {i ∈
                   Finset.Icc (1 : ℕ)
                    (T.length -
                     (HierarchyStarredStage C.hierarchy
                       (Fin.last C.hierarchy.dividerCount)).length) |
                  ∀ (r : Fin T.length),
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                      i ≤
                     (↑r : ℕ) →
                    G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
                h)
              fun
               (h :
                ¬{i ∈
                    Finset.Icc (1 : ℕ)
                     (T.length -
                      (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length) |
                   ∀ (r : Fin T.length),
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                       i ≤
                      (↑r : ℕ) →
                     G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
              T.length -
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length))
            (Finset.min'.congr_simp candidates
             ({i ∈
               Finset.Icc (1 : ℕ)
                (T.length -
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
              ∀ (r : Fin T.length),
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i ≤
                 (↑r : ℕ) →
                G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)})
             (Finset.filter_congr fun (x : ℕ) (a : x ∈ Finset.Icc (1 : ℕ) ell) =>
              Iff.of_eq
               (Eq.refl
                (∀ (r : Fin T.length),
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                    x ≤
                   (↑r : ℕ) →
                  G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ))))
             hne))
           (eq_self
            ({i ∈
                Finset.Icc (1 : ℕ)
                 (T.length -
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
               ∀ (r : Fin T.length),
                (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i ≤
                  (↑r : ℕ) →
                 G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
             hne)));
        have heq : candidates.min' hne = ell :=
         Trans.trans (Trans.trans (Eq.symm hpath) hsituation) (Eq.refl (HierarchyFullTailLength C));
        by omega,
     theta := theta, thetaOnLastEdge := htheta :
     HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx };
   ∀ alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex),
    hcommon.penultimateVertexIndex = penultimateVertexIndex →
     hcommon.terminalVertexIndex = terminalVertexIndex →
      alpha ∈ MissingColors G phi (T.vertex penultimateVertexIndex) →
       alpha ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) → False

private abbrev helperBranch407Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (hsituation : HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C)
  (htail :
   (2 : ℕ) ≤
    T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length)
  (hTtwo : (2 : ℕ) ≤ T.length),
  let lastEdgeIndex : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let penultimateVertexIndex : Fin (T.length + (1 : ℕ)) :=
   (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
  let terminalVertexIndex : Fin (T.length + (1 : ℕ)) := Fin.last T.length;
  ∀ (hlastPos : (↑lastEdgeIndex : ℕ) + (1 : ℕ) = T.length)
   (hpenPos : (↑penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length)
   (htermPos : (↑terminalVertexIndex : ℕ) = T.length) (theta : Fin k)
   (htheta : phi (T.edge lastEdgeIndex) = some theta),
   let hcommon : HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx :=
    {
     tailAtLeastTwo := htail, pathNumberFull := hsituation, lastEdgeIndex := lastEdgeIndex,
     penultimateVertexIndex := penultimateVertexIndex, terminalVertexIndex := terminalVertexIndex,
     lastEdgePosition := hlastPos, penultimateVertexPosition := hpenPos,
     terminalVertexPosition := htermPos,
     lastEdgeNotIncidentPenultimate :=
      fun (hinc : Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex)) =>
      Exists.casesOn (T.attaches lastEdgeIndex)
       fun (i : Fin ((↑lastEdgeIndex : ℕ) + (1 : ℕ)))
        (hi :
         G.ends (T.edge lastEdgeIndex) =
          s(T.vertex lastEdgeIndex.succ,
           T.vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ lastEdgeIndex.isLt))))) =>
       let ii : Fin (T.length + (1 : ℕ)) :=
        i.castLT (Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length + (1 : ℕ)) => by omega);
       have hmem : T.vertex penultimateVertexIndex ∈ s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
        id
         (fun (hinc : T.vertex penultimateVertexIndex ∈ G.ends (T.edge lastEdgeIndex)) =>
          Eq.mpr (id (propext Sym2.mem_iff))
           (Eq.mp (propext Sym2.mem_iff)
            (Eq.mp (congrArg (fun (_a : Sym2 V) => T.vertex penultimateVertexIndex ∈ _a) hi) hinc)))
         hinc;
       have hcases :
        T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ ∨
         T.vertex penultimateVertexIndex = T.vertex ii :=
        Sym2.mem_iff.mp hmem;
       Or.casesOn hcases
        (fun (hcase : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ) =>
         have hv : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ := hcase;
         have hi' : penultimateVertexIndex = lastEdgeIndex.succ := T.vertex_injective hv;
         have hv' : (↑penultimateVertexIndex : ℕ) = (↑lastEdgeIndex.succ : ℕ) :=
          congrArg Fin.val hi';
         False.elim (Eq.mp (Eq.trans (propext Nat.left_eq_add) (eq_false one_ne_zero)) hv'))
        fun (hcase : T.vertex penultimateVertexIndex = T.vertex ii) =>
        have hv : T.vertex penultimateVertexIndex = T.vertex ii := hcase;
        have hi' : penultimateVertexIndex = ii := T.vertex_injective hv;
        have hv' : (↑penultimateVertexIndex : ℕ) = (↑ii : ℕ) := congrArg Fin.val hi';
        have hlast : (↑i : ℕ) < T.length :=
         Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length) => by omega;
        have hii : ii = penultimateVertexIndex := Eq.symm hi';
        have hends : G.ends (T.edge lastEdgeIndex) = s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
         id hi;
        have htarget :
         G.ends (T.edge lastEdgeIndex) =
          s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex) :=
         Eq.mpr
          (id
           (congrArg
            (fun (_a : Sym2 V) =>
             _a = s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
            hends))
          (Eq.mpr
           (id
            (congrArg
             (fun (_a : Fin (T.length + (1 : ℕ))) =>
              s(T.vertex lastEdgeIndex.succ, T.vertex _a) =
               s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
             hii))
           (have hv : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
            congrArg T.vertex (Fin.ext (id hpenPos));
           Eq.mpr
            (id
             (congrArg
              (fun (_a : V) =>
               s(_a, T.vertex penultimateVertexIndex) =
                s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
              hv))
            Sym2.eq_swap));
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
        let ell : ℕ := T.length - A.length;
        let candidates : Finset ℕ :=
         {j ∈ Finset.Icc (1 : ℕ) ell |
          ∀ (r : Fin T.length),
           A.length + j ≤ (↑r : ℕ) → G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)};
        have htailA : (2 : ℕ) ≤ T.length - A.length := id htail;
        have hAle : A.length ≤ T.length :=
         Decidable.byContradiction fun (a : ¬A.length ≤ T.length) => by omega;
        have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAle;
        have hell : ell = T.length - A.length := rfl;
        have hmem : ell - (1 : ℕ) ∈ candidates :=
         Finset.mem_filter.mpr
          (⟨Finset.mem_Icc.mpr
             (⟨Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ ell - (1 : ℕ)) => by omega,
               Decidable.byContradiction fun (a : ¬ell - (1 : ℕ) ≤ ell) => by omega⟩ :
              (1 : ℕ) ≤ ell - (1 : ℕ) ∧ ell - (1 : ℕ) ≤ ell),
            fun (r : Fin T.length) (hr : A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ)) =>
            have hrval : (↑r : ℕ) = T.length - (1 : ℕ) :=
             Decidable.byContradiction fun (a : ¬(↑r : ℕ) = T.length - (1 : ℕ)) => by omega;
            have heq : r = lastEdgeIndex :=
             Fin.ext
              (of_eq_true
               (Eq.trans (congrFun' (congrArg Eq hrval) (T.length - (1 : ℕ)))
                (eq_self (T.length - (1 : ℕ)))));
            Eq.mpr
             (id
              (congrArg
               (fun (_a : Fin T.length) =>
                G.ends (T.edge _a) = s(T.vertex _a.castSucc, T.vertex _a.succ))
               heq))
             (have hv₁ : T.vertex lastEdgeIndex.castSucc = T.vertex penultimateVertexIndex :=
              congrArg T.vertex (Fin.ext (of_eq_true (eq_self (T.length - (1 : ℕ)))));
             have hv₂ : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
              congrArg T.vertex (Fin.ext (id hpenPos));
             Eq.mpr
              (id
               (congrArg
                (fun (_a : V) => G.ends (T.edge lastEdgeIndex) = s(_a, T.vertex lastEdgeIndex.succ))
                hv₁))
              (Eq.mpr
               (id
                (congrArg
                 (fun (_a : V) =>
                  G.ends (T.edge lastEdgeIndex) = s(T.vertex penultimateVertexIndex, _a))
                 hv₂))
               htarget))⟩ :
           ell - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) ell ∧
            ∀ (r : Fin T.length),
             A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ) →
              G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ));
        have hne : candidates.Nonempty := Exists.intro (ell - (1 : ℕ)) hmem;
        have hmin : candidates.min' hne ≤ ell - (1 : ℕ) :=
         Finset.min'_le candidates (ell - (1 : ℕ)) hmem;
        have hpath : HierarchyPathNumber C.hierarchy = candidates.min' hne :=
         of_eq_true
          (Eq.trans
           (congr
            (congrArg Eq
             ((fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
               (fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                  (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
                 dite_eq_left hne)
                x_0 x_1 x_2 x_3)
              Finset.decidableNonempty ℕ
              (fun
                (h :
                 {i ∈
                    Finset.Icc (1 : ℕ)
                     (T.length -
                      (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length) |
                   ∀ (r : Fin T.length),
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                       i ≤
                      (↑r : ℕ) →
                     G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
               {i ∈
                   Finset.Icc (1 : ℕ)
                    (T.length -
                     (HierarchyStarredStage C.hierarchy
                       (Fin.last C.hierarchy.dividerCount)).length) |
                  ∀ (r : Fin T.length),
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                      i ≤
                     (↑r : ℕ) →
                    G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
                h)
              fun
               (h :
                ¬{i ∈
                    Finset.Icc (1 : ℕ)
                     (T.length -
                      (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length) |
                   ∀ (r : Fin T.length),
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                       i ≤
                      (↑r : ℕ) →
                     G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
              T.length -
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length))
            (Finset.min'.congr_simp candidates
             ({i ∈
               Finset.Icc (1 : ℕ)
                (T.length -
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
              ∀ (r : Fin T.length),
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i ≤
                 (↑r : ℕ) →
                G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)})
             (Finset.filter_congr fun (x : ℕ) (a : x ∈ Finset.Icc (1 : ℕ) ell) =>
              Iff.of_eq
               (Eq.refl
                (∀ (r : Fin T.length),
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                    x ≤
                   (↑r : ℕ) →
                  G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ))))
             hne))
           (eq_self
            ({i ∈
                Finset.Icc (1 : ℕ)
                 (T.length -
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
               ∀ (r : Fin T.length),
                (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i ≤
                  (↑r : ℕ) →
                 G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
             hne)));
        have heq : candidates.min' hne = ell :=
         Trans.trans (Trans.trans (Eq.symm hpath) hsituation) (Eq.refl (HierarchyFullTailLength C));
        by omega,
     theta := theta, thetaOnLastEdge := htheta :
     HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx };
   ∀ alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex),
    hcommon.penultimateVertexIndex = penultimateVertexIndex →
     hcommon.terminalVertexIndex = terminalVertexIndex →
      alpha ∈ MissingColors G phi (T.vertex penultimateVertexIndex) →
       alpha ∉ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) → False

private abbrev helperBranch204Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (hsituation : HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C)
  (htail :
   (2 : ℕ) ≤
    T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length)
  (hTtwo : (2 : ℕ) ≤ T.length),
  let lastEdgeIndex : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let penultimateVertexIndex : Fin (T.length + (1 : ℕ)) :=
   (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
  let terminalVertexIndex : Fin (T.length + (1 : ℕ)) := Fin.last T.length;
  ∀ (hlastPos : (↑lastEdgeIndex : ℕ) + (1 : ℕ) = T.length)
   (hpenPos : (↑penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length)
   (htermPos : (↑terminalVertexIndex : ℕ) = T.length) (theta : Fin k)
   (htheta : phi (T.edge lastEdgeIndex) = some theta),
   let hcommon : HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx :=
    {
     tailAtLeastTwo := htail, pathNumberFull := hsituation, lastEdgeIndex := lastEdgeIndex,
     penultimateVertexIndex := penultimateVertexIndex, terminalVertexIndex := terminalVertexIndex,
     lastEdgePosition := hlastPos, penultimateVertexPosition := hpenPos,
     terminalVertexPosition := htermPos,
     lastEdgeNotIncidentPenultimate :=
      fun (hinc : Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex)) =>
      Exists.casesOn (T.attaches lastEdgeIndex)
       fun (i : Fin ((↑lastEdgeIndex : ℕ) + (1 : ℕ)))
        (hi :
         G.ends (T.edge lastEdgeIndex) =
          s(T.vertex lastEdgeIndex.succ,
           T.vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ lastEdgeIndex.isLt))))) =>
       let ii : Fin (T.length + (1 : ℕ)) :=
        i.castLT (Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length + (1 : ℕ)) => by omega);
       have hmem : T.vertex penultimateVertexIndex ∈ s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
        id
         (fun (hinc : T.vertex penultimateVertexIndex ∈ G.ends (T.edge lastEdgeIndex)) =>
          Eq.mpr (id (propext Sym2.mem_iff))
           (Eq.mp (propext Sym2.mem_iff)
            (Eq.mp (congrArg (fun (_a : Sym2 V) => T.vertex penultimateVertexIndex ∈ _a) hi) hinc)))
         hinc;
       have hcases :
        T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ ∨
         T.vertex penultimateVertexIndex = T.vertex ii :=
        Sym2.mem_iff.mp hmem;
       Or.casesOn hcases
        (fun (hcase : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ) =>
         have hv : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ := hcase;
         have hi' : penultimateVertexIndex = lastEdgeIndex.succ := T.vertex_injective hv;
         have hv' : (↑penultimateVertexIndex : ℕ) = (↑lastEdgeIndex.succ : ℕ) :=
          congrArg Fin.val hi';
         False.elim (Eq.mp (Eq.trans (propext Nat.left_eq_add) (eq_false one_ne_zero)) hv'))
        fun (hcase : T.vertex penultimateVertexIndex = T.vertex ii) =>
        have hv : T.vertex penultimateVertexIndex = T.vertex ii := hcase;
        have hi' : penultimateVertexIndex = ii := T.vertex_injective hv;
        have hv' : (↑penultimateVertexIndex : ℕ) = (↑ii : ℕ) := congrArg Fin.val hi';
        have hlast : (↑i : ℕ) < T.length :=
         Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length) => by omega;
        have hii : ii = penultimateVertexIndex := Eq.symm hi';
        have hends : G.ends (T.edge lastEdgeIndex) = s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
         id hi;
        have htarget :
         G.ends (T.edge lastEdgeIndex) =
          s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex) :=
         Eq.mpr
          (id
           (congrArg
            (fun (_a : Sym2 V) =>
             _a = s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
            hends))
          (Eq.mpr
           (id
            (congrArg
             (fun (_a : Fin (T.length + (1 : ℕ))) =>
              s(T.vertex lastEdgeIndex.succ, T.vertex _a) =
               s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
             hii))
           (have hv : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
            congrArg T.vertex (Fin.ext (id hpenPos));
           Eq.mpr
            (id
             (congrArg
              (fun (_a : V) =>
               s(_a, T.vertex penultimateVertexIndex) =
                s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
              hv))
            Sym2.eq_swap));
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
        let ell : ℕ := T.length - A.length;
        let candidates : Finset ℕ :=
         {j ∈ Finset.Icc (1 : ℕ) ell |
          ∀ (r : Fin T.length),
           A.length + j ≤ (↑r : ℕ) → G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)};
        have htailA : (2 : ℕ) ≤ T.length - A.length := id htail;
        have hAle : A.length ≤ T.length :=
         Decidable.byContradiction fun (a : ¬A.length ≤ T.length) => by omega;
        have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAle;
        have hell : ell = T.length - A.length := rfl;
        have hmem : ell - (1 : ℕ) ∈ candidates :=
         Finset.mem_filter.mpr
          (⟨Finset.mem_Icc.mpr
             (⟨Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ ell - (1 : ℕ)) => by omega,
               Decidable.byContradiction fun (a : ¬ell - (1 : ℕ) ≤ ell) => by omega⟩ :
              (1 : ℕ) ≤ ell - (1 : ℕ) ∧ ell - (1 : ℕ) ≤ ell),
            fun (r : Fin T.length) (hr : A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ)) =>
            have hrval : (↑r : ℕ) = T.length - (1 : ℕ) :=
             Decidable.byContradiction fun (a : ¬(↑r : ℕ) = T.length - (1 : ℕ)) => by omega;
            have heq : r = lastEdgeIndex :=
             Fin.ext
              (of_eq_true
               (Eq.trans (congrFun' (congrArg Eq hrval) (T.length - (1 : ℕ)))
                (eq_self (T.length - (1 : ℕ)))));
            Eq.mpr
             (id
              (congrArg
               (fun (_a : Fin T.length) =>
                G.ends (T.edge _a) = s(T.vertex _a.castSucc, T.vertex _a.succ))
               heq))
             (have hv₁ : T.vertex lastEdgeIndex.castSucc = T.vertex penultimateVertexIndex :=
              congrArg T.vertex (Fin.ext (of_eq_true (eq_self (T.length - (1 : ℕ)))));
             have hv₂ : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
              congrArg T.vertex (Fin.ext (id hpenPos));
             Eq.mpr
              (id
               (congrArg
                (fun (_a : V) => G.ends (T.edge lastEdgeIndex) = s(_a, T.vertex lastEdgeIndex.succ))
                hv₁))
              (Eq.mpr
               (id
                (congrArg
                 (fun (_a : V) =>
                  G.ends (T.edge lastEdgeIndex) = s(T.vertex penultimateVertexIndex, _a))
                 hv₂))
               htarget))⟩ :
           ell - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) ell ∧
            ∀ (r : Fin T.length),
             A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ) →
              G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ));
        have hne : candidates.Nonempty := Exists.intro (ell - (1 : ℕ)) hmem;
        have hmin : candidates.min' hne ≤ ell - (1 : ℕ) :=
         Finset.min'_le candidates (ell - (1 : ℕ)) hmem;
        have hpath : HierarchyPathNumber C.hierarchy = candidates.min' hne :=
         of_eq_true
          (Eq.trans
           (congr
            (congrArg Eq
             ((fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
               (fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                  (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
                 dite_eq_left hne)
                x_0 x_1 x_2 x_3)
              Finset.decidableNonempty ℕ
              (fun
                (h :
                 {i ∈
                    Finset.Icc (1 : ℕ)
                     (T.length -
                      (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length) |
                   ∀ (r : Fin T.length),
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                       i ≤
                      (↑r : ℕ) →
                     G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
               {i ∈
                   Finset.Icc (1 : ℕ)
                    (T.length -
                     (HierarchyStarredStage C.hierarchy
                       (Fin.last C.hierarchy.dividerCount)).length) |
                  ∀ (r : Fin T.length),
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                      i ≤
                     (↑r : ℕ) →
                    G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
                h)
              fun
               (h :
                ¬{i ∈
                    Finset.Icc (1 : ℕ)
                     (T.length -
                      (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length) |
                   ∀ (r : Fin T.length),
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                       i ≤
                      (↑r : ℕ) →
                     G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
              T.length -
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length))
            (Finset.min'.congr_simp candidates
             ({i ∈
               Finset.Icc (1 : ℕ)
                (T.length -
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
              ∀ (r : Fin T.length),
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i ≤
                 (↑r : ℕ) →
                G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)})
             (Finset.filter_congr fun (x : ℕ) (a : x ∈ Finset.Icc (1 : ℕ) ell) =>
              Iff.of_eq
               (Eq.refl
                (∀ (r : Fin T.length),
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                    x ≤
                   (↑r : ℕ) →
                  G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ))))
             hne))
           (eq_self
            ({i ∈
                Finset.Icc (1 : ℕ)
                 (T.length -
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
               ∀ (r : Fin T.length),
                (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + i ≤
                  (↑r : ℕ) →
                 G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
             hne)));
        have heq : candidates.min' hne = ell :=
         Trans.trans (Trans.trans (Eq.symm hpath) hsituation) (Eq.refl (HierarchyFullTailLength C));
        by omega,
     theta := theta, thetaOnLastEdge := htheta :
     HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx };
   ∀ alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex),
    hcommon.penultimateVertexIndex = penultimateVertexIndex →
     hcommon.terminalVertexIndex = terminalVertexIndex →
      alpha ∈ MissingColors G phi (T.vertex penultimateVertexIndex) → False

private abbrev helperBranch252Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (hsituation : HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C)
  (htail :
   (2 : ℕ) ≤
    T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length)
  (hTtwo : (2 : ℕ) ≤ T.length),
  let lastEdgeIndex : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let penultimateVertexIndex : Fin (T.length + (1 : ℕ)) :=
   (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
  let terminalVertexIndex : Fin (T.length + (1 : ℕ)) := Fin.last T.length;
  ∀ (hlastPos : (↑lastEdgeIndex : ℕ) + (1 : ℕ) = T.length)
   (hpenPos : (↑penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length)
   (htermPos : (↑terminalVertexIndex : ℕ) = T.length),
   lastEdgeIndex ≠ (⟨(0 : ℕ), T.positive⟩ : Fin T.length) →
    ∀ (theta : Fin k) (htheta : phi (T.edge lastEdgeIndex) = some theta),
     let hcommon : HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx :=
      {
       tailAtLeastTwo := htail, pathNumberFull := hsituation, lastEdgeIndex := lastEdgeIndex,
       penultimateVertexIndex := penultimateVertexIndex, terminalVertexIndex := terminalVertexIndex,
       lastEdgePosition := hlastPos, penultimateVertexPosition := hpenPos,
       terminalVertexPosition := htermPos,
       lastEdgeNotIncidentPenultimate :=
        fun (hinc : Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex)) =>
        Exists.casesOn (T.attaches lastEdgeIndex)
         fun (i : Fin ((↑lastEdgeIndex : ℕ) + (1 : ℕ)))
          (hi :
           G.ends (T.edge lastEdgeIndex) =
            s(T.vertex lastEdgeIndex.succ,
             T.vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ lastEdgeIndex.isLt))))) =>
         let ii : Fin (T.length + (1 : ℕ)) :=
          i.castLT (Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length + (1 : ℕ)) => by omega);
         have hmem :
          T.vertex penultimateVertexIndex ∈ s(T.vertex lastEdgeIndex.succ, T.vertex ii) :=
          id
           (fun (hinc : T.vertex penultimateVertexIndex ∈ G.ends (T.edge lastEdgeIndex)) =>
            Eq.mpr (id (propext Sym2.mem_iff))
             (Eq.mp (propext Sym2.mem_iff)
              (Eq.mp (congrArg (fun (_a : Sym2 V) => T.vertex penultimateVertexIndex ∈ _a) hi)
               hinc)))
           hinc;
         have hcases :
          T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ ∨
           T.vertex penultimateVertexIndex = T.vertex ii :=
          Sym2.mem_iff.mp hmem;
         Or.casesOn hcases
          (fun (hcase : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ) =>
           have hv : T.vertex penultimateVertexIndex = T.vertex lastEdgeIndex.succ := hcase;
           have hi' : penultimateVertexIndex = lastEdgeIndex.succ := T.vertex_injective hv;
           have hv' : (↑penultimateVertexIndex : ℕ) = (↑lastEdgeIndex.succ : ℕ) :=
            congrArg Fin.val hi';
           False.elim (Eq.mp (Eq.trans (propext Nat.left_eq_add) (eq_false one_ne_zero)) hv'))
          fun (hcase : T.vertex penultimateVertexIndex = T.vertex ii) =>
          have hv : T.vertex penultimateVertexIndex = T.vertex ii := hcase;
          have hi' : penultimateVertexIndex = ii := T.vertex_injective hv;
          have hv' : (↑penultimateVertexIndex : ℕ) = (↑ii : ℕ) := congrArg Fin.val hi';
          have hlast : (↑i : ℕ) < T.length :=
           Decidable.byContradiction fun (a : ¬(↑i : ℕ) < T.length) => by omega;
          have hii : ii = penultimateVertexIndex := Eq.symm hi';
          have hends :
           G.ends (T.edge lastEdgeIndex) = s(T.vertex lastEdgeIndex.succ, T.vertex ii) := id hi;
          have htarget :
           G.ends (T.edge lastEdgeIndex) =
            s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex) :=
           Eq.mpr
            (id
             (congrArg
              (fun (_a : Sym2 V) =>
               _a = s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
              hends))
            (Eq.mpr
             (id
              (congrArg
               (fun (_a : Fin (T.length + (1 : ℕ))) =>
                s(T.vertex lastEdgeIndex.succ, T.vertex _a) =
                 s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
               hii))
             (have hv : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
              congrArg T.vertex (Fin.ext (id hpenPos));
             Eq.mpr
              (id
               (congrArg
                (fun (_a : V) =>
                 s(_a, T.vertex penultimateVertexIndex) =
                  s(T.vertex penultimateVertexIndex, T.vertex terminalVertexIndex))
                hv))
              Sym2.eq_swap));
          let H : TashkinovHierarchy ett base := C.hierarchy;
          let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
          let ell : ℕ := T.length - A.length;
          let candidates : Finset ℕ :=
           {j ∈ Finset.Icc (1 : ℕ) ell |
            ∀ (r : Fin T.length),
             A.length + j ≤ (↑r : ℕ) → G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)};
          have htailA : (2 : ℕ) ≤ T.length - A.length := id htail;
          have hAle : A.length ≤ T.length :=
           Decidable.byContradiction fun (a : ¬A.length ≤ T.length) => by omega;
          have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAle;
          have hell : ell = T.length - A.length := rfl;
          have hmem : ell - (1 : ℕ) ∈ candidates :=
           Finset.mem_filter.mpr
            (⟨Finset.mem_Icc.mpr
               (⟨Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ ell - (1 : ℕ)) => by omega,
                 Decidable.byContradiction fun (a : ¬ell - (1 : ℕ) ≤ ell) => by omega⟩ :
                (1 : ℕ) ≤ ell - (1 : ℕ) ∧ ell - (1 : ℕ) ≤ ell),
              fun (r : Fin T.length) (hr : A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ)) =>
              have hrval : (↑r : ℕ) = T.length - (1 : ℕ) :=
               Decidable.byContradiction fun (a : ¬(↑r : ℕ) = T.length - (1 : ℕ)) => by omega;
              have heq : r = lastEdgeIndex :=
               Fin.ext
                (of_eq_true
                 (Eq.trans (congrFun' (congrArg Eq hrval) (T.length - (1 : ℕ)))
                  (eq_self (T.length - (1 : ℕ)))));
              Eq.mpr
               (id
                (congrArg
                 (fun (_a : Fin T.length) =>
                  G.ends (T.edge _a) = s(T.vertex _a.castSucc, T.vertex _a.succ))
                 heq))
               (have hv₁ : T.vertex lastEdgeIndex.castSucc = T.vertex penultimateVertexIndex :=
                congrArg T.vertex (Fin.ext (of_eq_true (eq_self (T.length - (1 : ℕ)))));
               have hv₂ : T.vertex lastEdgeIndex.succ = T.vertex terminalVertexIndex :=
                congrArg T.vertex (Fin.ext (id hpenPos));
               Eq.mpr
                (id
                 (congrArg
                  (fun (_a : V) =>
                   G.ends (T.edge lastEdgeIndex) = s(_a, T.vertex lastEdgeIndex.succ))
                  hv₁))
                (Eq.mpr
                 (id
                  (congrArg
                   (fun (_a : V) =>
                    G.ends (T.edge lastEdgeIndex) = s(T.vertex penultimateVertexIndex, _a))
                   hv₂))
                 htarget))⟩ :
             ell - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) ell ∧
              ∀ (r : Fin T.length),
               A.length + (ell - (1 : ℕ)) ≤ (↑r : ℕ) →
                G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ));
          have hne : candidates.Nonempty := Exists.intro (ell - (1 : ℕ)) hmem;
          have hmin : candidates.min' hne ≤ ell - (1 : ℕ) :=
           Finset.min'_le candidates (ell - (1 : ℕ)) hmem;
          have hpath : HierarchyPathNumber C.hierarchy = candidates.min' hne :=
           of_eq_true
            (Eq.trans
             (congr
              (congrArg Eq
               ((fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                  (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
                 (fun (x_0 : Decidable candidates.Nonempty) (x_1 : Type)
                    (x_2 : candidates.Nonempty → x_1) (x_3 : ¬candidates.Nonempty → x_1) =>
                   dite_eq_left hne)
                  x_0 x_1 x_2 x_3)
                Finset.decidableNonempty ℕ
                (fun
                  (h :
                   {i ∈
                      Finset.Icc (1 : ℕ)
                       (T.length -
                        (HierarchyStarredStage C.hierarchy
                          (Fin.last C.hierarchy.dividerCount)).length) |
                     ∀ (r : Fin T.length),
                      (HierarchyStarredStage C.hierarchy
                           (Fin.last C.hierarchy.dividerCount)).length +
                         i ≤
                        (↑r : ℕ) →
                       G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
                 {i ∈
                     Finset.Icc (1 : ℕ)
                      (T.length -
                       (HierarchyStarredStage C.hierarchy
                         (Fin.last C.hierarchy.dividerCount)).length) |
                    ∀ (r : Fin T.length),
                     (HierarchyStarredStage C.hierarchy
                          (Fin.last C.hierarchy.dividerCount)).length +
                        i ≤
                       (↑r : ℕ) →
                      G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
                  h)
                fun
                 (h :
                  ¬{i ∈
                      Finset.Icc (1 : ℕ)
                       (T.length -
                        (HierarchyStarredStage C.hierarchy
                          (Fin.last C.hierarchy.dividerCount)).length) |
                     ∀ (r : Fin T.length),
                      (HierarchyStarredStage C.hierarchy
                           (Fin.last C.hierarchy.dividerCount)).length +
                         i ≤
                        (↑r : ℕ) →
                       G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.Nonempty) =>
                T.length -
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length))
              (Finset.min'.congr_simp candidates
               ({i ∈
                 Finset.Icc (1 : ℕ)
                  (T.length -
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length) |
                ∀ (r : Fin T.length),
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                    i ≤
                   (↑r : ℕ) →
                  G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)})
               (Finset.filter_congr fun (x : ℕ) (a : x ∈ Finset.Icc (1 : ℕ) ell) =>
                Iff.of_eq
                 (Eq.refl
                  (∀ (r : Fin T.length),
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                      x ≤
                     (↑r : ℕ) →
                    G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ))))
               hne))
             (eq_self
              ({i ∈
                  Finset.Icc (1 : ℕ)
                   (T.length -
                    (HierarchyStarredStage C.hierarchy
                      (Fin.last C.hierarchy.dividerCount)).length) |
                 ∀ (r : Fin T.length),
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
                     i ≤
                    (↑r : ℕ) →
                   G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)}.min'
               hne)));
          have heq : candidates.min' hne = ell :=
           Trans.trans (Trans.trans (Eq.symm hpath) hsituation)
            (Eq.refl (HierarchyFullTailLength C));
          by omega,
       theta := theta, thetaOnLastEdge := htheta :
       HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx };
     ∀
      alpha ∈
       TreeMissingColors phi
        (TreeSequencePrefix T
         (min
          ((HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
           (T.length -
             (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length -
            (1 : ℕ)))
          T.length)
         ((by omega))
         (Nat.min_le_right
          ((HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
           (T.length -
             (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length -
            (1 : ℕ)))
          T.length)),
      alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex) →
       hcommon.penultimateVertexIndex = penultimateVertexIndex →
        hcommon.terminalVertexIndex = terminalVertexIndex →
         alpha ∉ MissingColors G phi (T.vertex penultimateVertexIndex) → False

private theorem helper_branch_109.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C →
    (2 : ℕ) ≤
        T.length -
          (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length →
    ∀ (hTtwo : (2 : ℕ) ≤ T.length),
    let lastEdgeIndex : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
    let penultimateVertexIndex : Fin (T.length + (1 : ℕ)) :=
      (⟨T.length - (1 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    let terminalVertexIndex : Fin (T.length + (1 : ℕ)) := Fin.last T.length;
    (↑lastEdgeIndex : ℕ) + (1 : ℕ) = T.length →
    (↑penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length →
    (↑terminalVertexIndex : ℕ) = T.length →
    ¬Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hsituation htail hTtwo lastEdgeIndex
      penultimateVertexIndex terminalVertexIndex hlastPos hpenPos htermPos hinc
  obtain ⟨i, hi⟩ := T.attaches lastEdgeIndex
  let ii : Fin (T.length + 1) := i.castLT (by omega)
  have hmem : T.vertex penultimateVertexIndex ∈
      s(T.vertex lastEdgeIndex.succ, T.vertex ii) := by
    change T.vertex penultimateVertexIndex ∈ G.ends (T.edge lastEdgeIndex) at hinc
    rw [hi] at hinc
    simpa [ii] using hinc
  have hcases := (Sym2.mem_iff.mp hmem)
  rcases hcases with hcase | hcase
  · have hv : T.vertex penultimateVertexIndex =
        T.vertex lastEdgeIndex.succ := hcase
    have hi' : penultimateVertexIndex = lastEdgeIndex.succ :=
      T.vertex_injective hv
    have hv' := congrArg Fin.val hi'
    simp [penultimateVertexIndex, lastEdgeIndex] at hv'
  · have hv : T.vertex penultimateVertexIndex = T.vertex ii := hcase
    have hi' : penultimateVertexIndex = ii := T.vertex_injective hv
    have hv' := congrArg Fin.val hi'
    have hlast : i.val < T.length := by omega
    dsimp [ii] at hi'
    dsimp [penultimateVertexIndex] at hv'
    have hii : ii = penultimateVertexIndex := hi'.symm
    have hends : G.ends (T.edge lastEdgeIndex) =
        s(T.vertex lastEdgeIndex.succ, T.vertex ii) := by
      simpa [ii] using hi
    have htarget : G.ends (T.edge lastEdgeIndex) =
        s(T.vertex penultimateVertexIndex,
          T.vertex terminalVertexIndex) := by
      rw [hends, hii]
      have hv : T.vertex lastEdgeIndex.succ =
          T.vertex terminalVertexIndex := by
        apply congrArg T.vertex
        apply Fin.ext
        simp [lastEdgeIndex, terminalVertexIndex]
        omega
      rw [hv]
      exact Sym2.eq_swap
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let ell := T.length - A.length
    let candidates := (Finset.Icc 1 ell).filter fun j =>
      ∀ r : Fin T.length, A.length + j ≤ r.val →
        G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)
    have htailA : 2 ≤ T.length - A.length := by
      simpa [A, H] using htail
    have hAle : A.length ≤ T.length := by omega
    have hsum : A.length + ell = T.length :=
      Nat.add_sub_of_le hAle
    have hell : ell = T.length - A.length := rfl
    have hmem : ell - 1 ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      intro r hr
      have hrval : r.val = T.length - 1 := by
        omega
      have heq : r = lastEdgeIndex := by
        apply Fin.ext
        simp [lastEdgeIndex, hrval]
      rw [heq]
      have hv₁ : T.vertex lastEdgeIndex.castSucc =
          T.vertex penultimateVertexIndex := by
        apply congrArg T.vertex
        apply Fin.ext
        simp [lastEdgeIndex, penultimateVertexIndex]
      have hv₂ : T.vertex lastEdgeIndex.succ =
          T.vertex terminalVertexIndex := by
        apply congrArg T.vertex
        apply Fin.ext
        simp [lastEdgeIndex, terminalVertexIndex]
        omega
      rw [hv₁, hv₂]
      exact htarget
    have hne : candidates.Nonempty := ⟨ell - 1, hmem⟩
    have hmin : candidates.min' hne ≤ ell - 1 :=
      Finset.min'_le candidates (ell - 1) hmem
    have hpath : HierarchyPathNumber C.hierarchy = candidates.min' hne := by
      simp [HierarchyPathNumber, H, A, ell, candidates, dite_eq_left hne]
    have heq : candidates.min' hne = ell := by
      calc
        candidates.min' hne = HierarchyPathNumber C.hierarchy := hpath.symm
        _ = HierarchyFullTailLength C := hsituation
        _ = ell := by rfl
    omega

private theorem helper_branch_381.{u_1, u_2} :
    helperBranch381Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation htail hTtwo lastEdgeIndex
      penultimateVertexIndex terminalVertexIndex hlastPos hpenPos htermPos theta htheta hcommon
      alpha halphaFinal hidxPen hidxTerm hpen hstored
  have hcard := C.good.twoColors (Fin.last C.hierarchy.dividerCount)
      alpha hstored
  obtain ⟨gammaOne, gammaTwo, hdistinct, hpair⟩ :=
    Finset.card_eq_two.mp hcard
  by_cases hmissing : theta ∈ MissingColors G phi
      (T.vertex penultimateVertexIndex)
  · let D : HierarchySituationTwoCaseOneTwoData
        G k e0 input T phi ett base C ctx :=
      ⟨hcommon, alpha, gammaOne, gammaTwo,
        (by simpa [hidxPen] using hpen),
        (by simpa [hidxTerm] using halphaFinal),
        hstored, by simpa using hpair, hdistinct, hmissing⟩
    exact HierarchySituationTwoSubcaseOneTwo
      G k e0 input T phi ett base C ctx D
  · let tail : HierarchySituationTwoTailData
        G k e0 input T phi ett base C ctx :=
      ⟨htail, hsituation, lastEdgeIndex, penultimateVertexIndex,
        terminalVertexIndex, hlastPos, hpenPos, htermPos,
        (by simpa using hcommon.lastEdgeNotIncidentPenultimate), theta,
        htheta, (by simpa [hidxPen] using hmissing)⟩
    let D : HierarchySituationTwoCaseOneData
        G k e0 input T phi ett base C ctx :=
      ⟨tail, alpha, gammaOne, gammaTwo, hpen, halphaFinal,
        hstored, by simpa using hpair, hdistinct⟩
    exact HierarchySituationTwoSubcaseOneOne
      G k e0 input T phi ett base C ctx D

private theorem helper_branch_407.{u_1, u_2} :
    helperBranch407Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation htail hTtwo lastEdgeIndex
      penultimateVertexIndex terminalVertexIndex hlastPos hpenPos htermPos theta htheta hcommon
      alpha halphaFinal hidxPen hidxTerm hpen hstored
  by_cases hmissing : theta ∈ MissingColors G phi
      (T.vertex penultimateVertexIndex)
  · let D : HierarchySituationTwoCaseTwoTwoData
        G k e0 input T phi ett base C ctx :=
      ⟨hcommon, alpha, (by simpa [hidxPen] using hpen),
        (by simpa [hidxTerm] using halphaFinal), hstored,
        (by simpa [hidxPen] using hmissing)⟩
    exact HierarchySituationTwoSubcaseTwoTwo
      G k e0 input T phi ett base C ctx D
  · let tail : HierarchySituationTwoTailData
        G k e0 input T phi ett base C ctx :=
      ⟨htail, hsituation, lastEdgeIndex, penultimateVertexIndex,
        terminalVertexIndex, hlastPos, hpenPos, htermPos,
        (by simpa using hcommon.lastEdgeNotIncidentPenultimate), theta,
        htheta, (by simpa [hidxPen] using hmissing)⟩
    let D : HierarchySituationTwoCaseTwoData
        G k e0 input T phi ett base C ctx :=
      ⟨tail, alpha, hpen, halphaFinal, hstored⟩
    exact HierarchySituationTwoSubcaseTwoOne
      G k e0 input T phi ett base C ctx D

private theorem helper_branch_204.{u_1, u_2} :
    helperBranch204Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation htail hTtwo lastEdgeIndex
      penultimateVertexIndex terminalVertexIndex hlastPos hpenPos htermPos theta htheta hcommon
      alpha halphaFinal hidxPen hidxTerm hpen
  by_cases hstored : alpha ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount)
  · exact @helper_branch_381 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation htail hTtwo hlastPos hpenPos htermPos theta htheta
      alpha halphaFinal hidxPen hidxTerm hpen hstored
  · exact @helper_branch_407 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation htail hTtwo hlastPos hpenPos htermPos theta htheta
      alpha halphaFinal hidxPen hidxTerm hpen hstored
private theorem helper_branch_252.{u_1, u_2} :
    helperBranch252Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation htail hTtwo lastEdgeIndex
      penultimateVertexIndex terminalVertexIndex hlastPos hpenPos htermPos hlastNeFirst theta
      htheta hcommon alpha halphaTree halphaFinal hidxPen hidxTerm hpen
  let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have hB : alpha ∈ TreeMissingColors phi Bplus := by
    simpa [Bplus, HierarchyFullTailPrefix, HierarchyFullTailLength] using halphaTree
  simp only [TreeMissingColors, TreeSequenceVertexSet, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_univ,
    true_and, exists_exists_eq_and] at hB
  obtain ⟨a, ha⟩ := hB
  have hBlen : Bplus.length = T.length - 1 := by
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length +
      (HierarchyFullTailLength C - 1)) T.length = T.length - 1
    have hA := (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).positive
    have hEll : HierarchyFullTailLength C = T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length := by rfl
    rw [hEll]
    omega
  let earlierVertexIndex : Fin (T.length + 1) :=
    ⟨a.val, by have ha' := a.isLt; omega⟩
  have haMissing : alpha ∈ MissingColors G phi
      (T.vertex earlierVertexIndex) := by
    convert ha using 1
    apply congrArg (fun v => MissingColors G phi v)
    apply congrArg T.vertex
    apply Fin.ext
    rfl
  have hbefore : earlierVertexIndex.val < penultimateVertexIndex.val := by
    have hlt : earlierVertexIndex.val < T.length := by
      dsimp [earlierVertexIndex]
      have ha' := a.isLt
      omega
    have hne : earlierVertexIndex ≠ penultimateVertexIndex := by
      intro he
      apply hpen
      simpa [he] using haMissing
    have hle : earlierVertexIndex.val ≤ penultimateVertexIndex.val := by
      dsimp [penultimateVertexIndex]
      omega
    omega
  let D : HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx :=
    ⟨hcommon, alpha, (by simpa [hidxTerm] using halphaFinal),
      earlierVertexIndex, (by simpa using hbefore), haMissing⟩
  obtain ⟨P, hP⟩ := HierarchySituationTwoCaseThreeNormalization
    G k e0 input T phi ett base C ctx D
  obtain ⟨N⟩ := hP
  by_cases hmissing : N.theta ∈ MissingColors G P.coloring
      (T.vertex N.penultimateVertexIndex)
  · exact HierarchySituationTwoSubcaseThreeTwo
      G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext
      ⟨N, hmissing⟩
  · exact HierarchySituationTwoSubcaseThreeOne
      G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext
      ⟨N, hmissing⟩

theorem HierarchySituationTwoImpossible {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation :
      HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C) :
    False := by
  classical
  have htail : 2 ≤ T.length -
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length := by
    exact HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hApos : 1 ≤ (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length := by
    exact (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).positive
  have hTtwo : 2 ≤ T.length := by omega
  let lastEdgeIndex : Fin T.length := ⟨T.length - 1, by omega⟩
  let penultimateVertexIndex : Fin (T.length + 1) :=
    ⟨T.length - 1, by omega⟩
  let terminalVertexIndex : Fin (T.length + 1) := Fin.last T.length
  have hlastPos : lastEdgeIndex.val + 1 = T.length := by
    dsimp [lastEdgeIndex]
    omega
  have hpenPos : penultimateVertexIndex.val + 1 = T.length := by
    dsimp [penultimateVertexIndex]
    omega
  have htermPos : terminalVertexIndex.val = T.length := by
    simp [terminalVertexIndex]
  have hlastNeFirst : lastEdgeIndex ≠ (⟨0, T.positive⟩ : Fin T.length) := by
    intro h
    have : lastEdgeIndex.val = 0 := congrArg Fin.val h
    simp [lastEdgeIndex] at this
    omega
  have hedgeNe : T.edge lastEdgeIndex ≠ e0 := by
    intro he
    apply hlastNeFirst
    apply T.edge_injective
    simpa [T.first_edge] using he
  obtain ⟨theta, htheta⟩ := ctx.oneEdgeUncolored.2 _ hedgeNe
  let hcommon : HierarchySituationTwoCommonTailData
      G k e0 input T phi ett base C ctx := by
    refine ⟨htail, hsituation, lastEdgeIndex, penultimateVertexIndex,
      terminalVertexIndex, hlastPos, hpenPos, htermPos, ?_, theta, htheta⟩
    · exact @helper_branch_109 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hsituation htail hTtwo hlastPos hpenPos htermPos
  obtain ⟨alpha, halphaTree, halphaTerm⟩ :=
    HierarchyCounterexampleTerminalCommonMissing G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have halphaFinal : alpha ∈ MissingColors G phi
      (T.vertex terminalVertexIndex) := by
    simpa [terminalVertexIndex] using halphaTerm
  have hidxPen : hcommon.penultimateVertexIndex = penultimateVertexIndex := by rfl
  have hidxTerm : hcommon.terminalVertexIndex = terminalVertexIndex := by rfl
  by_cases hpen : alpha ∈ MissingColors G phi
      (T.vertex penultimateVertexIndex)
  · exact @helper_branch_204 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation htail hTtwo hlastPos hpenPos htermPos theta htheta
      alpha halphaFinal hidxPen hidxTerm hpen
  · exact @helper_branch_252 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation htail hTtwo hlastPos hpenPos htermPos hlastNeFirst
      theta htheta alpha halphaTree halphaFinal hidxPen hidxTerm hpen
end GoldbergSeymour

end
