/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPathExists
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumUnused
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.ScheideReplacementPairFixed
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementBoundaryConfiguration
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Scheide Symmetric Replacement Free Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation495Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let r : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex r (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex r (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let ends0 : Finset V := (G.ends e0).toFinset; (↑r : ℕ) < C.s → (1 : ℕ) ≤ C.s → (2 : ℕ) ≤ C.p →
        T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s → R.replacementTree.length = T.length → X.card =
        C.p + (2 : ℕ) * C.s → Z.card = C.p + (2 : ℕ) * C.s - (2 : ℕ) → Z ⊆ Xd → ends0 ⊆ Z → ends0
        ⊆ Xd → ends0.card = (2 : ℕ) → (
    ∀ v ∈ ends0, Incident G v e0) → GlobalMaximumTriple G k e0 phiD R.replacementTree →
        ColoredVertexSetClosed G phiD Xd → (
    ∀ v ∈ TreeSequenceVertexSet R.replacementTree, (Incident G v e0 → (MissingColors G phiD
        v).card = k - Degree G v + (1 : ℕ) ∧ (2 : ℕ) ≤ (MissingColors G phiD v).card) ∧ (¬Incident
        G v e0 → (MissingColors G phiD v).card = k - Degree G v ∧ (1 : ℕ) ≤ (MissingColors G phiD
        v).card)) → ((↑Z : Set V).PairwiseDisjoint fun (v : V) => MissingColors G phiD v) → (
    ∀ v ∈ Z, (MissingColors G phiD v).Nonempty) →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∃ (beta : Fin k) (v : V) (z : V) (p : (TwoColorIncidenceGraph G phiD gamma beta).Walk (Sum.inl
        v) (Sum.inl z)), v ∈ TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2
        : ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∧ beta ∈ MissingColors G phiD v ∧
        beta ∈ MissingColors G phi v ∧ beta ∈ TreeFreeColors phiD R.replacementTree ∧ beta ≠ (↑d :
        Fin k) ∧ beta ≠ gamma ∧ ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p

private theorem helper_hendsAvoidU_129.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex r (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex r (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let ends0 : Finset V := (G.ends e0).toFinset;
    ∀ (hr : (↑r : ℕ) < C.s), (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s), R.replacementTree.length = T.length →
    let m : ℕ := C.p + (2 : ℕ) * (↑r : ℕ); T.vertex (⟨m,
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = u0 → T.vertex (⟨m + (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = u1 → X.card = C.p + (2 : ℕ) * C.s →
    ∀ v ∈ ends0, v ∉ U := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X r u0 u1 U ends0 hr hp hlength hreplacementLength m hm0
      hm1 hXcard v hv hU
  have hv' : v ∈ G.ends e0 := Sym2.mem_toFinset.mp hv
  rw [← T.first_edge] at hv'
  obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
  rw [hi, Sym2.mem_iff] at hv'
  simp only [U, Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hv' with hv' | hv' <;> rcases hU with hu | hu <;> subst v
  · have heq : T.vertex ⟨1, by omega⟩ = T.vertex ⟨m, by omega⟩ := by
      simpa using hu.trans hm0.symm
    have hi' := T.vertex_injective heq
    have := congrArg Fin.val hi'
    simp at this
    omega
  · have heq : T.vertex ⟨1, by omega⟩ = T.vertex ⟨m + 1, by omega⟩ := by
      simpa using hu.trans hm1.symm
    have hi' := T.vertex_injective heq
    have := congrArg Fin.val hi'
    simp at this
    omega
  · have hi_lt : i.val < 1 := by simp
    have hii : i.val = 0 := by omega
    have heq : T.vertex (Fin.castLT i (Nat.lt_trans i.isLt
        (Nat.succ_lt_succ (show (0 : Nat) < T.length by omega)))) =
        T.vertex ⟨m, by omega⟩ := by
      simpa using hu.trans hm0.symm
    have hi' := T.vertex_injective heq
    have := congrArg Fin.val hi'
    simp [] at this
    dsimp [m] at this
    omega
  · have hi_lt : i.val < 1 := by simp
    have hii : i.val = 0 := by omega
    have heq : T.vertex (Fin.castLT i (Nat.lt_trans i.isLt
        (Nat.succ_lt_succ (show (0 : Nat) < T.length by omega)))) =
        T.vertex ⟨m + 1, by omega⟩ := by
      simpa using hu.trans hm1.symm
    have hi' := T.vertex_injective heq
    have := congrArg Fin.val hi'
    simp [] at this

private theorem helper_hmissing_227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (_ : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex r (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex r (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let ends0 : Finset V := (G.ends e0).toFinset; Z.card = C.p + (2 : ℕ) * C.s - (2 : ℕ) →
    ∀ (hendsSubZ : ends0 ⊆ Z), ends0.card = (2 : ℕ) → ((↑Z : Set V).PairwiseDisjoint fun (v : V)
        => MissingColors G phiD v) →
    ∀ (hnonempty :
    ∀ v ∈ Z, (MissingColors G phiD v).Nonempty),
    let firstColor : (v : V) → v ∈ Z → Fin k := fun (v : V) (hv : v ∈ Z) => Classical.choose
        (hnonempty v hv); (
    ∀ (v : V) (hv : v ∈ Z), firstColor v hv ∈ MissingColors G phiD v) →
    ∀ (hsecond :
    ∀ (v : V) (hv : v ∈ ends0), ((MissingColors G phiD v).erase (firstColor v (hendsSubZ
        hv))).Nonempty),
    let extraColor : (v : V) → v ∈ ends0 → Fin k := fun (v : V) (hv : v ∈ ends0) =>
        Classical.choose (hsecond v hv); (
    ∀ (v : V) (hv : v ∈ ends0), extraColor v hv ∈ (MissingColors G phiD v).erase (firstColor v
        (hendsSubZ hv))) →
    let M : Finset (Fin k) := Z.biUnion fun (v : V) => MissingColors G phiD v; Z.card + (2 : ℕ) ≤
        M.card := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X r u0 u1 U Z ends0 hZcard hendsSubZ
      hendsCard hdisj hnonempty firstColor firstMem hsecond extraColor extraMem M
  let domain := Sum {v : V // v ∈ Z} {v : V // v ∈ ends0}
  let color : domain → Fin k := fun q => match q with
    | Sum.inl v => firstColor v.1 v.2
    | Sum.inr v => extraColor v.1 v.2
  have hmap : ∀ q : domain, color q ∈ M := by
    intro q
    rcases q with q | q
    · apply Finset.mem_biUnion.mpr
      exact ⟨q.1, q.2, firstMem q.1 q.2⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨q.1, hendsSubZ q.2,
        Finset.mem_erase.mp (extraMem q.1 q.2) |>.2⟩
  have hinj : Function.Injective color := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj a.2 b.2 hn
        have hc : firstColor a.1 a.2 = firstColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd) (firstMem a.1 a.2)
          (by simpa only [hc] using firstMem b.1 b.2)
      cases Subtype.ext huv
      rfl
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj a.2 (hendsSubZ b.2) hn
        have hc : firstColor a.1 a.2 = extraColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd) (firstMem a.1 a.2)
          (by simpa only [hc] using Finset.mem_erase.mp (extraMem b.1 b.2) |>.2)
      have he := Finset.mem_erase.mp (extraMem b.1 b.2)
      exact False.elim (he.1 (by simpa [color, huv] using hab.symm))
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj (hendsSubZ a.2) b.2 hn
        have hc : extraColor a.1 a.2 = firstColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd)
          (Finset.mem_erase.mp (extraMem a.1 a.2) |>.2)
          (by simpa only [hc] using firstMem b.1 b.2)
      have he := Finset.mem_erase.mp (extraMem a.1 a.2)
      exact False.elim (he.1 (by simpa [color, huv] using hab))
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj (hendsSubZ a.2) (hendsSubZ b.2) hn
        have hc : extraColor a.1 a.2 = extraColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd)
          (Finset.mem_erase.mp (extraMem a.1 a.2) |>.2)
          (by simpa only [hc] using Finset.mem_erase.mp (extraMem b.1 b.2) |>.2)
      cases Subtype.ext huv
      rfl
  let A : Finset domain :=
    Z.attach.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      ends0.attach.map ⟨Sum.inr, Sum.inr_injective⟩
  have hAdisj : Disjoint
      (Z.attach.map ⟨Sum.inl, Sum.inl_injective⟩)
      (ends0.attach.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rw [Finset.mem_map] at hq1 hq2
    rcases hq1 with ⟨a, ha, rfl⟩
    rcases hq2 with ⟨b, hb, h⟩
    cases h
  have hAcard : A.card = Z.card + 2 := by
    dsimp [A]
    rw [Finset.card_union_of_disjoint hAdisj]
    simp [hendsCard]
  have hle : A.card ≤ M.card := by
    apply Finset.card_le_card_of_injOn color
    · intro q hq
      exact hmap q
    · exact hinj.injOn
  omega

private theorem helper_husedSub_369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    ∀ (hr : (↑r : ℕ) < C.s), (1 : ℕ) ≤ C.s →
    ∀ (hp : (2 : ℕ) ≤ C.p) (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s)
        (hreplacementLength : R.replacementTree.length = T.length) (hXcard : X.card = C.p + (2 :
        ℕ) * C.s) (htreeD : TashkinovTree G e0 phiD R.replacementTree),
    let baseIndex : Fin (C.p - (2 : ℕ)) → Fin R.replacementTree.length := fun (q : Fin (C.p - (2 :
        ℕ))) => (⟨(↑q : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin R.replacementTree.length);
    ∀ (hbaseIndexPos :
    ∀ (q : Fin (C.p - (2 : ℕ))), (1 : ℕ) ≤ (↑(baseIndex q) : ℕ)),
    let baseColor : Fin (C.p - (2 : ℕ)) → Fin k := fun (q : Fin (C.p - (2 : ℕ))) =>
        Classical.choose (Exists.choose_spec (htreeD (baseIndex q) (hbaseIndexPos q))); (
    ∀ (q : Fin (C.p - (2 : ℕ))), phiD (R.replacementTree.edge (baseIndex q)) = some (baseColor q))
        →
    let baseColors : Finset (Fin k) := Finset.image baseColor Finset.univ;
    let allBlockColors : Finset (Fin k) := Finset.image C.gamma Finset.univ;
    let retainedBlockColors : Finset (Fin k) := allBlockColors.erase gamma; allBlockColors.card =
        C.s → (
    ∀ (q : ℕ) (hq : q < T.length), (1 : ℕ) ≤ q → phiD (T.edge (⟨q, hq⟩ : Fin T.length)) = phi
        (T.edge (⟨q, hq⟩ : Fin T.length))) → phiD R.f1 = some (↑d : Fin k) → phiD R.f2 = some (↑d
        : Fin k) → TreeUsedColors phiD R.replacementTree ⊆ baseColors ∪ (retainedBlockColors ∪
        {(↑d : Fin k)}) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X r hr hs hp hlength hreplacementLength
      hXcard htreeD baseIndex hbaseIndexPos baseColor hbaseColorSpec baseColors allBlockColors
      retainedBlockColors hallBlockCard originalEdgeFixed hf1D hf2D c hc
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases hc with ⟨j, hj, hc⟩
  by_cases hjBase : j.val < C.p - 1
  · apply Finset.mem_union_left
    let q : Fin (C.p - 2) := ⟨j.val - 1, by omega⟩
    have hqj : baseIndex q = j := by
      apply Fin.ext
      simp [baseIndex, q]
      omega
    have hcol : baseColor q = c := by
      apply Option.some.inj
      exact (hbaseColorSpec q).symm.trans (by simpa [hqj] using hc)
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hcol⟩
  · apply Finset.mem_union_right
    by_cases hbefore : j.val < C.p - 1 + 2 * r.val
    · apply Finset.mem_union_left
      let n := j.val - (C.p - 1)
      let q : Fin C.s := ⟨n / 2, by omega⟩
      let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
      have hjpos : j.val = C.p - 1 + 2 * q.val + t.val := by
        dsimp [q, t, n]
        have hdiv := Nat.mod_add_div (j.val - (C.p - 1)) 2
        omega
      have hqr : q ≠ r := by
        intro h
        have hval := congrArg Fin.val h
        dsimp [q, n] at hval
        omega
      have hedgeOld : T.edge ⟨j.val, by omega⟩ = C.blockEdge q t := by
        calc
          T.edge ⟨j.val, by omega⟩ =
              T.edge ⟨C.p - 1 + 2 * q.val + t.val, by omega⟩ := by
            congr 1
            exact Fin.ext hjpos
          _ = C.blockEdge q t := C.block_edge_position q t
      have hedgeRep : R.replacementTree.edge j = T.edge ⟨j.val, by omega⟩ := by
        exact R.retained_edges_before j.val hbefore (by omega)
      have hcolorD : phiD (R.replacementTree.edge j) = some (C.gamma q) := by
        rw [hedgeRep, originalEdgeFixed j.val (by omega) (by omega), hedgeOld]
        exact C.block_color q t
      have hcol : C.gamma q = c :=
        Option.some.inj (hcolorD.symm.trans hc)
      have hneGamma : C.gamma q ≠ gamma := by
        intro h
        apply hqr
        apply C.gamma_injective
        simpa [gamma, r] using h
      have hcGamma : c ≠ gamma := fun h => hneGamma (hcol.trans h)
      exact Finset.mem_erase.mpr ⟨hcGamma,
        Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hcol⟩⟩
    · by_cases hafter : j.val + 2 < T.length
      · apply Finset.mem_union_left
        let n := j.val + 2 - (C.p - 1)
        let q : Fin C.s := ⟨n / 2, by omega⟩
        let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
        have hjpos : j.val + 2 = C.p - 1 + 2 * q.val + t.val := by
          dsimp [q, t, n]
          have hdiv := Nat.mod_add_div (j.val + 2 - (C.p - 1)) 2
          omega
        have hqr : q ≠ r := by
          intro h
          have hval := congrArg Fin.val h
          dsimp [q, n] at hval
          omega
        have hedgeOld : T.edge ⟨j.val + 2, hafter⟩ = C.blockEdge q t := by
          calc
            T.edge ⟨j.val + 2, hafter⟩ =
                T.edge ⟨C.p - 1 + 2 * q.val + t.val, by omega⟩ := by
              congr 1
              exact Fin.ext hjpos
            _ = C.blockEdge q t := C.block_edge_position q t
        have hedgeRep : R.replacementTree.edge j =
            T.edge ⟨j.val + 2, hafter⟩ := by
          exact R.retained_edges_after j.val (by omega) hafter
        have hcolorD : phiD (R.replacementTree.edge j) = some (C.gamma q) := by
          rw [hedgeRep, originalEdgeFixed (j.val + 2) hafter (by omega), hedgeOld]
          exact C.block_color q t
        have hcol : C.gamma q = c :=
          Option.some.inj (hcolorD.symm.trans hc)
        have hneGamma : C.gamma q ≠ gamma := by
          intro h
          apply hqr
          apply C.gamma_injective
          simpa [gamma, r] using h
        have hcGamma : c ≠ gamma := fun h => hneGamma (hcol.trans h)
        exact Finset.mem_erase.mpr ⟨hcGamma,
          Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hcol⟩⟩
      · apply Finset.mem_union_right
        have hjlast : j.val = T.length - 2 ∨ j.val = T.length - 1 := by
          omega
        rcases hjlast with hjlast | hjlast
        · have hedge : R.replacementTree.edge j = R.f1 := by
            calc
              R.replacementTree.edge j =
                  R.replacementTree.edge ⟨T.length - 2, by
                    rw [hreplacementLength]
                    omega⟩ := by
                congr 1
                exact Fin.ext hjlast
              _ = R.f1 := R.replacement_last_edges.1
          have hdc : d.1 = c := Option.some.inj ((hedge ▸ hf1D).symm.trans hc)
          simp [hdc]
        · have hedge : R.replacementTree.edge j = R.f2 := by
            calc
              R.replacementTree.edge j =
                  R.replacementTree.edge ⟨T.length - 1, by
                    rw [hreplacementLength]
                    omega⟩ := by
                congr 1
                exact Fin.ext hjlast
              _ = R.f2 := R.replacement_last_edges.2
          have hdc : d.1 = c := Option.some.inj ((hedge ▸ hf2D).symm.trans hc)
          simp [hdc]

private theorem helper_originalEdgeFixed_487.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    ∀ (hr : (↑r : ℕ) < C.s) (hp : (2 : ℕ) ≤ C.p) (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) *
        C.s) (hreplacementLength : R.replacementTree.length = T.length) (hXcard : X.card = C.p +
        (2 : ℕ) * C.s), TashkinovTree G e0 phiD R.replacementTree →
    let baseIndex : Fin (C.p - (2 : ℕ)) → Fin R.replacementTree.length := fun (q : Fin (C.p - (2 :
        ℕ))) => (⟨(↑q : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin R.replacementTree.length); (
    ∀ (q : Fin (C.p - (2 : ℕ))), (1 : ℕ) ≤ (↑(baseIndex q) : ℕ)) → (↑d : Fin k) ∉ TreeUsedColors
        phi T → (IsProperEdgeColoring G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) e0 ∧ TwoColorComponentSwap G
        phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) (D.f0 d) = some (C.gamma
        (D.gammaIndex d)) ∧ MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (D.v0 d) = insert (↑d : Fin k) ((MissingColors G phi
        (D.v0 d)).erase (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → ¬f = D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, ¬v = D.v0 d → MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) ∧
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) →
    ∀ (q : ℕ) (hq : q < T.length), (1 : ℕ) ≤ q → phiD (T.edge (⟨q, hq⟩ : Fin T.length)) = phi
        (T.edge (⟨q, hq⟩ : Fin T.length)) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X r hr hp hlength hreplacementLength hXcard
      htreeD baseIndex hbaseIndexPos hdeltaUnusedOriginal heffect q hq hqpos
  apply heffect.2.2.2.2.1
  · obtain ⟨i, hi⟩ := T.attaches ⟨q, hq⟩
    refine ⟨T.vertex ⟨q + 1, by omega⟩, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · change T.vertex ⟨q + 1, by omega⟩ ∈ G.ends (T.edge ⟨q, hq⟩)
      rw [hi]
      simp
  · intro heq
    apply hdeltaUnusedOriginal
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨q, hq⟩, hqpos, by simpa [heq] using D.f0_color d⟩

private theorem helper_hused_518.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    ∀ (hr : (↑r : ℕ) < C.s), (1 : ℕ) ≤ C.s →
    ∀ (hp : (2 : ℕ) ≤ C.p) (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s)
        (hreplacementLength : R.replacementTree.length = T.length) (hXcard : X.card = C.p + (2 :
        ℕ) * C.s) (htreeD : TashkinovTree G e0 phiD R.replacementTree),
    let baseIndex : Fin (C.p - (2 : ℕ)) → Fin R.replacementTree.length := fun (q : Fin (C.p - (2 :
        ℕ))) => (⟨(↑q : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin R.replacementTree.length);
    ∀ (hbaseIndexPos :
    ∀ (q : Fin (C.p - (2 : ℕ))), (1 : ℕ) ≤ (↑(baseIndex q) : ℕ)),
    let baseColor : Fin (C.p - (2 : ℕ)) → Fin k := fun (q : Fin (C.p - (2 : ℕ))) =>
        Classical.choose (Exists.choose_spec (htreeD (baseIndex q) (hbaseIndexPos q)));
    let baseColors : Finset (Fin k) := Finset.image baseColor Finset.univ;
    let allBlockColors : Finset (Fin k) := Finset.image C.gamma Finset.univ;
    let retainedBlockColors : Finset (Fin k) := allBlockColors.erase gamma; baseColors.card ≤ C.p
        - (2 : ℕ) → allBlockColors.card = C.s → retainedBlockColors.card = C.s - (1 : ℕ) →
        TreeUsedColors phiD R.replacementTree ⊆ baseColors ∪ (retainedBlockColors ∪
        {(↑d : Fin k)}) → (TreeUsedColors phiD R.replacementTree).card ≤ C.p - (2 : ℕ) + C.s := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X r hr hs hp hlength hreplacementLength
      hXcard htreeD baseIndex hbaseIndexPos baseColor baseColors allBlockColors
      retainedBlockColors hbaseCard hallBlockCard hretainedBlockCard husedSub
  refine (Finset.card_le_card husedSub).trans ?_
  calc
    (baseColors ∪ (retainedBlockColors ∪ {d.1})).card ≤
        baseColors.card + (retainedBlockColors ∪ {d.1}).card :=
      Finset.card_union_le _ _
    _ ≤ baseColors.card + (retainedBlockColors.card + ({d.1} : Finset (Fin k)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ (C.p - 2) + ((C.s - 1) + 1) := by
      rw [hretainedBlockCard]
      simp only [Finset.card_singleton]
      omega
    _ = C.p - 2 + C.s := by omega

private theorem helper_hdeltaUsed_546.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    ∀ (hr : (↑r : ℕ) < C.s), (1 : ℕ) ≤ C.s →
    ∀ (hp : (2 : ℕ) ≤ C.p) (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s)
        (hreplacementLength : R.replacementTree.length = T.length) (hXcard : X.card = C.p + (2 :
        ℕ) * C.s), TashkinovTree G e0 phiD R.replacementTree →
    let baseIndex : Fin (C.p - (2 : ℕ)) → Fin R.replacementTree.length := fun (q : Fin (C.p - (2 :
        ℕ))) => (⟨(↑q : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin R.replacementTree.length); (
    ∀ (q : Fin (C.p - (2 : ℕ))), (1 : ℕ) ≤ (↑(baseIndex q) : ℕ)) →
    let allBlockColors : Finset (Fin k) := Finset.image C.gamma Finset.univ; allBlockColors.card =
        C.s → phiD R.f2 = some (↑d : Fin k) → (↑d : Fin k) ∈ TreeUsedColors phiD R.replacementTree
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X r hr hs hp hlength hreplacementLength
      hXcard htreeD baseIndex hbaseIndexPos allBlockColors hallBlockCard hf2D
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
  let j : Fin R.replacementTree.length := ⟨T.length - 1, by
    rw [hreplacementLength]
    omega⟩
  refine ⟨j, by simp [j]; omega, ?_⟩
  have hedge : R.replacementTree.edge j = R.f2 := by
    calc
      R.replacementTree.edge j =
          R.replacementTree.edge ⟨T.length - 1, by
            rw [hreplacementLength]
            omega⟩ := by
        congr 1
      _ = R.f2 := R.replacement_last_edges.2
  simpa [hedge] using hf2D

private theorem helper_continuation_495.{u_1, u_2} :
    helperContinuation495Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X Xd r u0 u1 U Z ends0 hr hs hp hlength
      hreplacementLength hXcard hZcard hZsubXd hendsSubZ hendsSubXd hendsCard hendsInc hglobalD
      hclosedD hcounts hdisj hnonempty
  let firstColor : (v : V) → v ∈ Z → Fin k := fun v hv =>
    Classical.choose (hnonempty v hv)
  have firstMem : ∀ (v : V) (hv : v ∈ Z),
      firstColor v hv ∈ MissingColors G phiD v := by
    intro v hv
    exact Classical.choose_spec (hnonempty v hv)
  have hsecond : ∀ (v : V) (hv : v ∈ ends0),
      ((MissingColors G phiD v).erase (firstColor v (hendsSubZ hv))).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (firstMem v (hendsSubZ hv))]
    have hh := (hcounts v (hendsSubXd hv)).1 (hendsInc v hv) |>.2
    omega
  let extraColor : (v : V) → v ∈ ends0 → Fin k := fun v hv =>
    Classical.choose (hsecond v hv)
  have extraMem : ∀ (v : V) (hv : v ∈ ends0),
      extraColor v hv ∈
        (MissingColors G phiD v).erase (firstColor v (hendsSubZ hv)) := by
    intro v hv
    exact Classical.choose_spec (hsecond v hv)
  let M := Z.biUnion fun v => MissingColors G phiD v
  have hmissing : Z.card + 2 ≤ M.card := by
    exact @helper_hmissing_227 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R hZcard hendsSubZ hendsCard hdisj hnonempty firstMem hsecond extraMem
  have hmissingBound : C.p + 2 * C.s ≤ M.card := by
    omega
  have htreeD : TashkinovTree G e0 phiD R.replacementTree := hglobalD.2.1
  let baseIndex : Fin (C.p - 2) → Fin R.replacementTree.length :=
    fun q => ⟨q.val + 1, by omega⟩
  have hbaseIndexPos : ∀ q : Fin (C.p - 2), 1 ≤ (baseIndex q).val := by
    intro q
    simp [baseIndex]
  let baseColor : Fin (C.p - 2) → Fin k := fun q =>
    Classical.choose (htreeD (baseIndex q) (hbaseIndexPos q) |>.choose_spec)
  have hbaseColorSpec : ∀ q : Fin (C.p - 2),
      phiD (R.replacementTree.edge (baseIndex q)) = some (baseColor q) := by
    intro q
    exact (Classical.choose_spec
      (htreeD (baseIndex q) (hbaseIndexPos q) |>.choose_spec)).1
  let baseColors := (Finset.univ : Finset (Fin (C.p - 2))).image baseColor
  let allBlockColors := (Finset.univ : Finset (Fin C.s)).image C.gamma
  let retainedBlockColors := allBlockColors.erase gamma
  have hbaseCard : baseColors.card ≤ C.p - 2 := by
    exact Finset.card_image_le.trans_eq (by simp)
  have hallBlockCard : allBlockColors.card = C.s := by
    dsimp [allBlockColors]
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb hab
      exact C.gamma_injective hab)]
    simp
  have hgammaAll : gamma ∈ allBlockColors := by
    apply Finset.mem_image.mpr
    exact ⟨r, Finset.mem_univ r, by simp [gamma, r]⟩
  have hretainedBlockCard : retainedBlockColors.card = C.s - 1 := by
    dsimp [retainedBlockColors]
    rw [Finset.card_erase_of_mem hgammaAll, hallBlockCard]
  have hglobal : GlobalMaximumTriple G k e0 phi T := C.globally_maximum
  have hdeltaUnusedOriginal : d.1 ∉ TreeUsedColors phi T := by
    have hu := (ScheideGlobalMaximumUnused G k e0 phi T hglobal).1
    exact fun hd => (Finset.disjoint_left.mp hu) d.2 hd
  have heffect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp [phiD, gamma] at heffect
  have originalEdgeFixed : ∀ (q : ℕ) (hq : q < T.length), 1 ≤ q →
      phiD (T.edge ⟨q, hq⟩) = phi (T.edge ⟨q, hq⟩) := by
    exact @helper_originalEdgeFixed_487 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 phi T C D d R hr hp hlength hreplacementLength hXcard htreeD
        hbaseIndexPos hdeltaUnusedOriginal heffect
  have hf1D : phiD R.f1 = some d.1 := by
    have hf := ScheideReplacementPairFixed G k e0 phi T C D d R R.f1
      (Or.inl (by
        change R.u1 ∈ G.ends R.f1
        rw [R.f1_ends]
        simp []))
    simpa [phiD, gamma] using hf.trans R.f1_color
  have hf2D : phiD R.f2 = some d.1 := by
    have hf := ScheideReplacementPairFixed G k e0 phi T C D d R R.f2
      (Or.inr (by
        change R.u2 ∈ G.ends R.f2
        rw [R.f2_ends]
        simp []))
    simpa [phiD, gamma] using hf.trans R.f2_color
  have husedSub : TreeUsedColors phiD R.replacementTree ⊆
      baseColors ∪ (retainedBlockColors ∪ {d.1}) := by
    exact @helper_husedSub_369 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R hr hs hp hlength hreplacementLength hXcard htreeD hbaseIndexPos
        hbaseColorSpec hallBlockCard originalEdgeFixed hf1D hf2D
  have hused : (TreeUsedColors phiD R.replacementTree).card ≤ C.p - 2 + C.s := by
    exact @helper_hused_518 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R hr hs hp hlength hreplacementLength hXcard htreeD hbaseIndexPos hbaseCard
        hallBlockCard hretainedBlockCard husedSub
  have hstrict : (TreeUsedColors phiD R.replacementTree).card < M.card := by
    omega
  have hnsub : ¬ M ⊆ TreeUsedColors phiD R.replacementTree := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnsub
  obtain ⟨beta, hbetaM, hbetaUnused⟩ := hnsub
  obtain ⟨v, hvZ, hbetaMissing⟩ := Finset.mem_biUnion.mp hbetaM
  have hvX : v ∈ X := (Finset.mem_sdiff.mp hvZ).1
  have hvXd : v ∈ Xd := hZsubXd hvZ
  have hbetaTreeMissing : beta ∈ TreeMissingColors phiD R.replacementTree := by
    exact Finset.mem_biUnion.mpr ⟨v, hvXd, hbetaMissing⟩
  have hbetaFree : beta ∈ TreeFreeColors phiD R.replacementTree := by
    exact Finset.mem_sdiff.mpr ⟨hbetaTreeMissing, hbetaUnused⟩
  have hdeltaUsed : d.1 ∈ TreeUsedColors phiD R.replacementTree := by
    exact @helper_hdeltaUsed_546 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d R hr hs hp hlength hreplacementLength hXcard htreeD hbaseIndexPos
        hallBlockCard hf2D
  have hbetaDelta : beta ≠ d.1 := by
    intro h
    exact hbetaUnused (h ▸ hdeltaUsed)
  have hboundary :=
    ScheideSymmetricReplacementBoundaryConfiguration G k e0 phi T C D d R
  dsimp [gamma, phiD] at hboundary
  have hgammaDef : gamma ∈ DefectiveColors G phiD Xd := by
    simpa [gamma, phiD, Xd] using hboundary.1
  have hgammaCard : 2 ≤ (BoundaryColorEdges G phiD Xd gamma).card := by
    change gamma ∈ Finset.univ.filter
      (fun alpha => DefectiveColor G phiD Xd alpha) at hgammaDef
    exact (Finset.mem_filter.mp hgammaDef).2
  obtain ⟨fgamma, hfgamma⟩ := Finset.card_pos.mp (by omega :
    0 < (BoundaryColorEdges G phiD Xd gamma).card)
  have hfgammaBoundary : fgamma ∈ BoundaryEdges G Xd :=
    (Finset.mem_filter.mp hfgamma).1
  have hfgammaColor : phiD fgamma = some gamma :=
    (Finset.mem_filter.mp hfgamma).2
  have hgammaNotMissing : gamma ∉ MissingColors G phiD v :=
    hclosedD hfgammaBoundary hvXd hfgammaColor
  have hbetaGamma : beta ≠ gamma := by
    intro h
    exact hgammaNotMissing (h ▸ hbetaMissing)
  have hbetaOldMissing : beta ∈ MissingColors G phi v := by
    by_cases hv0 : v = D.v0 d
    · subst v
      have hb := hbetaMissing
      rw [heffect.2.2.2.1] at hb
      simp only [Finset.mem_insert, Finset.mem_erase] at hb
      rcases hb with hb | hb
      · exact False.elim (hbetaDelta hb)
      · exact hb.2
    · rw [heffect.2.2.2.2.2.1 v hvX hv0] at hbetaMissing
      exact hbetaMissing
  obtain ⟨z, path, hpath⟩ := ScheideDefectiveChainPathExists
    G k e0 phiD R.replacementTree hglobalD gamma beta hgammaDef
      hbetaFree v hvXd hbetaMissing
  refine ⟨beta, v, z, path, ?_, hbetaMissing, hbetaOldMissing,
    hbetaFree, hbetaDelta, hbetaGamma, hpath⟩
  simpa [Z, X, U, u0, u1, r] using hvZ

theorem ScheideSymmetricReplacementFreePath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    ∃ (beta : Fin k) (v z : V) (p :
      (TwoColorIncidenceGraph G phiD gamma beta).Walk (Sum.inl v) (Sum.inl z)),
    v ∈
        TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} ∧
      beta ∈ MissingColors G phiD v ∧
        beta ∈ MissingColors G phi v ∧
          beta ∈ TreeFreeColors phiD R.replacementTree ∧
            beta ≠ d.1 ∧
              beta ≠ gamma ∧
                ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p := by
  classical
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let X := TreeSequenceVertexSet T
  let Xd := TreeSequenceVertexSet R.replacementTree
  let r := D.gammaIndex d
  let u0 := C.blockVertex r 0
  let u1 := C.blockVertex r 1
  let U : Finset V := {u0, u1}
  let Z := X \ U
  let ends0 := (G.ends e0).toFinset
  have hr : r.val < C.s := r.isLt
  have hs : 1 <= C.s := by omega
  have hp : 2 <= C.p := C.p_ge_two
  have hlength : T.length + 1 = C.p + 2 * C.s := C.length_eq
  have hreplacementLength : R.replacementTree.length = T.length :=
    R.replacement_length
  let m := C.p + 2 * r.val
  have hm0 : T.vertex ⟨m, by omega⟩ = u0 := by
    simpa [m, u0, r] using C.block_vertex_position r (0 : Fin 2)
  have hm1 : T.vertex ⟨m + 1, by omega⟩ = u1 := by
    simpa [m, u1, r] using C.block_vertex_position r (1 : Fin 2)
  have hu0X : u0 ∈ X := by
    rw [← hm0]
    simp [X, TreeSequenceVertexSet]
  have hu1X : u1 ∈ X := by
    rw [← hm1]
    simp [X, TreeSequenceVertexSet]
  have hu01 : u0 ≠ u1 := by
    intro h
    have hv : T.vertex ⟨m, by omega⟩ = T.vertex ⟨m + 1, by omega⟩ :=
      hm0.trans (h.trans hm1.symm)
    have hi := T.vertex_injective hv
    have hiv := congrArg Fin.val hi
    simp at hiv
  have hUsub : U ⊆ X := by
    intro v hv
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hu0X
    · exact hu1X
  have hUcard : U.card = 2 := by
    simp [U, hu01]
  have hXcard : X.card = C.p + 2 * C.s := by
    have himage : X.card = T.length + 1 := by
      simp [X, TreeSequenceVertexSet, Finset.card_image_of_injective,
        T.vertex_injective]
    omega
  have hZcard : Z.card = C.p + 2 * C.s - 2 := by
    dsimp [Z]
    rw [Finset.card_sdiff_of_subset hUsub, hXcard, hUcard]
  have hZsubXd : Z ⊆ Xd := by
    intro v hv
    have hv' : v ∈ X \ U := by simpa [Z, X, U] using hv
    change v ∈ TreeSequenceVertexSet R.replacementTree
    rw [R.replacement_vertices]
    exact Finset.mem_union_left _ hv'
  have hendsSubX : ends0 ⊆ X := by
    intro v hv
    have hv' : v ∈ G.ends e0 := Sym2.mem_toFinset.mp hv
    rw [← T.first_edge] at hv'
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    rw [hi, Sym2.mem_iff] at hv'
    rcases hv' with hv | hv <;> subst v <;>
      simp [X, TreeSequenceVertexSet]
  have hendsAvoidU : ∀ v ∈ ends0, v ∉ U := by
    exact @helper_hendsAvoidU_129 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d R hr hp hlength hreplacementLength hm0 hm1 hXcard
  have hendsSubZ : ends0 ⊆ Z := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hendsSubX hv, hendsAvoidU v hv⟩
  have hendsSubXd : ends0 ⊆ Xd := fun _ hv => hZsubXd (hendsSubZ hv)
  have hendsCard : ends0.card = 2 := by
    have hn : ¬ (G.ends e0).IsDiag := by
      intro hd
      induction he : G.ends e0 using Sym2.inductionOn with
      | _ a b =>
        rw [he] at hd
        rw [Sym2.mk_isDiag_iff] at hd
        apply G.loopless e0 a
        rw [he, hd]
    exact Sym2.card_toFinset_of_not_isDiag _ hn
  have hendsInc : ∀ v ∈ ends0, Incident G v e0 := by
    intro v hv
    exact Sym2.mem_toFinset.mp hv
  have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d R
  dsimp [phiD, gamma] at hmaximum
  have hglobalD : GlobalMaximumTriple G k e0 phiD R.replacementTree :=
    hmaximum.2.2
  have horderD := ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hglobalD
  have helemD : ColoredVertexSetElementary G phiD Xd := horderD.2.2.2.1
  have hclosedD : ColoredVertexSetClosed G phiD Xd := horderD.2.2.2.2
  have hcounts := ScheideGlobalMaximumMissingCounts
    G k e0 phiD R.replacementTree hglobalD
  have hdisj : (Z : Set V).PairwiseDisjoint (fun v => MissingColors G phiD v) := by
    intro a ha b hb hab
    exact helemD (hZsubXd ha) (hZsubXd hb) hab
  have hnonempty : ∀ v ∈ Z, (MissingColors G phiD v).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    by_cases hi : Incident G v e0
    · have hh := (hcounts v (hZsubXd hv)).1 hi |>.2
      omega
    · have hh := (hcounts v (hZsubXd hv)).2 hi |>.2
      omega
  exact @helper_continuation_495 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hr hs hp hlength hreplacementLength hXcard hZcard hZsubXd hendsSubZ
      hendsSubXd hendsCard hendsInc hglobalD hclosedD hcounts hdisj hnonempty
end GoldbergSeymour

end
