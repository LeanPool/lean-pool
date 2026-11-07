/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DisjointFamilyCardinality

public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPathExists
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.TreeFreeColors

/-!
# Scheide Symmetric Original Free Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hendsAvoidU_108.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let this : DecidableEq V := Classical.decEq V;
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex r (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex r (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let ends0 : Finset V := (G.ends e0).toFinset;
    ∀ (hr : (↑r : ℕ) < C.s), (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s),
    let m : ℕ := C.p + (2 : ℕ) * (↑r : ℕ); T.vertex (⟨m, Decidable.byContradiction fun (a : ¬m <
        T.length + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = u0 → T.vertex (⟨m + (1 : ℕ), Decidable.byContradiction fun (a
        : ¬m + (1 : ℕ) < T.length + (1 : ℕ)) =>
    by
                omega
    ⟩ : Fin (T.length + (1 : ℕ))) = u1 → X.card = C.p + (2 : ℕ) * C.s →
    ∀ v ∈ ends0, v ∉ U := by
  classical
  intro V E _ _ _ G k e0 phi T C D d this X r u0 u1 U ends0 hr hp hlength m hm0 hm1 hXcard v hv hU
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

private theorem helper_husedSub_301.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let r : Fin C.s := D.gammaIndex d;
    ∀ (hr : (↑r : ℕ) < C.s) (hp : (2 : ℕ) ≤ C.p) (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) *
        C.s) (hXcard : X.card = C.p + (2 : ℕ) * C.s) (htree : TashkinovTree G e0 phi T),
    let baseIndex : Fin (C.p - (2 : ℕ)) → Fin T.length := fun (q : Fin (C.p - (2 : ℕ))) => (⟨(↑q :
        ℕ) + (1 : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    ∀ (hbaseIndexPos :
    ∀ (q : Fin (C.p - (2 : ℕ))), (1 : ℕ) ≤ (↑(baseIndex q) : ℕ)),
    let baseColor : Fin (C.p - (2 : ℕ)) → Fin k := fun (q : Fin (C.p - (2 : ℕ))) =>
        Classical.choose (Exists.choose_spec (htree (baseIndex q) (hbaseIndexPos q))); (
    ∀ (q : Fin (C.p - (2 : ℕ))), phi (T.edge (baseIndex q)) = some (baseColor q)) →
    let baseColors : Finset (Fin k) := Finset.image baseColor Finset.univ;
    let blockColors : Finset (Fin k) := Finset.image C.gamma Finset.univ; blockColors.card = C.s →
        TreeUsedColors phi T ⊆ baseColors ∪ blockColors := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X r hr hp hlength hXcard htree baseIndex hbaseIndexPos
      baseColor hbaseColorSpec baseColors blockColors hblockCard c hc
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
    let n := j.val - (C.p - 1)
    have hn : n < 2 * C.s := by
      dsimp [n]
      omega
    let q : Fin C.s := ⟨n / 2, by omega⟩
    let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
    have hjpos : j.val = C.p - 1 + 2 * q.val + t.val := by
      dsimp [q, t, n]
      have hdiv := Nat.mod_add_div (j.val - (C.p - 1)) 2
      omega
    have hedge : T.edge j = C.blockEdge q t := by
      have hpos := C.block_edge_position q t
      rw [← hpos]
      congr 1
      exact Fin.ext hjpos
    have hcol : C.gamma q = c := by
      apply Option.some.inj
      exact (C.block_color q t).symm.trans (by simpa [hedge] using hc)
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hcol⟩

theorem ScheideSymmetricOriginalFreePath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (_ : ScheideReplacementData G k e0 phi T C D d) :
    ∃ (beta : Fin k) (v z : V) (p :
      (TwoColorIncidenceGraph G phi d.1 beta).Walk (Sum.inl v) (Sum.inl z)),
    v ∈
        TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} ∧
      beta ∈ MissingColors G phi v ∧
        beta ∈ TreeFreeColors phi T ∧
          beta ≠ C.gamma (D.gammaIndex d) ∧ ScheideDefectiveChainPath T phi d.1 beta v z p := by
  classical
  let := Classical.decEq V
  let X := TreeSequenceVertexSet T
  let r := D.gammaIndex d
  let u0 := C.blockVertex r 0
  let u1 := C.blockVertex r 1
  let U : Finset V := {u0, u1}
  let Z := X \ U
  let ends0 := (G.ends e0).toFinset
  have hr : r.val < C.s := r.isLt
  have hs : 1 ≤ C.s := by omega
  have hp : 2 ≤ C.p := C.p_ge_two
  have hlength : T.length + 1 = C.p + 2 * C.s := C.length_eq
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
      dsimp [X, TreeSequenceVertexSet]
      rw [Finset.card_image_iff.mpr (by
        intro a ha b hb hab
        exact T.vertex_injective hab)]
      simp
    omega
  have hZcard : Z.card = C.p + 2 * C.s - 2 := by
    dsimp [Z]
    rw [Finset.card_sdiff_of_subset hUsub, hXcard, hUcard]
  have hendsSubX : ends0 ⊆ X := by
    intro v hv
    have hv' : v ∈ G.ends e0 := Sym2.mem_toFinset.mp hv
    rw [← T.first_edge] at hv'
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    rw [hi, Sym2.mem_iff] at hv'
    rcases hv' with hv | hv <;> subst v <;>
      simp [X, TreeSequenceVertexSet]
  have hendsAvoidU : ∀ v ∈ ends0, v ∉ U := by
    exact @helper_hendsAvoidU_108 V E inferInstance inferInstance inferInstance G k e0 phi T C D
        d hr hp hlength hm0 hm1 hXcard
  have hendsSubZ : ends0 ⊆ Z := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hendsSubX hv, hendsAvoidU v hv⟩
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
  have hglobal : GlobalMaximumTriple G k e0 phi T := C.globally_maximum
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have helem : ColoredVertexSetElementary G phi X := horder.2.2.2.1
  have hcounts := ScheideGlobalMaximumMissingCounts G k e0 phi T hglobal
  have hdisj : (Z : Set V).PairwiseDisjoint (fun v => MissingColors G phi v) := by
    intro a ha b hb hab
    exact helem (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab
  have hnonempty : ∀ v ∈ Z, (MissingColors G phi v).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    have hvX := (Finset.mem_sdiff.mp hv).1
    by_cases hi : Incident G v e0
    · have hh := (hcounts v hvX).1 hi |>.2
      omega
    · have hh := (hcounts v hvX).2 hi |>.2
      omega
  let firstColor : (v : V) → v ∈ Z → Fin k := fun v hv =>
    Classical.choose (hnonempty v hv)
  have firstMem : ∀ (v : V) (hv : v ∈ Z),
      firstColor v hv ∈ MissingColors G phi v := by
    intro v hv
    exact Classical.choose_spec (hnonempty v hv)
  have hsecond : ∀ (v : V) (hv : v ∈ ends0),
      ((MissingColors G phi v).erase (firstColor v (hendsSubZ hv))).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (firstMem v (hendsSubZ hv))]
    have hh := (hcounts v (hendsSubX hv)).1 (hendsInc v hv) |>.2
    omega
  let extraColor : (v : V) → v ∈ ends0 → Fin k := fun v hv =>
    Classical.choose (hsecond v hv)
  have extraMem : ∀ (v : V) (hv : v ∈ ends0),
      extraColor v hv ∈
        (MissingColors G phi v).erase (firstColor v (hendsSubZ hv)) := by
    intro v hv
    exact Classical.choose_spec (hsecond v hv)
  let M := Z.biUnion fun v => MissingColors G phi v
  have hmissing : Z.card + 2 ≤ M.card := by
    simpa only [hendsCard] using
      Finset.card_biUnion_ge_card_add Z ends0 (fun v => MissingColors G phi v)
        hendsSubZ hdisj firstColor firstMem extraColor extraMem
  have hmissingBound : C.p + 2 * C.s ≤ M.card := by
    omega
  have htree : TashkinovTree G e0 phi T := hglobal.2.1
  let baseIndex : Fin (C.p - 2) → Fin T.length := fun q => ⟨q.val + 1, by omega⟩
  have hbaseIndexPos : ∀ q : Fin (C.p - 2), 1 ≤ (baseIndex q).val := by
    intro q
    simp [baseIndex]
  let baseColor : Fin (C.p - 2) → Fin k := fun q =>
    Classical.choose (htree (baseIndex q) (hbaseIndexPos q) |>.choose_spec)
  have hbaseColorSpec : ∀ q : Fin (C.p - 2),
      phi (T.edge (baseIndex q)) = some (baseColor q) := by
    intro q
    exact (Classical.choose_spec (htree (baseIndex q) (hbaseIndexPos q) |>.choose_spec)).1
  let baseColors := (Finset.univ : Finset (Fin (C.p - 2))).image baseColor
  let blockColors := (Finset.univ : Finset (Fin C.s)).image C.gamma
  have hbaseCard : baseColors.card ≤ C.p - 2 := by
    exact (Finset.card_image_le.trans_eq (by
      simp : (Finset.univ : Finset (Fin (C.p - 2))).card = C.p - 2))
  have hblockCard : blockColors.card = C.s := by
    dsimp [blockColors]
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb hab
      exact C.gamma_injective hab)]
    simp
  have husedSub : TreeUsedColors phi T ⊆ baseColors ∪ blockColors := by
    exact @helper_husedSub_301 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
        hr hp hlength hXcard htree hbaseIndexPos hbaseColorSpec hblockCard
  have hused : (TreeUsedColors phi T).card ≤ C.p - 2 + C.s := by
    refine (Finset.card_le_card husedSub).trans ?_
    calc
      (baseColors ∪ blockColors).card ≤ baseColors.card + blockColors.card :=
        Finset.card_union_le _ _
      _ ≤ (C.p - 2) + C.s := by omega
  have hstrict : (TreeUsedColors phi T).card < M.card := by
    omega
  have hnsub : ¬ M ⊆ TreeUsedColors phi T := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnsub
  obtain ⟨beta, hbetaM, hbetaUnused⟩ := hnsub
  obtain ⟨v, hvZ, hbetaMissing⟩ := Finset.mem_biUnion.mp hbetaM
  have hvX : v ∈ X := (Finset.mem_sdiff.mp hvZ).1
  have hbetaTreeMissing : beta ∈ TreeMissingColors phi T := by
    exact Finset.mem_biUnion.mpr ⟨v, hvX, hbetaMissing⟩
  have hbetaFree : beta ∈ TreeFreeColors phi T := by
    exact Finset.mem_sdiff.mpr ⟨hbetaTreeMissing, hbetaUnused⟩
  have hgammaUsed : C.gamma r ∈ TreeUsedColors phi T := by
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    let j : Fin T.length := ⟨C.p - 1 + 2 * r.val, by omega⟩
    refine ⟨j, by simp [j]; omega, ?_⟩
    rw [show T.edge j = C.blockEdge r (0 : Fin 2) by
      simpa [j] using C.block_edge_position r (0 : Fin 2)]
    exact C.block_color r 0
  have hbetaGamma : beta ≠ C.gamma r := by
    intro h
    exact hbetaUnused (h ▸ hgammaUsed)
  obtain ⟨z, path, hpath⟩ := ScheideDefectiveChainPathExists
    G k e0 phi T hglobal d.1 beta d.2 hbetaFree v hvX hbetaMissing
  refine ⟨beta, v, z, path, ?_, hbetaMissing, hbetaFree, ?_, hpath⟩
  · simpa [Z, X, U, u0, u1, r] using hvZ
  · simpa [r] using hbetaGamma

end GoldbergSeymour

end
