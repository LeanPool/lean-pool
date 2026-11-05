/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.OrderedTreeUnion

public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors

public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath

/-!
# Parallel Two Constituent Path Contradiction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ParallelTwoConstituentPathContradiction_missing_leaf_163.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k :
    ℕ) (e0 : E) (sigma : PartialEdgeColoring E k) (right : TreeSequence G e0),
    IsProperEdgeColoring G sigma → ColoredVertexSetClosed G sigma (TreeSequenceVertexSet
    right) → ∀ (alpha beta : Fin k), let H := TwoColorIncidenceGraph G sigma alpha beta; ∀ (x
    : V), alpha ∈ MissingColors G sigma x ∨ beta ∈ MissingColors G sigma x → (H.neighborSet
    (Sum.inl x)).Subsingleton := by
  classical
  intro V E _ _ G k e0 sigma right hproper _ alpha beta H x hmissing z hz w hw
  cases hzv : z with
  | inl y =>
      rw [hzv] at hz
      simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hz
  | inr e =>
      cases hwv : w with
      | inl y =>
          rw [hwv] at hw
          simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hw
      | inr f =>
          rw [hzv] at hz
          rw [hwv] at hw
          have he : Incident G x e ∧
              (sigma e = some alpha ∨ sigma e = some beta) := by
            simpa [H, SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] using hz
          have hf : Incident G x f ∧
              (sigma f = some alpha ∨ sigma f = some beta) := by
            simpa [H, SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] using hw
          apply congrArg Sum.inr
          by_contra hef
          rcases hmissing with ha | hb
          · have hna : alpha ∉ PresentColors G sigma x := by
              simpa [MissingColors] using ha
            have heBeta : sigma e = some beta := he.2.resolve_left (by
              intro heAlpha
              apply hna
              simpa [PresentColors] using
                (show ∃ q, Incident G x q ∧ sigma q = some alpha from
                  ⟨e, he.1, heAlpha⟩))
            have hfBeta : sigma f = some beta := hf.2.resolve_left (by
              intro hfAlpha
              apply hna
              simpa [PresentColors] using
                (show ∃ q, Incident G x q ∧ sigma q = some alpha from
                  ⟨f, hf.1, hfAlpha⟩))
            exact (hproper hef ⟨x, he.1, hf.1⟩ heBeta) hfBeta
          · have hnb : beta ∉ PresentColors G sigma x := by
              simpa [MissingColors] using hb
            have heAlpha : sigma e = some alpha := he.2.resolve_right (by
              intro heBeta
              apply hnb
              simpa [PresentColors] using
                (show ∃ q, Incident G x q ∧ sigma q = some beta from
                  ⟨e, he.1, heBeta⟩))
            have hfAlpha : sigma f = some alpha := hf.2.resolve_right (by
              intro hfBeta
              apply hnb
              simpa [PresentColors] using
                (show ∃ q, Incident G x q ∧ sigma q = some beta from
                  ⟨f, hf.1, hfBeta⟩))
            exact (hproper hef ⟨x, he.1, hf.1⟩ heAlpha) hfAlpha

private theorem ParallelTwoConstituentPathContradiction_continuation_235.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k :
    ℕ) (e0 : E) (sigma : PartialEdgeColoring E k) (left right : TreeSequence G e0),
    IsProperEdgeColoring G sigma → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
    left) → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet right) →
    ColoredVertexSetClosed G sigma (TreeSequenceVertexSet right) → ∀ (support common : V),
    common ∈ TreeSequenceVertexSet left → common ∈ TreeSequenceVertexSet right → ∀ (alpha :
    Fin k) (u v : V), u ∈ TreeSequenceVertexSet left → v ∈ TreeSequenceVertexSet right → u ≠ v
    → alpha ∈ MissingColors G sigma u → alpha ∈ MissingColors G sigma v → u ≠ common → v ≠
    common → v ≠ support → ∀ beta ∈ MissingColors G sigma common, alpha ≠ beta →
    TreeInterchangeable G left sigma alpha beta → TreeInterchangeable G right sigma alpha beta
    → let H := TwoColorIncidenceGraph G sigma alpha beta; (∀ (x : V), alpha ∈ MissingColors G
    sigma x ∨ beta ∈ MissingColors G sigma x → (H.neighborSet (Sum.inl x)).Subsingleton) →
    False := by
  classical
  intro V E _ _ G k e0 sigma left right hproper hleftElementary hrightElementary _ support common
      hcommonLeft hcommonRight alpha u v huLeft hvRight huv halphaU halphaV huCommon hvCommon
      hvSupport beta hbetaCommon halphaBeta hleft hright H missing_leaf
  have hbetaPresentU : beta ∈ PresentColors G sigma u := by
    by_contra hnotPresent
    have hmissing : beta ∈ MissingColors G sigma u := by
      simpa [MissingColors] using hnotPresent
    exact (Finset.disjoint_left.mp
      (hleftElementary huLeft hcommonLeft huCommon)) hmissing hbetaCommon
  have hbetaPresentV : beta ∈ PresentColors G sigma v := by
    by_contra hnotPresent
    have hmissing : beta ∈ MissingColors G sigma v := by
      simpa [MissingColors] using hnotPresent
    exact (Finset.disjoint_left.mp
      (hrightElementary hvRight hcommonRight hvCommon)) hmissing hbetaCommon
  have halphaPresentCommon : alpha ∈ PresentColors G sigma common := by
    by_contra hnotPresent
    have hmissing : alpha ∈ MissingColors G sigma common := by
      simpa [MissingColors] using hnotPresent
    exact (Finset.disjoint_left.mp
      (hleftElementary huLeft hcommonLeft huCommon)) halphaU hmissing
  have present_neighbor (x : V)
      (hpresent : alpha ∈ PresentColors G sigma x ∨
        beta ∈ PresentColors G sigma x) :
      (H.neighborSet (Sum.inl x)).Nonempty := by
    rcases hpresent with hpresent | hpresent
    · obtain ⟨e, he, hcolor⟩ := by simpa [PresentColors] using hpresent
      refine ⟨Sum.inr e, ?_⟩
      simpa [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] using
        (show Incident G x e ∧
          (sigma e = some alpha ∨ sigma e = some beta) from
            ⟨he, Or.inl hcolor⟩)
    · obtain ⟨e, he, hcolor⟩ := by simpa [PresentColors] using hpresent
      refine ⟨Sum.inr e, ?_⟩
      simpa [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] using
        (show Incident G x e ∧
          (sigma e = some alpha ∨ sigma e = some beta) from
            ⟨he, Or.inr hcolor⟩)
  have huLeaf := missing_leaf u (Or.inl halphaU)
  have hvLeaf := missing_leaf v (Or.inl halphaV)
  have hcommonLeaf := missing_leaf common (Or.inr hbetaCommon)
  have huDegreeOne : (H.neighborSet (Sum.inl u)).Nonempty ∧
      Set.Subsingleton (H.neighborSet (Sum.inl u)) :=
    ⟨present_neighbor u (Or.inr hbetaPresentU), huLeaf⟩
  have hvDegreeOne : (H.neighborSet (Sum.inl v)).Nonempty ∧
      Set.Subsingleton (H.neighborSet (Sum.inl v)) :=
    ⟨present_neighbor v (Or.inr hbetaPresentV), hvLeaf⟩
  have hcommonDegreeOne : (H.neighborSet (Sum.inl common)).Nonempty ∧
      Set.Subsingleton (H.neighborSet (Sum.inl common)) :=
    ⟨present_neighbor common (Or.inl halphaPresentCommon), hcommonLeaf⟩
  have self_mem (x : V) : Sum.inl x ∈
      TwoColorComponent G sigma alpha beta (Sum.inl x) :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have huPath : TwoColorPathComponent G sigma alpha beta (Sum.inl u) :=
    ⟨halphaBeta, Sum.inl u, self_mem u, huDegreeOne.2⟩
  have hvPath : TwoColorPathComponent G sigma alpha beta (Sum.inl v) :=
    ⟨halphaBeta, Sum.inl v, self_mem v, hvDegreeOne.2⟩
  have hcommonPath : TwoColorPathComponent G sigma alpha beta
      (Sum.inl common) :=
    ⟨halphaBeta, Sum.inl common, self_mem common, hcommonDegreeOne.2⟩
  have hcompUCommon := hleft (Sum.inl u) (Sum.inl common)
    huPath hcommonPath ⟨u, huLeft, self_mem u⟩
      ⟨common, hcommonLeft, self_mem common⟩
  have hcompVCommon := hright (Sum.inl v) (Sum.inl common)
    hvPath hcommonPath ⟨v, hvRight, self_mem v⟩
      ⟨common, hcommonRight, self_mem common⟩
  obtain ⟨a, b, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G sigma alpha beta hproper (Sum.inl common)
  have huComponent : Sum.inl u ∈
      TwoColorComponent G sigma alpha beta (Sum.inl common) := by
    rw [← hcompUCommon]
    exact self_mem u
  have hvComponent : Sum.inl v ∈
      TwoColorComponent G sigma alpha beta (Sum.inl common) := by
    rw [← hcompVCommon]
    exact self_mem v
  have huSupport : Sum.inl u ∈ p.support := by
    change Sum.inl u ∈ {x | x ∈ p.support}
    rw [hsupport]
    exact huComponent
  have hvSupport : Sum.inl v ∈ p.support := by
    change Sum.inl v ∈ {x | x ∈ p.support}
    rw [hsupport]
    exact hvComponent
  have hcommonSupport : Sum.inl common ∈ p.support := by
    change Sum.inl common ∈ {x | x ∈ p.support}
    rw [hsupport]
    exact self_mem common
  have huEnd : Sum.inl u = a ∨ Sum.inl u = b := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 huDegreeOne.2) huSupport
  have hvEnd : Sum.inl v = a ∨ Sum.inl v = b := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hvDegreeOne.2) hvSupport
  have hcommonEnd : Sum.inl common = a ∨ Sum.inl common = b := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hcommonDegreeOne.2) hcommonSupport
  have huv' : (Sum.inl u : Sum V E) ≠ Sum.inl v := by simpa using huv
  have huCommon' : (Sum.inl u : Sum V E) ≠ Sum.inl common := by
    simpa using huCommon
  have hvCommon' : (Sum.inl v : Sum V E) ≠ Sum.inl common := by
    simpa using hvCommon
  rcases huEnd with hua | hub <;> rcases hvEnd with hva | hvb <;>
    rcases hcommonEnd with hca | hcb <;> aesop

theorem ParallelTwoConstituentPathContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (sigma : PartialEdgeColoring E k)
    (left right union : TreeSequence G e0)
    (hunion : Nonempty (OrderedTreeUnion left right union))
    (hproper : IsProperEdgeColoring G sigma)
    (hleftElementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet left))
    (hrightElementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet right))
    (_ : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet right))
    (support common : V) (gamma delta : Fin k)
    (hsupportLeft : support ∈ TreeSequenceVertexSet left)
    (hsupportRight : support ∈ TreeSequenceVertexSet right)
    (hcommonLeft : common ∈ TreeSequenceVertexSet left)
    (hcommonRight : common ∈ TreeSequenceVertexSet right)
    (hcommonNe : common ≠ support)
    (hdelta : delta ∈ MissingColors G sigma support)
    (hgamma : gamma ∉ TreeMissingColors sigma left)
    (hcommonMissing : (MissingColors G sigma common).Nonempty)
    (hleftInterchangeable : ∀ alpha beta : Fin k,
      alpha ∈ TreeMissingColors sigma left →
      beta ∈ TreeMissingColors sigma left →
      alpha ≠ gamma → alpha ≠ delta →
      beta ≠ gamma → beta ≠ delta →
      TreeInterchangeable G left sigma alpha beta)
    (hrightInterchangeable : ∀ alpha beta : Fin k,
      (alpha ∈ TreeMissingColors sigma right ∨
        beta ∈ TreeMissingColors sigma right) →
      TreeInterchangeable G right sigma alpha beta) :
    ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet union) := by
  classical
  by_contra hnotElementary
  unfold ColoredVertexSetElementary at hnotElementary
  have hbad : ∃ u, u ∈ TreeSequenceVertexSet union ∧
      ∃ v, v ∈ TreeSequenceVertexSet union ∧ u ≠ v ∧
        ¬ Disjoint (MissingColors G sigma u) (MissingColors G sigma v) := by
    by_contra hnone
    apply hnotElementary
    intro u hu v hv huv
    by_contra hdisjoint
    exact hnone ⟨u, hu, v, hv, huv, hdisjoint⟩
  obtain ⟨u0, hu0, v0, hv0, huv0, hdisjoint⟩ := hbad
  rw [Finset.disjoint_left] at hdisjoint
  push Not at hdisjoint
  obtain ⟨alpha, halphaU0, halphaV0⟩ := hdisjoint
  obtain ⟨hordered⟩ := hunion
  rw [hordered.vertexSet] at hu0 hv0
  obtain ⟨u, v, huLeft, huNotRight, hvRight, hvNotLeft, huv,
      halphaU, halphaV⟩ :
      ∃ u v : V,
        u ∈ TreeSequenceVertexSet left ∧
        u ∉ TreeSequenceVertexSet right ∧
        v ∈ TreeSequenceVertexSet right ∧
        v ∉ TreeSequenceVertexSet left ∧
        u ≠ v ∧ alpha ∈ MissingColors G sigma u ∧
        alpha ∈ MissingColors G sigma v := by
    rcases Finset.mem_union.mp hu0 with huLeft | huRight <;>
      rcases Finset.mem_union.mp hv0 with hvLeft | hvRight
    · exact False.elim
        ((Finset.disjoint_left.mp
          (hleftElementary huLeft hvLeft huv0)) halphaU0 halphaV0)
    · refine ⟨u0, v0, huLeft, ?_, hvRight, ?_, huv0,
        halphaU0, halphaV0⟩
      · intro huRight
        exact (Finset.disjoint_left.mp
          (hrightElementary huRight hvRight huv0)) halphaU0 halphaV0
      · intro hvLeft
        exact (Finset.disjoint_left.mp
          (hleftElementary huLeft hvLeft huv0)) halphaU0 halphaV0
    · refine ⟨v0, u0, hvLeft, ?_, huRight, ?_, huv0.symm,
        halphaV0, halphaU0⟩
      · intro hvRight
        exact (Finset.disjoint_left.mp
          (hrightElementary hvRight huRight huv0.symm)) halphaV0 halphaU0
      · intro huLeft
        exact (Finset.disjoint_left.mp
          (hleftElementary huLeft hvLeft huv0)) halphaU0 halphaV0
    · exact False.elim
        ((Finset.disjoint_left.mp
          (hrightElementary huRight hvRight huv0)) halphaU0 halphaV0)
  have huCommon : u ≠ common := by
    intro h
    exact huNotRight (h ▸ hcommonRight)
  have hvCommon : v ≠ common := by
    intro h
    exact hvNotLeft (h ▸ hcommonLeft)
  have hvSupport : v ≠ support := by
    intro h
    exact hvNotLeft (h ▸ hsupportLeft)
  obtain ⟨beta, hbetaCommon⟩ := hcommonMissing
  have halphaLeft : alpha ∈ TreeMissingColors sigma left := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨u, huLeft, halphaU⟩
  have hbetaLeft : beta ∈ TreeMissingColors sigma left := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨common, hcommonLeft, hbetaCommon⟩
  have halphaRight : alpha ∈ TreeMissingColors sigma right := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨v, hvRight, halphaV⟩
  have halphaGamma : alpha ≠ gamma := by
    intro h
    apply hgamma
    exact h ▸ halphaLeft
  have hbetaGamma : beta ≠ gamma := by
    intro h
    apply hgamma
    exact h ▸ hbetaLeft
  have halphaDelta : alpha ≠ delta := by
    intro h
    exact (Finset.disjoint_left.mp
      (hrightElementary hvRight hsupportRight hvSupport)) halphaV
        (h ▸ hdelta)
  have hbetaDelta : beta ≠ delta := by
    intro h
    exact (Finset.disjoint_left.mp
      (hrightElementary hcommonRight hsupportRight hcommonNe)) hbetaCommon
        (h ▸ hdelta)
  have halphaBeta : alpha ≠ beta := by
    intro h
    exact (Finset.disjoint_left.mp
      (hleftElementary huLeft hcommonLeft huCommon)) halphaU
        (h ▸ hbetaCommon)
  have hleft := hleftInterchangeable alpha beta halphaLeft hbetaLeft
    halphaGamma halphaDelta hbetaGamma hbetaDelta
  have hright := hrightInterchangeable alpha beta (Or.inl halphaRight)
  let H := TwoColorIncidenceGraph G sigma alpha beta
  have missing_leaf (x : V)
      (hmissing : alpha ∈ MissingColors G sigma x ∨
        beta ∈ MissingColors G sigma x) :
      Set.Subsingleton (H.neighborSet (Sum.inl x)) := by
    exact @ParallelTwoConstituentPathContradiction_missing_leaf_163 V E inferInstance
        inferInstance G k e0 sigma right hproper (by assumption) alpha beta x hmissing
  exact @ParallelTwoConstituentPathContradiction_continuation_235 V E inferInstance inferInstance
        G k e0 sigma left right hproper hleftElementary
      hrightElementary (by assumption) support common hcommonLeft hcommonRight alpha u v huLeft
      hvRight huv halphaU halphaV huCommon hvCommon hvSupport beta hbetaCommon halphaBeta hleft
      hright missing_leaf
end GoldbergSeymour

end
