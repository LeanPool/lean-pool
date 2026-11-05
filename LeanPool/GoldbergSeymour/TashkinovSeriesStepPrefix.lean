/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesDataPrefix
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsPrefix

/-!
# Tashkinov Series Step Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch286Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (triple : KTriple G k
        e0 input) (seedLength : (data.tree (0 : Fin (rounds + (2 : ℕ)))).length = (1 : ℕ))
        (initialColoring : data.coloring (0 : Fin (rounds + (1 : ℕ))) = input) (initialStored :
        data.stored (0 : Fin (rounds + (1 : ℕ))) = ∅) (initialEdges : data.connectingEdges (0 :
        Fin (rounds + (1 : ℕ))) = ∅) (initialKind : data.kind (0 : Fin (rounds + (1 : ℕ))) = none)
        (initialVertex : data.chosenVertex (0 : Fin (rounds + (1 : ℕ))) = none) (initialOutside :
        data.outsideVertex (0 : Fin (rounds + (1 : ℕ))) = none) (initialDelta : data.delta (0 :
        Fin (rounds + (1 : ℕ))) = none) (initialGamma : data.gamma (0 : Fin (rounds + (1 : ℕ))) =
        none) (initialClosure : TashkinovClosure (data.coloring (0 : Fin (rounds + (1 : ℕ))))
        (data.tree (0 : Fin (rounds + (2 : ℕ)))) (data.tree (1 : Fin (rounds + (2 : ℕ))))) (hj :
        (↑(0 : Fin (rounds + (1 : ℕ))) : ℕ) ≤ m),
    ∃ (prefixCert : TashkinovSeriesStep G k m e0 input (TashkinovSeriesDataPrefix m hm data)
        (⟨(↑(0 : Fin (rounds + (1 : ℕ))) : ℕ),
    by omega
    ⟩ : Fin (m + (1 : ℕ)))), prefixCert ≍ TashkinovSeriesStep.initial triple seedLength
        initialColoring initialStored initialEdges initialKind initialVertex initialOutside
        initialDelta initialGamma initialClosure

private abbrev helperNoRevisiting362Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] {G : LooplessMultigraph V E}
        {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤
        rounds) (idx : Fin rounds), ¬Nonempty (RevisitingExtensionCertificate data idx.castSucc) →
    ∀ (_ : MaximumDefectiveChoice G e0 (data.tree idx.succ.castSucc) (TashkinovStoredColors data
        idx.castSucc) (data.coloring idx.castSucc)) (_ : Fin k), (↑idx : ℕ) + (1 : ℕ) ≤ m →
    ∀ (hidx : (↑idx : ℕ) < m),
    let idx' : Fin m := (⟨(↑idx : ℕ), hidx⟩ : Fin m); (TashkinovSeriesDataPrefix m hm
        data).coloring idx'.castSucc = data.coloring idx.castSucc → (TashkinovSeriesDataPrefix m
        hm data).tree idx'.succ.castSucc = data.tree idx.succ.castSucc →
        (TashkinovSeriesDataPrefix m hm data).tree idx'.castSucc.succ = data.tree
        idx.castSucc.succ → TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc = TashkinovStoredColors data idx.castSucc → ¬Nonempty
        (RevisitingExtensionCertificate (TashkinovSeriesDataPrefix m hm data) idx'.castSucc)

private noncomputable abbrev helperCycle365.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [Fintype V] →
  [Fintype E] →
  {G : LooplessMultigraph V E} →
  {k rounds : ℕ} →
  {e0 : E} →
  (data : TashkinovSeriesData G k rounds e0) →
  (m : ℕ) →
  (hm : m ≤ rounds) →
  (idx : Fin rounds) →
  (available : RevisitingExtensionCertificate data idx.castSucc) →
  (hidx : (↑idx : ℕ) < m) →
  let idx' : Fin m := (⟨(↑idx : ℕ), hidx⟩ : Fin m);
  (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
      data.coloring idx.castSucc →
  TwoColorCycle G
    ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
    available.gamma available.delta := by
  classical
  intro V E inst inst_1 G k rounds e0 data m hm idx available hidx idx' hprev
  exact {
    base := available.cycle.base,
    walk :=
      @Eq.ndrec (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 data
          (@Fin.castSucc rounds idx))
        (fun (phi : PartialEdgeColoring E k) ↦
          @SimpleGraph.Walk (Sum V E)
            (@TwoColorIncidenceGraph V E G k phi
              (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available)
              (@RevisitingExtensionCertificate.delta V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available))
            (@TwoColorCycle.base V E G k
              (@TashkinovSeriesData.coloring V E G k rounds e0 data
                (@Fin.castSucc rounds idx))
              (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available)
              (@RevisitingExtensionCertificate.delta V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available)
              (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available))
            (@TwoColorCycle.base V E G k
              (@TashkinovSeriesData.coloring V E G k rounds e0 data
                (@Fin.castSucc rounds idx))
              (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available)
              (@RevisitingExtensionCertificate.delta V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available)
              (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k rounds
                e0 data (@Fin.castSucc rounds idx) available)))
        (@TwoColorCycle.walk V E G k
          (@TashkinovSeriesData.coloring V E G k rounds e0 data
            (@Fin.castSucc rounds idx))
          (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k rounds e0
            data (@Fin.castSucc rounds idx) available)
          (@RevisitingExtensionCertificate.delta V E inst inst_1 G k rounds e0
            data (@Fin.castSucc rounds idx) available)
          (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k rounds e0
            data (@Fin.castSucc rounds idx) available))
        (@TashkinovSeriesData.coloring V E G k m e0
          (@TashkinovSeriesDataPrefix V E   G k rounds e0 m hm data)
          (@Fin.castSucc m idx'))
        (@Eq.symm (PartialEdgeColoring E k)
          (@TashkinovSeriesData.coloring V E G k m e0
            (@TashkinovSeriesDataPrefix V E   G k rounds e0 m hm data)
            (@Fin.castSucc m idx'))
          (@TashkinovSeriesData.coloring V E G k rounds e0 data
            (@Fin.castSucc rounds idx))
          hprev),
    isCycle :=
      id
        (Eq.casesOn (motive :=
          fun (a : PartialEdgeColoring E k)
            (t :
              (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
                a) ↦
          data.coloring idx.castSucc = a →
            hprev ≍ t →
              (@Eq.rec (PartialEdgeColoring E k)
                  (@TashkinovSeriesData.coloring V E G k rounds e0 data
                    (@Fin.castSucc rounds idx))
                  (fun (x : PartialEdgeColoring E k)
                      (x_1 :
                        @Eq (PartialEdgeColoring E k)
                          (@TashkinovSeriesData.coloring V E G k rounds e0 data
                            (@Fin.castSucc rounds idx))
                          x) ↦
                    @SimpleGraph.Walk (Sum V E)
                      (@TwoColorIncidenceGraph V E G k x
                        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx) available)
                        (@RevisitingExtensionCertificate.delta V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx)
                          available))
                      (@TwoColorCycle.base V E G k
                        (@TashkinovSeriesData.coloring V E G k rounds e0 data
                          (@Fin.castSucc rounds idx))
                        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx) available)
                        (@RevisitingExtensionCertificate.delta V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx) available)
                        (@RevisitingExtensionCertificate.cycle V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx)
                          available))
                      (@TwoColorCycle.base V E G k
                        (@TashkinovSeriesData.coloring V E G k rounds e0 data
                          (@Fin.castSucc rounds idx))
                        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx) available)
                        (@RevisitingExtensionCertificate.delta V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx) available)
                        (@RevisitingExtensionCertificate.cycle V E inst inst_1 G
                          k rounds e0 data (@Fin.castSucc rounds idx)
                          available)))
                  (@TwoColorCycle.walk V E G k
                    (@TashkinovSeriesData.coloring V E G k rounds e0 data
                      (@Fin.castSucc rounds idx))
                    (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available)
                    (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available)
                    (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available))
                  (@TashkinovSeriesData.coloring V E G k m e0
                    (@TashkinovSeriesDataPrefix V E   G k rounds e0 m
                      hm data)
                    (@Fin.castSucc m idx'))
                  (@Eq.symm (PartialEdgeColoring E k)
                    (@TashkinovSeriesData.coloring V E G k m e0
                      (@TashkinovSeriesDataPrefix V E   G k rounds e0
                        m hm data)
                      (@Fin.castSucc m idx'))
                    (@TashkinovSeriesData.coloring V E G k rounds e0 data
                      (@Fin.castSucc rounds idx))
                    hprev)).IsCycle)
          hprev
          (fun
              (h :
                data.coloring idx.castSucc =
                  (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
              (h_1 :
                hprev ≍
                  Eq.refl
                    ((TashkinovSeriesDataPrefix m hm data).coloring
                      idx'.castSucc)) ↦
            @Eq.ndrec
              (@Eq (PartialEdgeColoring E k)
                (@TashkinovSeriesData.coloring V E G k m e0
                  (@TashkinovSeriesDataPrefix V E   G k rounds e0 m hm
                    data)
                  (@Fin.castSucc m idx'))
                (@TashkinovSeriesData.coloring V E G k rounds e0 data
                  (@Fin.castSucc rounds idx)))
              (@Eq.refl (PartialEdgeColoring E k)
                (@TashkinovSeriesData.coloring V E G k m e0
                  (@TashkinovSeriesDataPrefix V E   G k rounds e0 m hm
                    data)
                  (@Fin.castSucc m idx')))
              (fun
                  (hprev :
                    @Eq (PartialEdgeColoring E k)
                      (@TashkinovSeriesData.coloring V E G k m e0
                        (@TashkinovSeriesDataPrefix V E   G k rounds
                          e0 m hm data)
                        (@Fin.castSucc m idx'))
                      (@TashkinovSeriesData.coloring V E G k rounds e0 data
                        (@Fin.castSucc rounds idx))) ↦
                @SimpleGraph.Walk.IsCycle (Sum V E)
                  (@TwoColorIncidenceGraph V E G k
                    (@TashkinovSeriesData.coloring V E G k m e0
                      (@TashkinovSeriesDataPrefix V E   G k rounds e0
                        m hm data)
                      (@Fin.castSucc m idx'))
                    (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available)
                    (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available))
                  (@TwoColorCycle.base V E G k
                    (@TashkinovSeriesData.coloring V E G k rounds e0 data
                      (@Fin.castSucc rounds idx))
                    (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available)
                    (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available)
                    (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k
                      rounds e0 data (@Fin.castSucc rounds idx) available))
                  (@Eq.rec (PartialEdgeColoring E k)
                    (@TashkinovSeriesData.coloring V E G k rounds e0 data
                      (@Fin.castSucc rounds idx))
                    (fun (x : PartialEdgeColoring E k)
                        (x_1 :
                          @Eq (PartialEdgeColoring E k)
                            (@TashkinovSeriesData.coloring V E G k rounds e0
                              data (@Fin.castSucc rounds idx))
                            x) ↦
                      @SimpleGraph.Walk (Sum V E)
                        (@TwoColorIncidenceGraph V E G k x
                          (@RevisitingExtensionCertificate.gamma V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available)
                          (@RevisitingExtensionCertificate.delta V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available))
                        (@TwoColorCycle.base V E G k
                          (@TashkinovSeriesData.coloring V E G k rounds e0 data
                            (@Fin.castSucc rounds idx))
                          (@RevisitingExtensionCertificate.gamma V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available)
                          (@RevisitingExtensionCertificate.delta V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available)
                          (@RevisitingExtensionCertificate.cycle V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available))
                        (@TwoColorCycle.base V E G k
                          (@TashkinovSeriesData.coloring V E G k rounds e0 data
                            (@Fin.castSucc rounds idx))
                          (@RevisitingExtensionCertificate.gamma V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available)
                          (@RevisitingExtensionCertificate.delta V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available)
                          (@RevisitingExtensionCertificate.cycle V E inst inst_1
                            G k rounds e0 data (@Fin.castSucc rounds idx)
                            available)))
                    (@TwoColorCycle.walk V E G k
                      (@TashkinovSeriesData.coloring V E G k rounds e0 data
                        (@Fin.castSucc rounds idx))
                      (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                        rounds e0 data (@Fin.castSucc rounds idx) available)
                      (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                        rounds e0 data (@Fin.castSucc rounds idx) available)
                      (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k
                        rounds e0 data (@Fin.castSucc rounds idx) available))
                    (@TashkinovSeriesData.coloring V E G k m e0
                      (@TashkinovSeriesDataPrefix V E   G k rounds e0
                        m hm data)
                      (@Fin.castSucc m idx'))
                    (@Eq.symm (PartialEdgeColoring E k)
                      (@TashkinovSeriesData.coloring V E G k m e0
                        (@TashkinovSeriesDataPrefix V E   G k rounds
                          e0 m hm data)
                        (@Fin.castSucc m idx'))
                      (@TashkinovSeriesData.coloring V E G k rounds e0 data
                        (@Fin.castSucc rounds idx))
                      hprev)))
              (@TwoColorCycle.isCycle V E G k
                (@TashkinovSeriesData.coloring V E G k rounds e0 data
                  (@Fin.castSucc rounds idx))
                (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                  rounds e0 data (@Fin.castSucc rounds idx) available)
                (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                  rounds e0 data (@Fin.castSucc rounds idx) available)
                (@RevisitingExtensionCertificate.cycle V E inst inst_1 G k
                  rounds e0 data (@Fin.castSucc rounds idx) available))
              hprev
              (@Eq.symm
                (@Eq (PartialEdgeColoring E k)
                  (@TashkinovSeriesData.coloring V E G k m e0
                    (@TashkinovSeriesDataPrefix V E   G k rounds e0 m
                      hm data)
                    (@Fin.castSucc m idx'))
                  (@TashkinovSeriesData.coloring V E G k rounds e0 data
                    (@Fin.castSucc rounds idx)))
                hprev
                (@Eq.refl (PartialEdgeColoring E k)
                  (@TashkinovSeriesData.coloring V E G k m e0
                    (@TashkinovSeriesDataPrefix V E   G k rounds e0 m
                      hm data)
                    (@Fin.castSucc m idx')))
                (@eq_of_heq
                  (@Eq (PartialEdgeColoring E k)
                    (@TashkinovSeriesData.coloring V E G k m e0
                      (@TashkinovSeriesDataPrefix V E   G k rounds e0
                        m hm data)
                      (@Fin.castSucc m idx'))
                    (@TashkinovSeriesData.coloring V E G k rounds e0 data
                      (@Fin.castSucc rounds idx)))
                  hprev
                  (@Eq.refl (PartialEdgeColoring E k)
                    (@TashkinovSeriesData.coloring V E G k m e0
                      (@TashkinovSeriesDataPrefix V E   G k rounds e0
                        m hm data)
                      (@Fin.castSucc m idx')))
                  h_1)))
          (Eq.refl (data.coloring idx.castSucc)) (HEq.refl hprev)) :
    TwoColorCycle G
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      available.gamma available.delta };

private noncomputable abbrev helperAvailable754.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [inst : Fintype V] →
  [inst_1 : Fintype E] →
  {G : LooplessMultigraph V E} →
  {k rounds : ℕ} →
  {e0 : E} →
  (data : TashkinovSeriesData G k rounds e0) →
  (m : ℕ) →
  (hm : m ≤ rounds) →
  (idx : Fin rounds) →
  (available : RevisitingExtensionCertificate data idx.castSucc) →
  (hidx : (↑idx : ℕ) < m) →
  let idx' : Fin m := (⟨(↑idx : ℕ), hidx⟩ : Fin m);
  (hprev :
      (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
        data.coloring idx.castSucc) →
  (TashkinovSeriesDataPrefix m hm data).tree idx'.castSucc.succ =
      data.tree idx.castSucc.succ →
  (haBound : (↑available.earlier : ℕ) < m + (1 : ℕ)) →
  let earlier' : Fin (m + (1 : ℕ)) :=
    (⟨(↑available.earlier : ℕ), haBound⟩ : Fin (m + (1 : ℕ)));
  (TashkinovSeriesDataPrefix m hm data).kind earlier' =
      data.kind available.earlier →
  (TashkinovSeriesDataPrefix m hm data).gamma earlier' =
      data.gamma available.earlier →
  (TashkinovSeriesDataPrefix m hm data).delta earlier' =
      data.delta available.earlier →
  (TashkinovSeriesDataPrefix m hm data).tree
        earlier'.castSucc =
      data.tree available.earlier.castSucc →
  let _ :
    TwoColorCycle G
      ((TashkinovSeriesDataPrefix m hm data).coloring
        idx'.castSucc)
      available.gamma available.delta := by
    exact
      @helperCycle365 (@V) (@E) inferInstance
        inferInstance (@G) (@k) (@rounds) (@e0) (@data)
        (@m) (@hm) (@idx) (@available) (@hidx) (@hprev)
  let _ :
    (TwoColorIncidenceGraph G
          ((TashkinovSeriesDataPrefix m hm
                data).coloring
            idx'.castSucc)
          available.gamma available.delta).Walk
      (Sum.inr available.edge)
      (Sum.inl available.returnVertex) :=
    @Eq.ndrec (PartialEdgeColoring E k)
      (@TashkinovSeriesData.coloring V E G k rounds e0
        data (@Fin.castSucc rounds idx))
      (fun (phi : PartialEdgeColoring E k) ↦
        @SimpleGraph.Walk (Sum V E)
          (@TwoColorIncidenceGraph V E G k phi
            (@RevisitingExtensionCertificate.gamma V E
              inst inst_1 G k rounds e0 data
              (@Fin.castSucc rounds idx) available)
            (@RevisitingExtensionCertificate.delta V E
              inst inst_1 G k rounds e0 data
              (@Fin.castSucc rounds idx) available))
          (@Sum.inr V E
            (@RevisitingExtensionCertificate.edge V E
              inst inst_1 G k rounds e0 data
              (@Fin.castSucc rounds idx) available))
          (@Sum.inl V E
            (@RevisitingExtensionCertificate.returnVertex
              V E inst inst_1 G k rounds e0 data
              (@Fin.castSucc rounds idx) available)))
      (@RevisitingExtensionCertificate.returnPath V E
        inst inst_1 G k rounds e0 data
        (@Fin.castSucc rounds idx) available)
      (@TashkinovSeriesData.coloring V E G k m e0
        (@TashkinovSeriesDataPrefix V E G k rounds e0 m
          hm data)
        (@Fin.castSucc m idx'))
      (@Eq.symm (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k m e0
          (@TashkinovSeriesDataPrefix V E G k rounds e0
            m hm data)
          (@Fin.castSucc m idx'))
        (@TashkinovSeriesData.coloring V E G k rounds e0
          data (@Fin.castSucc rounds idx))
        hprev);
  RevisitingExtensionCertificate
    (TashkinovSeriesDataPrefix m hm data)
    idx'.castSucc := by
  classical
  intro V E _ _ G k rounds e0 data m hm idx available hidx idx' hprev htreeCurrent haBound
      earlier' hkindEarlier hgammaEarlier hdeltaEarlier htreeEarlier cycle' returnPath'
  exact {
    earlier := earlier'
    earlierPositive := by
      simpa [earlier'] using available.earlierPositive
    earlierAtMost := by
      simpa [earlier', idx'] using available.earlierAtMost
    earlierPE := by
      simpa [hkindEarlier] using available.earlierPE
    interveningRevisiting := by
      intro j hjpos hjafter hjatMost
      let j' : Fin (rounds + 1) := Fin.castLE (by omega) j
      have hstep := available.interveningRevisiting j'
        (by simpa [j'] using hjpos)
        (by simpa [j', earlier'] using hjafter)
        (by simpa [j', idx'] using hjatMost)
      have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j =
          data.kind j' := by rfl
      simpa [hkindJ] using hstep
    gamma := available.gamma
    delta := available.delta
    earlierGamma := by
      simpa [hgammaEarlier] using available.earlierGamma
    earlierDelta := by
      simpa [hdeltaEarlier] using available.earlierDelta
    cycle := cycle'
    meetsEarlier := by
      rcases available.meetsEarlier with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [← htreeEarlier] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    leavesCurrent := by
      rcases available.leavesCurrent with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [← htreeCurrent] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    edge := available.edge
    edgeOnCycle := by
      dsimp [cycle']
      cases hprev
      exact available.edgeOnCycle
    edgeBoundary := by
      simpa only [htreeCurrent] using available.edgeBoundary
    insideEndpoint := available.insideEndpoint
    outsideEndpoint := available.outsideEndpoint
    insideInCurrent := by
      simpa only [htreeCurrent] using available.insideInCurrent
    outsideNotCurrent := by
      simpa only [htreeCurrent] using available.outsideNotCurrent
    edgeEnds := available.edgeEnds
    returnVertex := available.returnVertex
    returnInEarlier := by
      simpa only [htreeEarlier] using available.returnInEarlier
    returnPath := returnPath'
    returnPathIsPath := by
      dsimp [returnPath']
      cases hprev
      exact available.returnPathIsPath
    returnPathOnCycle := by
      dsimp [returnPath', cycle']
      cases hprev
      exact available.returnPathOnCycle
    returnPathInternal := by
      intro v hv
      have hv' : Sum.inl v ∈ available.returnPath.support := by
        dsimp [returnPath'] at hv
        cases hprev
        exact hv
      simpa only [htreeCurrent] using available.returnPathInternal v hv'
  }

private abbrev helperPrefixCert1166Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (_ : Fin (m + (1 :
        ℕ))) (idx : Fin rounds) (_ : IsProperEdgeColoring G (data.coloring idx.castSucc)) (_ :
        IsOneEdgeUncolored (data.coloring idx.castSucc) e0) (_ : ColoredVertexSetClosed G
        (data.coloring idx.castSucc) (TreeSequenceVertexSet (data.tree idx.succ.castSucc))) (_ :
        ¬ColoredVertexSetStronglyClosed G (data.coloring idx.castSucc) (TreeSequenceVertexSet
        (data.tree idx.succ.castSucc))) (choice : MaximumDefectiveChoice G e0 (data.tree
        idx.succ.castSucc) (TashkinovStoredColors data idx.castSucc) (data.coloring idx.castSucc))
        (_ :
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (data.tree idx.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data idx.castSucc) : Finset (Fin k)) choice.selected rho ∧ ¬Disjoint (MissingColors G rho
        choice.otherEndpoint) (TreeMissingColors rho (data.tree idx.succ.castSucc))) (gamma : Fin
        k) (secondStable : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G secondStable) (_ :
        IsOneEdgeUncolored secondStable e0) (_ : StableColoring (data.tree idx.succ.castSucc)
        (insert choice.color (TashkinovStoredColors data idx.castSucc) : Finset (Fin k))
        choice.selected secondStable) (_ : TreeExit (data.tree idx.succ.castSucc) secondStable
        gamma choice.color choice.vertex) (_ : data.coloring idx.succ = TwoColorComponentSwap G
        secondStable gamma choice.color (Sum.inl choice.vertex)) (_ : IsProperEdgeColoring G
        (data.coloring idx.succ)) (_ : IsOneEdgeUncolored (data.coloring idx.succ) e0) (_ :
        data.stored idx.succ = (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin
        k))) (_ : data.connectingEdges idx.succ = ({ choice.edge } : Finset E)) (_ : data.kind
        idx.succ = some TashkinovExtensionKind.PE) (_ : data.chosenVertex idx.succ = some
        choice.vertex) (_ : data.outsideVertex idx.succ = some choice.otherEndpoint) (_ :
        data.delta idx.succ = some choice.color) (_ : data.gamma idx.succ = some gamma) (_ :
        TashkinovClosure (data.coloring idx.succ) (data.tree idx.succ.castSucc) (data.tree
        idx.succ.succ)) (_ : TreeSequenceInitialSegment (data.tree idx.succ.castSucc) (data.tree
        idx.succ.succ)) (_ : (data.tree idx.succ.castSucc).length < (data.tree
        idx.succ.succ).length) (hidx : (↑idx : ℕ) < m),
    let idx' : Fin m := (⟨(↑idx : ℕ), hidx⟩ : Fin m);
    ∀ (hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc = data.coloring
        idx.castSucc) (htree : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc =
        data.tree idx.succ.castSucc) (_ : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ
        = data.coloring idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
        data.stored idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).connectingEdges idx'.succ
        = data.connectingEdges idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ
        = data.kind idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).chosenVertex idx'.succ =
        data.chosenVertex idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).outsideVertex
        idx'.succ = data.outsideVertex idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).delta
        idx'.succ = data.delta idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).gamma
        idx'.succ = data.gamma idx.succ) (_ : (TashkinovSeriesDataPrefix m hm data).tree
        idx'.succ.succ = data.tree idx.succ.succ) (hstored : TashkinovStoredColors
        (TashkinovSeriesDataPrefix m hm data) idx'.castSucc = TashkinovStoredColors data
        idx.castSucc),
    let choice' : MaximumDefectiveChoice G e0 ((TashkinovSeriesDataPrefix m hm data).tree
        idx'.succ.castSucc) (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc) ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) := {
        selected := choice.selected, selectedProper := choice.selectedProper, selectedOneUncolored
        := choice.selectedOneUncolored, selectedStable := ((Eq.symm (id (congrArg (fun (_a :
        TreeSequence G e0) ↦ StableColoring _a (TashkinovStoredColors (TashkinovSeriesDataPrefix m
        hm data) idx'.castSucc) ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
        choice.selected) htree))) ▸ ((Eq.symm (id (congrArg (fun (_a : Finset (Fin k)) ↦
        StableColoring (data.tree idx.succ.castSucc) _a ((TashkinovSeriesDataPrefix m hm
        data).coloring idx'.castSucc) choice.selected) hstored))) ▸ ((Eq.symm (id (congrArg (fun
        (_a : PartialEdgeColoring E k) ↦ StableColoring (data.tree idx.succ.castSucc)
        (TashkinovStoredColors data idx.castSucc) _a choice.selected) hprev))) ▸
        choice.selectedStable))), vertex := choice.vertex, vertexDefective := ((Eq.symm (id
        (congrArg (fun (_a : TreeSequence G e0) ↦ DefectiveVertex G choice.selected
        (TreeSequenceVertexSet _a) choice.vertex) htree))) ▸ choice.vertexDefective), maximal :=
        ((Eq.symm (id (congrArg (fun (_a : TreeSequence G e0) ↦
    ∀ (pi : PartialEdgeColoring E k) (w : V), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0
        → StableColoring _a (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc) ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) pi →
        DefectiveVertex G pi (TreeSequenceVertexSet _a) w → w = choice.vertex ∨ TreeVertexOrder _a
        w choice.vertex) htree))) ▸ ((Eq.symm (id (congrArg (fun (_a : Finset (Fin k)) ↦
    ∀ (pi : PartialEdgeColoring E k) (w : V), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0
        → StableColoring (data.tree idx.succ.castSucc) _a ((TashkinovSeriesDataPrefix m hm
        data).coloring idx'.castSucc) pi → DefectiveVertex G pi (TreeSequenceVertexSet (data.tree
        idx.succ.castSucc)) w → w = choice.vertex ∨ TreeVertexOrder (data.tree idx.succ.castSucc)
        w choice.vertex) hstored))) ▸ ((Eq.symm (id (congrArg (fun (_a : PartialEdgeColoring E k)
        ↦
    ∀ (pi : PartialEdgeColoring E k) (w : V), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0
        → StableColoring (data.tree idx.succ.castSucc) (TashkinovStoredColors data idx.castSucc)
        _a pi → DefectiveVertex G pi (TreeSequenceVertexSet (data.tree idx.succ.castSucc)) w → w =
        choice.vertex ∨ TreeVertexOrder (data.tree idx.succ.castSucc) w choice.vertex) hprev))) ▸
        choice.maximal))), edge := choice.edge, edgeDefective := ((Eq.symm (id (congrArg (fun (_a
        : TreeSequence G e0) ↦ DefectiveEdge G choice.selected (TreeSequenceVertexSet _a)
        choice.edge) htree))) ▸ choice.edgeDefective), edgeIncident := choice.edgeIncident,
        otherEndpoint := choice.otherEndpoint, otherOutside := ((Eq.symm (id (congrArg (fun (_a :
        TreeSequence G e0) ↦ choice.otherEndpoint ∉ TreeSequenceVertexSet _a) htree))) ▸
        choice.otherOutside), edgeEnds := choice.edgeEnds, color := choice.color, edgeColor :=
        choice.edgeColor : MaximumDefectiveChoice G e0 ((TashkinovSeriesDataPrefix m hm data).tree
        idx'.succ.castSucc) (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc) ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) };
    ∀ (_ : ¬Nonempty (RevisitingExtensionCertificate (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc)) (_ : ParallelExtensionColor (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc choice'.selected choice'.vertex gamma), TashkinovSeriesStep G k m e0 input
        (TashkinovSeriesDataPrefix m hm data) idx'.succ

private theorem helper_noRevisiting_120.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] {G : LooplessMultigraph V E}
        {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤
        rounds) (idx : Fin rounds), ¬Nonempty (RevisitingExtensionCertificate data idx.castSucc) →
    ∀ (_ : MaximumDefectiveChoice G e0 (data.tree idx.succ.castSucc) (TashkinovStoredColors data
        idx.castSucc) (data.coloring idx.castSucc)), (↑idx : ℕ) + (1 : ℕ) ≤ m →
    ∀ (hidx : (↑idx : ℕ) < m),
    let idx' : Fin m := (⟨(↑idx : ℕ), hidx⟩ : Fin m); (TashkinovSeriesDataPrefix m hm
        data).coloring idx'.castSucc = data.coloring idx.castSucc → (TashkinovSeriesDataPrefix m
        hm data).tree idx'.succ.castSucc = data.tree idx.succ.castSucc →
        (TashkinovSeriesDataPrefix m hm data).tree idx'.castSucc.succ = data.tree
        idx.castSucc.succ → TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc = TashkinovStoredColors data idx.castSucc → ¬Nonempty
        (RevisitingExtensionCertificate (TashkinovSeriesDataPrefix m hm data) idx'.castSucc) := by
  classical
  intro V E _ _ G k rounds e0 data m hm idx noRevisiting choice hidxSucc hidx idx' hprev htree
      htreeCurrent hstored
  rintro ⟨r⟩
  apply noRevisiting
  let earlier' : Fin (rounds + 1) := Fin.castLE (by omega) r.earlier
  have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
      r.earlier = data.kind earlier' := by rfl
  have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
      r.earlier = data.gamma earlier' := by rfl
  have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
      r.earlier = data.delta earlier' := by rfl
  have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
      r.earlier.castSucc = data.tree earlier'.castSucc := by rfl
  let cycle' : TwoColorCycle G (data.coloring idx.castSucc)
      r.gamma r.delta := {
    base := r.cycle.base
    walk := @Eq.ndrec (PartialEdgeColoring E k)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
        r.cycle.base r.cycle.base)
      r.cycle.walk (data.coloring idx.castSucc) hprev
    isCycle := by
      dsimp
      cases hprev
      exact r.cycle.isCycle
  }
  let returnPath' : (TwoColorIncidenceGraph G (data.coloring idx.castSucc)
      r.gamma r.delta).Walk (Sum.inr r.edge) (Sum.inl r.returnVertex) :=
    @Eq.ndrec (PartialEdgeColoring E k)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
        (Sum.inr r.edge) (Sum.inl r.returnVertex))
      r.returnPath (data.coloring idx.castSucc) hprev
  refine ⟨{
    earlier := earlier'
    earlierPositive := by simpa [earlier'] using r.earlierPositive
    earlierAtMost := by simpa [earlier', idx'] using r.earlierAtMost
    earlierPE := by
      simpa [hkindEarlier] using r.earlierPE
    interveningRevisiting := ?_
    gamma := r.gamma
    delta := r.delta
    earlierGamma := by
      simpa [hgammaEarlier] using r.earlierGamma
    earlierDelta := by
      simpa [hdeltaEarlier] using r.earlierDelta
    cycle := cycle'
    meetsEarlier := by
      rcases r.meetsEarlier with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [htreeEarlier] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    leavesCurrent := by
      rcases r.leavesCurrent with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [htreeCurrent] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    edge := r.edge
    edgeOnCycle := by
      dsimp [cycle']
      cases hprev
      exact r.edgeOnCycle
    edgeBoundary := by
      simpa only [htreeCurrent] using r.edgeBoundary
    insideEndpoint := r.insideEndpoint
    outsideEndpoint := r.outsideEndpoint
    insideInCurrent := by
      simpa only [htreeCurrent] using r.insideInCurrent
    outsideNotCurrent := by
      simpa only [htreeCurrent] using r.outsideNotCurrent
    edgeEnds := r.edgeEnds
    returnVertex := r.returnVertex
    returnInEarlier := by
      simpa [htreeEarlier] using r.returnInEarlier
    returnPath := returnPath'
    returnPathIsPath := by
      dsimp [returnPath']
      cases hprev
      exact r.returnPathIsPath
    returnPathOnCycle := by
      dsimp [returnPath', cycle']
      cases hprev
      exact r.returnPathOnCycle
    returnPathInternal := by
      intro v hv
      have hv' : Sum.inl v ∈ r.returnPath.support := by
        dsimp [returnPath'] at hv
        cases hprev
        exact hv
      simpa only [htreeCurrent] using r.returnPathInternal v hv'
  }⟩
  intro j hjpos hjafter hjatMost
  have hjle : j.val ≤ idx.val := by
    simpa [idx'] using hjatMost
  have hjm : j.val < m + 1 := by omega
  let j' : Fin (m + 1) := ⟨j.val, hjm⟩
  have hstep := r.interveningRevisiting j' (by simpa [j'] using hjpos)
    (by simpa [j', earlier'] using hjafter)
    (by simpa [j', idx'] using hjatMost)
  have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j' =
      data.kind j := by rfl
  simpa [hkindJ] using hstep

private theorem helper_noRevisiting_362.{u_1, u_2} :
    helperNoRevisiting362Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ G k rounds e0 data m hm idx noRevisiting choice gamma hidxSucc hidx idx' hprev
      htree htreeCurrent hstored
  rintro ⟨r⟩
  apply noRevisiting
  let earlier' : Fin (rounds + 1) := Fin.castLE (by omega) r.earlier
  have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
      r.earlier = data.kind earlier' := by rfl
  have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
      r.earlier = data.gamma earlier' := by rfl
  have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
      r.earlier = data.delta earlier' := by rfl
  have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
      r.earlier.castSucc = data.tree earlier'.castSucc := by rfl
  let cycle' : TwoColorCycle G (data.coloring idx.castSucc)
      r.gamma r.delta := {
    base := r.cycle.base
    walk := @Eq.ndrec (PartialEdgeColoring E k)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
        r.cycle.base r.cycle.base)
      r.cycle.walk (data.coloring idx.castSucc) hprev
    isCycle := by
      dsimp
      cases hprev
      exact r.cycle.isCycle
  }
  let returnPath' : (TwoColorIncidenceGraph G (data.coloring idx.castSucc)
      r.gamma r.delta).Walk (Sum.inr r.edge) (Sum.inl r.returnVertex) :=
    @Eq.ndrec (PartialEdgeColoring E k)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
        (Sum.inr r.edge) (Sum.inl r.returnVertex))
      r.returnPath (data.coloring idx.castSucc) hprev
  refine ⟨{
    earlier := earlier'
    earlierPositive := by simpa [earlier'] using r.earlierPositive
    earlierAtMost := by simpa [earlier', idx'] using r.earlierAtMost
    earlierPE := by simpa [hkindEarlier] using r.earlierPE
    interveningRevisiting := ?_
    gamma := r.gamma
    delta := r.delta
    earlierGamma := by simpa [hgammaEarlier] using r.earlierGamma
    earlierDelta := by simpa [hdeltaEarlier] using r.earlierDelta
    cycle := cycle'
    meetsEarlier := by
      rcases r.meetsEarlier with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [htreeEarlier] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    leavesCurrent := by
      rcases r.leavesCurrent with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [htreeCurrent] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    edge := r.edge
    edgeOnCycle := by
      dsimp [cycle']
      cases hprev
      exact r.edgeOnCycle
    edgeBoundary := by
      simpa only [htreeCurrent] using r.edgeBoundary
    insideEndpoint := r.insideEndpoint
    outsideEndpoint := r.outsideEndpoint
    insideInCurrent := by
      simpa only [htreeCurrent] using r.insideInCurrent
    outsideNotCurrent := by
      simpa only [htreeCurrent] using r.outsideNotCurrent
    edgeEnds := r.edgeEnds
    returnVertex := r.returnVertex
    returnInEarlier := by
      simpa [htreeEarlier] using r.returnInEarlier
    returnPath := returnPath'
    returnPathIsPath := by
      dsimp [returnPath']
      cases hprev
      exact r.returnPathIsPath
    returnPathOnCycle := by
      dsimp [returnPath', cycle']
      cases hprev
      exact r.returnPathOnCycle
    returnPathInternal := by
      intro v hv
      have hv' : Sum.inl v ∈ r.returnPath.support := by
        dsimp [returnPath'] at hv
        cases hprev
        exact hv
      simpa only [htreeCurrent] using r.returnPathInternal v hv'
  }⟩
  intro j hjpos hjafter hjatMost
  have hjle : j.val ≤ idx.val := by simpa [idx'] using hjatMost
  have hjm : j.val < m + 1 := by omega
  let j' : Fin (m + 1) := ⟨j.val, hjm⟩
  have hstep := r.interveningRevisiting j' (by simpa [j'] using hjpos)
    (by simpa [j', earlier'] using hjafter)
    (by simpa [j', idx'] using hjatMost)
  have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j' =
      data.kind j := by rfl
  simpa [hkindJ] using hstep

private theorem helper_branch_286.{u_1, u_2} :
    helperBranch286Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm triple seedLength initialColoring initialStored
      initialEdges initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure hj
  refine ⟨TashkinovSeriesStep.initial triple ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    proof_irrel_heq _ _⟩
  · simpa [TashkinovSeriesDataPrefix] using seedLength
  · simpa [TashkinovSeriesDataPrefix] using initialColoring
  · simpa [TashkinovSeriesDataPrefix] using initialStored
  · simpa [TashkinovSeriesDataPrefix] using initialEdges
  · simpa [TashkinovSeriesDataPrefix] using initialKind
  · simpa [TashkinovSeriesDataPrefix] using initialVertex
  · simpa [TashkinovSeriesDataPrefix] using initialOutside
  · simpa [TashkinovSeriesDataPrefix] using initialDelta
  · simpa [TashkinovSeriesDataPrefix] using initialGamma
  · simpa only [TashkinovSeriesDataPrefix, Fin.castLE_zero]

private theorem helper_prefixCert_1176.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (_ : Fin (m + (1 :
        ℕ))) (idx : Fin rounds), IsProperEdgeColoring G (data.coloring idx.castSucc) →
        IsOneEdgeUncolored (data.coloring idx.castSucc) e0 → ColoredVertexSetClosed G
        (data.coloring idx.castSucc) (TreeSequenceVertexSet (data.tree idx.succ.castSucc)) →
        ¬ColoredVertexSetStronglyClosed G (data.coloring idx.castSucc) (TreeSequenceVertexSet
        (data.tree idx.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate data idx.castSucc), data.coloring idx.succ =
        data.coloring idx.castSucc → data.stored idx.succ = (insert available.delta
        ({ available.gamma } : Finset (Fin k)) : Finset (Fin k)) → data.connectingEdges idx.succ =
        ({ available.edge } : Finset E) → data.kind idx.succ = some TashkinovExtensionKind.RE →
        data.chosenVertex idx.succ = some available.insideEndpoint → data.outsideVertex idx.succ =
        some available.outsideEndpoint → data.delta idx.succ = some available.delta → data.gamma
        idx.succ = some available.gamma →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (data.tree idx.succ.castSucc)
        available.edge adjoined → TashkinovClosure (data.coloring idx.succ) adjoined (data.tree
        idx.succ.succ) → TreeSequenceInitialSegment (data.tree idx.succ.castSucc) (data.tree
        idx.succ.succ) → (data.tree idx.succ.castSucc).length < (data.tree idx.succ.succ).length →
    ∀ (hidx : (↑idx : ℕ) < m),
    let idx' : Fin m := (⟨(↑idx : ℕ), hidx⟩ : Fin m);
    ∀ (hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc = data.coloring
        idx.castSucc), (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc = data.tree
        idx.succ.castSucc →
    ∀ (htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree idx'.castSucc.succ = data.tree
        idx.castSucc.succ), (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
        data.coloring idx.succ → (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
        data.stored idx.succ → (TashkinovSeriesDataPrefix m hm data).connectingEdges idx'.succ =
        data.connectingEdges idx.succ → (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
        data.kind idx.succ → (TashkinovSeriesDataPrefix m hm data).chosenVertex idx'.succ =
        data.chosenVertex idx.succ → (TashkinovSeriesDataPrefix m hm data).outsideVertex idx'.succ
        = data.outsideVertex idx.succ → (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
        data.delta idx.succ → (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ = data.gamma
        idx.succ → (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ = data.tree
        idx.succ.succ →
    ∀ (haBound : (↑available.earlier : ℕ) < m + (1 : ℕ)),
    let earlier' : Fin (m + (1 : ℕ)) := (⟨(↑available.earlier : ℕ), haBound⟩ : Fin (m + (1 : ℕ)));
    ∀ (hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind earlier' = data.kind
        available.earlier) (hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma earlier' =
        data.gamma available.earlier) (hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
        earlier' = data.delta available.earlier) (htreeEarlier : (TashkinovSeriesDataPrefix m hm
        data).tree earlier'.castSucc = data.tree available.earlier.castSucc),
    let _ : RevisitingExtensionCertificate (TashkinovSeriesDataPrefix m hm data) idx'.castSucc :=
        helperAvailable754 data m hm idx available hidx hprev htreeCurrent haBound hkindEarlier
        hgammaEarlier hdeltaEarlier htreeEarlier; TashkinovSeriesStep G k m e0 input
        (TashkinovSeriesDataPrefix m hm data) idx'.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm i idx previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension hidx idx' hprev htree
      htreeCurrent hcur hcurStored hcurEdges hcurKind hcurVertex hcurOutside hcurDelta hcurGamma
      hnext haBound earlier' hkindEarlier hgammaEarlier hdeltaEarlier htreeEarlier available'
  apply TashkinovSeriesStep.RE (input := input) (i := idx') (available := available')
    (adjoined := adjoined)
  · rw [hprev]
    exact previousProper
  · rw [hprev]
    exact previousOneUncolored
  · rw [hprev, htree]
    exact previousClosed
  · rw [hprev, htree]
    exact previousNotStronglyClosed
  · rw [hcur, hprev]
    exact currentColoring
  · change (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
      {available.delta, available.gamma}
    rw [hcurStored]
    exact currentStored
  · change (TashkinovSeriesDataPrefix m hm data).connectingEdges
      idx'.succ = {available.edge}
    rw [hcurEdges]
    exact currentEdges
  · rw [hcurKind]
    exact currentKind
  · change (TashkinovSeriesDataPrefix m hm data).chosenVertex
      idx'.succ = some available.insideEndpoint
    rw [hcurVertex]
    exact currentVertex
  · change (TashkinovSeriesDataPrefix m hm data).outsideVertex
      idx'.succ = some available.outsideEndpoint
    rw [hcurOutside]
    exact currentOutside
  · change (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
      some available.delta
    rw [hcurDelta]
    exact currentDelta
  · change (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
      some available.gamma
    rw [hcurGamma]
    exact currentGamma
  · change TreeSequenceAdjoinEdge
      ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
      available.edge adjoined
    rw [htree]
    exact adjoinedExactly
  · rw [hcur, hnext]
    exact closedExtension
  · rw [htree, hnext]
    exact orderedExtension
  · rw [htree, hnext]
    exact strictExtension

private theorem helper_prefixCert_1166.{u_1, u_2} :
    helperPrefixCert1166Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm i idx previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed choice seriesAlternativeFails gamma secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension hidx idx' hprev htree hcur hcurStored hcurEdges hcurKind hcurVertex
      hcurOutside hcurDelta hcurGamma hnext hstored choice' noRevisiting' gammaRule'
  apply TashkinovSeriesStep.PE (input := input) (i := idx') (choice := choice')
    (gamma := gamma) (secondStable := secondStable)
  · rw [hprev]
    exact previousProper
  · rw [hprev]
    exact previousOneUncolored
  · rw [hprev, htree]
    exact previousClosed
  · rw [hprev, htree]
    exact previousNotStronglyClosed
  · exact noRevisiting'
  · rcases seriesAlternativeFails with ⟨rho, hp, ho, hs, hd⟩
    refine ⟨rho, hp, ho, ?_, ?_⟩
    · change StableColoring
        ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
        (insert choice.color (TashkinovStoredColors
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc))
        choice.selected rho
      rw [htree, hstored]
      exact hs
    · change ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
        (TreeMissingColors rho
          ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc))
      rw [htree]
      exact hd
  · exact gammaRule'
  · exact secondStableProper
  · exact secondStableOneUncolored
  · change StableColoring
      ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
      (insert choice.color (TashkinovStoredColors
        (TashkinovSeriesDataPrefix m hm data) idx'.castSucc))
      choice.selected secondStable
    rw [htree, hstored]
    exact secondStableRelation
  · change TreeExit
      ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
      secondStable gamma choice.color choice.vertex
    rw [htree]
    exact exitWitness
  · change (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
      TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex)
    rw [hcur]
    exact currentColoring
  · rw [hcur]
    exact currentProper
  · rw [hcur]
    exact currentOneUncolored
  · change (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
      {choice.color, gamma}
    rw [hcurStored]
    exact currentStored
  · change (TashkinovSeriesDataPrefix m hm data).connectingEdges
      idx'.succ = {choice.edge}
    rw [hcurEdges]
    exact currentEdges
  · rw [hcurKind]
    exact currentKind
  · change (TashkinovSeriesDataPrefix m hm data).chosenVertex
      idx'.succ = some choice.vertex
    rw [hcurVertex]
    exact currentVertex
  · change (TashkinovSeriesDataPrefix m hm data).outsideVertex
      idx'.succ = some choice.otherEndpoint
    rw [hcurOutside]
    exact currentOutside
  · change (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
      some choice.color
    rw [hcurDelta]
    exact currentDelta
  · rw [hcurGamma]
    exact currentGamma
  · rw [hcur, htree, hnext]
    exact closedExtension
  · rw [htree, hnext]
    exact orderedExtension
  · rw [htree, hnext]
    exact strictExtension

private theorem helper_branch_1369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (_ : Fin (m + (1 :
        ℕ))) (idx : Fin rounds) (previousProper : IsProperEdgeColoring G (data.coloring
        idx.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (data.coloring idx.castSucc) e0)
        (previousClosed : ColoredVertexSetClosed G (data.coloring idx.castSucc)
        (TreeSequenceVertexSet (data.tree idx.succ.castSucc))) (previousNotStronglyClosed :
        ¬ColoredVertexSetStronglyClosed G (data.coloring idx.castSucc) (TreeSequenceVertexSet
        (data.tree idx.succ.castSucc))) (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate
        data idx.castSucc)) (choice : MaximumDefectiveChoice G e0 (data.tree idx.succ.castSucc)
        (TashkinovStoredColors data idx.castSucc) (data.coloring idx.castSucc))
        (seriesAlternativeFails :
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (data.tree idx.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data idx.castSucc) : Finset (Fin k)) choice.selected rho ∧ ¬Disjoint (MissingColors G rho
        choice.otherEndpoint) (TreeMissingColors rho (data.tree idx.succ.castSucc))) (gamma : Fin
        k) (gammaRule : ParallelExtensionColor data idx.castSucc choice.selected choice.vertex
        gamma) (secondStable : PartialEdgeColoring E k) (secondStableProper : IsProperEdgeColoring
        G secondStable) (secondStableOneUncolored : IsOneEdgeUncolored secondStable e0)
        (secondStableRelation : StableColoring (data.tree idx.succ.castSucc) (insert choice.color
        (TashkinovStoredColors data idx.castSucc) : Finset (Fin k)) choice.selected secondStable)
        (exitWitness : TreeExit (data.tree idx.succ.castSucc) secondStable gamma choice.color
        choice.vertex) (currentColoring : data.coloring idx.succ = TwoColorComponentSwap G
        secondStable gamma choice.color (Sum.inl choice.vertex)) (currentProper :
        IsProperEdgeColoring G (data.coloring idx.succ)) (currentOneUncolored : IsOneEdgeUncolored
        (data.coloring idx.succ) e0) (currentStored : data.stored idx.succ = (insert choice.color
        ({ gamma } : Finset (Fin k)) : Finset (Fin k))) (currentEdges : data.connectingEdges
        idx.succ = ({ choice.edge } : Finset E)) (currentKind : data.kind idx.succ = some
        TashkinovExtensionKind.PE) (currentVertex : data.chosenVertex idx.succ = some
        choice.vertex) (currentOutside : data.outsideVertex idx.succ = some choice.otherEndpoint)
        (currentDelta : data.delta idx.succ = some choice.color) (currentGamma : data.gamma
        idx.succ = some gamma) (closedExtension : TashkinovClosure (data.coloring idx.succ)
        (data.tree idx.succ.castSucc) (data.tree idx.succ.succ)) (orderedExtension :
        TreeSequenceInitialSegment (data.tree idx.succ.castSucc) (data.tree idx.succ.succ))
        (strictExtension : (data.tree idx.succ.castSucc).length < (data.tree
        idx.succ.succ).length) (hj : (↑idx.succ : ℕ) ≤ m),
    ∃ (prefixCert : TashkinovSeriesStep G k m e0 input (TashkinovSeriesDataPrefix m hm data)
        (⟨(↑idx.succ : ℕ),
    by
          omega
    ⟩ : Fin (m + (1 : ℕ)))), prefixCert ≍ TashkinovSeriesStep.PE (input := input) idx
        previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
        choice seriesAlternativeFails gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma closedExtension orderedExtension strictExtension := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm i idx previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma
      gammaRule secondStable secondStableProper secondStableOneUncolored secondStableRelation
      exitWitness currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension hj
  have hidxSucc : idx.val + 1 ≤ m := by simpa using hj
  have hidx : idx.val < m := by omega
  let idx' : Fin m := ⟨idx.val, hidx⟩
  have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
      data.coloring idx.castSucc := by rfl
  have htree : (TashkinovSeriesDataPrefix m hm data).tree
      idx'.succ.castSucc = data.tree idx.succ.castSucc := by rfl
  have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree
      idx'.castSucc.succ = data.tree idx.castSucc.succ := by rfl
  have hcur : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
      data.coloring idx.succ := by rfl
  have hcurStored : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
      data.stored idx.succ := by rfl
  have hcurEdges : (TashkinovSeriesDataPrefix m hm data).connectingEdges
      idx'.succ = data.connectingEdges idx.succ := by rfl
  have hcurKind : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
      data.kind idx.succ := by rfl
  have hcurVertex : (TashkinovSeriesDataPrefix m hm data).chosenVertex
      idx'.succ = data.chosenVertex idx.succ := by rfl
  have hcurOutside : (TashkinovSeriesDataPrefix m hm data).outsideVertex
      idx'.succ = data.outsideVertex idx.succ := by rfl
  have hcurDelta : (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
      data.delta idx.succ := by rfl
  have hcurGamma : (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
      data.gamma idx.succ := by rfl
  have hnext : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ =
      data.tree idx.succ.succ := by rfl
  have hstored : TashkinovStoredColors
      (TashkinovSeriesDataPrefix m hm data) idx'.castSucc =
      TashkinovStoredColors data idx.castSucc := by
    exact TashkinovStoredColorsPrefix m hm data idx'.castSucc
  let choice' : MaximumDefectiveChoice G e0
      ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
      (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) := by
    exact {
      selected := choice.selected
      selectedProper := choice.selectedProper
      selectedOneUncolored := choice.selectedOneUncolored
      selectedStable := by
        rw [htree, hstored, hprev]
        exact choice.selectedStable
      vertex := choice.vertex
      vertexDefective := by
        rw [htree]
        exact choice.vertexDefective
      maximal := by
        rw [htree, hstored, hprev]
        exact choice.maximal
      edge := choice.edge
      edgeDefective := by
        rw [htree]
        exact choice.edgeDefective
      edgeIncident := choice.edgeIncident
      otherEndpoint := choice.otherEndpoint
      otherOutside := by
        rw [htree]
        exact choice.otherOutside
      edgeEnds := choice.edgeEnds
      color := choice.color
      edgeColor := choice.edgeColor
    }
  have noRevisiting' : ¬ Nonempty (RevisitingExtensionCertificate
      (TashkinovSeriesDataPrefix m hm data) idx'.castSucc) := by
    apply helper_noRevisiting_362 <;> assumption
  have gammaRule' : ParallelExtensionColor
      (TashkinovSeriesDataPrefix m hm data) idx'.castSucc
      choice'.selected choice'.vertex gamma := by
    change ParallelExtensionColor (TashkinovSeriesDataPrefix m hm data)
      idx'.castSucc choice.selected choice.vertex gamma
    unfold ParallelExtensionColor at gammaRule ⊢
    refine ⟨gammaRule.1, ?_⟩
    rcases gammaRule.2 with existing | fresh
    · left
      rcases existing with
        ⟨h, hpos, hatMost, hkind, hvertex, hdelta, hlatest⟩
      have hle : h.val ≤ idx.val := by simpa using hatMost
      have hhm : h.val < m + 1 := by omega
      let h' : Fin (m + 1) := ⟨h.val, hhm⟩
      refine ⟨h', by simpa [h'] using hpos, by simpa [h', idx'] using hatMost,
        ?_, ?_, ?_, ?_⟩
      · simpa [h', TashkinovSeriesDataPrefix] using hkind
      · simpa [h', TashkinovSeriesDataPrefix] using hvertex
      · simpa [h', TashkinovSeriesDataPrefix] using hdelta
      · intro j jpos jatMost jkind jvertex
        let j' : Fin (rounds + 1) := Fin.castLE (by omega) j
        have latest := hlatest j' (by simpa [j'] using jpos)
          (by simpa [j', idx'] using jatMost)
          (by simpa [j', TashkinovSeriesDataPrefix] using jkind)
          (by simpa [j', TashkinovSeriesDataPrefix] using jvertex)
        simpa [j', h'] using latest
    · right
      intro h hpos hatMost hkind hvertex
      let h' : Fin (rounds + 1) := Fin.castLE (by omega) h
      apply fresh h' (by simpa [h'] using hpos)
        (by simpa [h', idx'] using hatMost)
      · simpa [h', TashkinovSeriesDataPrefix] using hkind
      · simpa [h', TashkinovSeriesDataPrefix] using hvertex
  have prefixCert := @helper_prefixCert_1166 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@rounds) (@e0) (@input) (@data) (@m) (@hm) (@i) (@idx) (@previousProper)
      (@previousOneUncolored) (@previousClosed) (@previousNotStronglyClosed) (@choice)
      (@seriesAlternativeFails) (@gamma) (@secondStable) (@secondStableProper)
      (@secondStableOneUncolored) (@secondStableRelation) (@exitWitness) (@currentColoring)
      (@currentProper) (@currentOneUncolored) (@currentStored) (@currentEdges) (@currentKind)
      (@currentVertex) (@currentOutside) (@currentDelta) (@currentGamma) (@closedExtension)
      (@orderedExtension) (@strictExtension) (@hidx) (@hprev) (@htree) (@hcur) (@hcurStored)
      (@hcurEdges) (@hcurKind) (@hcurVertex) (@hcurOutside) (@hcurDelta) (@hcurGamma) (@hnext)
      (@hstored) (@noRevisiting') (@gammaRule')
  have hresult : idx'.succ =
      (⟨idx.succ.val, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  rw [← hresult]
  exact ⟨prefixCert, proof_irrel_heq _ _⟩

private theorem helper_branch_1414.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (_ : Fin (m + (1 :
        ℕ))) (idx : Fin rounds) (previousProper : IsProperEdgeColoring G (data.coloring
        idx.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (data.coloring idx.castSucc) e0)
        (previousClosed : ColoredVertexSetClosed G (data.coloring idx.castSucc)
        (TreeSequenceVertexSet (data.tree idx.succ.castSucc))) (previousNotStronglyClosed :
        ¬ColoredVertexSetStronglyClosed G (data.coloring idx.castSucc) (TreeSequenceVertexSet
        (data.tree idx.succ.castSucc))) (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate
        data idx.castSucc)) (choice : MaximumDefectiveChoice G e0 (data.tree idx.succ.castSucc)
        (TashkinovStoredColors data idx.castSucc) (data.coloring idx.castSucc)) (seriesAlternative
        :
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (data.tree idx.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data idx.castSucc) : Finset (Fin k)) choice.selected pi → Disjoint (MissingColors G pi
        choice.otherEndpoint) (TreeMissingColors pi (data.tree idx.succ.castSucc)))
        (currentColoring : data.coloring idx.succ = choice.selected) (currentStored : data.stored
        idx.succ = ({ choice.color } : Finset (Fin k))) (currentEdges : data.connectingEdges
        idx.succ = ({ choice.edge } : Finset E)) (currentKind : data.kind idx.succ = some
        TashkinovExtensionKind.SE) (currentVertex : data.chosenVertex idx.succ = some
        choice.vertex) (currentOutside : data.outsideVertex idx.succ = some choice.otherEndpoint)
        (currentDelta : data.delta idx.succ = some choice.color) (currentGamma : data.gamma
        idx.succ = none) (adjoined : TreeSequence G e0) (adjoinedExactly : TreeSequenceAdjoinEdge
        (data.tree idx.succ.castSucc) choice.edge adjoined) (closedExtension : TashkinovClosure
        (data.coloring idx.succ) adjoined (data.tree idx.succ.succ)) (orderedExtension :
        TreeSequenceInitialSegment (data.tree idx.succ.castSucc) (data.tree idx.succ.succ))
        (strictExtension : (data.tree idx.succ.castSucc).length < (data.tree
        idx.succ.succ).length) (hj : (↑idx.succ : ℕ) ≤ m),
    ∃ (prefixCert : TashkinovSeriesStep G k m e0 input (TashkinovSeriesDataPrefix m hm data)
        (⟨(↑idx.succ : ℕ),
    by
          omega
    ⟩ : Fin (m + (1 : ℕ)))), prefixCert ≍ TashkinovSeriesStep.SE (input := input) idx
        previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
        choice seriesAlternative currentColoring currentStored currentEdges currentKind
        currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm i idx previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension hj
  have hidxSucc : idx.val + 1 ≤ m := by simpa using hj
  have hidx : idx.val < m := by omega
  let idx' : Fin m := ⟨idx.val, hidx⟩
  have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
      data.coloring idx.castSucc := by rfl
  have htree : (TashkinovSeriesDataPrefix m hm data).tree
      idx'.succ.castSucc = data.tree idx.succ.castSucc := by rfl
  have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree
      idx'.castSucc.succ = data.tree idx.castSucc.succ := by rfl
  have hcur : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
      data.coloring idx.succ := by rfl
  have hcurStored : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
      data.stored idx.succ := by rfl
  have hcurEdges : (TashkinovSeriesDataPrefix m hm data).connectingEdges
      idx'.succ = data.connectingEdges idx.succ := by rfl
  have hcurKind : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
      data.kind idx.succ := by rfl
  have hcurVertex : (TashkinovSeriesDataPrefix m hm data).chosenVertex
      idx'.succ = data.chosenVertex idx.succ := by rfl
  have hcurOutside : (TashkinovSeriesDataPrefix m hm data).outsideVertex
      idx'.succ = data.outsideVertex idx.succ := by rfl
  have hcurDelta : (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
      data.delta idx.succ := by rfl
  have hcurGamma : (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
      data.gamma idx.succ := by rfl
  have hnext : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ =
      data.tree idx.succ.succ := by rfl
  have hstored : TashkinovStoredColors
      (TashkinovSeriesDataPrefix m hm data) idx'.castSucc =
      TashkinovStoredColors data idx.castSucc := by
    exact TashkinovStoredColorsPrefix m hm data idx'.castSucc
  let choice' : MaximumDefectiveChoice G e0
      ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
      (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
        idx'.castSucc)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) := by
    exact {
      selected := choice.selected
      selectedProper := choice.selectedProper
      selectedOneUncolored := choice.selectedOneUncolored
      selectedStable := by
        rw [htree, hstored, hprev]
        exact choice.selectedStable
      vertex := choice.vertex
      vertexDefective := by
        rw [htree]
        exact choice.vertexDefective
      maximal := by
        rw [htree, hstored, hprev]
        exact choice.maximal
      edge := choice.edge
      edgeDefective := by
        rw [htree]
        exact choice.edgeDefective
      edgeIncident := choice.edgeIncident
      otherEndpoint := choice.otherEndpoint
      otherOutside := by
        rw [htree]
        exact choice.otherOutside
      edgeEnds := choice.edgeEnds
      color := choice.color
      edgeColor := choice.edgeColor
    }
  have noRevisiting' : ¬ Nonempty (RevisitingExtensionCertificate
      (TashkinovSeriesDataPrefix m hm data) idx'.castSucc) := by
    apply helper_noRevisiting_120 <;> assumption
  have prefixCert : TashkinovSeriesStep G k m e0 input
      (TashkinovSeriesDataPrefix m hm data) idx'.succ := by
    apply TashkinovSeriesStep.SE (input := input) (i := idx') (choice := choice')
      (adjoined := adjoined)
    · rw [hprev]
      exact previousProper
    · rw [hprev]
      exact previousOneUncolored
    · rw [hprev, htree]
      exact previousClosed
    · rw [hprev, htree]
      exact previousNotStronglyClosed
    · exact noRevisiting'
    · intro pi hp ho hs
      apply seriesAlternative pi hp ho
      change StableColoring
        ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
        (insert choice.color (TashkinovStoredColors
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc))
        choice.selected pi at hs
      rw [htree, hstored] at hs
      exact hs
    · change (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
        choice.selected
      rw [hcur]
      exact currentColoring
    · change (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
        {choice.color}
      rw [hcurStored]
      exact currentStored
    · change (TashkinovSeriesDataPrefix m hm data).connectingEdges
        idx'.succ = {choice.edge}
      rw [hcurEdges]
      exact currentEdges
    · rw [hcurKind]
      exact currentKind
    · change (TashkinovSeriesDataPrefix m hm data).chosenVertex
        idx'.succ = some choice.vertex
      rw [hcurVertex]
      exact currentVertex
    · change (TashkinovSeriesDataPrefix m hm data).outsideVertex
        idx'.succ = some choice.otherEndpoint
      rw [hcurOutside]
      exact currentOutside
    · change (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
        some choice.color
      rw [hcurDelta]
      exact currentDelta
    · rw [hcurGamma]
      exact currentGamma
    · change TreeSequenceAdjoinEdge
        ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
        choice.edge adjoined
      rw [htree]
      exact adjoinedExactly
    · rw [hcur, hnext]
      exact closedExtension
    · rw [htree, hnext]
      exact orderedExtension
    · rw [htree, hnext]
      exact strictExtension
  have hresult : idx'.succ =
      (⟨idx.succ.val, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  rw [← hresult]
  exact ⟨prefixCert, proof_irrel_heq _ _⟩

private theorem helper_branch_1559.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (idx : Fin rounds)
        (previousProper : IsProperEdgeColoring G (data.coloring idx.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (data.coloring idx.castSucc) e0)
        (previousClosed : ColoredVertexSetClosed G (data.coloring idx.castSucc)
        (TreeSequenceVertexSet (data.tree idx.succ.castSucc))) (previousNotStronglyClosed :
        ¬ColoredVertexSetStronglyClosed G (data.coloring idx.castSucc) (TreeSequenceVertexSet
        (data.tree idx.succ.castSucc))) (available : RevisitingExtensionCertificate data
        idx.castSucc) (currentColoring : data.coloring idx.succ = data.coloring idx.castSucc)
        (currentStored : data.stored idx.succ = (insert available.delta ({ available.gamma } :
        Finset (Fin k)) : Finset (Fin k))) (currentEdges : data.connectingEdges idx.succ =
        ({ available.edge } : Finset E)) (currentKind : data.kind idx.succ = some
        TashkinovExtensionKind.RE) (currentVertex : data.chosenVertex idx.succ = some
        available.insideEndpoint) (currentOutside : data.outsideVertex idx.succ = some
        available.outsideEndpoint) (currentDelta : data.delta idx.succ = some available.delta)
        (currentGamma : data.gamma idx.succ = some available.gamma) (adjoined : TreeSequence G e0)
        (adjoinedExactly : TreeSequenceAdjoinEdge (data.tree idx.succ.castSucc) available.edge
        adjoined) (closedExtension : TashkinovClosure (data.coloring idx.succ) adjoined (data.tree
        idx.succ.succ)) (orderedExtension : TreeSequenceInitialSegment (data.tree
        idx.succ.castSucc) (data.tree idx.succ.succ)) (strictExtension : (data.tree
        idx.succ.castSucc).length < (data.tree idx.succ.succ).length) (hj : (↑idx.succ : ℕ) ≤ m),
    ∃ (prefixCert : TashkinovSeriesStep G k m e0 input (TashkinovSeriesDataPrefix m hm data)
        (⟨(↑idx.succ : ℕ),
    by
          omega
    ⟩ : Fin (m + (1 : ℕ)))), prefixCert ≍ TashkinovSeriesStep.RE (input := input) idx
        previousProper previousOneUncolored previousClosed previousNotStronglyClosed available
        currentColoring currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm idx previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension hj
  have hidxSucc : idx.val + 1 ≤ m := by simpa using hj
  have hidx : idx.val < m := by omega
  let idx' : Fin m := ⟨idx.val, hidx⟩
  have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
      data.coloring idx.castSucc := by rfl
  have htree : (TashkinovSeriesDataPrefix m hm data).tree
      idx'.succ.castSucc = data.tree idx.succ.castSucc := by rfl
  have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree
      idx'.castSucc.succ = data.tree idx.castSucc.succ := by rfl
  have hcur : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
      data.coloring idx.succ := by rfl
  have hcurStored : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
      data.stored idx.succ := by rfl
  have hcurEdges : (TashkinovSeriesDataPrefix m hm data).connectingEdges
      idx'.succ = data.connectingEdges idx.succ := by rfl
  have hcurKind : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
      data.kind idx.succ := by rfl
  have hcurVertex : (TashkinovSeriesDataPrefix m hm data).chosenVertex
      idx'.succ = data.chosenVertex idx.succ := by rfl
  have hcurOutside : (TashkinovSeriesDataPrefix m hm data).outsideVertex
      idx'.succ = data.outsideVertex idx.succ := by rfl
  have hcurDelta : (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
      data.delta idx.succ := by rfl
  have hcurGamma : (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
      data.gamma idx.succ := by rfl
  have hnext : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ =
      data.tree idx.succ.succ := by rfl
  have haLe : available.earlier.val ≤ idx.val := by
    simpa using available.earlierAtMost
  have haBound : available.earlier.val < m + 1 := by omega
  let earlier' : Fin (m + 1) := ⟨available.earlier.val, haBound⟩
  have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
      earlier' = data.kind available.earlier := by rfl
  have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
      earlier' = data.gamma available.earlier := by rfl
  have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
      earlier' = data.delta available.earlier := by rfl
  have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
      earlier'.castSucc = data.tree available.earlier.castSucc := by rfl
  let cycle' : TwoColorCycle G
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      available.gamma available.delta := {
    base := available.cycle.base
    walk := @Eq.ndrec (PartialEdgeColoring E k)
      (data.coloring idx.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi available.gamma
        available.delta).Walk available.cycle.base available.cycle.base)
      available.cycle.walk
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      hprev.symm
    isCycle := by
      dsimp
      cases hprev
      exact available.cycle.isCycle
  }
  let returnPath' : (TwoColorIncidenceGraph G
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      available.gamma available.delta).Walk (Sum.inr available.edge)
      (Sum.inl available.returnVertex) :=
    @Eq.ndrec (PartialEdgeColoring E k) (data.coloring idx.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi available.gamma
        available.delta).Walk (Sum.inr available.edge)
        (Sum.inl available.returnVertex))
      available.returnPath
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      hprev.symm
  let available' : RevisitingExtensionCertificate
      (TashkinovSeriesDataPrefix m hm data) idx'.castSucc := by
    exact @helperAvailable754 (@V) (@E) inferInstance inferInstance (@G) (@k) (@rounds) (@e0)
        (@data) (@m) (@hm) (@idx) (@available) (@hidx) (@hprev) (@htreeCurrent) (@haBound)
        (@hkindEarlier) (@hgammaEarlier) (@hdeltaEarlier) (@htreeEarlier)
  have prefixCert : TashkinovSeriesStep G k m e0 input
      (TashkinovSeriesDataPrefix m hm data) idx'.succ := by
    apply helper_prefixCert_1176 <;> assumption
  have hresult : idx'.succ =
      (⟨idx.succ.val, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  rw [← hresult]
  exact ⟨prefixCert, proof_irrel_heq _ _⟩

private theorem helper_aux_33.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (input : PartialEdgeColoring E k)
        (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (_ : Fin (m + (1 :
        ℕ))) (j : Fin (rounds + (1 : ℕ))) (hj : (↑j : ℕ) ≤ m) (oldCert : TashkinovSeriesStep G k
        rounds e0 input data j),
    ∃ (prefixCert : TashkinovSeriesStep G k m e0 input (TashkinovSeriesDataPrefix m hm data) (⟨(↑j
        : ℕ), Decidable.byContradiction fun (a : ¬(↑j : ℕ) < m + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (m + (1 : ℕ)))), prefixCert ≍ oldCert := by
  classical
  intro V E _ _ _ G k rounds e0 input data m hm i j hj oldCert
  cases oldCert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
          apply helper_branch_286 <;> assumption
  | SE idx previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1414 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@rounds) (@e0) (@input) (@data) (@m) (@hm) (@i) (@idx) (@previousProper)
              (@previousOneUncolored) (@previousClosed) (@previousNotStronglyClosed)
              (@noRevisiting) (@choice) (@seriesAlternative) (@currentColoring) (@currentStored)
              (@currentEdges) (@currentKind) (@currentVertex) (@currentOutside) (@currentDelta)
              (@currentGamma) (@adjoined) (@adjoinedExactly) (@closedExtension)
              (@orderedExtension) (@strictExtension) (@hj)
  | PE idx previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1369 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@rounds) (@e0) (@input) (@data) (@m) (@hm) (@i) (@idx) (@previousProper)
              (@previousOneUncolored) (@previousClosed) (@previousNotStronglyClosed)
              (@noRevisiting) (@choice) (@seriesAlternativeFails) (@gamma) (@gammaRule)
              (@secondStable) (@secondStableProper) (@secondStableOneUncolored)
              (@secondStableRelation) (@exitWitness) (@currentColoring) (@currentProper)
              (@currentOneUncolored) (@currentStored) (@currentEdges) (@currentKind)
              (@currentVertex) (@currentOutside) (@currentDelta) (@currentGamma)
              (@closedExtension) (@orderedExtension) (@strictExtension) (@hj)
  | RE idx previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_1559 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@rounds) (@e0) (@input) (@data) (@m) (@hm) (@idx) (@previousProper)
              (@previousOneUncolored) (@previousClosed) (@previousNotStronglyClosed) (@available)
              (@currentColoring) (@currentStored) (@currentEdges) (@currentKind) (@currentVertex)
              (@currentOutside) (@currentDelta) (@currentGamma) (@adjoined) (@adjoinedExactly)
              (@closedExtension) (@orderedExtension) (@strictExtension) (@hj)
theorem TashkinovSeriesStepPrefix {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (m : ℕ) (hm : m ≤ rounds) (i : Fin (m + 1))
    (cert : TashkinovSeriesStep G k rounds e0 input data
      (Fin.castLE (by omega) i)) :
    ∃ prefixCert : TashkinovSeriesStep G k m e0 input
        (TashkinovSeriesDataPrefix m hm data) i,
      HEq prefixCert cert := by
  have aux : ∀ (j : Fin (rounds + 1)) (hj : j.val ≤ m)
      (oldCert : TashkinovSeriesStep G k rounds e0 input data j),
      ∃ prefixCert : TashkinovSeriesStep G k m e0 input
          (TashkinovSeriesDataPrefix m hm data) ⟨j.val, by omega⟩,
        HEq prefixCert oldCert := by
    apply helper_aux_33; assumption
  let included : Fin (rounds + 1) :=
    Fin.castLE (Nat.add_le_add_right hm 1) i
  have hibound : included.val ≤ m := by
    exact Nat.le_of_lt_succ i.isLt
  have hcertType : TashkinovSeriesStep G k rounds e0 input data included := by
    exact cert
  obtain ⟨prefixCert, hcert⟩ := aux included hibound hcertType
  have hi : (⟨included.val, by omega⟩ : Fin (m + 1)) = i := by
    apply Fin.ext
    rfl
  rw [hi] at prefixCert
  exact ⟨prefixCert, hcert⟩

end GoldbergSeymour

end
