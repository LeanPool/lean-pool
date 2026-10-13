/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalCompetitor

/-!
# GlobalSuperposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The multi-component competitor: superposition over the components of `ℐ`

`GlobalCompetitor.lean` builds, **for one bad family `C`**, the competitor
`ℓ̂_p^C = globalCompetitor m s C p` on the uniform scale-`s` Kuhn mesh of the
root cube, at that family's own common coarse scale `s = simplexScale m hn j`,
and proves the three `sum_of_a_decomp` clauses at `C`.  This module supplies a
local bridge from that A to the consumer's `badFamily`-indexed clauses: the
**superposition over the distinct connected components** of the bad family.

## Which branch this follows, and why

> Define the global modified affine by assigning the vertex data once on the >
full simplex complex, **or** superpose the component corrections while >
allowing overlap on good cubes.  [.] In the latter presentation one must >
retain a uniform overlap multiplicity (or merge components whose collars >
overlap) in the gradient and energy constants.

(The multiplicity obligation of the second sentence belongs to the summed
gradient estimate and is deliberately deferred — see the Scope section;
quotation expanded.)

The first branch is dissolved **at the vertex-datum level** by
`CompetitorVertexData.lean` (`claimedBadComponent_eq_badComponent`: at most one
component ever claims a vertex).

This module therefore follows the **second branch** (its construction clause
verbatim; its multiplicity clause deferred as noted above): it superposes the
per-component corrections, each built on *its own* component mesh at *its own*
common coarse scale, and it **allows them to overlap on good cubes**.  Nothing
below asserts, or uses, any disjointness of the collars `𝒩(𝒞)`; the pointwise
"at most one nonzero summand" property of the vertex datum is *not* lifted to
the function level and is *not* needed.

> the neighborhood of one component does not contain a bad cube belonging to
> another component

which is `notMem_whitneyNeighborhood_of_ne` below (two lines from `BadChain`
maximality), and which is exactly what clause 1 needs.  Clause 3 needs only the
monotonicity `𝒞 ⊆ ℐ ⟹ 𝒩(𝒞) ⊆ 𝒩(ℐ)`.

## Scope: what this module does NOT do

* Consequently **nothing below identifies `superposedCompetitorSlope` with a
  distributional gradient**; as in `GlobalCompetitor.lean` the field is a
  *defined* piecewise-constant object and the three clauses are statements
  about it.  `e.hat.linear.1` (the `H¹₀` leg) and the `hF`/`hG` binders of
  `sum_of_a_decomp` are untouched.
* **No gradient estimate.**  The summed active-component replacement for the
  false component-local gradient bound is **read and not consumed**: no
  diameter, no overlap count and no constant occurs below.
* **The two-layer window per component is a hypothesis** (`hwin`), exactly as in
  `CommonCoarseMesh.lean` and `GlobalCompetitor.lean` — but unlike there it is
  *discharged* in this file at the manuscript's own bad family
  (`badComponents_window_badFamily`).
* No three-layer window is used; no face-to-face property of `SW(□_m)` is used.

## References

* ABK26, (`l.piecewise.affine.approx`, `e.hat.linear.properties`; clause 1,
  clause 3), (the false disjointness), (Step 1), (`ℐ`, `𝒩(𝒥)`), (the
  components), (`l.bad.clusters.geometry` clause (1)), (`ℓ_e`).
* Its subtype index on the bad components, and its local-finiteness and
  continuity endpoints, have **no counterpart here**: the components are
  indexed by the sets themselves and no local finiteness is used.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The connected components of the bad family -/

/-- **The 2-connected components of `ℐ`**, presented as the set of subfamilies of
the form `badComponent ℐ □`.  Distinct bad cubes of one component give the
*same* member of this set, so it is the component set, not a list with
repetitions. -/
def badComponents (I : Set (TriadicCube d)) : Set (Set (TriadicCube d)) :=
  {C | ∃ Q ∈ I, C = badComponent I Q}

theorem badComponent_mem_badComponents {I : Set (TriadicCube d)} {Q : TriadicCube d}
    (hQ : Q ∈ I) : badComponent I Q ∈ badComponents I := ⟨Q, hQ, rfl⟩

theorem badComponents_subset {I C : Set (TriadicCube d)} (hC : C ∈ badComponents I) :
    C ⊆ I := by
  obtain ⟨Q, -, rfl⟩ := hC
  exact fun _ hR => hR.1

/-- Chain-joined bad cubes have the same component. -/
theorem badComponent_eq_of_badChain {I : Set (TriadicCube d)} {A B : TriadicCube d}
    (h : BadChain I A B) : badComponent I A = badComponent I B := by
  ext Q
  exact ⟨fun hQ => ⟨hQ.1, (badChain_symm h).trans hQ.2⟩, fun hQ => ⟨hQ.1, h.trans hQ.2⟩⟩

/-- **Overlap safety on the bad cubes** — the fact isolates as "what does follow
directly from maximality": a bad cube of one component lies off the touching
neighborhood of every *other* component.  Two cubes at distance zero are one
chain step apart, so a bad cube in `𝒩(𝒞)` is chain-joined to `𝒞` and therefore
belongs to it.

This is the only disjointness this file uses: the good-cube collars `𝒩(𝒞)`
are **not** assumed disjoint anywhere. -/
theorem notMem_whitneyNeighborhood_of_ne {m : ℤ} {hn : ℕ → ℕ}
    {I C : Set (TriadicCube d)} (hC : C ∈ badComponents I) {Q : TriadicCube d}
    (hQ : Q ∈ I) (hne : C ≠ badComponent I Q) :
    Q ∉ whitneyNeighborhood m hn C := by
  rintro ⟨-, R, hRC, hQR⟩
  obtain ⟨Q₀, hQ₀, rfl⟩ := hC
  exact hne ((badComponent_eq_of_badChain hRC.2).trans
    (badComponent_eq_of_badChain
      (Relation.ReflTransGen.single ⟨hQ, badComponents_subset ⟨Q₀, hQ₀, rfl⟩ hRC, hQR⟩)).symm)

/-- The touching neighborhood is monotone in the family. -/
theorem whitneyNeighborhood_mono {m : ℤ} {hn : ℕ → ℕ} {J J' : Set (TriadicCube d)}
    (h : J ⊆ J') : whitneyNeighborhood m hn J ⊆ whitneyNeighborhood m hn J' :=
  fun _ hQ => ⟨hQ.1, hQ.2.imp fun _ hR => ⟨h hR.1, hR.2⟩⟩

/-! ## The per-component window -/

/-- **The anchor layer of a component**: the least Whitney layer met by the
component's *touching neighborhood* — not by the component itself.  The
component's common coarse mesh is `simplexScale m hn (componentWindowLayer m hn
C)`. -/
def componentWindowLayer (m : ℤ) (hn : ℕ → ℕ) (C : Set (TriadicCube d)) : ℕ :=
  leastWhitneyLayer m hn (whitneyNeighborhood m hn C)

/-- The `Finset` presentation of `𝒩(C)` required by the mesh constructions. -/
private theorem window_mem {m : ℤ} {hn : ℕ → ℕ} {C : Set (TriadicCube d)}
    (hfin : (whitneyNeighborhood m hn C).Finite) (Q : TriadicCube d) :
    Q ∈ hfin.toFinset ↔ Q ∈ whitneyNeighborhood m hn C :=
  Set.Finite.mem_toFinset hfin

/-- The window hypothesis of `GlobalCompetitor.lean`, in the layer-index form it
asks for.  The conversion from the proved cluster-geometry form `R ∈ 𝒲(j) ∨ R ∈
𝒲(j+1)` is layer-index uniqueness, which needs only `Monotone hn`. -/
private theorem window_layer {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn)
    {C : Set (TriadicCube d)} (hfin : (whitneyNeighborhood m hn C).Finite)
    (hlayer : ∀ R ∈ whitneyNeighborhood m hn C,
      R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1)) :
    ∀ Q ∈ hfin.toFinset, ∀ n : ℕ, Q ∈ whitneyLayer m hn n →
      n = componentWindowLayer m hn C ∨ n = componentWindowLayer m hn C + 1 := by
  intro Q hQ n hQn
  rcases hlayer Q ((window_mem hfin Q).mp hQ) with h | h
  · exact Or.inl (whitneyLayer_index_unique hmono hQn h)
  · exact Or.inr (whitneyLayer_index_unique hmono hQn h)

/-- `Monotone hn` implies the `e.SW.def` transcription guard of
`SimplexPartition.lean`. -/
theorem step_of_monotone {hn : ℕ → ℕ} (hmono : Monotone hn) (k : ℕ) :
    hn k ≤ hn (k + 1) + 1 :=
  le_trans (hmono (Nat.le_succ k)) (Nat.le_succ _)

/-! ## The superposed competitor and its gradient field -/

/-- **The piecewise-constant gradient field of the superposition**, `p + Σ_𝒞
(∇ℓ̂_p^𝒞 − p)`.  As in `GlobalCompetitor.lean` this is a *defined* field; its
identification with a distributional gradient of `superposedCompetitor` is not
proved and is used nowhere. -/
def superposedCompetitorSlope (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d))
    (p : Vec d) : Vec d → Vec d := fun x =>
  p + ∑ᶠ C ∈ badComponents I,
    (globalCompetitorSlope m (simplexScale m hn (componentWindowLayer m hn C)) C p x - p)

/-- **The cell constant of the superposed field** on a cell of `SW(□_m)`, read
at the cell's interior point exactly as `globalCompetitorCellSlope` is. -/
def superposedCompetitorCellSlope (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d))
    (p : Vec d) (T : KuhnCell d) : Vec d :=
  superposedCompetitorSlope m hn I p (Multiscale.kuhnCellInteriorPoint T)

theorem superposedCompetitorCellSlope_eq_sum (m : ℤ) (hn : ℕ → ℕ)
    (I : Set (TriadicCube d)) (p : Vec d) (T : KuhnCell d) :
    superposedCompetitorCellSlope m hn I p T =
      p + ∑ᶠ C ∈ badComponents I,
        (globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) := rfl

/-! ## The `sum_of_a_decomp` clauses at the full bad family -/

/-- The three clauses of `GlobalCompetitor.lean` at one component, with the window
binder in the shape the proved cluster geometry delivers. -/
private theorem componentClauses [NeZero d] {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn)
    {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn)
    {C : Set (TriadicCube d)} (hC : C ∈ badComponents I)
    (hfin : (whitneyNeighborhood m hn C).Finite)
    (hlayer : ∀ R ∈ whitneyNeighborhood m hn C,
      R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (p : Vec d) {T : KuhnCell d} (hT : T ∈ simplexPartition m hn) :
    (∀ x ∈ T.openCarrier,
        globalCompetitorSlope m (simplexScale m hn (componentWindowLayer m hn C)) C p x =
          globalCompetitorCellSlope m
            (simplexScale m hn (componentWindowLayer m hn C)) C p T) ∧
      (Multiscale.whitneyCubeOf m hn T ∈ C →
        globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T = 0) ∧
      (Multiscale.whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn C →
        globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T = p) :=
  globalCompetitorSlope_eq_cellSlope (step_of_monotone hmono)
    (step_of_monotone hmono (componentWindowLayer m hn C + 1))
    ((badComponents_subset hC).trans hI) (window_mem hfin)
    (window_layer hmono hfin hlayer) p hT

/-- **The three `sum_of_a_decomp` clauses of the superposition, at one cell.**

* the field is constant on the open cell — every summand is, by the
  corresponding clause at its own component;
* the constant is `0` when the cell's Whitney cube `□` is **bad**: `□` belongs
  to exactly one component `𝒞₀`, whose correction contributes `0 − p`, while
  every other component has `□ ∉ 𝒩(𝒞)` by `notMem_whitneyNeighborhood_of_ne`
  and contributes `p − p = 0` — this is clause 1 of `e.hat.linear.properties`
  at the full family;
* the constant is `p` when `□` lies off `𝒩(ℐ)`: then `□ ∉ 𝒩(𝒞)` for every
  component, and every summand is `0` — clause 3.

No disjointness of collars, no overlap count and no finiteness of the component
family is used. -/
theorem superposedCompetitorSlope_eq_cellSlope [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    (hmono : Monotone hn) {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I, (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (p : Vec d) {T : KuhnCell d} (hT : T ∈ simplexPartition m hn) :
    (∀ x ∈ T.openCarrier,
        superposedCompetitorSlope m hn I p x = superposedCompetitorCellSlope m hn I p T) ∧
      (Multiscale.whitneyCubeOf m hn T ∈ I →
        superposedCompetitorCellSlope m hn I p T = 0) ∧
      (Multiscale.whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn I →
        superposedCompetitorCellSlope m hn I p T = p) := by
  classical
  have hclause : ∀ C ∈ badComponents I, _ := fun C hC =>
    componentClauses hmono hI hC (hwin C hC).1 (hwin C hC).2 p hT
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change p + ∑ᶠ C ∈ badComponents I, _ = p + ∑ᶠ C ∈ badComponents I, _
    refine congrArg (p + ·) (finsum_mem_congr rfl fun C hC => ?_)
    rw [(hclause C hC).1 x hx,
      (hclause C hC).1 _ (Multiscale.kuhnCellInteriorPoint_mem_openCarrier T)]
  · intro hR
    rw [superposedCompetitorCellSlope_eq_sum]
    have hsum : ∑ᶠ C ∈ badComponents I,
        (globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) = -p := by
      rw [finsum_mem_def,
        finsum_eq_single _ (badComponent I (Multiscale.whitneyCubeOf m hn T)) ?_]
      · rw [Set.indicator_of_mem (badComponent_mem_badComponents hR),
          (hclause _ (badComponent_mem_badComponents hR)).2.1 (self_mem_badComponent hR)]
        exact zero_sub p
      · intro C hne
        by_cases hCS : C ∈ badComponents I
        · rw [Set.indicator_of_mem hCS,
            (hclause C hCS).2.2 (notMem_whitneyNeighborhood_of_ne hCS hR hne)]
          exact sub_self p
        · exact Set.indicator_of_notMem hCS _
    rw [hsum]
    exact add_neg_cancel p
  · intro hR
    rw [superposedCompetitorCellSlope_eq_sum]
    have hsum : ∑ᶠ C ∈ badComponents I,
        (globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) = 0 := by
      refine finsum_mem_of_eqOn_zero fun C hC => ?_
      change globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p = 0
      rw [(hclause C hC).2.2 fun hmem =>
        hR (whitneyNeighborhood_mono (badComponents_subset hC) hmem)]
      exact sub_self p
    rw [hsum]
    exact add_zero p

/-- **The deliverable in the consumer's own binder shape.**  At the manuscript's
bad family `ℐ = badFamily M m h_n omega` and over the subtype
`↥(simplexPartition m hn)`, these are literally the `hFc`, `hbadF` and `hoffF`
hypotheses of `Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean)
(and, at `q`, its `hGc`, `hbadG`, `hoffG`). -/
theorem superposedCompetitor_decomp_clauses_badFamily [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    (hmono : Monotone hn) (M : ABKModel d) (omega : Cutoff.CutoffSample d)
    (hwin : ∀ C ∈ badComponents (badFamily M m hn omega),
      (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (p : Vec d) :
    (∀ T : ↥(simplexPartition (d := d) m hn), ∀ x ∈ (T : KuhnCell d).openCarrier,
        superposedCompetitorSlope m hn (badFamily M m hn omega) p x =
          superposedCompetitorCellSlope m hn (badFamily M m hn omega) p (T : KuhnCell d)) ∧
      (∀ T : ↥(simplexPartition (d := d) m hn),
        Multiscale.whitneyCubeOf m hn (T : KuhnCell d) ∈ badFamily M m hn omega →
          superposedCompetitorCellSlope m hn (badFamily M m hn omega) p
            (T : KuhnCell d) = 0) ∧
      (∀ T : ↥(simplexPartition (d := d) m hn),
        Multiscale.whitneyCubeOf m hn (T : KuhnCell d) ∉
            whitneyNeighborhood m hn (badFamily M m hn omega) →
          superposedCompetitorCellSlope m hn (badFamily M m hn omega) p
            (T : KuhnCell d) = p) :=
  ⟨fun T => (superposedCompetitorSlope_eq_cellSlope hmono (fun _ hQ => hQ.1) hwin p T.2).1,
    fun T => (superposedCompetitorSlope_eq_cellSlope hmono (fun _ hQ => hQ.1) hwin p T.2).2.1,
    fun T => (superposedCompetitorSlope_eq_cellSlope hmono (fun _ hQ => hQ.1) hwin p T.2).2.2⟩

/-! ## The window binder is a theorem, not an assumption -/

/-- The binders are those of
`whitneyNeighborhood_finite_and_mem_leastLayer_or_succ`, forwarded unchanged. -/
theorem badComponents_window {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)}
    (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q) :
    ∀ C ∈ badComponents S,
      (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) C,
        R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀)
            (componentWindowLayer m (whitneyScaleSeq b hs k₀) C) ∨
          R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀)
            (componentWindowLayer m (whitneyScaleSeq b hs k₀) C + 1) := by
  rintro C ⟨Q₀, hQ₀, rfl⟩
  exact whitneyNeighborhood_finite_and_mem_leastLayer_or_succ hb0 hb hk₀ havoid hSsub
    hSbad hQ₀

/-- **Discharge of `hwin` at the manuscript's own bad family** `ℐ = badFamily M m
h_n omega`, with the avoidance binder supplied by the proved
`e.diameter.deterministic`. -/
theorem badComponents_window_badFamily {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) :
    ∀ C ∈ badComponents
        (badFamily M m (whitneyScale M m E b k₀ omega) omega),
      (whitneyNeighborhood m (whitneyScale M m E b k₀ omega) C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m (whitneyScale M m E b k₀ omega) C,
        R ∈ whitneyLayer m (whitneyScale M m E b k₀ omega)
            (componentWindowLayer m (whitneyScale M m E b k₀ omega) C) ∨
          R ∈ whitneyLayer m (whitneyScale M m E b k₀ omega)
            (componentWindowLayer m (whitneyScale M m E b k₀ omega) C + 1) := by
  rintro C ⟨Q₀, hQ₀, rfl⟩
  exact badFamily_whitneyNeighborhood_finite_and_mem_leastLayer_or_succ hb0 hb hk₀ hne hQ₀

end

end Algsuperdiff.Section3.Provider.Affine
