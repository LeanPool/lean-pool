/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalSuperposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.CollarMass

/-!
# ActiveFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The active family `𝒜_R`, its multiplicity bound, and the superposed competitor

`GlobalSuperposition.lean` builds the multi-component competitor `ℓ̂_p = ℓ_p +
Σ_𝒞 (ℓ̂_p^𝒞 − ℓ_p)` and proves the three `sum_of_a_decomp` clauses for its
*field*, with **no** finiteness of the component family.  Its Scope section
names the gap that this module fills:

* **the active family is finite**, with a cardinality bounded by a dimensional
  constant `M(d)`, uniformly in the Whitney cube.

## The active family and the constant

For a Whitney cube `R` writes

> `𝒜_R := {𝒞 : R ∈ 𝒩(𝒞)}`

which is `activeComponents m hn ℐ R` below (the components of `ℐ` whose
touching collar contains `R`).  Here it is

```
M(d) = 3 · 11^d ,
```

`3` for the three layers `n−1, n, n+1` a cube touching a layer-`n` cube can
occupy (`BoundaryDistance.whitneyLayer_index_close_of_cubeTouch`, the adjacency
clause alone) and `11^d` for the per-layer packing at the **cubewise** touch
relation of `e.neighborhood.def`
(`Multiscale.CollarMass.card_le_eleven_pow_of_forall_cubeTouch`), the two
generations of scale slack being's `±2` depth window
(`Multiscale.CollarMass.layerDepth_sub_le_two`).

## Inactive components and the cell slope

The active family is what the superposed cell constants actually see.  The
Whitney cubes touching one Whitney cube form a finite family
(`finite_setOf_mem_whitneyPartition_cubeTouch`), each of them activating at most
`M(d)` components; and a component that is *inactive* at the Whitney cube `Q`
carrying a cell `T` — one whose touching collar misses `Q` — leaves the
competitor's cell constant on `T` equal to the ambient `p`, so it contributes
nothing to the sum of `superposedCompetitorCellSlope_eq_sum`.  That is
`globalCompetitorCellSlope_eq_of_notMem_activeComponents`, proved from the
predecessor's `globalCompetitorSlope_eq_cellSlope`.  Together with the
multiplicity bound it caps at `M(d)` the number of summands that can be nonzero
on any single cell.

## Scope: what this module does NOT do

* **No gradient estimate.**'s summed bound `|∇ℓ̂_p − p| ≤ C(d)|p| Σ_{𝒞 ∈ 𝒜_R}
  diam(𝒞)/ρ_𝒞` is **read and not consumed**: no diameter, no interpolation
  scale `ρ_𝒞` and no constant `C(d)` occurs below.  This module supplies the
  two inputs that estimate needs and nothing else — the finite index set `𝒜_R`
  over which the sum runs, and `|𝒜_R| ≤ M(d)` for the squared/Cauchy--Schwarz
  form.
* **No weak gradient, no `H¹₀`.**  The cell constants read below are those of
  the *defined* piecewise-constant field `superposedCompetitorCellSlope`, and
  nothing identifies them with a distributional gradient; no a.e. statement, no
  `MemVectorL2`, no `H10Function` and no zero-trace statement occurs.
  `e.hat.linear.1` and the `hF`/`hG` binders of `Multiscale.sum_of_a_decomp`
  remain untouched.
* **No continuity and no compact support.**  The counting below is confined to
  the **open** root cube, and that is sharp for this route: the Whitney cubes
  accumulate at `∂□_m`, so the finiteness argument has no analogue there.  As
  the predecessor recorded, compact support must come from the
  cutoff/truncation, not from the collar.
* **No disjointness of collars** is asserted or used, exactly as in
  `GlobalSuperposition.lean`; the overlap is counted, not removed.  Merging
  overlapping components is *not* attempted — rules it unsafe.
* **No three-layer window**  and no face-to-face property of `SW(□_m)`  is
  used.

## References

* ABK26, (`𝒲(□_m)`, `e.W.n.def`, the boundary distance), (`ℐ`,
  `e.neighborhood.def`), (the components), (the adjacency clause),
  (`e.SW.def`), (`l.piecewise.affine.approx`, `e.hat.linear.properties`), (the
  false disjointness), (Step 1, "well-defined and continuous"), (the gradient
  estimate — not consumed), (`ℓ_e`).
* Two ideas were taken: bound the touching cubes layerwise over `Icc (n-1)
  (n+1)` and sum the per-layer packing; and choose one bad cube per active
  component, recovering the component from it for injectivity.  Everything is
  restated at this repository's carriers (`CubeTouch`, `whitneyNeighborhood`,
  `badComponent`, `KuhnCell`, `globalCompetitor`) and reproved from this
  repository's proved inputs.

## Main results

* `card_le_three_mul_eleven_pow_of_forall_cubeTouch`,
  `finite_setOf_mem_whitneyPartition_cubeTouch` — the Whitney cubes touching one
  Whitney cube, counted and bounded.
* `activeComponents`, `activeComponents_finite`,
  `card_le_multiplicityBound_of_forall_mem_activeComponents` — **the deliverable
  `|𝒜_R| ≤ M(d) = 3·11^d`**, the bound being `multiplicityBound d = 3·11^d`.
* `globalCompetitorCellSlope_eq_of_notMem_activeComponents` — a component that
  is inactive at the Whitney cube of a cell leaves the competitor's slope on
  that cell equal to `p`.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The Whitney cubes touching one Whitney cube -/

/-- **The three-layer window of the touch relation.**  A Whitney cube touching a
layer-`n` cube occupies one of the layers `n-1`, `n`, `n+1` — the adjacency
clause, which consequence 2 needs no percolation input and no largeness of
`k₀`, only `h_n ≥ 1`. -/
theorem mem_Icc_of_cubeTouch_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ}
    (hn1 : ∀ j, 1 ≤ hn j) {n k : ℕ} {Q R : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn k) (hR : R ∈ whitneyLayer m hn n)
    (htouch : CubeTouch Q R) : k ∈ Finset.Icc (n - 1) (n + 1) := by
  have h := whitneyLayer_index_close_of_cubeTouch hn1 hQ hR htouch
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- **Only finitely many Whitney cubes touch one Whitney cube.**  They are
confined to three layers, and each layer is a `Finset`. -/
theorem finite_setOf_mem_whitneyPartition_cubeTouch {m : ℤ} {hn : ℕ → ℕ}
    (hn1 : ∀ j, 1 ≤ hn j) {n : ℕ} {R : TriadicCube d} (hR : R ∈ whitneyLayer m hn n) :
    {Q : TriadicCube d | Q ∈ whitneyPartition m hn ∧ CubeTouch Q R}.Finite := by
  refine Set.Finite.subset
    ((Finset.Icc (n - 1) (n + 1)).biUnion (whitneyLayer (d := d) m hn)).finite_toSet ?_
  rintro Q ⟨⟨k, hQk⟩, htouch⟩
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2
    ⟨k, mem_Icc_of_cubeTouch_of_mem_whitneyLayer hn1 hQk hR htouch, hQk⟩)

/-- **The dimension-only count of the touching cubes**: at most `3·11^d` Whitney
cubes touch a fixed Whitney cube.  `3` is the layer window and `11^d` is the
proved per-layer packing at the cubewise touch relation
(`Multiscale.card_le_eleven_pow_of_forall_cubeTouch`), applicable because's
`±2` depth window (`Multiscale.layerDepth_sub_le_two`) puts the three layers
within two generations of one another. -/
theorem card_le_three_mul_eleven_pow_of_forall_cubeTouch {m : ℤ} {hn : ℕ → ℕ}
    (hn1 : ∀ j, 1 ≤ hn j) (hmono : Monotone hn) (hgap : ∀ j, hn (j + 1) ≤ hn j + 1)
    {n : ℕ} {R : TriadicCube d} (hR : R ∈ whitneyLayer m hn n)
    {A : Finset (TriadicCube d)}
    (hA : ∀ Q ∈ A, Q ∈ whitneyPartition m hn ∧ CubeTouch Q R) :
    A.card ≤ 3 * 11 ^ d := by
  classical
  have hRscale : R.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hR
  have hsub : A ⊆ (Finset.Icc (n - 1) (n + 1)).biUnion
      (fun k => A.filter (fun Q => Q ∈ whitneyLayer m hn k)) := by
    intro Q hQ
    obtain ⟨⟨k, hQk⟩, htouch⟩ := hA Q hQ
    exact Finset.mem_biUnion.2 ⟨k, mem_Icc_of_cubeTouch_of_mem_whitneyLayer hn1 hQk hR htouch,
      Finset.mem_filter.2 ⟨hQ, hQk⟩⟩
  have hlayer : ∀ k ∈ Finset.Icc (n - 1) (n + 1),
      (A.filter (fun Q => Q ∈ whitneyLayer m hn k)).card ≤ 11 ^ d := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hwin := (Multiscale.layerDepth_sub_le_two hmono hgap (n := n) (j := k)
      (by omega) (by omega)).2
    refine Multiscale.card_le_eleven_pow_of_forall_cubeTouch
      (sQ := m - (k : ℤ) - (hn k : ℤ)) (by rw [hRscale]; omega) ?_
    intro Q hQ
    obtain ⟨hQA, hQk⟩ := Finset.mem_filter.mp hQ
    exact ⟨scale_eq_of_mem_whitneyLayer hQk, (hA Q hQA).2⟩
  calc A.card ≤ ((Finset.Icc (n - 1) (n + 1)).biUnion
        (fun k => A.filter (fun Q => Q ∈ whitneyLayer m hn k))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc (n - 1) (n + 1),
        (A.filter (fun Q => Q ∈ whitneyLayer m hn k)).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.Icc (n - 1) (n + 1), 11 ^ d := Finset.sum_le_sum hlayer
    _ ≤ 3 * 11 ^ d := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
        exact Nat.mul_le_mul_right _ (by omega)

/-! ## The active family `𝒜_R` -/

/-- **The multiplicity constant `M(d)`**, `M(d) = 3·11^d`: three layers times the
cubewise per-layer packing. -/
def multiplicityBound (d : ℕ) : ℕ := 3 * 11 ^ d

/-- **The active family `𝒜_R = {𝒞 : R ∈ 𝒩(𝒞)}`**: the components of the bad family
whose touching collar contains the Whitney cube `R`.  These are exactly the
components whose correction can be nonzero on `R`. -/
def activeComponents (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d))
    (R : TriadicCube d) : Set (Set (TriadicCube d)) :=
  {C | C ∈ badComponents I ∧ R ∈ whitneyNeighborhood m hn C}

theorem mem_activeComponents_iff {m : ℤ} {hn : ℕ → ℕ} {I : Set (TriadicCube d)}
    {R : TriadicCube d} {C : Set (TriadicCube d)} :
    C ∈ activeComponents m hn I R ↔
      C ∈ badComponents I ∧ R ∈ whitneyNeighborhood m hn C := Iff.rfl

/-- **An active component is recovered from any of its bad cubes touching `R`.**
This is the maximality fact isolates, in the form that makes the counting
injective. -/
theorem exists_cubeTouch_and_eq_badComponent_of_mem_activeComponents {m : ℤ} {hn : ℕ → ℕ}
    {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn) {R : TriadicCube d}
    {C : Set (TriadicCube d)} (hC : C ∈ activeComponents m hn I R) :
    ∃ B : TriadicCube d, B ∈ whitneyPartition m hn ∧ CubeTouch B R ∧
      C = badComponent I B := by
  obtain ⟨⟨Q₀, hQ₀, rfl⟩, -, B, hBC, htouch⟩ := hC
  exact ⟨B, hI hBC.1, htouch.symm, badComponent_eq_of_badChain hBC.2⟩

open Classical in
/-- The chosen bad cube of an active component, touching `R`. -/
def witnessCube (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d))
    (R : TriadicCube d) (C : Set (TriadicCube d)) : TriadicCube d :=
  if h : ∃ B : TriadicCube d, B ∈ whitneyPartition m hn ∧ CubeTouch B R ∧
      C = badComponent I B then h.choose else R

private theorem witnessCube_spec {m : ℤ} {hn : ℕ → ℕ} {I : Set (TriadicCube d)}
    (hI : I ⊆ whitneyPartition m hn) {R : TriadicCube d} {C : Set (TriadicCube d)}
    (hC : C ∈ activeComponents m hn I R) :
    witnessCube m hn I R C ∈ whitneyPartition m hn ∧
      CubeTouch (witnessCube m hn I R C) R ∧
      C = badComponent I (witnessCube m hn I R C) := by
  classical
  have h := exists_cubeTouch_and_eq_badComponent_of_mem_activeComponents hI hC
  have he : witnessCube m hn I R C = h.choose := dite_eq_left h
  rw [he]
  exact h.choose_spec

private theorem witnessCube_injOn {m : ℤ} {hn : ℕ → ℕ} {I : Set (TriadicCube d)}
    (hI : I ⊆ whitneyPartition m hn) {R : TriadicCube d} :
    Set.InjOn (witnessCube m hn I R) (activeComponents m hn I R) := by
  intro C hC C' hC' heq
  rw [(witnessCube_spec hI hC).2.2, (witnessCube_spec hI hC').2.2, heq]

/-- **Finiteness of the active family** — the input `GlobalSuperposition.lean`
names as the operative obstruction to continuity and per-cell affineness. -/
theorem activeComponents_finite {m : ℤ} {hn : ℕ → ℕ} (hn1 : ∀ j, 1 ≤ hn j)
    {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn) {n : ℕ}
    {R : TriadicCube d} (hR : R ∈ whitneyLayer m hn n) :
    (activeComponents m hn I R).Finite := by
  refine Set.Finite.of_finite_image
    (f := witnessCube m hn I R) ?_ (witnessCube_injOn hI)
  refine (finite_setOf_mem_whitneyPartition_cubeTouch hn1 hR).subset ?_
  rintro B ⟨C, hC, rfl⟩
  exact ⟨(witnessCube_spec hI hC).1, (witnessCube_spec hI hC).2.1⟩

/-- **The multiplicity bound, `Finset` form.**  Every finite family of components
active at `R` has at most `M(d)` members. -/
theorem card_le_multiplicityBound_of_forall_mem_activeComponents {m : ℤ} {hn : ℕ → ℕ}
    (hn1 : ∀ j, 1 ≤ hn j) (hmono : Monotone hn) (hgap : ∀ j, hn (j + 1) ≤ hn j + 1)
    {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn) {n : ℕ}
    {R : TriadicCube d} (hR : R ∈ whitneyLayer m hn n)
    {A : Finset (Set (TriadicCube d))} (hA : ∀ C ∈ A, C ∈ activeComponents m hn I R) :
    A.card ≤ multiplicityBound d := by
  classical
  have hTfin : {Q : TriadicCube d | Q ∈ whitneyPartition m hn ∧ CubeTouch Q R}.Finite :=
    finite_setOf_mem_whitneyPartition_cubeTouch hn1 hR
  refine le_trans (Finset.card_le_card_of_injOn (witnessCube m hn I R)
    (fun C hC => (Set.Finite.mem_toFinset hTfin).mpr
      ⟨(witnessCube_spec hI (hA C hC)).1, (witnessCube_spec hI (hA C hC)).2.1⟩)
    ((witnessCube_injOn hI).mono fun C hC => hA C (Finset.mem_coe.mp hC))) ?_
  exact card_le_three_mul_eleven_pow_of_forall_cubeTouch hn1 hmono hgap hR
    fun Q hQ => (Set.Finite.mem_toFinset hTfin).mp hQ

/-! ## Inactive components contribute nothing -/

/-- The window binder of `GlobalCompetitor.lean`, in the layer-index form it asks
for; the conversion from the proved cluster-geometry form is layer-index
uniqueness. -/
private theorem window_layer' {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn)
    {C : Set (TriadicCube d)} (hfin : (whitneyNeighborhood m hn C).Finite)
    (hlayer : ∀ R ∈ whitneyNeighborhood m hn C,
      R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1)) :
    ∀ Q ∈ hfin.toFinset, ∀ n : ℕ, Q ∈ whitneyLayer m hn n →
      n = componentWindowLayer m hn C ∨ n = componentWindowLayer m hn C + 1 := by
  intro Q hQ n hQn
  rcases hlayer Q ((Set.Finite.mem_toFinset hfin).mp hQ) with h | h
  · exact Or.inl (whitneyLayer_index_unique hmono hQn h)
  · exact Or.inr (whitneyLayer_index_unique hmono hQn h)

/-- **A component inactive at the cell's Whitney cube has cell constant `p`** —
clause 3 of `e.hat.linear.properties` read at the active family. -/
theorem globalCompetitorCellSlope_eq_of_notMem_activeComponents [NeZero d]
    {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn) {I : Set (TriadicCube d)}
    (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I, (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (p : Vec d) {n : ℕ} {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n)
    {T : KuhnCell d} (hT : T ∈ whitneySimplexCells m hn n Q)
    {C : Set (TriadicCube d)} (hC : C ∈ badComponents I)
    (hCQ : C ∉ activeComponents m hn I Q) :
    globalCompetitorCellSlope m (simplexScale m hn (componentWindowLayer m hn C)) C p T = p := by
  refine (globalCompetitorSlope_eq_cellSlope (step_of_monotone hmono)
    (step_of_monotone hmono (componentWindowLayer m hn C + 1))
    ((badComponents_subset hC).trans hI)
    (fun _ => Set.Finite.mem_toFinset (hwin C hC).1)
    (window_layer' hmono (hwin C hC).1 (hwin C hC).2) p
    (mem_simplexPartition_of_mem_whitneySimplexCells hQ hT)).2.2 ?_
  rw [Multiscale.whitneyCubeOf_of_mem_whitneySimplexCells hQ hT]
  exact fun hmem => hCQ (mem_activeComponents_iff.mpr ⟨hC, hmem⟩)

end

end Algsuperdiff.Section3.Provider.Affine
