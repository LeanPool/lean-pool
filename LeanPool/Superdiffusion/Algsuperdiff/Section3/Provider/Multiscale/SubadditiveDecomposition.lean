/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SimplexDomains
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.SubadditivityCountable

/-!
# SubadditiveDecomposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional trimming kernel for the subadditive decomposition

It does **not** by itself realize or close that step of `p.bfA.multiscalebound`:
its main theorem keeps the competitor fields and their structural clauses as
explicit premises.
The target display is `e.sum-of-a-decomp` of ABK26:

```
| 𝐀hom_{n-1}^{-1/2} P . 𝐀_L(□_n) 𝐀hom_{n-1}^{-1/2} P |
  ≤ ∑_{𝔰 ∈ 𝒮𝒲(□_n)} (|𝔰|/|□_n|) | 𝐀_L^{1/2}(𝔰) 𝐀hom_{n-1}^{-1/2} P |² 1_{¬𝓑(𝔰)}
  + ∑_{𝔰 ∈ 𝒮𝒲(□_n)} (|𝔰|/|□_n|)
        | 𝐀_L^{1/2}(𝔰) 𝐀hom_{n-1}^{-1/2} (∇ℓ̂_p(𝔰), (∇·D̂_q)(𝔰)) |²
        1_{¬𝓑(𝔰)} 1_{𝔰 ∈ 𝒩(ℐ)} .
```

## The route (/: varying slope, never `csInf_le`)

The engine is the **per-cell varying-slope** gluing of `l.subadd.betterer`,
proved in `Provider/Whitney/SubadditivityCountable.lean`
(`ofReal_bfA_quadratic_le_simplex_weighted_tsum`): exact cell minimizers at the
cell's own slope `(∇ℓ̂_p(𝔰), ∇·D̂_q(𝔰))` are pasted into a single admissible
competitor by zero-extension of their `L²_pot,0`/`L²_sol,0` corrections.  Every
term of the right-hand side below is therefore a genuine **coarse-grained**
`𝐀_L(𝔰)` quadratic form, which is what bounds.

This module supplies the two things the gluing lemma still needs at the
manuscript's own partition, and then performs the manuscript's *trimming*:

1. the cells of `SW(□_m)` as a countable family of Chapter 2 domains covering
   the root cube up to a null set (`SimplexDomains.lean`);
2. the split of the resulting single sum into the two printed sums, using the
   two structural clauses of `e.hat.linear.properties`.

## The load is a general block vector

The manuscript's left-hand side is loaded at `𝐀hom_{n-1}^{-1/2} P` and every
right-hand cell term at `𝐀hom_{n-1}^{-1/2} P̂(𝔰)`.  By `e.homs.defs.U.diag` (
an verified node) `𝐀hom_{n-1}` is block diagonal with scalar blocks,
`𝐀hom_{n-1}^{-1/2} (p,q) = (σ_{n-1}^{-1/2} p, σ_{n-1}^{1/2} q)`, and the two
legs are rescaled independently.  Since `L²_pot,0` and `L²_sol,0` are linear
spaces, the frame commutes with every hypothesis and with every conclusion
below.  The theorem is therefore stated at a **general** load `(p, q)` and a
general competitor pair; the manuscript's display is the instantiation

```
p ↦ σ_{n-1}^{-1/2} p ,  q ↦ σ_{n-1}^{1/2} q ,
F ↦ σ_{n-1}^{-1/2} ∇ℓ̂_p ,  G ↦ σ_{n-1}^{1/2} ∇·D̂_q .
```

This is strictly more general than the printed display; nothing is assumed
about `𝐀hom`.

## The competitor is an explicit local interface

The theorem in this low-level module is deliberately generic in the competitor
pair.  It therefore carries the relevant conclusions of
`l.piecewise.affine.approx` as explicit hypotheses, in the exact shape
`e.hat.linear.properties` delivers and at the same carrier at which
`l.subadd.betterer` already reads it (the two *fields* `F = ∇ℓ̂_p` and `G =
∇·D̂_q`, see `SubadditivityBetter.lean`):

* `hF`, `hG`: `e.hat.linear.1` and `e.hat.D.bc`, each read at its label and
  content;
* `hFc`, `hGc`: `e.hat.linear.2`, the subordination of the competitor to
  `SW(□_m)`, with `Fc`/`Gc` the manuscript's own notation `∇ℓ̂_p(𝔰)`,
  `∇·D̂_q(𝔰)`;
* `hbadF`, `hbadG`: clause 1 of `e.hat.linear.properties`, `∇ℓ̂_p = 0` in every
  `□ ∈ ℐ`;
* `hoffF`, `hoffG`: clause 3 of `e.hat.linear.properties` ((clause 3; the
  cases-end line asserts nothing —, format)), `∇ℓ̂_p = p` in every `𝔰 ∈ SW(□_m)
  ∖ 𝒩(ℐ)`.

Clauses 1 and 3 are printed for the potential leg only.  Their algebraic
transfer to the solenoidal leg is recorded below as
`hatDDivergenceValue_zero` and `hatDDivergenceValue_id`, but the generic theorem
`sum_of_a_decomp` still takes `hbadG` and `hoffG` explicitly because its
abstract field `G` is not definitionally `hatDDivergenceValue`.  The concrete
superposed route later discharges these premises.  Clause 2 of
`e.hat.linear.properties` (the collar gradient bound) is **not** used by this
node — it is spent by `#conclusion` through `r.gradient.bound.simplified` — and
is not assumed.

## The node's inputs, and where each is consumed

* `d.whitney.bad-set.definitions` and `d.simplex.partition` are consumed
  directly: `simplexPartition`, `whitneyPartition`, `badFamily`,
  `whitneyNeighborhood`, and the exactness/disjointness theorems of the proved
  Whitney layer.
* `l.subadd.betterer` is consumed directly, in its countable `[0,∞]` form.
* `l.bad.clusters.geometry` is *not* consumed by `sum_of_a_decomp` itself.  In
  the manuscript it checks the hypotheses of `l.piecewise.affine.approx` ("each
  `𝒞_j` satisfies the hypotheses of Lemma.").  Its proved geometry feeds the
  downstream affine/superposition construction, which now supplies the concrete
  cellwise clauses; none of that downstream discharge is credited to this
  conditional kernel.

## Scope notes

* No face-to-face or simplicial-complex property of `SW(□_m)` is used: the
  gluing pastes *measurable* `L²` corrections supported in single cells, never
  continuous ones, so no cross-cell compatibility is needed.  The two-layer
  common-coarse property --- that cells of adjacent layers sit in a common
  coarse simplex --- is an obligation of `l.piecewise.affine.approx`, not of
  this node, and nothing below needs it.
* concern Steps 3 of `p.bfA.multiscalebound`; they touch the *consumption* of
  this display, not its derivation, and nothing below depends on them.

## References

* ABK26, (`e.sum-of-a-decomp`),  (`e.hat.linear.1`, `e.hatdq`, `e.hat.D.bc`),
  (`l.piecewise.affine.approx`), (`e.homs.defs.U.diag`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## `e.hatdq`: the solenoidal leg of the two structural clauses

`(D̂_q)_{ij} = (d-1)^{-1} (q_j ℓ̂_{e_i} - q_i ℓ̂_{e_j})` and `(∇ · A)_j = ∑_i
∂_{x_i} A_{ij}` (footnote), so on a cell where every `∇ℓ̂_{e_k}` is the
constant vector `A k`,

`(∇ · D̂_q)_j = (d-1)^{-1} ∑_i (q_j (A i) i - q_i (A j) i)`.

The two clauses of `e.hat.linear.properties` used by this node fix `A`
completely — `A = 0` inside a bad cube, `A k = e_k` off the collar — so the
solenoidal leg is determined, and no separate hypothesis about `∇ · D̂_q` is
needed. -/


/-! ## The Whitney cube containing a cell of `SW(□_m)` -/

theorem carrier_nonempty (T : KuhnCell d) : T.carrier.Nonempty :=
  ⟨kuhnCellInteriorPoint T,
    T.openCarrier_subset_carrier (kuhnCellInteriorPoint_mem_openCarrier T)⟩

theorem exists_whitneyCube_of_mem_simplexPartition {m : ℤ} {hn : ℕ → ℕ}
    {T : KuhnCell d} (hT : T ∈ simplexPartition m hn) :
    ∃ Q, Q ∈ whitneyPartition m hn ∧ T.carrier ⊆ cubeSet Q := by
  obtain ⟨n, Q, hQ, hTQ⟩ := hT
  exact ⟨Q, ⟨n, hQ⟩, carrier_subset_cubeSet_of_mem_whitneySimplexCells hTQ⟩

open Classical in
/-- **"the cube `□ ∈ 𝒲(□_m)` containing `𝔰`"**.  The Whitney cubes are pairwise
disjoint and a cell has nonempty carrier, so this cube is unique
(`whitneyCubeOf_eq`); the value off `SW(□_m)` is irrelevant and is pinned to
the cell's own support cube. -/
def whitneyCubeOf (m : ℤ) (hn : ℕ → ℕ) (T : KuhnCell d) : TriadicCube d :=
  if h : ∃ Q, Q ∈ whitneyPartition m hn ∧ T.carrier ⊆ cubeSet Q then h.choose
  else T.supportCube

theorem whitneyCubeOf_mem {m : ℤ} {hn : ℕ → ℕ} {T : KuhnCell d}
    (hT : T ∈ simplexPartition m hn) :
    whitneyCubeOf m hn T ∈ whitneyPartition m hn := by
  classical
  rw [whitneyCubeOf, dite_eq_left (exists_whitneyCube_of_mem_simplexPartition hT)]
  exact (exists_whitneyCube_of_mem_simplexPartition hT).choose_spec.1

theorem carrier_subset_whitneyCubeOf {m : ℤ} {hn : ℕ → ℕ} {T : KuhnCell d}
    (hT : T ∈ simplexPartition m hn) :
    T.carrier ⊆ cubeSet (whitneyCubeOf m hn T) := by
  classical
  rw [whitneyCubeOf, dite_eq_left (exists_whitneyCube_of_mem_simplexPartition hT)]
  exact (exists_whitneyCube_of_mem_simplexPartition hT).choose_spec.2

/-- Uniqueness of the containing cube. -/
theorem whitneyCubeOf_eq {m : ℤ} {hn : ℕ → ℕ} {T : KuhnCell d}
    (hT : T ∈ simplexPartition m hn) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyPartition m hn) (hTQ : T.carrier ⊆ cubeSet Q) :
    whitneyCubeOf m hn T = Q := by
  by_contra hne
  obtain ⟨x, hx⟩ := carrier_nonempty T
  exact Set.disjoint_left.mp
    (disjoint_cubeSet_of_mem_whitneyPartition (whitneyCubeOf_mem hT) hQ hne)
    (carrier_subset_whitneyCubeOf hT hx) (hTQ hx)

/-- The containing cube of a cell produced by the layer-`n` decomposition of a
layer-`n` Whitney cube is that cube. -/
theorem whitneyCubeOf_of_mem_whitneySimplexCells {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m hn n Q) : whitneyCubeOf m hn T = Q :=
  whitneyCubeOf_eq (mem_simplexPartition_of_mem_whitneySimplexCells hQ hT) ⟨n, hQ⟩
    (carrier_subset_cubeSet_of_mem_whitneySimplexCells hT)

/-! ## The two indicators of `e.sum-of-a-decomp` -/

open Classical in
/-- `1_{¬𝓑(𝔰)}`: the bad event of the Whitney cube containing the cell does not
occur. -/
def notBadIndicator (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (omega : Algsuperdiff.Section3.Cutoff.CutoffSample d) (T : KuhnCell d) : ℝ :=
  if whitneyCubeOf m hn T ∈ badFamily M m hn omega then 0 else 1

open Classical in
/-- `1_{𝔰 ∈ 𝒩(ℐ)}`: the Whitney cube containing the cell lies in the neighborhood
of the bad family. -/
def collarIndicator (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (omega : Algsuperdiff.Section3.Cutoff.CutoffSample d) (T : KuhnCell d) : ℝ :=
  if whitneyCubeOf m hn T ∈ whitneyNeighborhood m hn (badFamily M m hn omega) then 1
  else 0

theorem notBadIndicator_of_bad {M : ABKModel d} {m : ℤ} {hn : ℕ → ℕ}
    {omega : Algsuperdiff.Section3.Cutoff.CutoffSample d} {T : KuhnCell d}
    (h : whitneyCubeOf m hn T ∈ badFamily M m hn omega) :
    notBadIndicator M m hn omega T = 0 := by
  classical
  rw [notBadIndicator, ite_eq_left h]

theorem notBadIndicator_of_not_bad {M : ABKModel d} {m : ℤ} {hn : ℕ → ℕ}
    {omega : Algsuperdiff.Section3.Cutoff.CutoffSample d} {T : KuhnCell d}
    (h : whitneyCubeOf m hn T ∉ badFamily M m hn omega) :
    notBadIndicator M m hn omega T = 1 := by
  classical
  rw [notBadIndicator, ite_eq_right h]

theorem collarIndicator_of_mem {M : ABKModel d} {m : ℤ} {hn : ℕ → ℕ}
    {omega : Algsuperdiff.Section3.Cutoff.CutoffSample d} {T : KuhnCell d}
    (h : whitneyCubeOf m hn T ∈ whitneyNeighborhood m hn (badFamily M m hn omega)) :
    collarIndicator M m hn omega T = 1 := by
  classical
  rw [collarIndicator, ite_eq_left h]

theorem collarIndicator_of_notMem {M : ABKModel d} {m : ℤ} {hn : ℕ → ℕ}
    {omega : Algsuperdiff.Section3.Cutoff.CutoffSample d} {T : KuhnCell d}
    (h : whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn (badFamily M m hn omega)) :
    collarIndicator M m hn omega T = 0 := by
  classical
  rw [collarIndicator, ite_eq_right h]

/-! ## `SW(□_m)` as an admissible dissection -/

/-- The weight `|𝔰| / |□_m|` of `e.sum-of-a-decomp`. -/
def cellWeight (m : ℤ) (T : KuhnCell d) : ℝ :=
  (volume T.openCarrier).toReal /
    (volume (openCubeSet (originCube d m))).toReal

variable [NeZero d]

theorem openCarrier_subset_openCubeSet_originCube {m : ℤ} {hn : ℕ → ℕ}
    (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1) {T : KuhnCell d}
    (hT : T ∈ simplexPartition m hn) :
    T.openCarrier ⊆ openCubeSet (originCube d m) := by
  intro x hx
  rw [← iUnion_carrier_simplexPartition_eq_openCubeSet (d := d) (m := m) (hn := hn) hstep]
  exact Set.mem_iUnion.mpr
    ⟨T, Set.mem_iUnion.mpr ⟨hT, T.openCarrier_subset_carrier hx⟩⟩

/-! ## The conditional trimming statement -/

/-- **`e.sum-of-a-decomp`, the trimmed simplex decomposition.**

For the simplex partition `SW(□_m)`, a competitor pair `(F, G)` admissible for
the load `(p, q)` on the open root cube, subordinate to `SW(□_m)` with cell
values `(Fc 𝔰, Gc 𝔰)`, vanishing on the cells of bad Whitney cubes and equal to
`(p, q)` on the cells off the collar `𝒩(ℐ)`,

```
| (p,q) . 𝐀(□_m) (p,q) |
  ≤ ∑'_{𝔰 ∈ SW(□_m)} (|𝔰|/|□_m|) ((p,q) . 𝐀(𝔰) (p,q)) 1_{¬𝓑(𝔰)}
  + ∑'_{𝔰 ∈ SW(□_m)} (|𝔰|/|□_m|)
        ((Fc 𝔰, Gc 𝔰) . 𝐀(𝔰) (Fc 𝔰, Gc 𝔰)) 1_{¬𝓑(𝔰)} 1_{𝔰 ∈ 𝒩(ℐ)}
```

as an inequality in `[0, ∞]`.  See the module docstring for the frame
instantiation `(p,q) ↦ 𝐀hom_{n-1}^{-1/2} P` recovering the printed display, and
for the conditional inventory of the `l.piecewise.affine.approx` binders. -/
theorem sum_of_a_decomp {m : ℤ} {hn : ℕ → ℕ}
    (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1)
    (M : ABKModel d) (omega : Algsuperdiff.Section3.Cutoff.CutoffSample d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
    (aS : ∀ T : ↥(simplexPartition (d := d) m hn),
      Book.Ch02.CoeffOn (kuhnCellDomain (T : KuhnCell d)))
    (haS : ∀ T, (aS T).toCoeffField = a.toCoeffField)
    (p q : Vec d) (F G : Vec d → Vec d)
    (Fc Gc : ↥(simplexPartition (d := d) m hn) → Vec d)
    (hF : Book.Ch01.PotentialZeroTraceFieldOn (openCubeSet (originCube d m))
      fun x => F x - p)
    (hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet (originCube d m))
      fun x => G x - q)
    (hFc : ∀ T : ↥(simplexPartition (d := d) m hn),
      ∀ x ∈ (T : KuhnCell d).openCarrier, F x = Fc T)
    (hGc : ∀ T : ↥(simplexPartition (d := d) m hn),
      ∀ x ∈ (T : KuhnCell d).openCarrier, G x = Gc T)
    (hbadF : ∀ T : ↥(simplexPartition (d := d) m hn),
      whitneyCubeOf m hn (T : KuhnCell d) ∈ badFamily M m hn omega → Fc T = 0)
    (hbadG : ∀ T : ↥(simplexPartition (d := d) m hn),
      whitneyCubeOf m hn (T : KuhnCell d) ∈ badFamily M m hn omega → Gc T = 0)
    (hoffF : ∀ T : ↥(simplexPartition (d := d) m hn),
      whitneyCubeOf m hn (T : KuhnCell d) ∉
        whitneyNeighborhood m hn (badFamily M m hn omega) → Fc T = p)
    (hoffG : ∀ T : ↥(simplexPartition (d := d) m hn),
      whitneyCubeOf m hn (T : KuhnCell d) ∉
        whitneyNeighborhood m hn (badFamily M m hn omega) → Gc T = q) :
    ENNReal.ofReal
        |blockVecDot (p, q)
          (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d m)) a)
            (p, q))| ≤
      (∑' T : ↥(simplexPartition (d := d) m hn), ENNReal.ofReal
          (cellWeight m (T : KuhnCell d) *
            blockVecDot (p, q)
              (blockMatVecMul
                (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                (p, q)) *
            notBadIndicator M m hn omega (T : KuhnCell d))) +
        ∑' T : ↥(simplexPartition (d := d) m hn), ENNReal.ofReal
          (cellWeight m (T : KuhnCell d) *
            blockVecDot (Fc T, Gc T)
              (blockMatVecMul
                (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                (Fc T, Gc T)) *
            notBadIndicator M m hn omega (T : KuhnCell d) *
            collarIndicator M m hn omega (T : KuhnCell d)) := by
  classical
  -- the dissection hypotheses for `l.subadd.betterer` at `SW(□_m)`
  have hsub : ∀ T : ↥(simplexPartition (d := d) m hn),
      ((kuhnCellDomain (T : KuhnCell d)) : Set (Vec d)) ⊆
        ((Book.Ch02.cubeDomain (originCube d m)) : Set (Vec d)) := fun T =>
    openCarrier_subset_openCubeSet_originCube hstep T.2
  have hdisj : Pairwise fun T U : ↥(simplexPartition (d := d) m hn) =>
      Disjoint ((kuhnCellDomain (T : KuhnCell d)) : Set (Vec d))
        ((kuhnCellDomain (U : KuhnCell d)) : Set (Vec d)) := by
    intro T U hTU
    exact ((simplexPartition_pairwiseDisjoint (d := d) (m := m) (hn := hn)) T.2 U.2
      (fun h => hTU (Subtype.ext h))).mono
      (T : KuhnCell d).openCarrier_subset_carrier
      (U : KuhnCell d).openCarrier_subset_carrier
  have hcover : volume (((Book.Ch02.cubeDomain (originCube d m)) : Set (Vec d)) \
      ⋃ T : ↥(simplexPartition (d := d) m hn),
        ((kuhnCellDomain (T : KuhnCell d)) : Set (Vec d))) = 0 := by
    have hU : (⋃ T : ↥(simplexPartition (d := d) m hn),
        ((kuhnCellDomain (T : KuhnCell d)) : Set (Vec d))) =
        ⋃ T ∈ simplexPartition (d := d) m hn, (T : KuhnCell d).openCarrier := by
      rw [Set.iUnion_subtype]
      rfl
    rw [Book.Ch02.cubeDomain_coe, hU]
    exact volume_openCubeSet_diff_iUnion_openCarrier hstep
  -- the varying-slope subadditivity of `l.subadd.betterer`
  have hmain := Whitney.ofReal_bfA_quadratic_le_simplex_weighted_tsum
    (ι := ↥(simplexPartition (d := d) m hn))
    (Q := Book.Ch02.cubeDomain (originCube d m))
    (S := fun T => kuhnCellDomain (T : KuhnCell d)) a aS haS hsub hdisj hcover
    p q F G Fc Gc hF hG hFc hGc
  -- the left-hand side is nonnegative, so the absolute value is inert
  have hnn : 0 ≤ blockVecDot (p, q)
      (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d m)) a) (p, q)) := by
    have h := Whitney.doubledMu_nonneg a (p, q)
    rw [(Book.Ch02.doubledMuTheory (Book.Ch02.cubeDomain (originCube d m)) a).mu_quadratic
      (p, q)] at h
    linarith
  rw [abs_of_nonneg hnn]
  -- termwise trimming by the two structural clauses of `e.hat.linear.properties`
  have hterm : ∀ T : ↥(simplexPartition (d := d) m hn),
      ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
          blockVecDot (Fc T, Gc T)
            (blockMatVecMul
              (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
              (Fc T, Gc T))) ≤
        ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            blockVecDot (p, q)
              (blockMatVecMul
                (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                (p, q)) *
            notBadIndicator M m hn omega (T : KuhnCell d)) +
          ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            blockVecDot (Fc T, Gc T)
              (blockMatVecMul
                (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                (Fc T, Gc T)) *
            notBadIndicator M m hn omega (T : KuhnCell d) *
            collarIndicator M m hn omega (T : KuhnCell d)) := by
    intro T
    by_cases hbad : whitneyCubeOf m hn (T : KuhnCell d) ∈ badFamily M m hn omega
    · -- bad cells: the competitor has zero slope there, so the term vanishes
      rw [hbadF T hbad, hbadG T hbad]
      have hz : blockVecDot ((0 : Vec d), (0 : Vec d))
          (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
            ((0 : Vec d), (0 : Vec d))) = 0 := by
        simp [blockVecDot, blockMatVecMul, vecDot]
      rw [hz]
      simp
    · by_cases hcol : whitneyCubeOf m hn (T : KuhnCell d) ∈
          whitneyNeighborhood m hn (badFamily M m hn omega)
      · -- good cells meeting the collar: the second sum already carries the term
        rw [notBadIndicator_of_not_bad hbad, collarIndicator_of_mem hcol]
        simp
      · -- good cells off the collar: the competitor has slope `(p, q)` there
        rw [notBadIndicator_of_not_bad hbad, hoffF T hcol, hoffG T hcol]
        simp
  calc
    ENNReal.ofReal (blockVecDot (p, q)
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d m)) a) (p, q)))
        ≤ ∑' T : ↥(simplexPartition (d := d) m hn), ENNReal.ofReal
            (cellWeight m (T : KuhnCell d) *
              blockVecDot (Fc T, Gc T)
                (blockMatVecMul
                  (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                  (Fc T, Gc T))) := hmain
    _ ≤ ∑' T : ↥(simplexPartition (d := d) m hn),
          (ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
              blockVecDot (p, q)
                (blockMatVecMul
                  (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                  (p, q)) *
              notBadIndicator M m hn omega (T : KuhnCell d)) +
            ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
              blockVecDot (Fc T, Gc T)
                (blockMatVecMul
                  (Book.Ch02.coarseBlockMatrix (kuhnCellDomain (T : KuhnCell d)) (aS T))
                  (Fc T, Gc T)) *
              notBadIndicator M m hn omega (T : KuhnCell d) *
              collarIndicator M m hn omega (T : KuhnCell d))) :=
        ENNReal.tsum_le_tsum hterm
    _ = _ := ENNReal.tsum_add

end

end Algsuperdiff.Section3.Provider.Multiscale
