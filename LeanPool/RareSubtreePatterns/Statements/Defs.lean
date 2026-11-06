/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Statement-level definitions

Every definition on which the statements of the four Introduction theorems depend: finite plane
trees, fringe subtrees and marked counts, Bienaymé laws and size conditioning, total variation,
the Łukasiewicz walk and hypothesis `(H_α)`, cutoffs and Assumptions (M), (S), (C), and the four
statement propositions (`PoissonApproximationStatement`, `PoissonApproximation2Statement`,
`MaxStringStatement`, `MaxLeafHeightStatement`), proved in `PoissonDeclumping.MainTheorems`.

These definitions originate in the upstream statement contract. The phase refinement in
`TwoPointLocalization` is strengthened here to every nontrivial filter of admissible sizes,
so that it applies to phase-separated subsequences even when the full sequence approaches
integer phases. The remaining definitions retain the upstream statements.
-/

@[expose] public section

/-! ### Plane trees and fringe subtrees (lemmas: `PlaneTree/Basic.lean`) -/

namespace PoissonDeclumping

/-- A finite plane tree consists of a root and an ordered list of child trees. -/
inductive PlaneTree : Type
  | node (children : List PlaneTree) : PlaneTree

namespace PlaneTree

/-- Ordered child subtrees of the root. A leaf has an empty list of children. -/
def children : PlaneTree → List PlaneTree
  | .node ts => ts

/-- Outdegree of the root. -/
def rootDegree (T : PlaneTree) : ℕ := T.children.length

/-- One fringe subtree per vertex, in depth-first order, including the root. -/
def fringeTrees : PlaneTree → List PlaneTree
  | .node ts => .node ts :: ts.flatMap fringeTrees

/-- Number of vertices, including the root. -/
def vertexCount (T : PlaneTree) : ℕ := T.fringeTrees.length

/-- Number of vertices whose fringe subtree satisfies the marking predicate. -/
noncomputable def markCount (G : PlaneTree → Prop) (T : PlaneTree) : ℕ := by
  classical
  exact T.fringeTrees.countP (fun U => decide (G U))

/-- The declumped mark of Section 1.2: an allowed root degree and a marked child. -/
def declumpedMark (B : Set ℕ) (G : PlaneTree → Prop) (T : PlaneTree) : Prop :=
  T.rootDegree ∈ B ∧ ∃ U ∈ T.children, G U

end PlaneTree
end PoissonDeclumping

/-! ### Discrete σ-algebra, outdegree sequence (lemmas: `PlaneTree/Countable.lean`) -/

namespace PoissonDeclumping.PlaneTree

/-- The discrete σ-algebra: every set of finite plane trees is measurable. -/
instance : MeasurableSpace PlaneTree := ⊤

/-- Outdegrees of the vertices in depth-first order, one entry per vertex
(`k_{u_1}(T), …, k_{u_n}(T)`). The paper's DFS sequence `𝐱(T)` is this list shifted by
`-1`. -/
def degSeq (T : PlaneTree) : List ℕ := T.fringeTrees.map rootDegree

end PoissonDeclumping.PlaneTree

/-! ### Complete `r`-ary trees, non-fringe embeddings and leaf-height (Sections 1.3–1.4, 2.1) -/

namespace PoissonDeclumping.PlaneTree

/-- The complete `r`-ary tree `H_{r,k}` of height `k`: all leaves at distance `k` from the
root, every internal vertex with exactly `r` children. -/
def completeTree (r : ℕ) : ℕ → PlaneTree
  | 0 => node []
  | k + 1 => node (List.replicate r (completeTree r k))

/-- `Embeds T' T` is the paper's `T' ≺ T`: `T` is obtained from `T'` by grafting plane trees
onto the leaves of `T'`. A leaf of `T'` matches an arbitrary tree; a vertex of `T'` with
`d ≥ 1` children matches a vertex of `T` with exactly `d` children, whose children are matched
in order. -/
inductive Embeds : PlaneTree → PlaneTree → Prop
  | leaf (T : PlaneTree) : Embeds (node []) T
  | node (cs ts : List PlaneTree) (hne : cs ≠ []) (hlen : cs.length = ts.length)
      (h : ∀ (i : ℕ) (hi : i < cs.length), Embeds cs[i] (ts[i]'(hlen ▸ hi))) :
      Embeds (node cs) (node ts)

/-- `H_r(T) = max {k ≥ 0 : ∃ u ∈ T, H_{r,k} ≺ T_u}`; the set is nonempty (it contains `0`)
and, for `r ≥ 1`, bounded by the number of vertices. -/
noncomputable def maxCompleteHeight (r : ℕ) (T : PlaneTree) : ℕ :=
  sSup {k : ℕ | ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U}

/-- The leaf-height `λ_∅(T)` of the root: the number of edges to the closest leaf
descendant (`0` for a leaf, `1 +` the minimum over the children otherwise). -/
def rootLeafHeight : PlaneTree → ℕ
  | .node [] => 0
  | .node (t :: us) => (us.map rootLeafHeight).foldr min (rootLeafHeight t) + 1

/-- The leaf-height `λ(T) = max_{v ∈ T} λ_v(T)` of a tree. -/
def leafHeight (T : PlaneTree) : ℕ := (T.fringeTrees.map rootLeafHeight).foldr max 0

end PoissonDeclumping.PlaneTree

/-! ### Bienaymé trees and size conditioning (Section 2.1) -/

section BienaymeDefs

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping

/-- `μ` is critical: its mean `∑ j μ_j` equals one. The sum is taken in `ℝ≥0∞`, so this
statement includes finiteness of the mean. -/
def IsCritical (μ : PMF ℕ) : Prop := ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1

namespace PlaneTree

/-- The Bienaymé weight `∏_{u∈T} μ_{k_u(T)}` of a finite plane tree: the product of the
offspring masses of the outdegrees of its vertices, listed in depth-first order. -/
noncomputable def weight (μ : PMF ℕ) (T : PlaneTree) : ℝ≥0∞ := (T.degSeq.map μ).prod

/-- The law of a `μ`-Bienaymé tree, as a measure on finite plane trees (with the discrete
σ-algebra). It is a probability measure for critical `μ` with `μ 1 ≠ 1`
(`PoissonDeclumping.PlaneTree.bienayme_isProbabilityMeasure`). -/
noncomputable def bienayme (μ : PMF ℕ) : Measure PlaneTree :=
  Measure.sum fun T => weight μ T • Measure.dirac T

/-- A size `n` is admissible if a `μ`-Bienaymé tree has `n` vertices with positive
probability. -/
def Admissible (μ : PMF ℕ) (n : ℕ) : Prop :=
  0 < bienayme μ {T | T.vertexCount = n}

/-- The `μ`-Bienaymé tree conditioned to have `n` vertices. This is a probability measure
exactly at admissible `n` (and the zero measure otherwise). -/
noncomputable def conditioned (μ : PMF ℕ) (n : ℕ) : Measure PlaneTree :=
  ProbabilityTheory.cond (bienayme μ) {T | T.vertexCount = n}

end PlaneTree
end PoissonDeclumping

end BienaymeDefs

/-! ### Total variation (lemmas: `Probability/TotalVariation.lean`) -/

section TotalVariation

open MeasureTheory

namespace PoissonDeclumping

variable {α : Type*} [MeasurableSpace α]

/-- Total variation in the paper's probability convention. For finite measures
this is half of mathlib's total variation. Like mathlib's real-valued distance,
it is totalized to zero if either measure is infinite; probabilistic uses must
retain their probability-measure hypotheses. -/
noncomputable def paperTVDist (μ ν : Measure α) : ℝ := tvDist μ ν / 2

end PoissonDeclumping

end TotalVariation

/-! ### The Łukasiewicz walk and the stable-domain hypothesis `(H_α)` -/

section Walk

open MeasureTheory Filter
open scoped Topology

namespace PoissonDeclumping

/-- The law of one increment `X = K - 1`, `P(X = i) = μ_{i+1}` for `i ≥ -1`. -/
noncomputable def stepLaw (μ : PMF ℕ) : Measure ℤ :=
  μ.toMeasure.map (fun k : ℕ => (k : ℤ) - 1)

/-- The law of the random walk `S_m = X_1 + … + X_m` (`S_0 = 0`) as an `m`-fold convolution. -/
noncomputable def walkLaw (μ : PMF ℕ) : ℕ → Measure ℤ
  | 0 => Measure.dirac 0
  | m + 1 => (walkLaw μ m).conv (stepLaw μ)

/-- A slowly varying function at infinity: `ℓ(a x) / ℓ(x) → 1` for every `a > 0` (the paper's
literal definition, line 850: no positivity or measurability is required; it is used only on the
hypothesis side, where a weaker notion would strengthen the theorems). -/
def SlowlyVarying (ℓ : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → Tendsto (fun x : ℝ => ℓ (a * x) / ℓ x) atTop (𝓝 1)

/-- Hypothesis `(H_α)` with normalizing sequence `a`: `μ` is critical, `μ_1 ≠ 1`,
`α ∈ (1,2]`, and `a` is a nondecreasing sequence (the paper's "increasing"), positive for
`n ≥ 1`, for which
`(K_1+…+K_n−n)/a_n → Y_α` in distribution, where `Y_α` (with law `ν`) has
`E exp(-λ Y_α) = exp(λ^α)` for all `λ > 0`. Convergence in distribution is expressed through
bounded continuous test functions (equivalent to weak convergence of the laws).
No truncated-moment criterion or local-limit estimate is assumed; the latter is proved
from this normalized attraction hypothesis. -/
structure StableDomain (μ : PMF ℕ) (α : ℝ) (a : ℕ → ℝ) : Prop where
  critical : IsCritical μ
  nondegenerate : μ 1 ≠ 1
  alpha_mem : 1 < α ∧ α ≤ 2
  monotone : Monotone a
  pos : ∀ n : ℕ, 1 ≤ n → 0 < a n
  converges : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
    (∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂((walkLaw μ n).map (fun z : ℤ => (z : ℝ) / a n)))
        atTop (𝓝 (∫ x, f x ∂ν))

/-- `(H_α)` for some `α` and some normalizing sequence (the phrase "critical and belongs to
the domain of attraction of a stable law" of Theorems 1.3 and 1.4). -/
def InStableDomain (μ : PMF ℕ) : Prop := ∃ (α : ℝ) (a : ℕ → ℝ), StableDomain μ α a

end PoissonDeclumping

end Walk

/-! ### Marks, cutoffs and Assumptions (M), (S), (C) -/

section Marks

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping

/-- Lists of plane trees (a countable type) carry the discrete σ-algebra. -/
instance : MeasurableSpace (List PlaneTree) := ⊤

/-- Limits are taken along admissible sizes: `n → ∞` with `P(|𝒯| = n) > 0`. -/
def admissibleSizes (μ : PMF ℕ) : Filter ℕ :=
  atTop ⊓ 𝓟 {n | PlaneTree.Admissible μ n}

/-- A cutoff sequence: positive integers (for `n ≥ 1`) with `M_n → ∞` and `M_n = o(n)`. -/
structure IsCutoff (M : ℕ → ℕ) : Prop where
  pos : ∀ n, 1 ≤ n → 0 < M n
  tendsto_atTop : Tendsto M atTop atTop
  isLittleO : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))

/-- `π_n = P(G_{k_n}(𝒯) = 1)` for the unconditioned Bienaymé tree. -/
noncomputable def markProb (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) (n : ℕ) : ℝ :=
  (PlaneTree.bienayme μ).real {T | G (k n) T}

/-- The law of the fringe subtree `𝒯^n_{U_n}` at a uniform vertex `U_n` of `𝒯^n`, with `U_n`
independent of `𝒯^n`: sample `T ~ 𝒯^n` and an independent uniform DFS index `i < n`, and
take the fringe subtree of the `i`-th vertex. -/
noncomputable def uniformFringeLaw (μ : PMF ℕ) (n : ℕ) : Measure PlaneTree :=
  ((PlaneTree.conditioned μ n).prod (uniformOn (Set.Iio n))).map
    (fun p : PlaneTree × ℕ => p.1.fringeTrees.getD p.2 p.1)

/-- Assumption (M), microscopicity: `P(G_{k_n}(𝒯^n_{U_n}) = 1) ∼ P(G_{k_n}(𝒯) = 1)` and
`P(|𝒯^n_{U_n}| > M_n | G_{k_n}(𝒯^n_{U_n}) = 1) = o(1)`. The conditional probability is mathlib's
`cond`, which is `0` when the conditioning event is null (the paper works along subsequences with
positive marking probability, line 206). -/
def Microscopic (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k M : ℕ → ℕ) : Prop :=
  IsEquivalent (admissibleSizes μ)
    (fun n => (uniformFringeLaw μ n).real {T | G (k n) T}) (markProb μ G k) ∧
  Tendsto (fun n => (cond (uniformFringeLaw μ n) {T | G (k n) T}).real
    {T | M n < T.vertexCount}) (admissibleSizes μ) (𝓝 0)

/-- A decomposition as in Assumption (S) for one mark `G`, i.e. under `P_k = P(· | G(𝒯) = 1)`.
It is a law `ρ` of `(𝒯, C, 𝒯^{(1)},…,𝒯^{(L)})` on `PlaneTree × ℕ × List PlaneTree`, with `L` the
length of the list, such that: (1) the first coordinate has law `P(· | G(𝒯) = 1)`;
(2) conditionally on `(C, L)` the listed trees are independent with the law of `𝒯` (the
product formula for point masses); (3) almost surely `|𝒯| = C + ∑_{i ≤ L} |𝒯^{(i)}|`.
(The paper's infinite sequence `𝒯^{(1)}, 𝒯^{(2)},…` only matters through its first `L` terms.) -/
structure Skeleton (μ : PMF ℕ) (G : PlaneTree → Prop)
    (ρ : Measure (PlaneTree × ℕ × List PlaneTree)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ρ
  law_tree : ρ.map Prod.fst = cond (PlaneTree.bienayme μ) {T | G T}
  conditionally_iid : ∀ (c : ℕ) (ts : List PlaneTree),
    ρ {ω | ω.2.1 = c ∧ ω.2.2 = ts} =
      ρ {ω | ω.2.1 = c ∧ ω.2.2.length = ts.length} *
        (ts.map (PlaneTree.weight μ)).prod
  size_eq : ∀ᵐ ω ∂ρ, ω.1.vertexCount = ω.2.1 + (ω.2.2.map PlaneTree.vertexCount).sum

/-- Assumption (S), structural microscopicity, with respect to the normalizing sequence `a`
of `(H_α)`: for each mark `G_k` with `P(G_k(𝒯) = 1) > 0` there is a decomposition `ρ_k` (the
paper works along subsequences with positive marking probability, line 206; at null marks `ρ_k`
is unconstrained), and for every `ε > 0`
`a_n P_{k_n}(C_{k_n} > ε M_n) → 0` and `E_{k_n}[L_{k_n}] / a_{M_n} → 0`. -/
def StructuralMicroscopic (μ : PMF ℕ) (a : ℕ → ℝ) (G : ℕ → PlaneTree → Prop)
    (k M : ℕ → ℕ) : Prop :=
  ∃ ρ : ℕ → Measure (PlaneTree × ℕ × List PlaneTree),
    (∀ j, 0 < PlaneTree.bienayme μ {T | G j T} → Skeleton μ (G j) (ρ j)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => a n * (ρ (k n)).real {ω | ε * (M n : ℝ) < ω.2.1})
      (admissibleSizes μ) (𝓝 0)) ∧
    Tendsto (fun n => (∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ (k n)) / ENNReal.ofReal (a (M n)))
      (admissibleSizes μ) (𝓝 0)

/-- `A_n(ℓ) = P(|𝒯| ≥ ℓ+1, G_{k_n}(𝒯) = 1, G_{k_n}(𝒯_{u_{ℓ+1}}) = 1)`; the `(ℓ+1)`-st vertex
in DFS order has fringe tree `T.fringeTrees[ℓ]`. -/
noncomputable def pairProb (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ)
    (n ℓ : ℕ) : ℝ :=
  (PlaneTree.bienayme μ).real
    {T | ℓ + 1 ≤ T.vertexCount ∧ G (k n) T ∧ ∃ U ∈ T.fringeTrees[ℓ]?, G (k n) U}

/-- Assumption (C), pair non-clustering: `∑_{ℓ=1}^{M_n} A_n(ℓ) = o(n π_n²)`. -/
def NonClustering (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k M : ℕ → ℕ) : Prop :=
  (fun n => ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) =o[admissibleSizes μ]
    (fun n => (n : ℝ) * markProb μ G k n ^ 2)

/-- The number of marked fringe subtrees `#{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}` is
`markCount (G (k n))`, a random variable on `conditioned μ n`. Its law, as a measure on `ℕ`. -/
noncomputable def markedCountLaw (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ)
    (n : ℕ) : Measure ℕ :=
  (PlaneTree.conditioned μ n).map (PlaneTree.markCount (G (k n)))

end PoissonDeclumping

end Marks

/-! ### Statements of the four Introduction theorems -/

section Main

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping

/-- Theorem 1.1 (`thm:PoissonApproximation`, source lines 305–329). -/
def PoissonApproximationStatement : Prop :=
  ∀ (μ : PMF ℕ), InStableDomain μ →
  ∀ (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ),
    (∃ M : ℕ → ℕ, IsCutoff M ∧ Microscopic μ G k M ∧ NonClustering μ G k M) →
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist (markedCountLaw μ G k n)
        (poissonMeasure (Real.toNNReal ((n : ℝ) * markProb μ G k n))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | ε < |(PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
        (admissibleSizes μ) (𝓝 0)) ∧
      (∀ K : ℕ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | PlaneTree.markCount (G (k n)) T ≤ K}) (admissibleSizes μ) (𝓝 0)))

/-- The constant `c_B = E[k_∅(𝒯) 1_{k_∅(𝒯) ∈ B}] = ∑_{j ∈ B} j μ_j`. -/
noncomputable def cB (μ : PMF ℕ) (B : Set ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, B.indicator (fun j => (j : ℝ≥0∞) * μ j) j

/-- Theorem 1.2 (`thm:PoissonApproximation2`, source lines 396–442): root declumping. The
raw marks satisfy (S) and the declumped marks `Ghat_k = declumpedMark B G_k` satisfy (C), both
with the same cutoff sequence. -/
def PoissonApproximation2Statement : Prop :=
  ∀ (μ : PMF ℕ) (α : ℝ) (a : ℕ → ℝ), StableDomain μ α a →
  ∀ (G : ℕ → PlaneTree → Prop) (k M : ℕ → ℕ), IsCutoff M →
  ∀ B : Set ℕ, 0 < cB μ B → cB μ B < ∞ →
    StructuralMicroscopic μ a G k M →
    NonClustering μ (fun j => PlaneTree.declumpedMark B (G j)) k M →
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist
        (markedCountLaw μ (fun j => PlaneTree.declumpedMark B (G j)) k n)
        (poissonMeasure (Real.toNNReal ((cB μ B).toReal * ((n : ℝ) * markProb μ G k n)))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop →
      ∀ K : ℕ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | PlaneTree.markCount (PlaneTree.declumpedMark B (G (k n))) T ≤ K})
        (admissibleSizes μ) (𝓝 0))

/-- The centering `t_n^*` of Theorem 1.3(i). -/
noncomputable def tStar (μ₁ : ℝ) (n : ℕ) : ℝ :=
  (Real.log n + Real.log (1 - μ₁)) / Real.log (1 / μ₁)

/-- The centering `t_n^{**}` of Theorem 1.3(ii). -/
noncomputable def tStarStar (r : ℕ) (μᵣ : ℝ) (n : ℕ) : ℝ :=
  Real.logb r (Real.log n) - Real.logb r (Real.log (1 / μᵣ) / ((r : ℝ) - 1))

/-- The two-point set `J_n`: `{m_n - 1, m_n}` if `θ_n ≤ 1/2`, otherwise `{m_n, m_n + 1}`,
where `m_n = ⌊x⌋` and `θ_n = {x}` for the centering `x`. -/
def twoPointSet (x : ℝ) : Set ℤ :=
  if Int.fract x ≤ 1 / 2 then {⌊x⌋ - 1, ⌊x⌋} else {⌊x⌋, ⌊x⌋ + 1}

/-- Localization on `J_n` along all admissible sizes, and on `m_n` along every nontrivial
filter of admissible sizes whose phases stay a positive distance from the integers.
In particular, the single-point refinement applies to every such admissible subsequence. -/
def TwoPointLocalization (μ : PMF ℕ) (H : PlaneTree → ℕ) (x : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real {T | ((H T : ℕ) : ℤ) ∈ twoPointSet (x n)})
    (admissibleSizes μ) (𝓝 1) ∧
  (∀ l : Filter ℕ, l ≤ admissibleSizes μ → l.NeBot →
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in l,
      δ ≤ min (Int.fract (x n)) (1 - Int.fract (x n))) →
    Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real {T | ((H T : ℕ) : ℤ) = ⌊x n⌋})
      l (𝓝 1))

/-- The lattice-modulated Gumbel limit `P(H(𝒯^n) ≤ ⌊x_n + t⌋) − exp(−μ₁^{t+1−{x_n+t}}) → 0`
for every real `t`. -/
def LatticeGumbel (μ : PMF ℕ) (H : PlaneTree → ℕ) (μ₁ : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ t : ℝ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n +
    t⌋} -
    Real.exp (-(μ₁ ^ (t + 1 - Int.fract (x n + t))))) (admissibleSizes μ) (𝓝 0)

/-- Theorem 1.3 (`thm:max_string`, source lines 475–501): the maximal complete non-fringe
`r`-ary height `H_r = maxCompleteHeight r`. -/
def MaxStringStatement : Prop :=
  ∀ μ : PMF ℕ, InStableDomain μ →
    (0 < μ 1 → LatticeGumbel μ (PlaneTree.maxCompleteHeight 1) (μ 1).toReal
      (tStar (μ 1).toReal)) ∧
    (∀ r : ℕ, 2 ≤ r → 0 < μ r →
      TwoPointLocalization μ (PlaneTree.maxCompleteHeight r)
        (tStarStar r (μ r).toReal))

/-- Theorem 1.4 (`thm:max_lh`, source lines 533–558): the maximum leaf-height
`λ = PlaneTree.leafHeight`. The constants `C_μ`, `D_μ` are identified with the limits of the
root leaf-height tails `π_k = P(λ_∅(𝒯) ≥ k)` (source lines 562–572), as the paper records;
the centerings are `k_n^*` and `k_n^{**}`. -/
def MaxLeafHeightStatement : Prop :=
  ∀ μ : PMF ℕ, InStableDomain μ →
    (0 < μ 1 → ∃ C : ℝ, 0 < C ∧
      Tendsto (fun j : ℕ => (PlaneTree.bienayme μ).real {T | j ≤ T.rootLeafHeight} /
        (μ 1).toReal ^ j) atTop (𝓝 C) ∧
      LatticeGumbel μ PlaneTree.leafHeight (μ 1).toReal (fun n : ℕ =>
        (Real.log n + Real.log ((1 - (μ 1).toReal) * C)) / Real.log (1 / (μ 1).toReal))) ∧
    (μ 1 = 0 →
      let κ : ℕ := sInf {i : ℕ | 2 ≤ i ∧ 0 < μ i}
      ∃ D : ℝ, 0 < D ∧ D < 1 ∧
        Tendsto (fun j : ℕ => ((PlaneTree.bienayme μ).real {T | j ≤ T.rootLeafHeight}) ^
          (1 / (κ : ℝ) ^ j)) atTop (𝓝 D) ∧
        TwoPointLocalization μ PlaneTree.leafHeight (fun n : ℕ =>
          Real.logb κ (Real.log n) - Real.logb κ (Real.log (1 / D))))

end PoissonDeclumping

end Main
