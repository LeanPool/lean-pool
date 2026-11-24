/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement
public import LeanPool.GraphMinor.Hypergraph.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Topological Surfaces, Curves, Discs, Drawings, and Paintings

This file defines the foundational topological notions for surfaces and graphs/hypergraphs
drawn on surfaces, shared by Graph Minors VI–IX and XI–XX:
- Standard model spaces (`EuclideanPlane`, `ClosedUnitDisc`, `OpenUnitDisc`, `UnitCircle`,
  `ClosedCylinder`) and connected/path-connected components in a subset (`componentsIn`,
  `arcComponentsIn`).
- Surfaces with boundary (`IsSurface`), closed surfaces (`IsClosedSurface`), manifold boundary
  (`bd`), topological frontier (`subBd`), cuffs (`IsCuff`), closed discs (`IsClosedDisc`), open
  discs (`IsOpenDisc`), lines (`IsLine`, `IsLineWithEnds`), $O$-arcs (`IsOArc`), and $I$-arcs
  (`IsIArc`, `IsProperIArc`).
- Parameterized curves (`Curve`), internal curves (`Curve.IsInternal`), injective curves / lines
  (`Curve.IsLine`), homotopy of curves and closed curves in a subset, null-homotopic curves and
  $O$-arcs, and simply connected subsets (`IsSimplyConnectedSet`).
- Topological drawings (`Drawing`) and paintings (`Painting`) in a surface $S$, their edges,
  regions, atoms, subdrawings, $\Gamma$-normality, restrictions $\Gamma \cap \Delta$, 2-cell
  drawings, radial drawings, dual drawings, walks and curves tracing walks, homotopy of forests,
  and the canonical bridge to `Graph` (`Drawing.toGraph`, `GraphDrawing`, `GraftDrawing`) and
  `Hypergraph` (`Painting.toHypergraph`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology unitInterval Graph

universe u v w

/-! ## 1. Standard Model Spaces and Components in a Subset -/

/-- The Euclidean plane $\mathbb{R}^2$, modeled as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev EuclideanPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- The closed unit disc $\{(x, y) \in \mathbb{R}^2 : x^2 + y^2 \le 1\}$.
Graph Minors XI, Section 3 (page 74); Graph Minors XIV, Section 2 (page 25). -/
noncomputable def ClosedUnitDisc : Set EuclideanPlane :=
  Metric.closedBall 0 1

/-- The open unit disc $\{(x, y) \in \mathbb{R}^2 : x^2 + y^2 < 1\}$.
Graph Minors XI, Section 3 (page 74); Graph Minors XIV, Section 2 (page 25). -/
noncomputable def OpenUnitDisc : Set EuclideanPlane :=
  Metric.ball 0 1

/-- The unit circle $\{(x, y) \in \mathbb{R}^2 : x^2 + y^2 = 1\}$ in $\mathbb{R}^2$.
Graph Minors XI, Section 3 (page 76). -/
noncomputable def UnitCircle : Set EuclideanPlane :=
  Metric.sphere 0 1

/-- The standard closed cylinder $[1, 2] \times S^1$.
Graph Minors VI, Section 5 (page 127): "It is convenient in this section to take a concrete
representation of $\Sigma$ (using polar coordinates) as
$$\Sigma = \{(r, \theta): 1 \le r \le 2, 0 \le \theta < 2\pi\}$$" -/
def ClosedCylinder : Set (ℝ × Circle) :=
  Set.Icc (1 : ℝ) 2 ×ˢ Set.univ

/-- The equivalence relation on `[0, 1] × [0, 1]` identifying `(0, y)` with `(1, 1 - y)`. -/
def mobiusSetoid : Setoid (unitInterval × unitInterval) :=
  Relation.EqvGen.setoid fun p q => p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2

/-- The standard Möbius band: the square `[0, 1] × [0, 1]` with `(0, y)` glued to `(1, 1 - y)`. -/
abbrev MobiusBand : Type :=
  Quotient mobiusSetoid

/-- The set of connected components of a subset $F \subseteq S$. -/
noncomputable def componentsIn {S : Type u} [TopologicalSpace S] (F : Set S) : Set (Set S) :=
  (connectedComponentIn F) '' F

/-- The set of arc-wise (path) connected components of a subset $F \subseteq S$.
Graph Minors XI, Section 3 (page 74): "$U - V$ has only finitely many arc-wise connected
components, called *edges*, ..." -/
def arcComponentsIn {S : Type u} [TopologicalSpace S] (F : Set S) : Set (Set S) :=
  {C : Set S | C.Nonempty ∧ C ⊆ F ∧ IsPathConnected C ∧
    ∀ D : Set S, D ⊆ F → IsPathConnected D → C ⊆ D → D = C}

/-! ## 2. Surfaces, Boundary, Cuffs, Discs, Lines, and $O$-Arcs -/

/-- A point $x \in S$ is an *interior point* of a 2-manifold $S$ if it has an open
neighbourhood homeomorphic to the open unit disc in $\mathbb{R}^2$. -/
def IsInteriorPoint {S : Type u} [TopologicalSpace S] (x : S) : Prop :=
  ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (U ≃ₜ OpenUnitDisc)

/-- A point $x \in S$ is a *chart point* of a 2-manifold with boundary $S$ if it has an
open neighbourhood homeomorphic either to the open unit disc or to an open subset of the upper
half-plane `EuclideanHalfSpace 2`. -/
def IsManifoldPoint {S : Type u} [TopologicalSpace S] (x : S) : Prop :=
  ∃ (U : Set S) (V : Set (EuclideanHalfSpace 2)),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ Nonempty (U ≃ₜ V)

/-- The *boundary* $\operatorname{bd}(\Sigma)$ of a surface $\Sigma$ is the set of points of
$\Sigma$ that do not have an open neighbourhood homeomorphic to an open disc.
Graph Minors VI, Section 1 (page 116): "A *surface* is a compact 2-manifold with boundary. ... We
generally denote a surface by $\Sigma$, and its boundary by $bd(\Sigma)$. Any component of
$bd(\Sigma)$ is called a *cuff* of $\Sigma$."
Graph Minors VII, Section 2 (page 213): "The boundary of a surface $\Sigma$ is denoted by
$\operatorname{bd}(\Sigma)$, and each component of $\operatorname{bd}(\Sigma)$ is called a
*cuff*." -/
def bd (S : Type u) [TopologicalSpace S] : Set S :=
  {x : S | ¬ IsInteriorPoint x}

/-- A *surface* (with possibly empty boundary) is a compact 2-manifold with boundary.
Graph Minors VI, Section 1 (page 116): "A *surface* is a compact 2-manifold with boundary."
Graph Minors VII, Section 2 (page 213): "A *surface* is a compact 2-manifold with (possibly null)
boundary." -/
def IsSurface (S : Type u) [TopologicalSpace S] : Prop :=
  CompactSpace S ∧ T2Space S ∧ ∀ x : S, IsManifoldPoint x

/-- A *closed surface* (or surface without boundary) is a compact 2-manifold without boundary.
Graph Minors XI, Section 3 (page 74): "A *surface* is a compact 2-manifold, without boundary." -/
def IsClosedSurface (S : Type u) [TopologicalSpace S] : Prop :=
  CompactSpace S ∧ T2Space S ∧ ∀ x : S, IsInteriorPoint x

/-- A *cuff* of a surface $\Sigma$ is a connected component of $\operatorname{bd}(\Sigma)$.
Graph Minors VI, Section 1 (page 116); Graph Minors VII, Section 2 (page 213);
Graph Minors XI, Section 3 (page 74); Graph Minors XIX, Section 2 (page 327). -/
def IsCuff {S : Type u} [TopologicalSpace S] (C : Set S) : Prop :=
  C ∈ componentsIn (bd S)

/-- The set of all cuffs of $\Sigma$. -/
noncomputable def cuffs (S : Type u) [TopologicalSpace S] : Set (Set S) :=
  componentsIn (bd S)

/-- For a subset $\Delta \subseteq \Sigma$, its topological boundary in $\Sigma$ is
$\bar{\Delta} \cap \overline{\Sigma - \Delta}$ (the topological frontier).
Graph Minors XI, Section 3 (page 74): "If $\Delta \subseteq \Sigma$, then $\bar{\Delta}$ denotes
the closure of $\Delta$, and $\operatorname{bd}(\Delta)$ denotes
$\bar{\Delta} \cap \overline{\Sigma - \Delta}$." -/
def subBd {S : Type u} [TopologicalSpace S] (Δ : Set S) : Set S :=
  closure Δ ∩ closure (Set.univ \ Δ)

/-- For a subset $X \subseteq \Sigma$, $\tilde{X} = \bar{X} \setminus X$.
Graph Minors XVII, Section 1 (page 164); Graph Minors XIX, Section 2 (page 327). -/
def tilde {S : Type u} [TopologicalSpace S] (X : Set S) : Set S :=
  closure X \ X

/-- A *closed disc* in $\Sigma$ is a subset $\Delta \subseteq \Sigma$ homeomorphic to
$\{(x, y) \in \mathbb{R}^2 : x^2 + y^2 \le 1\}$.
Graph Minors XI, Section 3 (pages 74–75): "$\Delta \subseteq \Sigma$ is a *closed disc* if it is
homeomorphic to $\{(x, y) : x^2 + y^2 \le 1\}$, and ... an *open disc* is defined similarly." -/
def IsClosedDisc {S : Type u} [TopologicalSpace S] (Δ : Set S) : Prop :=
  Nonempty (ClosedUnitDisc ≃ₜ Δ)

/-- The boundary $O$-arc of a closed disc $\Delta \subseteq \Sigma$, that is, its manifold boundary
$\operatorname{bd}(\Delta)$ when viewed as a surface in the subspace topology. -/
def discBd {S : Type u} [TopologicalSpace S] (Δ : Set S) : Set S :=
  Subtype.val '' (bd Δ)

/-- An *open disc* in $\Sigma$ is an open subset $\Lambda \subseteq \Sigma$ homeomorphic to
$\{(x, y) \in \mathbb{R}^2 : x^2 + y^2 < 1\}$.
Graph Minors XI, Section 3 (page 74); Graph Minors XIV, Section 2 (page 25). -/
def IsOpenDisc {S : Type u} [TopologicalSpace S] (Λ : Set S) : Prop :=
  IsOpen Λ ∧ Nonempty (OpenUnitDisc ≃ₜ Λ)

/-- If $X$ is a topological space, an *$X$-arc* in $\Sigma$ is a subset of $\Sigma$ homeomorphic to
$X$.
Graph Minors VII, Section 5 (page 231); Graph Minors VIII, Section 5 (page 262). -/
def IsXArc {S : Type u} [TopologicalSpace S] (X : Type v) [TopologicalSpace X]
    (F : Set S) : Prop :=
  Nonempty (X ≃ₜ F)

/-- A *line* (or $[0, 1]$-arc) in $\Sigma$ is a subset $L \subseteq \Sigma$ homeomorphic to the unit
interval $[0, 1]$.
Graph Minors XI, Section 3 (page 74): "A *line* in $\Sigma$ is a subset homeomorphic to $[0, 1]$,
and its *ends* are defined in the natural way." -/
def IsLine {S : Type u} [TopologicalSpace S] (L : Set S) : Prop :=
  Nonempty (unitInterval ≃ₜ L)

/-- A subset $L \subseteq \Sigma$ is a *line with ends $u$ and $v$* if there is a homeomorphism
$f \colon [0, 1] \simeq_t L$ mapping $0$ to $u$ and $1$ to $v$.
Graph Minors VII, Section 2 (page 214); Graph Minors XI, Section 3 (page 74). -/
def IsLineWithEnds {S : Type u} [TopologicalSpace S] (L : Set S) (u v : S) : Prop :=
  ∃ f : unitInterval ≃ₜ L, (f 0).1 = u ∧ (f 1).1 = v

/-- The set of ends of a line $L \subseteq \Sigma$.
Graph Minors XI, Section 3 (page 74); Graph Minors XIX, Section 15 (page 381). -/
def lineEnds {S : Type u} [TopologicalSpace S] (L : Set S) : Set S :=
  {u : S | ∃ v : S, IsLineWithEnds L u v}

/-- An *$O$-arc* in $\Sigma$ is a subset $F \subseteq \Sigma$ homeomorphic to the circle $S^1$.
Graph Minors VII, Section 2 (page 214); Graph Minors XI, Section 3 (page 74):
"An *O-arc* is a subset homeomorphic to a circle." -/
def IsOArc {S : Type u} [TopologicalSpace S] (F : Set S) : Prop :=
  Nonempty (Circle ≃ₜ F)

/-- An *$I$-arc* in $\Sigma$ is a subset $F \subseteq \Sigma$ homeomorphic to $[0, 1]$ with both
ends in $\operatorname{bd}(\Sigma)$.
Graph Minors VII, Section 2 (page 214): "An *I-arc* is a subset $F \subseteq \Sigma$ homeomorphic
to $[0, 1]$, such that there is a homeomorphism $f \colon [0, 1] \to F$ with
$f(0), f(1) \in \operatorname{bd}(\Sigma)$." -/
def IsIArc {S : Type u} [TopologicalSpace S] (F : Set S) : Prop :=
  ∃ u v : S, u ∈ bd S ∧ v ∈ bd S ∧ IsLineWithEnds F u v

/-- A *proper $I$-arc* in $\Sigma$ is an $I$-arc $F$ with $|F \cap \operatorname{bd}(\Sigma)| = 2$
(its two ends are in $\operatorname{bd}(\Sigma)$ and no interior point is in
$\operatorname{bd}(\Sigma)$).
Graph Minors VII, Section 2 (page 218); Graph Minors XVII, Section 1 (page 164). -/
def IsProperIArc {S : Type u} [TopologicalSpace S] (F : Set S) : Prop :=
  ∃ u v : S, u ≠ v ∧ F ∩ bd S = {u, v} ∧ IsLineWithEnds F u v

/-! ## 3. Parameterized Curves and Homotopy -/

/-- A *curve* in a surface $\Sigma$ is a continuous map $\phi \colon [0, 1] \to \Sigma$.
Graph Minors VI, Section 4 (page 123) & Section 5 (page 127) (paraphrased);
Graph Minors XI, Section 3 (page 75): "A curve in a surface $\Sigma$ is a continuous function
$\phi : [0, 1] \to \Sigma$." -/
abbrev Curve (S : Type u) [TopologicalSpace S] : Type u :=
  C(unitInterval, S)

/-- The initial point $f(0)$ of a curve $f$. -/
def Curve.head {S : Type u} [TopologicalSpace S] (f : Curve S) : S :=
  f 0

/-- The terminal point $f(1)$ of a curve $f$. -/
def Curve.tail {S : Type u} [TopologicalSpace S] (f : Curve S) : S :=
  f 1

/-- The set $\{f(0), f(1)\}$ of *ends* of a curve $f$ (paraphrasing Graph Minors VI, Section 4,
page 123, and Graph Minors VII, Section 2, page 214). -/
def Curve.ends {S : Type u} [TopologicalSpace S] (f : Curve S) : Set S :=
  {f 0, f 1}

/-- The image $|f|$ (denoted $|f|$ in GM VI and $|\phi|$ in GM XI) of a curve $f$, that is,
$\{f(x) : 0 \le x \le 1\}$.
Graph Minors VI, Section 5 (page 129); Graph Minors XI, Section 3 (page 75). -/
def Curve.support {S : Type u} [TopologicalSpace S] (f : Curve S) : Set S :=
  Set.range f

/-- The *interior* $f((0, 1))$ of a curve $f$ (paraphrasing Graph Minors VI, Section 4, page 123,
and Graph Minors VII, Section 2, page 214). -/
def Curve.interiorSupport {S : Type u} [TopologicalSpace S] (f : Curve S) : Set S :=
  f '' {t : unitInterval | (0 : ℝ) < t.1 ∧ t.1 < 1}

/-- A curve $f$ is *internal* if its interior $f((0, 1))$ is disjoint from
$\operatorname{bd}(\Sigma)$
(paraphrasing Graph Minors VI, Section 4, page 123, and Graph Minors VII, Section 2, page 218). -/
def Curve.IsInternal {S : Type u} [TopologicalSpace S] (f : Curve S) : Prop :=
  Disjoint f.interiorSupport (bd S)

/-- A curve $f \colon [0, 1] \to \Sigma$ is a *line* (parameterized injection) if it is
injective: $f(x) \ne f(y)$ for $0 \le x < y \le 1$ (paraphrasing the "continuous injection"
parameterization of paths in Graph Minors VI, Section 4, page 123, and Section 5, page 127). -/
def Curve.IsLine {S : Type u} [TopologicalSpace S] (f : Curve S) : Prop :=
  Function.Injective f

/-- A curve $\phi$ is *constant* if $|\phi|$ is a singleton.
Graph Minors XI, Section 3 (page 75). -/
def Curve.IsConstant {S : Type u} [TopologicalSpace S] (f : Curve S) : Prop :=
  ∃ c : S, ∀ x : unitInterval, f x = c

/-- Two curves $\phi_0, \phi_1 \colon [0, 1] \to \Sigma$ are *homotopic in $Z \subseteq \Sigma$* if
there is a continuous map $\psi \colon [0, 1] \times [0, 1] \to \Sigma$ with values in $Z$ such that
$\psi(x, 0) = \phi_0(x)$, $\psi(x, 1) = \phi_1(x)$, $\psi(0, y) = \phi_0(0) = \phi_1(0)$, and
$\psi(1, y) = \phi_0(1) = \phi_1(1)$.
Graph Minors VI, Section 4 (page 122) & Section 5 (page 126);
Graph Minors XI, Section 3 (pages 75–76). -/
def CurvesHomotopicIn {S : Type u} [TopologicalSpace S] (Z : Set S)
    (φ₀ φ₁ : Curve S) : Prop :=
  ∃ ψ : C(unitInterval × unitInterval, S),
    (∀ p, ψ p ∈ Z) ∧
    (∀ x, ψ (x, 0) = φ₀ x) ∧
    (∀ x, ψ (x, 1) = φ₁ x) ∧
    (∀ y, ψ (0, y) = φ₀ 0) ∧
    (∀ y, ψ (0, y) = φ₁ 0) ∧
    (∀ y, ψ (1, y) = φ₀ 1) ∧
    (∀ y, ψ (1, y) = φ₁ 1)

/-- Two curves $\phi_0, \phi_1$ are *homotopic* in $\Sigma$ if they are homotopic in `Set.univ`.
Graph Minors VI, Section 5 (page 126); Graph Minors XI, Section 3 (page 75). -/
def CurvesHomotopic {S : Type u} [TopologicalSpace S] (φ₀ φ₁ : Curve S) : Prop :=
  CurvesHomotopicIn Set.univ φ₀ φ₁

/-- A curve $\phi$ is *null-homotopic in $Z$* if it is homotopic in $Z$ to a constant curve.
Graph Minors XI, Section 3 (page 76). -/
def Curve.IsNullHomotopicIn {S : Type u} [TopologicalSpace S] (Z : Set S)
    (φ : Curve S) : Prop :=
  ∃ c : Curve S, c.IsConstant ∧ CurvesHomotopicIn Z φ c

/-- Two continuous maps $\phi_0, \phi_1 \colon S^1 \to \Sigma$ are *homotopic in $Z$* if there is a
continuous map $\psi \colon S^1 \times [0, 1] \to \Sigma$ with values in $Z$ such that
$\psi(x, 0) = \phi_0(x)$ and $\psi(x, 1) = \phi_1(x)$ for all $x \in S^1$.
Graph Minors XI, Section 3 (page 76). -/
def ClosedCurvesHomotopicIn {S : Type u} [TopologicalSpace S] (Z : Set S)
    (φ₀ φ₁ : C(Circle, S)) : Prop :=
  ∃ ψ : C(Circle × unitInterval, S),
    (∀ p, ψ p ∈ Z) ∧
    (∀ x, ψ (x, 0) = φ₀ x) ∧
    (∀ x, ψ (x, 1) = φ₁ x)

/-- A continuous map $\phi \colon S^1 \to \Sigma$ is *null-homotopic in $Z$* if it is homotopic in
$Z$ to a constant map.
Graph Minors XI, Section 3 (page 76). -/
def ClosedCurveIsNullHomotopicIn {S : Type u} [TopologicalSpace S] (Z : Set S)
    (φ : C(Circle, S)) : Prop :=
  ∃ c : S, c ∈ Z ∧ ClosedCurvesHomotopicIn Z φ (ContinuousMap.const Circle c)

/-- An $O$-arc $F \subseteq \Sigma$ is *null-homotopic in $Z$* if there is a homeomorphism
$\phi \colon S^1 \simeq_t F$ whose composition with the inclusion $F \hookrightarrow \Sigma$ is
null-homotopic in $Z$.
Graph Minors VII, Section 2 (page 214); Graph Minors XI, Section 3 (page 76). -/
def IsNullHomotopicOArcIn {S : Type u} [TopologicalSpace S] (Z : Set S) (F : Set S) : Prop :=
  ∃ φ : Circle ≃ₜ F,
    ClosedCurveIsNullHomotopicIn Z ⟨fun x => (φ x).1, continuous_subtype_val.comp φ.continuous⟩

/-- An $O$-arc $F \subseteq \Sigma$ is *null-homotopic* in $\Sigma$ if it is null-homotopic in
`Set.univ`.
Graph Minors VII, Section 2 (page 214); Graph Minors XI, Section 3 (page 76). -/
def IsNullHomotopicOArc {S : Type u} [TopologicalSpace S] (F : Set S) : Prop :=
  IsNullHomotopicOArcIn Set.univ F

/-- A subset $Z \subseteq \Sigma$ is *simply-connected* if it is arc-wise connected and every
continuous function $\phi \colon S^1 \to Z$ is null-homotopic in $Z$.
Graph Minors XI, Section 3 (page 76). -/
def IsSimplyConnectedSet {S : Type u} [TopologicalSpace S] (Z : Set S) : Prop :=
  IsPathConnected Z ∧
    ∀ φ : C(Circle, S), Set.range φ ⊆ Z → ClosedCurveIsNullHomotopicIn Z φ

/-! ## 4. Drawings and Paintings in a Surface -/

/-- A *drawing* $\Gamma = (U, V)$ in a topological space $\Sigma$: $V \subseteq U \subseteq \Sigma$,
$U$ is closed, $V$ is finite, $U - V$ has finitely many arc-wise connected components (called
*edges*), and for every edge $e$, either $\bar{e}$ is a line whose set of ends is $\bar{e} \cap V$
(with 2 distinct ends), or $\bar{e}$ is an $O$-arc and $|\bar{e} \cap V| = 1$.
Graph Minors XI, Section 3 (page 74): "A *drawing* in $\Sigma$ is a pair $(U, V)$, where
$V \subseteq U \subseteq \Sigma$, $U$ is closed, $V$ is finite, $U - V$ has only finitely many
arc-wise connected components, called *edges*, and for every edge $e$, either $\bar{e}$ is a line
whose set of ends is $\bar{e} \cap V$, or $\bar{e}$ is an $O$-arc and $|\bar{e} \cap V| = 1$."
Graph Minors VII, Section 2 (page 214); Graph Minors VIII, Section 5 (page 262);
Graph Minors XI, Section 3 (page 74); Graph Minors XII, Section 1 (page 240);
Graph Minors XIV, Section 2 (page 26). -/
structure Drawing (S : Type u) [TopologicalSpace S] where
  /-- The underlying closed subset $U(\Gamma) \subseteq \Sigma$ of the drawing. -/
  U : Set S
  /-- The finite set of vertices $V(\Gamma) \subseteq U(\Gamma)$. -/
  V : Set S
  /-- Every vertex lies in $U(\Gamma)$. -/
  V_subset_U : V ⊆ U
  /-- $U(\Gamma)$ is closed in $\Sigma$. -/
  isClosed_U : IsClosed U
  /-- $V(\Gamma)$ is finite. -/
  finite_V : V.Finite
  /-- $U(\Gamma) \setminus V(\Gamma)$ has only finitely many arc-wise connected components
  (edges). -/
  finite_edges : (arcComponentsIn (U \ V)).Finite
  /-- Each edge $e$ has closure $\bar{e}$ either a line with ends $\bar{e} \cap V$ of size 2, or an
  $O$-arc with $|\bar{e} \cap V| = 1$. -/
  edge_cond : ∀ e ∈ arcComponentsIn (U \ V),
    (∃ u v : S, u ≠ v ∧ closure e ∩ V = {u, v} ∧ IsLineWithEnds (closure e) u v) ∨
    (∃ u : S, closure e ∩ V = {u} ∧ IsOArc (closure e))

namespace Drawing

variable {S : Type u} [TopologicalSpace S]

/-- The set of *edges* $E(\Gamma)$ of a drawing $\Gamma$, defined as the arc-wise connected
components of $U(\Gamma) \setminus V(\Gamma)$.
Graph Minors VII, Section 2 (page 214); Graph Minors XI, Section 3 (page 74). -/
def E (Γ : Drawing S) : Set (Set S) :=
  arcComponentsIn (Γ.U \ Γ.V)

/-- The set of *regions* $R(\Gamma)$ of a drawing $\Gamma$, defined as the connected components of
$\Sigma \setminus U(\Gamma)$.
Graph Minors VI, Section 1 (page 116); Graph Minors XI, Section 3 (page 74). -/
noncomputable def R (Γ : Drawing S) : Set (Set S) :=
  componentsIn (Set.univ \ Γ.U)

/-- The set of *atoms* $A(\Gamma)$ of a drawing $\Gamma$: the singleton vertex sets $\{v\}$
($v \in V(\Gamma)$), the edges $e \in E(\Gamma)$, and the regions $r \in R(\Gamma)$.
Graph Minors XI, Section 9 (page 104); Graph Minors XII, Section 1 (page 240);
Graph Minors XIV, Section 2 (page 26). -/
noncomputable def A (Γ : Drawing S) : Set (Set S) :=
  (fun v : S => ({v} : Set S)) '' Γ.V ∪ Γ.E ∪ Γ.R

/-- A vertex $v \in V(\Gamma)$ is *incident with* an edge or region $x$ if $v \in \bar{x}$.
Graph Minors XI, Section 3 (page 74). -/
def VertexIncident (Γ : Drawing S) (v : S) (x : Set S) : Prop :=
  v ∈ Γ.V ∧ (x ∈ Γ.E ∨ x ∈ Γ.R) ∧ v ∈ closure x

/-- An edge $e \in E(\Gamma)$ is *incident with* a region $r \in R(\Gamma)$ if
$(e \cap \bar{r}).\text{Nonempty}$.
Graph Minors XI, Section 3 (page 74): "If $e$ is an edge and $r$ is a region, we say $e$ is
*incident with* $r$ (and vice versa) if $e \cap \bar{r} \ne \emptyset$." -/
def EdgeRegionIncident (Γ : Drawing S) (e r : Set S) : Prop :=
  e ∈ Γ.E ∧ r ∈ Γ.R ∧ (e ∩ closure r).Nonempty

/-- A subset $Z \subseteq \Sigma$ is *$\Gamma$-normal* if $Z \cap U(\Gamma) \subseteq V(\Gamma)$
(equivalently, $Z$ is disjoint from every edge of $\Gamma$).
Graph Minors VI, Section 5 (page 127); Graph Minors VII, Section 2 (page 214);
Graph Minors VIII, Section 5 (page 263); Graph Minors XI, Section 4 (page 78). -/
def IsNormal (Γ : Drawing S) (Z : Set S) : Prop :=
  Z ∩ Γ.U ⊆ Γ.V

/-- A drawing $\Gamma$ in $\Sigma$ is *proper* (or *properly drawn*) if no edge of $\Gamma$ meets
$\operatorname{bd}(\Sigma)$, that is, $\operatorname{bd}(\Sigma)$ is $\Gamma$-normal.
Graph Minors VI, Section 1 (page 116): "A graph $G$ is *properly drawn* on $\Sigma$ if no edge of
$G$ meets $bd(\Sigma)$."
Graph Minors VII, Section 2 (page 214): "A graph $G$ in $\Sigma$ is *proper* if
$\operatorname{bd}(\Sigma)$ is $G$-normal." -/
def IsProper (Γ : Drawing S) : Prop :=
  Γ.IsNormal (bd S)

/-- A drawing $\Gamma'$ is a *subdrawing* of $\Gamma$ ($\Gamma' \subseteq \Gamma$) if
$V(\Gamma') \subseteq V(\Gamma)$ and $E(\Gamma') \subseteq E(\Gamma)$.
Graph Minors XI, Section 3 (page 74). -/
def IsSubdrawing (Γ' Γ : Drawing S) : Prop :=
  Γ'.V ⊆ Γ.V ∧ Γ'.E ⊆ Γ.E

/-- A drawing $\Gamma$ in $\Sigma$ is *2-cell* if $\Sigma$ is connected and every region of $\Gamma$
is an open disc.
Graph Minors XI, Section 3 (page 75): "A painting or drawing $\Gamma$ in $\Sigma$ is *2-cell* if
$\Sigma$ is connected and every region is an open disc (and hence $\Gamma$ is not null)." -/
def IsTwoCell (Γ : Drawing S) : Prop :=
  ConnectedSpace S ∧ ∀ r ∈ Γ.R, IsOpenDisc r

/-- A drawing $\Gamma$ in a connected surface $\Sigma$ is *$\theta$-representative* if every
$\Gamma$-normal $O$-arc $F$ with $|F \cap V(\Gamma)| < \theta$ is null-homotopic in $\Sigma$.
Graph Minors XI, Section 4 (page 78). -/
def IsRepresentative (Γ : Drawing S) (θ : ℕ) : Prop :=
  ConnectedSpace S ∧
    ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.V).ncard < θ → IsNullHomotopicOArc F

/-- Every drawing $\Gamma$ in $\Sigma$ canonically defines an abstract graph
`Γ.toGraph : Graph S (Set S)` with vertex set $V(\Gamma)$, edge set $E(\Gamma)$, and link relation
$\bar{e} \cap V(\Gamma) = \{x, y\}$.
Graph Minors XI, Section 3 (page 74): "If $\Gamma$ is a drawing, then $V(\Gamma)$, $E(\Gamma)$ and
the incidence relation between them define a graph, and in this sense we may regard $\Gamma$ as a
graph, and use graph-theoretic terminology for drawings." -/
def toGraph (Γ : Drawing S) : Graph S (Set S) where
  vertexSet := Γ.V
  edgeSet := Γ.E
  IsLink e x y := e ∈ Γ.E ∧ x ∈ Γ.V ∧ y ∈ Γ.V ∧ closure e ∩ Γ.V = {x, y}
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.2.1, h.2.1, by rw [Set.pair_comm, h.2.2.2]⟩⟩
  eq_or_eq_of_isLink_of_isLink {e x y v w} h1 h2 := by
    have hpair : ({x, y} : Set S) = {v, w} := h1.2.2.2.symm.trans h2.2.2.2
    have hx := Set.mem_insert x {y}
    rw [hpair] at hx
    exact Set.mem_insert_iff.mp hx
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro he
      rcases Γ.edge_cond e he with ⟨u, v, _, hcap, _⟩ | ⟨u, hcap, _⟩
      · have hu : u ∈ Γ.V := by
          have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact Set.mem_insert u {v}
          exact this.2
        have hv : v ∈ Γ.V := by
          have : v ∈ closure e ∩ Γ.V := by rw [hcap]; exact Set.mem_insert_of_mem u rfl
          exact this.2
        exact ⟨u, v, he, hu, hv, hcap⟩
      · have hu : u ∈ Γ.V := by
          have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact Set.mem_singleton u
          exact this.2
        exact ⟨u, u, he, hu, hu, by rw [Set.pair_eq_singleton, hcap]⟩
    · rintro ⟨_, _, he, _, _, _⟩
      exact he
  left_mem_of_isLink _ _ _ h := h.2.1

/-- Every drawing $\Gamma$ also canonically defines an abstract hypergraph
`Γ.toHypergraph : Hypergraph S (Set S)`. -/
def toHypergraph (Γ : Drawing S) : Hypergraph S (Set S) where
  vertexSet := Γ.V
  edgeSet := Γ.E
  Inc e v := e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e
  vertex_mem_of_inc _ _ h := h.2.1
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Γ.finite_V
  edgeSet_finite := Γ.finite_edges

end Drawing

/-- A *drawing of an abstract graph* $G : \operatorname{Graph} \alpha \beta$ in a surface $\Sigma$
is a topological drawing $\Gamma$ in $\Sigma$ together with a graph isomorphism between $G$ and
`Γ.toGraph`.
Graph Minors VI, Section 1 (page 116); Graph Minors VIII, Section 5 (page 262). -/
structure GraphDrawing {α : Type u} {β : Type v} (G : Graph α β)
    (S : Type w) [TopologicalSpace S] where
  /-- The topological drawing $\Gamma$ in $\Sigma$. -/
  drawing : Drawing S
  /-- The isomorphism between the abstract graph $G$ and the geometric graph `drawing.toGraph`. -/
  iso : Iso G drawing.toGraph

/-- A *proper drawing of an abstract graph* $G$ in $\Sigma$ is a drawing of $G$ in $\Sigma$ whose
underlying topological drawing is proper (no edge meets $\operatorname{bd}(\Sigma)$).
Graph Minors VI, Section 1 (page 116). -/
structure ProperGraphDrawing {α : Type u} {β : Type v} (G : Graph α β)
    (S : Type w) [TopologicalSpace S] extends GraphDrawing G S where
  /-- No edge of the drawing meets $\operatorname{bd}(\Sigma)$. -/
  isProper : drawing.IsProper

/-- A *drawing of a graft* $(G, T)$ in $\Sigma$, where $T \subseteq V(G)$, is a proper drawing of
$G$ in $\Sigma$ such that a vertex $v \in V(G)$ is drawn in $\operatorname{bd}(\Sigma)$ if and only
if $v \in T$.
Graph Minors VIII, Section 5 (page 262). -/
structure GraftDrawing {α : Type u} {β : Type v} (G : Graph α β) (T : Set α)
    (S : Type w) [TopologicalSpace S] extends ProperGraphDrawing G S where
  /-- $T$ is a subset of $V(G)$. -/
  T_subset_V : T ⊆ V(G)
  /-- A vertex $v \in V(G)$ maps to $\operatorname{bd}(\Sigma)$ if and only if $v \in T$. -/
  mem_bd_iff : ∀ (v : α) (hv : v ∈ V(G)), (iso.vertexEquiv ⟨v, hv⟩).1 ∈ bd S ↔ v ∈ T

/-! ## 5. Paintings and Radial / Dual Drawings -/

/-- A *painting* $\Gamma = (U, V)$ in a surface $\Sigma$: $V \subseteq U \subseteq \Sigma$, $V$ is
finite, $U - V$ has finitely many arc-wise connected components (called *edges* or *cells*), and
for every edge $e$, $\bar{e}$ is a closed disc and
$\bar{e} \cap V \subseteq \operatorname{bd}(\bar{e})$.
Graph Minors XI, Section 3 (page 75): "A *painting* $\Gamma$ in a surface $\Sigma$ is a pair
$(U, V)$, where $V \subseteq U \subseteq \Sigma$, $V$ is finite, $U - V$ has only finitely many
arc-wise connected components, called *edges*, and for every edge $e$, $\bar{e}$ is a closed disc
and $\bar{e} \cap V \subseteq \operatorname{bd}(\bar{e})$." -/
structure Painting (S : Type u) [TopologicalSpace S] where
  /-- The underlying subset $U(\Gamma) \subseteq \Sigma$. (Unlike a drawing, Graph Minors XI does
  not require $U$ to be closed.) -/
  U : Set S
  /-- The finite set of vertices (or nodes) $V(\Gamma) \subseteq U(\Gamma)$. -/
  V : Set S
  /-- Every vertex lies in $U(\Gamma)$. -/
  V_subset_U : V ⊆ U
  /-- $V(\Gamma)$ is finite. -/
  finite_V : V.Finite
  /-- $U(\Gamma) \setminus V(\Gamma)$ has finitely many arc-wise connected components
  (edges/cells). -/
  finite_edges : (arcComponentsIn (U \ V)).Finite
  /-- Each edge $e$ has closure $\bar{e}$ a closed disc with $\bar{e} \cap V$ in its boundary. -/
  edge_cond : ∀ e ∈ arcComponentsIn (U \ V),
    IsClosedDisc (closure e) ∧ closure e ∩ V ⊆ subBd (closure e)

namespace Painting

variable {S : Type u} [TopologicalSpace S]

/-- The set of *edges* (or *cells*) $E(\Gamma)$ of a painting $\Gamma$.
Graph Minors XI, Section 3 (page 75). -/
def E (Γ : Painting S) : Set (Set S) :=
  arcComponentsIn (Γ.U \ Γ.V)

/-- The set of *regions* $R(\Gamma)$ of a painting $\Gamma$.
Graph Minors XI, Section 3 (page 75). -/
noncomputable def R (Γ : Painting S) : Set (Set S) :=
  componentsIn (Set.univ \ Γ.U)

/-- A subset $Z \subseteq \Sigma$ is *$\Gamma$-normal* for a painting $\Gamma$ if
$Z \cap U(\Gamma) \subseteq V(\Gamma)$.
Graph Minors XI, Section 4 (page 78); Graph Minors XVII, Section 1 (page 165). -/
def IsNormal (Γ : Painting S) (Z : Set S) : Prop :=
  Z ∩ Γ.U ⊆ Γ.V

/-- A painting $\Gamma$ in $\Sigma$ is *2-cell* if $\Sigma$ is connected and every region of
$\Gamma$ is an open disc.
Graph Minors XI, Section 3 (page 75). -/
def IsTwoCell (Γ : Painting S) : Prop :=
  ConnectedSpace S ∧ ∀ r ∈ Γ.R, IsOpenDisc r

/-- Every painting $\Gamma$ in $\Sigma$ canonically defines a hypergraph
`Γ.toHypergraph : Hypergraph S (Set S)` with vertex set $V(\Gamma)$, edge set $E(\Gamma)$, and
incidence $v \in \bar{e}$.
Graph Minors XI, Section 3 (page 75): "If $\Gamma$ is a painting, then $V(\Gamma)$, $E(\Gamma)$ and
the incidence relation between them define a hypergraph, and in this sense we may regard $\Gamma$ as
a hypergraph." -/
def toHypergraph (Γ : Painting S) : Hypergraph S (Set S) where
  vertexSet := Γ.V
  edgeSet := Γ.E
  Inc e v := e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e
  vertex_mem_of_inc _ _ h := h.2.1
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Γ.finite_V
  edgeSet_finite := Γ.finite_edges

end Painting

/-- Pre-conditions (i)–(iv) of a *radial drawing* $\Gamma'$ of a 2-cell drawing $\Gamma$ in
$\Sigma$:
(i) $U(\Gamma) \cap U(\Gamma') = V(\Gamma) \subseteq V(\Gamma')$;
(ii) each region $r$ of $\Gamma$ contains a unique vertex $v_r$ of $\Gamma'$, with
$W = V(\Gamma') \setminus V(\Gamma)$;
(iii) $\Gamma'$ is bipartite with bipartition $(V(\Gamma), W)$;
(iv) if $e, f \in E(\Gamma')$ have the same ends $v \in V(\Gamma)$ and $v_r \in r$, then
$\bar{e} \cup \bar{f}$ does not bound a closed disc in $r \cup \{v\}$.
Graph Minors XI, Section 3 (page 75). -/
def IsPreRadialDrawing {S : Type u} [TopologicalSpace S] (Γ Γ' : Drawing S) : Prop :=
  Γ.U ∩ Γ'.U = Γ.V ∧
  Γ.V ⊆ Γ'.V ∧
  (∀ r ∈ Γ.R, ∃! w, w ∈ r ∧ w ∈ Γ'.V) ∧
  (∀ w ∈ Γ'.V \ Γ.V, ∃ r ∈ Γ.R, w ∈ r) ∧
  (∀ e ∈ Γ'.E, ∃ v ∈ Γ.V, ∃ w ∈ Γ'.V \ Γ.V, closure e ∩ Γ'.V = {v, w}) ∧
  (∀ e ∈ Γ'.E, ∀ f ∈ Γ'.E, e ≠ f → ∀ v ∈ Γ.V, ∀ r ∈ Γ.R, ∀ w ∈ r ∩ Γ'.V,
    closure e ∩ Γ'.V = {v, w} → closure f ∩ Γ'.V = {v, w} →
    ¬ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {v} ∧ subBd Δ = closure e ∪ closure f)

/-- A drawing $\Gamma'$ is a *radial drawing* of a 2-cell drawing $\Gamma$ if it satisfies
(i)–(iv) of `IsPreRadialDrawing` and (v) is maximal subject to (i)–(iv).
Graph Minors XI, Section 3 (page 75). -/
def IsRadialDrawing {S : Type u} [TopologicalSpace S] (Γ Γ' : Drawing S) : Prop :=
  Γ.IsTwoCell ∧ IsPreRadialDrawing Γ Γ' ∧
    ∀ Γ'' : Drawing S, IsPreRadialDrawing Γ Γ'' → Γ'.V = Γ''.V → Γ'.E ⊆ Γ''.E → Γ'.E = Γ''.E

/-- A 2-cell drawing $\Gamma^*$ is a *surface dual* of a 2-cell drawing $\Gamma$ if they share a
common radial drawing $\Gamma'$ with complementary vertex bipartitions
$V(\Gamma^*) = V(\Gamma') \setminus V(\Gamma)$.
Graph Minors XI, Section 6 (page 92). -/
def IsSurfaceDual {S : Type u} [TopologicalSpace S] (Γ Γ_dual : Drawing S) : Prop :=
  Γ.IsTwoCell ∧ Γ_dual.IsTwoCell ∧
    ∃ Γ' : Drawing S, IsRadialDrawing Γ Γ' ∧ IsRadialDrawing Γ_dual Γ' ∧
      Γ_dual.V = Γ'.V \ Γ.V

/-! ## 6. Walks in Drawings, Tracing Curves, and Homotopy of Walks and Forests -/

/-- A *walk* $W = v_0, e_1, v_1, \dots, e_t, v_t$ in an abstract multigraph $G :
\operatorname{Graph} \alpha \beta$.
Graph Minors XI, Section 3 (pages 76–77): "A walk in a drawing $\Gamma$ is a finite sequence
$v_0, e_1, v_1, e_2, \dots, e_t, v_t$ with $t \ge 0$, where $v_0, v_1, \dots, v_t$ are vertices of
$\Gamma$, $e_1, e_2, \dots, e_t$ are edges, and for ... $1 \le i \le t$ the ends of $e_i$ are
$v_{i-1}, v_i$." -/
inductive GraphWalk {α : Type u} {β : Type v} (G : Graph α β) : α → α → Type (max u v)
  | nil {v : α} (hv : v ∈ V(G)) : GraphWalk G v v
  | cons {u v w : α} {e : β} (hlink : G.IsLink e u v) (rest : GraphWalk G v w) :
      GraphWalk G u w

namespace GraphWalk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The list of vertices visited by a walk $W$. -/
def support {u v : α} : GraphWalk G u v → List α
  | .nil _ => [u]
  | .cons _ rest => u :: rest.support

/-- The list of edges traversed by a walk $W$. -/
def edges {u v : α} : GraphWalk G u v → List β
  | .nil _ => []
  | .cons (e := e) _ rest => e :: rest.edges

/-- The length $t$ of a walk $W$.
Graph Minors XI, Section 3 (page 76). -/
def length {u v : α} (W : GraphWalk G u v) : ℕ :=
  W.edges.length

/-- A walk is *simple* (a path) if all its vertices $v_0, v_1, \dots, v_t$ are distinct.
Graph Minors XI, Section 3 (page 76). -/
def IsSimple {u v : α} (W : GraphWalk G u v) : Prop :=
  W.support.Nodup

/-- A closed walk $W$ from $u$ to $u$ is *simple-closed* if $v_1, \dots, v_t$ are distinct and
$e_1, \dots, e_t$ are distinct.
Graph Minors XI, Section 3 (page 76). -/
def IsSimpleClosed {u : α} (W : GraphWalk G u u) : Prop :=
  W.support.tail.Nodup ∧ W.edges.Nodup

end GraphWalk

/-- A multigraph $G$ is a *forest* if it has no simple-closed walks of positive length.
Graph Minors VI, Section 4 (page 122); Graph Minors VII, Section 3 (page 220):
"A *forest* in a surface $\Sigma$ is a proper graph in $\Sigma$ with no circuits." -/
def IsGraphForest {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  ∀ (u : α) (W : GraphWalk G u u), W.IsSimpleClosed → W.length = 0

/-- A curve $\phi \colon [0, 1] \to \Sigma$ *traces* a walk $W$ in a drawing $\Gamma$ if $[0, 1]$
can be subdivided so that each step $e_i$ from $u$ to $v$ is traced in $\bar{e}_i$.
Graph Minors XI, Section 3 (page 77).

In `cons`, `hconcat` does not tie `φ` to `φ₁`: on `[0, t₀]` it only requires `φ 0 = u`,
`φ t₀ = v`, and `φ x ∈ closure e` (not injectivity along `e`, or covering `e` when `u = v`), and
on `[t₀, 1]` it only requires `φ t₀ = v`, `φ 1 = w`, and `φ x ∈ Set.range φ₂` rather than that `φ`
on `[t₀, 1]` reparametrizes `φ₂`, so `φ` on `[t₀, 1]` need not visit the intermediate vertices or
edges of `W` in order. Its uses in `GM07` only rely on `endpoints` (`φ 0 = u ∧ φ 1 = v`),
`range_subset_U` (`Set.range φ ⊆ Γ.U`), `exists_curveTracesWalk`, and transport along
homeomorphisms and `IsCarry` maps. -/
inductive CurveTracesWalk {S : Type u} [TopologicalSpace S] (Γ : Drawing S) :
    ∀ {u v : S}, Curve S → GraphWalk Γ.toGraph u v → Prop
  | nil {v : S} (hv : v ∈ Γ.V) (φ : Curve S) (hconst : ∀ x, φ x = v) :
      CurveTracesWalk Γ φ (.nil hv)
  | cons {u v w : S} {e : Set S} {W : GraphWalk Γ.toGraph v w}
      (hlink : Γ.toGraph.IsLink e u v) (φ₁ φ₂ φ : Curve S)
      (hφ₁ : φ₁ 0 = u ∧ φ₁ 1 = v ∧ Set.range φ₁ ⊆ closure e)
      (hφ₂ : CurveTracesWalk Γ φ₂ W)
      (hconcat : ∃ t₀ : unitInterval, (0 : ℝ) < t₀.1 ∧ t₀.1 < 1 ∧
        φ 0 = u ∧ φ t₀ = v ∧ φ 1 = w ∧
        (∀ x : unitInterval, x.1 ≤ t₀.1 → φ x ∈ closure e) ∧
        (∀ x : unitInterval, t₀.1 ≤ x.1 → φ x ∈ Set.range φ₂)) :
      CurveTracesWalk Γ φ (.cons hlink W)

/-- Two forests $H_1, H_2$ properly drawn on $\Sigma$ are *homotopic* if:
(i) $V(H_1) \cap \operatorname{bd}(\Sigma) = V(H_2) \cap \operatorname{bd}(\Sigma)$, and
(ii) for all distinct $s, t \in V(H_1) \cap \operatorname{bd}(\Sigma)$, there is a path of $H_1$
between $s$ and $t$ if and only if there is such a path in $H_2$, and any curves tracing such paths
are homotopic in $\Sigma$.
Graph Minors VI, Section 4 (page 122); Graph Minors VII, Section 3 (page 220). -/
def ForestsHomotopic {S : Type u} [TopologicalSpace S] (H₁ H₂ : Drawing S) : Prop :=
  H₁.IsProper ∧ H₂.IsProper ∧
  IsGraphForest H₁.toGraph ∧ IsGraphForest H₂.toGraph ∧
  H₁.V ∩ bd S = H₂.V ∩ bd S ∧
  ∀ s ∈ H₁.V ∩ bd S, ∀ t ∈ H₁.V ∩ bd S, s ≠ t →
    ((∃ P₁ : GraphWalk H₁.toGraph s t, P₁.IsSimple) ↔
     (∃ P₂ : GraphWalk H₂.toGraph s t, P₂.IsSimple)) ∧
    (∀ (P₁ : GraphWalk H₁.toGraph s t) (P₂ : GraphWalk H₂.toGraph s t) (φ₁ φ₂ : Curve S),
      P₁.IsSimple → P₂.IsSimple →
      CurveTracesWalk H₁ φ₁ P₁ → CurveTracesWalk H₂ φ₂ P₂ →
      CurvesHomotopic φ₁ φ₂)

end GraphMinor.Surface
