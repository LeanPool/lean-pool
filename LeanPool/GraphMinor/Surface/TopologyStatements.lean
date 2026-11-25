/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The topological facts that Graph Minors VI–XIX use without proof

The papers use several theorems of plane and surface topology without proof, or with a reference
to the literature. This file states each of them as a `Prop`, in the form the papers use it, on
the definitions of `GraphMinor/Surface/Defs.lean`.

The statements, in order:
- the 2-sphere (`IsSphere`), the boundary of a closed disc (`DiscBoundaryStatement`), and cuffs
  (`CuffStatement`);
- the Jordan curve theorem (`JordanCurveStatement`) and the Schoenflies theorem
  (`SchoenfliesStatement`, `SphereDiscStatement`);
- discs: `O`-arcs and proper `I`-arcs in a closed disc (`DiscOArcStatement`, `DiscIArcStatement`),
  union and difference of discs (`DiscUnionStatement`, `DiscDifferenceStatement`), and crossing
  connected sets (`DiscCrossingStatement`);
- the model surfaces $\Sigma(a, b, c)$ (`SurfaceModel`), and their classification
  (`ClassificationStatement`, `ModelCriterionStatement`);
- cutting along arcs and pasting discs (`IsCutting`, `IsSimplerThan`, `CutIArcStatement`,
  `CutOArcStatement`, `PasteDiscStatement`, `SimplerWellFoundedStatement`);
- null-homotopic `O`-arcs (`EpsteinStatement`, `OpenDiscStatement`);
- moving points and arcs by homeomorphisms (`MoveCuffStatement`, `ParallelArcsStatement`,
  `SimilarArcsFiniteStatement`, `PushOffStatement`).

Each statement holds as written for the topological notions of `Defs.lean`. Two points differ from
the loose wording in the papers.

* Crossing connected sets: two arbitrary connected sets in a disc whose ends cross need not meet.
  With the axiom of choice one can split a disc into two disjoint dense connected sets (a
  Bernstein set and its complement). So `DiscCrossingStatement` asks for compact sets, which is
  what the papers use, and `DiscCrossingStatement.of_isPathConnected` deduces the form for
  path-connected sets.
* Parallel arcs: Graph Minors VII, (3.2), claim (1) must also ask that the homeomorphism fixes the
  ends of the arc. See `ParallelArcsStatement`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

/-! ## 1. The sphere, the boundary of a disc, and cuffs -/

/-- `S` is a *2-sphere*: homeomorphic to the one-point compactification of the plane. Mathlib's
`onePointEquivSphereOfFinrankEq` identifies this space with the unit sphere of $\mathbb{R}^3$.
Graph Minors VII, Section 2 (page 213). -/
def IsSphere (S : Type u) [TopologicalSpace S] : Prop :=
  Nonempty (S ≃ₜ OnePoint EuclideanPlane)

/-- The manifold boundary of a closed disc is the image of the unit circle under every
homeomorphism from the closed unit disc onto it. This is the invariance of the boundary, and it
makes `discBd` the boundary that the papers mean. -/
def DiscBoundaryStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (Δ : Set S) (φ : ClosedUnitDisc ≃ₜ Δ),
    discBd Δ = (fun x => (φ x).1) '' {x | x.1 ∈ UnitCircle}

/-- A surface has finitely many cuffs, and each of them is an `O`-arc.
Graph Minors VI, Section 1 (page 116); Graph Minors VII, Section 2 (page 213): "Every cuff is
homeomorphic to the circle $S^1$." -/
def CuffStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S →
    IsClosed (bd S) ∧ (cuffs S).Finite ∧ ∀ C ∈ cuffs S, IsOArc C

/-! ## 2. The Jordan curve theorem and the Schoenflies theorem -/

/-- `A` and `B` are the two components of the complement of `F`, and `F` is the frontier of
each. -/
def IsJordanSplit {S : Type u} [TopologicalSpace S] (F A B : Set S) : Prop :=
  A ≠ B ∧ componentsIn (univ \ F) = {A, B} ∧ frontier A = F ∧ frontier B = F

/-- **Jordan curve theorem.** The complement of an `O`-arc `F` in the plane has exactly two
components, one bounded and one unbounded, and `F` is the frontier of each. The complement of an
`O`-arc in a sphere has exactly two components, and `F` is the frontier of each.
Used in Graph Minors VI, Section 3 (pages 119–121), and throughout the later papers. -/
def JordanCurveStatement : Prop :=
  (∀ F : Set EuclideanPlane, IsOArc F →
    ∃ A B, IsJordanSplit F A B ∧ Bornology.IsBounded A ∧ ¬ Bornology.IsBounded B) ∧
  (∀ (S : Type u) [TopologicalSpace S], IsSphere S → ∀ F : Set S, IsOArc F →
    ∃ A B, IsJordanSplit F A B)

/-- **Schoenflies theorem.** Every homeomorphism from the unit circle onto an `O`-arc of the plane
extends to a homeomorphism of the plane. -/
def SchoenfliesStatement : Prop :=
  ∀ (F : Set EuclideanPlane) (f : UnitCircle ≃ₜ F),
    ∃ g : EuclideanPlane ≃ₜ EuclideanPlane, ∀ x : UnitCircle, g x.1 = (f x).1

/-- An `O`-arc `F` in a sphere is the common boundary of exactly two closed discs. They cover the
sphere, they meet exactly in `F`, and the complement of `F` has the two components `Δ₁ \ F` and
`Δ₂ \ F`.
Graph Minors XI, Section 4 (page 79), treats the sphere separately because of these two sides. -/
def SphereDiscStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSphere S → ∀ F : Set S, IsOArc F →
    ∃ Δ₁ Δ₂ : Set S, Δ₁ ≠ Δ₂ ∧ IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      discBd Δ₁ = F ∧ discBd Δ₂ = F ∧ Δ₁ ∪ Δ₂ = univ ∧ Δ₁ ∩ Δ₂ = F ∧
      componentsIn (univ \ F) = {Δ₁ \ F, Δ₂ \ F} ∧
      ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F → Δ = Δ₁ ∨ Δ = Δ₂

/-! ## 3. Closed discs -/

/-- `Δ` is the closed disc inside the `O`-arc `F` of the closed disc `D`: it lies in `D`, its
boundary is `F`, and `Δ \ F` is a component of `D \ F` that misses the boundary of `D`, the only
such component. -/
def IsInsideDisc {S : Type u} [TopologicalSpace S] (D F Δ : Set S) : Prop :=
  Δ ⊆ D ∧ IsClosedDisc Δ ∧ discBd Δ = F ∧
    Δ \ F ∈ componentsIn (D \ F) ∧ Disjoint (Δ \ F) (discBd D) ∧
    ∀ C ∈ componentsIn (D \ F), Disjoint C (discBd D) → C = Δ \ F

/-- Every `O`-arc `F` in a closed disc `D` bounds a closed disc `Δ ⊆ D`, and `Δ` is the only closed
disc in `D` with boundary `F`. Moreover `Δ \ F` is the unique component of `D \ F` disjoint from
`bd D`. The arc `F` may meet `bd D`, or may equal it, and then `Δ = D`.
Graph Minors VI, Section 4 (pages 122–125); Graph Minors XVII, Section 5 (pages 172–173). -/
def DiscOArcStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (D F : Set S), IsClosedDisc D → F ⊆ D → IsOArc F →
    ∃ Δ : Set S, IsInsideDisc D F Δ ∧
      ∀ Δ' : Set S, Δ' ⊆ D → IsClosedDisc Δ' → discBd Δ' = F → Δ' = Δ

/-- Let `F` be a line in the closed disc `D` with distinct ends `s, t` in `bd D` and no other point
in `bd D`. Then `bd D` minus `{s, t}` has two components `A₁, A₂`, and `F` divides `D` into two
closed discs `Δ₁, Δ₂` that meet exactly in `F`, with boundaries `A₁ ∪ F` and `A₂ ∪ F`. The set
`D \ F` has the two components `Δ₁ \ F` and `Δ₂ \ F`.
Graph Minors VI, (3.1) and (4.2); Graph Minors VII, Section 4 (page 228); Graph Minors XII, (6.1);
Graph Minors XVII, (5.3). -/
def DiscIArcStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (D F : Set S) (s t : S), IsClosedDisc D → F ⊆ D →
    s ≠ t → IsLineWithEnds F s t → F ∩ discBd D = {s, t} →
    ∃ A₁ A₂ Δ₁ Δ₂ : Set S, A₁ ≠ A₂ ∧ componentsIn (discBd D \ {s, t}) = {A₁, A₂} ∧
      IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = D ∧ Δ₁ ∩ Δ₂ = F ∧
      discBd Δ₁ = A₁ ∪ F ∧ discBd Δ₂ = A₂ ∪ F ∧
      componentsIn (D \ F) = {Δ₁ \ F, Δ₂ \ F}

/-- Two closed discs that meet exactly in a line `L` of both boundaries have a closed disc as
union. Its boundary consists of the two boundaries without the interior of `L`.
Graph Minors IX, Section 11 (page 67): "the union of $\Delta_0$ with all lawns is a closed disc";
Graph Minors XI, proof of (6.1) (page 88): "$\Delta = \Delta_1 \cup \Delta_2$ is a closed disc with
$bd(\Delta) = F$." -/
def DiscUnionStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S] (Δ₁ Δ₂ L : Set S) (s t : S),
    IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → IsLineWithEnds L s t → Δ₁ ∩ Δ₂ = L →
    L ⊆ discBd Δ₁ → L ⊆ discBd Δ₂ →
    IsClosedDisc (Δ₁ ∪ Δ₂) ∧ discBd (Δ₁ ∪ Δ₂) = (discBd Δ₁ ∪ discBd Δ₂) \ (L \ {s, t})

/-- Let `Δ₁ ⊆ Δ₂` be closed discs whose boundaries meet exactly in a line `L`. Then
`closure (Δ₂ \ Δ₁)` is a closed disc. Its boundary consists of the two boundaries without the
interior of `L`, and it meets `Δ₁` exactly in the rest of `bd Δ₁`.
Graph Minors XI, proof of (6.1) (page 88): "If $\Delta_1 \subseteq \Delta_2$ then since
$F_1 \cap F_2 = F'$, it follows that $\Delta = \overline{\Delta_2 - \Delta_1}$ is a closed disc
and $bd(\Delta) = F$." -/
def DiscDifferenceStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S] (Δ₁ Δ₂ L : Set S) (s t : S),
    IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → Δ₁ ⊆ Δ₂ → IsLineWithEnds L s t →
    discBd Δ₁ ∩ discBd Δ₂ = L →
    IsClosedDisc (closure (Δ₂ \ Δ₁)) ∧
      discBd (closure (Δ₂ \ Δ₁)) = (discBd Δ₁ ∪ discBd Δ₂) \ (L \ {s, t}) ∧
      closure (Δ₂ \ Δ₁) ∩ Δ₁ = discBd Δ₁ \ (L \ {s, t})

/-- Two compact connected sets in a closed disc `D` meet if their ends cross on `bd D`.
Graph Minors VI, Sections 2 and 3; Graph Minors IX, Section 1 (page 41). The sets of the papers
are paths and connected subgraphs of drawings, which are compact. For arbitrary connected sets
the statement fails (see the module docstring). -/
def DiscCrossingStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (D A B : Set S) (a c b d : S),
    IsClosedDisc D → A ⊆ D → B ⊆ D → IsCompact A → IsCompact B →
    IsConnected A → IsConnected B → a ∈ A → c ∈ A → b ∈ B → d ∈ B →
    PairsCrossOn (discBd D) a c b d → (A ∩ B).Nonempty

/-- `DiscCrossingStatement` for path-connected sets: the ends lie on compact paths inside the two
sets. -/
theorem DiscCrossingStatement.of_isPathConnected (h : DiscCrossingStatement.{u})
    {S : Type u} [TopologicalSpace S] (D A B : Set S) (a c b d : S)
    (hD : IsClosedDisc D) (hA : A ⊆ D) (hB : B ⊆ D)
    (hA' : IsPathConnected A) (hB' : IsPathConnected B)
    (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (hcross : PairsCrossOn (discBd D) a c b d) : (A ∩ B).Nonempty := by
  obtain ⟨p, hp⟩ := hA'.joinedIn a ha c hc
  obtain ⟨q, hq⟩ := hB'.joinedIn b hb d hd
  have hprange : range p ⊆ A := by rintro _ ⟨x, rfl⟩; exact hp x
  have hqrange : range q ⊆ B := by rintro _ ⟨x, rfl⟩; exact hq x
  have hmeet := h D (range p) (range q) a c b d hD (hprange.trans hA) (hqrange.trans hB)
    (isCompact_range p.continuous) (isCompact_range q.continuous)
    (isConnected_range p.continuous) (isConnected_range q.continuous)
    ⟨0, p.source⟩ ⟨1, p.target⟩ ⟨0, q.source⟩ ⟨1, q.target⟩ hcross
  exact hmeet.mono (inter_subset_inter hprange hqrange)

/-! ## 4. The surfaces $\Sigma(a, b, c)$ and their classification -/

/-- The centre $(3i, 0)$ of the `i`-th deleted disc of the model surfaces. Any two of the unit
discs around these points are disjoint. -/
noncomputable def modelCentre (i : ℕ) : EuclideanPlane :=
  !₂[3 * (i : ℝ), 0]

/-- The mirror image $(x, -y)$ of $(x, y)$. -/
noncomputable def modelMirror (u : EuclideanPlane) : EuclideanPlane :=
  !₂[u 0, -u 1]

/-- The sphere with the interiors of `n` pairwise disjoint closed discs removed: the points of
the one-point compactification of the plane outside the first `n` open unit discs around the
points `modelCentre i`. -/
def modelBase (n : ℕ) : Set (OnePoint EuclideanPlane) :=
  {p | ∀ i < n, ∀ x : EuclideanPlane, p = x → 1 ≤ dist x (modelCentre i)}

/-- The identifications that add `a` handles and `b` cross-caps to the sphere with holes. The
circles around centres `2i` and `2i + 1` with `i < a` are pasted to each other by the mirror map
(this map reverses the boundary orientation, so the result is a handle). Antipodal points of the
circle around centre `2a + i` with `i < b` are pasted to each other (this is a cross-cap). -/
inductive ModelGlue (a b n : ℕ) : modelBase n → modelBase n → Prop
  | handle (i : ℕ) (hi : i < a) (u : EuclideanPlane) (hu : ‖u‖ = 1) (p q : modelBase n)
      (hp : p.1 = ((modelCentre (2 * i) + u : EuclideanPlane) : OnePoint EuclideanPlane))
      (hq : q.1 = ((modelCentre (2 * i + 1) + modelMirror u : EuclideanPlane) :
        OnePoint EuclideanPlane)) : ModelGlue a b n p q
  | crosscap (i : ℕ) (hi : i < b) (u : EuclideanPlane) (hu : ‖u‖ = 1) (p q : modelBase n)
      (hp : p.1 = ((modelCentre (2 * a + i) + u : EuclideanPlane) : OnePoint EuclideanPlane))
      (hq : q.1 = ((modelCentre (2 * a + i) - u : EuclideanPlane) : OnePoint EuclideanPlane)) :
      ModelGlue a b n p q

/-- $\Sigma(a, b, c)$: the surface obtained from a 2-sphere by adding `a` handles and `b`
cross-caps,
and then removing the interiors of `c` pairwise disjoint closed discs.
Graph Minors VII, Section 2 (page 213); Graph Minors VIII, Section 5 (page 262); Graph Minors
XVII, Section 1 (page 163). Here we remove the interiors of `2a + b + c` discs from the sphere,
paste the boundaries of the first `2a + b` of them as in `ModelGlue`, and keep the remaining `c`
as cuffs. This is the model that Graph Minors VI, Section 1 (page 116), describes. -/
def SurfaceModel (a b c : ℕ) : Type :=
  Quot (ModelGlue a b (2 * a + b + c))

noncomputable instance (a b c : ℕ) : TopologicalSpace (SurfaceModel a b c) :=
  inferInstanceAs (TopologicalSpace (Quot (ModelGlue a b (2 * a + b + c))))

/-- **Classification of surfaces, part (i).** Every connected surface is homeomorphic to
$\Sigma(a, b, c)$ for some $a, b, c$.
Graph Minors VII, Section 2 (page 213); Graph Minors XVII, (1.1)(i) (page 163). -/
def ClassificationStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S →
    ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c)

/-- **Classification of surfaces, part (ii).** The models are surfaces, and
$\Sigma(a, b, c) \cong \Sigma(a', b', c')$ if and only if $c = c'$, $2a + b = 2a' + b'$, and both or
neither of $b, b'$ are zero.
Graph Minors XVII, (1.1)(ii) (page 163). The printed "$a + 2b = a' + 2b'$" is a slip: page 164
uses $2a + b$, and $\Sigma(1, 1, 0) \cong \Sigma(0, 3, 0)$ is the classical relation it must allow.
-/
def ModelCriterionStatement : Prop :=
  (∀ a b c : ℕ, IsSurface (SurfaceModel a b c) ∧ ConnectedSpace (SurfaceModel a b c)) ∧
  ∀ a b c a' b' c' : ℕ, Nonempty (SurfaceModel a b c ≃ₜ SurfaceModel a' b' c') ↔
    c = c' ∧ 2 * a + b = 2 * a' + b' ∧ (b = 0 ↔ b' = 0)

/-! ## 5. Cutting along arcs and pasting discs -/

/-- `X` is *simpler than* `Y`, for connected surfaces: there are $a \le a'$ and $b \le b'$ with
$X \cong \Sigma(a, b, c)$, $Y \cong \Sigma(a', b', c')$ and $4a + 2b + c < 4a' + 2b' + c'$.
Graph Minors XVII, Section 1 (page 164), second form.

The paper first gives another condition, on any representations: (i) if $b' = 0$ then $b = 0$;
(ii) $2a + b \le 2a' + b'$; (iii) $4a + 2b + c < 4a' + 2b' + c'$. It calls the two equivalent, but
they are not: $\Sigma(1, 0, 0)$ and $\Sigma(0, 2, 1)$ meet (i) to (iii), and the only representation
of $\Sigma(0, 2, 1)$ with $b' \neq 0$ has $a' = 0$. The proof of (13.4) (page 207) needs that a
graph
drawn in a simpler surface can be drawn in the larger one, and this needs the second form. The first
form follows from the second, by `IsSimplerThan.conditions`. -/
def IsSimplerThan (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Prop :=
  ∃ a b c a' b' c' : ℕ, Nonempty (X ≃ₜ SurfaceModel a b c) ∧ Nonempty (Y ≃ₜ SurfaceModel a' b' c') ∧
    a ≤ a' ∧ b ≤ b' ∧ 4 * a + 2 * b + c < 4 * a' + 2 * b' + c'

/-- The paper's first form of "simpler" follows from the second. -/
theorem IsSimplerThan.conditions {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (h : IsSimplerThan X Y) :
    ∃ a b c a' b' c' : ℕ, Nonempty (X ≃ₜ SurfaceModel a b c) ∧ Nonempty
      (Y ≃ₜ SurfaceModel a' b' c') ∧
      (b' = 0 → b = 0) ∧ 2 * a + b ≤ 2 * a' + b' ∧ 4 * a + 2 * b + c < 4 * a' + 2 * b' + c' := by
  obtain ⟨a, b, c, a', b', c', hX, hY, h1, h2, h3⟩ := h
  exact ⟨a, b, c, a', b', c', hX, hY, by omega, by omega, h3⟩

/-- The relation "simpler than" on spaces is well-founded. Graph Minors VII, VIII, XVII and XIX
use induction along it. -/
def SimplerWellFoundedStatement : Prop :=
  WellFounded fun X Y : (Σ X : Type u, TopologicalSpace X) =>
    @IsSimplerThan X.1 Y.1 X.2 Y.2

/-- `ψ : S' → S` is the surjection associated with cutting `S` along `F`: it is a continuous
surjection, it is injective off `F`, every point of `F` has exactly two preimages, and these
preimages lie in the boundary of `S'`.
Graph Minors VII, Section 2 (page 214): pasting and cutting of arcs; (4.4) and (4.5) use "the
associated surjection". -/
def IsCutting {S' S : Type u} [TopologicalSpace S'] [TopologicalSpace S]
    (ψ : S' → S) (F : Set S) : Prop :=
  Continuous ψ ∧ Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' Fᶜ) ∧
    (∀ x ∈ F, (ψ ⁻¹' {x}).ncard = 2) ∧ ψ ⁻¹' F ⊆ bd S'

/-- The set of components of a space, as subsets. -/
noncomputable def spaceComponents (S : Type u) [TopologicalSpace S] : Set (Set S) :=
  componentsIn univ

/-- Every component of `S'` is simpler than `S`, and `S'` has one or two components. These are the
cases "(i) a connected surface simpler than $\Sigma$" and "(ii) a surface with two components, both
simpler than $\Sigma$" of Graph Minors XVII, Section 1 (page 164). -/
def CutIsSimpler (S' S : Type u) [TopologicalSpace S'] [TopologicalSpace S] : Prop :=
  (spaceComponents S').encard ≤ 2 ∧ ∀ C ∈ spaceComponents S', IsSimplerThan C S

/-- `S'` has exactly two components, one of them a closed disc. -/
def CutHasDisc (S' : Type u) [TopologicalSpace S'] : Prop :=
  ∃ C₁ C₂ : Set S', C₁ ≠ C₂ ∧ spaceComponents S' = {C₁, C₂} ∧ IsClosedDisc C₁

/-- `S'` has exactly two components, one homeomorphic to `X` and the other homeomorphic to `S`. -/
def CutHasCopy (S' S X : Type*) [TopologicalSpace S'] [TopologicalSpace S]
    [TopologicalSpace X] : Prop :=
  ∃ C₁ C₂ : Set S', C₁ ≠ C₂ ∧ spaceComponents S' = {C₁, C₂} ∧
    Nonempty (C₁ ≃ₜ X) ∧ Nonempty (C₂ ≃ₜ S)

/-- Cutting along an `I`-arc. Let `F` be a proper `I`-arc with ends `s, t` of a connected surface
`S`. Cutting along `F` gives a surface `S'`. If the ends lie in different cuffs, then `S'` is
connected with one cuff fewer. If they lie in the same cuff, then `S'` is either (i) connected and
simpler than `S`, (ii) two components, both simpler than `S`, or (iii) two components, one a
closed disc and the other homeomorphic to `S`. The preimage of `F` is two disjoint lines `X, Y` in
the boundary of `S'`, and `S` arises from `S'` by pasting them (these are the arcs $X, Y$ of the
proof of Graph Minors VII, (3.1), page 218).
Graph Minors XVII, Section 1 (page 164). -/
def CutIArcStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (F : Set S) (s t : S), IsSurface S → ConnectedSpace S →
    s ≠ t → F ∩ bd S = {s, t} → IsLineWithEnds F s t →
    ∃ (S' : Type u) (_ : TopologicalSpace S') (ψ : S' → S), IsSurface S' ∧ IsCutting ψ F ∧
      (connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t →
        ConnectedSpace S' ∧ ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b (c + 1)) ∧
          Nonempty (S' ≃ₜ SurfaceModel a b c)) ∧
      (connectedComponentIn (bd S) s = connectedComponentIn (bd S) t →
        CutIsSimpler S' S ∨ CutHasCopy S' S ClosedUnitDisc) ∧
      ∃ X Y : Set S', Disjoint X Y ∧ X ∪ Y = ψ ⁻¹' F ∧ IsLine X ∧ IsLine Y ∧
        BijOn ψ X F ∧ BijOn ψ Y F

/-- Cutting along an `O`-arc. Let `F` be an `O`-arc disjoint from the boundary of a connected
surface `S`. Cutting along `F` gives a surface `S'` that is either (i) connected and simpler than
`S`, (ii) two components, both simpler than `S`, (iii) two components, one a cylinder and the other
homeomorphic to `S`, or (iv) two components, one a closed disc. The preimage of `F` is two disjoint
`O`-arcs that `ψ` maps bijectively onto `F` (if `F` is two-sided), or one `O`-arc (if `F` is
one-sided).
Graph Minors XVII, Section 1 (page 164). -/
def CutOArcStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (F : Set S), IsSurface S → ConnectedSpace S →
    IsOArc F → Disjoint F (bd S) →
    ∃ (S' : Type u) (_ : TopologicalSpace S') (ψ : S' → S), IsSurface S' ∧ IsCutting ψ F ∧
      (CutIsSimpler S' S ∨ CutHasCopy S' S ClosedCylinder ∨ CutHasDisc S') ∧
      ((∃ X Y : Set S', Disjoint X Y ∧ X ∪ Y = ψ ⁻¹' F ∧ IsOArc X ∧ IsOArc Y ∧
        BijOn ψ X F ∧ BijOn ψ Y F) ∨ IsOArc (ψ ⁻¹' F))

/-- Pasting a closed disc onto a cuff `C` of `S` gives a surface `S'`: `S` embeds in `S'` as a
closed set, and the rest of `S'` is the interior of a closed disc `Δ` with
$\Delta \cap S = \operatorname{bd}(\Delta) = C$. Its boundary is `bd S` without `C`.
Graph Minors VII, Section 4 (page 224); Graph Minors VIII, Section 18 (page 285); Graph Minors
XIX, Section 2 (page 327). -/
def PasteDiscStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (C : Set S), IsSurface S → IsCuff C →
    ∃ (S' : Type u) (_ : TopologicalSpace S') (ι : S → S') (Δ : Set S'),
      IsSurface S' ∧ IsClosedEmbedding ι ∧ IsClosedDisc Δ ∧ range ι ∪ Δ = univ ∧
      range ι ∩ Δ = ι '' C ∧ discBd Δ = ι '' C ∧ bd S' = ι '' (bd S \ C)

/-! ## 6. Null-homotopic `O`-arcs -/

/-- **Disc bounding for null-homotopic curves.** Let `S` be a connected surface, and let
`F ⊆ Z` be an `O`-arc disjoint from `bd S`. Then `F` is null-homotopic in `Z` if and only if
`F` bounds a closed disc included in `Z`. This is equivalent to `F` lying inside a closed disc
included in `Z`. If `S` is
not a sphere, a closed disc bounded by `F` is unique.
Graph Minors VII, Section 2 (page 214), citing H. I. Levine, *Homotopic curves on surfaces*;
Epstein's *Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966) 83–107, Theorem 1.7,
gives ambient disc bounding and is quoted as Graph Minors XI (7.1). Robertson and Seymour's
XI (7.2) (page 93) gives disc containment in the subset `Z`. -/
def EpsteinStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (Z F : Set S), IsSurface S → ConnectedSpace S →
    IsOArc F → F ⊆ Z → Disjoint F (bd S) →
    (IsNullHomotopicOArcIn Z F → ∃ Δ : Set S, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ discBd Δ = F) ∧
    ((∃ Δ : Set S, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ F ⊆ Δ) → IsNullHomotopicOArcIn Z F) ∧
    (∀ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → discBd Δ₁ = F → discBd Δ₂ = F →
      ¬ IsSphere S → Δ₁ = Δ₂)

/-- Graph Minors VII, (4.2) (page 222): "Let $\Sigma$ be a connected surface with
$bd(\Sigma) = \emptyset$, and let $Y \subseteq \Sigma$ be connected and open. Suppose that every
$O$-arc included in $Y$ bounds a disc included in $Y$. Then either $\Sigma$ is a sphere and
$Y = \Sigma$, or $Y$ is an open disc." -/
def OpenDiscStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (Y : Set S), IsClosedSurface S → ConnectedSpace S →
    IsConnected Y → IsOpen Y →
    (∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F) →
    (IsSphere S ∧ Y = univ) ∨ IsOpenDisc Y

/-! ## 7. Moving points and arcs by homeomorphisms -/

/-- A homeomorphism of the circle *preserves orientation* if it lifts to an increasing continuous
map of the real line. -/
def PreservesCircleOrientation (h : Circle ≃ₜ Circle) : Prop :=
  ∃ l : ℝ → ℝ, Continuous l ∧ StrictMono l ∧ ∀ t : ℝ, h (Circle.exp t) = Circle.exp (l t)

/-- Let `C` be a cuff of a surface `S` with arc-map `φ`, and let `h` be an orientation-preserving
homeomorphism of the circle. Then the homeomorphism $\varphi h \varphi^{-1}$ of `C` extends to a
homeomorphism of `S` that is the identity outside any given open set `U ⊇ C`, so in particular on
all other cuffs. This moves finite sets of boundary points in the same circular order onto each
other.
Graph Minors VII, Section 3 (pages 218–221); Graph Minors XIX, Section 3 (page 330) and proof of
(2.1) ("replacing each $\Gamma_i$ by its image under a suitable homeomorphism"). -/
def MoveCuffStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (C U : Set S) (φ : Circle ≃ₜ C) (h : Circle ≃ₜ Circle),
    IsSurface S → IsCuff C → IsOpen U → C ⊆ U → PreservesCircleOrientation h →
    ∃ α : S ≃ₜ S, (∀ x : Circle, α (φ x).1 = (φ (h x)).1) ∧ ∀ x ∉ U, α x = x

/-- `α` maps every cuff to itself, preserving its orientation. This is the "null signature" of
Graph Minors VII, (3.2) (page 219). -/
def HasNullSignature {S : Type u} [TopologicalSpace S] (α : S ≃ₜ S) : Prop :=
  ∀ (C : Set S) (φ : Circle ≃ₜ C), C ∈ cuffs S →
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ ∀ x, α (φ x).1 = (φ (h x)).1

/-- Graph Minors VII, (3.2), claim (1) (page 219): if `F, F'` are proper `I`-arcs with the same
ends `s, t`, and a homeomorphism `α` with null signature maps `F` to `F'` and fixes `s` and `t`,
then `F` and `F'` are parallel: a homeomorphism fixing `bd S` pointwise maps `F` to `F'`.

The paper does not ask that `α` fixes the ends. This is needed: take an annulus with `s, t`
antipodal on one cuff, and two arcs with these ends on the two sides of the hole. A rotation by a
half turn swaps them and has null signature, yet each arc cuts off a different part of the cuff. -/
def ParallelArcsStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] (F F' : Set S) (s t : S) (α : S ≃ₜ S), IsSurface S →
    s ≠ t → F ∩ bd S = {s, t} → F' ∩ bd S = {s, t} → IsLineWithEnds F s t → IsLineWithEnds F' s t →
    α '' F = F' → α s = s → α t = t → HasNullSignature α →
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x

/-- Graph Minors VII, (3.1) (page 218): a surface has only finitely many similarity classes of
proper `I`-arcs, where two arcs are similar if a homeomorphism of the surface maps one to the
other. The paper's proof reduces this to the classification and to cutting along the arc. -/
def SimilarArcsFiniteStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S →
    ∃ 𝓕 : Set (Set S), 𝓕.Finite ∧ ∀ F : Set S, IsProperIArc F →
      ∃ F₀ ∈ 𝓕, ∃ α : S ≃ₜ S, α '' F₀ = F

/-- The step that makes a disc narrow, as a statement on surfaces: an `O`-arc that misses the chords
of
some discs can be pushed off these discs by a homeomorphism of the surface that fixes the nodes.
Here the
discs `D i` meet each other and the closed set `Z` only in the finite set `N`, and each disc has
exactly
two points in `N`, on its boundary. The line `L i` joins these two points. Either it runs through
the
interior of `D i`, and then `D i` meets `bd(Σ)` only in `N`, or it is `D i ∩ bd(Σ)`.

This is the content of the paper's "make the discs narrow" (Graph Minors XX, Section 8, page 348).
-/
def PushOffStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S], IsSurface S → ∀ (ι : Type) [Finite ι] (N Z : Set S)
    (D L : ι → Set S), N.Finite → IsClosed Z → (∀ i, IsClosedDisc (D i)) →
    (∀ i, ∃ a b, IsLineWithEnds (L i) a b ∧ D i ∩ N = {a, b} ∧ a ∈ discBd (D i) ∧
      b ∈ discBd (D i) ∧ L i ⊆ D i ∧
      ((L i \ {a, b} ⊆ D i \ discBd (D i) ∧ D i ∩ bd S ⊆ N) ∨ L i = D i ∩ bd S)) →
    (∀ i j, i ≠ j → D i ∩ D j ⊆ N) → (∀ i, D i ∩ Z ⊆ N) →
    ∀ F : Set S, IsOArc F → F ∩ Z ⊆ N → (∀ i, F ∩ L i ⊆ N) →
    ∃ h : S ≃ₜ S, (∀ n ∈ N, h n = n) ∧ (h '' F) ∩ Z ⊆ N ∧ ∀ i, (h '' F) ∩ D i ⊆ N

end GraphMinor.Surface
