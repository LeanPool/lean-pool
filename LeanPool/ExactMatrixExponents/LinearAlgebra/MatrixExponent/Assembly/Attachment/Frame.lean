/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Packing.Frame
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Serial

/-!
# Keeping frozen tables while the core moves

A second local record contains the full border and the tether endpoints.
Host addresses and the block number are shared with the core record. The
first station slot is reserved for the core, even if it is empty.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly
open Coloring Packing

/-- The data for the attachment construction, including `k`, `e`, `ℓ`, `decode`, `live`. -/
structure Attachment {F : Type} (D : Template F) where
  /-- The `Attachment` field of type `ℕ`. -/
  k : ℕ
  /-- The `Attachment` field of type `ℕ`. -/
  e : ℕ
  /-- The `Attachment` field of type `ℕ`. -/
  ℓ : ℕ
  /-- The `Attachment` component of type `B ℓ → Pattern F D.scheme.d k e`. -/
  decode : B ℓ → Pattern F D.scheme.d k e
  /-- The `Attachment` component of type `B ℓ → B k → Bool`. -/
  live : B ℓ → B k → Bool
  /-- The `Attachment` component of type `B ℓ → B k → ℝ`. -/
  charge : B ℓ → B k → ℝ
  /-- Embeds the coordinates as `B D.scheme.e ↪ B e`. -/
  coreSpan : B D.scheme.e ↪ B e

namespace Attachment

variable {F T : Type} {D : Template F} (A : Attachment D)

/-- Uses `⟨D.scheme.m, D.scheme.d, D.scheme.h, A.k, A.e, A.ℓ, A.decode⟩` as the representation. -/
abbrev scheme : Scheme F :=
  ⟨D.scheme.m, D.scheme.d, D.scheme.h, A.k, A.e, A.ℓ, A.decode⟩

/-- The value specified by `Format.vec D.scheme.m (.vec D.scheme.h (.addr A.ℓ))`. -/
abbrev label := Format.vec D.scheme.m (.vec D.scheme.h (.addr A.ℓ))

/-- Computes the format by the application `D.format.pair A.label`. -/
abbrev format := D.format.pair A.label

/-- Evaluates `(D.nav r.1 v, r.2 v)` at the input `v`. -/
def rows (r : A.format.obj) : A.scheme.format.obj :=
  fun v => (D.nav r.1 v, r.2 v)

theorem width : A.format.width = D.format.width + 2 ^ D.scheme.m * (2 ^ D.scheme.h * A.ℓ) := by
  simp only [format, label, Format.width_pair, Format.width_vec, Format.width_addr]

variable [Field F] [Fintype T] {x y a b : Wire} {u : ℕ} {L : Fringe x y T}
variable (r : A.format.obj) (G : HostNet F L D.scheme.h u) (Z : Border F T a b x y)

/-- The core and the border records must describe the same individual
core bits, in order. A frozen table is kept on its own assigned slot. -/
structure Encloses where
  full : D.full = true
  tether : L.tensor = Z.tensor
  /-- The `Encloses` component of type `D.Encodes r.1 G`. -/
  core : D.Encodes r.1 G
  /-- The `Encloses` component of type `A.scheme.Presentation (A.rows r) (Z.attach G.diagram)`. -/
  pres : A.scheme.Presentation (A.rows r) (Z.attach G.diagram)
  directed : pres.Directed
  occupied : ∀ v : A.scheme.Vtx, A.live (r.2 v.1 v.2.1) v.2.2 = true ↔ v ∈ Set.range pres.vertex
  /-- The `Encloses` component of type `T → B A.k`. -/
  slot : T → B A.k
  positive : ∀ t, slot t ≠ 0
  internal : ∀ v, pres.vertex (.inl v) =
    (core.post.host (G.units.place v).1, core.post.block (G.units.place v).2, 0)
  frozen : ∀ t, pres.vertex (.inr t) =
    (core.post.host (G.park t).1, core.post.block (G.park t).2, slot t)
  charge : ∀ t, A.charge (r.2 (core.post.host (G.park t).1) (core.post.block (G.park t).2))
    (slot t) = L.charge t
  ordered : ∀ v (j : G.diagram.Port v),
    (pres.pin (.inl v) j).1 = A.coreSpan (core.post.pin v j).1 ∧
      (pres.pin (.inl v) j).2.val = (core.post.pin v j).2.val

variable {r G Z A}

theorem Encloses.distinct (q : A.Encloses r G Z) {v w : T}
    (h : G.park v = G.park w) (hs : q.slot v = q.slot w) : v = w := by
  apply Sum.inr.inj
  apply q.pres.vertex.injective
  rw [q.frozen, q.frozen, h, hs]

end Attachment
end MatrixMultiplicationAllFields.MatrixExponent.Assembly
end

/- # Common stage boundary while the border is retained -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Attachment
open Packing Coloring

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
    (x y : Wire) (u height : ℕ)

/-- The data for the data construction, including `T`, `[finite`, `a`, `b`, `L`. -/
structure Data where
  /-- The `Data` component of type `Type`. -/
  T : Type
  [finite : Fintype T]
  /-- The left component of type `Wire`. -/
  a : Wire
  /-- The right component of type `Wire`. -/
  b : Wire
  /-- The `Data` component of type `Fringe a b T`. -/
  L : Fringe a b T
  /-- The `Data` component of type `HostNet F L D.scheme.h u`. -/
  G : HostNet F L D.scheme.h u
  /-- The `Data` component of type `Border F T x y a b`. -/
  Z : Border F T x y a b
  /-- The `Data` component of type `A.format.obj`. -/
  raw : A.format.obj
  /-- The `Data` component of type `A.Encloses raw G Z`. -/
  q : A.Encloses raw G Z

attribute [instance] Data.finite

/-- The quantity computed by `2 ^ m + wd x + wd y`. -/
abbrev volume (m : ℕ) := 2 ^ m + wd x + wd y
/-- The value specified by `Fmt.payload m (volume x y m) height`. -/
abbrev payload (m : ℕ) := Fmt.payload m (volume x y m) height
/-- Computes the port by the application `A.format.pair (payload x y height D.scheme.m)`. -/
abbrev port := A.format.pair (payload x y height D.scheme.m)

namespace Data
variable {A x y u height} (X : Data A x y u)

/-- Computes the diagram by the application `X.Z.attach X.G.diagram`. -/
abbrev diagram := X.Z.attach X.G.diagram
/-- The value specified by `A.scheme.Fits (A.rows X.raw) (volume x y D.scheme.m) height`. -/
abbrev Fits (height : ℕ) := A.scheme.Fits (A.rows X.raw) (volume x y D.scheme.m) height

/-- Computes the data by the application `A.scheme.store _ fit (X.q.pres.exterior i j)`. -/
def data (fit : X.Fits height) (i : Val x) (j : Val y) : (payload x y height D.scheme.m).obj :=
  A.scheme.store _ fit (X.q.pres.exterior i j)

/-- The condition `∀ v, X.G.diagram.arity v = 0 → ∀ t, Transcript.sample (X.G.diagram.table v) t
= 1` on the specified data. -/
def Neutral := ∀ v, X.G.diagram.arity v = 0 → ∀ t, Transcript.sample (X.G.diagram.table v) t = 1

end Data

/-- Builds `Assembly.Snapshot.{1} F x y where state` with the specified `state`, `eval`, `port`,
`encode`. -/
def frame (P : Data A x y u → Prop) : Assembly.Snapshot.{1} F x y where
  state := {X : Data A x y u // P X ∧ X.Fits height}
  eval i := i.val.diagram.eval
  port := A.port x y height
  encode i a b := (i.val.raw, i.val.data i.property.2 a b)

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Attachment
end
