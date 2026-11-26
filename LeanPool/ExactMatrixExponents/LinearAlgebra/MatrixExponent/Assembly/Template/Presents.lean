/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Group.Model
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Boundary
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.History.Dense
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Bins
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Serial
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Local
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Group.ChildPaths

/-!
# A uniform representation of intermediate core networks

The scheme contains the table and port data. At each host a common
header records occupancy, frozen status and graph masks. A short
second field in each block encodes its load and history counters.
The decoder and the ordering for measuring tag lengths are shared
by all branches at this stage.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly
open Coloring Packing

open scoped Classical in
/-- The data for the template construction, including `scheme`, `count`, `load`, `park`, `past`. -/
structure Template (F : Type) where
  /-- The `Template` component of type `Scheme F`. -/
  scheme : Scheme F
  /-- The number of entries. -/
  count : ℕ
  /-- The `Template` component of type `B count → ℝ`. -/
  load : B count → ℝ
  /-- The `Template` component of type `B count → ℝ`. -/
  park : B count → ℝ
  /-- The `Template` component of type `B count → ℕ`. -/
  past : B count → ℕ
  /-- Reindexes the data using `B scheme.ℓ ≃ B scheme.ℓ`. -/
  order : B scheme.ℓ ≃ B scheme.ℓ
  /-- The `Template` component of type `Bool`. -/
  full : Bool := true

namespace Template
variable {F T : Type} (D : Template F)

open scoped Classical in
/-- Computes the header by the application `Format.pair (.pair .bit .bit) (.pair (Group.Flags
D.scheme.d) (.vec D.scheme.h (.addr D.count)))`. -/
abbrev header := Format.pair (.pair .bit .bit)
  (.pair (Group.Flags D.scheme.d) (.vec D.scheme.h (.addr D.count)))

open scoped Classical in
/-- Computes the format by the application `D.scheme.format.pair (.vec D.scheme.m D.header)`. -/
abbrev format := D.scheme.format.pair (.vec D.scheme.m D.header)

open scoped Classical in
theorem width : D.format.width = 2 ^ D.scheme.m *
    (2 ^ D.scheme.d * (D.scheme.m + 2) + 2 + 2 ^ D.scheme.h * (D.scheme.ℓ + D.count)) := by
  simp only [format, header, Scheme.format, Fmt.rows, Group.Flags, Format.width_pair,
    Format.width_vec,
    Format.width_addr]
  rw [Format.width_bit]
  ring

open scoped Classical in
theorem scheme_width_le : D.scheme.format.width ≤ D.format.width := by
  rw [Format.width_pair]
  exact Nat.le_add_right ..

variable (r : D.format.obj)

open scoped Classical in
/-- The value specified by `(r.1 i).1`. -/
abbrev nav (i : B D.scheme.m) := (r.1 i).1
open scoped Classical in
/-- The value specified by `(r.2 i).1.1`. -/
abbrev live (i : B D.scheme.m) := (r.2 i).1.1
open scoped Classical in
/-- The value specified by `(r.2 i).1.2`. -/
abbrev frozen (i : B D.scheme.m) := (r.2 i).1.2
open scoped Classical in
/-- The value specified by `(r.2 i).2.1`. -/
abbrev flags (i : B D.scheme.m) := (r.2 i).2.1
open scoped Classical in
/-- The value specified by `(r.2 i).2.2`. -/
abbrev counter (i : B D.scheme.m) := (r.2 i).2.2

variable [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  (G : HostNet F L D.scheme.h u)

open scoped Classical in
/-- If noncore propagation is too slow to cross an edge in one
phase, the controller need only store the core graph. -/
abbrev adj := if D.full then G.N else G.C

open scoped Classical in
/-- The data for the encodes construction, including `post`, `block`, `live`, `frozen`,
`closed`. -/
structure Encodes where
  /-- The `Encodes` component of type `D.scheme.Posting r.1 G`. -/
  post : D.scheme.Posting r.1 G
  block : ∀ i, post.block i = cellIndex _ i
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range post.host
  frozen : ∀ v, D.frozen r (post.host v) = true ↔ G.frozen v
  closed : ∀ v j, D.nav r (post.host v) j ∈ Set.range post.host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ D.adj G v ↔ ∃ j, D.nav r (post.host v) j = post.host w ∧
    (D.flags r (post.host v) j).1 = true
  core : ∀ v w, w ∈ G.C v ↔ ∃ j, D.nav r (post.host v) j = post.host w ∧
    (D.flags r (post.host v) j).2 = true
  load : ∀ v i, D.load (D.counter r (post.host v) (post.block i)) = G.load v i
  park : ∀ v i, D.park (D.counter r (post.host v) (post.block i)) = push G.park L.charge (v, i)
  past : ∀ v i, D.past (D.counter r (post.host v) (post.block i)) = G.past (v, i)

open scoped Classical in
/-- Computes the tag length by the application `History.Dense.used (D.order ((r.1 i).2 t)).val`. -/
def tagLength (i : B D.scheme.m) (t : B D.scheme.h) :=
  History.Dense.used (D.order ((r.1 i).2 t)).val

end Template
end MatrixMultiplicationAllFields.MatrixExponent.Assembly
end

/- # A board with one station per occurrence -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
open Coloring Packing Rounds

variable {F : Type} [Field F] {x y : Wire} (D : Template F)
  (r : D.format.obj) (P : Rounds.Board F x y D.scheme.h)

/-- The data for the presents construction, including `pres`, `host`, `vertex`, `directed`,
`live`. -/
structure Presents where
  /-- The `Presents` component of type `D.scheme.Presentation r.1 P.diagram`. -/
  pres : D.scheme.Presentation r.1 P.diagram
  /-- Embeds the coordinates as `P.V ↪ B D.scheme.m`. -/
  host : P.V ↪ B D.scheme.m
  vertex : ∀ v, pres.vertex v = (host (P.place v).1, cellIndex _ (P.place v).2, 0)
  directed : pres.Directed
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range host
  closed : ∀ v j, D.nav r (host v) j ∈ Set.range host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ P.adj v ↔ ∃ j, D.nav r (host v) j = host w ∧
    (D.flags r (host v) j).1 = true
  core : ∀ v w, w ∈ P.adj v ↔ ∃ j, D.nav r (host v) j = host w ∧
    (D.flags r (host v) j).2 = true
  load : ∀ v i, D.load (D.counter r (host v) (cellIndex _ i)) = push P.place P.charge (v, i)

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
end

/- # A presentation of one concentrated term before cutting off its border -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
open Coloring Packing Rounds
variable {F : Type} [Field F] {x y : Wire} {u : ℕ}

open scoped Classical in
/-- The data for the shows construction, including `pres`, `host`, `vertex`, `directed`,
`uniform`. -/
structure Shows (D : Template F) (r : D.format.obj) (Q : LocalTerm F x y D.scheme.h u) where
  /-- The `Shows` component of type `D.scheme.Presentation r.1 Q.diagram`. -/
  pres : D.scheme.Presentation r.1 Q.diagram
  /-- Embeds the coordinates as `Q.V ↪ B D.scheme.m`. -/
  host : Q.V ↪ B D.scheme.m
  vertex : ∀ v, pres.vertex v = (host (Q.frame.place v).1, cellIndex _ (Q.frame.place v).2, 0)
  directed : pres.Directed
  uniform : pres.Uniform u
  /-- The identification of the indices of type `Q.V → Q.V → B D.scheme.d`. -/
  index : Q.V → Q.V → B D.scheme.d
  neighbor : ∀ v w i j, D.scheme.peer r.1 (pres.vertex v, i) = some (pres.vertex w, j) →
    (D.scheme.pattern r.1 (pres.vertex v)).peer 0 i =
      some (index (Q.frame.place v).1 (Q.frame.place w).1, 0, j)
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range host
  frozen : ∀ v, D.frozen r (host v) = true ↔ Q.frame.frozen v
  closed : ∀ v j, D.nav r (host v) j ∈ Set.range host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ Q.frame.N v ↔ ∃ j, D.nav r (host v) j = host w ∧ (D.flags r (host v) j).1 = true
  core : ∀ v w, w ∈ Q.frame.C v ↔ ∃ j, D.nav r (host v) j = host w ∧ (D.flags r (host v) j).2 = true
  charge : ∀ v, Q.charge v = Q.diagram.arity v + (u : ℝ)
  amount : ∀ i j, D.load (D.counter r i j) =
    ∑ v, if (pres.vertex v).1 = i ∧ (pres.vertex v).2.1 = j then Q.charge v else 0

variable (D : Template F)

open scoped Classical in
/-- Computes the cut counter by the application `Format.pair .bit (.addr D.count)`. -/
abbrev cutCounter := Format.pair .bit (.addr D.count)

open scoped Classical in
/-- Builds `Template F where scheme` with the specified `scheme`, `count`, `load`, `let`. -/
abbrev cut (u : ℕ) (scale : ℝ) : Template F where
  scheme := D.scheme.cut
  count := D.cutCounter.width
  load j :=
    let x := D.cutCounter.serial.symm j
    if x.1 then scale * D.load x.2 else max 0 (D.load x.2 - u)
  park j :=
    let x := D.cutCounter.serial.symm j
    if x.1 then D.load x.2 else 0
  past _ := 0
  order := Equiv.refl _
  full := true

open scoped Classical in
/-- The value specified by `!(D.frozen r i)`. -/
def mobile (r : D.format.obj) (i : B D.scheme.m) := !(D.frozen r i)

open scoped Classical in
/-- The indexed operation `(D.scheme.remove r.1 (D.mobile r), fun i => ((r.2 i).1, (D.flags r i,
fun j => D.cutCounter.serial (D.frozen r i, D.counter r i j))))`. -/
def remove (u : ℕ) (scale : ℝ) (r : D.format.obj) : (D.cut u scale).format.obj :=
  (D.scheme.remove r.1 (D.mobile r), fun i =>
    ((r.2 i).1, (D.flags r i, fun j => D.cutCounter.serial (D.frozen r i, D.counter r i j))))

namespace Shows
variable {D} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u} (s : D.Shows r Q)

open scoped Classical in
theorem kept (v : Q.diagram.V) : D.mobile r (s.pres.vertex v).1 = true ↔ ¬ Q.freeze.frozen v := by
  rw [s.vertex]
  have h := (s.frozen (Q.frame.place v).1).trans (Q.frame.keep v)
  simp only [mobile, Bool.not_eq_true', ← h, Bool.eq_false_iff]

open scoped Classical in
/-- Computes the presentation by the application `s.pres.freeze Q.freeze (D.mobile r) s.kept`. -/
abbrev presentation := s.pres.freeze Q.freeze (D.mobile r) s.kept
open scoped Classical in
/-- Computes the oriented by the application `s.pres.freeze_directed Q.freeze (D.mobile r)
s.kept s.directed`. -/
abbrev oriented := s.pres.freeze_directed Q.freeze (D.mobile r) s.kept s.directed
open scoped Classical in
/-- The indexed operation `s.pres.freeze_uniform Q.freeze (D.mobile r) s.kept (fun e =>
s.uniform e.val)`. -/
abbrev sizes := s.pres.freeze_uniform Q.freeze (D.mobile r) s.kept (fun e => s.uniform e.val)
open scoped Classical in
/-- Uses `s.presentation.packets s.oriented s.sizes` as the representation. -/
abbrev packets := s.presentation.packets s.oriented s.sizes

open scoped Classical in
/-- The posting of type `D.scheme.cut.Posting (D.scheme.remove r.1 (D.mobile r)) (Q.frame.hostOf
hu L hL s.packets)` for the given inputs. -/
abbrev posting (hu : 0 < u) (L : Fringe Q.freeze.x Q.freeze.y Q.freeze.Fixed)
    (hL : L.tensor = Q.freeze.border.tensor) :
    D.scheme.cut.Posting (D.scheme.remove r.1 (D.mobile r)) (Q.frame.hostOf hu L hL s.packets) :=
  s.pres.freezePosting Q.freeze (D.mobile r) s.kept s.directed (fun e => s.uniform e.val)
    Q.frame hu L hL s.host (cellIndex _).toEmbedding s.index s.vertex s.neighbor

end Shows
end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
end

/-
# Reading loads and electing a grouping from the encoded host
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
open Coloring Packing

variable {F T : Type} (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h)
local notation "M" => D.scheme.m
local notation "d" => D.scheme.d
local notation "n" => (D.scheme.h - a)

open scoped Classical in
/-- The value specified by `cellIndex _ ((splitCell a ha).symm ((cellIndex a).symm u, (cellIndex
_).symm v))`. -/
def position (u : B a) (v : B n) : B D.scheme.h :=
  cellIndex _ ((splitCell a ha).symm ((cellIndex a).symm u, (cellIndex _).symm v))

open scoped Classical in
/-- Computes the group input by the application `Group.Input M d a n D.count`. -/
abbrev groupInput := Group.Input M d a n D.count

open scoped Classical in
/-- Evaluates `(D.nav r i, D.live r i, D.flags r i, fun x y => D.counter r i (D.position a ha x
y))` at the input `i`. -/
def groups (r : D.format.obj) : (D.groupInput a).obj :=
  fun i => (D.nav r i, D.live r i, D.flags r i, fun x y => D.counter r i (D.position a ha x y))

open scoped Classical in
/-- The quantity computed by `D.load v / ((2 : ℝ) ^ k * b)`. -/
def relative (k : ℕ) (b : ℝ) (v : B D.count) := D.load v / ((2 : ℝ) ^ k * b)

variable [Field F]

open scoped Classical in
theorem groups_circuit : Circuit F D.format (D.groupInput a) (D.groups a ha)
    (D.format.width + 2 * (D.groupInput a).width) := by
  let f : (D.groupInput a).pins → D.format.pins
    | (i, .inl j) => .inl (i, .inl j)
    | (i, .inr (.inl j)) => .inr (i, .inl (.inl j))
    | (i, .inr (.inr (.inl j))) => .inr (i, .inr (.inl j))
    | (i, .inr (.inr (.inr (x, y, j)))) => .inr (i, .inr (.inr (D.position a ha x y, j)))
  exact Circuit.project f (by rintro _ ⟨_, _ | (_ | (_ | ⟨_, _, _⟩))⟩ <;> rfl)

variable [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G) (k : ℕ) (b : ℝ)

open scoped Classical in
theorem presents :
    Group.Presents (D.groups a ha r) p.post.host (D.adj G) G.C
      (Packing.relative k b (G.regroup a ha).load) (D.relative k b) := by
  refine ⟨p.live, p.closed, p.edge, p.core, ?_⟩
  intro v i j
  let q := (splitCell a ha).symm (i, j)
  have he : splitAddr G.V a ha (v, q) = ((v, i), j) := by
    unfold splitAddr
    simp [q]
  have hl := G.regroup_load a ha (v, q)
  rw [he] at hl
  have ht := p.load v q
  rw [p.block] at ht
  have hh : D.position a ha (cellIndex a i) (cellIndex n j) = cellIndex _ q := by
    simp [position, q]
  change D.load (D.counter r (p.post.host v) (D.position a ha _ _)) / _ = _
  rw [hh, ht]
  exact congrArg (fun a => a / ((2 : ℝ) ^ k * b)) hl.symm

variable (Δ C : ℕ)
open scoped Classical in
/-- The value specified by `Group.labels Δ C (D.relative k b) (D.groups a ha r)`. -/
def intervals (r : D.format.obj) := Group.labels Δ C (D.relative k b) (D.groups a ha r)

open scoped Classical in
theorem grouping (hΔ : 0 < Δ) (hC : 0 < C) (hk : 1 ≤ k) (hn : k ≤ n) (hb : 0 < b)
    (hG : G.Bounded Δ C b) (delayed : D.full = false → n ≤ 32 * Nat.clog 2 (2 * C)) :
    ∃ g : Grouping (inGroup a G.N) (inGroup a G.C) Δ C k b (G.regroup a ha).load,
      ∀ v i, D.intervals a ha k b Δ C r (Group.embed p.post.host a v) (cellIndex n i) =
        intervalCode n (g.here v i).2 := by
  have hg := G.regroup_bounded a ha hG
  have hs : ∀ v w, w ∈ D.adj G v → v ∈ D.adj G w := by
    unfold adj
    split
    · exact G.ns
    · exact G.cs
  have hc : ∀ v, G.C v ⊆ D.adj G v := by
    unfold adj
    split
    · exact G.sub
    · exact fun _ => Finset.Subset.rfl
  have hsize : ∀ v, (D.adj G v).card ≤ C := by
    unfold adj
    split
    · exact hG.2.1
    · exact fun v => (Finset.card_le_card (G.sub v)).trans (hG.2.1 v)
  obtain ⟨q, hq⟩ := (D.presents a ha p k b).grouping hΔ hC hk hn hb hs G.cs hc hsize hG.1
    (fun v i => ⟨(G.regroup a ha).load_nonneg _ _, hg.2.2 _ _⟩)
  refine ⟨{ q with edge := ?_ }, hq⟩
  intro v w hw i
  by_cases e : w ∈ inGroup a (D.adj G) v
  · exact q.edge v w e i
  have hf : D.full = false := Bool.eq_false_iff.mpr (by
    intro h
    exact e (by simpa only [adj, ite_eq_left h] using hw))
  have e' : w ∉ inGroup a G.C v := by simpa [adj, hf] using e
  rw [ite_eq_right e']
  have h := (q.part w _ (q.mem w i)).1
  have hd := delayed hf
  omega

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
end

/-
# Common addresses of child hosts

In core-only mode the stored neighbor width depends on the core
degree. Delayed noncore contacts are tracked separately.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
open Coloring Packing

variable {F T : Type} (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (Δ C : ℕ)
local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d

open scoped Classical in
/-- Returns `C` when `D.full` holds, and `Δ` otherwise. -/
abbrev bound := if D.full then C else Δ
open scoped Classical in
/-- The quantity computed by `m + (n + 1)`. -/
abbrev size := m + (n + 1)
open scoped Classical in
/-- The value specified by `Child.nextWidth n (D.bound Δ C) d`. -/
abbrev degree := Child.nextWidth n (D.bound Δ C) d
open scoped Classical in
/-- The value specified by `Neighborhood.Rows (D.size a) (D.degree a Δ C)`. -/
abbrev Graph := Neighborhood.Rows (D.size a) (D.degree a Δ C)
open scoped Classical in
/-- Computes the status by the application `Format.vec (D.size a) .bit`. -/
abbrev Status := Format.vec (D.size a) .bit

open scoped Classical in
/-- The value specified by `Child.neighbors n (D.bound Δ C) (Child.fromGroup (D.groups a ha r)
false)`. -/
def childNav (r : D.format.obj) : (D.Graph a Δ C).obj :=
  Child.neighbors n (D.bound Δ C) (Child.fromGroup (D.groups a ha r) false)

open scoped Classical in
/-- The value specified by `Child.neighbors n Δ (Child.fromGroup (D.groups a ha r) true)`. -/
def childCore (r : D.format.obj) :=
  Child.neighbors n Δ (Child.fromGroup (D.groups a ha r) true)

open scoped Classical in
/-- The construction uses `Match.rowIndex m (n + 1) j` for its intermediate `t`. -/
def childLive (r : D.format.obj) (j : B (D.size a)) :=
  let t := Match.rowIndex m (n + 1) j
  D.live r t.1 && decide (t.2 ∈ Set.range (intervalCode n))

open scoped Classical in
/-- The quantity computed by `D.frozen r (Match.rowIndex m (n + 1) j).1`. -/
def childFrozen (r : D.format.obj) (j : B (D.size a)) :=
  D.frozen r (Match.rowIndex m (n + 1) j).1

open scoped Classical in
theorem childSelf (r : D.format.obj) (j : B (D.size a)) : D.childNav a ha Δ C r j 0 = j :=
  Neighborhood.origin

variable [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G)

open scoped Classical in
theorem child_live (j : B (D.size a)) :
    D.childLive a r j = true ↔ j ∈ Set.range (Child.host p.post.host n) := by
  simp only [childLive, Bool.and_eq_true, decide_eq_true_eq, p.live]
  constructor
  · rintro ⟨⟨v, hv⟩, ⟨t, ht⟩⟩
    refine ⟨(v, t), (Match.rowIndex m (n + 1)).injective ?_⟩
    rw [Child.host_parts]
    exact Prod.ext hv ht
  · rintro ⟨v, rfl⟩
    rw [Child.host_parts]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

open scoped Classical in
theorem child_presents :
    Child.Presents (D.adj G) p.post.host (Child.fromGroup (D.groups a ha r) false) :=
  Child.presents (D.presents a ha p 0 1) false

open scoped Classical in
theorem core_presents :
    Child.Presents G.C p.post.host (Child.fromGroup (D.groups a ha r) true) :=
  Child.presents (D.presents a ha p 0 1) true

omit [Field F] in
open scoped Classical in
theorem bound_pos (hd : 0 < Δ) (hc : Δ ≤ C) : 0 < D.bound Δ C := by
  unfold bound
  split <;> omega

include p in
open scoped Classical in
theorem child_reciprocal (hd : 0 < Δ) (hc : Δ ≤ C) (A : Format) (f : B (D.size a) → A.obj) :
    Fmt.Reciprocal A (fun i => (D.childNav a ha Δ C r i, f i)) := by
  refine (D.child_presents a ha p).reciprocal (D.bound_pos Δ C hd hc) ?_ A f
  unfold adj
  split
  · exact G.ns
  · exact G.cs

open scoped Classical in
theorem child_hop (hd : 0 < Δ) (hc : Δ ≤ C) (v w : Site G.V n)
    (hw : w ∈ (G.project a ha Δ C hc).C v) :
    let nav := D.childNav a ha Δ C r
    let H := Child.host p.post.host n
    nav (H v) (Child.index nav (H v) (H w)) = H w := by
  apply (D.child_presents a ha p).nav (D.bound_pos Δ C hd hc)
  by_cases h : D.full = true
  · rw [adj, bound, ite_eq_left h, ite_eq_left h]
    exact (G.project a ha Δ C hc).sub v hw
  · rw [adj, bound, ite_eq_right h, ite_eq_right h]
    exact hw

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
end

/- # Cost of the common child address and mask computations -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
open Coloring

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h)
  (Δ C : ℕ)
local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "j" => D.size a
local notation "v" => D.degree a Δ C

open scoped Classical in
/-- The bound obtained by adding the component charges `D.format.width + 3 * (D.groupInput
a).width + 68 * (Child.Input m d).width + 2 ^ j * (100 + (j + 2 ^ degree)) ^ 201`. -/
def navCost (degree : ℕ) :=
  D.format.width + 3 * (D.groupInput a).width + 68 * (Child.Input m d).width +
    2 ^ j * (100 + (j + 2 ^ degree)) ^ 201

open scoped Classical in
theorem nav_net (core : Bool) (deg : ℕ) :
    Circuit F D.format (Neighborhood.Rows j (Child.nextWidth n deg d))
      (fun r => Child.neighbors n deg (Child.fromGroup (D.groups a ha r) core))
      (D.navCost a (Child.nextWidth n deg d)) := by
  let prep := (D.groups_circuit a ha).comp (Child.fromGroup_circuit F core)
  obtain ⟨k, hk, h⟩ := Child.cheap F m d n deg
  refine (prep.comp hk).mono ?_
  change _ + _ + k ≤ 2 ^ j * (100 + (j + 2 ^ Child.nextWidth n deg d)) ^ 201 at h
  unfold navCost
  change D.format.width + 2 * (D.groupInput a).width +
    ((D.groupInput a).width + 68 * (Child.Input m d).width) + k ≤ _
  omega

open scoped Classical in
/-- The quantity computed by `D.format.width + 34 * (D.Status a).width`. -/
def statusCost := D.format.width + 34 * (D.Status a).width

open scoped Classical in
theorem status_net :
    Circuit F D.format (D.Status a) (D.childLive a) (D.statusCost a) := by
  have h : Install.Depends ((D.Status a).code ∘ D.childLive a ∘ D.format.code.symm) 1 := by
    rintro ⟨i, ⟨⟩⟩
    let p := (Match.rowIndex m (n + 1) i).1
    let pin : D.format.pins := .inr (p, .inl (.inl ()))
    refine ⟨{pin}, by simp, fun x y he => ?_⟩
    change (x pin && _) = (y pin && _)
    rw [he pin (by simp)]
  exact h.bnet F

open scoped Classical in
/-- The quantity computed by `4 * (5 * D.format.width + D.statusCost a + D.navCost a v)`. -/
def childCost := 4 * (5 * D.format.width + D.statusCost a + D.navCost a v)

open scoped Classical in
theorem child_map {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) :
    Map F u L D.format ((D.Status a).pair (D.Graph a Δ C))
      (fun r => (D.childLive a r, D.childNav a ha Δ C r)) (D.childCost a Δ C) :=
  Map.circuit hu ((D.status_net a).pair (D.nav_net a ha false (D.bound Δ C)))

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
end
