/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Pruned
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Price

/-! # Indexing selectors on occupied occurrences -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse
open Coloring Finset Transcript

variable {J I : Type} {m h k : ℕ} (loc : J ↪ B m × B h) (pad : B k)

open scoped Classical in
/-- The condition `∀ v ∉ Set.range loc, c v.1 v.2 = pad` on the specified data. -/
def Supported (c : B m → B h → B k) : Prop :=
  ∀ v ∉ Set.range loc, c v.1 v.2 = pad

open scoped Classical in
/-- Extends the specified values along the indexing map, using a default elsewhere. -/
def pack (c : J → B k) (i : B m) (j : B h) :=
  Function.extend loc c (fun _ => pad) (i, j)

open scoped Classical in
/-- Computes the sample by the application `c (loc j).1 (loc j).2`. -/
def sample (c : B m → B h → B k) (j : J) := c (loc j).1 (loc j).2

open scoped Classical in
@[simp] theorem sample_pack (c : J → B k) : sample loc (pack loc pad c) = c :=
  funext fun j => loc.injective.extend_apply c (fun _ => pad) j

open scoped Classical in
theorem pack_supported (c : J → B k) : Supported loc pad (pack loc pad c) :=
  fun _ hv => Function.extend_apply' _ _ _ hv

open scoped Classical in
theorem pack_sample {c : B m → B h → B k} (hc : Supported loc pad c) :
    pack loc pad (sample loc c) = c := by
  have he (v : B m × B h) : pack loc pad (sample loc c) v.1 v.2 = c v.1 v.2 := by
    by_cases hv : v ∈ Set.range loc
    · obtain ⟨i, rfl⟩ := hv
      exact congrFun (sample_pack loc pad (sample loc c)) i
    · rw [pack_supported loc pad _ v hv, hc v hv]
  exact funext fun i => funext fun j => he (i, j)

open scoped Classical in
/-- Compression preserves the unique code of every supported branch. -/
def compress (s : Selector I (B m → B h → B k))
    (ok : ∀ i, Supported loc pad (s.write i)) : Selector I (J → B k) where
  write i := sample loc (s.write i)
  read x := s.read (pack loc pad x)
  valid x i := by
    rw [s.valid]
    exact ⟨fun e => (sample_pack loc pad x).symm.trans (congrArg (sample loc) e),
      fun e => e ▸ pack_sample loc pad (ok i)⟩

open scoped Classical in
theorem of_weight {F : Type} [Zero F] (s : Selector I (B m → B h → B k))
    (ok : ∀ i, Supported loc pad (s.write i)) {w : I → F} {c : B m → B h → B k}
    (hc : (s.read c).elim 0 w ≠ 0) : Supported loc pad c := by
  cases e : s.read c with
  | none => simp [e] at hc
  | some i => rw [(s.valid c i).mp e]; exact ok i

variable [Fintype J]

open scoped Classical in
theorem card_le [Fintype I] (s : Selector I (J → B k)) :
    Fintype.card I ≤ 2 ^ (k * Fintype.card J) := by
  have h := Fintype.card_le_of_injective s.write s.injective
  simpa only [Fintype.card_fun, Fintype.card_fin, pow_mul] using h

open scoped Classical in
/-- Padded occurrences do not count toward the number of choices. -/
theorem sum_pack {F : Type} [CommSemiring F] (weight f : (B m → B h → B k) → F)
    (support : ∀ c, weight c ≠ 0 → Supported loc pad c) :
    (∑ c, weight c * f c) = ∑ x, weight (pack loc pad x) * f (pack loc pad x) := by
  have inj : Function.Injective (pack loc pad) :=
    Function.LeftInverse.injective (sample_pack loc pad)
  let active := univ.image (pack loc pad)
  calc
    _ = ∑ c ∈ active, weight c * f c := (sum_subset (subset_univ _) (by
      intro c _ hc
      have hw : weight c = 0 := by
        by_contra h
        exact hc (mem_image.mpr ⟨sample loc c, mem_univ _, pack_sample loc pad (support c h)⟩)
      rw [hw, zero_mul])).symm
    _ = _ := sum_image inj.injOn

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse
end

/- # A shared dictionary for a cell of ordered bundles -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder
open Coloring

open scoped Classical in
/-- Computes the entry by the application `Format.pair (.addr w) (.pair .bit (.pair .bit (.pair
(.addr d) (.pair (.addr k) (.addr e)))))`. -/
abbrev entry (e d k w : ℕ) :=
  Format.pair (.addr w) (.pair .bit (.pair .bit (.pair (.addr d) (.pair (.addr k) (.addr e)))))

open scoped Classical in
/-- Computes the name by the application `Format.pair .bit (.pair .bit (.pair (.addr a) (.vec e
(entry e d k w))))`. -/
abbrev name (a e d k w : ℕ) :=
  Format.pair .bit (.pair .bit (.pair (.addr a) (.vec e (entry e d k w))))

open scoped Classical in
/-- Computes the row by the application `Format.vec k (name a e d k w)`. -/
abbrev row (a e d k w : ℕ) := Format.vec k (name a e d k w)

open scoped Classical in
theorem row_width (a e d k w : ℕ) :
    (row a e d k w).width = 2 ^ k * (2 + a + 2 ^ e * (w + 2 + d + k + e)) := by
  simp only [row, name, entry, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]
  ring

variable {F : Type} [Field F] {e d k a w : ℕ} (read : BundleReader F a e)
local notation "N" => name a e d k w
local notation "R" => row a e d k w

open scoped Classical in
/-- The indexed operation `(false, false, 0, fun _ => (0, false, false, 0, 0, 0))`. -/
def blank : (N).obj := (false, false, 0, fun _ => (0, false, false, 0, 0, 0))

open scoped Classical in
/-- The value specified by `(t.2.2.2 s).1.val`. -/
def length (t : (N).obj) (s : B e) := (t.2.2.2 s).1.val
open scoped Classical in
/-- The value specified by `(t.2.2.2 s).2.1`. -/
def side (t : (N).obj) (s : B e) := (t.2.2.2 s).2.1
open scoped Classical in
/-- Returns `some (t.2.2.2 s).2.2.2` when `(t.2.2.2 s).2.2.1` holds, and `none` otherwise. -/
def mate (t : (N).obj) (s : B e) :=
  if (t.2.2.2 s).2.2.1 then some (t.2.2.2 s).2.2.2 else none

open scoped Classical in
/-- Builds `Pattern F d k e where width j` with the specified `width`, `direction`, `peer`,
`value`. -/
def pattern (x : (R).obj) : Pattern F d k e where
  width j := length (x j)
  direction j := side (x j)
  peer j := mate (x j)
  value j z := if (x j).1 then read (x j).2.2.1 (length (x j)) (side (x j))
    (fun i n => if h : n < length (x j) i then z i ⟨n, h⟩ else false) else 1

open scoped Classical in
/-- Uses `⟨m, d, h, k, e, (row a e d k w).width, fun i => pattern read ((row a e d k
w).serial.symm i)⟩` as the representation. -/
abbrev scheme (m h d k w : ℕ) : Scheme F :=
  ⟨m, d, h, k, e, (row a e d k w).width, fun i => pattern read ((row a e d k w).serial.symm i)⟩

open scoped Classical in
/-- The value specified by `((row a e d k w).serial.symm t i).2.1`. -/
def mobile (a e d k w : ℕ) (t : B (row a e d k w).width) (i : B k) :=
  ((row a e d k w).serial.symm t i).2.1

variable {read} {x y : Wire} {G : Diagram F x y} (o : BundleOrder G read) {m h : ℕ}

open scoped Classical in
/-- The data for the schedule construction, including `vertex`, `flag`, `nav`, `index`, `link`. -/
structure Schedule (m h d k w : ℕ) where
  /-- The placement of the vertices carried by `Schedule`, with type `G.V ↪ B m × B h × B k`. -/
  vertex : G.V ↪ B m × B h × B k
  /-- The `Schedule` component of type `G.V → Bool`. -/
  flag : G.V → Bool
  /-- The `Schedule` component of type `B m → B d → B m`. -/
  nav : B m → B d → B m
  /-- The identification of the indices of type `G.V → G.V → B d`. -/
  index : G.V → G.V → B d
  link : ∀ i j, o.peer i = some j →
    (nav (vertex i.1).1 (index i.1 j.1), (vertex i.1).2.1, (vertex j.1).2.2) = vertex j.1
  capacity : ∀ v, G.arity v < 2 ^ w

namespace Schedule
variable {o} (c : o.Schedule m h d k w)
local notation "S" => scheme read m h d k w

open scoped Classical in
/-- The label of type `(N).obj` for the given inputs. -/
def label (v : G.V) : (N).obj :=
  (true, c.flag v, o.label v, fun j =>
    (⟨o.width (v, j), (o.size _ _).trans_lt (c.capacity _)⟩, o.dir (v, j),
      (o.peer (v, j)).isSome, (o.peer (v, j)).elim (0, 0, 0) fun u => (c.index v u.1,
        (c.vertex u.1).2.2, u.2)))

open scoped Classical in
/-- Extends the specified values along the indexing map, using a default elsewhere. -/
def tags (u : (S).Vtx) : (N).obj := Function.extend c.vertex c.label (fun _ => blank) u

open scoped Classical in
/-- Evaluates `c.tags (i, b, j)` at the input `j`. -/
def book (i : B m) (b : B h) : (R).obj := fun j => c.tags (i, b, j)

open scoped Classical in
/-- Evaluates `(c.nav i, fun b => (R).serial (c.book i b))` at the input `i`. -/
def tape : (S).format.obj := fun i => (c.nav i, fun b => (R).serial (c.book i b))

open scoped Classical in
theorem fetch (u : (S).Vtx) :
    (S).pattern c.tape u = pattern read (c.book u.1 u.2.1) :=
  congrArg (pattern read) ((R).serial.symm_apply_apply _)

open scoped Classical in
theorem tags_eq (v : G.V) : c.tags (c.vertex v) = c.label v :=
  c.vertex.injective.extend_apply _ _ v

open scoped Classical in
theorem tags_off {u : (S).Vtx} (hu : u ∉ Set.range c.vertex) : c.tags u = blank :=
  Function.extend_apply' _ _ _ hu

open scoped Classical in
theorem mobility (v : G.V) :
    mobile a e d k w ((c.tape (c.vertex v).1).2 (c.vertex v).2.1) (c.vertex v).2.2 = c.flag v := by
  unfold mobile tape
  dsimp only
  rw [Equiv.symm_apply_apply]
  change (c.tags (c.vertex v)).2.1 = _
  rw [tags_eq]; rfl

end Schedule
end MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder
end

/-
# Describing the sum over local binary loops

Augment a label by one length and an optional local mate per lane.
The endpoints of a closed lane share a bit for each offset. The
reader sums over assignments to those bits when evaluating a table.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder
open Coloring
variable {F : Type} {x y : Wire} {G : Diagram F x y} {a e : ℕ}
    {read : BundleReader F a e}

open scoped Classical in
/-- The value specified by `.pair (.addr a) (.vec e (.pair (.addr n) (.pair .bit (.addr e))))`. -/
abbrev letter (a e n : ℕ) : Format :=
  .pair (.addr a) (.vec e (.pair (.addr n) (.pair .bit (.addr e))))

open scoped Classical in
theorem letter_width (a e n : ℕ) : (letter a e n).width = a + 2 ^ e * (n + (1 + e)) := by
  simp only [letter, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]

open scoped Classical in
/-- The indexed operation `(letter a e n).serial (o.label v, fun j => (Fin.ofNat _ (o.width (v,
j)), (o.turn v j).isSome, (o.turn v j).getD 0))`. -/
def traceLabel (o : BundleOrder G read) (n : ℕ) (v : G.V) : B (letter a e n).width :=
  (letter a e n).serial (o.label v, fun j =>
    (Fin.ofNat _ (o.width (v, j)), (o.turn v j).isSome, (o.turn v j).getD 0))

variable {w : B e → ℕ} {d : B e → Bool} {m : B e → Option (B e)}

open scoped Classical in
/-- The value specified by `(i.val.1, i.val.2.val)`. -/
def location (i : Closed w d m) : B e × ℕ := (i.val.1, i.val.2.val)

open scoped Classical in
theorem location_injective : Function.Injective (location (w := w) (d := d) (m := m)) := by
  intro i j h
  have ⟨ha, hb⟩ := Prod.mk.inj h
  exact Subtype.ext (Sigma.ext ha ((Fin.heq_ext_iff (congrArg w ha)).mpr hb))

open scoped Classical in
/-- In the case `none`, this construction gives `z i t`. -/
def fill (z : B e → ℕ → Bool) (l : Closed w d m → Bool) (i : B e) (t : ℕ) :=
  match m i with
  | none => z i t
  | some j => Function.extend location l (fun _ => false) (if d i then j else i, t)

variable [Field F]

open scoped Classical in
/-- The sum of `read i w d (fill z l)` indexed by `l : Closed w d m → Bool`. -/
def weight (read : BundleReader F a e) (i : B a) (w : B e → ℕ) (d : B e → Bool)
    (m : B e → Option (B e)) (z : B e → ℕ → Bool) :=
  ∑ l : Closed w d m → Bool, read i w d (fill z l)

open scoped Classical in
/-- The reader of type `BundleReader F (letter a e n).width e`, constructed using `(letter a e
n).serial.symm i`. -/
def reader (read : BundleReader F a e) (n : ℕ) : BundleReader F (letter a e n).width e :=
  fun i _ d z =>
    let c := (letter a e n).serial.symm i
    weight read c.1 (fun j => (c.2 j).1.val) d
      (fun j => if (c.2 j).2.1 then some (c.2 j).2.2 else none) z

open scoped Classical in
theorem reader_label (o : BundleOrder G read) (n : ℕ) (v : G.V)
    (h : G.arity v < 2 ^ n) (t : B e → ℕ) (d : B e → Bool) (z : B e → ℕ → Bool) :
    reader read n (o.traceLabel n v) t d z =
      weight read (o.label v) (fun j => o.width (v, j)) d (o.turn v) z := by
  unfold reader traceLabel
  simp only [Equiv.symm_apply_apply]
  have hl (j : B e) : (Fin.ofNat (2 ^ n) (o.width (v, j))).val = o.width (v, j) :=
    Nat.mod_eq_of_lt ((o.size v j).trans_lt h)
  have hm (j : B e) : (if (o.turn v j).isSome then some ((o.turn v j).getD 0) else none)
    = o.turn v j := by
    cases o.turn v j <;> rfl
  simp only [hl, hm]

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder
end

/- # Transporting the table reader through contraction and pruning -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder
open Coloring Restore Restore.Chain.Frame
variable {F : Type} {x y : Wire} {G : Diagram F x y} {a e : ℕ}
    {read : BundleReader F a e} (o : BundleOrder G read)
    (v : G.V) (z : B e → ℕ → Bool)

open scoped Classical in
private theorem fill_loop (l : o.loops v → Bool) (t : G.LocalLoop v) (d : Bool) :
    fill z l (o.lane (tip G t.val d)) (o.offset (tip G t.val d)) = l (o.loopBits v t) := by
  unfold fill
  simp only [o.loop_turn, o.loop_side]
  have hs : o.offset (tip G t.val true) = o.offset (tip G t.val false) := (o.aligned _).symm
  have hx : Function.extend location l (fun _ => false) (location (o.loopBits v t))
    = l (o.loopBits v t) :=
    location_injective.extend_apply _ _ _
  cases d
  · exact hx
  · rw [hs]
    exact hx

variable [Field F]

open scoped Classical in
private theorem fill_keep (l : o.loops v → Bool) (i : G.removeLoops.End)
    (h : G.removeLoops.station i = v) :
    fill z l (o.lane (G.embedEnd i)) (o.offset (G.embedEnd i)) = z (o.keep i).1.2 (o.keep i).2.val
      := by
  have ht := (o.retain (G.embedEnd i)).mpr ⟨i, rfl⟩
  rw [G.station_embedEnd, h] at ht
  unfold fill
  rw [ht]
  rfl

open scoped Classical in
theorem contraction :
    weight read (o.label v) (fun j => o.width (v, j)) (fun j => o.dir (v, j)) (o.turn v) z =
      Transcript.sample (G.removeLoops.table v) (fun i =>
        let t := o.keep (G.removeLoops.portEquiv ⟨v, i⟩)
        z t.1.2 t.2.val) := by
  let E := (o.loopBits v).arrowCongr (Equiv.refl Bool)
  let s (i : G.removeLoops.End) := z (o.keep i).1.2 (o.keep i).2.val
  let t (l : G.LocalLoop v → Bool) (i : G.End) :=
    fill z (E l) (o.lane i) (o.offset i)
  have h := G.loopTable v s t (fun l i hi => o.fill_keep v z (E l) i hi)
    (fun l i b => (o.fill_loop v z (E l) i b).trans (by simp [E]))
  refine Eq.trans ?_ h.symm
  unfold weight
  symm
  refine Fintype.sum_equiv E _ _ fun l => ?_
  exact (o.sample v (fill z (E l))).symm

open scoped Classical in
/-- Builds `BundleOrder G.removeLoops (reader read n) where label` with the specified
`BundleOrder`, `width`, `dir`, `place`. -/
def contracted (n : ℕ) (h : ∀ v, G.arity v < 2 ^ n) :
    BundleOrder G.removeLoops (reader read n) where
  label := o.traceLabel n
  width := o.keepWidth
  dir := o.dir
  place := o.keep
  station := o.keep_station
  direction := o.keep_direction
  paired := o.keep_paired
  aligned := o.keep_aligned
  sample v z := (o.reader_label n v (h v) _ _ z).trans (o.contraction v z)

open scoped Classical in
/-- The value specified by `(o.contracted n h).prune`. -/
abbrev reduced (n : ℕ) (h : ∀ v, G.arity v < 2 ^ n) :
    BundleOrder G.removeLoops.prune (reader read n) :=
  (o.contracted n h).prune

open scoped Classical in
theorem reduced_lane (n : ℕ) (h : ∀ v, G.arity v < 2 ^ n) (i : G.removeLoops.prune.End) :
    (o.reduced n h).lane i = o.lane (G.embedEnd i) := rfl

open scoped Classical in
theorem reduced_offset (n : ℕ) (h : ∀ v, G.arity v < 2 ^ n) (i : G.removeLoops.prune.End) :
    (o.reduced n h).offset i = o.offset (G.embedEnd i) := rfl

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder
end

/- # Correctness of all occupied and vacant bundle descriptors -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder.Schedule
open Coloring Restore Restore.Chain.Frame

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y}
  {a e d k w m h : ℕ} {read : BundleReader F a e} {o : BundleOrder G read} (c : o.Schedule m h d k
    w)
local notation "S" => scheme read m h d k w
local notation "r" => c.tape

open scoped Classical in
/-- The value specified by `(c.vertex x.1, x.2)`. -/
def span (x : G.V × B e) : (S).Span := (c.vertex x.1, x.2)

open scoped Classical in
theorem width_eq (x : (S).Span) : (S).width r x = length (c.tags x.1) x.2 := by
  unfold Scheme.width; rw [fetch]; rfl

open scoped Classical in
theorem width (x : G.V × B e) : (S).width r (c.span x) = o.width x := by
  rw [width_eq, span, tags_eq]; rfl

open scoped Classical in
theorem direction (x : G.V × B e) : (S).direction r (c.span x) = o.dir x := by
  unfold Scheme.direction span
  rw [fetch]
  change BundleOrder.side (c.tags (c.vertex x.1)) x.2 = _
  rw [tags_eq]; rfl

open scoped Classical in
theorem peer_eq (x : (S).Span) :
    (S).peer r x = (mate (c.tags x.1) x.2).map
      (fun j => ((c.nav x.1.1 j.1, x.1.2.1, j.2.1), j.2.2)) := by
  unfold Scheme.peer; rw [fetch]; rfl

open scoped Classical in
theorem peer (x : G.V × B e) : (S).peer r (c.span x) = (o.peer x).map c.span := by
  have eq : mate (c.label x.1) x.2 =
      (o.peer x).map (fun j => (c.index x.1 j.1, (c.vertex j.1).2.2, j.2)) := by
    let value (t : G.V × B e) := (c.index x.1 t.1, (c.vertex t.1).2.2, t.2)
    change (if (o.peer x).isSome then some ((o.peer x).elim (0, 0, 0) value) else none) = _
    cases o.peer x <;> rfl
  rw [peer_eq, span, tags_eq, eq]
  cases hx : o.peer x with
  | none => rfl
  | some t => exact congrArg (fun v => some (v, t.2)) (c.link _ _ hx)

open scoped Classical in
theorem proper : (S).Proper r := by
  rintro ⟨v, j⟩ t ht
  by_cases h : v ∈ Set.range c.vertex
  · obtain ⟨w, rfl⟩ := h
    change (S).peer r (c.span (w, j)) = some t at ht
    rw [peer] at ht
    cases hp : o.peer (w, j) with
    | none => simp [hp] at ht
    | some q =>
      rw [hp] at ht
      obtain rfl := Option.some.inj ht
      obtain ⟨i, b, hx, hy⟩ := o.peer_source hp
      have rev : o.peer q = some (w, j) := by rw [← hy, o.peer_edge, Bool.not_not, hx]
      have dir : o.dir (w, j) ≠ o.dir q := by
        rw [← hx, ← hy, o.direction, o.direction, side_tip, side_tip]
        cases b <;> decide
      change (S).peer r (c.span q) = some (c.span (w, j)) ∧
        (S).width r (c.span (w, j)) = (S).width r (c.span q) ∧
        (S).direction r (c.span (w, j)) ≠ (S).direction r (c.span q)
      rw [peer, rev, width, width, direction, direction]
      exact ⟨rfl, Nat.le_antisymm (o.width_le hp) (o.width_le rev), dir⟩
  · rw [peer_eq, c.tags_off h] at ht; cases ht

open scoped Classical in
/-- The entry at of type `(S).LocalPin r (c.vertex v)`, constructed using `G.portEquiv ⟨v, i⟩`. -/
def entryAt (v : G.V) (i : G.Port v) : (S).LocalPin r (c.vertex v) :=
  let q := G.portEquiv ⟨v, i⟩
  ⟨o.lane q, ⟨o.offset q, by
    have he : (o.place q).1 = (v, o.lane q) := Prod.ext ((o.station q).trans (G.station_port _)) rfl
    exact ((o.place q).2.isLt.trans_eq (congrArg o.width he)).trans_eq (c.width (v,
      o.lane q)).symm⟩⟩

open scoped Classical in
theorem bijective (v : G.V) : Function.Bijective (c.entryAt v) := by
  constructor
  · intro i j he
    let q := G.portEquiv ⟨v, i⟩
    let q' := G.portEquiv ⟨v, j⟩
    have ha : (o.place q).1 = (o.place q').1 := by
      have hb : o.lane q = o.lane q' := congrArg Sigma.fst he
      rw [o.position, o.position, hb]
      exact Prod.ext ((G.station_port ⟨v, i⟩).trans (G.station_port ⟨v, j⟩).symm) rfl
    have hw : o.offset q = o.offset q' := congrArg (fun p => p.2.val) he
    have hh := o.place.injective (Sigma.ext ha ((Fin.heq_ext_iff (congrArg o.width ha)).mpr hw))
    exact eq_of_heq (Sigma.mk.inj (G.portEquiv.injective hh)).2
  · rintro ⟨j, n⟩
    obtain ⟨t, ht, hn⟩ := o.fills (n.isLt.trans_eq (c.width (v, j)))
    obtain ⟨⟨u, i⟩, rfl⟩ := G.portEquiv.surjective t
    rw [o.position, Diagram.station_port] at ht
    obtain ⟨rfl, he⟩ := Prod.mk.inj ht
    exact ⟨i, Sigma.ext he ((Fin.heq_ext_iff (congrArg (fun a => (S).width r (c.vertex u,
      a)) he)).mpr hn)⟩

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder.Schedule
end

/- # Presenting the input dictionary and its ordered wires -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder.Schedule
open Coloring Restore Restore.Chain.Frame

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y}
  {a e d k w m h : ℕ} {read : BundleReader F a e} {o : BundleOrder G read} (c : o.Schedule m h d k
    w)
local notation "S" => scheme read m h d k w
local notation "r" => c.tape

open scoped Classical in
private theorem value (B' : Pattern F d k e) (x : (row a e d k w).obj) (hx : B' = pattern read x)
    (i : B k) (z : ∀ j, Fin (B'.width i j) → Bool) :
    B'.value i z = if (x i).1 then read (x i).2.2.1 (length (x i)) (side (x i))
      (fun j n => if h : n < B'.width i j then z j ⟨n, h⟩ else false) else 1 := by subst B'; rfl

open scoped Classical in
private theorem test (v : (S).Vtx) (z : (S).LocalPin r v → Bool) :
    (S).table r v z = if (c.tags v).1 then
      read (c.tags v).2.2.1 (length (c.tags v)) (side (c.tags v))
        (fun j n => if h : n < (S).width r (v, j) then z ⟨j, ⟨n, h⟩⟩ else false) else 1 :=
  value _ _ (c.fetch v) v.2.2 (fun j i => z ⟨j, i⟩)

open scoped Classical in
/-- Builds `(S).Seating r G where vertex` with the specified `vertex`, `pin`, `cover`,
`by_contra`. -/
def seats : (S).Seating r G where
  vertex := c.vertex
  pin v := Equiv.ofBijective _ (c.bijective v)
  cover q := by
    by_contra h
    have hp := q.2.pos
    rw [c.width_eq, c.tags_off h] at hp
    exact Nat.lt_irrefl 0 hp
  sample v z := by
    let bits (j : B e) (n : ℕ) := if h : n < (S).width r (c.vertex v, j) then z ⟨j, ⟨n, h⟩⟩
      else false
    rw [c.test, c.tags_eq]
    change read (o.label v) (fun j => o.width (v, j)) (fun j => o.dir (v, j)) bits = _
    rw [o.sample]
    apply congrArg (Transcript.sample (G.table v))
    funext i
    change bits (c.entryAt v i).1 (c.entryAt v i).2.val = z (c.entryAt v i)
    unfold bits
    rw [dite_eq_left (c.entryAt v i).2.isLt]
  vacant v hv z := by rw [c.test, c.tags_off hv]; rfl

open scoped Classical in
theorem ends (i : G.End) :
    (c.seats.ends i).1 = c.span (o.place i).1 ∧ (c.seats.ends i).2.val = o.offset i := by
  obtain ⟨⟨v, q⟩, rfl⟩ := G.portEquiv.surjective i
  rw [Scheme.Seating.ends_at, o.position, Diagram.station_port]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- Builds `(S).Presentation r G where toSeating` with the specified `toSeating`, `proper`,
`internal`, `change`. -/
def presentation : (S).Presentation r G where
  toSeating := c.seats
  proper := c.proper
  internal i := by
    change (S).Joins r (c.seats.ends (tip G i false)) (c.seats.ends (tip G i true))
    refine ⟨?_, ?_⟩
    · rw [(c.ends _).1, (c.ends _).1, c.peer, o.peer_edge]; rfl
    · rw [(c.ends _).2, (c.ends _).2]; exact o.aligned _
  input _ := by rw [(c.ends _).1, c.peer, o.peer_at]; rfl
  output _ := by rw [(c.ends _).1, c.peer, o.peer_at]; rfl

open scoped Classical in
theorem directed : c.presentation.Directed := by
  intro i
  change (S).direction r (c.seats.ends i).1 = _
  rw [(c.ends i).1, c.direction, o.direction]

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder.Schedule
end

/- # A schedule names each neighboring station consistently across its bundles -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder.Schedule
open Coloring

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y}
  {a e d k w m h : ℕ} {read : BundleReader F a e} {o : BundleOrder G read} (c : o.Schedule m h d k
    w)
local notation "S" => scheme read m h d k w
local notation "r" => c.tape

open scoped Classical in
private theorem arc (v : G.V) (s : B e) :
    (S).arc r (c.vertex v, s) =
      (o.peer (v, s)).map (fun q => (c.index v q.1, (c.vertex q.1).2.2)) := by
  unfold Scheme.arc Pattern.target
  rw [c.fetch]
  change (mate (c.tags (c.vertex v)) s).map (fun u => (u.1, u.2.1)) = _
  rw [c.tags_eq]
  let dest (q : G.V × B e) := (c.index v q.1, (c.vertex q.1).2.2, q.2)
  change ((if (o.peer (v, s)).isSome then some ((o.peer (v, s)).elim (0, 0, 0) dest) else none).map
    (fun u : B d × B k × B e => (u.1, u.2.1))) = _
  cases o.peer (v, s) <;> rfl

open scoped Classical in
/-- Each nonempty bundle determines a unique local address for its remote station. -/
theorem resolved : (S).Resolved r := by
  intro u s t hs _ hp
  obtain ⟨v, rfl⟩ : u ∈ Set.range c.vertex := by
    by_contra hn
    rw [c.width_eq, c.tags_off hn] at hs
    exact Nat.lt_irrefl 0 hs
  change ((S).peer r (c.span (v, s))).map Prod.fst = ((S).peer r (c.span (v, t))).map Prod.fst at hp
  rw [c.peer, c.peer] at hp
  rw [c.arc, c.arc]
  cases hi : o.peer (v, s) <;> cases hj : o.peer (v, t) <;>
    simp only [hi, hj, Option.map_none, Option.map_some, span, Option.some.injEq, reduceCtorEq]
      at hp ⊢
  rw [c.vertex.injective hp]

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.BundleOrder.Schedule
end

/- # The unique ballot at a vacant occurrence -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Finset

variable {F K N : Type} {m d h e M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h e M r t q D k n u j z)

open scoped Classical in
/-- The ordinal coding the ballot whose digits are all zero. -/
def pad : B U.digits := U.ballot (fun _ _ => 0)

variable [Field F] (data : U.rows.obj) (c : U.selectors.obj)

open scoped Classical in
theorem score_away (hn : U.score data c ≠ 0) (v : B m × B h)
    (hv : U.menu ((data v.1).2 v.2) = none) : c v.1 v.2 = U.pad := by
  let w := U.view (((U.around data c) v.1).2 v.2)
  have he : w 0 0 = (none, U.ballot.symm (c v.1 v.2)) := by
    simp only [w, view, around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin, hv]
  have hw : w.valid U.positive := by
    by_contra ho
    apply hn
    unfold score Fmt.weight
    apply prod_eq_zero (mem_univ v.1)
    apply prod_eq_zero (mem_univ v.2)
    exact ite_eq_right ho
  apply U.ballot.symm.injective
  rw [pad, U.ballot.symm_apply_apply]
  funext i j
  have hz : tally (U.ballot.symm (c v.1 v.2) i) = 0 := by
    simpa [Lens.ask, he, quota] using hw i
  have le : (U.ballot.symm (c v.1 v.2) i j).val ≤ tally (U.ballot.symm (c v.1 v.2) i) :=
    single_le_sum (fun l _ => Nat.zero_le (U.ballot.symm (c v.1 v.2) i l).val) (mem_univ j)
  exact Fin.ext (Nat.eq_zero_of_le_zero (le.trans_eq hz))

open scoped Classical in
theorem supported {J : Type} (loc : J ↪ B m × B h)
    (vacant : ∀ v ∉ Set.range loc, U.menu ((data v.1).2 v.2) = none)
    (hn : U.score data c ≠ 0) : Sparse.Supported loc U.pad c :=
  fun v h => U.score_away data c hn v (vacant v h)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
end

/- # Reading a whole motion history from its selector words -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local
open Assembly Coloring

namespace Design

variable (a : Design) {e k : ℕ} (start : (a.port e).obj)

/-- The metadata tape, computed independently of the weights. -/
def path : (i : ℕ) → (Fin i → (a.selectors k).obj) → (a.port (a.widthAt e k i)).obj
  | 0, _ => start
  | i + 1, c => a.update (path i (Fin.init c)) (c (Fin.last i))

theorem path_snoc {i : ℕ} (c : Fin i → (a.selectors k).obj) (t : (a.selectors k).obj) :
    a.path start (i + 1) (Fin.snoc c t) = a.update (a.path start i c) t := by
  rw [path, Fin.init_snoc, Fin.snoc_last]

variable {F N A : Type} [Field F] [Fintype F] [ExpChar F a.p]
  (hF : a.M * (2 * a.D + 1) < Fintype.card F) (menu : a.Menu F N A e)

/-- In the case `0, _, _`, this construction gives `1`. -/
def totalCharge : (i : ℕ) → i ≤ a.waves → (Fin i → (a.selectors k).obj) → F
  | 0, _, _ => 1
  | i + 1, hi, c =>
    let j : Fin a.waves := ⟨i, hi⟩
    let p := a.path start i (Fin.init c)
    totalCharge i j.isLt.le (Fin.init c) *
      Fmt.weight (a.tariff hF j (a.menuAt hF menu k i j.isLt.le) k) (a.around p (c (Fin.last i)))

theorem charge_snoc {i : ℕ} (hi : i < a.waves) (c : Fin i → (a.selectors k).obj)
    (t : (a.selectors k).obj) :
    a.totalCharge start hF menu (i + 1) hi (Fin.snoc c t) =
      a.totalCharge start hF menu i hi.le c *
        Fmt.weight (a.tariff hF ⟨i, hi⟩ (a.menuAt hF menu k i hi.le) k) (a.around (a.path start i
          c) t) := by
  rw [totalCharge, Fin.init_snoc, Fin.snoc_last]

end Design

namespace Scenario

variable {F N A : Type} [Field F] {x y : Wire} {a : Design} (w : Scenario F N A a x y)
  {k i : ℕ}

/-- The indexing data represented by `Fin i → w.V → B k`. -/
abbrev History (k i : ℕ) := Fin i → w.V → B k

/-- Evaluates `Sparse.pack w.atlas.coord 0 (c j)` at the input `j`. -/
def tapes (c : w.History k i) : Fin i → (a.selectors k).obj :=
  fun j => Sparse.pack w.atlas.coord 0 (c j)

theorem tapes_snoc (c : w.History k i) (t : w.V → B k) :
    w.tapes (Fin.snoc c t) = Fin.snoc (w.tapes c) (Sparse.pack w.atlas.coord 0 t) := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [tapes]

end Scenario
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local
end

/- # Factoring the charge of a history over its occupied cells -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse
open Coloring Finset

open scoped Classical in
theorem prod_occupied {V F : Type} [Fintype V] [CommMonoid F] {m h : ℕ}
    (loc : V ↪ B m × B h) (f : B m × B h → F) (off : ∀ x ∉ Set.range loc, f x = 1) :
    (∏ i, ∏ j, f (i, j)) = ∏ v, f (loc v) := by
  rw [← Fintype.prod_prod_type, ← prod_image loc.injective.injOn]
  symm
  apply prod_subset (subset_univ _)
  intro i _ hi
  exact off i (by simpa using hi)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse

namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Design
open Assembly Coloring Finset

variable (a : Design) {e k : ℕ} {F N A : Type} [Field F] [Fintype F] [ExpChar F a.p]
  (start : (a.port e).obj) (hF : a.M * (2 * a.D + 1) < Fintype.card F) (menu : a.Menu F N A e)

open scoped Classical in
/-- In the case `0, _, _, _`, this construction gives `1`. -/
def localCharge : (i : ℕ) → i ≤ a.waves → (Fin i → (a.selectors k).obj) → B a.m × B a.h → F
  | 0, _, _, _ => 1
  | i + 1, hi, c, v =>
    let j : Fin a.waves := ⟨i, hi⟩
    let p := a.path start i (Fin.init c)
    localCharge i j.isLt.le (Fin.init c) v *
      a.tariff hF j (a.menuAt hF menu k i j.isLt.le) k (((a.around p (c (Fin.last i))) v.1).2 v.2)

open scoped Classical in
theorem total_eq_prod (i : ℕ) (hi : i ≤ a.waves) (c : Fin i → (a.selectors k).obj) :
    a.totalCharge start hF menu i hi c = ∏ v, ∏ w, a.localCharge start hF menu i hi c (v, w) := by
  induction i with
  | zero => simp [totalCharge, localCharge]
  | succ i ih =>
    simp only [totalCharge, localCharge, Fmt.weight, prod_mul_distrib]
    rw [ih]

open scoped Classical in
theorem vacant_step (j : Fin a.waves) (c : (a.selectors k).obj) (v : B a.m × B a.h)
    (hv : (menu ((start v.1).2 v.2)).2 = none) (hc : c v.1 v.2 = 0) :
    (a.nextMenu hF j menu k (((a.update start c) v.1).2 v.2)).2 = none ∧
      a.tariff hF j menu k (((a.around start c) v.1).2 v.2) = 1 := by
  have origin : ((a.around start c) v.1).2 v.2 0 0 = ((start v.1).2 v.2, 0) := by
    simp only [around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin, hc]
  simp [nextMenu, update, Fmt.update, tariff, route, charge, selected, origin, hv]

open scoped Classical in
theorem vacant_path (v : B a.m × B a.h) (hv : (menu ((start v.1).2 v.2)).2 = none)
    (i : ℕ) (hi : i ≤ a.waves) (c : Fin i → (a.selectors k).obj) (hc : ∀ j, c j v.1 v.2 = 0) :
    (a.menuAt hF menu k i hi (((a.path start i c) v.1).2 v.2)).2 = none ∧
      a.localCharge start hF menu i hi c v = 1 := by
  induction i with
  | zero => exact ⟨hv, rfl⟩
  | succ i ih =>
    obtain ⟨empty, unit⟩ := ih (Nat.le_of_succ_le hi) (Fin.init c) (fun j => hc j.castSucc)
    obtain ⟨hm, ht⟩ := a.vacant_step _ hF _ ⟨i, hi⟩ _ v empty (hc (Fin.last i))
    exact ⟨hm, by rw [localCharge, unit, ht, one_mul]⟩

open scoped Classical in
theorem total_occupied {V : Type} [Fintype V] (loc : V ↪ B a.m × B a.h)
    (hv : ∀ v ∉ Set.range loc, (menu ((start v.1).2 v.2)).2 = none)
    (i : ℕ) (hi : i ≤ a.waves) (c : Fin i → (a.selectors k).obj)
    (hc : ∀ j, Sparse.Supported loc 0 (c j)) :
    a.totalCharge start hF menu i hi c = ∏ v, a.localCharge start hF menu i hi c (loc v) := by
  rw [total_eq_prod]
  exact Sparse.prod_occupied loc _ (fun v h =>
    (a.vacant_path start hF menu v (hv v h) i hi c (fun j => hc j v h)).2)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Design
end

/- # Wave selectors vanish outside the occupied occurrences -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring Transcript

variable {F A N : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {e k : ℕ} {x y : Wire} {menu : a.Menu F N A e}
  (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (s : w.Code j.val menu)
  (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

theorem selector_away (i : Branch w hF j s) (v : B a.m × B a.h) (hv : v ∉ Set.range w.atlas.coord) :
    (w.selector hF j s hk).write i v.1 v.2 = 0 := by
  apply Selector.scatter_away
  rintro ⟨t, ht⟩
  exact hv ⟨_, ht⟩

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end
