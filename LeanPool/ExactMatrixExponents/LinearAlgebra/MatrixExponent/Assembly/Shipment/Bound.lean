/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Restore.Spans
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Volumes
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.PayloadProgram
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment

/-! # Reuse one old label to program a station or a relay -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore
open Coloring Chain.Frame

variable {F : Type} (S : Scheme F)

open scoped Classical in
/-- The quantity computed by `Format.pair .bit (.pair .bit (.pair (.addr 3) (.addr (1 + e))))`. -/
abbrev terminal (e : ℕ) := Format.pair .bit (.pair .bit (.pair (.addr 3) (.addr (1 + e))))

open scoped Classical in
/-- The quantity computed by `Format.pair .bit (.pair (.pair (.addr S.ℓ) (.addr S.k)) (.vec (1 +
S.e) (terminal S.e)))`. -/
abbrev script := Format.pair .bit (.pair (.pair (.addr S.ℓ) (.addr S.k)) (.vec (1
    + S.e) (terminal S.e)))

open scoped Classical in
theorem script_width : (script S).width = 1 + ((S.ℓ + S.k) + 2 ^ (1 + S.e) * (1 + (1 + (3 + (1
    + S.e))))) := by
  simp only [script, terminal, Format.width_pair, Format.width_addr, Format.width_vec]
  rw [Format.width_bit, Format.width_addr]

open scoped Classical in
/-- The value specified by `(script S).obj`. -/
abbrev Script := (script S).obj

namespace Script
variable {S} (a : Script S)

open scoped Classical in
/-- The indexed operation `(false, (0, 0), fun _ => (false, false, 0, 0))`. -/
def vacant (S : Scheme F) : Script S := (false, (0, 0), fun _ => (false, false, 0, 0))

open scoped Classical in
/-- The value specified by `((pair e).symm j).1`. -/
def dir {e : ℕ} (j : B (1 + e)) := ((pair e).symm j).1

open scoped Classical in
/-- The value specified by `((pair e).symm j).2`. -/
def channel {e : ℕ} (j : B (1 + e)) := ((pair e).symm j).2

open scoped Classical in
/-- Returns `(S.decode a.2.1.1).width a.2.1.2 (channel i)` when `(a.2.2 i).1` holds, and `0`
otherwise. -/
def size (i : B (1 + S.e)) :=
  if (a.2.2 i).1 then (S.decode a.2.1.1).width a.2.1.2 (channel i) else 0

open scoped Classical in
/-- Returns `some ((a.2.2 i).2.2.1, 0, (a.2.2 i).2.2.2)` when `(a.2.2 i).2.1` holds, and `none`
otherwise. -/
def peer (i : B (1 + S.e)) : Option (B 3 × B 0 × B (1 + S.e)) :=
  if (a.2.2 i).2.1 then some ((a.2.2 i).2.2.1, 0, (a.2.2 i).2.2.2) else none

open scoped Classical in
/-- A total reader lets the decoder use an ordinary integer offset. -/
def read (z : ∀ i, Fin (size a i) → Bool) (j : B (1 + S.e)) (n : ℕ) :=
  if h : n < size a j then z j ⟨n, h⟩ else false

variable [Field F]

open scoped Classical in
/-- The test of type `F`, constructed using `S.decode a.2.1.1`. -/
def test (z : B (1 + S.e) → ℕ → Bool) : F :=
  let p := S.decode a.2.1.1
  let k := a.2.1.2
  if a.1 then p.value k (fun j i => z (pair S.e (p.direction k j, j)) i.val)
  else if ∀ j n, n < size a (pair S.e (true, j)) →
    z (pair S.e (true, j)) n = z (pair S.e (false, j)) n then 1 else 0

open scoped Classical in
/-- Builds `Pattern F 3 0 (1 + S.e) where width _` with the specified `width`, `direction`,
`peer`, `value`. -/
def pattern : Pattern F 3 0 (1 + S.e) where
  width _ := size a
  direction _ := dir
  peer _ := peer a
  value _ z := test a (read a z)

open scoped Classical in
/-- The quantity computed by `⟨m, 3, h, 0, 1 + S.e, (script S).width, fun i => pattern ((script
S).serial.symm i)⟩`. -/
abbrev scheme (S : Scheme F) (m h : ℕ) : Scheme F :=
  ⟨m, 3, h, 0, 1 + S.e, (script S).width, fun i => pattern ((script S).serial.symm i)⟩

end Script

namespace Chain.Frame
variable [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  {C : Chain G V} (f : C.Frame) {S} {r : S.format.obj} (p : S.Presentation r G)
  (index : V → V → B 3)
local notation "H" => C.graph

open scoped Classical in
/-- The token of type `B S.ℓ × B S.k`, constructed using `p.vertex v`. -/
def token (v : G.V) : B S.ℓ × B S.k :=
  let t := p.vertex v
  ((r t.1).2 t.2.1, t.2.2)

open scoped Classical in
/-- In the case `some (w, i)`, this construction gives `(true, true, index v w, i)`. -/
def entry (v : V) (j : B (1 + S.e)) : (terminal S.e).obj :=
  if h : ∃ q, f.mark p q = (v, j) then
    match (opposite H h.choose).map (f.mark p) with
    | some (w, i) => (true, true, index v w, i)
    | none => (true, false, 0, 0)
  else (false, false, 0, 0)

open scoped Classical in
/-- The indexed operation `(decide (v ∈ Set.range C.owner), Function.extend C.owner (token p)
(fun _ => (0, 0)) (f.root v), f.entry p index v)`. -/
def encode (v : V) : Script S :=
  (decide (v ∈ Set.range C.owner), Function.extend C.owner (token p) (fun _ => (0, 0)) (f.root v),
    f.entry p index v)

open scoped Classical in
theorem token_eq (v : V) (u : G.V) (hu : f.root v = C.owner u) :
    (f.encode p index v).2.1 = token p u := by
  unfold encode
  rw [hu, f.one.extend_apply]

open scoped Classical in
theorem entry_eq (hd : p.Directed) (q : (H).End) :
    f.entry p index ((H).station q) (f.lane p q) =
      match (opposite H q).map (f.mark p) with
      | some (w, i) => (true, true, index ((H).station q) w, i)
      | none => (true, false, 0, 0) := by
  have h : ∃ z, f.mark p z = ((H).station q, f.lane p q) := ⟨q, rfl⟩
  rw [entry, dite_eq_left h, f.contacts p hd (q' := q) h.choose_spec]

open scoped Classical in
theorem marked (v : V) (j : B (1 + S.e)) :
    (f.entry p index v j).1 = true ↔ ∃ q, f.mark p q = (v, j) := by
  unfold entry
  split
  · rename_i h
    split <;> exact iff_of_true rfl h
  · exact iff_of_false Bool.false_ne_true (by assumption)

open scoped Classical in
theorem old_at (q : (H).End) : (f.old p q).1.1 = p.vertex (G.station (f.ref q)) := by
  unfold old
  obtain ⟨⟨u, i⟩, he⟩ := G.portEquiv.surjective (f.ref q)
  rw [← he, Scheme.Seating.ends_at, G.station_port]; rfl

open scoped Classical in
theorem dir_lane (q : (H).End) : Script.dir (f.lane p q) = q.isRight :=
  congrArg Prod.fst ((pair S.e).symm_apply_apply _)

open scoped Classical in
theorem length (q : (H).End) :
    Script.size (f.encode p index ((H).station q)) (f.lane p q) = S.width r (f.old p q).1 := by
  have active := (f.marked p index _ _).mpr ⟨q, rfl⟩
  change ((f.encode p index ((H).station q)).2.2 (f.lane p q)).1 = true at active
  rw [Script.size, ite_eq_left active, f.token_eq p index _ _ (f.anchor q)]
  unfold Scheme.width Scheme.pattern token
  rw [old_at]
  simp only [Script.channel, lane, Equiv.symm_apply_apply]

open scoped Classical in
theorem ordinal (q : (H).End) :
    f.offset p q < Script.size (f.encode p index ((H).station q)) (f.lane p q) := by
  rw [length]; exact (f.old p q).2.isLt

open scoped Classical in
theorem used (hd : p.Directed) (v : V) (j : B (1 + S.e)) (n : ℕ)
    (hn : n < Script.size (f.encode p index v) j) :
    ∃ q, f.mark p q = (v, j) ∧ f.offset p q = n := by
  have ha : (f.entry p index v j).1 = true := by
    by_contra h
    simp [Script.size, encode, h] at hn
  obtain ⟨q, hq⟩ := (f.marked p index v j).mp ha
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
  rw [length] at hn
  exact f.covers p hd q n hn

open scoped Classical in
theorem peer_used {v : V} {j : B (1 + S.e)}
    (hn : Script.peer (f.encode p index v) j ≠ none) : ∃ q, f.mark p q = (v, j) := by
  by_contra h
  simp [Script.peer, encode, entry, h] at hn

end Chain.Frame
end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore
end

/- # Checking the truth table of a restored station -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore.Chain.Frame
open Coloring Finset

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  {C : Chain G V} (f : C.Frame) {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G)
  (index : V → V → B 3)
local notation "H" => C.graph

open scoped Classical in
theorem lane_pass (t : C.Turn) (b : Bool) :
    f.lane p (C.relay t b) = pair S.e (b, (p.toSeating.ends (f.fromTurn t)).1.2) := by
  rw [lane, C.side_relay t b, old, pass]

open scoped Classical in
theorem offset_pass (t : C.Turn) (b : Bool) :
    f.offset p (C.relay t b) = (p.toSeating.ends (f.fromTurn t)).2.val := by
  rw [offset, old, pass]

open scoped Classical in
/-- Computes the listener by the application `z (f.lane p q) (f.offset p q)`. -/
def listener (z : B (1 + S.e) → ℕ → Bool) (q : (H).End) := z (f.lane p q) (f.offset p q)

open scoped Classical in
private theorem relay_test (hd : p.Directed) (v : V) (hv : v ∉ Set.range C.owner)
    (z : B (1 + S.e) → ℕ → Bool) :
    (∀ j n, n < Script.size (f.encode p index v) (pair S.e (true, j)) →
      z (pair S.e (true, j)) n = z (pair S.e (false, j)) n) ↔
    ∀ t, C.joint t = v → f.listener p z (C.relay t true) = f.listener p z (C.relay t false) := by
  constructor
  · intro hs t ht
    have hn := f.ordinal p index (C.relay t true)
    rw [C.station_relay, ht, lane_pass, offset_pass] at hn
    simp only [listener, lane_pass, offset_pass]
    exact hs _ _ hn
  · intro hs j n hn
    obtain ⟨q, hq, hm⟩ := f.used p index hd v _ _ hn
    obtain ⟨he, hl⟩ := Prod.mk.inj hq
    rcases C.cases_end q with ⟨i, rfl⟩|⟨t, b, rfl⟩
    · exact (hv ⟨_, (C.station_original i).symm.trans he⟩).elim
    rw [C.station_relay] at he
    rw [lane_pass] at hl
    rw [offset_pass] at hm
    obtain ⟨_, hj⟩ := Prod.mk.inj ((pair _).injective hl)
    simpa only [listener, lane_pass, offset_pass, hj, hm] using hs t he

open scoped Classical in
theorem eval_script (hd : p.Directed) (v : V) (z : B (1 + S.e) → ℕ → Bool) :
    Script.test (f.encode p index v) z = value H v (f.listener p z) := by
  rw [C.test]
  by_cases hv : v ∈ Set.range C.owner
  · obtain ⟨u, rfl⟩ := hv
    have no (t : C.Turn) : C.joint t ≠ C.owner u := by
      intro he; exact f.away t (he.symm ▸ f.fix u)
    have empty (t : C.Turn) (ht : C.joint t = C.owner u) :
        f.listener p z (C.relay t true) = f.listener p z (C.relay t false) := (no t ht).elim
    rw [ite_eq_left empty, mul_one, prod_eq_single (⟨u, rfl⟩ : {w // C.owner w = C.owner u})]
    · have yes : (f.encode p index (C.owner u)).1 = true := decide_eq_true ⟨u, rfl⟩
      rw [Script.test, ite_eq_left yes, token_eq _ _ _ _ _ (f.fix u)]
      let a : S.LocalPin r (p.vertex u) → Bool := fun i =>
        z (pair S.e (S.direction r (p.vertex u, i.1), i.1)) i.2.val
      change S.table r (p.vertex u) a = _
      rw [p.sample]
      apply congrArg (Transcript.sample (G.table u))
      funext i
      change a (p.pin u i) = f.listener p z (C.original (G.portEquiv ⟨u, i⟩))
      rw [listener, lane, offset, C.side_original, old, orig, ← hd, Scheme.Seating.ends_at]
      rfl
    · exact fun i _ hi => (hi (Subtype.ext (f.one i.property))).elim
    · simp
  · have no : ¬(f.encode p index v).1 = true := by simpa [encode] using hv
    have eq : (∏ w : {w // C.owner w = v}, value G w (f.listener p z ∘ C.original)) = 1 :=
      prod_eq_one fun i _ => (hv ⟨i.val, i.property⟩).elim
    rw [eq, one_mul, Script.test, ite_eq_right no]
    exact if_congr (f.relay_test p index hd v hv z) rfl rfl

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore.Chain.Frame
end

/- # Reading the directed chains from their local records -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore
open Coloring

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  {C : Chain G V} (f : C.Frame) {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G)
  {m h : ℕ} (out : (Script.scheme S m h).format.obj)
local notation "H" => C.graph
local notation "U" => Script.scheme S m h

open scoped Classical in
/-- The data for the written construction, including `vertex`, `index`, `dir`, `code`, `idle`. -/
structure Written where
  /-- The placement of the vertices carried by `Written`, with type `V ↪ (U).Vtx`. -/
  vertex : V ↪ (U).Vtx
  /-- The identification of the indices of type `V → V → B 3`. -/
  index : V → V → B 3
  dir : p.Directed
  code : ∀ v, (U).pattern out (vertex v) = Script.pattern (f.encode p index v)
  idle : ∀ v ∉ Set.range vertex, (U).pattern out v = Script.pattern (Script.vacant S)
  nav : ∀ (i : C.Edge) (b : Bool),
    let v := endpoint H i b
    let w := endpoint H i (!b)
    ((out (vertex v).1).1 (index v w), (vertex v).2.1, 0) = vertex w

namespace Written
variable {f p out} (a : Written f p out)

open scoped Classical in
/-- The value specified by `(a.vertex ((H).station q), f.lane p q)`. -/
def span (q : (H).End) : (U).Span := (a.vertex ((H).station q), f.lane p q)

open scoped Classical in
theorem width (v : V) (j : B (1 + S.e)) :
    (U).width out (a.vertex v, j) = Script.size (f.encode p a.index v) j := by
  unfold Scheme.width; rw [a.code]; rfl

open scoped Classical in
theorem size (q : (H).End) : (U).width out (a.span q) = S.width r (f.old p q).1 := by
  unfold span; rw [width, Chain.Frame.length]

open scoped Classical in
theorem side (q : (H).End) : (U).direction out (a.span q) = q.isRight := by
  unfold span Scheme.direction; rw [a.code]
  exact f.dir_lane p q

open scoped Classical in
/-- The address of type `(U).LocalPin out (a.vertex v)`, constructed using `(H).portEquiv ⟨v,
i⟩`. -/
def address (v : V) (i : (H).Port v) : (U).LocalPin out (a.vertex v) :=
  let e := (H).portEquiv ⟨v, i⟩
  ⟨f.lane p e, ⟨f.offset p e, by
    rw [a.width]
    exact (f.ordinal p a.index e).trans_eq (congrArg (fun w
      => Script.size (f.encode p a.index w) (f.lane p e)) ((H).station_port ⟨v, i⟩))⟩⟩

open scoped Classical in
theorem bijective (v : V) : Function.Bijective (a.address v) := by
  constructor
  · intro i j he
    have ht : (H).portEquiv ⟨v, i⟩ = (H).portEquiv ⟨v, j⟩ := by
      apply f.mark_inj p _ (congrArg (fun z => z.2.val) he)
      refine Prod.ext ?_ (congrArg Sigma.fst he)
      exact ((H).station_port ⟨v, i⟩).trans ((H).station_port ⟨v, j⟩).symm
    exact eq_of_heq (Sigma.mk.inj ((H).portEquiv.injective ht)).2
  · rintro ⟨j, n⟩
    obtain ⟨e, he, hn⟩ := f.used p a.index a.dir v j n.val (n.isLt.trans_eq (a.width v j))
    obtain ⟨hv, hj⟩ := Prod.mk.inj he
    obtain ⟨⟨u, i⟩, rfl⟩ := (H).portEquiv.surjective e
    rw [Diagram.station_port] at hv
    change u = v at hv
    subst u
    exact ⟨i, Sigma.ext hj ((Fin.heq_ext_iff (congrArg (fun j => (U).width out (a.vertex v,
      j)) hj)).mpr hn)⟩

open scoped Classical in
private theorem eval_pattern (b : Script S) (q : Pattern F 3 0 (1 + S.e)) (hq : q
    = Script.pattern b)
    (j : B 0) (x : ∀ i, Fin (q.width j i) → Bool) :
    q.value j x = Script.test b (fun i n => if h : n < q.width j i then x i ⟨n, h⟩ else false) :=
  by subst q; rfl

open scoped Classical in
/-- Builds `(U).Seating out H where vertex` with the specified `vertex`, `pin`, `cover`,
`by_contra`. -/
def seating : (U).Seating out H where
  vertex := a.vertex
  pin v := Equiv.ofBijective _ (a.bijective v)
  cover q := by
    by_contra hv
    have hn := Nat.zero_lt_of_lt q.2.isLt
    unfold Scheme.width at hn
    rw [a.idle _ hv] at hn
    exact Nat.not_lt_zero _ hn
  sample v x := by
    let z (i : B (1 + S.e)) (n : ℕ) :=
      if t : n < (U).width out (a.vertex v, i) then x ⟨i, ⟨n, t⟩⟩ else false
    have hw : (U).table out (a.vertex v) x = Script.test (f.encode p a.index v) z :=
      eval_pattern _ _ (a.code v) _ (fun i j => x ⟨i, j⟩)
    rw [hw, f.eval_script p a.index a.dir]
    apply congrArg (Transcript.sample ((H).table v))
    funext i
    change z (a.address v i).1 (a.address v i).2.val = x (a.address v i)
    unfold z
    rw [dite_eq_left (a.address v i).2.isLt]
  vacant v hv x := by
    unfold Scheme.table
    rw [eval_pattern _ _ (a.idle v hv)]
    simp [Script.test, Script.vacant, Script.size]

open scoped Classical in
theorem ends (q : (H).End) :
    (a.seating.ends q).1 = a.span q ∧ (a.seating.ends q).2.val = f.offset p q := by
  obtain ⟨⟨v, i⟩, rfl⟩ := (H).portEquiv.surjective q
  rw [Scheme.Seating.ends_at, span, Diagram.station_port]
  exact ⟨rfl, rfl⟩

end Written
end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore
end

/- # Recovering all internal and exposed spans from the short record -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore.Written
open Coloring Chain.Frame

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {V : Type} [Fintype V]
  {C : Chain G V} {f : C.Frame} {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G}
  {m h : ℕ} {out : (Script.scheme S m h).format.obj} (a : Written f p out)
local notation "H" => C.graph
local notation "U" => Script.scheme S m h

open scoped Classical in
theorem peer (q : (H).End) : (U).peer out (a.span q) = (opposite H q).map a.span := by
  unfold Scheme.peer span
  rw [a.code]
  change (Script.peer (f.encode p a.index ((H).station q)) (f.lane p q)).map _ = _
  let pin (v : (terminal S.e).obj) : Option (B 3 × B 0 × B (1 + S.e)) :=
    if v.2.1 then some (v.2.2.1, 0, v.2.2.2) else none
  change (pin (f.entry p a.index ((H).station q) (f.lane p q))).map _ = _
  rw [f.entry_eq p a.index a.dir q]
  rcases either q with ⟨i, rfl⟩|⟨e, b, rfl⟩
  · cases i <;> rfl
  rw [opposite_tip]
  change some (((out (a.vertex ((H).station (tip H e b))).1).1
      (a.index ((H).station (tip H e b)) ((H).station (tip H e (!b)))),
      (a.vertex ((H).station (tip H e b))).2.1, 0), _) =
      some (a.vertex ((H).station (tip H e (!b))), _)
  rw [station_tip, station_tip, a.nav]
  rfl

open scoped Classical in
private theorem source {q : (U).Span} (he : (U).peer out q ≠ none) :
    ∃ z, a.span z = q := by
  obtain ⟨v, j⟩ := q
  unfold Scheme.peer at he
  by_cases hv : v ∈ Set.range a.vertex
  · obtain ⟨z, rfl⟩ := hv
    rw [a.code] at he
    have hj : Script.peer (f.encode p a.index z) j ≠ none := by
      intro ht
      apply he
      change (Script.peer (f.encode p a.index z) j).map _ = none
      rw [ht]; rfl
    obtain ⟨q, hq⟩ := f.peer_used p a.index hj
    exact ⟨q, congrArg (fun t => (a.vertex t.1, t.2)) hq⟩
  · rw [a.idle _ hv] at he
    exact (he rfl).elim

open scoped Classical in
theorem internal_size (e : C.Edge) (b : Bool) :
    (U).width out (a.span (tip H e b)) = S.width r (p.wirePin e.1 false).1 := by
  rw [a.size, old_tip]
  cases f.leg e b
  · rfl
  · exact (p.proper _ _ (p.internal _).1).2.1.symm

open scoped Classical in
theorem offset_tip (e : C.Edge) (b : Bool) :
    f.offset p (tip H e b) = (p.wirePin e.1 false).2.val := by
  rw [offset, old_tip]
  cases f.leg e b
  · rfl
  · exact (p.internal _).2.symm

include a in
open scoped Classical in
theorem proper : (U).Proper out := by
  intro i j he
  obtain ⟨q, rfl⟩ := a.source (q := i) (by rw [he]; simp)
  rw [peer] at he
  rcases either q with ⟨k, rfl⟩|⟨e, b, rfl⟩
  · cases k <;> cases he
  rw [opposite_tip, Option.map_some, Option.some.injEq] at he
  subst j
  rw [peer, opposite_tip, Bool.not_not, a.internal_size, a.internal_size, a.side, a.side, side_tip,
    side_tip]
  exact ⟨rfl, rfl, by cases b <;> decide⟩

open scoped Classical in
/-- Builds `(U).Presentation out H where toSeating` with the specified `toSeating`, `proper`,
`internal`, `change`. -/
def presentation : (U).Presentation out H where
  toSeating := a.seating
  proper := a.proper
  internal e := by
    change (U).Joins out (a.seating.ends (tip H e false)) (a.seating.ends (tip H e true))
    constructor
    · rw [(a.ends _).1, (a.ends _).1, peer, opposite_tip]; rfl
    · rw [(a.ends _).2, (a.ends _).2, offset_tip, offset_tip]
  input i := by rw [(a.ends _).1, peer]; rfl
  output i := by rw [(a.ends _).1, peer]; rfl

open scoped Classical in
theorem directed : a.presentation.Directed := by
  intro t
  exact (congrArg ((U).direction out) (a.ends t).1).trans (a.side t)

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Restore.Written
end

section
/-
# Cost scales for payload movement

The address length occurs in the cost per host and contact.
The charges per span and per payload bit use only short widths.
-/

namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
open BatchDescent.Phase

/-- The data for the size construction, including `m`, `V`, `k`, `m'`, `V'`. -/
structure Size where
  /-- The `Size` field of type `ℕ`. -/
  m : ℕ
  /-- The `Size` field of type `ℕ`. -/
  V : ℕ
  /-- The `Size` field of type `ℕ`. -/
  k : ℕ
  /-- The `Size` field of type `ℕ`. -/
  m' : ℕ
  /-- The `Size` field of type `ℕ`. -/
  V' : ℕ
  /-- The `Size` field of type `ℕ`. -/
  k' : ℕ
  /-- The `Size` field of type `ℕ`. -/
  p : ℕ
  /-- The `Size` field of type `ℕ`. -/
  l : ℕ
  /-- The `Size` field of type `ℕ`. -/
  n : ℕ
  /-- The `Size` field of type `ℕ`. -/
  W : ℕ
  /-- The `Size` field of type `ℕ`. -/
  w : ℕ
  /-- The `Size` field of type `ℕ`. -/
  v : ℕ

namespace Size
variable (i : Size)
/-- The quantity computed by `1000 + i.W + i.k + i.k'`. -/
abbrev outer := 1000 + i.W + i.k + i.k'
/-- The quantity computed by `1000 + i.W + i.k + i.k' + i.p + i.l + i.n`. -/
abbrev short := 1000 + i.W + i.k + i.k' + i.p + i.l + i.n
/-- The quantity computed by `i.short + i.m + i.m' + i.w + i.v`. -/
abbrev long := i.short + i.m + i.m' + i.w + i.v
/-- The quantity computed by `2 ^ i.m + 2 ^ i.m'`. -/
abbrev hosts := 2 ^ i.m + 2 ^ i.m'
/-- The quantity computed by `i.hosts * 2 ^ i.p`. -/
abbrev links := i.hosts * 2 ^ i.p
/-- The quantity computed by `i.links * 2 ^ i.n`. -/
abbrev slots := i.links * 2 ^ i.n
/-- The quantity computed by `i.V + i.V'`. -/
abbrev volume := i.V + i.V'
/-- The maximum of the quantities in `i.k i.k'`. -/
abbrev q := max i.k i.k'
/-- The value specified by `PeerLayout.height i.m i.k i.m' i.k' i.p`. -/
abbrev height := PeerLayout.height i.m i.k i.m' i.k' i.p
/-- The quantity computed by `i.links * i.long ^ s + i.slots * i.short ^ s`. -/
abbrev bound (s : ℕ) := i.links * i.long ^ s + i.slots * i.short ^ s

theorem outer_two : 2 ≤ i.outer := by unfold outer; omega
theorem outer_le : i.outer ≤ i.short := by unfold outer short; omega
theorem two : 2 ≤ i.short := by unfold short; omega
theorem le_long : i.short ≤ i.long := by unfold long; omega
theorem two_long : 2 ≤ i.long := i.two.trans i.le_long

end Size

/-- Computes the short by the application `Poly Size.short`. -/
abbrev Short := Poly Size.short
/-- Computes the long by the application `Poly Size.long`. -/
abbrev Long := Poly Size.long
/-- The condition `∃ s : ℕ, ∀ i, f i ≤ i.bound s` on the specified data. -/
def Work (f : Size → ℕ) := ∃ s : ℕ, ∀ i, f i ≤ i.bound s

variable {f g : Size → ℕ}
theorem Short.long (h : Short f) : Long f := h.grow Size.le_long

theorem num (s : ℕ) : Short (fun _ => s) := Poly.const Size.two s
theorem k : Short Size.k := Poly.of_le Size.two (fun i => by unfold Size.short; omega)
theorem k' : Short Size.k' := Poly.of_le Size.two (fun i => by unfold Size.short; omega)
theorem q : Short Size.q := (k.add k').mono (fun _
    => max_le (Nat.le_add_right ..) (Nat.le_add_left ..))
theorem p : Short Size.p := Poly.of_le Size.two (fun i => by unfold Size.short; omega)
theorem l : Short Size.l := Poly.of_le Size.two (fun i => by unfold Size.short; omega)
theorem n : Short Size.n := Poly.of_le Size.two (fun i => by unfold Size.short; omega)
theorem rate : Short Size.W := Poly.of_le Size.two (fun i => by unfold Size.short; omega)
theorem m : Long Size.m := Poly.of_le Size.two_long (fun i => by unfold Size.long; omega)
theorem m' : Long Size.m' := Poly.of_le Size.two_long (fun i => by unfold Size.long; omega)
theorem w : Long Size.w := Poly.of_le Size.two_long (fun i => by unfold Size.long; omega)
theorem v : Long Size.v := Poly.of_le Size.two_long (fun i => by unfold Size.long; omega)

namespace Work

theorem mono (hf : Work f) (h : ∀ i, g i ≤ f i) : Work g :=
  let ⟨s, hs⟩ := hf
  ⟨s, fun i => (h i).trans (hs i)⟩

theorem add (hf : Work f) (hg : Work g) : Work (fun i => f i + g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨max s t + 1, fun i => (Nat.add_le_add (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_add_add_comm, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.two_long ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.two ..))

theorem mul (hf : Work f) (hg : Short g) : Work (fun i => f i * g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg.bound
  refine ⟨s + t, fun i => (Nat.mul_le_mul (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_mul, mul_assoc i.links, mul_assoc i.slots, pow_add, pow_add]
  gcongr
  exact i.le_long

theorem scale (hf : Work f) (hg : Short g) : Work (fun i => g i * f i) :=
  (hf.mul hg).mono fun _ => (mul_comm ..).le

theorem links (hf : Long f) : Work (fun i => i.links * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans (Nat.le_add_right ..)⟩

theorem slots : Work Size.slots := ⟨0, fun i => by simp only [Size.bound, pow_zero, mul_one]; omega⟩
end Work

/-- An exterior bit only pays for the two payload depths and the routing price. -/
abbrev Outer := Poly Size.outer

theorem outer_num (s : ℕ) : Outer (fun _ => s) := Poly.const Size.outer_two s
theorem outer_k : Outer Size.k := Poly.of_le Size.outer_two (fun i => by unfold Size.outer; omega)
theorem outer_k' : Outer Size.k' := Poly.of_le Size.outer_two (fun i => by unfold Size.outer; omega)
theorem outer_q : Outer Size.q :=
  (outer_k.add outer_k').mono fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
theorem outer_rate : Outer Size.W := Poly.of_le Size.outer_two (fun i
    => by unfold Size.outer; omega)

/-- The condition `∃ s : ℕ, ∀ i, f i ≤ i.bound s + i.volume * i.outer ^ s` on the specified
data. -/
def Heavy (f : Size → ℕ) := ∃ s : ℕ, ∀ i, f i ≤ i.bound s + i.volume * i.outer ^ s

theorem Work.heavy (h : Work f) : Heavy f :=
  let ⟨s, hs⟩ := h
  ⟨s, fun i => (hs i).trans (Nat.le_add_right ..)⟩

namespace Heavy
theorem mono (hf : Heavy f) (h : ∀ i, g i ≤ f i) : Heavy g :=
  let ⟨s, hs⟩ := hf
  ⟨s, fun i => (h i).trans (hs i)⟩

theorem add (hf : Heavy f) (hg : Heavy g) : Heavy (fun i => f i + g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨max s t + 1, fun i => (Nat.add_le_add (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_add_add_comm, add_add_add_comm (i.links * _ ^ s), ← mul_add, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.two_long ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.two ..)))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.outer_two ..))

theorem mul (hf : Heavy f) (hg : Outer g) : Heavy (fun i => f i * g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg.bound
  refine ⟨s + t, fun i => (Nat.mul_le_mul (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_mul, add_mul]
  simp only [mul_assoc, pow_add]
  gcongr
  · exact i.outer_le.trans i.le_long
  · exact i.outer_le

theorem scale (hf : Heavy f) (hg : Outer g) : Heavy (fun i => g i * f i) :=
  (hf.mul hg).mono fun _ => (mul_comm ..).le

theorem volume : Heavy Size.volume := ⟨0, fun i => by
    rw [pow_zero, mul_one]; exact Nat.le_add_left ..⟩
end Heavy
end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
end

/- # Counting the endpoint tables and fragment records -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
open Coloring Finset

namespace Size
variable (i : Size)
open scoped Classical in
/-- Computes the bank by the application `payloadBank i.m i.V i.k i.m' i.V' i.k'`. -/
abbrev bank := payloadBank i.m i.V i.k i.m' i.V' i.k'
open scoped Classical in
/-- The quantity computed by `i.bank.channels i.q (2 ^ i.p)`. -/
abbrev channels := i.bank.channels i.q (2 ^ i.p)
open scoped Classical in
/-- The quantity computed by `i.bank.Endpoint i.q (2 ^ i.p)`. -/
abbrev endpts := i.bank.Endpoint i.q (2 ^ i.p)
open scoped Classical in
/-- The quantity computed by `2 ^ i.p * 2 ^ i.n`. -/
abbrev gates := 2 ^ i.p * 2 ^ i.n

open scoped Classical in
theorem levels : ∀ a, i.bank.depth a ≤ i.q := by
  rintro (a|a)
  · exact (Nat.lt_succ_iff.mp a.1.isLt).trans (le_max_left ..)
  · exact (Nat.lt_succ_iff.mp a.1.isLt).trans (le_max_right ..)

open scoped Classical in
theorem rows : Fintype.card i.endpts ≤ (i.q + 1) ^ 2 * i.hosts := by
  change Fintype.card (Σ j : i.bank.Level i.q (2 ^ i.p), i.bank.AtDepth j.1.val) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : i.bank.Level i.q (2 ^ i.p), Fintype.card i.bank.Slot :=
      sum_le_sum fun _ _ => Fintype.card_subtype_le _
    _ = Fintype.card (i.bank.Level i.q (2 ^ i.p)) * Fintype.card i.bank.Slot := by simp
    _ ≤ (i.q + 1) * ((i.q + 1) * i.hosts) := Nat.mul_le_mul (i.bank.level_count ..) (bank_slots ..)
    _ = _ := by rw [pow_two, mul_assoc]

open scoped Classical in
theorem sends : 2 ^ i.p ≤ i.gates := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
open scoped Classical in
theorem receives : 2 ^ i.n ≤ i.gates := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
open scoped Classical in
theorem gate_pos : 0 < i.gates := (Nat.two_pow_pos _).trans_le i.sends

open scoped Classical in
theorem fragment : (Fragments.Input i.l i.p i.n).width ≤ i.gates * (i.l + (i.p + 3 * i.l)) := by
  simp only [Fragments.Input, Fragments.Entry, Intervals.span, Format.width_pair, Format.width_vec,
    Format.width_addr]
  rw [mul_add i.gates]
  refine Nat.add_le_add (Nat.mul_le_mul_right _ i.sends) (Nat.mul_le_mul i.receives ?_)
  omega

open scoped Classical in
theorem item : (Payload.Script.item i.l i.p i.n).width ≤ i.gates * (i.l + (i.p + 3 * i.l) + i.l)
    := by
  rw [Payload.Script.item, Format.width_pair, Format.width_addr, mul_add i.gates]
  exact Nat.add_le_add i.fragment (Nat.le_mul_of_pos_left _ i.gate_pos)
end Size

open scoped Classical in
theorem host_gates : Work (fun i => i.hosts * i.gates) :=
  Work.slots.mono (fun _ => (mul_assoc ..).symm.le)

open scoped Classical in
theorem slot_gates : Work (fun i => Fintype.card i.bank.Slot * i.gates) :=
  (host_gates.scale (q.add (num 1))).mono fun _ =>
    (Nat.mul_le_mul_right _ (bank_slots ..)).trans_eq (mul_assoc ..)

open scoped Classical in
theorem end_gates : Work (fun i => Fintype.card i.endpts * i.gates) :=
  (host_gates.scale ((q.add (num 1)).pow 2)).mono fun i =>
    (Nat.mul_le_mul_right _ i.rows).trans_eq (mul_assoc ..)

open scoped Classical in
private theorem fixed_width {J : Type} [Fintype J] (A : Format) :
    (Fmt.pi (fun _ : J => A)).width = Fintype.card J * A.width := by simp

open scoped Classical in
private theorem packed {f : Size → ℕ} (hf : Work (fun i => f i * i.gates)) :
    Work (fun i => f i * (Fragments.Input i.l i.p i.n).width) :=
  (hf.mul (l.add (p.add ((num 3).mul l)))).mono fun i =>
    (Nat.mul_le_mul_left _ i.fragment).trans_eq (mul_assoc ..).symm

open scoped Classical in
theorem distribution :
    Work (fun i => i.bank.distributionCost i.q (2 ^ i.p) i.l i.p i.n) := by
  have ha : Work (fun i => (i.bank.records i.l i.p i.n).width) :=
    (packed slot_gates).mono (fun _ => (fixed_width _).le)
  have hb : Work (fun i => (i.bank.copies i.q (2 ^ i.p) i.l i.p i.n).width) :=
    (packed end_gates).mono (fun _ => (fixed_width _).le)
  have hc : Short (fun i => (100 + (i.n + 4 * i.l + 2 * i.p + i.q + 2)) ^ 118) :=
    ((num 100).add ((((n.add ((num 4).mul l)).add ((num 2).mul p)).add q).add (num 2))).pow 118
  refine ((ha.add (hb.scale (num 2))).scale (num 4)).add ?_
  refine ((end_gates.mul hc).scale (num 4)).mono fun i => ?_
  have e : 2 ^ max i.p i.n ≤ i.gates := by
    change 2 ^ max i.p i.n ≤ 2 ^ i.p * 2 ^ i.n
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))
  rw [mul_left_comm _ 4, mul_assoc (Fintype.card i.endpts)]
  gcongr

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
end

/- # Bounding the dyadic routing commands -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
open Coloring Finset

open scoped Classical in
theorem height : Long Size.height := by
  have hm : Long (fun i => max i.m i.m') := (m.add m').mono fun _
    => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
  exact ((hm.add (Short.long (q.add (num 1)).clog)).add p.long).add (num 2).long

open scoped Classical in
private theorem pow_height (i : Size) : 2 ^ i.height ≤ i.links * (8 * (i.q + 1)) := by
  have hm : 2 ^ max i.m i.m' ≤ i.hosts := by
    rcases max_choice i.m i.m' with h|h
    · rw [h]; exact Nat.le_add_right ..
    · rw [h]; exact Nat.le_add_left ..
  calc
    _ = 2 ^ max i.m i.m' * 2 ^ Nat.clog 2 (i.q + 1) * 2 ^ i.p * 4 := by
      unfold Size.height PeerLayout.height PeerLayout.bits; rw [pow_add, pow_add, pow_add]; rfl
    _ ≤ i.hosts * (2 * (i.q + 1)) * 2 ^ i.p * 4 := by
      gcongr; exact Transcript.pow_clog_le_twice (by omega)
    _ = _ := by unfold Size.links; ring

open scoped Classical in
private theorem addresses {f : Size → ℕ} (hf : Long f) : Work (fun i => 2 ^ i.height * f i) :=
  (Work.links ((Short.long ((num 8).mul (q.add (num 1)))).mul hf)).mono fun i =>
    (Nat.mul_le_mul_right _ (pow_height i)).trans_eq (mul_assoc ..)

open scoped Classical in
private theorem peers : Work (fun i => PeerLayout.size i.m i.k i.m' i.k' i.p i.l) := by
  have h := (((num 101).long.add ((num 5).long.mul height)).add l.long).pow 134
  exact (addresses h).scale ((num 16).mul (q.add (num 2)))

open scoped Classical in
private theorem columns : Heavy (fun i => (Fmt.payload i.m i.V i.k).width) := by
  refine ((Heavy.volume.scale (outer_num 2)).scale (outer_k.add (outer_num 1))).mono fun i => ?_
  exact (Fmt.width_payload ..).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.le_add_right ..)))

open scoped Classical in
private theorem columns' : Heavy (fun i => (Fmt.payload i.m' i.V' i.k').width) := by
  refine ((Heavy.volume.scale (outer_num 2)).scale (outer_k'.add (outer_num 1))).mono fun i => ?_
  exact (Fmt.width_payload ..).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left
    ..)))

open scoped Classical in
private theorem cap : Heavy (fun i => i.bank.capacity) :=
  (columns.add columns').mono (fun _ => (bank_capacity ..).le)

open scoped Classical in
private theorem locals : Heavy (fun i => ∑ a, 2 ^ i.channels.localWidth a) :=
  ((cap.scale (outer_num 2)).scale (outer_q.add (outer_num 1))).mono fun i
    => i.bank.local_volume i.q (2 ^ i.p)

open scoped Classical in
private theorem labels : Work (fun i => ∑ a, 2 ^ i.channels.count a * i.channels.count a) := by
  refine ((addresses height).scale (q.add (num 1))).mono fun i => ?_
  calc
    _ ≤ ∑ _a : i.bank.Level i.q (2 ^ i.p), 2 ^ i.height * i.height := by
      refine sum_le_sum fun j _ => ?_
      have h := PeerLayout.count_bound le_rfl j
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) h) h
    _ = Fintype.card (i.bank.Level i.q (2 ^ i.p)) * (2 ^ i.height * i.height) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (i.bank.level_count ..)

open scoped Classical in
/-- Charge a pointer to the larger of the requested and local widths.
Only the latter branch can involve the exterior-bit count. -/
private theorem split_bound {A D : Format} (S : Channels A D) (j k : ℕ)
    (hk : ∀ i, S.localWidth i ≤ k) :
    S.expandCost (fun _ => j) ≤ 4 * (Fintype.card S.I * 2 ^ j * (100 + 4 * j) ^ 101 +
      (∑ i, 2 ^ S.localWidth i) * (100 + 4 * k) ^ 101 + (∑ i, 2 ^ S.count i * S.count i) + D.width)
        := by
  have step (i : S.I) : Channels.pointerCost j (S.localWidth i) ≤
      4 * (2 ^ j * (100 + 4 * j) ^ 101 + 2 ^ S.localWidth i * (100 + 4 * k) ^ 101) := by
    unfold Channels.pointerCost
    apply Nat.mul_le_mul_left
    rcases le_total (S.localWidth i) j with h|h
    · rw [max_eq_left h]
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)).trans (Nat.le_add_right ..)
    · rw [max_eq_right h]
      have := hk i
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)).trans (Nat.le_add_left ..)
  have ht := sum_le_sum (s := univ) (fun i _ => step i)
  simp only [← mul_sum, sum_add_distrib, ← sum_mul, sum_const, card_univ, smul_eq_mul] at ht
  rw [← mul_assoc (2 ^ j), mul_comm (2 ^ j) (Fintype.card S.I)] at ht
  let U := Format.pair (Fmt.pi (fun i => Perm (S.count i))) (Fmt.raw D.pins)
  change (∑ i, Channels.pointerCost j (S.localWidth i)) + 4 * U.width ≤ _
  rw [show U.width = (∑ i, 2 ^ S.count i * S.count i) + D.width by simp [U]]
  omega

open scoped Classical in
private theorem expand : Heavy (fun i => i.channels.expandCost (fun _ => i.n)) := by
  have ha : Work (fun i => Fintype.card i.channels.I * 2 ^ i.n) :=
    end_gates.mono fun i => Nat.mul_le_mul_left _ i.receives
  have hj := ha.mul (((num 100).add ((num 4).mul n)).pow 101)
  have ht := ((outer_num 100).add ((outer_num 4).mul (outer_q.add (outer_num 1)))).pow 101
  refine ((((hj.heavy.add (locals.mul ht)).add labels.heavy).add columns').scale (outer_num
    4)).mono fun i => ?_
  exact split_bound i.channels _ _ (fun j => Nat.succ_le_succ (i.levels j.2.val))

open scoped Classical in
theorem command : Heavy (fun i => Payload.Script.commandCost i.m i.V i.k i.m' i.V' i.k' (2 ^ i.p)
    i.p i.l i.n) :=
  (distribution.heavy.add (peers.heavy.add (columns'.scale ((outer_num 8000).mul
    (outer_k'.add (outer_num 2)))))).add expand

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
end

/-
# Uniform cost of moving exterior payloads

The cost per payload bit is polynomial in the short widths. The
full host addresses occur only in a term charged per contact.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment
open Coloring

namespace Size
variable (i : Size)
/-- The quantity computed by `(Payload.Script.item i.l i.p i.n).width + i.v`. -/
abbrev cap := (Payload.Script.item i.l i.p i.n).width + i.v
/-- The value specified by `Payload.Script.cost i.m i.k i.m' i.k' i.p i.l i.cap (i.W * (2 ^ i.m
* i.cap)) (i.W * (2 ^ i.m' * i.cap))`. -/
def control := Payload.Script.cost i.m i.k i.m' i.k' i.p i.l i.cap
  (i.W * (2 ^ i.m * i.cap)) (i.W * (2 ^ i.m' * i.cap))
/-- The value specified by `500000 * ((102 + i.q) ^ 8 + i.W) * (i.q + 1) ^ 2* (1 + i.volume + 2
^ i.p * i.hosts * (i.v + i.w + 1))`. -/
def payload := 500000 * ((102 + i.q) ^ 8 + i.W) * (i.q + 1) ^ 2*
  (1 + i.volume + 2 ^ i.p * i.hosts * (i.v + i.w + 1))

theorem links_pos : 0 < i.links := by unfold links hosts; positivity
theorem host_links : i.hosts ≤ i.links := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

end Size

private theorem names {f : Size → ℕ} (h : Long f) : Work (fun i => i.hosts * f i) :=
  (Work.links h).mono fun i => Nat.mul_le_mul_right _ i.host_links

private theorem threshold : Work (fun i => i.hosts * i.cap) := by
  have g := ((l.add (p.add ((num 3).mul l))).add l)
  refine ((host_gates.mul g).add (names v)).mono fun i => ?_
  unfold Size.cap
  rw [mul_add]
  exact Nat.add_le_add_right ((Nat.mul_le_mul_left _ i.item).trans_eq (mul_assoc ..).symm) _

private theorem control : Work Size.control := by
  have mail : Work (fun i => i.W * (2 ^ i.m * i.cap) + i.W * (2 ^ i.m' * i.cap)) :=
    (threshold.scale rate).mono fun i => by unfold Size.hosts; rw [add_mul, mul_add i.W]
  have cost := (((((num 101).long.add m).add m').add l.long).add k'.long).pow 60
  have prep : Work (fun i => i.hosts * (i.cap + (101 + i.m + i.m' + i.l + i.k') ^ 60)) :=
    (threshold.add (names cost)).mono fun _ => by rw [mul_add]
  have shift : Work (fun i => 2 ^ (i.m + i.p) * (i.m' + i.p)) := by
    refine (Work.links (m'.add p.long)).mono fun i => ?_
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  exact ((mail.add prep).add shift).scale ((num 50000).mul ((k.add k').add (num 2)))

private theorem payload : Heavy Size.payload := by
  have one : Work (fun _ => 1) := (Work.links (num 1).long).mono (fun i
    => by rw [mul_one]; exact i.links_pos)
  have long : Work (fun i => 2 ^ i.p * i.hosts * (i.v + i.w + 1)) := by
    refine (Work.links ((v.add w).add (num 1).long)).mono fun i => ?_
    rw [mul_comm (2 ^ i.p) i.hosts]
  exact ((one.heavy.add Heavy.volume).add long.heavy).scale
    (((outer_num 500000).mul ((((outer_num 102).add outer_q).pow 8).add outer_rate)).mul
      ((outer_q.add (outer_num 1)).pow 2))

theorem total : Heavy (fun i => i.control +
    Payload.Script.commandCost i.m i.V i.k i.m' i.V' i.k' (2 ^ i.p) i.p i.l i.n + i.payload) :=
  (control.heavy.add command).add payload

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Shipment

namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Contraction.Prices
open Assembly

theorem shipment_le : ∃ K : ℕ, ∀ (F : Type) [Field F] (W : Prices F)
    (size m V k m' V' k' p l n : ℕ),
    let s := 1000 + W.W + k + k' + p + l + n
    let t := s + m + m' + W.w + W.w ^ W.power
    W.shipment size m V k m' V' k' p l n ≤
      4 * size + (2 ^ m + 2 ^ m') * 2 ^ p * (t ^ K + 2 ^ n * s ^ K) + (V + V') * (1000 + W.W + k
        + k') ^ K := by
  obtain ⟨j, h⟩ := Shipment.total
  refine ⟨j, ?_⟩
  intro F _ W size m V k m' V' k' p l n s t
  let i : Shipment.Size := ⟨m, V, k, m', V', k', p, l, n, W.W, W.w, W.w ^ W.power⟩
  change 4 * size + (i.control + Payload.Script.commandCost m V k m' V' k' (2 ^ p) p l n)
    + i.payload ≤ _
  rw [add_assoc]
  refine (Nat.add_le_add_left (h i) _).trans_eq ?_
  change 4 * size + (i.links * t ^ j + i.links * 2 ^ n * s ^ j + (V + V') * i.outer ^ j) = 4 * size
    + i.links * (t ^ j + 2 ^ n * s ^ j) + (V + V') * i.outer ^ j
  ring

theorem shipment_bound : ∃ K : ℕ, ∀ (F : Type) [Field F] (W : Prices F)
    (size m V k m' V' k' p l n : ℕ),
    let s := 1000 + W.W + k + k' + p + l + n
    let t := s + m + m' + W.w + W.w ^ W.power
    W.shipment size m V k m' V' k' p l n ≤
      4 * size + (2 ^ m + 2 ^ m') * 2 ^ p * (t ^ K + 2 ^ n * s ^ K) + (V + V') * s ^ K := by
  obtain ⟨K, h⟩ := shipment_le
  refine ⟨K, ?_⟩
  intro F _ W size m V k m' V' k' p l n s t
  have he : 1000 + W.W + k + k' ≤ s := by unfold s; omega
  exact (h F W size m V k m' V' k' p l n).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he K)) _)

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Contraction.Prices
end
