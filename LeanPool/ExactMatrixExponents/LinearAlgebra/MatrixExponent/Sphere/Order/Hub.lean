/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Layout.Host
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Pruned
public import Mathlib.Data.List.NodupEquivFin
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing

/-! # Number of bundle incidences after routing -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout
open Finset
variable {F V I : Type} [Field F] {a b : Wire} {d : ℕ}

open Classical in
/-- A unit width on every bundle specializes the arity estimates to degree. -/
private abbrev thin (G : Bundled F a b) : Bundled F .unit .unit where
  V := G.V
  E := G.E
  state _ := Unit
  width _ := 1
  code _ := binaryCode _ _ (by simp)
  src := G.src
  dst := G.dst
  left := Empty.elim
  right := Empty.elim
  station _ _ _ _ := 1
  locality _ _ _ _ _ _ _ _ _ _ := rfl

open Classical in
private theorem thin_arity (G : Bundled F a b) (v : G.V) : (thin G).arity v = G.degree v := by
  simp [Bundled.arity, Bundled.degree, thin]

namespace Fanout
variable {G : Bundled F a b} {T : Trie V d} (H : Fanout G T I)

open Classical in
private abbrev unitFan : Fanout (thin G) T I :=
  ⟨H.site, H.one, H.near, H.group⟩

open Classical in
private theorem fan_arity (v : Node G.V d) : H.route.net.degree v = H.unitFan.route.net.arity v
    := by
  rw [← thin_arity]
  unfold Bundled.arity
  rfl

open Classical in
theorem fan_degree {k : ℕ} (hk : ∀ v, G.degree v ≤ k) (v : Node G.V d) :
    H.route.net.degree v ≤ 2 * k := by
  rw [fan_arity]
  cases v with
  | inl v => rw [Routes.old_arity, thin_arity]; have := hk v; omega
  | inr v =>
    refine (H.unitFan.relay_le v).trans ?_
    rw [thin_arity]
    exact Nat.mul_le_mul_left 2 (hk _)

end Fanout
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout
end

/-
# Diagrams with prescribed ordered station tables

Local recipes see only the two exterior strings and two lists of bundle
words. The incidence bijections preserve bundle offsets at both ends.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open Transcript Finset MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout

variable {F : Type} {a b : Wire}

open Classical in
/-- The data for the drawing construction, including `left`, `right`, `recipe`. -/
structure Drawing (G : Bundled F a b) where
  /-- The left-side data carried by `Drawing`, with type `Side G.left G.src`. -/
  left : Side G.left G.src
  /-- The right-side data carried by `Drawing`, with type `Side G.right G.dst`. -/
  right : Side G.right G.dst
  /-- The `Drawing` component of type `G.V → Recipe F`. -/
  recipe : G.V → Recipe F

namespace Drawing
variable {G : Bundled F a b} (D : Drawing G)

open Classical in
/-- Computes the front by the application `D.left.panel G.width v`. -/
abbrev front (v : G.V) := D.left.panel G.width v
open Classical in
/-- Computes the back by the application `D.right.panel G.width v`. -/
abbrev back (v : G.V) := D.right.panel G.width v

open Classical in
/-- Builds `Diagram F a b where V` with the specified `table`, `src`, `dst`. -/
abbrev diagram : Diagram F a b where
  V := G.V
  E := G.Bit
  table v := (D.front v).table (D.back v) (D.recipe v)
  src := D.left.ports G.width
  dst := D.right.ports G.width

open Classical in
theorem source (e : G.Bit) : D.diagram.source e = G.src e.1 := D.left.owner G.width (.inr e)
open Classical in
theorem target (e : G.Bit) : D.diagram.target e = G.dst e.1 := D.right.owner G.width (.inr e)

open Classical in
theorem exterior (q : slots a ⊕ slots b) :
    Packing.portEnd D.diagram q = Sum.elim G.left G.right q := by
  cases q with
  | inl i => exact D.left.owner G.width (.inl i)
  | inr i => exact D.right.owner G.width (.inl i)

open Classical in
theorem arity (v : G.V) : D.diagram.arity v = G.arity v := by
  change wd (D.left.panel G.width v).wire + wd (D.right.panel G.width v).wire = _
  rw [Side.wd_panel, Side.wd_panel, Bundled.arity]
  omega

open Classical in
theorem count (v : G.V) : (D.front v).count + (D.back v).count = G.degree v := by
  change D.left.inner.count v + D.right.inner.count v = _
  simp only [Enum.count_eq, Fintype.card_subtype, card_filter, Bundled.degree]

open Classical in
theorem vertex (x : Val a) (y : Val b) (z : G.Bit → Bool) (v : G.V) :
    D.diagram.vertex x y z v =
      D.recipe v (D.left.view G.width v (bits a x) z) (D.right.view G.width v (bits b y) z) :=
  congrArg₂ (D.recipe v) (D.left.read G.width v (bits a x) z) (D.right.read G.width v (bits b y) z)

variable [Field F]

open Classical in
theorem eval
    (valid : ∀ x y s v, D.diagram.vertex x y (G.pack s) v = G.station v x y s)
    (invalid : ∀ x y z, z ∉ Set.range G.pack → ∃ v, D.diagram.vertex x y z v = 0) :
    D.diagram.eval = G.eval := by
  rw [← Bundled.eval_diagram]
  funext x y
  apply sum_congr rfl
  intro z _
  by_cases h : z ∈ Set.range G.pack
  · obtain ⟨s, rfl⟩ := h
    exact prod_congr rfl fun v _ => (valid x y s v).trans (G.vertex x y s v).symm
  · obtain ⟨v, hv⟩ := invalid x y z h
    exact (prod_eq_zero (mem_univ v) hv).trans (G.invalid x y z h).symm

end Drawing
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- # Consecutive blocks on both sides of each physical station -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open Transcript Finset MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout

namespace Side
variable {X Y V E : Type} {f : X → V} {g : Y → V} {u v : E → V}
  (P : Side f u) (Q : Side g v) (w : E → ℕ) (a : V) (b : Bool)

open Classical in
/-- In the case `.inl _`, this construction gives `(b, none)`. -/
def remote : (P.panel w a).Port → Bool × Option (V × ℕ)
  | .inl _ => (b, none)
  | .inr ⟨i, j⟩ => (b, some (Q.peer w ⟨P.inner.get a i, j⟩))

open Classical in
theorem adjacent (i j : (P.panel w a).Port)
    (h : (P.panel w a).number i + 1 = (P.panel w a).number j)
    (he : (P.panel w a).block i = (P.panel w a).block j) :
    P.remote Q w a b j = Diagram.advance (P.remote Q w a b i) := by
  rcases i with i | ⟨i, k⟩ <;> rcases j with j | ⟨j, l⟩
  · rfl
  · simp [Panel.block] at he
  · simp [Panel.block] at he
  · have hij : i = j := Fin.ext (Nat.succ.inj he)
    subst j
    rw [Panel.number_inner, Panel.number_inner] at h
    have hl : k.val + 1 = l.val := by dsimp only at h; omega
    obtain ⟨s, hs⟩ := Q.peer_offset w (P.inner.get a i)
    unfold remote
    simp only [hs, Diagram.advance, Option.map_some, Nat.add_assoc, hl]

end Side

namespace Drawing
variable {F : Type} {a b : Wire} {G : Bundled F a b} (D : Drawing G) (v : G.V)

open Classical in
/-- Indexes the both by the coordinates of `(D.front v).Port ⊕ (D.back v).Port`. -/
abbrev Both := (D.front v).Port ⊕ (D.back v).Port

open Classical in
private def place : D.Both v ≃ Fin (D.diagram.arity v) :=
  ((D.front v).port.symm.sumCongr (D.back v).port.symm).trans
    (positions (.pair (D.front v).wire (D.back v).wire))

open Classical in
private theorem left_val (i : (D.front v).Port) :
    (D.place v (.inl i)).val = (D.front v).number i := rfl

open Classical in
private theorem right_val (i : (D.back v).Port) :
    (D.place v (.inr i)).val = wd (D.front v).wire + (D.back v).number i := rfl

open Classical in
private theorem left_peer (i : (D.front v).Port) :
    D.diagram.peer v (D.place v (.inl i)) = D.left.remote D.right G.width v false i := by
  let e := positions (.pair (D.front v).wire (D.back v).wire)
  change D.diagram.portPeer v (e.symm (e (.inl ((D.front v).port.symm i)))) = _
  rw [Equiv.symm_apply_apply]
  change (false, (D.left.ports G.width ⟨v, (D.front v).port.symm i⟩).elim (fun _ => none)
    (fun j => some (D.right.peer G.width j))) = _
  rcases i with i | ⟨i, k⟩
  · rw [D.left.ports_ext G.width v i]; rfl
  · rw [D.left.ports_inner G.width v i k]; rfl

open Classical in
private theorem right_peer (i : (D.back v).Port) :
    D.diagram.peer v (D.place v (.inr i)) = D.right.remote D.left G.width v true i := by
  let e := positions (.pair (D.front v).wire (D.back v).wire)
  change D.diagram.portPeer v (e.symm (e (.inr ((D.back v).port.symm i)))) = _
  rw [Equiv.symm_apply_apply]
  change (true, (D.right.ports G.width ⟨v, (D.back v).port.symm i⟩).elim (fun _ => none)
    (fun j => some (D.left.peer G.width j))) = _
  rcases i with i | ⟨i, k⟩
  · rw [D.right.ports_ext G.width v i]; rfl
  · rw [D.right.ports_inner G.width v i k]; rfl

open Classical in
/-- In the case `.inl i`, this construction gives `(D.front v).block i`. -/
def block : D.Both v → ℕ
  | .inl i => (D.front v).block i
  | .inr i => (D.front v).count + 1 + (D.back v).block i

open Classical in
private theorem block_lt (i : D.Both v) : D.block v i < G.degree v + 2 := by
  have hc := D.count v
  have ef : (D.front v).count = D.left.inner.count v := rfl
  cases i with
  | inl i => have := (D.front v).block_le i; unfold block; dsimp only; omega
  | inr i => have := (D.back v).block_le i; unfold block; dsimp only; omega

open Classical in
private theorem block_mono (i j : D.Both v) (h : (D.place v i).val ≤ (D.place v j).val) :
    D.block v i ≤ D.block v j := by
  have ef : (D.front v).count = D.left.inner.count v := rfl
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [left_val, right_val] at h
  all_goals simp only [block]
  · exact (D.front v).monotone i j h
  · have := (D.front v).block_le i; omega
  · have : (D.front v).number j < wd (D.front v).wire := Fin.isLt _
    omega
  · exact Nat.add_le_add_left ((D.back v).monotone i j (by omega)) _

open Classical in
private theorem block_next (i j : D.Both v)
    (h : (D.place v i).val + 1 = (D.place v j).val) (he : D.block v i = D.block v j) :
    D.diagram.peer v (D.place v j) = Diagram.advance (D.diagram.peer v (D.place v i)) := by
  have ef : (D.front v).count = D.left.inner.count v := rfl
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [block] at he
  · rw [left_peer, left_peer]
    exact D.left.adjacent D.right _ _ _ i j h he
  · have := (D.front v).block_le i; omega
  · have := (D.front v).block_le j; omega
  · rw [right_peer, right_peer]
    rw [right_val, right_val] at h
    apply D.right.adjacent D.left
    · exact Nat.add_left_cancel (by rwa [Nat.add_assoc] at h)
    · exact Nat.add_left_cancel he

open Classical in
theorem order {R : ℕ} (hR : ∀ v, G.degree v + 2 ≤ R) : D.diagram.PortOrder R := by
  intro v
  let block (i : Fin (D.diagram.arity v)) : Fin R :=
    ⟨D.block v ((D.place v).symm i), (D.block_lt v _).trans_le (hR v)⟩
  refine ⟨block, ?_, ?_⟩
  · intro i j h
    apply D.block_mono
    simpa only [Equiv.apply_symm_apply] using (show i.val ≤ j.val from h)
  · intro i j h he
    obtain ⟨i, rfl⟩ := (D.place v).surjective i
    obtain ⟨j, rfl⟩ := (D.place v).surjective j
    exact D.block_next v i j h (by simpa [block] using congrArg Fin.val he)

end Drawing
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- # Decoding a bundle with its own finite alphabet -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout

open Classical in
/-- The indexing data represented by `List Bool → Option α`. -/
abbrev Decoder (α : Type) := List Bool → Option α

variable {α β : Type}

open Classical in
/-- Extends the specified values along the indexing map, using a default elsewhere. -/
def decode (X : Type) (n : ℕ) (c : X ↪ (Fin n → Bool)) (tag : X → α) : Decoder α :=
  Function.extend (fun x => List.ofFn (c x)) (fun x => some (tag x)) (fun _ => none)

variable {X : Type} {n : ℕ} (c : X ↪ (Fin n → Bool)) (tag : X → α)

open Classical in
theorem decode_good (x : X) : decode X n c tag (List.ofFn (c x)) = some (tag x) :=
  Function.Injective.extend_apply
    (show Function.Injective (fun x => List.ofFn (c x)) from List.ofFn_injective.comp c.injective)
      _ _ x

open Classical in
theorem decode_none (x : List Bool) (h : ¬ ∃ j, List.ofFn (c j) = x) :
    decode X n c tag x = none := by simp [decode, Function.extend, h]

open Classical in
/-- Evaluates `(D x).map f` at the input `x`. -/
def Decoder.map (f : α → β) (D : Decoder α) : Decoder β := fun x => (D x).map f

open Classical in
theorem decode_comp (f : α → β) : decode X n c (f ∘ tag) = (decode X n c tag).map f := by
  funext x
  by_cases h : ∃ j, List.ofFn (c j) = x
  · obtain ⟨j, rfl⟩ := h
    simp [Decoder.map, decode_good]
  · simp [Decoder.map, decode_none _ _ _ h]

open Classical in
/-- Evaluates `if h : i.val < n then x ⟨i.val, h⟩ else false` at the input `i`. -/
def padBits (u n : ℕ) (x : Fin n → Bool) : Fin (Diagram.padWidth u n) → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

open Classical in
theorem padBits_injective (u n : ℕ) : Function.Injective (padBits u n) := by
  intro x y h
  funext i
  simpa [padBits] using congrFun h (Fin.castLE (Diagram.le_padWidth u n) i)

open Classical in
/-- Extends the specified values along the indexing map, using a default elsewhere. -/
def Decoder.pad (u n : ℕ) (D : Decoder α) : Decoder α :=
  Function.extend (fun x => List.ofFn (padBits u n x)) (fun x => D (List.ofFn x)) (fun _ => none)

open Classical in
theorem decode_pad {F : Type} {a b : Wire} (G : Bundled F a b) (e : G.E) (u : ℕ)
    (tag : G.state e → α) :
    decode _ _ ((G.pad u).code e) tag = Decoder.pad u (G.width e) (decode _ _ (G.code e) tag) := by
  let w := G.width e
  have hp (s : G.state e) : (G.pad u).code e s = padBits u w (G.code e s) := rfl
  have hi : Function.Injective (fun z => List.ofFn (padBits u w z)) :=
    List.ofFn_injective.comp (padBits_injective u w)
  funext x
  by_cases h : ∃ z, List.ofFn (padBits u w z) = x
  · obtain ⟨z, rfl⟩ := h
    rw [Decoder.pad, hi.extend_apply]
    by_cases hz : ∃ s, G.code e s = z
    · obtain ⟨s, rfl⟩ := hz
      rw [← hp, decode_good, decode_good]
    · rw [decode_none, decode_none]
      · rintro ⟨s, hs⟩; exact hz ⟨s, List.ofFn_injective hs⟩
      · rintro ⟨s, hs⟩; exact hz ⟨s, hi hs⟩
  · rw [decode_none _ _ _ (fun ⟨s, hs⟩ => h ⟨G.code e s, hs⟩)]
    simp [Decoder.pad, Function.extend, show ¬ ∃ z, List.ofFn (padBits u (G.width e) z) = x from h]

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/-
# Local scripts

A script supplies the exterior order, a list of incident operands and
an operation on their decoded symbols. The rendered recipe names
operands by local bundle offsets only. Every source checks its own
bundle words, including those omitted by the operation.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open Finset MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout

open Classical in
/-- The indexing data represented by `List Bool → List Bool → List α → F`. -/
abbrev Program (F α : Type) := List Bool → List Bool → List α → F
open Classical in
/-- Indexes the call by the coordinates of `Bool × ℕ × Decoder α`. -/
abbrev Call (α : Type) := Bool × ℕ × Decoder α

variable {F α V X : Type} {a b : Wire} {G : Bundled F a b}

open Classical in
/-- The data for the exterior construction, including `ports`, `nodup`, `mem`. -/
structure Exterior (f : X → V) where
  /-- The `Exterior` component of type `V → List X`. -/
  ports : V → List X
  nodup : ∀ v, (ports v).Nodup
  mem : ∀ v i, i ∈ ports v ↔ f i = v

variable {f : X → V}

open Classical in
/-- Builds `Enum f where count v` with the specified `count`, `elem`. -/
def Exterior.enum (B : Exterior f) : Enum f where
  count v := (B.ports v).length
  elem v := (List.Nodup.getEquiv _ (B.nodup v)).trans (Equiv.subtypeEquivRight (B.mem v))

open Classical in
theorem Exterior.values (B : Exterior f) (v : V) (x : X → Bool) :
    List.ofFn (fun i => x (B.enum.get v i)) = (B.ports v).map x := by
  change List.ofFn (x ∘ (B.ports v).get) = _
  rw [← List.map_ofFn, List.ofFn_get]

open Classical in
/-- The data for the script construction, including `left`, `right`, `tag`, `program`, `reads`. -/
structure Script (G : Bundled F a b) (α : Type) where
  /-- The left-side data carried by `Script`, with type `Exterior G.left`. -/
  left : Exterior G.left
  /-- The right-side data carried by `Script`, with type `Exterior G.right`. -/
  right : Exterior G.right
  /-- Embeds the coordinates as `∀ e, G.state e ↪ α`. -/
  tag : ∀ e, G.state e ↪ α
  /-- The `Script` component of type `G.V → Program F α`. -/
  program : G.V → Program F α
  /-- The `Script` component of type `G.V → List G.E`. -/
  reads : G.V → List G.E
  incident : ∀ v e, e ∈ reads v → G.src e = v ∨ G.dst e = v
  run : ∀ v x y z, G.station v x y z =
    program v ((left.ports v).map (bits a x)) ((right.ports v).map (bits b y))
      ((reads v).map fun e => tag e (z e))

open Classical in
/-- The value specified by `t.2.2 (((if t.1 then y else x).2[t.2.1]?).getD [])`. -/
def Call.read (t : Call α) (x y : View) : Option α :=
  t.2.2 (((if t.1 then y else x).2[t.2.1]?).getD [])

open Classical in
/-- The selected finite family `fun x y => if ∀ c ∈ checks ++ reads, c.read x y ≠ none then f
x.1 y.1 (reads.filterMap (fun c => c.read x y)) else 0`. -/
def render [Zero F] (f : Program F α) (reads checks : List (Call α)) : Recipe F :=
  fun x y => if ∀ c ∈ checks ++ reads, c.read x y ≠ none then
    f x.1 y.1 (reads.filterMap (fun c => c.read x y)) else 0

namespace Script
variable (p : Script G α)

open Classical in
/-- Uses `⟨p.left.enum, Enum.any G.src⟩` as the representation. -/
abbrev source : Side G.left G.src := ⟨p.left.enum, Enum.any G.src⟩
open Classical in
/-- Uses `⟨p.right.enum, Enum.any G.dst⟩` as the representation. -/
abbrev target : Side G.right G.dst := ⟨p.right.enum, Enum.any G.dst⟩

open Classical in
/-- Computes the signal by the application `decode _ _ (G.code e) (p.tag e)`. -/
def signal (e : G.E) := decode _ _ (G.code e) (p.tag e)

open Classical in
/-- Returns `(false, (p.source.inner.index e).val, p.signal e)` when `G.src e = v` holds, and
`(true, (p.target.inner.index e).val, p.signal e)` otherwise. -/
def call (v : G.V) (e : G.E) : Call α :=
  if G.src e = v then (false, (p.source.inner.index e).val, p.signal e)
  else (true, (p.target.inner.index e).val, p.signal e)

open Classical in
/-- The indexed operation `(univ.filter fun e => G.src e = v).toList`. -/
def checks (v : G.V) := (univ.filter fun e => G.src e = v).toList

open Classical in
/-- Builds `Drawing G where left` with the specified `left`, `right`, `recipe`. -/
abbrev drawing [Field F] : Drawing G where
  left := p.source
  right := p.target
  recipe v := render (p.program v) ((p.reads v).map (p.call v))
    ((checks (G := G) v).map (p.call v))

open Classical in
theorem read_side {X E V : Type} {l : X → V} {f : E → V} (S : Side l f)
    (w : E → ℕ) (x : X → Bool) (s : Side.Bit w → Bool) (e : E) :
    (((S.view w (f e) x s).2[(S.inner.index e).val]?).getD []) =
      List.ofFn (fun i => s ⟨e, i⟩) := by
  let q (e : E) := List.ofFn (fun i => s ⟨e, i⟩)
  change ((List.ofFn (fun j => q (S.inner.get (f e) j)))[(S.inner.index e).val]?).getD [] = q e
  simp

open Classical in
theorem read_call (v : G.V) (e : G.E) (h : G.src e = v ∨ G.dst e = v)
    (x : Val a) (y : Val b) (z : G.Bit → Bool) :
    (p.call v e).read (p.source.view G.width v (bits a x) z) (p.target.view G.width v (bits b y) z)
      =
      p.signal e (List.ofFn fun i => z ⟨e, i⟩) := by
  by_cases hs : G.src e = v
  · subst v
    simp only [call, ite_true, Call.read, Bool.false_eq_true, ite_false]
    rw [read_side]
  · have he := h.resolve_left hs
    subst v
    simp only [call, ite_eq_right hs, Call.read, ite_true]
    rw [read_side]

variable [Field F]

open Classical in
theorem valid (x : Val a) (y : Val b) (s : G.State) (v : G.V) :
    p.drawing.diagram.vertex x y (G.pack s) v = G.station v x y s := by
  rw [Drawing.vertex, p.run]
  let l := p.source.view G.width v (bits a x) (G.pack s)
  let r := p.target.view G.width v (bits b y) (G.pack s)
  have h (e : G.E) (he : G.src e = v ∨ G.dst e = v) :
      (p.call v e).read l r = some (p.tag e (s e)) :=
    (p.read_call v e he _ _ _).trans (decode_good (G.code e) (p.tag e) (s e))
  have hv : ∀ c ∈ (checks (G := G) v).map (p.call v), c.read l r ≠ none := by
    simp only [List.forall_mem_map, checks, mem_toList, mem_filter, mem_univ, true_and]
    intro e he
    rw [h e (.inl he)]
    exact Option.some_ne_none _
  have hr (es : List G.E) (hs : es ⊆ p.reads v) :
      (es.map (p.call v)).filterMap (fun c => c.read l r) = es.map (fun e => p.tag e (s e)) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      rw [List.map_cons, List.filterMap_cons, h e (p.incident _ _ (hs (by simp)))]
      exact congrArg _ (ih (fun _ ht => hs (List.mem_cons_of_mem _ ht)))
  change render _ _ _ l r = _
  have ha : ∀ c ∈ (p.reads v).map (p.call v), c.read l r ≠ none := by
    rw [List.forall_mem_map]
    intro e he
    rw [h e (p.incident _ _ he)]
    exact Option.some_ne_none _
  rw [render, ite_eq_left (List.forall_mem_append.mpr ⟨hv, ha⟩), hr _ (fun _ he => he)]
  exact congrArg₂ (fun a b => p.program v a b _) (p.left.values _ _) (p.right.values _ _)

open Classical in
theorem invalid (x : Val a) (y : Val b) (z : G.Bit → Bool) (h : z ∉ Set.range G.pack) :
    ∃ v, p.drawing.diagram.vertex x y z v = 0 := by
  have he : ∃ e, ¬ ∃ t, List.ofFn (G.code e t) = List.ofFn (fun i => z ⟨e, i⟩) := by
    by_contra! hh
    choose s hs using hh
    exact h ⟨s, funext fun j => congrFun (List.ofFn_injective (hs j.1)) j.2⟩
  obtain ⟨e, he⟩ := he
  refine ⟨G.src e, ?_⟩
  rw [Drawing.vertex]
  apply ite_eq_right
  intro h'
  have hx := h' (p.call (G.src e) e) (List.mem_append_left _ (List.mem_map_of_mem (by simp
    [checks])))
  exact hx ((p.read_call (G.src e) e (.inl rfl) _ _ _).trans (decode_none _ _ _ he))

open Classical in
theorem eval : p.drawing.diagram.eval = G.eval := p.drawing.eval p.valid p.invalid

end Script
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/-
# Counting physical table names

Boundedly many whole records are selected from finite dictionaries.
The exponent depends on the number of bundles read, never on their bit
width. The bound is uniform over all global station and edge names.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open Finset MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout

variable {α F : Type}

open Classical in
/-- In the case `0`, this construction gives `{[]}`. -/
def strings (s : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => insert [] ((s ×ˢ strings s n).image fun p => p.1 :: p.2)

open Classical in
theorem mem_strings (s : Finset α) (n : ℕ) (l : List α)
    (hl : l.length ≤ n) (h : ∀ x ∈ l, x ∈ s) : l ∈ strings s n := by
  induction n generalizing l with
  | zero => simp [strings, List.length_eq_zero_iff.mp (by omega : l.length = 0)]
  | succ n ih =>
    cases l with
    | nil => exact mem_insert_self _ _
    | cons x l =>
      apply mem_insert_of_mem
      refine mem_image.mpr ⟨(x, l), mem_product.mpr ⟨h x (by simp), ?_⟩, rfl⟩
      exact ih _ (Nat.succ_le_succ_iff.mp hl) (fun y hy => h _ (List.mem_cons_of_mem _ hy))

open Classical in
theorem card_strings (s : Finset α) (n : ℕ) : (strings s n).card ≤ (s.card + 1) ^ n := by
  induction n with
  | zero => simp [strings]
  | succ n ih =>
    refine (card_insert_le _ _).trans ((Nat.add_le_add_right card_image_le _).trans ?_)
    rw [card_product, pow_succ', add_mul, one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.one_le_pow _ _ (by omega))

open Classical in
/-- Uses `⟨e, xs.length, xs.get⟩` as the representation. -/
def Panel.ofList (e : ℕ) (xs : List ℕ) : Panel := ⟨e, xs.length, xs.get⟩

open Classical in
private theorem panel_roundtrip (p : Panel) : Panel.ofList p.ext (List.ofFn p.width) = p := by
  cases p with
  | mk e n f =>
    simp only [Panel.ofList, Panel.mk.injEq, true_and, List.length_ofFn]
    exact Function.hfunext (by simp) (fun i j h => by simp [Fin.val_eq_val_of_heq h])

open Classical in
/-- The quantity computed by `((range (u + 1)) ×ˢ strings (range (u + 1)) k).image fun p =>
Panel.ofList p.1 p.2`. -/
def panels (k u : ℕ) : Finset Panel :=
  ((range (u + 1)) ×ˢ strings (range (u + 1)) k).image fun p => Panel.ofList p.1 p.2

open Classical in
theorem panel_mem (p : Panel) {k u : ℕ} (hk : p.count ≤ k) (hu : wd p.wire ≤ u) :
    p ∈ panels k u := by
  rw [Panel.wd_wire] at hu
  refine mem_image.mpr ⟨(p.ext, List.ofFn p.width), mem_product.mpr ⟨mem_range.mpr (by omega),
    mem_strings _ _ _ (by simpa using hk) ?_⟩, panel_roundtrip p⟩
  rintro _ hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have h : p.width i ≤ p.size := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  exact mem_range.mpr (by omega)

open Classical in
theorem panel_count (k u : ℕ) : (panels k u).card ≤ (u + 1) * (u + 2) ^ k := by
  refine card_image_le.trans ?_
  rw [card_product, card_range]
  exact Nat.mul_le_mul_left _ (by simpa only [card_range] using card_strings (range (u + 1)) k)

open Classical in
/-- The value specified by `univ ×ˢ (range k ×ˢ d)`. -/
def calls (d : Finset (Decoder α)) (k : ℕ) : Finset (Call α) :=
  univ ×ˢ (range k ×ˢ d)

open Classical in
/-- The menu of type `Finset (Table F)`, constructed using `panels k u`. -/
def menu [Zero F] (ops : Finset (Program F α)) (dec : Finset (Decoder α)) (k u : ℕ) : Finset (Table
    F) :=
  let side := panels k u
  let args := strings (calls dec k) k
  ((side ×ˢ side) ×ˢ (ops ×ˢ (args ×ˢ args))).image fun s =>
    s.1.1.table s.1.2 (render s.2.1 s.2.2.1 s.2.2.2)

open Classical in
theorem menu_count [Zero F] (ops : Finset (Program F α)) (dec : Finset (Decoder α)) (k u : ℕ) :
    (menu ops dec k u).card ≤ ((u + 1) * (u + 2) ^ k) ^ 2 * ops.card * ((2 * k * dec.card
      + 1) ^ k) ^ 2 := by
  have ha : (strings (calls dec k) k).card ≤ (2 * k * dec.card + 1) ^ k := by
    simpa [calls, mul_assoc] using card_strings (calls dec k) k
  refine card_image_le.trans ?_
  rw [card_product, card_product, card_product, card_product, ← pow_two, ← pow_two, ← mul_assoc]
  gcongr
  exact panel_count _ _

namespace Script
variable [Field F] {a b : Wire} {G : Bundled F a b} (s : Script G α)
  (ops : Finset (Program F α)) (dec : Finset (Decoder α)) (k u : ℕ)

open Classical in
theorem menu_mem (ho : ∀ v, s.program v ∈ ops) (hc : ∀ e, s.signal e ∈ dec)
    (hw : ∀ v, G.arity v ≤ u) (hv : ∀ v, G.degree v ≤ k) (hr : ∀ v, (s.reads v).length ≤ k)
    (v : G.V) : s.drawing.diagram.table v ∈ menu ops dec k u := by
  let L := s.drawing.front v
  let R := s.drawing.back v
  have hdeg : L.count + R.count ≤ k := (s.drawing.count v).trans_le (hv v)
  have hwidth : wd L.wire + wd R.wire ≤ u := (s.drawing.arity v).trans_le (hw v)
  have hm (e : G.E) (he : G.src e = v ∨ G.dst e = v) : s.call v e ∈ calls dec k := by
    unfold call calls
    split_ifs with h
    · have h' : (s.source.inner.index e).val < L.count := by
        change _ < s.source.inner.count v
        rw [← h]
        exact Fin.isLt _
      exact mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_range.mpr (h'.trans_le (show L.count
        ≤ k by omega)), hc e⟩⟩
    · have h' : (s.target.inner.index e).val < R.count := by
        change _ < s.target.inner.count v
        rw [← he.resolve_left h]
        exact Fin.isLt _
      exact mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_range.mpr (h'.trans_le (show R.count
        ≤ k by omega)), hc e⟩⟩
  have hl (l : List G.E) (hn : l.length ≤ k) (hi : ∀ e ∈ l, G.src e = v ∨ G.dst e = v) :
      l.map (s.call v) ∈ strings (calls dec k) k := by
    refine mem_strings _ _ _ (by simpa using hn) ?_
    rintro _ h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact hm e (hi e he)
  let c := checks (G := G) v
  have hn : c.length ≤ k := by
    have : c.length = L.count := by
      change (univ.filter fun e => G.src e = v).toList.length = s.source.inner.count v
      rw [Enum.count_eq, Fintype.card_subtype, length_toList]
    omega
  refine mem_image.mpr ⟨((L, R), s.program v, (s.reads v).map (s.call v), c.map (s.call v)), ?_,
    rfl⟩
  simp only [mem_product]
  refine ⟨⟨panel_mem _ (by omega) (by omega), panel_mem _ (by omega) (by omega)⟩,
    ho v, hl _ (hr v) (s.incident v), hl _ hn ?_⟩
  simp only [c, checks, mem_toList, mem_filter, mem_univ, true_and]
  exact fun _ h => .inl h

end Script
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- # One equality program suffices for all relay and hub tables -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Finset

variable {F α V E X Y : Type} {a b : Wire} {G : Bundled F a b}

open Classical in
/-- Chooses the operation for the left or right summand. -/
def Exterior.lift {f : X → V} (P : Exterior f) (Y : Type) :
    Exterior (Sum.inl ∘ f : X → V ⊕ Y) where
  ports := Sum.elim P.ports (fun _ => [])
  nodup := by
    rintro (v|v)
    · exact P.nodup v
    · exact List.nodup_nil
  mem := by rintro (v|v) i <;> simp [P.mem]

open Classical in
/-- The indexed operation `l.flatMap (fun p => [p.1, p.2])`. -/
def pairs (l : List (E × E)) : List E := l.flatMap (fun p => [p.1, p.2])

open Classical in
theorem length_pairs (l : List (E × E)) : (pairs l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => change (p.1 :: p.2 :: pairs l).length = _; simp [ih]; omega

open Classical in
theorem pairs_forall (l : List (E × E)) (p : E → Prop) :
    (∀ e ∈ pairs l, p e) ↔ ∀ t ∈ l, p t.1 ∧ p t.2 := by
  simp [pairs]
  grind

open Classical in
/-- In the case `[]`, this construction gives `True`. -/
def equalPairs : List α → Prop
  | [] => True
  | [_] => False
  | x :: y :: l => x = y ∧ equalPairs l

open Classical in
/-- Evaluates `if equalPairs l then 1 else 0` at the input `_ _ l`. -/
def checkPairs [Field F] : Program F α := fun _ _ l => if equalPairs l then 1 else 0

open Classical in
theorem checkPairs_eq [Field F] (f : E → α) (l : List (E × E)) (x y : List Bool) :
    checkPairs x y ((pairs l).map f) = if ∀ p ∈ l, f p.1 = f p.2 then (1 : F) else 0 := by
  have h : equalPairs ((pairs l).map f) ↔ ∀ p ∈ l, f p.1 = f p.2 := by
    induction l with
    | nil => simp [pairs, equalPairs]
    | cons p l ih =>
      change (f p.1 = f p.2 ∧ equalPairs ((pairs l).map f)) ↔ _
      rw [List.forall_mem_cons, ih]
  simp only [checkPairs, h]

namespace Script
variable (p : Script G α)

open Classical in
/-- Uses `⟨p.left, p.right, p.tag, p.program, p.reads, p.incident, p.run⟩` as the
representation. -/
abbrev pad (u : ℕ) : Script (G.pad u) α :=
  ⟨p.left, p.right, p.tag, p.program, p.reads, p.incident, p.run⟩

open Classical in
theorem signal_pad (u : ℕ) (e : G.E) :
    (p.pad u).signal e = Decoder.pad u (G.width e) (p.signal e) := decode_pad _ _ _ _

variable (R : Routes G Y)

open Classical in
/-- Returns `⟨e, 0⟩` when `G.src e = v` holds, and `⟨e, Fin.last _⟩` otherwise. -/
def endpoint (v : G.V) (e : G.E) : R.Hop :=
  if G.src e = v then ⟨e, 0⟩ else ⟨e, Fin.last _⟩

open Classical in
theorem endpoint_incident (v : G.V) (e : G.E) (he : G.src e = v ∨ G.dst e = v) :
    R.src (endpoint R v e) = .inl v ∨ R.dst (endpoint R v e) = .inl v := by
  unfold endpoint
  split_ifs with h
  · exact .inl (by simp [Routes.src, h])
  · exact .inr (by simp [Routes.dst, he.resolve_left h])

open Classical in
/-- Computes the route tag by the application `p.tag i.1`. -/
def routeTag (i : R.Hop) := p.tag i.1

open Classical in
theorem endpoint_tag (v : G.V) (s : R.Data) (e : G.E) :
    p.routeTag R (endpoint R v e) (s (endpoint R v e)) = p.tag e (R.read v s e) := by
  unfold Routes.read
  by_cases h : G.src e = v
  · rw [ite_eq_left h, show endpoint R v e = ⟨e, 0⟩ from ite_eq_left h]
    rfl
  · rw [ite_eq_right h, show endpoint R v e = ⟨e, Fin.last _⟩ from ite_eq_right h]
    rfl

open Classical in
/-- Indexes the visit by the coordinates of `Σ e, Fin (R.length e)`. -/
abbrev Visit := Σ e, Fin (R.length e)
open Classical in
/-- Selects the elements of all indices satisfying `(fun i : Visit R => R.via i.1 i.2 = v)`. -/
def visits (v : Y) := univ.filter (fun i : Visit R => R.via i.1 i.2 = v)
open Classical in
/-- The value specified by `(⟨i.1, i.2.castSucc⟩, ⟨i.1, i.2.succ⟩)`. -/
def ends (i : Visit R) : R.Hop × R.Hop := (⟨i.1, i.2.castSucc⟩, ⟨i.1, i.2.succ⟩)
open Classical in
/-- Transforms the indexed data by `(visits R v).toList.map (ends R)`. -/
def matched (v : Y) := (visits R v).toList.map (ends R)

variable [Field F] [Fintype Y]

open Classical in
/-- Builds `Script R.net α where left` with the specified `left`, `right`, `tag`, `program`. -/
abbrev route : Script R.net α where
  left := p.left.lift Y
  right := p.right.lift Y
  tag := p.routeTag R
  program := Sum.elim p.program (fun _ => checkPairs)
  reads := Sum.elim (fun v => (p.reads v).map (endpoint R v)) (fun v => pairs (matched R v))
  incident := by
    rintro (v|v) e he
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      exact endpoint_incident R v i (p.incident v i hi)
    · have h : ∀ e ∈ pairs (matched R v), R.src e = .inr v ∨ R.dst e = .inr v := by
        rw [pairs_forall]
        rintro _ hs
        obtain ⟨⟨i, j⟩, hi, rfl⟩ := List.mem_map.mp hs
        have hj := (mem_filter.mp (mem_toList.mp hi)).2
        exact ⟨.inr (by simp [ends, Routes.dst, hj]), .inl (by simp [ends, Routes.src, hj])⟩
      exact h e he
  run := by
    rintro (v|v) x y z
    · change G.station v x y (R.read v z) =
        p.program v _ _ (((p.reads v).map (endpoint R v)).map (fun e => p.routeTag R e (z e)))
      rw [p.run, List.map_map]
      simp only [Function.comp_def, endpoint_tag]
      rfl
    · change (if R.Valid v z then 1 else 0) =
        checkPairs [] [] ((pairs (matched R v)).map (fun e => p.routeTag R e (z e)))
      rw [checkPairs_eq (F := F)]
      have he : (∀ i ∈ matched R v,
          p.routeTag R i.1 (z i.1) = p.routeTag R i.2 (z i.2)) ↔ R.Valid v z := by
        simp only [matched, List.forall_mem_map, mem_toList, visits, mem_filter, mem_univ, true_and,
          ends, routeTag, Routes.Valid, Sigma.forall]
        constructor
        · exact fun h e j hj => (p.tag e).injective (h e j hj)
        · exact fun h e j hj => congrArg (p.tag e) (h e j hj)
      simp only [he]

open Classical in
private theorem visit_count (v : Y) : (visits R v).card ≤ R.net.degree (.inr v) := by
  unfold visits Bundled.degree
  refine le_trans ?_ (Nat.le_add_right _ _)
  rw [card_filter, Fintype.sum_sigma, Fintype.sum_sigma]
  apply sum_le_sum
  intro e _
  rw [Fin.sum_univ_succ]
  simp [Routes.src]

open Classical in
theorem length_route (v : Y) : ((p.route R).reads (.inr v)).length ≤ 2 * R.net.degree (.inr v) := by
  change (pairs (matched R v)).length ≤ _
  rw [length_pairs, matched, List.length_map, length_toList]
  exact Nat.mul_le_mul_left _ (visit_count R v)

end Script
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- A station reads a list of ordinary keys; repeated reads are allowed. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Surface.Stage

variable {F U X E V K : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}

/-- The data for the rules construction, including `left`, `right`, `tag`, `label`, `reads`. -/
structure Rules (S : Sharing C a b Y) where
  /-- The left-side data carried by `Rules`, with type `Exterior S.left`. -/
  left : Exterior S.left
  /-- The right-side data carried by `Rules`, with type `Exterior S.right`. -/
  right : Exterior S.right
  /-- Embeds the coordinates as `∀ k, Y.state k ↪ Symbol (M * t)`. -/
  tag : ∀ k, Y.state k ↪ Symbol (M * t)
  /-- The label at each coordinate of type `Place C → Label F (M * r) (M * t)`. -/
  label : Place C → Label F (M * r) (M * t)
  /-- The `Rules` component of type `Place C → List K`. -/
  reads : Place C → List K
  seen : ∀ i k, k ∈ reads i → k ∈ S.reads i
  run : ∀ i x y s a' b', (item C i).table (S.param x y s) a' b' =
    label i ((left.ports i).map (bits a x)) ((right.ports i).map (bits b y))
      ((reads i).map fun k => tag k (s k)) a'.val b'.val

namespace Rules
variable {S : Sharing C a b Y} (L : Rules S)
/-- Computes the signal by the application `decode _ _ (Y.code k) (L.tag k)`. -/
def signal (k : K) := decode _ _ (Y.code k) (L.tag k)
end Rules

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- An ordinary hub compares each visible key with its local storage copy. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Finset

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y) (v : V)

open Classical in
/-- The indexed operation `univ.filter fun e => e.1 ∈ S.seen v ∧ (S.source e = .inr (.inl v) ∨
S.target e = .inr (.inl v))`. -/
def contacts : Finset S.Edge :=
  univ.filter fun e => e.1 ∈ S.seen v ∧ (S.source e = .inr (.inl v) ∨ S.target e = .inr (.inl v))

open Classical in
/-- The value specified by `(i.val, ⟨i.val.1, .inl ⟨v, (mem_filter.mp i.property).2.1⟩⟩)`. -/
def mates (i : ↥(contacts S v)) : S.Edge × S.Edge :=
  (i.val, ⟨i.val.1, .inl ⟨v, (mem_filter.mp i.property).2.1⟩⟩)

open Classical in
/-- Computes the hub reads by the application `pairs ((contacts S v).attach.toList.map (mates S
v))`. -/
def hubReads : List S.Edge := pairs ((contacts S v).attach.toList.map (mates S v))

omit [Field F] in
open Classical in
theorem hub_meets : ∀ e ∈ hubReads S v, S.source e = .inr (.inl v) ∨ S.target e = .inr (.inl v)
    := by
  unfold hubReads
  rw [pairs_forall]
  rintro _ he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(mem_filter.mp i.property).2.2, .inl rfl⟩

open Classical in
theorem hub_eval {α : Type} (tag : ∀ k, Y.state k ↪ α) (z : S.State) (x y : List Bool) :
    checkPairs x y ((hubReads S v).map (fun e => tag e.1 (z e))) =
      if S.checks (.inr (.inl v)) z then (1 : F) else 0 := by
  rw [hubReads, checkPairs_eq]
  simp only [List.forall_mem_map, mem_toList, mem_attach, true_implies]
  congr 1
  apply propext
  constructor
  · intro h k j hj e he
    have hj' : v = j.val := Sum.inl.inj (Sum.inr.inj hj)
    subst v
    let i : ↥(contacts S j.val) := ⟨⟨k, e⟩, mem_filter.mpr ⟨mem_univ _, j.property, he⟩⟩
    exact (tag k).injective (h i)
  · intro h i
    obtain ⟨_, hs, he⟩ := mem_filter.mp i.property
    exact congrArg (tag i.val.1) (h _ ⟨v, hs⟩ rfl i.val.2 he)

open Classical in
theorem length_hubReads : (hubReads S v).length ≤ 2 * S.base.degree (.inr (.inl v)) := by
  rw [hubReads, length_pairs, List.length_map, length_toList, card_attach]
  apply Nat.mul_le_mul_left
  simp only [contacts, card_filter, Bundled.degree, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  split_ifs <;> grind

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- Local operations for reassembling chunk states and evaluating sphere forms. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Surface.Stage

open Classical in
/-- The signal of type `Symbol (M * t) → Signal M r t | front : Wedge r → Signal M r t | back :
Wedge t → Signal M r t` for the given inputs. -/
inductive Signal (M r t : ℕ) where
  | key : Symbol (M * t) → Signal M r t
  | front : Wedge r → Signal M r t
  | back : Wedge t → Signal M r t

variable {M r t : ℕ}

open Classical in
/-- Indexes the args by the coordinates of `List (Symbol (M * t)) × (Fin M → Wedge r) × (Fin M →
Wedge t)`. -/
abbrev Args (M r t : ℕ) := List (Symbol (M * t)) × (Fin M → Wedge r) × (Fin M → Wedge t)

open Classical in
/-- Concatenates the components in the order `u.1.map .key ++ List.ofFn (fun j => .front (u.2.1
j)) ++ List.ofFn (fun j => .back (u.2.2 j))`. -/
def symbols (u : Args M r t) : List (Signal M r t) :=
  u.1.map .key ++ List.ofFn (fun j => .front (u.2.1 j)) ++ List.ofFn (fun j => .back (u.2.2 j))

open Classical in
private theorem symbols_injective : Function.Injective (symbols (M := M) (r := r) (t := t)) := by
  rintro ⟨x, a, b⟩ ⟨x', a', b'⟩ h
  unfold symbols at h
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_ofFn, List.length_map] at hl
  have hl₁ : (x.map (Signal.key (r := r)) ++ List.ofFn (fun i => Signal.front (a i))).length =
      (x'.map Signal.key ++ List.ofFn (fun i => Signal.front (a' i))).length := by
    simp only [List.length_append, List.length_ofFn, List.length_map]
    omega
  obtain ⟨h, hb⟩ := List.append_inj h hl₁
  let key : Symbol (M * t) → Signal M r t := Signal.key
  have hl₂ : (x.map key).length = (x'.map key).length := by
    simp only [List.length_map]
    omega
  obtain ⟨hx, ha⟩ := List.append_inj h hl₂
  have hx' := Function.Injective.list_map (fun _ _ he => Signal.key.inj he) hx
  have ha' : a = a' := funext fun i => Signal.front.inj (congrFun (List.ofFn_injective ha) i)
  have hb' : b = b' := funext fun i => Signal.back.inj (congrFun (List.ofFn_injective hb) i)
  exact Prod.ext hx' (Prod.ext ha' hb')

variable {F : Type} [Field F]

open Classical in
/-- The indexed operation `fun x y => Function.extend symbols (fun u => f x y u.1 (Chunk.join
u.2.1) (Chunk.join u.2.2)) (fun _ => 0)`. -/
def load (f : Label F (M * r) (M * t)) : Program F (Signal M r t) :=
  fun x y => Function.extend symbols
    (fun u => f x y u.1 (Chunk.join u.2.1) (Chunk.join u.2.2)) (fun _ => 0)

open Classical in
theorem load_symbols (f : Label F (M * r) (M * t)) (x y : List Bool) (u : Args M r t) :
    load f x y (symbols u) = f x y u.1 (Chunk.join u.2.1) (Chunk.join u.2.2) :=
  symbols_injective.extend_apply _ _ u

open Classical in
/-- In the case `.front a`, this construction gives `a`. -/
def Signal.first : Signal M r t → Wedge r
  | .front a => a
  | _ => ⟨[], by simp⟩

open Classical in
/-- In the case `.back a`, this construction gives `a`. -/
def Signal.second : Signal M r t → Wedge t
  | .back a => a
  | _ => ⟨[], by simp⟩

open Classical in
/-- Evaluates `wick fieldKernel (z.zipWith (fun v s => Surface.modes v (g s)) u).flatten` at the
input `_ _ u`. -/
def chamber {α : Type} (g : α → Wedge r) (z : List F) : Program F α :=
  fun _ _ u => wick fieldKernel (z.zipWith (fun v s => Surface.modes v (g s)) u).flatten

open Classical in
theorem chamber_eval {α I : Type} (g : α → Wedge r) (h : I → α) (z : I → F)
    (l : List I) (x y : List Bool) :
    chamber g (l.map z) x y (l.map h) = Layout.read z (g ∘ h) l := by
  unfold chamber Layout.read
  congr 1
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.flatten_cons, List.flatMap_cons, ih,
      Function.comp_apply]

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end
