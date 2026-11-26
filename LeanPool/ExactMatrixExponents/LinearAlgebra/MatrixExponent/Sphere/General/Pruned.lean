/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Normalize
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Processor.Labels
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Restore.Spans
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Pad

/-! # Endpoints retained by loop removal -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

/-- The subtype of `e : G.E` satisfying `G.source e = v ∧ G.target e = v`. -/
abbrev LocalLoop (v : G.V) := {e : G.E // G.source e = v ∧ G.target e = v}

variable [Field F]

/-- Embeds `G.removeLoops.End` into `G.End`. -/
def embedEnd : G.removeLoops.End ↪ G.End :=
  let c : G.removeLoops.E ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  ((Function.Embedding.refl (slots a)).sumMap c).sumMap ((Function.Embedding.refl (slots b)).sumMap
    c)

theorem station_embedEnd (p : G.removeLoops.End) :
    G.station (G.embedEnd p) = G.removeLoops.station p := by
  rcases p with (p|p)|(p|p) <;> rfl

end MatrixMultiplicationAllFields.MatrixExponent.Diagram
end

/-
# The local order of a station's ports

Each side begins with its exterior bits. Named internal bundles follow
in the chosen order, with ascending offsets inside each bundle.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open Transcript Finset

/-- Indexes the view by the coordinates of `List Bool × List (List Bool)`. -/
abbrev View := List Bool × List (List Bool)
/-- The indexing data represented by `View → View → F`. -/
abbrev Recipe (F : Type) := View → View → F

/-- The data for the panel construction, including `ext`, `count`, `width`. -/
structure Panel where
  /-- Stores the ext associated with this `Panel`. -/
  ext : ℕ
  /-- The number of entries. -/
  count : ℕ
  /-- The width parameter carried by `Panel`, with type `Fin count → ℕ`. -/
  width : Fin count → ℕ

namespace Panel
variable (P : Panel)

/-- The sum of `P.width i` indexed by `i`. -/
def size := ∑ i, P.width i
/-- Indexes the inner by the coordinates of `Σ i, Fin (P.width i)`. -/
abbrev Inner := Σ i, Fin (P.width i)
/-- Indexes the port by the coordinates of `Fin P.ext ⊕ P.Inner`. -/
abbrev Port := Fin P.ext ⊕ P.Inner

/-- Computes the wire by the application `Wire.pair (word P.ext) (word P.size)`. -/
def wire := Wire.pair (word P.ext) (word P.size)

theorem wd_wire : wd P.wire = P.ext + P.size := by simp [wire, wd, wd_word]

/-- The value specified by `(positions (word n)).trans (finCongr (wd_word n))`. -/
def bitOrder (n : ℕ) := (positions (word n)).trans (finCongr (wd_word n))

/-- Reindexes `Fin P.size` and `P.Inner` by an equivalence. -/
def serial : Fin P.size ≃ P.Inner :=
  (Fintype.orderIsoFinOfCardEq (Lex P.Inner) (by simp [size, Inner])).toEquiv.trans ofLex

/-- Reindexes `slots P.wire` and `P.Port` by an equivalence. -/
def port : slots P.wire ≃ P.Port :=
  (bitOrder P.ext).sumCongr ((bitOrder P.size).trans P.serial)

/-- The value specified by `((positions P.wire) (P.port.symm i)).val`. -/
def number (i : P.Port) := ((positions P.wire) (P.port.symm i)).val

/-- Chooses the operation for the left or right summand. -/
def block : P.Port → ℕ := Sum.elim (fun _ => 0) (fun i => i.1.val + 1)

theorem block_le (i : P.Port) : P.block i ≤ P.count := by
  cases i with
  | inl _ => exact Nat.zero_le _
  | inr i => exact i.1.isLt

private theorem bitOrder_val (n : ℕ) (i : Fin n) :
    ((positions (word n)) ((bitOrder n).symm i)).val = i.val := by
  simp [bitOrder]

theorem number_ext (i : Fin P.ext) : P.number (.inl i) = i.val := by
  change ((positions (word P.ext)) ((bitOrder P.ext).symm i)).val = _
  exact bitOrder_val _ _

theorem number_inner (i : P.Inner) :
    P.number (.inr i) = P.ext + Processor.start P.width i.1 + i.2.val := by
  change wd (word P.ext) + ((positions (word P.size)) ((bitOrder P.size).symm (P.serial.symm
    i))).val = _
  rw [wd_word, bitOrder_val, Nat.add_assoc]
  congr 1
  exact Processor.serial_rank _ _ (toLex i)

theorem monotone (i j : P.Port) (h : P.number i ≤ P.number j) : P.block i ≤ P.block j := by
  cases i with
  | inl _ => exact Nat.zero_le _
  | inr i =>
    rw [number_inner] at h
    cases j with
    | inl j => rw [number_ext] at h; have := j.isLt; omega
    | inr j =>
      rw [number_inner] at h
      change i.1.val + 1 ≤ j.1.val + 1
      by_contra! he
      have hj : j.1 < i.1 := Fin.lt_def.mpr (by omega)
      have hh := Processor.start_left P.width _ _ hj
      have := j.2.isLt
      omega

/-- The view of type `View` for the given inputs. -/
def view (x : Val P.wire) : View :=
  (List.ofFn fun i => bits P.wire x (P.port.symm (.inl i)),
    List.ofFn fun j : Fin P.count => List.ofFn fun i => bits P.wire x (P.port.symm (.inr ⟨j, i⟩)))

/-- Uses `⟨P.wire, Q.wire, fun x y => f (P.view x) (Q.view y)⟩` as the representation. -/
def table {F : Type} (Q : Panel) (f : Recipe F) : Table F :=
  ⟨P.wire, Q.wire, fun x y => f (P.view x) (Q.view y)⟩

end Panel
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- Incidence bijections with independently prescribed local orders. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
open Transcript Finset

variable {X V E : Type} {f : X → V}

open Classical in
/-- The data for the enum construction, including `count`, `elem`. -/
structure Enum (f : X → V) where
  /-- The number of entries of type `V → ℕ`. -/
  count : V → ℕ
  /-- Reindexes the data using `∀ v, Fin (count v) ≃ {x // f x = v}`. -/
  elem : ∀ v, Fin (count v) ≃ {x // f x = v}

namespace Enum
open Classical in
/-- Uses `⟨fun v => Fintype.card {x // f x = v}, fun _ => (Fintype.equivFin _).symm⟩` as the
representation. -/
def any [Fintype X] (f : X → V) : Enum f :=
  ⟨fun v => Fintype.card {x // f x = v}, fun _ => (Fintype.equivFin _).symm⟩

variable (B : Enum f)

open Classical in
/-- Reindexes `(Σ v, Fin (B.count v))` and `X` by an equivalence. -/
def full : (Σ v, Fin (B.count v)) ≃ X :=
  (Equiv.sigmaCongrRight B.elem).trans (Equiv.sigmaFiberEquiv f)

open Classical in
/-- The value specified by `B.full ⟨v, i⟩`. -/
abbrev get (v : V) (i : Fin (B.count v)) := B.full ⟨v, i⟩

open Classical in
/-- The value specified by `(B.elem (f x)).symm ⟨x, rfl⟩`. -/
def index (x : X) := (B.elem (f x)).symm ⟨x, rfl⟩

open Classical in
theorem owner (v : V) (i : Fin (B.count v)) : f (B.get v i) = v := (B.elem v i).property

open Classical in
@[simp] theorem get_index (x : X) : B.get (f x) (B.index x) = x :=
  congrArg Subtype.val ((B.elem (f x)).apply_symm_apply ⟨x, rfl⟩)

open Classical in
theorem count_eq [Fintype X] (v : V) : B.count v = Fintype.card {x // f x = v} :=
  (Fintype.card_fin _).symm.trans (Fintype.card_congr (B.elem v))

end Enum

open Classical in
/-- The data for the side construction, including `ext`, `inner`. -/
structure Side (f : X → V) (g : E → V) where
  /-- The `Side` component of type `Enum f`. -/
  ext : Enum f
  /-- The internal data of type `Enum g`. -/
  inner : Enum g

namespace Side

variable {g : E → V} (S : Side f g) (w : E → ℕ)

open Classical in
/-- Uses `⟨S.ext.count v, S.inner.count v, fun j => w (S.inner.get v j)⟩` as the representation. -/
abbrev panel (v : V) : Panel :=
  ⟨S.ext.count v, S.inner.count v, fun j => w (S.inner.get v j)⟩

open Classical in
/-- Indexes the bit by the coordinates of `Σ e, Fin (w e)`. -/
abbrev Bit := Σ e, Fin (w e)

open Classical in
/-- Reindexes `(Σ v, slots (S.panel w v).wire)` and `X ⊕ Bit w` by an equivalence. -/
def ports : (Σ v, slots (S.panel w v).wire) ≃ X ⊕ Bit w :=
  (Equiv.sigmaCongrRight fun v => (S.panel w v).port).trans <|
    (Equiv.sigmaSumDistrib _ _).trans <|
      S.ext.full.sumCongr ((Equiv.sigmaAssoc fun v j => Fin (w (S.inner.get v j))).symm.trans
        (Equiv.sigmaCongrLeft (β := fun e => Fin (w e)) S.inner.full))

open Classical in
theorem ports_ext (v : V) (i : Fin (S.ext.count v)) :
    S.ports w ⟨v, (S.panel w v).port.symm (.inl i)⟩ = .inl (S.ext.get v i) := by
  simp [ports, Enum.get, Equiv.sigmaAssoc]

open Classical in
theorem ports_inner (v : V) (i : Fin (S.inner.count v)) (k : Fin (w (S.inner.get v i))) :
    S.ports w ⟨v, (S.panel w v).port.symm (.inr ⟨i, k⟩)⟩ = .inr ⟨S.inner.get v i, k⟩ := by
  simp [ports, Enum.get, Equiv.sigmaAssoc]

open Classical in
theorem owner (i : X ⊕ Bit w) :
    ((S.ports w).symm i).1 = Sum.elim f (fun e => g e.1) i := by
  obtain ⟨⟨v, k⟩, rfl⟩ := (S.ports w).surjective i
  rw [Equiv.symm_apply_apply]
  obtain ⟨j|⟨j, l⟩, rfl⟩ := (S.panel w v).port.symm.surjective k
  · rw [S.ports_ext w v j]; exact (S.ext.owner _ _).symm
  · rw [S.ports_inner w v j l]; exact (S.inner.owner _ _).symm

open Classical in
/-- The peer of type `V × ℕ`, constructed using `(S.ports w).symm (.inr i)`. -/
def peer (i : Bit w) : V × ℕ :=
  let s := (S.ports w).symm (.inr i)
  (s.1, (positions (S.panel w s.1).wire s.2).val)

open Classical in
theorem peer_offset (e : E) : ∃ n : ℕ, ∀ k, S.peer w ⟨e, k⟩ = (g e, n + k.val) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := S.inner.full.surjective e
  refine ⟨S.ext.count v + Processor.start (S.panel w v).width i, fun k => ?_⟩
  change S.peer w ⟨S.inner.get v i, k⟩ = (g (S.inner.get v i), _)
  unfold peer
  rw [← ports_inner, Equiv.symm_apply_apply, S.inner.owner]
  exact congrArg (fun n => (v, n)) ((S.panel w v).number_inner ⟨i, k⟩)

open Classical in
/-- The indexed operation `(List.ofFn (fun i => x (S.ext.get v i)), List.ofFn (fun i =>
List.ofFn (fun k => y ⟨S.inner.get v i, k⟩)))`. -/
def view (v : V) (x : X → Bool) (y : Bit w → Bool) : View :=
  (List.ofFn (fun i => x (S.ext.get v i)),
    List.ofFn (fun i => List.ofFn (fun k => y ⟨S.inner.get v i, k⟩)))

open Classical in
theorem read (v : V) (x : X → Bool) (z : Bit w → Bool) :
    (S.panel w v).view ((bits (S.panel w v).wire).symm (fun i => Sum.elim x z (S.ports w ⟨v, i⟩))) =
      S.view w v x z := by
  simp only [Panel.view, Equiv.apply_symm_apply, view]
  refine Prod.ext (congrArg List.ofFn (funext fun i => ?_))
    (congrArg List.ofFn (funext fun i => congrArg List.ofFn (funext fun j => ?_)))
  · rw [S.ports_ext w v i]; rfl
  · rw [S.ports_inner w v i j]; rfl

open Classical in
theorem wd_panel [Fintype X] [Fintype E] (v : V) :
    wd (S.panel w v).wire = Fintype.card {x // f x = v} + ∑ e, if g e = v then w e else 0 := by
  rw [Panel.wd_wire]
  change S.ext.count v + (∑ i, w (S.inner.get v i)) = _
  rw [S.ext.count_eq, ← sum_filter, sum_subtype _ (by simp : ∀ e, e ∈ univ.filter (fun e => g e
    = v) ↔ g e = v) w]
  exact congrArg _ ((S.inner.elem v).sum_comp (fun j => w j.val))

end Side
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order
end

/- # Local table values after contracting self-loops -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Diagram

open Assembly.Restore

variable {F : Type} {a b : Wire} (G : Diagram F a b) [Field F]

open scoped Classical in
private def extendSide {I : Type} (v : G.V) (x : I ⊕ G.removeLoops.E → Bool)
    (z : G.LocalLoop v → Bool) : I ⊕ G.E → Bool
  | .inl i => x (.inl i)
  | .inr e => if h : G.source e ≠ G.target e then x (.inr ⟨e, h⟩)
    else if hv : G.source e = v ∧ G.target e = v then z ⟨e, hv⟩ else false

open scoped Classical in
private theorem weight_remove (v : G.V) (x : slots a ⊕ G.removeLoops.E → Bool)
    (y : slots b ⊕ G.removeLoops.E → Bool) :
    G.removeLoops.weight v x y = ∑ z : G.LocalLoop v → Bool,
      G.weight v (G.extendSide v x z) (G.extendSide v y z) := by
  unfold removeLoops
  rw [weight_ofLocal]
  · rfl
  · intro w x₁ y₁ x₂ y₂ hx hy
    change (∑ z : G.LocalLoop w → Bool, G.weight w (G.extendSide w x₁ z) (G.extendSide w y₁ z)) =
      ∑ z : G.LocalLoop w → Bool, G.weight w (G.extendSide w x₂ z) (G.extendSide w y₂ z)
    apply Finset.sum_congr rfl
    intro z _
    apply G.local_weight
    · rintro (p|e) hp
      · exact hx (.inl p) hp
      · by_cases h : G.source e ≠ G.target e
        · simpa only [extendSide, dite_eq_left h] using hx (.inr ⟨e, h⟩) hp
        · simp only [extendSide, dite_eq_right h]
    · rintro (p|e) hp
      · exact hy (.inl p) hp
      · by_cases h : G.source e ≠ G.target e
        · simpa only [extendSide, dite_eq_left h] using hy (.inr ⟨e, h⟩) hp
        · simp only [extendSide, dite_eq_right h]

open scoped Classical in
/-- Values on ports at other stations are immaterial. The two ends of
each removed loop share one summation bit. -/
theorem loopTable (v : G.V) (x : G.removeLoops.End → Bool)
    (y : (G.LocalLoop v → Bool) → G.End → Bool)
    (retained : ∀ z p, G.removeLoops.station p = v → y z (G.embedEnd p) = x p)
    (removed : ∀ z (e : G.LocalLoop v) d, y z (tip G e.val d) = z e) :
    Transcript.sample (G.removeLoops.table v) (fun p => x (G.removeLoops.portEquiv ⟨v, p⟩)) =
      ∑ z, Transcript.sample (G.table v) (fun p => y z (G.portEquiv ⟨v, p⟩)) := by
  change G.removeLoops.weight v (x ∘ Sum.inl) (x ∘ Sum.inr) =
    ∑ z, G.weight v (y z ∘ Sum.inl) (y z ∘ Sum.inr)
  rw [weight_remove]
  apply Finset.sum_congr rfl
  intro z _
  apply G.local_weight
  · rintro (p|e) hp
    · exact (retained z (.inl (.inl p)) hp).symm
    · by_cases h : G.source e ≠ G.target e
      · rw [extendSide, dite_eq_left h]
        exact (retained z (.inl (.inr ⟨e, h⟩)) hp).symm
      · have hv : G.source e = v ∧ G.target e = v := ⟨hp, (not_ne_iff.mp h).symm.trans hp⟩
        rw [extendSide, dite_eq_right h, dite_eq_left hv]
        exact (removed z ⟨e, hv⟩ false).symm
  · rintro (p|e) hp
    · exact (retained z (.inr (.inl p)) hp).symm
    · by_cases h : G.source e ≠ G.target e
      · rw [extendSide, dite_eq_left h]
        exact (retained z (.inr (.inr ⟨e, h⟩)) hp).symm
      · have hv : G.source e = v ∧ G.target e = v := ⟨(not_ne_iff.mp h).trans hp, hp⟩
        rw [extendSide, dite_eq_right h, dite_eq_left hv]
        exact (removed z ⟨e, hv⟩ true).symm

end MatrixMultiplicationAllFields.MatrixExponent.Diagram
end
