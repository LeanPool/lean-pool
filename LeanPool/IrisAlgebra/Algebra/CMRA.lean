/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sukharik (@suhr), Markus de Medeiros, Puming Liu, Janine Lohse
-/
module

public import LeanPool.IrisAlgebra.Algebra.OFE
public import LeanPool.IrisAlgebra.Algebra.Monoid

/-! Ordered resource algebras and their morphisms.

Copyright (c) The Iris-Lean Contributors.
-/

@[expose] public section

namespace Iris
open OFE

/-- The underlying operation of a resource. -/
class Op (α : Type _) [OFE α] where
  /-- The composition operation. -/
  op : α → α → α
  op_ne : NonExpansive (op x)
  assoc : op x (op y z) = op (op x y) z
  comm : op x y = op y x

namespace Op

@[inherit_doc] infix:60 " • " => op

variable [OFE α] [Op α]

/-- The composition operation with an optional right argument. -/
def optionalOp (x : α) : Option α → α
  | some y => x • y
  | none => x
@[inherit_doc] infix:60 " •? " => optionalOp

end Op

/-- The partial core operator for a resource algebra. -/
class PCore (α : Type _) [OFE α] where
  /-- The partial core of a resource. -/
  pcore : α → Option α
  pcore_ne {n : Nat} {x y cx : α} : x ≡{n}≡ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx
      ≡{n}≡ cy
  pcore_idem {x cx : α} : pcore x = some cx → pcore cx = some cx

namespace PCore
variable [OFE α] [PCore α]

/-- The total core operation. -/
def core (x : α) := (pcore x).getD x

end PCore

/-- A resource algebra whose core is total. -/
class IsTotal (α : Type _) [OFE α] [PCore α] : Prop where
  total (x : α) : ∃ cx, PCore.pcore x = some cx

/-- The validity predicates of a resource algebra. -/
class Validity (α : Type _) [OFE α] where
  /-- The step-indexed validity predicate. -/
  ValidN : Nat → α → Prop
  /-- The validity predicate. -/
  Valid : α → Prop
  validN_ne : x ≡{n}≡ y → ValidN n x → ValidN n y
  valid_iff_validN : Valid x ↔ ∀ n, ValidN n x
  validN_succ : ValidN n.succ x → ValidN n x

namespace Validity

@[inherit_doc] prefix:50 "✓ " => Validity.Valid
@[inherit_doc] notation:50 "✓{" n "} " x:51 => Validity.ValidN n x

end Validity

/-- The ordering predicate on a resource algebra. -/
class Ordered (α : Type _) [OFE α] where
  /-- The indexed ordering predicate. This is the generic ORA order predicate; if your ORA is
  `OrdInc`, the lemma `ordN_incN` converts it to the extension order typical of Iris CMRAs. -/
  OrderN : Nat → α → α → Prop
  /-- The ordering predicate. This is the generic ORA order predicate; if your ORA is `OrdInc`,
  the lemma `ord_inc` converts it to the extension order typical of Iris CMRAs. -/
  Order : α → α → Prop
  ordN_ne {n} {x x' y y' : α} : x ≡{n}≡ x' → y ≡{n}≡ y' → OrderN n x y → OrderN n x' y'
  ordN_succ {n} {x y : α} : OrderN n.succ x y → OrderN n x y
  ordN_trans {n} {x y z : α} : OrderN n x y → OrderN n y z → OrderN n x z
  ord_trans {x y z : α} : Order x y → Order y z → Order x z
  ordN_of_ord {x y : α} (n) : Order x y → OrderN n x y

namespace Ordered

@[inherit_doc] notation:50 x " ≼ₒ{" n "} " y:51 => OrderN n x y
@[inherit_doc] infix:50 " ≼ₒ " => Order

variable [OFE α] [Ordered α]

/-- The reflexive closure of the step-indexed order. -/
def OrderNR (n : Nat) (x y : α) : Prop := x ≡{n}≡ y ∨ x ≼ₒ{n} y
@[inherit_doc] notation:50 x " ≼ₒ*{" n "} " y:51 => OrderNR n x y

/-- The reflexive closure of the order. -/
def OrderR (x y : α) : Prop := x = y ∨ x ≼ₒ y
@[inherit_doc] infix:50 " ≼ₒ* " => OrderR

theorem OrderN.ordNR {n} {x y : α} : x ≼ₒ{n} y → x ≼ₒ*{n} y := .inr
theorem Order.ordR {x y : α} : x ≼ₒ y → x ≼ₒ* y := .inr

@[refl] theorem OrderNR.rfl {n} {x : α} : x ≼ₒ*{n} x := .inl .rfl
@[refl] theorem OrderR.rfl {x : α} : x ≼ₒ* x := .inl (Eq.refl x)

theorem OrderNR.ne {n} {x x' y y' : α} (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') :
    x ≼ₒ*{n} y → x' ≼ₒ*{n} y'
  | .inl e => .inl (ex.symm.trans (e.trans ey))
  | .inr h => .inr (ordN_ne ex ey h)

theorem OrderNR.succ {n} {x y : α} : x ≼ₒ*{n.succ} y → x ≼ₒ*{n} y
  | .inl e => .inl (e.le (Nat.le_succ n))
  | .inr h => .inr (ordN_succ h)

theorem OrderNR.trans {n} {x y z : α} : x ≼ₒ*{n} y → y ≼ₒ*{n} z → x ≼ₒ*{n} z
  | .inl e₁, .inl e₂ => .inl (e₁.trans e₂)
  | .inl e₁, .inr h₂ => .inr (ordN_ne e₁.symm .rfl h₂)
  | .inr h₁, .inl e₂ => .inr (ordN_ne .rfl e₂ h₁)
  | .inr h₁, .inr h₂ => .inr (ordN_trans h₁ h₂)

theorem OrderR.trans {x y z : α} : x ≼ₒ* y → y ≼ₒ* z → x ≼ₒ* z
  | .inl e₁, h₂ => e₁ ▸ h₂
  | h₁, .inl e₂ => e₂ ▸ h₁
  | .inr h₁, .inr h₂ => .inr (ord_trans h₁ h₂)

theorem OrderR.ordNR (n) {x y : α} : x ≼ₒ* y → x ≼ₒ*{n} y
  | .inl e => .inl (e ▸ .rfl)
  | .inr h => .inr (ordN_of_ord n h)

end Ordered

/-- Reflexivity of the order: the order law of unital algebras (`UORA`), also enjoyed by
total algebras under their extension inclusion. -/
class OrderRefl (α : Type _) [OFE α] [Ordered α] : Prop where
  ord_refl (x : α) : x ≼ₒ x

/-- An element `x` is increasing if composing with it never shrinks a resource. Cores and units
are increasing; in an affine algebra every element is. -/
class Increasing {α : Type _} [OFE α] [Op α] [Ordered α] (x : α) : Prop where
  increasing (y : α) : y ≼ₒ x • y

/-- The step-indexed extension inclusion: `y` is `x` composed with some frame. This is the
inclusion of classical resource algebras. -/
def IncludedN {α : Type _} [OFE α] [Op α] (n : Nat) (x y : α) : Prop := ∃ z : α, y ≡{n}≡ x • z
@[inherit_doc] notation:50 x " ≼{" n "} " y:51 => IncludedN n x y

/-- The extension inclusion: `y` is `x` composed with some frame. -/
def Included {α : Type _} [OFE α] [Op α] (x y : α) : Prop := ∃ z : α, y = x • z
@[inherit_doc] infix:50 " ≼ " => Included

/-- The extension inclusion is contained in the order: every element is increasing. -/
class IncOrd (α : Type _) [OFE α] [Op α] [Ordered α] : Prop where
  inc_ord {x y : α} : x ≼ y → x ≼ₒ y

/-- An algebra is affine when extension inclusion implies its resource order. -/
@[reducible] def ORA.Affine (α : Type _) [OFE α] [Op α] [Ordered α] : Prop := IncOrd α

/-- The order is contained in the extension inclusion: every ordered pair has a frame. -/
class OrdInc (α : Type _) [OFE α] [Op α] [Ordered α] : Prop where
  ord_inc {x y : α} : x ≼ₒ y → x ≼ y
  ordN_incN {n} {x y : α} : x ≼ₒ{n} y → x ≼{n} y

/-- The order is the extension inclusion. -/
class IsInc (α : Type _) [OFE α] [Op α] [Ordered α] : Prop extends IncOrd α, OrdInc α

section
variable {α : Type _} [OFE α] [Op α] [Ordered α]

theorem IncOrd.increasing [IncOrd α] (x : α) : Increasing x :=
  ⟨fun _ => IncOrd.inc_ord ⟨x, Op.comm⟩⟩

theorem IncOrd.of_increasing (h : ∀ x : α, Increasing x) : IncOrd α where
  inc_ord {x _} := fun ⟨z, e⟩ => by subst e; rw [Op.comm]; exact (h z).increasing x

instance instIncreasingOfIncOrd [IncOrd α] (x : α) : Increasing x := IncOrd.increasing x

theorem inc_iff_ord [IncOrd α] [OrdInc α] {x y : α} : x ≼ y ↔ x ≼ₒ y :=
  ⟨IncOrd.inc_ord, OrdInc.ord_inc⟩

theorem IncOrd.incN_ordN [IncOrd α] {n} {x y : α} : x ≼{n} y → x ≼ₒ{n} y
  | ⟨z, hz⟩ => Ordered.ordN_ne .rfl hz.symm (Ordered.ordN_of_ord n (IncOrd.inc_ord ⟨z, rfl⟩))

theorem incN_iff_ordN [IncOrd α] [OrdInc α] {n} {x y : α} : x ≼{n} y ↔ x ≼ₒ{n} y :=
  ⟨IncOrd.incN_ordN, OrdInc.ordN_incN⟩

end

/-! ## Order-free theory -/

namespace ORA
variable [OFE α] [Op α]

export Op (op optionalOp op_ne assoc comm)
export PCore (pcore pcore_ne pcore_idem core)
export Validity (Valid ValidN validN_ne valid_iff_validN validN_succ)
export IsTotal (total)

/-! ## Op -/
theorem comm' {x y : α} : x • y = y • x := comm

theorem assoc' {x y z : α} : x • (y • z) = (x • y) • z := assoc

theorem op_right_dist (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.op_r {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z := op_right_dist _

theorem op_commN {x y : α} : x • y ≡{n}≡ y • x := Dist.of_eq comm

theorem op_assocN {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z := Dist.of_eq assoc

theorem op_left_dist {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.op_l {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z := op_left_dist _

theorem _root_.Iris.OFE.Dist.op {x x' y y' : α}
    (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') : x • y ≡{n}≡ x' • y' := ex.op_l.trans ey.op_r

theorem _root_.Iris.OFE.Dist.opM {x₁ x₂ : α} {y₁ y₂ : Option α}
    (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ •? y₁ ≡{n}≡ x₂ •? y₂ :=
  match y₁, y₂, H2 with
  | none, none, _ => H1
  | some _, some _, H2 => H1.op H2

theorem opM_left_dist {n} {x y : α} (z : Option α) (e : x ≡{n}≡ y) : x •? z ≡{n}≡ y •? z :=
  e.opM Dist.rfl
theorem opM_right_dist {n} (x : α) {y z : Option α} (e : y ≡{n}≡ z) : x •? y ≡{n}≡ x •? z :=
  Dist.rfl.opM e

theorem op_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz = x • (y •? mz) := by
  unfold optionalOp; cases mz <;> simp [assoc]

theorem op_opM_assoc_dist (x y : α) (mz : Option α) : (x • y) •? mz ≡{n}≡ x • (y •? mz) := by
  unfold optionalOp; cases mz <;> simp [op_assocN, Dist.symm]

theorem incN_ne {n} {x x' y y' : α} (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') :
    x ≼{n} y → x' ≼{n} y'
  | ⟨z, hz⟩ => ⟨z, ey.symm.trans (hz.trans ex.op_l)⟩

theorem incN_of_incN_of_dist (h : (a : α) ≼{n} b) (e : b ≡{n}≡ c) : a ≼{n} c := incN_ne .rfl e h

instance {n : Nat} : Trans (IncludedN (α := α) n) (Dist n) (IncludedN n) where
  trans := incN_of_incN_of_dist

theorem incN_of_dist_of_incN (e : (a : α) ≡{n}≡ b) (h : b ≼{n} c) : a ≼{n} c :=
  incN_ne e.symm .rfl h

instance {n : Nat} : Trans (Dist (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_of_dist_of_incN

theorem incN_of_inc (n) {x y : α} : x ≼ y → x ≼{n} y
  | ⟨z, hz⟩ => ⟨z, hz.dist⟩

theorem incN_iff_left (e : (a : α) ≡{n}≡ b) : a ≼{n} c ↔ b ≼{n} c :=
  ⟨incN_ne e .rfl, incN_ne e.symm .rfl⟩
theorem _root_.Iris.OFE.Dist.incN_l : (a : α) ≡{n}≡ b → (a ≼{n} c ↔ b ≼{n} c) := incN_iff_left

theorem incN_iff_right (e : (b : α) ≡{n}≡ c) : a ≼{n} b ↔ a ≼{n} c :=
  ⟨incN_ne .rfl e, incN_ne .rfl e.symm⟩
theorem _root_.Iris.OFE.Dist.incN_r : (b : α) ≡{n}≡ c → (a ≼{n} b ↔ a ≼{n} c) := incN_iff_right

theorem incN_dist_iff (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') :
    a ≼{n} b ↔ a' ≼{n} b' :=
  ⟨incN_ne ea eb, incN_ne ea.symm eb.symm⟩
theorem _root_.Iris.OFE.Dist.incN :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼{n} b ↔ a' ≼{n} b') :=
  incN_dist_iff

theorem inc_trans {x y z : α} : x ≼ y → y ≼ z → x ≼ z
  | ⟨w, hw⟩, ⟨t, ht⟩ => ⟨w • t, ht.trans (hw ▸ assoc.symm)⟩

instance : Trans (Included (α := α)) Included Included where
  trans := inc_trans

theorem incN_trans {x y z : α} : x ≼{n} y → y ≼{n} z → x ≼{n} z
  | ⟨w, hw⟩, ⟨t, ht⟩ => ⟨w • t, ht.trans (hw.op_l.trans op_assocN.symm)⟩

instance : Trans (IncludedN (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_trans

theorem incN_of_incN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼{n} y → x ≼{n'} y
  | ⟨z, hz⟩ => ⟨z, Dist.le hz l1⟩
theorem inc0_of_incN {n} {x y : α} : x ≼{n} y → x ≼{0} y := incN_of_incN_le (Nat.zero_le n)

theorem incN_of_incN_succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y :=
  incN_of_incN_le (Nat.le_succ n)

theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

theorem inc_op_left (x y : α) : x ≼ x • y := ⟨y, rfl⟩

theorem inc_op_right (x y : α) : y ≼ x • y := ⟨x, comm⟩

theorem incN_op_right (n) (x y : α) : y ≼{n} x • y := ⟨x, op_commN⟩

theorem op_mono_right {x y} (z : α) : x ≼ y → z • x ≼ z • y
  | ⟨w, hw⟩ => ⟨w, (congrArg (z • ·) hw).trans assoc⟩

theorem op_monoN_right {n x y} (z : α) : x ≼{n} y → z • x ≼{n} z • y
  | ⟨w, hw⟩ => ⟨w, hw.op_r.trans op_assocN⟩

theorem op_monoN_left {n x y} (z : α) (h : x ≼{n} y) : x • z ≼{n} y • z :=
  (op_commN.incN op_commN).1 (op_monoN_right z h)

theorem op_mono_left {x y} (z : α) (h : x ≼ y) : x • z ≼ y • z := by
  rw [comm' (x := x) (y := z), comm' (x := y) (y := z)]; exact op_mono_right z h

theorem op_monoN {n} {x x' y y' : α} (hx : x ≼{n} x') (hy : y ≼{n} y') :
    x • y ≼{n} x' • y' :=
  incN_trans (op_monoN_left _ hx) (op_monoN_right _ hy)

theorem op_mono {x x' y y' : α} (hx : x ≼ x') (hy : y ≼ y') :
    x • y ≼ x' • y' :=
  inc_trans (op_mono_left _ hx) (op_mono_right _ hy)

/-- Equip a resource operation with its extension-inclusion order. -/
@[reducible] def extOrdered : Ordered α where
  OrderN := IncludedN
  Order := Included
  ordN_ne := incN_ne
  ordN_succ := incN_of_incN_succ
  ordN_trans := incN_trans
  ord_trans := inc_trans
  ordN_of_ord n h := incN_of_inc n h

section pcore
variable [PCore α]

instance : NonExpansive (pcore (α := α)) where
  ne n x {y} e := by
    suffices ∀ ox oy, pcore x = ox → pcore y = oy → pcore x ≡{n}≡ pcore y from
      this (pcore x) (pcore y) rfl rfl
    intro ox oy ex ey
    match ox, oy with
    | .some a, .some b =>
      let ⟨w, hw, ew⟩ := pcore_ne e ex
      calc
        pcore x ≡{n}≡ some a := .of_eq ex
        _ ≡{n}≡ some w := ew
        _ ≡{n}≡ pcore y := .of_eq hw.symm
    | .some a, .none =>
      let ⟨w, hw, ew⟩ := pcore_ne e ex
      cases hw.symm ▸ ey
    | .none, .some b =>
      let ⟨w, hw, ew⟩ := pcore_ne e.symm ey
      cases hw.symm ▸ ex
    | .none, .none => rw [ex, ey]

section total
variable [IsTotal α]

omit [Op α] in
theorem pcore_eq_core (x : α) : pcore x = some (core x) := by
  unfold core
  have ⟨cx, hcx⟩ := IsTotal.total x
  simp [hcx]

end total
end pcore

end ORA

/-! ## Ordered resource algebras -/

/-- An ordered resource algebra: composition, core and validity together with the laws relating
them, and a step-indexed order that they respect. The order is neither required to be reflexive
(`OrderRefl`) nor to contain the extension inclusion (`IncOrd`). -/
class ORA (α : Type _) extends OFE α, Op α, PCore α, Validity α, Ordered α where
  validN_op_left {n} {x y : α} : ✓{n} (x • y) → ✓{n} x
  pcore_op_left {x cx : α} : pcore x = some cx → cx • x = x
  /-- Split a valid resource into factors matching an approximate decomposition. -/
  extend {n} {x y₁ y₂ : α} : ✓{n} x → x ≡{n}≡ y₁ • y₂ →
    Σ' z₁ z₂ : α, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂
  op_monoN_left_ord {n} {x y : α} (z : α) : x ≼ₒ{n} y → x • z ≼ₒ{n} y • z
  op_mono_left_ord {x y : α} (z : α) : x ≼ₒ y → x • z ≼ₒ y • z
  validN_of_ordN {n} {x y : α} : x ≼ₒ{n} y → ✓{n} y → ✓{n} x
  pcore_monoN_ord {n} {x y cx : α} : x ≼ₒ{n} y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≼ₒ{n} cy
  pcore_mono_ord {x y cx : α} : x ≼ₒ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ₒ cy
  pcore_order_op {x cx : α} : pcore x = some cx → ∀ y, ∃ cxy, pcore (x • y) = some cxy ∧ cx ≼ₒ cxy
  pcore_increasing {x cx : α} : pcore x = some cx → Increasing cx
  increasing_closed {n} {x y : α} : Increasing x → x ≼ₒ*{n} y → Increasing y
  ordN_extend {n} {x y : α} : ✓{n} y → x ≼ₒ{n} y → ∃ z, z ≼ₒ{n.succ} y ∧ z ≡{n}≡ x

namespace ORA
variable [ORA α]

/-- A resource equal to its own partial core. -/
class CoreId (x : α) where
  core_id : pcore x = some x
export CoreId (core_id)

/-- A resource that cannot be composed validly with any further resource. -/
class Exclusive (x : α) where
  exclusive0_l y : ¬✓{0} x • y
export Exclusive (exclusive0_l)

/-- A resource cancellable from valid compositions at each step index. -/
class Cancelable (x : α) where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z
export Cancelable (cancelableN)

/-- A valid resource that cannot absorb a right factor at index zero. -/
class IdFree (x : α) where
  id_free0_r y : ✓{0} x → ¬x • y ≡{0}≡ x
export IdFree (id_free0_r)

theorem pcore_l {x cx : α} (e : pcore x = some cx) : cx • x = x := pcore_op_left e

theorem pcore_idemp {x cx : α} (e : pcore x = some cx) : pcore cx = some cx := pcore_idem e

/-- A dependent-pair form of the resource decomposition operation. -/
def extend' {n} {x y₁ y₂ : α} (v : ✓{n} x) (e : x ≡{n}≡ y₁ • y₂) :
    Σ' z₁ z₂, x = (z₁ • z₂ : α) ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨z₁, z₂, hx, hz, hw⟩ := extend (y₁ := y₁) (y₂ := y₂) v e
  ⟨z₁, z₂, hx, hz, hw⟩

theorem validN_op_l {n} {x y : α} : ✓{n} (x • y) → ✓{n} x := validN_op_left

theorem valid_validN {x : α} : ✓ x ↔ ∀ n, ✓{n} x := valid_iff_validN

theorem op_ne' {x : α} : NonExpansive (x • ·) := op_ne

theorem pcore_ne' {n} {x y : α} {cx} (h : x ≡{n}≡ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := pcore_ne h e

theorem validN_ne' {n} {x y : α} (h : x ≡{n}≡ y) : ✓{n} x → ✓{n} y := validN_ne h

theorem opM_ne_right {n} {x : α} {y₁ y₂ : Option α} (h : y₁ ≡{n}≡ y₂) : x •? y₁ ≡{n}≡ x •? y₂ :=
  match y₁, y₂, h with
  | none, none, _ => .rfl
  | some _, some _, h => op_ne.ne h

instance : NonExpansive₂ (optionalOp (α := α)) where
  ne _ x₁ _ e₁ y₁ y₂ e₂ := match y₁, y₂, e₂ with
    | none, none, _ => e₁
    | some _, some y₂, e₂ =>
      ((op_ne (x := x₁)).ne e₂).trans (Dist.of_eq comm |>.trans <|
        ((op_ne (x := y₂)).ne e₁).trans (Dist.of_eq comm))

/-! ## Validity -/

theorem _root_.Iris.Validity.Valid.validN : ✓ (x : α) → ✓{n} x := (valid_iff_validN.1 · _)
protected theorem Valid.validN : ✓ (x : α) → ✓{n} x := Iris.Validity.Valid.validN

theorem valid_mapN {x y : α} (f : ∀ n, ✓{n} x → ✓{n} y) (v : ✓ x) : ✓ y :=
  valid_iff_validN.mpr fun n => f n v.validN

theorem validN_dist_iff {x y : α} (e : x ≡{n}≡ y) : ✓{n} x ↔ ✓{n} y :=
  ⟨validN_ne e, validN_ne e.symm⟩
theorem _root_.Iris.OFE.Dist.validN : (x : α) ≡{n}≡ y → (✓{n} x ↔ ✓{n} y) := validN_dist_iff

theorem validN_of_le {n n'} {x : α} (le : n' ≤ n) : ✓{n} x → ✓{n'} x :=
  le.recOn id fun _ ih vs => ih (validN_succ vs)

theorem validN_of_lt {n n'} {x : α} (lt : n' < n) : ✓{n} x → ✓{n'} x :=
  validN_of_le (Nat.le_of_lt lt)

theorem valid0_of_validN {n} {x : α} : ✓{n} x → ✓{0} x := validN_of_le (Nat.zero_le n)

theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (comm' (x := x) (y := y) ▸ v)

theorem valid_op_right (x y : α) : ✓ (x • y) → ✓ y := valid_mapN fun _ => validN_op_right

theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_op_right y x (comm' (x := x) (y := y) ▸ v)

theorem validN_opM {x : α} {my : Option α} : ✓{n} (x •? my) → ✓{n} x := match my with
  | none => id | some _ => validN_op_left

theorem valid_opM {x : α} {my : Option α} : ✓ (x •? my) → ✓ x := match my with
  | none => id | some _ => valid_op_left

theorem validN_op_opM_left {mz : Option α} : ✓{n} (x • y : α) •? mz → ✓{n} x •? mz := match mz with
  | .none => validN_op_left
  | .some z => fun h =>
    have := calc
      (x • y) • z ≡{n}≡ x • (y • z) := op_assocN.symm
      _ ≡{n}≡ x • (z • y) := op_right_dist x op_commN
      _ ≡{n}≡ (x • z) • y := op_assocN
    validN_op_left ((Dist.validN this).mp h)

theorem validN_op_opM_right {mz : Option α} (h : ✓{n} (x • y : α) •? mz) : ✓{n} y •? mz :=
  validN_op_opM_left (validN_ne (opM_left_dist mz op_commN) h)

/-! ## Core -/
instance cmra_op_ne2 : NonExpansive₂ (op (α := α)) where
  ne _ _ _ e₁ _ _ e₂ := e₁.op e₂

theorem pcore_op_left' {x : α} {cx} (e : pcore x = some cx) : cx • x = x := pcore_l e

theorem pcore_op_right {x : α} {cx} (e : pcore x = some cx) : x • cx = x := comm'.trans (pcore_l e)

theorem pcore_op_right' {x : α} {cx} (e : pcore x = some cx) : x • cx = x := pcore_op_right e

theorem pcore_idem' {x : α} {cx} (e : pcore x = some cx) : pcore cx = some cx := pcore_idemp e

theorem pcore_op_self {x : α} {cx} (e : pcore x = some cx) : cx • cx = cx :=
  pcore_op_right' (pcore_idem e)

theorem pcore_op_self' {x : α} {cx} (e : pcore x = some cx) : cx • cx = cx := pcore_op_self e

theorem pcore_validN {n} {x : α} {cx} (e : pcore x = some cx) (v : ✓{n} x) : ✓{n} cx :=
  validN_op_right ((pcore_op_right e).symm ▸ v)

theorem pcore_valid {x : α} {cx} (e : pcore x = some cx) : ✓ x → ✓ cx :=
  valid_mapN fun _ => pcore_validN e

theorem op_self (x : α) [CoreId x] : x • x = x := pcore_op_self' CoreId.core_id

theorem CoreId.of_pcore_eq_some {x y : α} (e : pcore x = some y) : CoreId y where
  core_id := pcore_idem e

/-! ## Exclusive elements -/
theorem not_valid_exclN_op_left {n} {x : α} [Exclusive x] {y} : ¬✓{n} (x • y) :=
  n.recOn (Exclusive.exclusive0_l _) fun _ ih => ih ∘ validN_succ

theorem not_valid_exclN_op_right {n} {x : α} [Exclusive x] {y} : ¬✓{n} (y • x) :=
  fun v => not_valid_exclN_op_left (comm' (x := y) (y := x) ▸ v)

theorem not_valid_excl_op_left {x : α} [Exclusive x] {y} : ¬✓ (x • y) :=
  fun v => Exclusive.exclusive0_l _ v.validN

theorem not_excl_op_right {x : α} [Exclusive x] {y} : ¬✓ (y • x) :=
  fun v => not_valid_excl_op_left (comm' (x := y) (y := x) ▸ v)

theorem none_of_excl_valid_op {n} {x : α} [Exclusive x] {my} : ✓{n} (x •? my) → my = none := by
  cases my <;> simp [optionalOp, not_valid_exclN_op_left]

/-! ## Total cores -/

section total
variable [IsTotal α]

theorem op_core (x : α) : x • core x = x := pcore_op_right (pcore_eq_core x)

theorem core_op (x : α) : core x • x = x := comm'.trans (op_core x)

theorem op_core_dist (x : α) : x • core x ≡{n}≡ x := Dist.of_eq (op_core x)
theorem core_op_dist (x : α) : core x • x ≡{n}≡ x := Dist.of_eq (core_op x)

theorem core_op_core {x : α} : core x • core x = core x := pcore_op_self (pcore_eq_core x)

theorem validN_core {n} {x : α} (v : ✓{n} x) : ✓{n} core x := pcore_validN (pcore_eq_core x) v

theorem valid_core {x : α} (v : ✓ x) : ✓ core x := pcore_valid (pcore_eq_core x) v

instance (y : α) : CoreId (core y) := CoreId.of_pcore_eq_some (pcore_eq_core _)

theorem core_ne : NonExpansive (core : α → α) where
  ne n x₁ x₂ H := by
    change some (core x₁) ≡{n}≡ some (core x₂)
    rw [← pcore_eq_core, ← pcore_eq_core]
    exact NonExpansive.ne H

theorem _root_.Iris.OFE.Dist.core :
  ∀ {n} {x₁ x₂ : α}, x₁ ≡{n}≡ x₂ → core x₁ ≡{n}≡ core x₂ := @core_ne.ne

theorem core_eqv_self (x : α) [CoreId x] : core (x : α) = x :=
  Option.some.inj ((pcore_eq_core x).symm.trans CoreId.core_id)

theorem coreId_iff_core_eqv_self : CoreId (x : α) ↔ core x = x :=
  ⟨fun _ => core_eqv_self x, fun e => { core_id := (pcore_eq_core x).trans (congrArg some e) }⟩

theorem core_idem (x : α) : core (core x) = core x := core_eqv_self _

instance instOrderReflOfIsTotal : OrderRefl α where
  ord_refl x :=
    (congrArg (x ≼ₒ ·) (core_op x)).mp ((pcore_increasing (pcore_eq_core x)).increasing x)

end total

/-! ## Discrete elements -/
theorem discrete_op {x y : α} (Hv : ✓{0} x • y) [Hx : DiscreteE x] [Hy : DiscreteE y] :
    DiscreteE (x • y) where
  discrete h := by
    obtain ⟨_w, _t, wt, wx, ty⟩ := extend ((Dist.validN h).mp Hv) h.symm
    rw [Hx.discrete wx.symm, Hy.discrete ty.symm, wt]

end ORA

namespace ORA
export Ordered (OrderN Order ordN_ne ordN_succ ordN_trans ord_trans ordN_of_ord)
export OrderRefl (ord_refl)
end ORA

/-! ## The extension inclusion -/

namespace ORA

variable [ORA α]

theorem valid_of_inc {x y : α} : x ≼ y → ✓ y → ✓ x
  | ⟨_, hz⟩, v => valid_op_left (hz ▸ v)

theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)

theorem validN_of_inc {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz.dist v)

theorem pcore_inc_self {x : α} {cx} (e : pcore x = some cx) : cx ≼ x := ⟨x, (pcore_op_left e).symm⟩

theorem op_core_right_of_inc {x y : α} [CoreId x] : x ≼ y → x • y = y
  | ⟨z, hz⟩ => hz ▸ assoc'.trans (congrArg (· • z) (op_self x))

theorem op_core_left_of_inc {x y : α} [CoreId x] (le : x ≼ y) : y • x = y :=
  comm'.trans (op_core_right_of_inc le)

theorem included_dist_l {n} {x1 x2 x1' : α} :
    x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2
  | ⟨y, hy⟩, e => ⟨x1' • y, inc_op_left x1' y, e.op_l.trans hy.symm.dist⟩

theorem not_valid_of_exclN_inc {n} {x : α} [Exclusive x] {y} : x ≼{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

theorem not_valid_of_excl_inc {x : α} [Exclusive x] {y} : x ≼ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l _ <| hz ▸ v.validN

theorem incN_extend {n} {x y : α} (v : ✓{n} y) :
    x ≼{n} y → ∃ z, z ≼{n.succ} y ∧ z ≡{n}≡ x
  | ⟨_, hw⟩ =>
    let ⟨z₁, z₂, hy, hz₁, _⟩ := extend v hw
    ⟨z₁, ⟨z₂, hy.dist⟩, hz₁⟩

theorem incN_map {β : Type _} [ORA β] (f : α → β) [NonExpansive f]
    (hop : ∀ x y, f (x • y) = f x • f y) {n} {x y : α} : x ≼{n} y → f x ≼{n} f y
  | ⟨z, hz⟩ => ⟨f z, (NonExpansive.ne hz).trans (hop x z).dist⟩

theorem inc_map {β : Type _} [ORA β] (f : α → β)
    (hop : ∀ x y, f (x • y) = f x • f y) {x y : α} : x ≼ y → f x ≼ f y
  | ⟨z, hz⟩ => ⟨f z, (congrArg f hz).trans (hop x z)⟩

section total
variable [IsTotal α]

theorem inc_refl (x : α) : x ≼ x := ⟨core x, (op_core x).symm⟩

theorem incN_refl (x : α) : x ≼{n} x := incN_of_inc _ (inc_refl _)

theorem incN_of_dist {n} {x y : α} (h : x ≡{n}≡ y) : x ≼{n} y := incN_ne .rfl h (incN_refl x)
theorem _root_.Iris.OFE.Dist.to_incN {n} {x y : α} : x ≡{n}≡ y → x ≼{n} y := incN_of_dist

theorem core_inc_self {x : α} : core x ≼ x := ⟨x, (core_op x).symm⟩

end total

section discrete

theorem inc_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼ y ↔ x ≼{n} y :=
  ⟨incN_of_inc _, fun ⟨z, hz⟩ => ⟨z, discrete hz⟩⟩

theorem inc_0_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼{0} y ↔ x ≼{n} y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, (discrete hz).dist⟩, inc0_of_incN⟩

theorem inc_of_inc0 [OFE.Discrete α] {x y : α} : x ≼{0} y → x ≼ y := (inc_iff_incN 0).mpr

theorem discrete_inc_l {x y : α} [HD : DiscreteE x] (Hv : ✓{0} y) (Hle : x ≼{0} y) :
    x ≼ y :=
  have ⟨_, hz⟩ := Hle
  let ⟨_, t, wt, wx, _⟩ := extend Hv hz
  ⟨t, wt.trans (congrArg (· • t) (HD.discrete wx.symm).symm)⟩

theorem discrete_inc_r {x y : α} [HD : DiscreteE y] : x ≼{0} y → x ≼ y
  | ⟨z, hz⟩ => ⟨z, HD.discrete hz⟩

end discrete

end ORA

/-- A classical resource algebra: composition, core and validity together with the laws
relating them, and the monotonicity of the partial core along frames. It is not itself an
ordered resource algebra; `ORA.ofCMRAData` makes one of it, taking the order to be the extension
inclusion. -/
class CMRAData (α : Type _) [OFE α] extends Op α, PCore α, Validity α where
  validN_op_left {n} {x y : α} : ✓{n} (x • y) → ✓{n} x
  pcore_op_left {x cx : α} : pcore x = some cx → cx • x = x
  /-- Decompose a valid classical resource along an approximate composition. -/
  extend {n} {x y₁ y₂ : α} : ✓{n} x → x ≡{n}≡ y₁ • y₂ →
    Σ' z₁ z₂ : α, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂
  pcore_op_mono {x cx : α} : pcore x = some cx → ∀ y, ∃ cy : α, pcore (x • y) = some (cx • cy)

namespace CMRAData
open ORA

/-- The frame law follows from monotonicity of the partial core along the extension inclusion,
the form of the law in Iris-Rocq (`cmra_pcore_mono`). -/
theorem pcore_op_mono_of_pcore_mono [OFE α] [Op α] [PCore α]
    (h : ∀ {x y cx : α}, x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy)
    {x cx : α} (e : pcore x = some cx) (y) : ∃ cy : α, pcore (x • y) = some (cx • cy) :=
  let ⟨_, hcy, z, hz⟩ := h (inc_op_left _ y) e
  ⟨z, hcy.trans (congrArg some hz)⟩

theorem pcore_op_mono_of_core_mono [OFE α] [Op α] [PCore α] [IsTotal α]
    (h : ∀ x y : α, x ≼ y → core x ≼ core y)
    {x cx : α} (e : pcore x = some cx) (y) : ∃ cy : α, pcore (x • y) = some (cx • cy) :=
  pcore_op_mono_of_pcore_mono (fun {x y cx} hxy e =>
    have hcx : cx = core x := Option.some.inj (e.symm.trans (pcore_eq_core x))
    ⟨core y, pcore_eq_core y, hcx ▸ h x y hxy⟩) e y

variable [OFE α] [CMRAData α]

theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)

theorem incN_extend {n} {x y : α} (v : ✓{n} y) :
    x ≼{n} y → ∃ z, z ≼{n.succ} y ∧ z ≡{n}≡ x
  | ⟨_, hw⟩ =>
    let ⟨z₁, z₂, hy, hz₁, _⟩ := extend v hw
    ⟨z₁, ⟨z₂, hy.dist⟩, hz₁⟩

theorem pcore_mono {x y cx : α} :
    x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨_, hw⟩, e =>
    have ⟨z, hz⟩ := pcore_op_mono e _
    let ⟨t, ht, et⟩ := OFE.equiv_some ((congrArg pcore hw).trans hz)
    ⟨t, ht, z, et⟩

theorem pcore_mono' {x y : α} {cx} (le : x ≼ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ cy :=
  pcore_mono le e

theorem pcore_monoN' {n} {x y : α} {cx} :
    x ≼{n} y → pcore x ≡{n}≡ some cx → ∃ cy, pcore y = some cy ∧ cx ≼{n} cy
  | ⟨z, hz⟩, e =>
    let ⟨_, hw, ew⟩ := OFE.dist_some e
    let ⟨t, ht⟩ := pcore_op_mono hw z
    let ⟨r, hr, er⟩ := PCore.pcore_ne hz.symm ht
    ⟨r, hr, incN_ne ew.symm er (incN_op_left n _ t)⟩

theorem pcore_monoN {n} {x y : α} {cx} (h : x ≼{n} y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼{n} cy :=
  pcore_monoN' h (Dist.of_eq e)

section total
variable [IsTotal α]

theorem core_incN_core {n} {x y : α} (le : x ≼{n} y) : core x ≼{n} core y :=
  let ⟨_, hcy, icy⟩ := pcore_monoN' le (Dist.of_eq (pcore_eq_core x))
  Option.some.inj ((pcore_eq_core y).symm.trans hcy) ▸ icy

theorem core_op_mono (x y : α) : core x ≼ core (x • y) := by
  have ⟨cy, hcy⟩ := pcore_op_mono (pcore_eq_core x) y
  simp only [pcore_eq_core, Option.some.injEq] at hcy
  exact ⟨_, hcy⟩

theorem core_mono {x y : α} (Hinc : x ≼ y) : core x ≼ core y := by
  have ⟨z, hz⟩ := Hinc
  rw [hz]; exact core_op_mono x z

theorem inc_refl (x : α) : x ≼ x := ⟨core x, (Op.comm.trans (pcore_op_left (pcore_eq_core x))).symm⟩

end total

section extOrder
attribute [local instance] extOrdered

theorem increasing (x : α) : Increasing x where
  increasing y := inc_op_right x y

instance instOrderRefl [IsTotal α] : OrderRefl α where
  ord_refl := inc_refl

/-- Give classical resource algebra data its extension-inclusion order. -/
@[reducible] def toORA : ORA α where
  toOrdered := extOrdered
  validN_op_left := validN_op_left
  pcore_op_left := pcore_op_left
  extend := extend
  op_monoN_left_ord := op_monoN_left
  op_mono_left_ord := op_mono_left
  validN_of_ordN := validN_of_incN
  pcore_monoN_ord := pcore_monoN
  pcore_mono_ord := pcore_mono
  pcore_order_op {_ cx} e y :=
    let ⟨cy, hcy⟩ := pcore_op_mono e y
    ⟨cx • cy, hcy, inc_op_left cx cy⟩
  pcore_increasing _ := increasing _
  increasing_closed _ _ := increasing _
  ordN_extend := incN_extend

theorem isInc : @IsInc α _ _ (toORA (α := α)).toOrdered :=
  { inc_ord := id, ord_inc := id, ordN_incN := id }

end extOrder

end CMRAData

/-- An ordered resource algebra whose order is exactly extension inclusion. -/
class CMRA (α : Type _) extends ORA α, IsInc α

instance (priority := low) CMRA.ofIsInc [ORA α] [IsInc α] : CMRA α := {}

/-- Construct a classical ordered resource algebra from its operation and core. -/
@[reducible] def ORA.ofCMRAData [OFE α] (d : CMRAData α) : CMRA α :=
  { toORA := @CMRAData.toORA α _ d, toIsInc := @CMRAData.isInc α _ d }

namespace CMRA
open ORA
variable [CMRA α]

theorem ord_of_ord0 [OFE.Discrete α] {x y : α} (h : x ≼ₒ{0} y) : x ≼ₒ y :=
  inc_iff_ord.mp (inc_of_inc0 (incN_iff_ordN.mpr h))

end CMRA

section
open ORA
variable [OFE α] [Op α]

theorem Included.incN {n} {x y : α} : x ≼ y → x ≼{n} y := incN_of_inc _
theorem Included.trans : (x : α) ≼ y → y ≼ z → x ≼ z := inc_trans
theorem IncludedN.trans : (x : α) ≼{n} y → y ≼{n} z → x ≼{n} z := incN_trans
theorem IncludedN.le {n n'} {x y : α} : n' ≤ n → x ≼{n} y → x ≼{n'} y := incN_of_incN_le
theorem IncludedN.succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y := incN_of_incN_succ

end

section
open ORA
variable [ORA α]

theorem Included.validN {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x := validN_of_inc
theorem IncludedN.validN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x := validN_of_incN

variable [IsTotal α]

@[refl] theorem Included.rfl {x : α} : x ≼ x := inc_refl x
@[refl] theorem IncludedN.rfl {x : α} : x ≼{n} x := incN_refl x

end

/-! ## Discrete and affine algebras -/

namespace ORA
variable [ORA α]

/-- An algebra with discrete equivalence, validity, and resource order. -/
class Discrete (α : Type _) [ORA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x
  discrete_ord {x y : α} : x ≼ₒ{0} y → x ≼ₒ y := by
    first | exact CMRA.ord_of_ord0 | exact fun ⟨z, hz⟩ => ⟨z, hz⟩
export Discrete (discrete_valid discrete_ord)

end ORA

/-! ## Unital algebras -/

/-- A unital ordered resource algebra: an ordered resource algebra with a unit, whose order is
reflexive. -/
class UORA (α : Type _) extends ORA α, OrderRefl α where
  /-- The unit resource. -/
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x = x
  pcore_unit : pcore unit = some unit

/-- The unit of a classical unital resource algebra; the input of `UORA.ofUCMRAData`. -/
class UCMRAData (α : Type _) [CMRA α] where
  /-- The proposed unit of a classical resource algebra. -/
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x = x
  pcore_unit : ORA.pcore unit = some unit

/-- A classical resource algebra equipped with a unit. -/
class UCMRA (α : Type _) extends CMRA α, UORA α

instance (priority := low) UCMRA.ofIsInc [UORA α] [IsInc α] : UCMRA α := {}

/-- Add a specified unit to a classical resource algebra. -/
@[reducible] def UORA.ofUCMRAData [CMRA α] (d : UCMRAData α) : UCMRA α where
  unit := d.unit
  unit_valid := d.unit_valid
  unit_left_id := d.unit_left_id
  pcore_unit := d.pcore_unit
  ord_refl _ := IncOrd.inc_ord ⟨d.unit, (Op.comm.trans d.unit_left_id).symm⟩

/-- The laws asserting that a specified resource is a valid unit with itself as core. -/
class IsUnit [ORA α] (ε : α) : Prop where
  unit_valid : ✓ ε
  unit_left_id : ε • x = x
  pcore_unit : ORA.pcore ε = some ε

instance [UORA α] : IsUnit (UORA.unit : α) where
  unit_valid := UORA.unit_valid
  unit_left_id := UORA.unit_left_id
  pcore_unit := UORA.pcore_unit

namespace ORA

export UORA (unit unit_valid unit_left_id pcore_unit)

/-! ## Order -/

section orderN
variable [OFE α] [Ordered α]

theorem ordN_of_ordN_of_dist (h : (a : α) ≼ₒ{n} b) (e : b ≡{n}≡ c) : a ≼ₒ{n} c := ordN_ne .rfl e h

instance instTransOrderNDist {n : Nat} : Trans (OrderN (α := α) n) (Dist n) (OrderN n) where
  trans := ordN_of_ordN_of_dist

theorem ordN_of_dist_of_ordN (e : (a : α) ≡{n}≡ b) (h : b ≼ₒ{n} c) : a ≼ₒ{n} c :=
  ordN_ne e.symm .rfl h

instance {n : Nat} : Trans (Dist (α := α) n) (OrderN n) (OrderN n) where
  trans := ordN_of_dist_of_ordN

theorem _root_.Iris.Ordered.Order.ordN {n} {x y : α} : x ≼ₒ y → x ≼ₒ{n} y := ordN_of_ord _

theorem ordN_iff_left (e : (a : α) ≡{n}≡ b) : a ≼ₒ{n} c ↔ b ≼ₒ{n} c :=
  ⟨ordN_ne e .rfl, ordN_ne e.symm .rfl⟩
theorem _root_.Iris.OFE.Dist.ordN_l : (a : α) ≡{n}≡ b → (a ≼ₒ{n} c ↔ b ≼ₒ{n} c) := ordN_iff_left

theorem ordN_iff_right (e : (b : α) ≡{n}≡ c) : a ≼ₒ{n} b ↔ a ≼ₒ{n} c :=
  ⟨ordN_ne .rfl e, ordN_ne .rfl e.symm⟩
theorem _root_.Iris.OFE.Dist.ordN_r : (b : α) ≡{n}≡ c → (a ≼ₒ{n} b ↔ a ≼ₒ{n} c) := ordN_iff_right

theorem ordN_dist_iff (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') : a ≼ₒ{n} b ↔ a' ≼ₒ{n} b' :=
  ⟨ordN_ne ea eb, ordN_ne ea.symm eb.symm⟩
theorem _root_.Iris.OFE.Dist.ordN :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼ₒ{n} b ↔ a' ≼ₒ{n} b') := ordN_dist_iff

theorem _root_.Iris.Ordered.Order.trans : (x : α) ≼ₒ y → y ≼ₒ z → x ≼ₒ z := ord_trans

instance instTransOrder : Trans (Order (α := α)) Order Order where
  trans := ord_trans

theorem _root_.Iris.Ordered.OrderN.trans : (x : α) ≼ₒ{n} y → y ≼ₒ{n} z → x ≼ₒ{n} z := ordN_trans

instance instTransOrderN : Trans (OrderN (α := α) n) (OrderN n) (OrderN n) where
  trans := ordN_trans

theorem ordN_of_ordN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼ₒ{n} y → x ≼ₒ{n'} y :=
  l1.recOn id fun _ ih h => ih (ordN_succ h)
theorem ord0_of_ordN {n} {x y : α} : x ≼ₒ{n} y → x ≼ₒ{0} y := ordN_of_ordN_le (Nat.zero_le n)
theorem _root_.Iris.Ordered.OrderN.le {n n'} {x y : α} :
    n' ≤ n → x ≼ₒ{n} y → x ≼ₒ{n'} y := ordN_of_ordN_le

theorem ordN_of_ordN_succ {n} {x y : α} : x ≼ₒ{n.succ} y → x ≼ₒ{n} y := ordN_succ
theorem _root_.Iris.Ordered.OrderN.succ {n} {x y : α} : x ≼ₒ{n.succ} y → x ≼ₒ{n} y := ordN_succ

section ordRefl
variable [OrderRefl α]

theorem ordN_refl (x : α) : x ≼ₒ{n} x := (ord_refl x).ordN
@[refl] theorem _root_.Iris.Ordered.Order.rfl {x : α} : x ≼ₒ x := ord_refl x
@[refl] theorem _root_.Iris.Ordered.OrderN.rfl {x : α} : x ≼ₒ{n} x := ordN_refl x

theorem ordN_of_dist {n} {x y : α} (h : x ≡{n}≡ y) : x ≼ₒ{n} y := ordN_ne .rfl h (ordN_refl x)
theorem _root_.Iris.OFE.Dist.to_ordN {n} {x y : α} : x ≡{n}≡ y → x ≼ₒ{n} y := ordN_of_dist

end ordRefl

end orderN

variable [ORA α]

theorem valid_of_ord {x y : α} (h : x ≼ₒ y) : ✓ y → ✓ x :=
  valid_mapN fun n => validN_of_ordN (ordN_of_ord n h)

theorem _root_.Iris.Ordered.OrderN.validN {n} {x y : α} : x ≼ₒ{n} y → ✓{n} y → ✓{n} x :=
  validN_of_ordN

theorem validN_of_ord {n} {x y : α} (h : x ≼ₒ y) : ✓{n} y → ✓{n} x :=
  validN_of_ordN (ordN_of_ord n h)
theorem _root_.Iris.Ordered.Order.validN {n} {x y : α} : x ≼ₒ y → ✓{n} y → ✓{n} x := validN_of_ord

theorem pcore_mono_ord' {x y : α} {cx} (le : x ≼ₒ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ₒ cy :=
  pcore_mono_ord le e

theorem pcore_monoN_ord' {n} {x y : α} {cx} (h : x ≼ₒ{n} y) (e : pcore x ≡{n}≡ some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ₒ{n} cy :=
  let ⟨_, hw, ew⟩ := OFE.dist_some e
  let ⟨cy, hcy, hi⟩ := pcore_monoN_ord h hw
  ⟨cy, hcy, ordN_of_dist_of_ordN ew hi⟩

theorem pcore_mono [OrdInc α] {x y cx : α} :
    x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨z, hz⟩, e =>
    let ⟨cy, hcy, o⟩ := pcore_order_op e z
    ⟨cy, hz ▸ hcy, OrdInc.ord_inc o⟩

theorem pcore_mono' [OrdInc α] {x y : α} {cx} (le : x ≼ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ cy :=
  pcore_mono le e

theorem pcore_monoN' [OrdInc α] {n} {x y : α} {cx} :
    x ≼{n} y → pcore x ≡{n}≡ some cx → ∃ cy, pcore y = some cy ∧ cx ≼{n} cy
  | ⟨z, hz⟩, e =>
    let ⟨_, hw, ew⟩ := OFE.dist_some e
    let ⟨_, ht, o⟩ := pcore_order_op hw z
    let ⟨r, hr, er⟩ := pcore_ne' hz.symm ht
    ⟨r, hr, incN_ne ew.symm er (incN_of_inc n (OrdInc.ord_inc o))⟩

theorem pcore_op_mono [OrdInc α] {x cx : α} (e : pcore x = some cx) (y : α) :
    ∃ cy, pcore (x • y) = some (cx • cy) :=
  let ⟨_, h, o⟩ := pcore_order_op e y
  let ⟨z, hz⟩ := OrdInc.ord_inc o
  ⟨z, h.trans (congrArg some hz)⟩

theorem op_monoN_right_ord {n x y} (z : α) (h : x ≼ₒ{n} y) : z • x ≼ₒ{n} z • y :=
  (op_commN.ordN op_commN).1 (op_monoN_left_ord z h)

theorem op_mono_right_ord {x y} (z : α) (h : x ≼ₒ y) : z • x ≼ₒ z • y := by
  rw [comm' (x := z) (y := x), comm' (x := z) (y := y)]; exact op_mono_left_ord z h

theorem op_monoN_ord {n} {x x' y y' : α} (hx : x ≼ₒ{n} x') (hy : y ≼ₒ{n} y') :
    x • y ≼ₒ{n} x' • y' :=
  (op_monoN_left_ord _ hx).trans (op_monoN_right_ord _ hy)

theorem op_mono_ord {x x' y y' : α} (hx : x ≼ₒ x') (hy : y ≼ₒ y') : x • y ≼ₒ x' • y' :=
  (op_mono_left_ord _ hx).trans (op_mono_right_ord _ hy)

theorem optionalOp_monoN_left_ord {n} {x y : α} (mz : Option α) (h : x ≼ₒ{n} y) :
    x •? mz ≼ₒ{n} y •? mz :=
  match mz with
  | none => h
  | some z => op_monoN_left_ord z h

theorem optionalOp_mono_left_ord {x y : α} (mz : Option α) (h : x ≼ₒ y) : x •? mz ≼ₒ y •? mz :=
  match mz with
  | none => h
  | some z => op_mono_left_ord z h

theorem _root_.Iris.Ordered.OrderNR.op_left {n} {x y : α} (z : α) :
    x ≼ₒ*{n} y → x • z ≼ₒ*{n} y • z
  | .inl e => .inl e.op_l
  | .inr h => .inr (op_monoN_left_ord z h)

theorem _root_.Iris.Ordered.OrderR.op_left {x y : α} (z : α) : x ≼ₒ* y → x • z ≼ₒ* y • z
  | .inl e => .inl (e ▸ rfl)
  | .inr h => .inr (op_mono_left_ord z h)

theorem _root_.Iris.Ordered.OrderNR.validN {n} {x y : α} : x ≼ₒ*{n} y → ✓{n} y → ✓{n} x
  | .inl e, v => validN_ne e.symm v
  | .inr h, v => validN_of_ordN h v

theorem _root_.Iris.Ordered.OrderR.validN {n} {x y : α} : x ≼ₒ* y → ✓{n} y → ✓{n} x
  | .inl e, v => e ▸ v
  | .inr h, v => validN_of_ord h v

theorem op_extend_ord {n} {x y₁ y₂ : α} (v : ✓{n} x) (h : y₁ • y₂ ≼ₒ{n} x) :
    ∃ z₁ z₂ : α, z₁ • z₂ ≼ₒ{n.succ} x ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨_, hx', e⟩ := ordN_extend v h
  let ⟨z₁, z₂, hz, hz₁, hz₂⟩ := extend (validN_of_ordN (ordN_succ hx') v) e
  ⟨z₁, z₂, hz ▸ hx', hz₁, hz₂⟩

end ORA

/-! ## Increasing elements -/

section
open ORA
variable [ORA α]

namespace Increasing

theorem of_ordNR {n} {x y : α} (h : Increasing x) (hxy : x ≼ₒ*{n} y) : Increasing y :=
  increasing_closed h hxy
theorem of_dist {n} {x y : α} (h : Increasing x) (e : x ≡{n}≡ y) : Increasing y :=
  h.of_ordNR (.inl e)
theorem of_ordN {n} {x y : α} (h : Increasing x) (hxy : x ≼ₒ{n} y) : Increasing y :=
  h.of_ordNR (.inr hxy)
theorem of_ord {x y : α} (h : Increasing x) (hxy : x ≼ₒ y) : Increasing y :=
  h.of_ordN (ordN_of_ord 0 hxy)
theorem of_ordR {x y : α} (h : Increasing x) : x ≼ₒ* y → Increasing y
  | .inl e => e ▸ h
  | .inr hxy => h.of_ord hxy

theorem ordN {n} {x : α} (h : Increasing x) (y : α) : y ≼ₒ{n} x • y :=
  ordN_of_ord n (h.increasing y)

instance op (x y : α) [Increasing x] [Increasing y] : Increasing (x • y) where
  increasing z := calc
    z ≼ₒ y • z := Increasing.increasing z
    _ ≼ₒ x • (y • z) := Increasing.increasing _
    _ = (x • y) • z := assoc'

end Increasing

instance instIncreasingOfCoreId (x : α) [CoreId x] : Increasing x := pcore_increasing core_id

end

namespace ORA
variable [ORA α]

section total
variable [IsTotal α]

theorem core_ordN_core {n} {x y : α} (le : x ≼ₒ{n} y) : core x ≼ₒ{n} core y :=
  let ⟨_, hcy, icy⟩ := pcore_monoN_ord le (pcore_eq_core x)
  Option.some.inj (hcy.symm.trans (pcore_eq_core y)) ▸ icy

theorem core_mono_ord {x y : α} (le : x ≼ₒ y) : core x ≼ₒ core y :=
  let ⟨_, hcy, icy⟩ := pcore_mono_ord le (pcore_eq_core x)
  Option.some.inj (hcy.symm.trans (pcore_eq_core y)) ▸ icy

theorem core_op_mono_ord (x y : α) : core x ≼ₒ core (x • y) :=
  let ⟨_, hcxy, h⟩ := pcore_order_op (pcore_eq_core x) y
  Option.some.inj (hcxy.symm.trans (pcore_eq_core _)) ▸ h

theorem core_incN_core [OrdInc α] {n} {x y : α} (le : x ≼{n} y) : core x ≼{n} core y :=
  let ⟨_, hcy, icy⟩ := pcore_monoN' le (Dist.of_eq (pcore_eq_core x))
  Option.some.inj (hcy.symm.trans (pcore_eq_core y)) ▸ icy

theorem core_op_mono [OrdInc α] (x y : α) : core x ≼ core (x • y) :=
  OrdInc.ord_inc (core_op_mono_ord x y)

theorem core_mono [OrdInc α] {x y : α} : x ≼ y → core x ≼ core y
  | ⟨z, hz⟩ => hz ▸ core_op_mono x z

instance increasing_core (x : α) : Increasing (core x) := pcore_increasing (pcore_eq_core x)

end total

/-! ## Composition with increasing elements -/

section increasing

theorem ord_op_right (x y : α) [Increasing x] : y ≼ₒ x • y := Increasing.increasing y
theorem ord_op_left (x y : α) [Increasing y] : x ≼ₒ x • y :=
  comm' (x := y) (y := x) ▸ ord_op_right y x
theorem ordN_op_left (n) (x y : α) [Increasing y] : x ≼ₒ{n} x • y := (ord_op_left x y).ordN
theorem ordN_op_right (n) (x y : α) [Increasing x] : y ≼ₒ{n} x • y := (ord_op_right x y).ordN

theorem pcore_ord_self {x : α} {cx} [Increasing x] (e : pcore x = some cx) : cx ≼ₒ x :=
  pcore_op_left e ▸ ord_op_left cx x

theorem core_ord_self [IsTotal α] {x : α} [Increasing x] : core x ≼ₒ x :=
  pcore_ord_self (pcore_eq_core x)

end increasing

section discreteORA

theorem valid_iff_validN' [Discrete α] (n) {x : α} : ✓ x ↔ ✓{n} x :=
  ⟨Valid.validN, fun v => discrete_valid <| validN_of_le (Nat.zero_le n) v⟩

theorem valid_0_iff_validN [Discrete α] (n) {x : α} : ✓{0} x ↔ ✓{n} x :=
  ⟨Valid.validN ∘ discrete_valid, validN_of_le (Nat.zero_le n)⟩

theorem ord_iff_ordN [Discrete α] (n) {x y : α} : x ≼ₒ y ↔ x ≼ₒ{n} y :=
  ⟨ordN_of_ord _, fun h => discrete_ord (ord0_of_ordN h)⟩

theorem ord_0_iff_ordN [Discrete α] (n) {x y : α} : x ≼ₒ{0} y ↔ x ≼ₒ{n} y :=
  ⟨fun h => ordN_of_ord n (discrete_ord h), ord0_of_ordN⟩

end discreteORA

section cancelableElements

theorem cancelable {x y z : α} [Cancelable x] (v : ✓ (x • y)) (e : x • y = x • z) : y = z :=
  OFE.eq_dist_2 fun _ => cancelableN v.validN e.dist

theorem discrete_cancelable {x : α} [Discrete α]
    (H : ∀ {y z : α}, ✓ (x • y) → x • y = x • z → y = z) : Cancelable x where
  cancelableN {n} {_ _} v e := (H ((valid_iff_validN' n).mpr v) (Discrete.discrete e)).dist

instance cancelable_op {x y : α} [Cancelable x] [Cancelable y] : Cancelable (x • y) where
  cancelableN {n w _} v e :=
    have v1 : ✓{n} x • (y • w) := validN_ne op_assocN.symm v
    have v2 := validN_op_right v1
    cancelableN v2 <| cancelableN v1 <| op_assocN.trans <| e.trans op_assocN.symm

instance exclusive_cancelable {x : α} [Exclusive x] : Cancelable x where
  cancelableN v _ := absurd v not_valid_exclN_op_left

theorem op_opM_cancel_dist {x y z : α} {mw : Option α} [Cancelable x]
    (vxy : ✓{n} x • y) (h : x • y ≡{n}≡ (x • z) •? mw) : y ≡{n}≡ z •? mw :=
  match mw with
  | none => cancelableN vxy h
  | some _ => cancelableN vxy (h.trans (op_assocN.symm))

end cancelableElements

section idFreeElements

theorem IdFree.of_dist {x₁ x₂ : α} {n} (e : x₁ ≡{n}≡ x₂) (h : IdFree x₁) : IdFree x₂ where
  id_free0_r z v := fun h₂ =>
    have ee := Dist.le e (Nat.zero_le _)
    have := calc
      x₁ • z ≡{0}≡ x₂ • z := op_left_dist z ee
      _ ≡{0}≡ x₂ := h₂
      _ ≡{0}≡ x₁ := ee.symm
    h.id_free0_r _ ((validN_dist_iff ee).mpr v) this

theorem _root_.Iris.OFE.Dist.idFree {x₁ x₂ : α} (e : x₁ ≡{n}≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  ⟨.of_dist e, .of_dist e.symm⟩

theorem id_freeN_r {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(x • y ≡{n'}≡ x) :=
  id_free0_r _ (validN_of_le (Nat.zero_le _) v) |>.imp (·.le (Nat.zero_le _))

theorem id_freeN_l {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(y • x ≡{n'}≡ x) :=
  id_freeN_r v ∘ comm'.dist.trans

theorem id_free_r {x : α} [IdFree x] {y} (v : ✓ x) : ¬(x • y = x) :=
  fun h => id_free0_r y (valid_iff_validN.mp v 0) h.dist

theorem id_free_l {x : α} [IdFree x] {y} (v : ✓ x) : ¬(y • x = x) :=
  id_free_r v ∘ comm'.trans

theorem discrete_id_free {x : α} [Discrete α] (H : ∀ y, ✓ x → ¬(x • y = x)) : IdFree x where
  id_free0_r y v h := H y (Discrete.discrete_valid v) (Discrete.discrete_0 h)

instance idFree_op_r {x y : α} [IdFree y] [Cancelable x] : IdFree (x • y) where
  id_free0_r z v h :=
    id_free0_r z (validN_op_right v) (cancelableN v (op_assocN.trans h).symm).symm

instance idFree_op_l {x y : α} [IdFree x] [Cancelable y] : IdFree (x • y) := by
  rw [comm']; exact inferInstance

instance exclusive_idFree {x : α} [Exclusive x] : IdFree x where
  id_free0_r z v h := exclusive0_l z ((validN_dist_iff h.symm).mp v)

end idFreeElements

section ucmra

variable {α : Type _} [UORA α]

theorem unit_validN {n} : ✓{n} (unit : α) := valid_iff_validN.mp (unit_valid) n

theorem unit_left_id_dist {n} (x : α) : unit • x ≡{n}≡ x := unit_left_id.dist

theorem unit_right_id {x : α} : x • unit = x := comm'.trans unit_left_id

theorem unit_right_id_dist (x : α) : x • unit ≡{n}≡ x := comm'.dist.trans (unit_left_id_dist x)

theorem incN_unit {n} {x : α} : unit ≼{n} x := ⟨x, unit_left_id.symm.dist⟩

theorem inc_unit {x : α} : unit ≼ x := ⟨x, unit_left_id.symm⟩

instance unit_CoreId : CoreId (unit : α) where
  core_id := pcore_unit

instance unit_total : IsTotal α where
  total x :=
    let ⟨cx, hcx, _⟩ := pcore_order_op (pcore_unit (α := α)) x
    ⟨cx, unit_left_id (x := x) ▸ hcx⟩

instance empty_cancelable : Cancelable (unit : α) where
  cancelableN {n w t} _ e := calc
    w ≡{n}≡ unit • w := unit_left_id.dist.symm
    _ ≡{n}≡ unit • t := e
    _ ≡{n}≡ t := unit_left_id.dist

theorem increasing_iff_unit_ord {x : α} : Increasing x ↔ unit ≼ₒ x :=
  ⟨fun h => unit_right_id (x := x) ▸ h.increasing unit,
   fun h => ⟨fun y => calc
    y = unit • y := unit_left_id.symm
    _ ≼ₒ x • y := op_mono_left_ord y h⟩⟩

theorem ordN_op_right_of_unit_ordN {n} {x : α} (y : α) (h : unit ≼ₒ{n} x) : y ≼ₒ{n} x • y :=
  calc y ≡{n}≡ unit • y := (unit_left_id_dist y).symm
    _ ≼ₒ{n} x • y := op_monoN_left_ord y h

theorem unit_ord_core (x : α) : unit ≼ₒ core x := increasing_iff_unit_ord.mp (increasing_core x)

theorem unit_ordN_core {n} (x : α) : unit ≼ₒ{n} core x := (unit_ord_core x).ordN

theorem exists_op_ordN_iff_ordN [IncOrd α] {n} {x y : α} : (∃ c, x • c ≼ₒ{n} y) ↔ x ≼ₒ{n} y :=
  ⟨fun ⟨c, h⟩ => (ordN_op_left n x c).trans h, fun h => ⟨unit, (unit_right_id (x := x)).symm ▸ h⟩⟩

theorem exists_op_ord_iff_ord [IncOrd α] {x y : α} : (∃ c, x • c ≼ₒ y) ↔ x ≼ₒ y :=
  ⟨fun ⟨c, h⟩ => (ord_op_left x c).trans h, fun h => ⟨unit, (unit_right_id (x := x)).symm ▸ h⟩⟩

theorem exists_op_ordN_iff_incN [OrdInc α] {n} {x y : α} : (∃ c, x • c ≼ₒ{n} y) ↔ x ≼{n} y :=
  ⟨fun ⟨c, h⟩ => (incN_op_left n x c).trans (OrdInc.ordN_incN h),
   fun ⟨c, hc⟩ => ⟨c, hc.symm.to_ordN⟩⟩

theorem exists_op_ord_iff_inc [OrdInc α] {x y : α} : (∃ c, x • c ≼ₒ y) ↔ x ≼ y :=
  ⟨fun ⟨c, h⟩ => (inc_op_left x c).trans (OrdInc.ord_inc h), fun ⟨c, hc⟩ => ⟨c, hc ▸ .rfl⟩⟩

section increasing

theorem ordN_unit {n} {x : α} [Increasing x] : unit ≼ₒ{n} x :=
  unit_left_id (x := x) ▸ ordN_op_left n unit x

theorem ord_unit {x : α} [Increasing x] : unit ≼ₒ x := unit_left_id (x := x) ▸ ord_op_left unit x

end increasing

instance ucmraMonoidOps {α : Type _} [UORA α] : Algebra.MonoidOps (op (α := α)) unit where
  op_ne := ⟨fun _ _ _ hx _ _ hy => hx.op hy⟩
  op_assoc := assoc.symm
  op_comm := comm
  op_left_id := unit_left_id

end ucmra

section Leibniz

theorem assoc_L {x y z : α} : x • (y • z) = (x • y) • z := assoc

theorem comm_L {x y : α} : x • y = y • x := comm

theorem pcore_op_left_L {x cx : α} (h : pcore x = some cx) : cx • x = x :=
   pcore_op_left h

theorem pcore_idem_L {x cx : α} (h : pcore x = some cx) : pcore cx = some cx :=
  pcore_idem h

theorem op_opM_assoc_L {x y : α} {mz} : (x • y) •? mz = x • (y •? mz) :=
  op_opM_assoc _ _ _

theorem pcore_op_right_L {x cx : α} (h : pcore x = some cx) : x • cx = x :=
  pcore_op_right h

theorem pcore_op_self_L {x cx : α} (h : pcore x = some cx) : cx • cx = cx :=
  pcore_op_self h

theorem core_id_dup_L {x : α} [CoreId x] : x • x = x :=
  op_self x

theorem op_core_L {x : α} [IsTotal α] : x • core x = x :=
  op_core x

theorem core_op_L {x : α} [IsTotal α] : core x • x = x :=
  core_op x

theorem core_idem_L {x : α} [IsTotal α] : core (core x) = core x :=
  core_idem x

theorem core_op_core_L {x : α} [IsTotal α] : core x • core x = core x :=
  core_op_core

theorem coreId_iff_core_eq_self {x : α} [IsTotal α] : CoreId x ↔ core x = x :=
  coreId_iff_core_eqv_self

theorem core_eq_self {x : α} [IsTotal α] [c : CoreId x] : core x = x :=
  coreId_iff_core_eq_self.mp c

end Leibniz

section UORA

variable {α : Type _} [UORA α]

theorem ucmra_unit_valid : ✓ (unit : α) := unit_valid

theorem ucmra_unit_left_id {x : α} : unit • x = x := unit_left_id

theorem ucmra_pcore_unit : pcore (unit : α) = some unit := pcore_unit

theorem unit_left_id_L {x : α} : unit • x = x := unit_left_id

theorem unit_right_id_L {x : α} : x • unit = x := unit_right_id

end UORA

end ORA

/-- A morphism between CMRAs is defined to be a non-expansive function which
preserves `validN`, `pcore` and `op`. -/
structure CMRA.Hom (α β : Type _) [OFE α] [Op α] [PCore α] [Validity α]
    [OFE β] [Op β] [PCore β] [Validity β] extends OFE.Hom α β where
  protected validN {n x} : ✓{n} x → ✓{n} (f x)
  protected pcore x : (PCore.pcore x).map f = PCore.pcore (f x)
  protected op x y : f (x • y) = f x • f y

namespace ORA
variable [ORA α]

section Hom

/-- A morphism between ORAs, written `α -C> β`, is defined to be a non-expansive function which
preserves `validN`, `pcore`, `op`, the order and increasing elements. -/
@[ext]
structure Hom (α β : Type _) [ORA α] [ORA β] extends toCMRAHom : CMRA.Hom α β where
  protected monoN_ord {n x₁ x₂} : x₁ ≼ₒ{n} x₂ → f x₁ ≼ₒ{n} f x₂
  protected mono_ord {x₁ x₂} : x₁ ≼ₒ x₂ → f x₁ ≼ₒ f x₂
  protected increasing {x} : Increasing x → Increasing (f x)

@[inherit_doc]
infixr:25 " -C> " => Hom

instance [ORA β] : CoeFun (α -C> β) (fun _ => α → β) := ⟨fun F => F.f⟩

instance [ORA β] : OFE (α -C> β) where
  Dist n f g := f.toHom ≡{n}≡ g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := Hom.ext_iff.trans eq_dist
  dist_lt := dist_lt

/-- The identity morphism of an ordered resource algebra. -/
protected def Hom.id : α -C> α where
  toHom := OFE.Hom.id
  validN := id
  pcore x := by dsimp; cases pcore x <;> rfl
  op _ _ := rfl
  monoN_ord := id
  mono_ord := id
  increasing := id

/-- Composition of ordered resource algebra morphisms. -/
protected def Hom.comp [ORA β] [ORA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
  toHom := OFE.Hom.comp g.toHom f.toHom
  validN v := g.validN (f.validN v)
  pcore x := ((Option.map_map ..).symm.trans (congrArg _ (f.pcore x))).trans (g.pcore (f x))
  op x y := (congrArg g.f (f.op x y)).trans (g.op ..)
  monoN_ord h := g.monoN_ord (f.monoN_ord h)
  mono_ord h := g.mono_ord (f.mono_ord h)
  increasing h := g.increasing (f.increasing h)

protected theorem Hom.core [ORA β] (f : α -C> β) {x : α} : core (f x) = f (core x) := by
  have h := f.pcore x
  unfold core
  cases hx : pcore x <;> rw [hx] at h <;> simp only [Option.map] at h <;> simp [← h]

protected theorem Hom.mono [ORA β] (f : α -C> β) {x₁ x₂ : α} :
    x₁ ≼ x₂ → f x₁ ≼ f x₂ :=
  inc_map f.f f.op

protected theorem Hom.monoN [ORA β] (f : α -C> β) n {x₁ x₂ : α} :
    x₁ ≼{n} x₂ → f x₁ ≼{n} f x₂ :=
  incN_map f.f f.op

protected theorem Hom.valid [ORA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  valid_iff_validN.mpr fun _ => f.validN H.validN

end Hom
end ORA

section HomExt
open ORA
variable [ORA α] [ORA β] [OrdInc α] [IncOrd β]

/-- A morphism between classical resource algebras needs only the classical fields: under the
extension order, `monoN_ord`, `mono_ord` and `increasing` follow from `op`. -/
@[reducible] def CMRA.Hom.toORA (g : CMRA.Hom α β) : α -C> β where
  toCMRAHom := g
  monoN_ord h := IncOrd.incN_ordN (incN_map g.f g.op (OrdInc.ordN_incN h))
  mono_ord h := IncOrd.inc_ord (inc_map g.f g.op (OrdInc.ord_inc h))
  increasing _ := IncOrd.increasing _

end HomExt

section rFunctor

/-- A mixed-variance family of ordered resource algebras with a non-expansive action. -/
class RFunctor (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) where
  [cmra [COFE α] [COFE β] : ORA (F α β)]
  /-- The contravariant and covariant action on non-expansive maps. -/
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

/-- A resource functor whose action on morphisms is contractive. -/
class RFunctorContractive (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type
    _)) extends (RFunctor F) where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] RFunctor.cmra

instance RFunctor.toOFunctor [R : RFunctor F] : COFE.OFunctor F where
  ofe := RFunctor.cmra.toOFE
  map a b := (RFunctor.map a b).toHom
  map_ne.ne := RFunctor.map_ne.ne
  map_id x := RFunctor.map_id x
  map_comp f g f' g' x := RFunctor.map_comp f g f' g' x

instance RFunctorContractive.toOFunctorContractive
    [RFunctorContractive F] : COFE.OFunctorContractive F where
  map_contractive.1 := map_contractive.1

end rFunctor

section urFunctor
open ORA

/-- A resource functor whose values are unital ordered resource algebras. -/
class URFunctor (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) where
  [cmra [COFE α] [COFE β] : UORA (F α β)]
  /-- The action on morphisms of a unital resource functor. -/
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

/-- A unital resource functor with a contractive action on morphisms. -/
class URFunctorContractive (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type
    _)) extends URFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] URFunctor.cmra

/-- A resource functor whose values have increasing composition. -/
class RFunctorAffine (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))
    [RFunctor F] : Prop where
  affine [COFE α] [COFE β] : IncOrd (F α β)

attribute [instance] RFunctorAffine.affine

instance URFunctor.toRFunctor [UF : URFunctor F] : RFunctor F where
  cmra := URFunctor.cmra.toORA
  map f g := URFunctor.map f g
  map_ne := URFunctor.map_ne
  map_id := URFunctor.map_id
  map_comp := URFunctor.map_comp

instance URFunctorContractive.toRFunctorContractive
    [URFunctorContractive F] : RFunctorContractive F where
  map_contractive := map_contractive

end urFunctor

section ComposeRF

open COFE

theorem RFunctorContractive.map_distLater {F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
    [Iris.COFE β] → Type _)} [RFunctorContractive F]
    [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] {n} {f₁ f₂ : α₂ -n> α₁} {g₁ g₂ : β₁ -n> β₂}
    (hf : DistLater n f₁ f₂) (hg : DistLater n g₁ g₂) (x : F α₁ β₁) :
    RFunctor.map f₁ g₁ x ≡{n}≡ RFunctor.map f₂ g₂ x :=
  map_contractive.1 (x := (f₁, g₁)) (y := (f₂, g₂)) (fun m hm => ⟨hf m hm, hg m hm⟩) x

theorem URFunctorContractive.map_distLater {F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
    [Iris.COFE β] → Type _)} [URFunctorContractive F]
    [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] {n} {f₁ f₂ : α₂ -n> α₁} {g₁ g₂ : β₁ -n> β₂}
    (hf : DistLater n f₁ f₂) (hg : DistLater n g₁ g₂) (x : F α₁ β₁) :
    URFunctor.map f₁ g₁ x ≡{n}≡ URFunctor.map f₂ g₂ x :=
  map_contractive.1 (x := (f₁, g₁)) (y := (f₂, g₂)) (fun m hm => ⟨hf m hm, hg m hm⟩) x

variable {F₁ F₂ : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)} [OFunctor
    F₂] [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)]

open OFunctor in
instance rFunctorComposeOF [RFunctor F₁] : RFunctor (ComposeOF F₁ F₂) where
  cmra := RFunctor.cmra (F := F₁)
  map f g := RFunctor.map (F := F₁) (map (F := F₂) g f) (map (F := F₂) f g)
  map_ne.ne _ _ _ hf _ _ hg _ :=
    (RFunctor.map_ne (F := F₁)).ne (fun _ => (map_ne (F := F₂)).ne hg hf _)
      (fun _ => (map_ne (F := F₂)).ne hf hg _) _
  map_id _ := by
    simp only [map_id_eq]
    exact RFunctor.map_id (F := F₁) _
  map_comp _ _ _ _ _ := by
    simp only [map_comp_eq]
    exact RFunctor.map_comp (F := F₁) _ _ _ _ _

open OFunctor in
instance urFunctorComposeOF [URFunctor F₁] : URFunctor (ComposeOF F₁ F₂) where
  cmra := URFunctor.cmra (F := F₁)
  map f g := URFunctor.map (F := F₁) (map (F := F₂) g f) (map (F := F₂) f g)
  map_ne.ne _ _ _ hf _ _ hg _ :=
    (URFunctor.map_ne (F := F₁)).ne (fun _ => (map_ne (F := F₂)).ne hg hf _)
      (fun _ => (map_ne (F := F₂)).ne hf hg _) _
  map_id _ := by
    simp only [map_id_eq]
    exact URFunctor.map_id (F := F₁) _
  map_comp _ _ _ _ _ := by
    simp only [map_comp_eq]
    exact URFunctor.map_comp (F := F₁) _ _ _ _ _

instance instRFunctorAffineComposeOF [RFunctor F₁] [RFunctorAffine F₁] :
    RFunctorAffine (ComposeOF F₁ F₂) where
  affine := RFunctorAffine.affine (F := F₁)

open OFunctor in
instance rFunctorComposeOFContractiveLeft [RFunctorContractive F₁] :
    RFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    RFunctorContractive.map_distLater (F := F₁)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).2 (h m hm).1 _)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).1 (h m hm).2 _) x⟩

open OFunctor in
instance urFunctorComposeOFContractiveLeft [URFunctorContractive F₁] :
    URFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    URFunctorContractive.map_distLater (F := F₁)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).2 (h m hm).1 _)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).1 (h m hm).2 _) x⟩

end ComposeRF

section ComposeRFContractive

open COFE OFunctorContractive

variable {F₁ F₂ : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)}
    [OFunctorContractive F₂]
  [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)]

instance rFunctorComposeOFContractiveRight [RFunctor F₁] :
    RFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    (RFunctor.map_ne (F := F₁)).ne
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _)
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) _) x⟩

instance urFunctorComposeOFContractiveRight [URFunctor F₁] :
    URFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    (URFunctor.map_ne (F := F₁)).ne
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _)
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) _) x⟩

end ComposeRFContractive

section Id
open ORA

instance COFE.OFunctor.constOFRFunctor [ORA B] : RFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance COFE.OFunctor.constOF_RFunctorAffine [ORA B] [IncOrd B] : RFunctorAffine (constOF B) where
  affine := inferInstance

instance OFunctor.constOFRFunctorContractive [ORA B] : RFunctorContractive (constOF B) where
  map_contractive.1 := fun _ => .rfl

instance COFE.OFunctor.constOFURFunctor [UORA B] : URFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance OFunctor.constOFURFunctorContractive [UORA B] : URFunctorContractive (constOF B) where
  map_contractive.1 _ := .rfl

end Id

/-! ## Transporting a CMRA equality

Rocq bundles a CMRA as a record, so a proof of `A = B` transports the whole algebra. In Lean
`ORA` is a type class, and an equality of carriers says nothing about the two instances, so the
transport lemmas are replaced by `transpAp` and the `OFE.transpAp_*` family in
`Iris.Instances.IProp.Instance`, which carry the equality of the instances explicitly. -/

section DiscreteFunO
open ORA

namespace DiscreteFun

variable {α : Type _} {β : α → Type _}

section
variable [∀ x, ORA (β x)]

/-- The resource order on dependent functions. -/
@[reducible] def raOrdered : Ordered (∀ x, β x) where
  OrderN n f g := ∀ x, f x ≼ₒ{n} g x
  Order f g := ∀ x, f x ≼ₒ g x
  ordN_ne ef eg h x := ordN_ne (ef x) (eg x) (h x)
  ordN_succ h x := ordN_succ (h x)
  ordN_trans h₁ h₂ x := ordN_trans (h₁ x) (h₂ x)
  ord_trans h₁ h₂ x := ord_trans (h₁ x) (h₂ x)
  ordN_of_ord n h x := ordN_of_ord n (h x)

attribute [local instance] raOrdered

theorem ordNR_apply {n} {f g : ∀ x, β x} (h : f ≼ₒ*{n} g) (x : α) : f x ≼ₒ*{n} g x :=
  h.imp (· x) (· x)

variable [∀ x, IsTotal (β x)]

/-- Composition on dependent functions. -/
@[reducible]
def raOp : Op (∀ x, β x) where
  op f g x := f x • g x
  op_ne.ne _ _ _ H y := (H y).op_r
  assoc := funext fun _ => assoc
  comm := funext fun _ => comm

/-- The partial core on dependent functions. -/
@[reducible]
def raPCore : PCore (∀ x, β x) where
  pcore f := some fun x => core (f x)
  pcore_ne {n f g _} H := by rintro ⟨⟩; exact ⟨_, rfl, fun x => (H _).core⟩
  pcore_idem := by
    rintro f _ ⟨⟩; exact congrArg some (funext fun x => core_idem (f x))

/-- Validity on dependent functions. -/
@[reducible]
def raValid : _root_.Iris.Validity (∀ x, β x) where
  ValidN n f := ∀ x, ✓{n} f x
  Valid f := ∀ x, ✓ f x
  validN_ne {n x y} H H1 y := (H y).validN.mp (H1 y)
  valid_iff_validN {g} := by simpa [valid_iff_validN] using forall_comm
  validN_succ H _ := validN_succ (H _)

attribute [local instance] raOp raPCore raValid

omit [∀ (x : α), IsTotal (β x)] in
open Classical in
theorem increasing_apply {f : ∀ x, β x} (h : Increasing f) (x : α) : Increasing (f x) where
  increasing y := by
    let g : ∀ x', β x' := fun x' => if e : x' = x then e ▸ y else f x'
    have hg : g x = y := dite_eq_left rfl
    rw [← hg]
    exact h.increasing g x

omit [∀ (x : α), IsTotal (β x)] in
theorem increasing_iff {f : ∀ x, β x} : Increasing f ↔ ∀ x, Increasing (f x) :=
  ⟨increasing_apply, fun h => { increasing := fun g x => (h x).increasing (g x) }⟩

end

end DiscreteFun

section
open DiscreteFun
variable {α : Type _} {β : α → Type _} [∀ x, ORA (β x)] [∀ x, IsTotal (β x)]
attribute [local instance] raOp raPCore raValid raOrdered

variable (β) in
instance cmraDiscreteFunO : ORA (∀ x, β x) where
  toOp := raOp
  toPCore := raPCore
  toValidity := raValid
  validN_op_left H _ := validN_op_left (H _)
  pcore_op_left := by rintro f _ ⟨⟩; exact funext fun x => core_op (f x)
  extend {n f f1 f2} Hv He := by
    let F x := extend (Hv x) (He x)
    exact ⟨fun x => (F x).1, fun x => (F x).2.1,
      funext fun x => (F x).2.2.1, fun x => (F x).2.2.2.1, fun x => (F x).2.2.2.2⟩
  toOrdered := raOrdered
  op_monoN_left_ord h H x := op_monoN_left_ord (h x) (H x)
  op_mono_left_ord h H x := op_mono_left_ord (h x) (H x)
  validN_of_ordN H V x := validN_of_ordN (H x) (V x)
  pcore_monoN_ord := by rintro n f g _ H ⟨⟩; exact ⟨_, rfl, fun x => core_ordN_core (H x)⟩
  pcore_mono_ord := by rintro f g _ H ⟨⟩; exact ⟨_, rfl, fun x => core_mono_ord (H x)⟩
  pcore_order_op := by rintro f _ ⟨⟩ g; exact ⟨_, rfl, fun x => core_op_mono_ord (f x) (g x)⟩
  pcore_increasing := by rintro f _ ⟨⟩; exact increasing_iff.mpr fun x => inferInstance
  increasing_closed H₁ H₂ :=
    increasing_iff.mpr fun x => increasing_closed (increasing_apply H₁ x) (ordNR_apply H₂ x)
  ordN_extend V H :=
    let ⟨z, hz⟩ := Classical.skolem.mp fun x => ordN_extend (V x) (H x)
    ⟨z, fun x => (hz x).1, fun x => (hz x).2⟩

end

instance ucmraDiscreteFunO {α : Type _} (β : α → Type _) [∀ x, UORA (β x)] :
    UORA (∀ x, β x) where
  unit _ := unit
  unit_valid _ := unit_valid
  unit_left_id := funext fun _ => unit_left_id
  pcore_unit := congrArg some (funext fun _ => core_eqv_self _)
  ord_refl f x := ord_refl (f x)

namespace DiscreteFun

variable {α : Type _} {β : α → Type _}

attribute [local instance] raOp in
theorem op_apply [∀ x, ORA (β x)] (f g : ∀ x, β x) (x : α) :
    (f • g) x = f x • g x := rfl

theorem core_apply [∀ x, ORA (β x)] [∀ x, IsTotal (β x)] (f : ∀ x, β x) (x : α) :
    core f x = core (f x) := rfl

theorem unit_apply [∀ x, UORA (β x)] (x : α) : (unit : ∀ x, β x) x = unit := rfl

instance [∀ x, UORA (β x)] [∀ x, OFE.DiscreteE (unit : β x)] : OFE.DiscreteE (unit : ∀ x, β x) where
  discrete h := funext fun x => OFE.DiscreteE.discrete (h x)

variable [∀ x, ORA (β x)] [∀ x, IsTotal (β x)]

theorem ord_apply {f g : ∀ x, β x} (h : f ≼ₒ g) (x : α) : f x ≼ₒ g x := h x

theorem ord_iff {f g : ∀ x, β x} : f ≼ₒ g ↔ ∀ x, f x ≼ₒ g x := .rfl

theorem ordN_iff {n} {f g : ∀ x, β x} : f ≼ₒ{n} g ↔ ∀ x, f x ≼ₒ{n} g x := .rfl

theorem inc_apply {f g : ∀ x, β x} : f ≼ g → ∀ x, f x ≼ g x
  | ⟨h, hh⟩, x => ⟨h x, congrFun hh x⟩

/-- Note: The finiteness assumption from Iris-Rocq is removed using choice. -/
theorem inc_iff {f g : ∀ x, β x} : f ≼ g ↔ ∀ x, f x ≼ g x := by
  refine ⟨inc_apply, fun h => ?_⟩
  obtain ⟨z, hz⟩ := Classical.skolem.mp h
  exact ⟨z, funext hz⟩

theorem incN_apply {n} {f g : ∀ x, β x} : f ≼{n} g → ∀ x, f x ≼{n} g x
  | ⟨h, hh⟩, x => ⟨h x, hh x⟩

/-- Note: The finiteness assumption from Iris-Rocq is removed using choice. -/
theorem incN_iff {n} {f g : ∀ x, β x} : f ≼{n} g ↔ ∀ x, f x ≼{n} g x :=
  ⟨incN_apply, Classical.skolem.mp⟩

instance instOrderRefl [∀ x, OrderRefl (β x)] : OrderRefl (∀ x, β x) where
  ord_refl f x := ord_refl (f x)

instance instIncOrd [∀ x, IncOrd (β x)] : IncOrd (∀ x, β x) :=
  IncOrd.of_increasing fun f => increasing_iff.mpr fun x => IncOrd.increasing (f x)

instance instOrdInc [∀ x, OrdInc (β x)] : OrdInc (∀ x, β x) where
  ord_inc h := inc_iff.mpr fun x => OrdInc.ord_inc (h x)
  ordN_incN h := incN_iff.mpr fun x => OrdInc.ordN_incN (h x)

instance instIsInc [∀ x, IsInc (β x)] : IsInc (∀ x, β x) := {}

end DiscreteFun

/-- Apply a family of resource morphisms pointwise to dependent functions. -/
def mapCodHomC {α : Type _} {β₁ β₂ : α → Type _}
    [∀ x, UORA (β₁ x)] [∀ x, UORA (β₂ x)]
    (F : ∀ x, β₁ x -C> β₂ x) : (∀ x, β₁ x) -C> (∀ x, β₂ x) where
  toHom := mapCodHom fun x => (F x).toHom
  validN h x := (F x).validN (h x)
  pcore _ := congrArg some (funext fun x => (F x).core.symm)
  op f g := funext fun x => (F x).op (f x) (g x)
  monoN_ord h x := (F x).monoN_ord (h x)
  mono_ord h x := (F x).mono_ord (h x)
  increasing h := DiscreteFun.increasing_iff.mpr fun x =>
    (F x).increasing (DiscreteFun.increasing_apply h x)

end DiscreteFunO

section DiscreteFunURF
open ORA

instance urFunctorDiscreteFunOF {C} (F : C → (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
    [Iris.COFE β] → Type _)) [∀ c, URFunctor (F c)] :
    URFunctor (DiscreteFunOF F) where
  map f g := {
    toHom := COFE.OFunctor.map f g
    validN hv _ := (URFunctor.map f g).validN (hv _)
    pcore x := by
      simp only [pcore, Option.map]
      exact congrArg some (funext fun c => ((URFunctor.map f g).core).symm)
    op x y := funext fun c => (URFunctor.map f g).op (x c) (y c)
    monoN_ord h c := (URFunctor.map f g).monoN_ord (h c)
    mono_ord h c := (URFunctor.map f g).mono_ord (h c)
    increasing h := DiscreteFun.increasing_iff.mpr fun c =>
      (URFunctor.map f g).increasing (DiscreteFun.increasing_apply h c)
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

instance instRFunctorAffineDiscreteFunOF {C} (F : C → (∀ (α : Type _) (β : Type _), [Iris.COFE α]
    → [Iris.COFE β] → Type _)) [∀ c, URFunctor (F c)]
    [∀ c, RFunctorAffine (F c)] : RFunctorAffine (DiscreteFunOF F) where
  affine := inferInstance

instance DiscreteFunOFURFC {C} (F : C → (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE
    β] → Type _)) [HURF : ∀ c, URFunctorContractive (F c)] :
    URFunctorContractive (DiscreteFunOF F) where
  map_contractive.1 h _ _ := URFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunURF

section option

open ORA Iris.Option Iris.OFE.Option

variable [ORA α]

/-- Lift the partial core to an optional resource. -/
@[simp]
def optionCore (x : Option α) : Option α := x.bind pcore

/-- Compose optional resources, taking absence as the unit. -/
@[simp]
def optionOp (x y : Option α) : Option α :=
  match x, y with
  | some x', some y' => some (op x' y')
  | none, _ => y
  | _, none => x

/-- Step-indexed validity of an optional resource; absence is valid. -/
@[simp]
def optionValidN (n : Nat) : Option α → Prop
  | some x => ✓{n} x
  | none => True

/-- Validity of an optional resource; absence is valid. -/
@[simp]
def optionValid : Option α → Prop
  | some x => ✓ x
  | none => True

/-- The step-indexed order on `Option α`: `none` lies below `none` and below every increasing
element, `some` is monotone up to `n`-equivalence, and nothing but `none` lies below `none`. -/
@[simp]
def optionOrderN (n : Nat) : Option α → Option α → Prop
  | none, none => True
  | none, some y => Increasing y
  | some x, some y => x ≼ₒ*{n} y
  | some _, none => False

/-- Resource order on optional values, with absence below increasing resources. -/
@[simp]
def optionOrder : Option α → Option α → Prop
  | none, none => True
  | none, some y => Increasing y
  | some x, some y => x ≼ₒ* y
  | some _, none => False

namespace Option

/-- Composition on optional resources. -/
@[reducible]
def raOp : Op (Option α) where
  op := optionOp
  op_ne.ne n x1 x2 H := by
    rename_i x
    rcases x1, x2, x with ⟨_|_, _|_, _|_⟩ <;> simp_all [op_right_dist]
  assoc {x y z} := by
    rcases x, y, z with ⟨_|_, _|_, _|_⟩ <;> first | rfl | exact congrArg some assoc
  comm {x y} := by
    rcases x, y with ⟨_|_, _|_⟩ <;> first | rfl | exact congrArg some comm

/-- The partial core on optional resources. -/
@[reducible]
def raPCore : PCore (Option α) where
  pcore x := some (optionCore x)
  pcore_ne {n} x y cx H := by
    simp only [Option.some.injEq]; rintro rfl
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all only [Dist, Option.Forall₂, optionCore,
        Option.bind_none, exists_eq_left', Option.bind_some]
    cases Hv : pcore x <;> cases Hv' : pcore y <;> simp only []
    · cases pcore_ne H.symm Hv'; simp_all
    · cases pcore_ne H Hv; simp_all
    · obtain ⟨w, Hw1, Hw2⟩ := pcore_ne H.symm Hv'
      cases Hv.symm.trans Hw1
      exact Hw2.symm
  pcore_idem := by
    rintro (_|x) <;> simp only [optionCore, Option.bind_none, Option.some.injEq, forall_eq',
        Option.bind_some]
    rcases H : pcore x with _|y <;> simp only [Option.bind_none, Option.bind_some]
    exact pcore_idem H

/-- Validity on optional resources. -/
@[reducible]
def raValid : _root_.Iris.Validity (Option α) where
  ValidN := optionValidN
  Valid := optionValid
  validN_ne {n} x y H := by
    rcases x, y with ⟨_|_, _|_⟩ <;> simp_all only [Dist, Option.Forall₂, optionValidN, imp_self]
    exact Dist.validN H |>.mp
  valid_iff_validN {x} := by
    rcases x with ⟨_|_⟩ <;> simp [valid_iff_validN]
  validN_succ {x n} := by
    rcases x with ⟨_|_⟩ <;> simp_all [validN_succ]

/-- The resource order on optional resources. -/
@[reducible] def raOrdered : Ordered (Option α) where
  OrderN := optionOrderN
  Order := optionOrder
  ordN_ne {n x x' y y'} ex ey h := by
    rcases x, x', y, y' with ⟨_|x, _|x', _|y, _|y'⟩ <;> simp_all only [Dist, Option.Forall₂,
        optionOrderN]
    · exact h.of_dist ey
    · exact Ordered.OrderNR.ne ex ey h
  ordN_succ {n x y} h := by
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all only [optionOrderN, Nat.succ_eq_add_one]
    exact Ordered.OrderNR.succ h
  ordN_trans {n x y z} h₁ h₂ := by
    rcases x, y, z with ⟨_|x, _|y, _|z⟩ <;> simp_all only [optionOrderN]
    · exact h₁.of_ordNR h₂
    · exact Ordered.OrderNR.trans h₁ h₂
  ord_trans {x y z} h₁ h₂ := by
    rcases x, y, z with ⟨_|x, _|y, _|z⟩ <;> simp_all only [optionOrder]
    · exact h₁.of_ordR h₂
    · exact Ordered.OrderR.trans h₁ h₂
  ordN_of_ord {x y} n h := by
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all only [optionOrder, optionOrderN]
    exact Ordered.OrderR.ordNR n h

section
attribute [local instance] raOp raPCore raValid raOrdered

theorem some_ordN_some_iff {n} {a b : α} : some a ≼ₒ{n} some b ↔ a ≡{n}≡ b ∨ a ≼ₒ{n} b := .rfl

theorem some_ord_some_iff {a b : α} : some a ≼ₒ some b ↔ a = b ∨ a ≼ₒ b := .rfl

theorem none_ordN_some_iff {n} {b : α} : none ≼ₒ{n} some b ↔ Increasing b := .rfl

theorem none_ord_some_iff {b : α} : none ≼ₒ some b ↔ Increasing b := .rfl

theorem not_some_ordN_none {n} {a : α} : ¬some a ≼ₒ{n} none := id

theorem eq_none_of_ordN_none {n} {ma : Option α} : ma ≼ₒ{n} none → ma = none :=
  match ma with | none => fun _ => rfl | some _ => False.elim

theorem exists_of_some_ordN {n} {a : α} {mb : Option α} :
    some a ≼ₒ{n} mb → ∃ b, mb = some b ∧ some a ≼ₒ{n} some b :=
  match mb with | none => False.elim | some b => fun h => ⟨b, rfl, h⟩

theorem exists_of_some_ord {a : α} {mb : Option α} :
    some a ≼ₒ mb → ∃ b, mb = some b ∧ some a ≼ₒ some b :=
  match mb with | none => False.elim | some b => fun h => ⟨b, rfl, h⟩

theorem not_some_ord_none {a : α} : ¬some a ≼ₒ none := id

instance instOrderRefl : OrderRefl (Option α) where
  ord_refl | none => trivial | some _ => Or.inl rfl

theorem increasing_some_iff {a : α} : Increasing (some a) ↔ Increasing a where
  mp h := h.increasing none
  mpr h := ⟨fun | none => h | some b => Or.inr (h.increasing b)⟩

instance instIncreasingNone : Increasing (none : Option α) :=
  ⟨fun | none => trivial | some _ => Or.inl rfl⟩

theorem increasing_pcore (x : α) : Increasing (pcore x : Option α) := match h : pcore x with
  | none => inferInstance
  | some _ => increasing_some_iff.mpr (pcore_increasing h)

theorem none_ord_pcore (x : α) : none ≼ₒ pcore x := match h : pcore x with
  | none => trivial
  | some _ => pcore_increasing h

theorem none_ordN_pcore {n} (x : α) : none ≼ₒ{n} pcore x := Ordered.ordN_of_ord n (none_ord_pcore x)

theorem pcore_ordN_pcore {n} {x y : α} : x ≼ₒ*{n} y → pcore x ≼ₒ{n} pcore y
  | .inl e => (NonExpansive.ne (f := pcore) e).to_ordN
  | .inr i => match hx : pcore x with
    | none => none_ordN_pcore y
    | some _ => let ⟨_, hcy, icy⟩ := pcore_monoN_ord i hx; hcy ▸ Or.inr icy

theorem pcore_ord_pcore {x y : α} : x ≼ₒ* y → pcore x ≼ₒ pcore y
  | .inl rfl => .rfl
  | .inr i => match hx : pcore x with
    | none => none_ord_pcore y
    | some _ => let ⟨_, hcy, icy⟩ := pcore_mono_ord i hx; hcy ▸ Or.inr icy

theorem pcore_ord_pcore_op (x y : α) : (pcore x : Option α) ≼ₒ pcore (x • y) :=
  match hx : pcore x with
  | none => none_ord_pcore _
  | some _ => let ⟨_, hcxy, i⟩ := pcore_order_op hx y; hcxy ▸ Or.inr i

end

end Option

section
attribute [local instance] Option.raOp Option.raPCore Option.raValid Option.raOrdered

instance cmraOption : ORA (Option α) where
  toOp := Option.raOp
  toPCore := Option.raPCore
  toValidity := Option.raValid
  validN_op_left {n x y} := by
    rcases x, y with ⟨_|_, _|_⟩ <;> simp_all only [ValidN, optionValidN, op, optionOp, imp_self,
        implies_true]
    apply validN_op_left
  pcore_op_left {x cx} := by
    rcases x, cx with ⟨_|_, _|_⟩ <;> simp_all only [pcore, optionCore, Option.bind_none, op,
        optionOp, imp_self, Option.some.injEq, not_none_eqv_some, not_some_eqv_none, implies_true,
        Option.bind_some]
    intro h; exact pcore_op_left h
  extend {n} := by
    rintro (_|x) (_|mb1) (_|mb2) Hx Hx' <;> simp only [op, optionOp, Dist.refl,
        not_none_dist_some, not_some_dist_none, some_dist_some] at Hx' ⊢
    · exists none, none
    · exists none, some x
    · exists some x, none
    · rcases extend Hx Hx' with ⟨mc1, mc2, hx, h1, h2⟩
      exact ⟨some mc1, some mc2, congrArg some hx, h1, h2⟩
  toOrdered := Option.raOrdered
  op_monoN_left_ord {n x y} z h := match x, y, z, h with
    | none, none, _, _ => .rfl
    | none, some _, none, h => h
    | none, some _, some z, h => Or.inr (Increasing.ordN h z)
    | some _, none, _, h => False.elim h
    | some _, some _, none, h => h
    | some _, some _, some z, h => Ordered.OrderNR.op_left z h
  op_mono_left_ord {x y} z h := match x, y, z, h with
    | none, none, _, _ => .rfl
    | none, some _, none, h => h
    | none, some _, some z, h => Or.inr (h.increasing z)
    | some _, none, _, h => False.elim h
    | some _, some _, none, h => h
    | some _, some _, some z, h => Ordered.OrderR.op_left z h
  validN_of_ordN {n x y} h v := match x, y, h with
    | none, _, _ => trivial
    | some _, none, h => False.elim h
    | some _, some _, h => Ordered.OrderNR.validN h v
  pcore_monoN_ord {n x y _} h := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    match x, y, h with
    | none, none, _ => trivial
    | none, some y, _ => exact none_ordN_pcore y
    | some _, none, h => exact False.elim h
    | some x, some y, h => exact pcore_ordN_pcore h
  pcore_mono_ord {x y _} h := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    match x, y, h with
    | none, none, _ => trivial
    | none, some y, _ => exact none_ord_pcore y
    | some _, none, h => exact False.elim h
    | some x, some y, h => exact pcore_ord_pcore h
  pcore_order_op {x _} := by
    rintro ⟨⟩ y
    refine ⟨_, rfl, ?_⟩
    match x, y with
    | none, none => trivial
    | none, some y => exact none_ord_pcore y
    | some x, none => exact ord_refl _
    | some x, some y => exact pcore_ord_pcore_op x y
  pcore_increasing {x _} := by
    rintro ⟨⟩
    match x with
    | none => exact (inferInstance : Increasing (none : Option α))
    | some x => exact increasing_pcore x
  increasing_closed {n x y} h h' := match x, y, h' with
    | none, none, _ => inferInstance
    | none, some _, .inl e => False.elim e
    | none, some _, .inr i => increasing_some_iff.mpr i
    | some _, none, .inl e => False.elim e
    | some _, none, .inr i => False.elim i
    | some _, some _, h' =>
      increasing_some_iff.mpr ((increasing_some_iff.mp h).of_ordNR (h'.elim .inl id))
  ordN_extend {n x y} v h := match x, y, h with
    | none, none, _ => ⟨none, trivial, .rfl⟩
    | none, some _, h => ⟨none, h, .rfl⟩
    | some _, none, h => False.elim h
    | some _, some y, .inl e => ⟨some y, Or.inl .rfl, e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz, ez⟩ := ordN_extend v i
      ⟨some z, Or.inr hz, ez⟩

instance ucmraOption : UORA (Option α) where
  unit := none
  unit_valid := trivial
  unit_left_id := by rintro ⟨⟩ <;> rfl
  pcore_unit := by rfl
  ord_refl := ord_refl

end

namespace Option

theorem some_op (a b : α) : some (a • b) = some a • some b := rfl

theorem some_valid {a : α} : ✓ (some a) ↔ ✓ a := .rfl

theorem some_validN {n} {a : α} : ✓{n} (some a) ↔ ✓{n} a := .rfl

theorem pcore_some (a : α) :
    pcore (some a) = (some (pcore a) : Option (Option α)) := rfl

theorem some_core [IsTotal α] (a : α) : some (core a) = core (some a) := by
  simp [core, pcore, optionCore]
  obtain ⟨c, hc⟩ := IsTotal.total a
  simp [hc]

instance some_core_id (a : α) [CoreId a] : CoreId (some a : Option α) where
  core_id := by simp only [pcore_some, Option.some.injEq]; exact CoreId.core_id

instance none_core_id : CoreId (none : Option α) := ⟨rfl⟩

instance option_core_id (ma : Option α) [∀ x : α, CoreId x] : CoreId ma where
  core_id := by
    rcases ma with _|a
    · rfl
    · exact (some_core_id a).core_id

theorem op_none_iff (ma mb : Option α) : ma • mb = none ↔ ma = none ∧ mb = none := by
  cases ma <;> cases mb <;> simp [op, optionOp]

theorem op_isSome (ma mb : Option α) : (ma • mb).isSome ↔ ma.isSome ∨ mb.isSome := by
  cases ma <;> cases mb <;> simp [op, optionOp]

theorem op_none_left_id (a : Option α) : (none : Option α) • a = a := by
  cases a <;> rfl

theorem op_none_right_id (a : Option α) : a • (none : Option α) = a := by
  cases a <;> rfl

theorem dist_of_some_dist_some {n} {x y : α} (H : some x ≡{n}≡ some y) : x ≡{n}≡ y := H

theorem eq_none_of_op_eq_none_left {x y : Option α} (h : x • y = none) : x = none := by
  match x, y with
  | none, _ => rfl
  | some _, none => simp [op] at h
  | some _, some _ => simp [op] at h

theorem eq_none_of_op_eq_none_right {x y : Option α} (h : x • y = none) : y = none := by
  match x, y with
  | _, none => rfl
  | none, some _ => simp [op] at h
  | some _, some _ => simp [op] at h

theorem op_some_opM_assoc {x y : α} {mz : Option α} : (x • y) •? mz = x •? (some y • mz) :=
  match mz with | none => rfl | some _ => assoc'.symm

theorem some_op_opM {a : α} {ma : Option α} : some a • ma = some (a •? ma) := by
  rcases ma with ⟨_|_⟩ <;> simp [optionalOp, op]

theorem opM_opM_assoc {x : α} {y z : Option α} : (x •? y) •? z = x •? (y • z) := by
  rcases y, z with ⟨_|_, _|_⟩ <;> simp [optionalOp, op, assoc.symm]

theorem opM_opM_swap {x : α} {y z : Option α} : (x •? y) •? z = (x •? z) •? y :=
  opM_opM_assoc.trans <| (congrArg (x •? ·) comm).trans opM_opM_assoc.symm

theorem opM_map_some {ma₁ ma₂ : Option α} : ma₁ •? ma₂.map some = ma₁ • ma₂ := by
  rcases ma₁, ma₂ with ⟨_|_, _|_⟩ <;> rfl

theorem op_some_opM_assoc_dist {x y : α} {mz : Option α} : (x • y) •? mz ≡{n}≡ x •? (some y • mz) :=
  match mz with | none => .rfl | some _ => assoc.dist.symm

theorem exists_op_some_eqv_some (x : Option α) (y : α) : ∃ z, x • some y = some z :=
  match x with | .none => ⟨y, rfl⟩ | .some w => ⟨w • y, rfl⟩

theorem exists_op_some_dist_some {n} (x : Option α) (y : α) : ∃ z, x • some y ≡{n}≡ some z :=
  exists_op_some_eqv_some x y |>.elim (⟨·, ·.dist⟩)

theorem not_valid_some_exclN_op_left {n} {x : α} [Exclusive x] {y : α} : ¬✓{n} (some x • some y) :=
  not_valid_exclN_op_left (α := α)

theorem exclusiveN_some_left {n} {a : α} [Exclusive a] {mb : Option α}
    (h : ✓{n} (some a • mb)) : mb = none := by
  cases mb with
  | none => rfl
  | some b => exact (not_valid_some_exclN_op_left h).elim

theorem exclusiveN_some_right {n} {a : α} [Exclusive a] {mb : Option α}
    (h : ✓{n} (mb • some a)) : mb = none :=
  exclusiveN_some_left (validN_ne op_commN h)

theorem exclusive_some_left {a : α} [Exclusive a] {mb : Option α}
    (h : ✓ (some a • mb)) : mb = none :=
  exclusiveN_some_left (n := 0) h.validN

theorem exclusive_some_right {a : α} [Exclusive a] {mb : Option α}
    (h : ✓ (mb • some a)) : mb = none :=
  exclusiveN_some_right (n := 0) h.validN

theorem validN_op_unit {n} {x : Option α} (vx : ✓{n} x) : ✓{n} x • unit := by
  rcases x with ⟨_|_⟩ <;> trivial

/-! ### The order on `Option α` -/
theorem dist_or_ordN_of_some_ordN_some {n} {a b : α} (h : some a ≼ₒ{n} some b) :
    a ≡{n}≡ b ∨ a ≼ₒ{n} b := h

theorem some_ordN_some_of_dist_or_ordN {n} {a b : α} (h : a ≡{n}≡ b ∨ a ≼ₒ{n} b) :
    some a ≼ₒ{n} some b := h

theorem some_ordN_some_of_ordN {n} {a b : α} (h : a ≼ₒ{n} b) : some a ≼ₒ{n} some b := Or.inr h

theorem some_ordN_some_of_dist {n} {a b : α} (h : a ≡{n}≡ b) : some a ≼ₒ{n} some b := Or.inl h

theorem isSome_of_some_ordN {n} {a : α} {mb : Option α} (h : some a ≼ₒ{n} mb) : mb.isSome :=
  match mb, h with
  | some _, _ => rfl
  | none, h => False.elim h

theorem eq_or_ord_of_some_ord_some {a b : α} (h : some a ≼ₒ some b) : a = b ∨ a ≼ₒ b := h

theorem some_ord_some_of_eq_or_ord {a b : α} (h : a = b ∨ a ≼ₒ b) : some a ≼ₒ some b := h

theorem some_ord_some_of_ord {a b : α} (h : a ≼ₒ b) : some a ≼ₒ some b := Or.inr h

theorem some_ord_some_of_eq {a b : α} (h : a = b) : some a ≼ₒ some b := Or.inl h

theorem isSome_of_some_ord {a : α} {mb : Option α} (h : some a ≼ₒ mb) : mb.isSome :=
  match mb, h with
  | some _, _ => rfl
  | none, h => False.elim h

theorem isSome_monoN_ord {n} {ma mb : Option α} (h : ma ≼ₒ{n} mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_ordN h

theorem isSome_mono_ord {ma mb : Option α} (h : ma ≼ₒ mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_ord h

theorem ord_of_some_ord_some [OrderRefl α] {x y : α} (H : some y ≼ₒ some x) : y ≼ₒ x :=
  Or.elim H (· ▸ ord_refl y) id

theorem ordN_of_some_ordN_some [OrderRefl α] {n} {x y : α} (H : some y ≼ₒ{n} some x) :
    y ≼ₒ{n} x :=
  Or.elim H Dist.to_ordN id

theorem some_ord_some_iff_orderRefl [OrderRefl α] {a b : α} : some a ≼ₒ some b ↔ a ≼ₒ b :=
  ⟨ord_of_some_ord_some, Or.inr⟩

theorem some_ordN_some_iff_orderRefl [OrderRefl α] {n} {a b : α} :
    some a ≼ₒ{n} some b ↔ a ≼ₒ{n} b :=
  ⟨ordN_of_some_ordN_some, Or.inr⟩

theorem validN_of_ordN_validN {n} {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼ₒ{n} some a) :
    ✓{n} b :=
  validN_of_ordN (α := Option α) Hinc Hv

theorem valid_of_ord_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ₒ some a) : ✓ b :=
  valid_of_ord (α := Option α) Hinc Hv

theorem ord_iff [IncOrd α] {ma mb : Option α} :
    ma ≼ₒ mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a = b ∨ a ≼ₒ b) :=
  match ma, mb with
  | none, none => ⟨fun _ => .inl rfl, fun _ => trivial⟩
  | none, some b => ⟨fun _ => .inl rfl, fun _ => IncOrd.increasing b⟩
  | some _, none => ⟨False.elim, nofun⟩
  | some a, some b => ⟨fun h => .inr ⟨a, b, rfl, rfl, h⟩, fun | .inr ⟨_, _, rfl, rfl, h⟩ => h⟩

theorem ordN_iff [IncOrd α] {n} {ma mb : Option α} :
    ma ≼ₒ{n} mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼ₒ{n} b) :=
  match ma, mb with
  | none, none => ⟨fun _ => .inl rfl, fun _ => trivial⟩
  | none, some b => ⟨fun _ => .inl rfl, fun _ => IncOrd.increasing b⟩
  | some _, none => ⟨False.elim, nofun⟩
  | some a, some b => ⟨fun h => .inr ⟨a, b, rfl, rfl, h⟩, fun | .inr ⟨_, _, rfl, rfl, h⟩ => h⟩

theorem ord_iff_orderRefl [IncOrd α] [OrderRefl α] {ma mb : Option α} :
    ma ≼ₒ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ₒ b :=
  ord_iff.trans <| or_congr_right <| exists₂_congr fun _ _ =>
    and_congr_right fun _ => and_congr_right fun _ => some_ord_some_iff_orderRefl

theorem ordN_iff_orderRefl [IncOrd α] [OrderRefl α] {n} {ma mb : Option α} :
    ma ≼ₒ{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ₒ{n} b :=
  ordN_iff.trans <| or_congr_right <| exists₂_congr fun _ _ =>
    and_congr_right fun _ => and_congr_right fun _ => some_ordN_some_iff_orderRefl

theorem eqv_of_ord_exclusive [OrdInc α] [Exclusive (a : α)] {b : α} (H : some a ≼ₒ some b)
    (Hv : ✓ b) : a = b :=
  H.elim id fun h => (not_valid_of_excl_inc (OrdInc.ord_inc h) Hv).elim

theorem dist_of_ord_exclusive [OrdInc α] [Exclusive (a : α)] {n} {b : α}
    (H : some a ≼ₒ{n} some b) (Hv : ✓{n} b) : a ≡{n}≡ b :=
  H.elim id fun h => (not_valid_of_exclN_inc (OrdInc.ordN_incN h) Hv).elim

theorem map_mono_ord {β : Type _} [ORA β] [IncOrd β] (f : α → β) {ma mb : Option α}
    (hf : ∀ x y : α, x ≼ₒ y → f x ≼ₒ f y) (h : ma ≼ₒ mb) :
    ma.map f ≼ₒ mb.map f :=
  match ma, mb, h with
  | none, none, _ => trivial
  | none, some b, _ => IncOrd.increasing (f b)
  | some a, some b, h => h.elim (fun e => .inl (congrArg f e)) fun i => .inr (hf a b i)

instance instIncOrd [IncOrd α] : IncOrd (Option α) := IncOrd.of_increasing fun
    | none => inferInstance
    | some a => increasing_some_iff.mpr (IncOrd.increasing a)

instance instOrdInc [OrdInc α] : OrdInc (Option α) where
  ord_inc {mx my} h := match mx, my, h with
    | none, none, _ => ⟨none, rfl⟩
    | none, some b, _ => ⟨some b, rfl⟩
    | some _, some _, .inl e => ⟨none, congrArg some e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz⟩ := OrdInc.ord_inc i
      ⟨some z, congrArg some hz⟩
  ordN_incN {_ mx my} h := match mx, my, h with
    | none, none, _ => ⟨none, .rfl⟩
    | none, some b, _ => ⟨some b, .rfl⟩
    | some _, some _, .inl e => ⟨none, OFE.some_dist_some.mpr e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz⟩ := OrdInc.ordN_incN i
      ⟨some z, OFE.some_dist_some.mpr hz⟩

instance instIsInc [IsInc α] : IsInc (Option α) := {}

/-! ### The extension inclusion on `Option α` -/
theorem some_inc_some_of_dist_opM {n} {x y : α} {mz : Option α} (H : x ≡{n}≡ y •? mz) :
    some y ≼{n} some x :=
  match mz with | none => ⟨none, H⟩ | some z => ⟨some z, H⟩

theorem some_ordN_some_of_dist_opM [IncOrd α] {n} {x y : α} {mz : Option α}
    (H : x ≡{n}≡ y •? mz) : some y ≼ₒ{n} some x :=
  IncOrd.incN_ordN (some_inc_some_of_dist_opM H)

theorem inc_of_some_inc_some [IsTotal α] {x y : α} (H : some y ≼ some x) :
    y ≼ x :=
  let ⟨mz, hmz⟩ := H
  match mz with
  | none => ⟨core y, (Option.some.inj hmz).trans (op_core y).symm⟩
  | some z => ⟨z, Option.some.inj hmz⟩

theorem some_incN_some_iff_some [IsTotal α] {n} {x y : α} :
    some y ≼{n} some x → y ≼{n} x
  | ⟨none, hmz⟩ => ⟨core y, dist_of_some_dist_some hmz |>.trans (op_core_dist y).symm⟩
  | ⟨some z, hmz⟩ => ⟨z, hmz⟩

theorem inc_iff {ma mb : Option α} :
    ma ≼ mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a = b ∨ a ≼ b) := by
  refine ⟨fun ⟨mc, Hmc⟩ => ?_, ?_⟩
  · rcases ma with _|a
    · exact .inl rfl
    rcases mb with _|b
    · rcases mc with _|c <;> simp [op, optionOp] at Hmc
    refine .inr ⟨a, b, rfl, rfl, ?_⟩
    rcases mc with _|c <;> simp only [op, optionOp, Option.some.injEq] at Hmc
    · exact .inl Hmc.symm
    · exact .inr ⟨c, Hmc⟩
  · rintro (H|⟨_, _, _, _, (H|⟨z, _⟩)⟩) <;> subst_eqs
    · exists mb
    · exists none
    · exists some z

theorem incN_iff {n} {ma mb : Option α} :
    ma ≼{n} mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼{n} b) := by
  refine ⟨fun ⟨mc, Hmc⟩ => ?_, ?_⟩
  · rcases ma, mb, mc with ⟨_|_, _|_, _|_⟩ <;> simp_all only [op, optionOp, Dist.refl,
      not_none_eqv_some, false_and, and_self, exists_false, or_false, not_none_dist_some,
      not_some_dist_none, some_dist_some, Option.some.injEq, not_some_eqv_none, exists_and_left,
      exists_eq_left', false_or]
    · exact .inl Hmc.symm
    · exact .inr ⟨_, Hmc⟩
  · rintro (H|⟨_, _, _, _, (H|⟨z, _⟩)⟩) <;> subst_eqs
    · exists mb
    · exists none; simp only [op, optionOp, some_dist_some]; exact H.symm
    · exists some z

theorem inc_iff_isTotal [IsTotal α] {ma mb : Option α} :
    ma ≼ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ b :=
  inc_iff.trans <| or_congr_right <| exists₂_congr fun _ _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨fun h => h.elim (· ▸ inc_refl _) id, .inr⟩

theorem incN_iff_is_total [IsTotal α] {n} {ma mb : Option α} :
    ma ≼{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼{n} b :=
  incN_iff.trans <| or_congr_right <| exists₂_congr fun a _ => and_congr_right fun _ =>
    and_congr_right fun _ =>
      ⟨fun h => h.elim (⟨core a, ·.symm.trans (op_core_dist a).symm⟩) id, .inr⟩

theorem some_incN_some_iff {n} {a b : α} :
    some a ≼{n} some b ↔ a ≡{n}≡ b ∨ a ≼{n} b := by
  apply incN_iff.trans; simp

theorem dist_or_incN_of_some_incN_some {n} {a b : α} (h : some a ≼{n} some b) :
    a ≡{n}≡ b ∨ a ≼{n} b := some_incN_some_iff.mp h

theorem some_incN_some_of_dist_or_incN {n} {a b : α} (h : a ≡{n}≡ b ∨ a ≼{n} b) :
    some a ≼{n} some b := some_incN_some_iff.mpr h

theorem some_incN_some_of_incN {n} {a b : α} (h : a ≼{n} b) : some a ≼{n} some b :=
  some_incN_some_iff.mpr (.inr h)

theorem some_incN_some_of_dist {n} {a b : α} (h : a ≡{n}≡ b) : some a ≼{n} some b :=
  some_incN_some_iff.mpr (.inl h)

theorem isSome_of_some_incN {n} {a : α} {mb : Option α} (h : some a ≼{n} mb) :
    mb.isSome := by
  rcases incN_iff.mp h with h | ⟨_, _, _, rfl, _⟩ <;> simp_all

theorem some_inc_some_iff {a b : α} : some a ≼ some b ↔ a = b ∨ a ≼ b := by
  apply inc_iff.trans; simp

theorem eq_or_inc_of_some_inc_some {a b : α} (h : some a ≼ some b) :
    a = b ∨ a ≼ b :=
  some_inc_some_iff.mp h

theorem some_inc_some_of_eq_or_inc {a b : α} (h : a = b ∨ a ≼ b) :
    some a ≼ some b :=
  some_inc_some_iff.mpr h

theorem some_inc_some_of_inc {a b : α} (h : a ≼ b) : some a ≼ some b :=
  some_inc_some_iff.mpr (.inr h)

theorem some_inc_some_of_eq {a b : α} (h : a = b) : some a ≼ some b :=
  some_inc_some_iff.mpr (.inl h)

theorem isSome_of_some_inc {a : α} {mb : Option α} (h : some a ≼ mb) : mb.isSome := by
  rcases inc_iff.mp h with h | ⟨_, _, _, rfl, _⟩ <;> simp_all

theorem isSome_monoN {n} {ma mb : Option α} (h : ma ≼{n} mb) :
    ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_incN h

theorem isSome_mono {ma mb : Option α} (h : ma ≼ mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_inc h

theorem eqv_of_inc_exclusive [Exclusive (a : α)] {b : α} (H : some a ≼ some b)
    (Hv : ✓ b) : a = b :=
  (eq_or_inc_of_some_inc_some H).elim id fun h => (not_valid_of_excl_inc h Hv).elim

theorem dist_of_inc_exclusive [Exclusive (a : α)] {n} {b : α} (H : some a ≼{n} some b)
    (Hv : ✓{n} b) : a ≡{n}≡ b :=
  (dist_or_incN_of_some_incN_some H).elim id fun h => (not_valid_of_exclN_inc h Hv).elim

theorem some_inc_some_iff_is_total [IsTotal α] {a b : α} :
    some a ≼ some b ↔ a ≼ b :=
  ⟨inc_of_some_inc_some, some_inc_some_of_inc⟩

theorem map_mono {β : Type _} [ORA β] (f : α → β) {ma mb : Option α}
    (hf : ∀ x y : α, x ≼ y → f x ≼ f y) (h : ma ≼ mb) :
    ma.map f ≼ mb.map f := by
  rcases inc_iff.mp h with rfl | ⟨a, b, rfl, rfl, hab⟩
  · exact ⟨mb.map f, by cases mb.map f <;> rfl⟩
  · rcases hab with rfl | hab
    · exact inc_refl _
    · exact some_inc_some_iff.mpr (.inr (hf a b hab))

theorem some_incN_some_iff_is_total [IsTotal α] {n} {a b : α} :
    some a ≼{n} some b ↔ a ≼{n} b :=
  ⟨some_incN_some_iff_some, some_incN_some_of_incN⟩

instance {a : α} [IdFree a] [Cancelable a] : Cancelable (some a) := by
  refine ⟨@fun n b c Hv He => ?_⟩
  rcases b, c with ⟨_|b, _|c⟩
  · trivial
  · exact id_free0_r c (valid0_of_validN Hv) (He.symm.le <| n.zero_le)
  · refine id_free0_r b ?_ (He.le <| n.zero_le)
    exact valid0_of_validN (He.validN.mp Hv)
  · exact cancelableN (α := α) Hv He

instance {ma : Option α} [∀ a : α, IdFree a] [∀ a : α, Cancelable a] : Cancelable ma := by
  rcases ma with ⟨_|_⟩
  constructor
  · simp [op]
  · infer_instance

theorem validN_of_incN_validN {n} {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼{n} some a) :
    ✓{n} b :=
  validN_of_incN (α := Option α) Hinc Hv

theorem valid_of_inc_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ some a) : ✓ b :=
  valid_of_inc (α := Option α) Hinc Hv

theorem some_inc_some_iff_opM {a b : α} : some a ≼ some b ↔ ∃ mc, b = a •? mc := by
  simp only [inc_iff, not_some_eqv_none, Option.some.injEq, exists_and_left, exists_eq_left',
      false_or]
  constructor
  · rintro (Heqv | ⟨mc', Hinc⟩)
    · exact ⟨none, by simpa [optionalOp] using Heqv.symm⟩
    · exact ⟨some mc', Hinc⟩
  · rintro ⟨_|z, H⟩
    · exact .inl H.symm
    · exact .inr ⟨z, H⟩

theorem some_incN_some_iff_opM {n} {a b : α} :
    some a ≼{n} some b ↔ ∃ mc, b ≡{n}≡ a •? mc := by
  simp only [incN_iff, not_some_eqv_none, Option.some.injEq, exists_and_left, exists_eq_left',
      false_or]
  constructor
  · rintro (H|H)
    · exists none; simpa [optionalOp] using H.symm
    · rcases H with ⟨mc', H⟩
      exists (some mc')
  · rintro ⟨(_|z), H⟩
    · exact .inl H.symm
    · right; exists z

instance [ORA.Discrete α] : ORA.Discrete (Option α) where
  discrete_valid {x} := match x with
    | none => fun _ => trivial
    | some _ => discrete_valid (α := α)
  discrete_ord {x y} h := match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => h
    | some _, none, h => False.elim h
    | some _, some _, h =>
      Or.elim h (fun e => Or.inl (OFE.Discrete.discrete_0 e))
        fun i => Or.inr (discrete_ord (α := α) i)

end Option
end option

section unit
open ORA

/-- The classical resource algebra on the one-element type. -/
@[instance_reducible] def Unit.cmraData : CMRAData Unit where
  pcore _ := some ()
  op _ _ := ()
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ := id
  pcore_ne _ _ := ⟨(), rfl, .rfl⟩
  validN_ne _ := id
  valid_iff_validN := ⟨fun _ _ => ⟨⟩, fun _ => ⟨⟩⟩
  validN_succ := id
  validN_op_left := id
  assoc := rfl
  comm := rfl
  pcore_op_left _ := rfl
  pcore_idem _ := rfl
  extend _ _ := ⟨(), (), rfl, .rfl, .rfl⟩
  pcore_op_mono _ _ := ⟨.unit, rfl⟩

instance cmraUnit : CMRA Unit := ofCMRAData Unit.cmraData

/-- The unique element is the unit of the one-element resource algebra. -/
@[instance_reducible] def Unit.ucmraData : UCMRAData Unit where
  unit := ()
  unit_valid := ⟨⟩
  unit_left_id := rfl
  pcore_unit := rfl

instance ucmraUnit : UCMRA Unit := UORA.ofUCMRAData Unit.ucmraData

instance : ORA.Discrete Unit where
  discrete_valid _ := ⟨⟩

end unit

section empty
open ORA

/-- The classical resource algebra on the empty type. -/
@[instance_reducible] def Empty.cmraData : CMRAData Empty where
  pcore x := some x
  op x _ := x
  ValidN _ _ := False
  Valid _ := False
  op_ne.ne _ _ _ _ := .rfl
  pcore_ne {_ x} := x.elim
  validN_ne _ := id
  valid_iff_validN {x} := x.elim
  validN_succ := id
  validN_op_left := id
  assoc {x} := x.elim
  comm {x} := x.elim
  pcore_op_left {x} := x.elim
  pcore_idem {x} := x.elim
  extend {_ x} := x.elim
  pcore_op_mono {x} := x.elim

instance cmraEmpty : CMRA Empty := ofCMRAData Empty.cmraData

instance : ORA.Discrete Empty where
  discrete_valid := id

instance (x : Empty) : CoreId x where
  core_id := rfl

instance (x : Empty) : Cancelable x where
  cancelableN := x.elim

end empty

namespace Prod
open ORA

variable {α β : Type _} [ORA α] [ORA β]

/-- The partial core of a pair, defined when both component cores exist. -/
abbrev pcore (x : α × β) : Option (α × β) := (ORA.pcore x.fst).bind fun a =>
  (ORA.pcore x.snd).bind fun b =>
  return (a, b)

/-- Componentwise composition of a pair of resources. -/
abbrev op (x y : α × β) : α × β :=
  (x.1 • y.1, x.2 • y.2)

/-- A pair is valid at an index when both components are valid there. -/
abbrev ValidN n (x : α × β) := ✓{n} x.fst ∧ ✓{n} x.snd

/-- A pair is valid when both components are valid. -/
abbrev Valid (x : α × β) := ✓ x.fst ∧ ✓ x.snd

/-- The componentwise step-indexed order on resource pairs. -/
abbrev OrderN n (x y : α × β) := x.fst ≼ₒ{n} y.fst ∧ x.snd ≼ₒ{n} y.snd

/-- The componentwise order on resource pairs. -/
abbrev Order (x y : α × β) := x.fst ≼ₒ y.fst ∧ x.snd ≼ₒ y.snd

/-- Composition on resource pairs. -/
@[reducible]
def raOp : Op (α × β) where
  op := op
  op_ne.ne _ _ _ h := dist_prod_ext (Dist.op_r <| dist_fst h) (Dist.op_r <| dist_snd h)
  assoc := equiv_prod_ext assoc assoc
  comm := equiv_prod_ext comm comm

/-- The partial core on resource pairs. -/
@[reducible]
def raPCore : PCore (α × β) where
  pcore := pcore
  pcore_ne {n x y cx} h ph := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp ph
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨cy₁, hcy₁, hxy₁⟩ := pcore_ne (dist_fst h) hcx₁
    have ⟨cy₂, hcy₂, hxy₂⟩ := pcore_ne (dist_snd h) hcx₂
    suffices g : cx ≡{n}≡ (cy₁, cy₂) by simp [hcy₁, hcy₂, g, pcore]
    calc
      cx ≡{n}≡ (cx₁, cx₂) := Dist.of_eq (Option.some.inj hcx).symm
      _ ≡{n}≡ (cy₁, cy₂) := dist_prod_ext hxy₁ hxy₂
  pcore_idem {x cx} h := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp h
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨a, ha, ea⟩ := equiv_some (pcore_idem hcx₁)
    have ⟨b, hb, eb⟩ := equiv_some (pcore_idem hcx₂)
    have g : (a, b) = (cx₁, cx₂) := equiv_prod_ext ea eb
    rw [Option.some.inj hcx.symm]
    simp only [ha, hb, pcore]
    exact congrArg some g

/-- Validity on resource pairs. -/
@[reducible]
def raValid : _root_.Iris.Validity (α × β) where
  ValidN := ValidN
  Valid := Valid
  validN_ne {_} x y H := fun ⟨vx1, vx2⟩ => ⟨H.1.validN.mp vx1, H.2.validN.mp vx2⟩
  valid_iff_validN {x} := by
    refine ⟨fun ⟨va, vb⟩ n => ⟨va.validN, vb.validN⟩, fun h => ⟨?_, ?_⟩⟩
    · exact valid_iff_validN.mpr fun n => (h n).left
    · exact valid_iff_validN.mpr fun n => (h n).right
  validN_succ {x n} := fun ⟨va, vb⟩ => ⟨validN_succ va, validN_succ vb⟩

/-- The resource order on resource pairs. -/
@[reducible] def raOrdered : Ordered (α × β) where
  OrderN := OrderN
  Order := Order
  ordN_ne ex ey h :=
    ⟨ordN_ne (dist_fst ex) (dist_fst ey) h.1, ordN_ne (dist_snd ex) (dist_snd ey) h.2⟩
  ordN_succ h := ⟨ordN_succ h.1, ordN_succ h.2⟩
  ordN_trans h₁ h₂ := ⟨ordN_trans h₁.1 h₂.1, ordN_trans h₁.2 h₂.2⟩
  ord_trans h₁ h₂ := ⟨ord_trans h₁.1 h₂.1, ord_trans h₁.2 h₂.2⟩
  ordN_of_ord n h := ⟨ordN_of_ord n h.1, ordN_of_ord n h.2⟩

section
open ORA
attribute [local instance] raOp raPCore raValid raOrdered

theorem pcore_eq_some {x cx : α × β} :
    ORA.pcore x = some cx ↔ ORA.pcore x.1 = some cx.1 ∧ ORA.pcore x.2 = some cx.2 := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ =>
    Option.bind_eq_some_iff.mpr ⟨cx.1, h₁, Option.bind_eq_some_iff.mpr ⟨cx.2, h₂, rfl⟩⟩⟩
  obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact ⟨h₁, h₂⟩

theorem increasing_iff {x : α × β} : Increasing x ↔ Increasing x.1 ∧ Increasing x.2 := ⟨fun h =>
    ⟨⟨fun y => (h.increasing (y, x.2)).1⟩, ⟨fun y => (h.increasing (x.1, y)).2⟩⟩,
   fun ⟨h₁, h₂⟩ => ⟨fun y => ⟨h₁.increasing y.1, h₂.increasing y.2⟩⟩⟩

theorem ordNR_fst {n} {x y : α × β} (h : x ≼ₒ*{n} y) : x.1 ≼ₒ*{n} y.1 := h.imp dist_fst And.left
theorem ordNR_snd {n} {x y : α × β} (h : x ≼ₒ*{n} y) : x.2 ≼ₒ*{n} y.2 := h.imp dist_snd And.right

instance cmraProd : ORA (α × β) where
  toOp := raOp
  toPCore := raPCore
  toValidity := raValid
  validN_op_left := fun ⟨va, vb⟩ => ⟨validN_op_left va, validN_op_left vb⟩
  pcore_op_left h :=
    let ⟨_, ha, ho⟩ := Option.bind_eq_some_iff.mp h
    let ⟨_, hb, hh⟩ := Option.bind_eq_some_iff.mp ho
    (Option.some.inj hh) ▸ (equiv_prod_ext (pcore_op_left ha) (pcore_op_left hb))
  extend := fun ⟨vx₁, vx₂⟩ e =>
    let ⟨z₁, w₁, hx₁, hz₁, hw₁⟩ := extend vx₁ (OFE.dist_fst e)
    let ⟨z₂, w₂, hx₂, hz₂, hw₂⟩ := extend vx₂ (OFE.dist_snd e)
    ⟨(z₁, z₂), (w₁, w₂), equiv_prod_ext hx₁ hx₂, ⟨hz₁, hz₂⟩, ⟨hw₁, hw₂⟩⟩
  toOrdered := raOrdered
  op_monoN_left_ord z h := ⟨op_monoN_left_ord z.1 h.1, op_monoN_left_ord z.2 h.2⟩
  op_mono_left_ord z h := ⟨op_mono_left_ord z.1 h.1, op_mono_left_ord z.2 h.2⟩
  validN_of_ordN h v := ⟨validN_of_ordN h.1 v.1, validN_of_ordN h.2 v.2⟩
  pcore_monoN_ord h e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cy₁, hcy₁, i₁⟩ := pcore_monoN_ord h.1 e₁
    let ⟨cy₂, hcy₂, i₂⟩ := pcore_monoN_ord h.2 e₂
    ⟨(cy₁, cy₂), pcore_eq_some.mpr ⟨hcy₁, hcy₂⟩, i₁, i₂⟩
  pcore_mono_ord h e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cy₁, hcy₁, i₁⟩ := pcore_mono_ord h.1 e₁
    let ⟨cy₂, hcy₂, i₂⟩ := pcore_mono_ord h.2 e₂
    ⟨(cy₁, cy₂), pcore_eq_some.mpr ⟨hcy₁, hcy₂⟩, i₁, i₂⟩
  pcore_order_op e y :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cxy₁, h₁, i₁⟩ := pcore_order_op e₁ y.1
    let ⟨cxy₂, h₂, i₂⟩ := pcore_order_op e₂ y.2
    ⟨(cxy₁, cxy₂), pcore_eq_some.mpr ⟨h₁, h₂⟩, i₁, i₂⟩
  pcore_increasing e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    increasing_iff.mpr ⟨pcore_increasing e₁, pcore_increasing e₂⟩
  increasing_closed h h' :=
    let ⟨h₁, h₂⟩ := increasing_iff.mp h
    increasing_iff.mpr ⟨increasing_closed h₁ (ordNR_fst h'), increasing_closed h₂ (ordNR_snd h')⟩
  ordN_extend v h :=
    let ⟨z₁, h₁, e₁⟩ := ordN_extend v.1 h.1
    let ⟨z₂, h₂, e₂⟩ := ordN_extend v.2 h.2
    ⟨(z₁, z₂), ⟨h₁, h₂⟩, dist_prod_ext e₁ e₂⟩

end

theorem valid_fst {x : α × β} (h : ✓ x) : ✓ x.fst := h.left
theorem valid_snd {x : α × β} (h : ✓ x) : ✓ x.snd := h.right

theorem validN_fst {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.fst := h.left
theorem validN_snd {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.snd := h.right

attribute [local instance] raOp in
theorem mk_op_mk (a a' : α) (b b' : β) : (a, b) • (a', b') = (a • a', b • b') := rfl

theorem mk_valid (a : α) (b : β) : ✓ (a, b) ↔ ✓ a ∧ ✓ b := .rfl

theorem mk_validN {n} (a : α) (b : β) : ✓{n} (a, b) ↔ ✓{n} a ∧ ✓{n} b := .rfl

theorem mk_pcore (a : α) (b : β) :
    ORA.pcore (a, b) = (ORA.pcore a).bind fun c₁ => (ORA.pcore b).bind fun c₂ => some (c₁, c₂) :=
  rfl

theorem mk_core [IsTotal α] [IsTotal β] (a : α) (b : β) :
    core (a, b) = (core a, core b) :=
  congrArg (Option.getD · (a, b)) (pcore_eq_some.mpr ⟨pcore_eq_core a, pcore_eq_core b⟩)

theorem ord_def {x y : α × β} : x ≼ₒ y ↔ x.1 ≼ₒ y.1 ∧ x.2 ≼ₒ y.2 := .rfl

theorem ordN_def {n} {x y : α × β} : x ≼ₒ{n} y ↔ x.1 ≼ₒ{n} y.1 ∧ x.2 ≼ₒ{n} y.2 := .rfl

theorem mk_ord_mk (a a' : α) (b b' : β) : (a, b) ≼ₒ (a', b') ↔ a ≼ₒ a' ∧ b ≼ₒ b' := .rfl

theorem mk_ordN_mk {n} (a a' : α) (b b' : β) :
    (a, b) ≼ₒ{n} (a', b') ↔ a ≼ₒ{n} a' ∧ b ≼ₒ{n} b' := .rfl

theorem inc_def {x y : α × β} : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2 :=
  ⟨fun ⟨z, hz⟩ => ⟨⟨z.1, congrArg Prod.fst hz⟩, ⟨z.2, congrArg Prod.snd hz⟩⟩,
   fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨(z₁, z₂), Prod.ext hz₁ hz₂⟩⟩

theorem incN_def {n} {x y : α × β} :
    x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2 :=
  ⟨fun ⟨z, hz⟩ => ⟨⟨z.1, dist_fst hz⟩, ⟨z.2, dist_snd hz⟩⟩,
   fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨(z₁, z₂), dist_prod_ext hz₁ hz₂⟩⟩

theorem mk_inc_mk (a a' : α) (b b' : β) :
    (a, b) ≼ (a', b') ↔ a ≼ a' ∧ b ≼ b' := inc_def

theorem mk_incN_mk {n} (a a' : α) (b b' : β) :
    (a, b) ≼{n} (a', b') ↔ a ≼{n} a' ∧ b ≼{n} b' := incN_def

instance instIsTotalProd [IsTotal α] [IsTotal β] : IsTotal (α × β) where
  total x :=
    let ⟨ca, ha⟩ := total x.1
    let ⟨cb, hb⟩ := total x.2
    ⟨(ca, cb), pcore_eq_some.mpr ⟨ha, hb⟩⟩

instance instCmraDiscreteProd [ORA.Discrete α] [ORA.Discrete β] : ORA.Discrete (α × β) where
  discrete_valid v := ⟨discrete_valid v.1, discrete_valid v.2⟩
  discrete_ord h := ⟨discrete_ord h.1, discrete_ord h.2⟩

instance instOrderRefl [OrderRefl α] [OrderRefl β] : OrderRefl (α × β) where
  ord_refl x := ⟨ord_refl x.1, ord_refl x.2⟩

instance instIncOrd [IncOrd α] [IncOrd β] : IncOrd (α × β) :=
  IncOrd.of_increasing fun x => increasing_iff.mpr ⟨IncOrd.increasing x.1, IncOrd.increasing x.2⟩

instance instOrdInc [OrdInc α] [OrdInc β] : OrdInc (α × β) where
  ord_inc h := inc_def.mpr (h.imp OrdInc.ord_inc OrdInc.ord_inc)
  ordN_incN h := incN_def.mpr (h.imp OrdInc.ordN_incN OrdInc.ordN_incN)

instance instIsInc [IsInc α] [IsInc β] : IsInc (α × β) := {}

instance instCoreIdPair {x : α} {y : β} [CoreId x] [CoreId y] : CoreId (x, y) where
  core_id := pcore_eq_some.mpr ⟨CoreId.core_id, CoreId.core_id⟩

instance instExclusivePairLeft {x : α} [Exclusive x] {y : β} : Exclusive (x, y) where
  exclusive0_l z hv := exclusive0_l z.1 hv.1

instance instExclusivePairRight {x : α} {y : β} [Exclusive y] : Exclusive (x, y) where
  exclusive0_l z hv := exclusive0_l z.2 hv.2

instance instCancelablePair {x : α} {y : β} [Cancelable x] [Cancelable y] : Cancelable (x, y) where
  cancelableN hv he := ⟨cancelableN hv.1 he.1, cancelableN hv.2 he.2⟩

instance instIdFreePairLeft {x : α} [IdFree x] {y : β} : IdFree (x, y) where
  id_free0_r z hv he := id_free0_r z.1 hv.1 he.1

instance instIdFreePairRight {x : α} {y : β} [IdFree y] : IdFree (x, y) where
  id_free0_r z hv he := id_free0_r z.2 hv.2 he.2

end Prod

section ProdUnit
namespace Prod
open ORA

variable {α β : Type _} [UORA α] [UORA β]

instance ucmraProd : UORA (α × β) where
  unit := (unit, unit)
  unit_valid := ⟨unit_valid, unit_valid⟩
  unit_left_id := Prod.ext unit_left_id unit_left_id
  pcore_unit := pcore_eq_some.mpr ⟨pcore_unit, pcore_unit⟩

theorem mk_split (a : α) (b : β) : (a, b) = ((a, unit) : α × β) • (unit, b) :=
  Prod.ext unit_right_id.symm unit_left_id.symm

theorem mk_op_fst (a a' : α) :
    ((a • a', unit) : α × β) = ((a, unit) : α × β) • (a', unit) :=
  Prod.ext rfl unit_left_id.symm

theorem mk_op_snd (b b' : β) :
    ((unit, b • b') : α × β) = ((unit, b) : α × β) • (unit, b') :=
  Prod.ext unit_left_id.symm rfl

end Prod
end ProdUnit

section OptionProd

open ORA Iris.Option Iris.OFE.Option

variable {α β : Type _} [ORA α] [ORA β]

namespace Option

theorem some_mk_ordN {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ{n} some (a₂, b₂)) :
    some a₁ ≼ₒ{n} some a₂ ∧ some b₁ ≼ₒ{n} some b₂ :=
  h.elim (·.imp .inl .inl) (·.imp .inr .inr)

theorem some_mk_ordN_left {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ{n} some (a₂, b₂)) :
    some a₁ ≼ₒ{n} some a₂ := (some_mk_ordN h).1

theorem some_mk_ordN_right {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ{n} some (a₂, b₂)) :
    some b₁ ≼ₒ{n} some b₂ := (some_mk_ordN h).2

theorem some_mk_ord {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ some (a₂, b₂)) :
    some a₁ ≼ₒ some a₂ ∧ some b₁ ≼ₒ some b₂ :=
  h.elim (fun e => (Prod.mk.inj e).imp .inl .inl) (·.imp .inr .inr)

theorem some_mk_ord_left {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ some (a₂, b₂)) :
    some a₁ ≼ₒ some a₂ := (some_mk_ord h).1

theorem some_mk_ord_right {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ some (a₂, b₂)) :
    some b₁ ≼ₒ some b₂ := (some_mk_ord h).2

theorem some_op_ordN_snd {n} {x y : α × β} {c : Option (α × β)} (h : some x • c ≼ₒ{n} some y) :
    some x.2 • c.map Prod.snd ≼ₒ{n} some y.2 := by
  cases c <;> exact h.imp (·.2) (·.2)

theorem some_mk_incN {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some a₁ ≼{n} some a₂ ∧ some b₁ ≼{n} some b₂ := by
  rcases some_incN_some_iff.mp h with hd | hi
  · exact ⟨some_incN_some_of_dist hd.1, some_incN_some_of_dist hd.2⟩
  · have ⟨h₁, h₂⟩ := Prod.incN_def.mp hi
    exact ⟨some_incN_some_of_incN h₁, some_incN_some_of_incN h₂⟩

theorem some_mk_incN_left {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) : some a₁ ≼{n} some a₂ :=
  (some_mk_incN h).1

theorem some_mk_incN_right {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) : some b₁ ≼{n} some b₂ :=
  (some_mk_incN h).2

theorem some_mk_incN_total_fst [IsTotal α] {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    a₁ ≼{n} a₂ ∧ some b₁ ≼{n} some b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incN h
  ⟨some_incN_some_iff_is_total.mp h₁, h₂⟩

theorem some_mk_incN_total_snd [IsTotal β] {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some a₁ ≼{n} some a₂ ∧ b₁ ≼{n} b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incN h
  ⟨h₁, some_incN_some_iff_is_total.mp h₂⟩

theorem some_mk_inc {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some a₁ ≼ some a₂ ∧ some b₁ ≼ some b₂ := by
  rcases some_inc_some_iff.mp h with he | hi
  · exact ⟨some_inc_some_of_eq (congrArg Prod.fst he),
      some_inc_some_of_eq (congrArg Prod.snd he)⟩
  · have ⟨h₁, h₂⟩ := Prod.inc_def.mp hi
    exact ⟨some_inc_some_of_inc h₁, some_inc_some_of_inc h₂⟩

theorem some_mk_inc_left {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) : some a₁ ≼ some a₂ :=
  (some_mk_inc h).1

theorem some_mk_inc_right {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) : some b₁ ≼ some b₂ :=
  (some_mk_inc h).2

theorem some_mk_inc_total_fst [IsTotal α] {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    a₁ ≼ a₂ ∧ some b₁ ≼ some b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_inc h
  ⟨some_inc_some_iff_is_total.mp h₁, h₂⟩

theorem some_mk_inc_total_snd [IsTotal β] {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some a₁ ≼ some a₂ ∧ b₁ ≼ b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_inc h
  ⟨h₁, some_inc_some_iff_is_total.mp h₂⟩

end Option
end OptionProd

section OptionMor

open ORA

variable {α β : Type _} [ORA α] [ORA β]

/-- Lift a resource morphism to optional resources. -/
def Option.mapC (f : α -C> β) : Option α -C> Option β where
  toHom := optionMap f.toHom
  validN {_ x} h := by cases x with | none => trivial | some a => exact f.validN h
  pcore x := by
    cases x with | none => rfl | some a => exact congrArg some (f.pcore a)
  op x y := by
    cases x <;> cases y <;> try rfl
    exact congrArg some (f.op ..)
  monoN_ord {n x y} h := match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => f.increasing h
    | some _, some _, h => h.imp (f.ne.ne ·) f.monoN_ord
  mono_ord {x y} h := match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => f.increasing h
    | some _, some _, h => h.imp (congrArg f) f.mono_ord
  increasing {x} h := match x, h with
    | none, _ => (inferInstance : Increasing (none : Option β))
    | some _, h => Option.increasing_some_iff.mpr (f.increasing (Option.increasing_some_iff.mp h))

end OptionMor

section ProdMor

open ORA

variable [ORA A] [ORA A'] [ORA B] [ORA B']

/-- The product of two ordered resource algebra morphisms. -/
def Prod.mapC (f : A -C> A') (g : B -C> B') : A × B -C> A' × B' where
  f := Prod.map f g
  ne := inferInstance
  validN {n x} := fun ⟨h1, h2⟩ => ⟨f.validN h1, g.validN h2⟩
  pcore x := by
    simp [Option.map, Prod.map, ORA.pcore, pcore]
    have h2 := g.pcore x.snd
    have h1 := f.pcore x.fst
    cases _ : ORA.pcore x.fst
    · cases _ : ORA.pcore (f.f x.fst) <;> simp_all
    · cases _ : ORA.pcore x.snd <;>
      cases _ : ORA.pcore (f.f x.fst) <;>
      cases _ : ORA.pcore (g.f x.snd) <;>
      simp_all
  op x y := equiv_prod_ext (f.op x.fst y.fst) (g.op x.snd y.snd)
  monoN_ord h := ⟨f.monoN_ord h.1, g.monoN_ord h.2⟩
  mono_ord h := ⟨f.mono_ord h.1, g.mono_ord h.2⟩
  increasing h :=
    Prod.increasing_iff.mpr <| (Prod.increasing_iff.mp h).imp f.increasing g.increasing

end ProdMor

section ProdRF

open RFunctor

instance instRFunctorProdOF [RFunctor F1] [RFunctor F2] : RFunctor (ProdOF F1 F2) where
  map f g := Prod.mapC (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ :=
    Prod.map_ne (fun _ => map_ne.ne Hx Hy _) (fun _ => map_ne.ne Hx Hy _)
  map_id _ := equiv_prod_ext (map_id _) (map_id _)
  map_comp _ _ _ _ _ :=
    equiv_prod_ext (map_comp _ _ _ _ _) (map_comp _ _ _ _ _)

instance instRFunctorAffineProdOF [RFunctor F1] [RFunctor F2] [RFunctorAffine F1]
    [RFunctorAffine F2] : RFunctorAffine (ProdOF F1 F2) where
  affine := inferInstance

instance instRFunctorContractiveProdOF
    [RFunctorContractive F1] [RFunctorContractive F2] :
    RFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => RFunctorContractive.map_contractive.1 H _)
      (fun _ => RFunctorContractive.map_contractive.1 H _)

instance instURFunctorProdOF [URFunctor F1] [URFunctor F2] : URFunctor (ProdOF F1 F2) where
  map f g := Prod.mapC (URFunctor.map f g) (URFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ :=
    Prod.map_ne (fun _ => URFunctor.map_ne.ne Hx Hy _) (fun _ => URFunctor.map_ne.ne Hx Hy _)
  map_id _ := equiv_prod_ext (URFunctor.map_id _) (URFunctor.map_id _)
  map_comp _ _ _ _ _ :=
    equiv_prod_ext (URFunctor.map_comp _ _ _ _ _) (URFunctor.map_comp _ _ _ _ _)

instance instURFunctorContractiveProdOF
    [URFunctorContractive F1] [URFunctorContractive F2] :
    URFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => URFunctorContractive.map_contractive.1 H _)
      (fun _ => URFunctorContractive.map_contractive.1 H _)

end ProdRF

section optionOF

variable {F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)}

instance urFunctorOptionOF [RFunctor F] : URFunctor (OptionOF F) where
  cmra := ucmraOption
  map f g := Option.mapC (RFunctor.map f g)
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

instance instRFunctorAffineOptionOF [RFunctor F] [RFunctorAffine F] :
    RFunctorAffine (OptionOF F) where
  affine := inferInstance

instance urFunctorContractiveOptionOF
    [RFunctorContractive F] : URFunctorContractive (OptionOF F) where
  map_contractive.1 := COFE.OFunctorContractive.map_contractive.1

end optionOF

end Iris
