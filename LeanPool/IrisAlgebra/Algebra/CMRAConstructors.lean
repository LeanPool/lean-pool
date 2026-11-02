/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sukharik (@suhr), Markus de Medeiros, Puming Liu, Janine Lohse
-/
module

-- Adapted for Lean Pool from Iris-Lean.

public import LeanPool.IrisAlgebra.Algebra.CMRA

/-! Resource algebra construction from embeddings and discrete data. -/

@[expose] public section

namespace Iris
open OFE

section CmraMixin

namespace CMRA
open ORA

variable {α β : Type _}

/-- Constructing a CMRA `β` through a mapping into a CMRA `α`.

The mapping may restrict the domain (i.e., we have an injection from `β` to `α`, not a
bijection) and validity. These two restrictions work on opposite "ends" of `α` according to
`≼`: domain restriction must prove that when an element is in the domain, so is its
composition with other elements; validity restriction must prove that if the composition of
two elements is valid, then so are both of the elements. The "domain" is the image of `g` in
`α`, or equivalently the part of `α` where `f` returns `some`. -/
@[reducible]
def ofInjRestrictValidity [CMRA α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → Option β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective into the part of `α` where `f` returns `some`, and `f` is its inverse
    (gf_dist : ∀ (x : α) (y : β) n, f x ≡{n}≡ some y ↔ g y ≡{n}≡ x)
    -- `g` commutes with `pcore` (where it is defined) and with `op`
    (g_pcore_dist : ∀ (y cy : β) n, pcore y ≡{n}≡ some cy ↔ ORA.pcore (g y) ≡{n}≡ some (g cy))
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    -- `g` commutes with `opM` when the right-hand side is produced by `f`, cancelling it
    (g_opM_f : ∀ (x : α) (y : β), g ((f x).elim y (op y)) = g y • x)
    -- the validity predicate on `β` restricts the one on `α`
    (g_validN : ∀ n (y : β), ValidN n y → ✓{n} (g y))
    -- the validity predicate on `β` satisfies the laws of validity
    (validN_ne : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (op y₁ y₂) → ValidN n y₁) :
    CMRA β :=
  have g_ne : ∀ {n} {y₁ y₂ : β}, y₁ ≡{n}≡ y₂ → g y₁ ≡{n}≡ g y₂ := (g_dist ..).mp
  have g_eq : ∀ {y₁ y₂ : β}, y₁ = y₂ ↔ g y₁ = g y₂ :=
    eq_dist.trans <| (forall_congr' fun n => g_dist n _ _).trans eq_dist.symm
  have g_pcore : ∀ {y cy : β}, pcore y = some cy ↔ ORA.pcore (g y) = some (g cy) :=
    eq_dist.trans <| (forall_congr' fun n => g_pcore_dist _ _ n).trans eq_dist.symm
  have gf : ∀ {x : α} {y : β}, f x = some y ↔ g y = x :=
    eq_dist.trans <| (forall_congr' fun n => gf_dist _ _ n).trans eq_dist.symm
  have pcore_idem' : ∀ {y cy : β}, pcore y = some cy → pcore cy = some cy :=
    fun h => g_pcore.mpr <| pcore_idem (g_pcore.mp h)
  have pcore_op_left' : ∀ {y cy : β}, pcore y = some cy → op cy y = y :=
    fun h => g_eq.mpr <| (g_op ..).trans <| pcore_op_left (g_pcore.mp h)
  ofCMRAData {
    pcore, op, Valid, ValidN
    op_ne.ne _ _ _ h := (g_dist ..).mpr <|
      (g_op ..).dist.trans <| (g_ne h).op_r.trans (g_op ..).symm.dist
    pcore_ne h hcy :=
      let ⟨c, hc, hcd⟩ := pcore_ne (g_ne h) (g_pcore.mp hcy)
      dist_some <| (g_pcore_dist ..).mpr <| hc.dist.trans <| some_dist_some.mpr hcd.symm
    validN_ne h hv := validN_ne _ _ _ h hv
    valid_iff_validN := valid_validN _
    validN_succ hv := validN_le _ _ _ hv (Nat.le_succ _)
    validN_op_left hv := validN_op_left _ _ _ hv
    assoc := g_eq.mpr <| by
      simp only [g_op]
      exact assoc
    comm := g_eq.mpr <| (g_op ..).trans <| comm.trans (g_op ..).symm
    pcore_op_left := pcore_op_left'
    pcore_idem := pcore_idem'
    extend := fun hv he => by
      obtain ⟨x₁, x₂, hx, hx₁, hx₂⟩ :=
        extend (g_validN _ _ hv) (((g_dist ..).mp he).trans (g_op ..).dist)
      obtain ⟨w₁, hw₁, hd₁⟩ := distSome ((gf_dist ..).mpr hx₁.symm)
      obtain ⟨w₂, hw₂, hd₂⟩ := distSome ((gf_dist ..).mpr hx₂.symm)
      refine ⟨w₁, w₂, g_eq.mpr ?_, hd₁.symm, hd₂.symm⟩
      rw [g_op, gf.mp hw₁, gf.mp hw₂]
      exact hx
    pcore_op_mono := fun {y cy} h z => by
      obtain ⟨c, hc⟩ := ORA.pcore_op_mono (g_pcore.mp h) (g z)
      obtain ⟨w, hw⟩ : ∃ w, (f c).elim cy (op cy) = op cy w := match f c with
        | some w => ⟨w, rfl⟩
        | none => ⟨cy, (pcore_op_left' (pcore_idem' h)).symm⟩
      rw [← g_op, ← g_opM_f c cy, hw] at hc
      exact ⟨w, g_pcore.mpr hc⟩ }

/-- Constructing a CMRA through an isomorphism that may restrict validity. -/
@[reducible]
def ofIsoRestrictValidity [CMRA α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective, and `f` is its inverse
    (gf : ∀ x : α, g (f x) = x)
    -- `g` commutes with `pcore` and with `op`
    (g_pcore : ∀ y : β, ORA.pcore (g y) = (pcore y).map g)
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    -- the validity predicate on `β` restricts the one on `α`
    (g_validN : ∀ n (y : β), ValidN n y → ✓{n} (g y))
    -- the validity predicate on `β` satisfies the laws of validity
    (validN_ne : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (op y₁ y₂) → ValidN n y₁) :
    CMRA β :=
  ofInjRestrictValidity pcore op Valid ValidN (fun x => some (f x)) g g_dist
    (fun x y n => ⟨fun h => ((g_dist ..).mp h.symm).trans (gf x).dist,
      fun h => (g_dist ..).mpr <| (gf x).dist.trans h.symm⟩)
    (fun y cy n => by
      rw [g_pcore]
      cases pcore y with
      | none => simp
      | some z => exact g_dist n z cy)
    g_op (fun x y => (g_op y (f x)).trans <| congrArg (g y • ·) (gf x))
    g_validN validN_ne valid_validN validN_le validN_op_left

/-- Constructing a CMRA through an isomorphism. -/
@[reducible]
def ofIso [CMRA α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective, and `f` is its inverse
    (gf : ∀ x : α, g (f x) = x)
    -- `g` commutes with `pcore`, `op`, `Valid` and `ValidN`
    (g_pcore : ∀ y : β, ORA.pcore (g y) = (pcore y).map g)
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    (g_valid : ∀ y : β, ✓ (g y) ↔ Valid y)
    (g_validN : ∀ n (y : β), ✓{n} (g y) ↔ ValidN n y) :
    CMRA β :=
  ofIsoRestrictValidity pcore op Valid ValidN f g g_dist gf g_pcore g_op
    (fun n y => (g_validN n y).mpr)
    (fun n y₁ y₂ h hv =>
      (g_validN n y₂).mp <| validN_ne ((g_dist ..).mp h) <| (g_validN n y₁).mpr hv)
    (fun y => (g_valid y).symm.trans <|
      valid_iff_validN.trans <| forall_congr' fun n => g_validN n y)
    (fun n n' y hv hle => (g_validN n' y).mp <| validN_of_le hle <| (g_validN n y).mpr hv)
    (fun n y₁ y₂ hv => (g_validN n y₁).mp <| validN_op_left <|
      g_op y₁ y₂ ▸ (g_validN n (op y₁ y₂)).mpr hv)

/-- Build a discrete classical resource algebra from unindexed algebraic laws. -/
@[reducible]
def ofDiscrete [OFE α] [OFE.Discrete α]
    (pcore : α → Option α) (op : α → α → α) (Valid : α → Prop)
    (assoc : ∀ x y z : α, op x (op y z) = op (op x y) z)
    (comm : ∀ x y : α, op x y = op y x)
    (pcore_op_left : ∀ x cx : α, pcore x = some cx → op cx x = x)
    (pcore_idem : ∀ x cx : α, pcore x = some cx → pcore cx = some cx)
    (valid_op_left : ∀ x y : α, Valid (op x y) → Valid x)
    (pcore_op_mono : ∀ x cx : α, pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) = some (op cx cy)) :
    CMRA α := ofCMRAData {
  pcore := pcore
  op := op
  ValidN _ := Valid
  Valid := Valid
  op_ne.ne _ _ _ h := (congrArg (op _) (OFE.discrete h)).dist
  pcore_ne h hcx := ⟨_, (OFE.discrete h) ▸ hcx, .rfl⟩
  validN_ne h hv := (OFE.discrete h) ▸ hv
  valid_iff_validN := (forall_const Nat).symm
  validN_succ := id
  validN_op_left := valid_op_left _ _
  assoc := assoc ..
  comm := comm ..
  pcore_op_left := pcore_op_left _ _
  pcore_idem := pcore_idem _ _
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩
  pcore_op_mono := pcore_op_mono _ _ }

/-- Build a discrete classical resource algebra whose core is total. -/
@[reducible]
def ofDiscreteTotal [OFE α] [OFE.Discrete α]
    (core : α → α) (op : α → α → α) (Valid : α → Prop)
    (assoc : ∀ x y z : α, op x (op y z) = op (op x y) z)
    (comm : ∀ x y : α, op x y = op y x)
    (core_op_left : ∀ x : α, op (core x) x = x)
    (core_idem : ∀ x : α, core (core x) = core x)
    (valid_op_left : ∀ x y : α, Valid (op x y) → Valid x)
    (core_op_mono : ∀ x y : α, ∃ cy, core (op x y) = op (core x) cy) :
    CMRA α :=
  ofDiscrete (fun x => some (core x)) op Valid assoc comm
    (fun _ _ h => Option.some.inj h ▸ core_op_left _)
    (fun _ _ h => Option.some.inj h ▸ congrArg some (core_idem _))
    valid_op_left
    (fun _ _ h y => Option.some.inj h ▸ (core_op_mono _ y).imp fun _ e => congrArg some e)

section OfDiscrete

instance ofDiscrete_discrete [OFE α] [OFE.Discrete α] (pcore : α → Option α)
    (op : α → α → α) (Valid : α → Prop) h₁ h₂ h₃ h₄ h₅ h₆ :
    @Discrete α (ofDiscrete pcore op Valid h₁ h₂ h₃ h₄ h₅ h₆).toORA :=
  letI := ofDiscrete pcore op Valid h₁ h₂ h₃ h₄ h₅ h₆
  { discrete_valid := id }

end OfDiscrete
end CMRA

/-- Smart constructor for discrete ORA instances. -/
class DiscreteORAData (α : Type _) where
  /-- The partial core operation of the proposed discrete algebra. -/
  pcore : α → Option α
  /-- The composition operation of the proposed discrete algebra. -/
  op : α → α → α
  /-- The validity predicate of the proposed discrete algebra. -/
  Valid : α → Prop
  /-- The resource order of the proposed discrete algebra. -/
  Order : α → α → Prop
  assoc : ∀ x y z : α, op x (op y z) = op (op x y) z
  comm : ∀ x y : α, op x y = op y x
  pcore_op_left : ∀ x cx : α, pcore x = some cx → op cx x = x
  pcore_idem : ∀ x cx : α, pcore x = some cx → pcore cx = some cx
  valid_op_left : ∀ x y : α, Valid (op x y) → Valid x
  ord_trans : ∀ x y z : α, Order x y → Order y z → Order x z
  op_mono_left : ∀ x y z : α, Order x y → Order (op x z) (op y z)
  valid_of_ord : ∀ x y : α, Order x y → Valid y → Valid x
  pcore_mono : ∀ x y cx : α, Order x y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ Order cx cy
  pcore_order_op : ∀ x cx : α, pcore x = some cx →
    ∀ y, ∃ cxy, pcore (op x y) = some cxy ∧ Order cx cxy
  pcore_increasing : ∀ x cx : α, pcore x = some cx → ∀ y, Order y (op cx y)
  increasing_closed : ∀ x y : α, (∀ z, Order z (op x z)) → Order x y → ∀ z, Order z (op y z)

namespace ORA

/-- Construct a discrete ordered resource algebra from unindexed laws. -/
@[reducible] def ofDiscreteORAData [OFE α] [OFE.Discrete α] (d : DiscreteORAData α) : ORA α :=
  letI : Op α :=
    { op := d.op
      op_ne.ne _ _ _ h := (congrArg (d.op _) (OFE.discrete h)).dist
      assoc := d.assoc ..
      comm := d.comm .. }
  letI : PCore α :=
    { pcore := d.pcore
      pcore_ne h hcx := ⟨_, (OFE.discrete h) ▸ hcx, .rfl⟩
      pcore_idem := d.pcore_idem _ _ }
  letI : _root_.Iris.Validity α :=
    { Valid := d.Valid
      ValidN _ := d.Valid
      validN_ne h hv := (OFE.discrete h) ▸ hv
      valid_iff_validN := (forall_const Nat).symm
      validN_succ := id }
  letI : Ordered α :=
    { Order := d.Order
      OrderN _ := d.Order
      ordN_ne ex ey h := (OFE.discrete ex) ▸ (OFE.discrete ey) ▸ h
      ordN_succ := id
      ordN_trans := d.ord_trans _ _ _
      ord_trans := d.ord_trans _ _ _
      ordN_of_ord _ := id }
  { validN_op_left := d.valid_op_left _ _
    pcore_op_left := d.pcore_op_left _ _
    extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩
    op_monoN_left_ord z h := d.op_mono_left _ _ z h
    op_mono_left_ord z h := d.op_mono_left _ _ z h
    validN_of_ordN := d.valid_of_ord _ _
    pcore_monoN_ord h e := d.pcore_mono _ _ _ h e
    pcore_mono_ord h e := d.pcore_mono _ _ _ h e
    pcore_order_op e y := d.pcore_order_op _ _ e y
    pcore_increasing e := ⟨d.pcore_increasing _ _ e⟩
    increasing_closed {_ x y} hx h := ⟨fun z => match h with
        | .inl e => (OFE.discrete e) ▸ hx.increasing z
        | .inr ho => d.increasing_closed x y (fun w => hx.increasing w) ho z⟩
    ordN_extend _ h := ⟨_, h, .rfl⟩ }

instance ofDiscreteORAData_discrete [OFE α] [OFE.Discrete α] (d : DiscreteORAData α) :
    @Discrete α (ofDiscreteORAData d) :=
  letI := ofDiscreteORAData d
  { discrete_valid := id, discrete_ord := id }

end ORA
end CmraMixin
end Iris
