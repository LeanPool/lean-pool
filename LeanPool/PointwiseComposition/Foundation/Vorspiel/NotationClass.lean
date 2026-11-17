/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Basic

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Supplemental notation classes
-/

@[expose] public section

namespace FFL

/-! ## Heterogeneous notation classes -/

/-- Data and laws for HTilde in `FFL`. -/
class HTilde (α : Type*) (β : outParam Type*) where
  /-- The h Tilde construction in `FFL.HTilde`. -/
  hTilde : α → β

/-- The «term∼ » construction in `FFL`. -/
prefix:75 "∼" => HTilde.hTilde
macro_rules
  | `(∼$x) => `(unop% HTilde.hTilde $x)

/-- Data and laws for HArrow in `FFL`. -/
class HArrow (α β : Type*) (γ : outParam Type*) where
  /-- The h Arrow construction in `FFL.HArrow`. -/
  hArrow : α → β → γ

/-- The «term ⇒ₗ » construction in `FFL`. -/
infixr:60 " ⇒ₗ " => HArrow.hArrow
macro_rules | `($x ⇒ₗ $y) => `(binop% HArrow.hArrow $x $y)



/-- Data and laws for HWedge in `FFL`. -/
class HWedge (α β : Type*) (γ : outParam Type*) where
  /-- The h Wedge construction in `FFL.HWedge`. -/
  hWedge : α → β → γ

/-- The «term ⋏ » construction in `FFL`. -/
infixr:69 " ⋏ " => HWedge.hWedge
macro_rules | `($x ⋏ $y) => `(binop% HWedge.hWedge $x $y)



/-- Data and laws for HVee in `FFL`. -/
class HVee (α β : Type*) (γ : outParam Type*) where
  /-- The h Vee construction in `FFL.HVee`. -/
  hVee : α → β → γ

/-- The «term ⋎ » construction in `FFL`. -/
infixr:68 " ⋎ " => HVee.hVee
macro_rules | `($x ⋎ $y) => `(binop% HVee.hVee $x $y)



attribute [match_pattern] HTilde.hTilde HArrow.hArrow HWedge.hWedge HVee.hVee

/-! ## Homogeneous notation classes -/

/-- Data and laws for Tilde in `FFL`. -/
class Tilde (α : Type*) where
  /-- The tilde construction in `FFL.Tilde`. -/
  tilde : α → α

/-- Data and laws for Arrow in `FFL`. -/
class Arrow (α : Type*) where
  /-- The arrow construction in `FFL.Arrow`. -/
  arrow : α → α → α

/-- Data and laws for Wedge in `FFL`. -/
class Wedge (α : Type*) where
  /-- The wedge construction in `FFL.Wedge`. -/
  wedge : α → α → α

/-- Data and laws for Vee in `FFL`. -/
class Vee (α : Type*) where
  /-- The vee construction in `FFL.Vee`. -/
  vee : α → α → α

attribute [match_pattern] Tilde.tilde Arrow.arrow Wedge.wedge Vee.vee

@[default_instance]
instance Tilde.instHTilde [Tilde α] : HTilde α α :=
  ⟨Tilde.tilde⟩

@[default_instance]
instance Arrow.instHArrow [Arrow α] : HArrow α α α :=
  ⟨Arrow.arrow⟩

@[default_instance]
instance Wedge.instHWedge [Wedge α] : HWedge α α α :=
  ⟨Wedge.wedge⟩

@[default_instance]
instance Vee.instHVee [Vee α] : HVee α α α :=
  ⟨Vee.vee⟩

/-- Data and laws for Box in `FFL`. -/
class Box (α : Type*) where
  /-- The box construction in `FFL.Box`. -/
  box : α → α

/-- The «term□ » construction in `FFL`. -/
prefix:76 "□" => Box.box

/-- Data and laws for Dia in `FFL`. -/
class Dia (α : Type*) where
  /-- The dia construction in `FFL.Dia`. -/
  dia : α → α

/-- The «term◇ » construction in `FFL`. -/
prefix:76 "◇" => Dia.dia

/-- Data and laws for Rhd in `FFL`. -/
class Rhd (α : Type*) where
  /-- The rhd construction in `FFL.Rhd`. -/
  rhd : α → α → α

/-- The «term ▷ » construction in `FFL`. -/
infixl:70 " ▷ " => Rhd.rhd

attribute [match_pattern] Box.box Dia.dia Rhd.rhd

/-- Data and laws for Exp in `FFL`. -/
class Exp (α : Type*) where
  /-- The exp construction in `FFL.Exp`. -/
  exp : α → α

/-- Data and laws for Superexp in `FFL`. -/
class Superexp (α : Type*) where
  /-- The superexp construction in `FFL.Superexp`. -/
  superexp : α → α

/-- Data and laws for Smash in `FFL`. -/
class Smash (α : Type*) where
  /-- The smash construction in `FFL.Smash`. -/
  smash : α → α → α

/-- The «term ⊛ » construction in `FFL`. -/
infix:80 " ⊛ " => Smash.smash

/-- Data and laws for Length in `FFL`. -/
class Length (α : Type*) where
  /-- The length construction in `FFL.Length`. -/
  length : α → α

/-- The «term‖ ‖» construction in `FFL`. -/
notation "‖" x "‖" => Length.length x

/-- Coding objects into syntactic objects (e.g. natural numbers, first-order terms) -/
class GödelQuote (α β : Sort*) where
  /-- The quote construction in `FFL.GödelQuote`. -/
  quote : α → β

/-- The «term⌜ ⌝» construction in `FFL`. -/
notation:max "⌜" x "⌝" => GödelQuote.quote x

/-- Data and laws for Sigma Symbol in `FFL`. -/
class SigmaSymbol (α : Type*) where
  /-- The sigma construction in `FFL.SigmaSymbol`. -/
  sigma : α

/-- Data and laws for Pi Symbol in `FFL`. -/
class PiSymbol (α : Type*) where
  /-- The pi construction in `FFL.PiSymbol`. -/
  pi : α

/-- Data and laws for Delta Symbol in `FFL`. -/
class DeltaSymbol (α : Type*) where
  /-- The delta construction in `FFL.DeltaSymbol`. -/
  delta : α

/-- The «termΣ» construction in `FFL`. -/
notation "Σ" => SigmaSymbol.sigma

/-- The «termΠ» construction in `FFL`. -/
notation "Π" => PiSymbol.pi

/-- The «term∆» construction in `FFL`. -/
notation "∆" => DeltaSymbol.delta

attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta

end FFL

end

end PointwiseComposition
