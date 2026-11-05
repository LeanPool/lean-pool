/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf, Sergei Stepanenko, Markus de Medeiros
-/
module

-- Adapted for Lean Pool from Iris-Lean.

public import LeanPool.IrisAlgebra.Std.Nat
public import LeanPool.IrisAlgebra.Std.Option

/-! Ordered families of equivalences and complete step-indexed spaces.

Copyright (c) The Iris-Lean Contributors.
-/

@[expose] public section

namespace Iris

/-- Ordered family of equivalences -/
class OFE (α : Type _) where
  /-- The equivalence relation at a specified step index. -/
  Dist : Nat → α → α → Prop
  dist_eqv : Equivalence (Dist n)
  eq_dist' : x = y ↔ ∀ n, Dist n x y
  dist_lt : Dist n x y → m < n → Dist m x y

open OFE

/-- Notation for equivalence at a specified step index. -/
scoped notation:40 x " ≡{" n "}≡ " y:41 => OFE.Dist n x y

/- `OFE.eq_dist` is `OFE.eq_dist'` restated in preparation for
generalizing over the type of step-indices -/
theorem OFE.eq_dist {α} [self : OFE α] {x y : α} :
  x = y ↔ ∀ n, OFE.Dist n x y := OFE.eq_dist'

theorem OFE.eq_dist_1 {α} [self : OFE α] {x y : α} :
  x = y → ∀ n, OFE.Dist n x y := OFE.eq_dist.mp
theorem OFE.eq_dist_2 {α} [self : OFE α] {x y : α} :
  (∀ n, OFE.Dist n x y) → x = y := OFE.eq_dist.mpr

namespace OFE

theorem dist_equivalence [OFE α] {n} : Equivalence (Dist (α := α) n) := dist_eqv

theorem Dist.lt [OFE α] {m n} {x y : α} : x ≡{n}≡ y → m < n → x ≡{m}≡ y := dist_lt

theorem Dist.le [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (Nat.lt_of_le_of_ne h' hm)

@[refl] theorem Dist.rfl [OFE α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
@[simp, refl] theorem Dist.refl [OFE α] {n} (x : α) : x ≡{n}≡ x := dist_eqv.1 _
@[symm] theorem Dist.symm [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3
theorem Dist.of_eq [OFE α] {x y : α} : x = y → x ≡{n}≡ y := (· ▸ .rfl)

theorem _root_.Eq.dist [OFE α] {x y : α} (h : x = y) : x ≡{n}≡ y := h ▸ .rfl

instance [OFE α] {n} : Trans (OFE.Dist n) (OFE.Dist n) (OFE.Dist n : α → α → Prop) where
  trans := Dist.trans

/-- A function `f : α → β` is non-expansive if it preserves `n`-equivalence. -/
class NonExpansive [OFE α] [OFE β] (f : α → β) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFE α] : NonExpansive (@id α) := ⟨fun _ _ _ h => h⟩

instance const_ne [OFE α] [OFE β] {x : α} : NonExpansive (Function.const β x) := ⟨fun _ _ _ _ =>
    .rfl⟩

/-- Note: Not an instance, as any function can be decomposed as a composition in multiple ways. -/
theorem NonExpansive.comp [OFE α] [OFE β] [OFE γ] {g : β → γ} {f : α → β}
    (hg : NonExpansive g) (hf : NonExpansive f) : NonExpansive (g ∘ f) :=
  ⟨fun {_ _ _} h => hg.ne (hf.ne h)⟩

/-- A function `f : α → β → γ` is non-expansive if it preserves `n`-equivalence in each argument. -/
class NonExpansive₂ [OFE α] [OFE β] [OFE γ] (f : α → β → γ) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

/-- Note: Not an instance, for symmetry with NonExpansive₂.ne_left, which cannot be an instance. -/
theorem NonExpansive₂.ne_right [OFE α] [OFE β] [OFE γ] (f : α → β → γ) [NonExpansive₂ f]
    (a : α) : NonExpansive (f a) :=
  ⟨fun {_ _ _} h => ne Dist.rfl h⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₂.ne_left [OFE α] [OFE β] [OFE γ] (f : α → β → γ) [NonExpansive₂ f]
    (b : β) : NonExpansive (f · b) :=
  ⟨fun {_ _ _} h => ne h Dist.rfl⟩

/-- A function `f : α → β → γ → δ` is non-expansive if it preserves `n`-equivalence in each
argument. -/
class NonExpansive₃ [OFE α] [OFE β] [OFE γ] [OFE δ] (f : α → β → γ → δ) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → ∀ ⦃z₁ z₂⦄, z₁ ≡{n}≡ z₂ →
    f x₁ y₁ z₁ ≡{n}≡ f x₂ y₂ z₂

/-- A function `f : α → β → γ → δ → ε` is non-expansive if it preserves `n`-equivalence in each
argument. -/
class NonExpansive₄ [OFE α] [OFE β] [OFE γ] [OFE δ] [OFE ε] (f : α → β → γ → δ → ε) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → ∀ ⦃z₁ z₂⦄, z₁ ≡{n}≡ z₂ →
    ∀ ⦃w₁ w₂⦄, w₁ ≡{n}≡ w₂ → f x₁ y₁ z₁ w₁ ≡{n}≡ f x₂ y₂ z₂ w₂

/-- `DistLater n x y` means that `x` and `y` are `m`-equivalent for all `m < n`. -/
def DistLater [OFE α] (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

@[refl] theorem DistLater.rfl [OFE α] {n} {x : α} : DistLater n x x := fun _ _ => .rfl
@[simp, refl] theorem DistLater.refl [OFE α] {n} (x : α) : DistLater n x x := fun _ _ => .rfl
@[symm] theorem DistLater.symm [OFE α] {n} {x : α} (h : DistLater n x y) : DistLater n y x :=
  fun _ hm => (h _ hm).symm
theorem DistLater.trans [OFE α] {n} {x : α} (h1 : DistLater n x y) (h2 : DistLater n y z) :
    DistLater n x z := fun _ hm => (h1 _ hm).trans (h2 _ hm)

/-- `DistLater n`-equivalence is an equivalence relation. -/
theorem distLater_eqv [OFE α] {n} : Equivalence (α := α) (DistLater n) where
  refl := DistLater.refl
  symm h := h.symm
  trans h1 := h1.trans

/-- `n`-equivalence implies `DistLater n`-equivalence. -/
theorem Dist.distLater [OFE α] {n} {x y : α} (h : x ≡{n}≡ y) : DistLater n x y :=
  fun _ => dist_lt h

/-- `DistLater n`-equivalence implies `m`-equivalence for all `m < n`. -/
theorem DistLater.dist_lt [OFE α] {m n} {x y : α} (h : DistLater n x y) (hm : m < n) : x ≡{m}≡ y :=
  h _ hm

/-- `DistLater 0`-equivalence is trivial. -/
@[simp] theorem distLater_zero [OFE α] {x y : α} : DistLater 0 x y := nofun

/-- `DistLater (n + 1)`-equivalence is equivalent to `n`-equivalence. -/
theorem distLater_succ [OFE α] {n} {x y : α} : DistLater n.succ x y ↔ x ≡{n}≡ y :=
  ⟨(·.dist_lt (Nat.lt_succ_self _)), fun h1 _ h2 => h1.le (Nat.le_of_lt_succ h2)⟩

theorem distLater_soundness [OFE α] {x y : α} (H : ∀ n, DistLater n x y → x ≡{n}≡ y) : x = y := by
  refine eq_dist_2 fun n => ?_
  induction n with
  | zero => exact H 0 distLater_zero
  | succ n IH => exact H (n + 1) (distLater_succ.mpr IH)

/-- A function `f : α → β` is contractive if it sends `DistLater n`-equivalent inputs to
`n`-equivalent outputs. -/
class Contractive [OFE α] [OFE β] (f : α → β) where
  distLater_dist : DistLater n x y → f x ≡{n}≡ f y

@[simp] theorem Contractive.zero [OFE α] [OFE β] (f : α → β)
    [Contractive f] {x y} : f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

/-- A contractive function is non-expansive. -/
instance ne_of_contractive [OFE α] [OFE β] (f : α → β) [Contractive f] : NonExpansive f where
  ne := fun _ _ _ h => Contractive.distLater_dist (Dist.distLater h)

/-- Pre-composing a non-expansive function preserves `DistLater`. -/
theorem ne_dist_later [OFE α] [OFE β] (f : α → β) [NonExpansive f] {n x y}
    (h : DistLater n x y) : DistLater n (f x) (f y) := fun m hm => NonExpansive.ne (h m hm)

theorem dist_pointwise_lt [OFE β] {n m} {f g : α → β} (hlt : m < n)
    (hp : ∀ a, DistLater n (f a) (g a)) : ∀ a, f a ≡{m}≡ g a := fun a => hp a m hlt

/-- Constant functions are contractive. -/
instance [OFE α] [OFE β] {x : β} : Contractive (fun _ : α => x) where
  distLater_dist := fun _ => Dist.rfl

/-- The discrete OFE obtained from an equality relation `Eq` -/
@[reducible]
def ofDiscrete (α : Type _) : OFE α where
  Dist _ := Eq
  dist_eqv := ⟨congrFun rfl, (Eq.symm ·), (· ▸ ·)⟩
  eq_dist' := (forall_const _).symm
  dist_lt h _ := h

/-- A discrete element in an OFE -/
class DiscreteE {α : Type _} [OFE α] (x : α) : Prop where
  discrete : x ≡{0}≡ y → x = y

/-- A discrete OFE is one where equality is implied by `0`-equivalence. -/
class Discrete (α : Type _) [OFE α] where
  discrete_0 {x y : α} : x ≡{0}≡ y → x = y
export OFE.Discrete (discrete_0)

theorem discreteE_eq [OFE α] {x y : α} (h : x = y) : DiscreteE x ↔ DiscreteE y := h ▸ Iff.rfl

/-- For discrete OFEs, `n`-equivalence implies equality. -/
theorem Discrete.discrete [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{n}≡ y) : x = y :=
  discrete_0 (h.le (Nat.zero_le _))
export OFE.Discrete (discrete)

instance Discrete.toDiscreteE [OFE α] [Discrete α] (x : α) : DiscreteE x := ⟨discrete_0⟩

/-- For discrete OFEs, `0`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete_n [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{0}≡ y) : x ≡{n}≡ y :=
  (discrete h).dist
export OFE.Discrete (discrete_n)

theorem Discrete.discrete_iff [OFE α] [Discrete α] (n) {x y : α} : x = y ↔ x ≡{n}≡ y :=
  ⟨Eq.dist, discrete⟩

theorem Discrete.discrete_iff_0 [OFE α] [Discrete α] (n) {x y : α} : x ≡{0}≡ y ↔ x ≡{n}≡ y :=
  ⟨discrete_n, fun h => h.le (Nat.zero_le _)⟩

/-- Build a Leibniz OFE on `Quotient s` from a step-indexed distance `dist` on the carrier,
given that the setoid relation coincides with the OFE equivalence `fun x y => ∀ n, dist n x y`
(hypothesis `hs`). Quotienting forces the resulting OFE equality to be Leibniz, while
`Quotient.sound`/`Quotient.exact` keep speaking about the domain relation `s.r`. See
https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Evaluating.20a.20specialization.20to.20Leibnize.20OFE.27s/with/606745235
-/
@[reducible] def ofQuotient {X : Type u} {s : Setoid X} (dist : Nat → X → X → Prop)
    (heqv : ∀ {n}, Equivalence (dist n))
    (hlt : ∀ {n m} {x y : X}, dist n x y → m < n → dist m x y)
    (hs : ∀ x y : X, s.r x y ↔ ∀ n, dist n x y) : OFE (Quotient s) :=
  letI D : Nat → Quotient s → Quotient s → Prop :=
    fun n => Quotient.lift₂ (dist n) fun _ _ _ _ hac hbd => propext <|
      have hac' := (hs _ _).mp hac
      have hbd' := (hs _ _).mp hbd
      ⟨fun h => heqv.trans (heqv.trans (heqv.symm (hac' n)) h) (hbd' n),
       fun h => heqv.trans (heqv.trans (hac' n) h) (heqv.symm (hbd' n))⟩
  { Dist := D
    dist_eqv := by
      refine ⟨Quotient.ind fun a => heqv.refl a, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
      · induction x, y using Quotient.ind₂ with | _ a b => exact heqv.symm h
      · induction x, y using Quotient.ind₂ with | _ a b =>
          induction z using Quotient.ind with | _ c => exact heqv.trans h₁ h₂
    eq_dist' {x y} := by
      induction x, y using Quotient.ind₂ with | _ a b =>
        exact ⟨fun h n => (hs _ _).mp (Quotient.exact h) n,
               fun h => Quotient.sound ((hs _ _).mpr h)⟩
    dist_lt := fun {n x y m} h hlt' => by
      induction x, y using Quotient.ind₂ with | _ a b => exact hlt h hlt' }

theorem ofQuotient.dist_mk {X : Type u} {s : Setoid X} {dist : Nat → X → X → Prop}
    {heqv : ∀ {n}, Equivalence (dist n)}
    {hlt : ∀ {n m} {x y : X}, dist n x y → m < n → dist m x y}
    {hs : ∀ x y : X, s.r x y ↔ ∀ n, dist n x y} {n} {x y : X} :
    (ofQuotient dist heqv hlt hs).Dist n (Quotient.mk s x) (Quotient.mk s y) ↔ dist n x y := Iff.rfl

/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is
non-expansive. -/
@[ext] structure Hom (α β : Type _) [OFE α] [OFE β] where
  /-- The underlying function of a non-expansive morphism. -/
  f : α → β
  ne : NonExpansive f

@[inherit_doc]
infixr:25 " -n> " => Hom

instance [OFE α] [OFE β] : CoeFun (α -n> β) (fun _ => α → β) := ⟨Hom.f⟩
instance [OFE α] [OFE β] (f : α -n> β) : NonExpansive f := f.ne

/-- The identity morphism on an OFE. -/
protected def Hom.id [OFE α] : α -n> α where
  f := id
  ne.ne _ _ _ := id

/-- The composition of two morphisms between OFEs. -/
protected def Hom.comp [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  f := g.f ∘ f.f
  ne.1 _ _ _ h := g.ne.1 (f.ne.1 h)

@[simp] theorem Hom.id_apply [OFE α] {x} : (Hom.id : α -n> α) x = x := rfl
@[simp] theorem Hom.comp_apply [OFE α] [OFE β] [OFE γ] {g : β -n> γ} {f : α -n> β} {x} :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem Hom.id_comp [OFE α] [OFE β] {f : α -n> β} : Hom.id.comp f = f := rfl
@[simp] theorem Hom.comp_id [OFE α] [OFE β] {f : α -n> β} : f.comp Hom.id = f := rfl

theorem Hom.comp_assoc [OFE α] [OFE β] [OFE γ] [OFE δ]
    (h : γ -n> δ) (g : β -n> γ) (f : α -n> β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- The constant non-expansive morphism with a specified value. -/
protected def Hom.const [OFE α] [OFE β] (x : β) : α -n> β where
  f := Function.const α x
  ne.ne _ _ _ _ := Dist.rfl

@[simp] theorem Hom.const_apply [OFE α] [OFE β] {x : β} {a : α} :
    (Hom.const x : α -n> β) a = x := rfl

/-- Construct a `Hom` from a subtype bundling a function with its nonexpansiveness proof. -/
def Hom.ofSubtype [OFE α] [OFE β] (f : { f : α → β // NonExpansive f }) : α -n> β :=
  ⟨f.val, f.property⟩

/-- A bundled contractive function between ordered equivalence spaces. -/
@[ext] structure ContractiveHom (α β : Type _) [OFE α] [OFE β] extends Hom α β where
  [contractive : Contractive f]
  ne := ne_of_contractive f

/-- Notation for a bundled contractive map. -/
infixr:25 " -c> " => ContractiveHom

instance [OFE α] [OFE β] : CoeFun (α -c> β) (fun _ => α → β) := ⟨fun x => x.toHom.f⟩
instance [OFE α] [OFE β] (f : α -c> β) : Contractive f := f.contractive

/-- Bundle a function with its available contractiveness instance. -/
def _root_.Function.toContractiveHom (f : α → β) [OFE α] [OFE β] [ι : OFE.Contractive f] : α -c> β
    where
  f := f
  contractive := ι

@[simp] theorem _root_.Function.toContractiveHom_apply {f : α → β} [OFE α] [OFE β] [ι :
    OFE.Contractive f] {x} :
  f.toContractiveHom x = f x := by rfl

theorem InvImage.equivalence {α : Sort u} {β : Sort v}
    {r : β → β → Prop} {f : α → β} (H : Equivalence r) : Equivalence (InvImage r f) where
  refl _ := H.refl _
  symm := H.symm
  trans := H.trans

instance unitOFE : OFE Unit where
  Dist _ _ _ := True
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  eq_dist' := by simp
  dist_lt _ _ := ⟨⟩

instance : DiscreteE (() : Unit) := ⟨fun _ => Subsingleton.elim _ _⟩

instance : OFE Empty where
  Dist _ _ _ := True
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  eq_dist' {x} := x.elim
  dist_lt _ _ := ⟨⟩

instance [OFE α] : OFE (ULift α) where
  Dist n x y := x.down ≡{n}≡ y.down
  dist_eqv := InvImage.equivalence dist_eqv
  eq_dist' {x y} := by cases x; cases y; rw [ULift.up.injEq]; exact eq_dist
  dist_lt := dist_lt

/-- The non-expansive injection into a universe lift. -/
def uliftUpHom [OFE α] : α -n> ULift α where
  f := .up
  ne.1 _ _ _ := id

/-- The non-expansive projection from a universe lift. -/
def uliftDownHom [OFE α] : ULift α -n> α where
  f := ULift.down
  ne.1 _ _ _ := id

instance [OFE α] : OFE (Option α) where
  Dist n := Option.Forall₂ (Dist n)
  dist_eqv := Option.Forall₂.equivalence dist_eqv
  eq_dist' {x y} := by cases x <;> cases y <;> simp [Option.Forall₂, eq_dist]
  dist_lt {_ x y _} := by cases x <;> cases y <;> simp only [Option.Forall₂, implies_true,
      imp_false, Nat.not_lt, false_implies]; apply dist_lt

instance [OFE α] [OFE.Discrete α] : OFE.Discrete (Option α) where
  discrete_0 {mx my} e :=
    match mx, my with
    | none, none => rfl
    | none, some _ => e.elim
    | some _, none => e.elim
    | some _, some _ => congrArg some (discrete_0 e)

@[simp]
theorem some_dist_some [OFE α] {n} {x y : α} : (some x ≡{n}≡ some y) ↔ x ≡{n}≡ y := .rfl
@[simp] theorem not_some_dist_none [OFE α] {n} {x : α} : ¬some x ≡{n}≡ none := id
@[simp] theorem not_none_dist_some [OFE α] {n} {x : α} : ¬none ≡{n}≡ some x := id

theorem dist_none [OFE α] {o : Option α} : o ≡{n}≡ none ↔ o = none :=
  ⟨fun h => by cases o with | none => rfl | some _ => exact h.elim, (· ▸ .rfl)⟩

theorem dist_some [OFE α] {n mx y} (h : mx ≡{n}≡ some y) :
    ∃ z : α, mx = some z ∧ y ≡{n}≡ z :=
  suffices hh : ∀ mx my y, mx ≡{n}≡ my → my = some y → ∃ t, mx = some t ∧ t ≡{n}≡ y from
    (hh mx (some y) _ h rfl).elim (fun t h => ⟨t, h.left, h.right.symm⟩)
  fun mx _ y e1 e2 =>
    match mx with
    | some t => ⟨t, rfl, (e2 ▸ e1 : some t ≡{n}≡ some y)⟩
    | none => False.elim (e2 ▸ e1 : none ≡{n}≡ some y)

/-- Data-valued form of `dist_some`, for building the witnesses of `ORA.extend`. -/
def distSome [OFE α] {n} {mx : Option α} {y : α} (h : mx ≡{n}≡ some y) :
    (z : α) ×' mx = some z ∧ y ≡{n}≡ z :=
  match mx, h with
  | some _, h => ⟨_, rfl, h.symm⟩
  | none, h => h.elim

theorem dist_some_inv_l [OFE α] {n} {mx my : Option α} {x} (h : mx ≡{n}≡ my)
    (e : mx = some x) : ∃ y, my = some y ∧ x ≡{n}≡ y := by
  subst e; exact dist_some h.symm

theorem dist_some_inv_r [OFE α] {n} {mx my : Option α} {y} (h : mx ≡{n}≡ my)
    (e : my = some y) : ∃ x, mx = some x ∧ x ≡{n}≡ y := by
  subst e; obtain ⟨z, hz, hd⟩ := dist_some h; exact ⟨z, hz, hd.symm⟩

theorem dist_some_inv_l' [OFE α] {n} {my : Option α} {x} (h : some x ≡{n}≡ my) :
    ∃ x', some x' = my ∧ x ≡{n}≡ x' :=
  let ⟨y, hy, hd⟩ := dist_some_inv_l h rfl; ⟨y, hy.symm, hd⟩

theorem fmap_some_dist [OFE β] (f : α → β) {mx : Option α} {y : β} {n} :
    (Option.map f mx ≡{n}≡ some y) ↔ ∃ x, mx = some x ∧ y ≡{n}≡ f x := by
  refine ⟨fun h => ?_, ?_⟩
  · match mx with
    | none => exact absurd h not_none_dist_some
    | some x => exact ⟨x, rfl, (some_dist_some.mp h).symm⟩
  · rintro ⟨x, rfl, hd⟩; exact some_dist_some.mpr hd.symm

instance Option.some.ne [OFE α] : OFE.NonExpansive (some : α → Option α) := ⟨fun _ _ _ => id⟩

instance Option.some_is_discrete [OFE α] {e : α} [OFE.DiscreteE e] : OFE.DiscreteE (some e) where
  discrete {y} h :=
    match y with
    | .none => absurd h not_some_dist_none
    | .some _ => congrArg some (DiscreteE.discrete h)

/-- Note: Not an instance, due to instance coherence problems. -/
theorem Option.ne_match [OFE α] {B : Type _} [OFE B]
    (f : α → B) (hf : NonExpansive f) (g : B) :
    NonExpansive (fun x : Option α => match x with | some a => f a | none => g) :=
  ⟨fun {n x' y'} (h : Option.Forall₂ (Dist n) x' y') =>
    match x', y', h with | some _, some _, h => hf.ne h | none, none, _ => Dist.rfl⟩

instance Option.none_is_discrete [OFE α] : DiscreteE (none : Option α) := by
  constructor; rintro (_|_) <;> simp

instance Option.merge_ne [OFE α] {op : α → α → α} [NonExpansive₂ op] :
    NonExpansive₂ (Option.merge op) where
  ne n x1 x2 Hx y1 y2 Hy := by
    rcases x1, x2, y1, y2 with ⟨_|_, _|_, _|_, _|_⟩ <;> simp_all only [Dist.refl,
        Option.merge_none_right, not_none_dist_some, not_some_dist_none, some_dist_some,
        Option.merge_none_left, Option.merge_some_some]
    exact NonExpansive₂.ne Hx Hy

instance Option.bind_fun_ne [OFE α] [OFE β] (f : α → Option β) [NonExpansive f] : NonExpansive
    (flip Option.bind f) where
  ne _ _ x2 Hx := match x2 with
    | some _ => (dist_some Hx).choose_spec.left ▸ (NonExpansive.ne (f := f) (dist_some
        Hx).choose_spec.right.symm)
    | none => (dist_none.mp Hx).symm ▸ .rfl

theorem Option.bind_dist [OFE β] {x : Option α} {f g : α → Option β} (H : ∀ x, f x ≡{n}≡ g
    x) : Option.bind x f ≡{n}≡ Option.bind x g :=
  match x with
  | some _ => H _
  | none => .rfl

/-- A pointwise family of ordered equivalence structures. -/
abbrev OFEFun {α : Type _} (β : α → Type _) := ∀ a, OFE (β a)

instance [OFEFun (β : α → _)] : OFE ((x : α) → β x) where
  Dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  eq_dist' {_ _} := by rw [funext_iff]; simpa only [eq_dist] using forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2

instance [OFE α] [OFE β] : OFE (α -n> β) where
  Dist n f g := f.f ≡{n}≡ g.f
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := Hom.ext_iff.trans eq_dist
  dist_lt := dist_lt

instance ofe_mor_car_ne [OFE α] [OFE β] :
    NonExpansive₂ (fun (f : α -n> β) (x : α) => f x) where
  ne _ _ _ hf _ _ hx := dist_eqv.trans (hf _) (NonExpansive.ne hx)

instance [OFE α] [OFE β] [Inhabited β] : Inhabited (α -n> β) where
  default := { f := Function.const α default, ne := const_ne }

instance [OFE α] [OFE β] : OFE (α -c> β) where
  Dist n f g := Dist n f.toHom g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := ContractiveHom.ext_iff.trans eq_dist
  dist_lt := dist_lt

/-- Evaluate a dependent function at a specified argument. -/
def applyHom [OFEFun (β : α → _)] (x : α) : ((x : α) → β x) -n> β x where
  f f := f x
  ne.1 _ _ _ H := H x

/-- Evaluate a bundled non-expansive morphism at a specified argument. -/
def applyNe [OFE α] [OFE β] (x : α) : (α -n> β) -n> β where
  f f := f x
  ne.1 _ _ _ H := H x

instance [OFE α] [OFE β] : NonExpansive (applyNe (α := α) (β := β)) where
  ne _ _ _ H f := f.ne.1 H

/-- Apply a family of non-expansive maps pointwise to dependent functions. -/
def mapCodHom [OFEFun (β₁ : α → _)] [OFEFun β₂]
    (F : ∀ x, β₁ x -n> β₂ x) : ((x : α) → β₁ x) -n> ((x : α) → β₂ x) where
  f f x := F x (f x)
  ne.1 _ _ _ H x := (F x).ne.1 (H x)

theorem mapCodHom_id [OFEFun (β : α → _)] (g : (x : α) → β x) :
    mapCodHom (fun _ => Hom.id) g = g := rfl

theorem mapCodHom_compose [OFEFun (β₁ : α → _)] [OFEFun β₂] [OFEFun β₃]
    (f₁ : ∀ x, β₁ x -n> β₂ x) (f₂ : ∀ x, β₂ x -n> β₃ x) (g : (x : α) → β₁ x) :
  mapCodHom (fun x => (f₂ x).comp (f₁ x)) g = mapCodHom f₂ (mapCodHom f₁ g) := rfl

open Classical in
instance mapCod_lookup_discrete [OFEFun (β : α → _)]
    (f : (x : α) → β x) (x : α) [hf : DiscreteE f] : DiscreteE (f x) where
  discrete {y} h := by
    let g : (x' : α) → β x' := fun x' => if e : x = x' then e ▸ y else f x'
    have hgx : g x = y := dite_eq_left rfl
    have hne : ∀ x', x ≠ x' → g x' = f x' := fun x' e => dite_eq_right e
    refine (congrFun (hf.discrete fun x' => ?_) x).trans hgx
    by_cases e : x = x'
    · grind
    · exact .of_eq (hne x' e).symm

instance [OFE α] [OFE β] : OFE (α × β) where
  Dist n a b := a.1 ≡{n}≡ b.1 ∧ a.2 ≡{n}≡ b.2
  dist_eqv := {
    refl _ := ⟨dist_eqv.refl _, dist_eqv.refl _⟩
    symm h := ⟨dist_eqv.symm h.1, dist_eqv.symm h.2⟩
    trans h1 h2 := ⟨dist_eqv.trans h1.1 h2.1, dist_eqv.trans h1.2 h2.2⟩
  }
  eq_dist' {_ _} := by rw [Prod.ext_iff]; simp only [eq_dist, forall_and]
  dist_lt h1 h2 := ⟨dist_lt h1.1 h2, dist_lt h1.2 h2⟩

theorem dist_fst {n} [OFE α] [OFE β] {x y : α × β} (h : x ≡{n}≡ y) : x.fst ≡{n}≡ y.fst := h.left
theorem dist_snd {n} [OFE α] [OFE β] {x y : α × β} (h : x ≡{n}≡ y) : x.snd ≡{n}≡ y.snd := h.right

theorem dist_prod_ext {n} [OFE α] [OFE β] {x₁ x₂ : α} {y₁ y₂ : β}
    (ex : x₁ ≡{n}≡ x₂) (ey : y₁ ≡{n}≡ y₂) : (x₁, y₁) ≡{n}≡ (x₂, y₂) := ⟨ex, ey⟩

instance Prod.mk_ne [OFE α] [OFE β] : NonExpansive₂ (Prod.mk (α := α) (β := β)) where
  ne _ _ _ hx _ _ hy := dist_prod_ext hx hy

/-- Note: Not an instance, due to instance coherence problems. -/
theorem prod_mk_ne_left [OFE α] [OFE β] (b : β) : NonExpansive (β := α × β) (·, b) :=
  ⟨fun {_ _ _} h => dist_prod_ext h Dist.rfl⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem prod_mk_ne_right [OFE α] [OFE β] (a : α) : NonExpansive (β := α × β) (a, ·) :=
  ⟨fun {_ _ _} h => dist_prod_ext Dist.rfl h⟩

instance [OFE α] [OFE β] : NonExpansive (Prod.fst (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => dist_fst h⟩

instance [OFE α] [OFE β] : NonExpansive (Prod.snd (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => dist_snd h⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₂.uncurry [OFE α] [OFE β] [OFE γ] {f : α → β → γ} (hf : NonExpansive₂ f) :
    NonExpansive (Function.uncurry f) :=
  ⟨fun {_ _ _} (h : _ ∧ _) => hf.ne h.1 h.2⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive.curry [OFE α] [OFE β] [OFE γ] {f : α × β → γ} (hf : NonExpansive f) :
    NonExpansive₂ (Function.curry f) :=
  ⟨fun _ _ _ hx _ _ hy => hf.ne ⟨hx, hy⟩⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive.curry₃ [OFE α] [OFE β] [OFE γ] [OFE δ] {f : α × β × γ → δ}
    (hf : NonExpansive f) : NonExpansive₃ fun a b c => f (a, b, c) :=
  ⟨fun _ _ _ hx _ _ hy _ _ hz => hf.ne ⟨hx, hy, hz⟩⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₃.uncurry [OFE α] [OFE β] [OFE γ] [OFE δ] {f : α → β → γ → δ}
    (hf : NonExpansive₃ f) : NonExpansive fun p : α × β × γ => f p.1 p.2.1 p.2.2 :=
  ⟨fun {_ _ _} (h : _ ∧ _ ∧ _) => hf.ne h.1 h.2.1 h.2.2⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive.curry₄ [OFE α] [OFE β] [OFE γ] [OFE δ] [OFE ε] {f : α × β × γ × δ → ε}
    (hf : NonExpansive f) : NonExpansive₄ fun a b c d => f (a, b, c, d) :=
  ⟨fun _ _ _ hx _ _ hy _ _ hz _ _ hw => hf.ne ⟨hx, hy, hz, hw⟩⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₄.uncurry [OFE α] [OFE β] [OFE γ] [OFE δ] [OFE ε] {f : α → β → γ → δ → ε}
    (hf : NonExpansive₄ f) : NonExpansive fun p : α × β × γ × δ => f p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  ⟨fun {_ _ _} (h : _ ∧ _ ∧ _ ∧ _) => hf.ne h.1 h.2.1 h.2.2.1 h.2.2.2⟩

instance prod.is_discrete [OFE α] [OFE β] {a : α} {b : β} [DiscreteE a] [DiscreteE b] :
    DiscreteE (a, b) := by
  constructor
  intro y H; exact Prod.ext (DiscreteE.discrete H.1) (DiscreteE.discrete H.2)

instance instDiscreteProd [OFE α] [OFE β] [Discrete α] [Discrete β] : Discrete (α × β) where
  discrete_0 H := Prod.ext (discrete_0 H.1) (discrete_0 H.2)

section sum

variable [OFE α] [OFE β]

instance : OFE (α ⊕ β) where
  Dist n
    | .inl a, .inl b => a ≡{n}≡ b
    | .inr a, .inr b => a ≡{n}≡ b
    | _, _ => False
  dist_eqv := {
    refl
    | .inl _ => dist_eqv.refl _
    | .inr _ => dist_eqv.refl _
    symm {a b} h := match a, b with
    | .inl _, .inl _ => h.symm
    | .inr _, .inr _ => h.symm
    | .inr _, .inl _ => h
    | .inl _, .inr _ => h
    trans {a b c} h1 h2 := match a, b, c with
    | .inl _, .inl _, .inl _ => h1.trans h2
    | .inr _, .inr _, .inr _ => h1.trans h2
    | .inr _, .inl _, _ => h1.elim
    | .inl _, .inr _, _ => h1.elim
    | _, .inr _, .inl _ => h2.elim
  }
  eq_dist' {a b} := by
    match a, b with
    | .inl _, .inl _ => rw [Sum.inl.injEq]; exact eq_dist
    | .inr _, .inr _ => rw [Sum.inr.injEq]; exact eq_dist
    | .inl _, .inr _ => exact ⟨fun h => (nomatch h), fun x => (x 0).elim⟩
    | .inr _, .inl _ => exact ⟨fun h => (nomatch h), fun x => (x 0).elim⟩
  dist_lt {_ a b} := match a, b with
    | .inl _, .inl _ => dist_lt
    | .inr _, .inr _ => dist_lt
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

theorem dist_inl (h : x ≡{n}≡ y) : (.inl x : α ⊕ β) ≡{n}≡ .inl y := h
theorem dist_inr {x y : β} (h : x ≡{n}≡ y) : (.inr x : α ⊕ β) ≡{n}≡ .inr y := h

theorem dist_ext_left {x y : α} (h : (.inl x : α ⊕ β) ≡{n}≡ .inl y) : x ≡{n}≡ y := h

theorem dist_ext_right {x y : β} (h : (.inr x : α ⊕ β) ≡{n}≡ .inr y) : x ≡{n}≡ y := h

instance instNonExpansiveInl : NonExpansive (Sum.inl (α := α) (β := β)) where
  ne {_ _ _} H := dist_inl H

instance instNonExpansiveInr : NonExpansive (Sum.inr (α := α) (β := β)) where
  ne {_ _ _} H := dist_inr H

instance instNonExpansiveElim [OFE γ] {f₁ : α → γ} {f₂ : β → γ} [NonExpansive f₁] [NonExpansive
    f₂] :
    NonExpansive (Sum.elim f₁ f₂) where
  ne {_ x y} := match x, y with
    | .inl _, .inl _ => (NonExpansive.ne (f := f₁) <| dist_ext_left ·)
    | .inr _, .inr _ => (NonExpansive.ne (f := f₂) <| dist_ext_right ·)
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

theorem discreteE_inl {a : α} (Ha : DiscreteE a) : DiscreteE (.inl a : α ⊕ β) := by
  constructor
  rintro (_|_) H
  · exact congrArg Sum.inl (Ha.discrete H)
  · exact H.elim

theorem discreteE_inr {a : β} (Ha : DiscreteE a) : DiscreteE (.inr a : α ⊕ β) := by
  constructor
  rintro (_|_) H
  · exact H.elim
  · exact congrArg Sum.inr (Ha.discrete H)

instance instDiscreteSum [Discrete α] [Discrete β] : Discrete (α ⊕ β) where
  discrete_0 {x y} := match x, y with
    | .inl _, .inl _ => (congrArg Sum.inl <| discrete_0 (α := α) <| dist_ext_left ·)
    | .inr _, .inr _ => (congrArg Sum.inr <| discrete_0 (α := β) <| dist_ext_right ·)
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

end sum

instance [OFE α] (P : α → Prop) : OFE (Subtype P) where
  Dist n x y := x.val ≡{n}≡ y.val
  dist_eqv := ⟨fun _ => .rfl, Dist.symm, Dist.trans⟩
  eq_dist' {_ _} := Subtype.ext_iff.trans eq_dist
  dist_lt := dist_lt

instance [OFE α] (P : α → Prop) (x : Subtype P) [DiscreteE x.val] : DiscreteE x where
  discrete h := Subtype.ext (DiscreteE.discrete h)

instance [OFE α] [Discrete α] (P : α → Prop) : Discrete (Subtype P) where
  discrete_0 h := Subtype.ext (Discrete.discrete_0 (α := α) h)

theorem exist_ne [OFE α] {P : α → Prop} {n} {a1 a2 : α} (H1 : P a1) (H2 : P a2)
    (h : a1 ≡{n}≡ a2) : (⟨a1, H1⟩ : Subtype P) ≡{n}≡ ⟨a2, H2⟩ := h

instance [OFE α] (P : α → Prop) : NonExpansive (Subtype.val : Subtype P → α) where
  ne {_ _ _} := id

instance Hom.ofSubtype_ne [OFE α] [OFE β] : NonExpansive (Hom.ofSubtype (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => h⟩

/-- Extract the underlying subtype from a `Hom`. -/
def Hom.toSubtype [OFE α] [OFE β] (f : α -n> β) : { f : α → β // NonExpansive f } :=
  ⟨f.f, f.ne⟩

instance Hom.toSubtype_ne [OFE α] [OFE β] : NonExpansive (Hom.toSubtype (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => h⟩

instance instOFESigma (P : α → Type _) [∀ x, OFE (P x)] : OFE (Sigma P) where
  Dist n x y := ∃ heq : x.fst = y.fst, heq ▸ x.snd ≡{n}≡ y.snd
  dist_eqv := {
    refl _ := ⟨rfl, .rfl⟩
    symm {x y} := match x, y with
      | ⟨x, xH⟩, ⟨y, yH⟩ => fun
        | ⟨heq, H⟩ => ⟨heq.symm, by simp only at heq; subst heq; exact H.symm⟩
    trans {x y z} := match x, y, z with
      | ⟨x, xH⟩, ⟨y, yH⟩, ⟨z, zH⟩ => fun
        | ⟨heq, H⟩, ⟨heq', H'⟩ =>
          ⟨heq.trans heq', by simp only at heq heq'; subst heq; subst heq'; exact H.trans H'⟩
  }
  eq_dist' {x y} := by
    refine ⟨fun h n => h ▸ ⟨rfl, .rfl⟩, fun h => ?_⟩
    obtain ⟨heq, _⟩ := h 0
    obtain ⟨xf, xs⟩ := x; obtain ⟨yf, ys⟩ := y
    simp only at heq; subst heq
    exact congrArg _ (eq_dist_2 fun n => (h n).2)
  dist_lt {_ x y} := match x, y with
    | ⟨x, xH⟩, ⟨y, yH⟩ => fun
      | ⟨heq, H⟩ => fun hlt => ⟨heq, by simp only at heq; subst heq; exact dist_lt H hlt⟩

instance instDiscreteESigma {P : α → Type _} [∀ x, OFE (P x)] {x : Sigma P} [inst : DiscreteE
    x.snd] :
    DiscreteE x where
  discrete {y} := by
    rcases x, y with ⟨⟨x, xH⟩, ⟨y, yH⟩⟩; rintro ⟨heq, H⟩
    simp only at heq; subst heq
    exact congrArg _ (inst.discrete H)

instance instDiscreteSigma {P : α → Type _} [∀ x, OFE (P x)] [∀ x, Discrete (P x)] :
    Discrete (Sigma P) where
  discrete_0 {x y} H := match x, y, H with
    | ⟨x, xH⟩, ⟨y, yH⟩, ⟨heq, H⟩ => by simp only at heq; subst heq; exact congrArg _ (discrete_0 H)

theorem Sigma.dist_eq {P : α → Type _} [∀ x, OFE (P x)] {n} {x1 x2 : Sigma P} :
    (x1 ≡{n}≡ x2) ↔ ∃ heq : x1.fst = x2.fst, heq ▸ x1.snd ≡{n}≡ x2.snd := Iff.rfl

instance Sigma.fst_ne {P : α → Type _} [OFE α] [∀ x, OFE (P x)] :
    NonExpansive (Sigma.fst : Sigma P → α) where
  ne {_ _ _} h := Dist.of_eq h.1

/-- The first components of `n`-equivalent dependent pairs are equal.

Split out of `Sigma.dist_snd` so that the projection happens in a body rather than in a statement:
in a statement the `OFE (Sigma P)` instance argument is still an unsolved metavariable, so `h`'s
type cannot be reduced to the `∃ heq, ..` of `instOFESigma` to project out of. -/
theorem Sigma.dist_fst {P : α → Type _} [∀ x, OFE (P x)] {n} {x y : Sigma P}
    (h : x ≡{n}≡ y) : x.fst = y.fst := h.1

theorem Sigma.dist_snd {P : α → Type _} [∀ x, OFE (P x)] {n} {x y : Sigma P}
    (h : x ≡{n}≡ y) : Sigma.dist_fst h ▸ x.snd ≡{n}≡ y.snd := h.2

theorem Sigma.mk_dist {P : α → Type _} [∀ x, OFE (P x)] {n} {i1 i2 : α} {v1 : P i1} {v2 : P i2}
    (heq : i1 = i2) (h : heq ▸ v1 ≡{n}≡ v2) : Sigma.mk i1 v1 ≡{n}≡ Sigma.mk i2 v2 :=
  ⟨heq, h⟩

instance Sigma.mk_ne {P : α → Type _} [∀ x, OFE (P x)] (a : α) :
    NonExpansive (Sigma.mk a : P a → Sigma P) where
  ne {_ _ _} h := ⟨rfl, h⟩

/-- An isomorphism between two OFEs is a pair of morphisms whose composition is equivalent to the
identity morphism. -/
@[ext] structure Iso (α β : Type _) [OFE α] [OFE β] where
  /-- The forward non-expansive map of an isomorphism. -/
  hom : α -n> β
  /-- The inverse non-expansive map of an isomorphism. -/
  inv : β -n> α
  hom_inv : hom (inv x) = x
  inv_hom : inv (hom x) = x

attribute [simp] Iso.hom_inv Iso.inv_hom

instance [OFE α] [OFE β] : CoeFun (Iso α β) (fun _ => α -n> β) := ⟨Iso.hom⟩
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.hom := iso.hom.ne
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.inv := iso.inv.ne

theorem Iso.hom_inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.hom (iso.inv x) ≡{n}≡ x :=
  (Iso.hom_inv iso).dist

theorem Iso.inv_hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.inv (iso.hom x) ≡{n}≡ x :=
  (Iso.inv_hom iso).dist

/-- OFE isomorphisms preserve equivalence. -/
theorem Iso.hom_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x = y ↔ iso.hom x = iso.hom y :=
  ⟨fun h => h ▸ rfl,
   fun h => iso.inv_hom.symm.trans ((congrArg iso.inv h).trans iso.inv_hom)⟩

/-- The inverse of an OFE isomorphism preserves equivalence. -/
theorem Iso.inv_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x = y ↔ iso.inv x = iso.inv y :=
  ⟨fun h => h ▸ rfl,
   fun h => iso.hom_inv.symm.trans ((congrArg iso.hom h).trans iso.hom_inv)⟩

/-- OFE isomorphisms preserve `n`-equivalence. -/
theorem Iso.hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.hom x ≡{n}≡ iso.hom y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.inv_hom_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.inv_hom_dist)⟩

/-- The inverse of an OFE isomorphism preserves `n`-equivalence. -/
theorem Iso.inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.inv x ≡{n}≡ iso.inv y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.hom_inv_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.hom_inv_dist)⟩

/-- The identity OFE isomorphism -/
def Iso.id [OFE α] : Iso α α where
  hom := Hom.id
  inv := Hom.id
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

@[simp] theorem Iso.id_apply [OFE α] {x} : ((Iso.id : Iso α α) : α -n> α) x = x := rfl

/-- The inverse of an OFE isomorphism -/
def Iso.symm [OFE α] [OFE β] (iso : Iso α β) : Iso β α where
  hom := iso.inv
  inv := iso.hom
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

/-- Composition of OFE isomorphisms -/
def Iso.comp [OFE α] [OFE β] [OFE γ] (iso1 : Iso β γ) (iso2 : Iso α β) : Iso α γ where
  hom := iso1.hom.comp iso2.hom
  inv := iso2.inv.comp iso1.inv
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

end OFE

/-- A chain in an OFE is a `Nat`-indexed sequence of elements that is upward-closed in terms of
`n`-equivalence. -/
structure Chain (α : Type _) [OFE α] where
  /-- The approximation at each natural-number index. -/
  chain : Nat → α
  cauchy : n ≤ i → chain i ≡{n}≡ chain n

instance [OFE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.chain⟩

namespace Chain

/-- The constant chain. -/
def const [OFE α] (a : α) : Chain α where
  chain := fun _ => a
  cauchy _ := OFE.Dist.rfl

@[simp] theorem const_apply [OFE α] {a : α} {n} : const a n = a := rfl

/-- Mapping a chain through a non-expansive function. -/
def map [OFE α] [OFE β] (f : α -n> β) (c : Chain α) : Chain β where
  chain n := f (c n)
  cauchy h := f.ne.1 (c.cauchy h)

@[simp] theorem map_apply [OFE α] [OFE β] {f : α -n> β} {c : Chain α} {n} :
    map f c n = f (c n) := rfl

@[simp] theorem map_id [OFE α] {c : Chain α} : map (Hom.id : α -n> α) c = c := by
  simp [map]

theorem map_comp [OFE α] [OFE β] [OFE γ] {f : α -n> β} {g : β -n> γ} {c : Chain α} :
    map (g.comp f) c = map g (map f c) := by
  simp [map]

/-- If a chain of Option is ever none, is the constant none chain. -/
theorem chain_none_const [OFE V] {c : Chain (Option V)} (H : c n = none) :
    c = Chain.const none := by
  rcases c with ⟨c, Hc⟩
  congr 1; refine funext (fun k => ?_)
  rcases Nat.le_or_ge n k with (Hnk|Hnk)
  · suffices c k ≡{n}≡ c n by cases _ : c k <;> simp_all
    exact Hc Hnk
  · suffices c k ≡{k}≡ c n by cases _ : c k <;> simp_all
    exact (Hc Hnk).symm

/-- If a chain of Option is ever some, it is the lift a chain by some. -/
theorem chain_option_some [OFE V] {c : Chain (Option V)} (H : c n = some v) :
    ∃ c' : Chain V, c = Chain.map ⟨some, OFE.Option.some.ne⟩ c' := by
  have HVc (k) : ∃ v', c k = some v' := by
    rcases h : c.chain k with (_|v')
    · simp [chain_none_const h] at H
    · exists v'
  let c' : Chain V :=
    ⟨fun n => Classical.choose <| HVc n,
     by
       intro n i Hni
       have HR := c.cauchy Hni
       rw [Classical.choose_spec (HVc n), Classical.choose_spec (HVc i)] at HR
       exact HR ⟩
  exists c'
  rcases hcc : c with ⟨cc, Hcc⟩
  simp only [Chain.map, Chain.mk.injEq]
  refine funext (fun i => ?_)
  simp only [c']
  have Hchoose := Classical.choose_spec (HVc i)
  rw [← Hchoose]
  simp [hcc]

end Chain

/-- Complete ordered family of equivalences -/
class IsCOFE (α : Type _) [OFE α] where
  /-- Complete a Cauchy chain in the ordered equivalence space. -/
  compl : Chain α → α
  conv_compl {c : Chain α} : compl c ≡{n}≡ c n

/-- Complete ordered family of equivalences -/
class COFE (α : Type _) extends OFE α, IsCOFE α

instance [OFE α] [IsCOFE α] : COFE α := {}

namespace COFE
export IsCOFE (compl conv_compl)

theorem conv_compl' [COFE α] {c : Chain α} {n i} (h : n ≤ i) : compl c ≡{n}≡ c i :=
  conv_compl.trans (c.cauchy h).symm

/-- Chain maps commute with completion. -/
theorem compl_map [COFE α] [COFE β] (f : α -n> β) (c : Chain α) :
    compl (Chain.map f c) = f (compl c) := by
  refine OFE.eq_dist_2 (fun n => ?_)
  exact Dist.trans conv_compl (NonExpansive.ne (Dist.symm conv_compl))

/-- Constant chains complete to their constant value -/
@[simp]
theorem compl_const [COFE α] (a : α) : compl (Chain.const a) = a :=
  OFE.eq_dist_2 (fun _ => conv_compl)

/-- Completion of discrete COFEs is the constant value. -/
@[simp] theorem discrete_cofe_compl [COFE α] [OFE.Discrete α] (c : Chain α) : compl c = c 0 :=
  Discrete.discrete_0 conv_compl

/-- The discrete COFE obtained from an equality relation `Eq` -/
@[reducible]
def ofDiscrete (α : Type _) : COFE α :=
  letI : OFE α := OFE.ofDiscrete α
  {
    compl := fun c => c 0
    conv_compl := fun {n c} => (c.cauchy (Nat.zero_le n)).symm
  }

instance [COFE α] : COFE (ULift α) where
  compl c := ⟨compl (c.map uliftDownHom)⟩
  conv_compl := conv_compl

instance : Discrete Unit where
  discrete_0 _ := Subsingleton.elim _ _

instance : COFE Unit where
  compl _ := ()
  conv_compl := ⟨⟩

instance : Discrete Empty where
  discrete_0 {x} _ := x.elim

instance : COFE Empty where
  compl c := (c 0).elim
  conv_compl {_ c} := (c 0).elim

/-- Pointwise completeness of a family of ordered equivalence spaces. -/
abbrev IsCOFEFun {α : Type _} (β : α → Type _) [OFEFun β] := ∀ x : α, IsCOFE (β x)

instance {α : Type _} (β : α → Type _) [∀ x, COFE (β x)] : COFE ((x : α) → β x) where
  compl c x := compl (c.map (applyHom x))
  conv_compl _ := IsCOFE.conv_compl

instance instIsCOFEHom [OFE α] [OFE β] [IsCOFE β] : IsCOFE (α -n> β) where
  compl c := by
    refine ⟨(compl <| c.map <| applyNe ·), ⟨fun n _ _ H => ?_⟩⟩
    refine conv_compl.trans (.trans ?_ conv_compl.symm)
    exact NonExpansive.ne (f := c.chain n) H
  conv_compl _ := IsCOFE.conv_compl

instance instIsCOFEProd [OFE α] [OFE β] [IsCOFE α] [IsCOFE β] : IsCOFE (α × β) where
  compl c := ⟨compl (c.map ⟨Prod.fst, inferInstance⟩), compl (c.map ⟨Prod.snd, inferInstance⟩)⟩
  conv_compl := ⟨conv_compl, conv_compl⟩

instance instIsCOFESum [OFE α] [OFE β] [IsCOFE α] [IsCOFE β] : IsCOFE (α ⊕ β) where
  compl c := match c 0 with
    | .inl seed => .inl (compl (c.map ⟨Sum.elim id (Function.const _ seed), inferInstance⟩))
    | .inr seed => .inr (compl (c.map ⟨Sum.elim (Function.const _ seed) id, inferInstance⟩))
  conv_compl {n c} := by
    cases h1 : c.chain 0 with
    | inl seed =>
      refine (dist_inl conv_compl).trans ?_
      dsimp only [Chain.map_apply]
      cases h2 : c.chain n with
      | inl _ => simp
      | inr _ => exact (h1 ▸ h2 ▸ c.cauchy (by omega : 0 ≤ n)).elim
    | inr seed =>
      refine (dist_inr conv_compl).trans ?_
      dsimp only [Chain.map_apply]
      cases h2 : c.chain n with
      | inl _ => exact (h1 ▸ h2 ▸ c.cauchy (by omega : 0 ≤ n)).elim
      | inr _ => simp

theorem Sigma.chain_const_proj1 {P : α → Type _} [∀ x, OFE (P x)]
  (c : Chain (Sigma P)) n : (c n).fst = (c 0).fst := (c.cauchy (by omega : 0 ≤ n)).choose

/-- Transport a dependent-pair chain into the fiber of its constant first component. -/
def Sigma.chainMapSnd {P : α → Type _} [∀ x, OFE (P x)] (c : Chain (Sigma P)) :
    Chain (P (c 0).fst) where
  chain n := Sigma.chain_const_proj1 c n ▸ (c n).snd
  cauchy {n i} hle := by
    obtain ⟨heq, hequiv⟩ := c.cauchy hle
    clear hle
    rw [show Sigma.chain_const_proj1 c i = heq.trans (Sigma.chain_const_proj1 c n) by rfl]
    generalize Sigma.chain_const_proj1 c n = heq'
    revert heq' hequiv heq; cases c.chain i; cases c.chain n
    rintro ⟨⟩ hequiv ⟨⟩
    exact hequiv

instance {P : α → Type _} [∀ x, OFE (P x)] [∀ x, IsCOFE (P x)] : IsCOFE (Sigma P) where
  compl c := ⟨(c 0).fst, compl (Sigma.chainMapSnd c)⟩
  conv_compl {n c} := by
    refine ⟨(Sigma.chain_const_proj1 c n).symm, ?_⟩
    have hequiv := conv_compl (c := Sigma.chainMapSnd c) (n := n)
    revert hequiv
    dsimp only [Sigma.chainMapSnd]
    generalize Sigma.chain_const_proj1 c n = heq
    revert heq; cases c.chain n
    rintro ⟨⟩ hequiv
    exact hequiv

/-- A mixed-variance family of ordered equivalence spaces with a non-expansive action. -/
class OFunctor (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) where
  ofe [COFE α] [COFE β] : OFE (F α β)
  /-- The contravariant and covariant action on non-expansive maps. -/
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

/-- A mixed-variance space functor whose action on morphisms is contractive. -/
class OFunctorContractive (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type
    _)) extends OFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] OFunctor.ofe

end COFE

/-- A type equipped with equality as its step-indexed equivalence. -/
@[ext] structure DiscreteO (α : Type _) where
  /-- The underlying element of a discrete ordered equivalence space. -/
  car : α

section DiscreteO
instance : COFE (DiscreteO α) := COFE.ofDiscrete _
instance {α : Type _} : OFE.Discrete (DiscreteO α) := ⟨fun h => h⟩

theorem DiscreteO.eqv_inj {x y : α} (H : DiscreteO.mk x = DiscreteO.mk y) : x = y :=
  congrArg DiscreteO.car H

theorem DiscreteO.dist_inj {x y : α} {n} (H : DiscreteO.mk x ≡{n}≡ DiscreteO.mk y) : x = y :=
  DiscreteO.eqv_inj <| discrete H

end DiscreteO

section ComposeOF
open COFE

/-- The composition of two functors, `F₁` applied to `F₂`. -/
abbrev ComposeOF (F₁ F₂ : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))
    [OFunctor F₂]
    [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)] : (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
        [Iris.COFE β] → Type _) :=
  fun α β _ _ => F₁ (F₂ β α) (F₂ α β)

theorem COFE.OFunctor.map_id_eq {F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] →
    Type _)} [OFunctor F] [COFE α] [COFE β] :
    OFunctor.map (F := F) (Hom.id (α := α)) (Hom.id (α := β)) = Hom.id :=
  Hom.ext (funext fun y => OFunctor.map_id y)

theorem COFE.OFunctor.map_comp_eq {F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β]
    → Type _)} [OFunctor F]
    [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) :
    OFunctor.map (F := F) (f.comp g) (g'.comp f') =
      (OFunctor.map g g').comp (OFunctor.map f f') :=
  Hom.ext (funext fun y => OFunctor.map_comp f g f' g' y)

theorem COFE.OFunctorContractive.map_distLater {F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
    [Iris.COFE β] → Type _)} [OFunctorContractive F]
    [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] {n} {f₁ f₂ : α₂ -n> α₁} {g₁ g₂ : β₁ -n> β₂}
    (hf : DistLater n f₁ f₂) (hg : DistLater n g₁ g₂) (x : F α₁ β₁) :
    OFunctor.map f₁ g₁ x ≡{n}≡ OFunctor.map f₂ g₂ x :=
  map_contractive.1 (x := (f₁, g₁)) (y := (f₂, g₂)) (fun m hm => ⟨hf m hm, hg m hm⟩) x

variable {F₁ F₂ : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)} [OFunctor
    F₂] [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)]

open OFunctor in
instance oFunctorComposeOF [OFunctor F₁] : OFunctor (ComposeOF F₁ F₂) where
  ofe := _
  map f g := map (F := F₁) (map (F := F₂) g f) (map (F := F₂) f g)
  map_ne.ne _ _ _ hf _ _ hg _ :=
    (map_ne (F := F₁)).ne (fun _ => (map_ne (F := F₂)).ne hg hf _)
      (fun _ => (map_ne (F := F₂)).ne hf hg _) _
  map_id _ := by
    simp only [map_id_eq]
    rfl
  map_comp _ _ _ _ _ := by
    simp only [map_comp_eq]
    rfl

open OFunctor OFunctorContractive in
instance oFunctorComposeOFContractiveLeft [OFunctorContractive F₁] :
    OFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    map_distLater (F := F₁)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).2 (h m hm).1 _)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).1 (h m hm).2 _) x⟩

end ComposeOF

section ComposeOFContractive
open COFE OFunctor OFunctorContractive

variable {F₁ F₂ : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)}
    [OFunctorContractive F₂]
  [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)]

instance oFunctorComposeOFContractiveRight [OFunctor F₁] :
    OFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    (map_ne (F := F₁)).ne
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _)
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) _) x⟩

end ComposeOFContractive

section DiscreteFunOF
open COFE

/-- The pointwise product of an indexed family of space functors. -/
abbrev DiscreteFunOF {C : Type _} (F : C → (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
    [Iris.COFE β] → Type _)) : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type
    _) :=
  fun A B _ _ => (c : C) → F c A B

instance oFunctorDiscreteFunOF {C} (F : C → (∀ (α : Type _) (β : Type _), [Iris.COFE α] →
    [Iris.COFE β] → Type _)) [∀ c, OFunctor (F c)] :
    OFunctor (DiscreteFunOF F) where
  ofe := _
  map f₁ f₂ := mapCodHom fun _ => OFunctor.map f₁ f₂
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := OFunctor.map_ne.ne Hx Hy ..
  map_id x := funext fun c => OFunctor.map_id (x c)
  map_comp f g f' g' x := funext fun c => OFunctor.map_comp f g f' g' (x c)

instance oFunctorDiscreteFunOFContractive {C} (F : C → (∀ (α : Type _) (β : Type _), [Iris.COFE
    α] → [Iris.COFE β] → Type _))
    [∀ c, OFunctorContractive (F c)] : OFunctorContractive (DiscreteFunOF F) where
  map_contractive.1 h _ _ := OFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunOF

section Option
variable [OFE α]

/-- Extract a chain of values from an optional chain, using a fallback for absence. -/
def optionChain (c : Chain (Option α)) (x : α) : Chain α := by
  refine ⟨fun n => (c n).getD x, fun {n i} H => ?_⟩
  have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [OFE.Dist, Option.Forall₂]

instance isCOFEOption [IsCOFE α] : IsCOFE (Option α) where
  compl c := (c 0).map fun x => IsCOFE.compl (optionChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    rcases c.chain 0 with _|x' <;> rcases e : c.chain n with _|y' <;> simp only [Dist,
        Option.Forall₂, Option.map_none, imp_self, Option.map_some]
    refine fun _ => OFE.dist_eqv.trans IsCOFE.conv_compl ?_
    simp [optionChain, e]

/-- Lift a non-expansive map to optional values. -/
def optionMap {α β : Type _} [OFE α] [OFE β] (f : α -n> β) : Option α -n> Option β := by
  refine ⟨Option.map f, ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all only [Dist, Option.Forall₂, Option.map_none, Option.map_some]
  exact f.ne.ne H

theorem Option.map_ne [OFE β] {f g : α → β} {x y : Option α} {n} :
    (∀ x y, x ≡{n}≡ y → f x ≡{n}≡ g y) → x ≡{n}≡ y → Option.map f x ≡{n}≡ Option.map g y := by
  intro hf hxy
  cases x with
  | none => cases y with
    | none => exact .rfl
    | some _ => exact hxy.elim
  | some a => cases y with
    | none => exact hxy.elim
    | some b => exact hf a b hxy

instance optionMap_ne [OFE β] : NonExpansive (optionMap (α := α) (β := β)) where
  ne _ f _ h o :=
    Option.map_ne (fun _ _ hab => dist_eqv.trans (f.ne.ne hab) (h _)) (dist_eqv.refl o)

theorem Option.bind_ne [OFE β] {f g : α → Option β} {x y : Option α} {n}
    (hf : ∀ x y, x ≡{n}≡ y → f x ≡{n}≡ g y) (hxy : x ≡{n}≡ y) : x.bind f ≡{n}≡ y.bind g := by
  cases x with
  | none => cases y with
    | none => exact .rfl
    | some _ => exact hxy.elim
  | some a => cases y with
    | none => exact hxy.elim
    | some b => exact hf a b hxy

theorem Option.join_ne {x y : Option (Option α)} {n} (hxy : x ≡{n}≡ y) : x.join ≡{n}≡ y.join := by
  cases x with
  | none => cases y with
    | none => exact .rfl
    | some _ => exact hxy.elim
  | some a => cases y with
    | none => exact hxy.elim
    | some b => exact hxy

theorem Option.elim_ne {β : Type _} (R : β → β → Prop) {f g : α → β} {d d' : β}
    {x y : Option α} {n} (hf : ∀ x y, x ≡{n}≡ y → R (f x) (g y)) (hd : R d d')
    (hxy : x ≡{n}≡ y) : R (x.elim d f) (y.elim d' g) := by
  cases x with
  | none => cases y with
    | none => exact hd
    | some _ => exact hxy.elim
  | some a => cases y with
    | none => exact hxy.elim
    | some b => exact hf a b hxy

end Option

section OptionOF
open COFE

/-- Lift a space functor to optional values. -/
abbrev OptionOF (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) : (∀
    (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _) :=
  fun A B _ _ => Option (F A B)

variable (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))

instance oFunctorOption [OFunctor F] : OFunctor (OptionOF F) where
  ofe := _
  map f g := optionMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy z := by
    cases z <;> simp only [Dist, Option.Forall₂, optionMap, Option.map_none, Option.map_some]
    exact OFunctor.map_ne.ne Hx Hy ..
  map_id z := by
    cases z with
    | none => rfl
    | some c => exact congrArg some (OFunctor.map_id c)
  map_comp f g f' g' z := by
    cases z with
    | none => rfl
    | some c => exact congrArg some (OFunctor.map_comp f g f' g' c)

instance [OFunctorContractive F] : OFunctorContractive (OptionOF F) where
  map_contractive.1 H z := by
    have := (OFunctorContractive.map_contractive (F := F)).distLater_dist H
    cases z <;> simp_all [optionMap, OFE.Dist, Option.Forall₂, Function.uncurry, OFunctor.map]

end OptionOF

section ProdOF

open COFE

variable [OFE A] [OFE A'] [OFE B] [OFE B']

instance instNonExpansiveProdMap (f : A → A') (g : B → B') [NonExpansive f] [NonExpansive g] :
    NonExpansive (Prod.map f g) where
  ne _ _ _ H := by
    constructor
    · rw [Prod.map_fst]
      exact NonExpansive.ne H.1
    · rw [Prod.map_snd]
      exact NonExpansive.ne H.2

omit [OFE A] [OFE A'] [OFE B] [OFE B'] in
theorem Prod.map_ext {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a = f' a)
    (Hg : ∀ a, g a = g' a) : Prod.map f g x = Prod.map f' g' x :=
  Prod.ext (Hf x.fst) (Hg x.snd)

omit [OFE A] [OFE B] in
theorem Prod.map_ne {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a ≡{n}≡ f' a)
    (Hg : ∀ a, g a ≡{n}≡ g' a) : Prod.map f g x ≡{n}≡ Prod.map f' g' x :=
  ⟨Hf x.fst, Hg x.snd⟩

/-- The product of two non-expansive maps. -/
def Prod.mapO (f : A -n> A') (g : B -n> B') : A × B -n> A' × B' where
  f := .map f g
  ne := inferInstance

instance Prod.mapO_ne : NonExpansive₂ (Prod.mapO (A := A) (A' := A') (B := B) (B' := B')) where
  ne _ _ _ Hf _ _ Hg _ := Prod.map_ne Hf Hg

/-- The pointwise product of two mixed-variance space functors. -/
abbrev ProdOF (F1 F2 : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) : (∀
    (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _) :=
  fun A B => (F1 A B) × (F2 A B)

open OFunctor in
instance instOFunctorProdOF [OFunctor F1] [OFunctor F2] : OFunctor (ProdOF F1 F2) where
  ofe := inferInstance
  map f g := Prod.mapO (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ := ⟨map_ne.ne Hx Hy _, map_ne.ne Hx Hy _⟩
  map_id _ := Prod.ext (map_id _) (map_id _)
  map_comp _ _ _ _ _ := Prod.ext (map_comp _ _ _ _ _) (map_comp _ _ _ _ _)

open OFunctorContractive in
instance instOFunctorContractiveProdOF [OFunctorContractive F1] [OFunctorContractive F2] :
    OFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
   Prod.map_ne (fun _ => map_contractive.1 H _) (fun _ => map_contractive.1 H _)

end ProdOF

section SumOF

open COFE

variable [OFE A] [OFE A'] [OFE B] [OFE B']

instance instNonExpansiveSumMap (f : A → A') (g : B → B') [NonExpansive f] [NonExpansive g] :
    NonExpansive (Sum.map f g) where
  ne _ x y H := match x, y with
    | .inl _, .inl _ => NonExpansive.ne (f := Sum.inl) (NonExpansive.ne (dist_ext_left H))
    | .inr _, .inr _ => NonExpansive.ne (f := Sum.inr) (NonExpansive.ne (dist_ext_right H))

omit [OFE A] [OFE A'] [OFE B] [OFE B'] in
theorem Sum.map_ext {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a = f' a)
    (Hg : ∀ a, g a = g' a) : Sum.map f g x = Sum.map f' g' x :=
    match x with
    | .inl _ => congrArg Sum.inl (Hf _)
    | .inr _ => congrArg Sum.inr (Hg _)

omit [OFE A] [OFE B] in
theorem Sum.map_ne {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a ≡{n}≡ f' a)
    (Hg : ∀ a, g a ≡{n}≡ g' a) : Sum.map f g x ≡{n}≡ Sum.map f' g' x :=
    match x with
    | .inl _ => dist_inl (Hf _)
    | .inr _ => dist_inr (Hg _)

/-- The sum of two non-expansive maps. -/
def Sum.mapO (f : A -n> A') (g : B -n> B') : A ⊕ B -n> A' ⊕ B' where
  f := .map f g
  ne := inferInstance

instance Sum.mapO_ne : NonExpansive₂ (Sum.mapO (A := A) (A' := A') (B := B) (B' := B')) where
  ne _ _ _ Hf _ _ Hg _ := Sum.map_ne Hf Hg

/-- The pointwise sum of two mixed-variance space functors. -/
abbrev SumOF (F1 F2 : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) : (∀
    (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _) := fun A B => (F1 A B) ⊕
    (F2 A B)

open OFunctor in
instance instOFunctorSumOF [OFunctor F1] [OFunctor F2] : OFunctor (SumOF F1 F2) where
  ofe := inferInstance
  map f g := Sum.mapO (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy x := match x with
    | .inl _ => dist_inl (map_ne.ne Hx Hy _)
    | .inr _ => dist_inr (map_ne.ne Hx Hy _)
  map_id x := match x with
    | .inl _ => congrArg Sum.inl (map_id _)
    | .inr _ => congrArg Sum.inr (map_id _)
  map_comp _ _ _ _ x := match x with
    | .inl _ => congrArg Sum.inl (map_comp _ _ _ _ _)
    | .inr _ => congrArg Sum.inr (map_comp _ _ _ _ _)

open OFunctorContractive in
instance instOFunctorContractiveSumOF [OFunctorContractive F1] [OFunctorContractive F2] :
    OFunctorContractive (SumOF F1 F2) where
  map_contractive.1 H _ :=
    Sum.map_ne (fun _ => map_contractive.1 H _) (fun _ => map_contractive.1 H _)

end SumOF

section SigmaOF

open COFE

/-- Map non-expansive fiber maps over dependent pairs. -/
def Sigma.mapO {P1 P2 : A → Type _} [∀ x, OFE (P1 x)] [∀ x, OFE (P2 x)] :
  ((a : A) → P1 a -n> P2 a) -n> Sigma P1 -n> Sigma P2 where
  f g := ⟨fun x => ⟨_, g x.fst x.snd⟩, ⟨by rintro n ⟨x, xH⟩ ⟨y, yH⟩ ⟨⟨⟩, hdist⟩; exact ⟨rfl, (g
      x).ne.ne hdist⟩⟩⟩
  ne := ⟨fun n f g hdist x => ⟨rfl, hdist _ _⟩⟩

open OFunctor in
/-- The dependent sum of an indexed family of space functors. -/
abbrev SigmaOF (F : A → (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) :
    (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _) :=
  fun B C => Sigma (fun (a : A) => (F a) B C)

open OFunctor in
instance instOFunctorSigmaOF {F : A → (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β]
    → Type _)} [∀ a, OFunctor (F a)] : OFunctor (SigmaOF F) where
  ofe := inferInstance
  map f g := Sigma.mapO (fun _ => map f g)
  map_ne.ne _ _ _ Hx _ _ Hy := NonExpansive.ne (fun _ => map_ne.ne Hx Hy)
  map_id x := by obtain ⟨a, v⟩ := x; exact congrArg (Sigma.mk a) (OFunctor.map_id v)
  map_comp f g f' g' x := by
    obtain ⟨a, v⟩ := x; exact congrArg (Sigma.mk a) (OFunctor.map_comp f g f' g' v)

open OFunctorContractive in
instance instOFunctorContractiveSigmaOF [∀ a, OFunctorContractive (F a)] :
    OFunctorContractive (SigmaOF F) where
  map_contractive.1 H := Sigma.mapO.ne.ne (fun _ => map_contractive.1 H)

end SigmaOF

section ConstantFunctor

open COFE

/-- The constant mixed-variance space family. -/
notation "constOF" =>
  (fun (B : Type _) (A : Type _) (C : Type _) [COFE A] [COFE C] => B)

instance oFunctorConstOF [OFE B] : OFunctor (constOF B) where
  ofe := _
  map _ _ := ⟨id, id_ne⟩
  map_ne := by intros; constructor; simp
  map_id := by simp
  map_comp := by simp

instance OFunctor.constOFContractive [OFE B] : OFunctorContractive (constOF B) where
  map_contractive.1 _ _ := .rfl

end ConstantFunctor

section IdentityFunctor

open COFE

/-- The space family selecting its covariant argument. -/
notation "IdOF" =>
  (fun (A : Type _) (B : Type _) [COFE A] [COFE B] => B)

open OFunctor in
instance : OFunctor IdOF where
  ofe := inferInstance
  map _ g := g
  map_ne.ne _ _ _ _ _ _ Hy := Hy
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

end IdentityFunctor

section HomOF

open COFE

variable [OFE A] [OFE A'] [OFE B] [OFE B']

/-- Precompose and postcompose a non-expansive map. -/
def Hom.map (pre : A' -n> A) (post : B -n> B') : (A -n> B) -n> (A' -n> B') where
  f h := post.comp (h.comp pre)
  ne.ne _ _ _ Hh := fun x => post.ne.ne (Hh (pre x))

instance instNonExpansive₂HomMap :
    NonExpansive₂ (Hom.map (A := A) (A' := A') (B := B) (B' := B')) where
  ne {_ _ _} Hx {y₁ _} Hy f g :=
    (NonExpansive.ne (f := y₁) (NonExpansive.ne (f := f) (Hx g))).trans (Hy _)

/-- The mixed-variance family of non-expansive maps between two space functors. -/
abbrev HomOF (F1 F2 : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))
    [OFunctor F1] [OFunctor F2] : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] →
    Type _) :=
  fun (A : Type _) (B : Type _) (_ : COFE A) (_ : COFE B) => @F1 B A _ _ -n> @F2 A B _ _

open OFunctor in
instance instOFunctorHomOF [OFunctor F1] [OFunctor F2] : OFunctor (HomOF F1 F2) where
  ofe := inferInstance
  map f g := Hom.map (map (F := F1) g f) (map (F := F2) f g)
  map_ne.ne _ _ _ Hf _ _ Hg := NonExpansive₂.ne (map_ne.ne Hg Hf) (map_ne.ne Hf Hg)
  map_id x := OFE.eq_dist_2 fun _ a => ((map_id _).trans (congrArg x.f (map_id a))).dist
  map_comp _ _ _ _ x := OFE.eq_dist_2 fun _ _ =>
    ((map_comp _ _ _ _ _).trans (congrArg _ (congrArg _ (congrArg x.f (map_comp _ _ _ _ _))))).dist

open OFunctorContractive in
instance instOFunctorContractiveHomOF [OFunctorContractive F1] [OFunctorContractive F2] :
    OFunctorContractive (HomOF F1 F2) where
  map_contractive.1 {n} ab ab' h := match ab, ab' with
    | ⟨a, b⟩, ⟨a', b'⟩ => by
      simp only [Function.uncurry_apply_pair, OFunctor.map]
      have h' : DistLater n (b, a) (b', a') :=
        fun m hm => ⟨(h m hm).right, (h m hm).left⟩
      refine NonExpansive₂.ne ?_ ?_
      · exact (map_contractive (F := F1)).1 h'
      · exact (map_contractive (F := F2)).1 h

end HomOF

section Fixpoint

/-- A predicate closed under completion of Cauchy approximation chains. -/
structure LimitPreserving [COFE α] (P : α → Prop) : Prop where
  compl : ∀ (c : Chain α), (∀ n, P (c n)) → P (COFE.compl c)

theorem LimitPreserving.const [COFE α] {P : Prop} : LimitPreserving fun (_ : α) => P where
  compl _ H := H 0

theorem LimitPreserving.discrete [COFE α] {P : α → Prop}
  (hdisc : ∀ {x y : α}, x ≡{0}≡ y → (P x → P y)) : LimitPreserving P where
  compl _ H := hdisc COFE.conv_compl.symm (H _)

theorem LimitPreserving.and [COFE α] {P Q : α → Prop} (HP : LimitPreserving P)
    (HQ : LimitPreserving Q) : LimitPreserving fun a => P a ∧ Q a where
  compl _ HPQ := ⟨HP.compl _ (fun n => (HPQ n).left), HQ.compl _ (fun n => (HPQ n).right)⟩

theorem LimitPreserving.forall [COFE α] (P : β → α → Prop) (Hlim : ∀ y, LimitPreserving (P y)) :
    LimitPreserving (∀ y, P y ·) where
  compl c H y := (Hlim y).compl c (H · y)

theorem LimitPreserving.impl [COFE α] (P1 P2 : α → Prop)
    (HP1 : ∀ {x y : α}, x ≡{0}≡ y → P1 x → P1 y)
    (Hcompl : LimitPreserving P2) :
    LimitPreserving (fun x => P1 x → P2 x) where
  compl _ Hc HP1c := Hcompl.compl _ <| fun n => Hc _ (HP1 (COFE.conv_compl' (Nat.zero_le n)) HP1c)

theorem LimitPreserving.impl' [COFE α] (P1 P2 : α → Prop)
    (HP1 : ∀ {x y : α}, x ≡{0}≡ y → (P1 x ↔ P1 y))
    (Hcompl : LimitPreserving P2) :
    LimitPreserving (fun x => P1 x → P2 x) :=
  LimitPreserving.impl P1 P2 (fun h => (HP1 h).mp) Hcompl

theorem LimitPreserving.equiv [COFE α] [OFE β] (f g : α -n> β) :
    LimitPreserving (fun x => f x = g x) where
  compl := by
    intro c Hfg
    refine eq_dist_2 fun n => ?_
    exact (f.ne.ne (COFE.conv_compl (c := c))).trans
      ((Hfg n).dist.trans (g.ne.ne COFE.conv_compl.symm))

theorem LimitPreserving.ext {α} [COFE α] {P Q : α -> Prop} (he : ∀ {x}, (P x ↔ Q x))
    (hp : LimitPreserving P) : LimitPreserving Q where
  compl _ := (he.1 <| hp.compl _ <| fun _ => he.2 <| · _)

/-- The Cauchy chain obtained by iterating a contractive endomorphism. -/
def Fixpoint.chain [OFE α] [Inhabited α] (f : α → α) [Contractive f] : Chain α where
  chain n := Nat.repeat f (n + 1) default
  cauchy {n} := by
    induction n with simp only [Nat.repeat, Nat.zero_le, Contractive.zero, imp_self, implies_true]
        | succ n IH
    rintro (_|i) <;> simp only [Nat.le_zero_eq, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false,
        false_implies, Nat.add_le_add_iff_right]
    intro H
    apply Contractive.distLater_dist
    intro _ Hm
    exact (IH H).le (Nat.le_of_lt_succ Hm)

/-- The chain construction of the Banach fixpoint. `fixpointP` packages it, together with
its unfolding equation, in an irreducible definition. -/
def fixpointAux [COFE α] [Inhabited α] (f : α → α) [Contractive f] : α :=
  COFE.compl <| Fixpoint.chain f

theorem fixpointAux_unfold [COFE α] [Inhabited α] (f : α -c> α) :
    fixpointAux f = f (fixpointAux f) := by
  refine eq_dist_2 fun n => ?_
  apply COFE.conv_compl.trans
  refine .trans ?_ (NonExpansive.ne COFE.conv_compl.symm)
  induction n with
  | zero => exact Contractive.zero f.f
  | succ _ IH => exact (Contractive.succ f.f IH.symm).symm

/-- The Banach fixed point together with its unfolding equation. Irreducibility keeps
elaboration from unfolding the approximation chain implicitly. -/
@[irreducible] def fixpointP [COFE α] [Inhabited α] (f : α → α) [Contractive f] : { x : α // x = f
    x } :=
  ⟨fixpointAux f, fixpointAux_unfold f.toContractiveHom⟩

/-- Fixpoints inside of a COFE -/
def fixpoint [COFE α] [Inhabited α] (f : α → α) [Contractive f] : α :=
  (fixpointP f).val

/-- The fixed point of a bundled contractive endomorphism. -/
nonrec abbrev OFE.ContractiveHom.fixpoint [COFE α] [Inhabited α] (f : α -c> α) : α := fixpoint f.f

theorem fixpoint_unfold [COFE α] [Inhabited α] (f : α -c> α) :
    fixpoint f = f (fixpoint f) :=
  (fixpointP f).property

theorem fixpoint_unique [COFE α] [Inhabited α] {f : α -c> α} {x : α} (H : x = f x) :
    x = fixpoint f := by
  refine eq_dist_2 fun n => ?_
  induction n with refine H.dist.trans <| .trans ?_ (fixpoint_unfold f).dist.symm
  | zero => exact Contractive.zero f.f
  | succ _ IH => exact Contractive.succ f.f IH

instance OFE.ContractiveHom.fixpoint_ne [COFE α] [Inhabited α] :
    NonExpansive (ContractiveHom.fixpoint (α := α)) where
  ne n f1 f2 H := by
    induction n with
      refine (fixpoint_unfold f1).dist.trans <|
        ((H _).trans ?_).trans (fixpoint_unfold f2).dist.symm
    | zero => exact Contractive.zero f2.f
    | succ _ IH => exact Contractive.succ f2.f <| IH <| Dist.lt H (Nat.lt_add_one _)

theorem fixpoint_dist [COFE α] [Inhabited α] {f g : α → α} [Contractive f] [Contractive g] {n}
    (H : ∀ z, f z ≡{n}≡ g z) : fixpoint f ≡{n}≡ fixpoint g :=
  (OFE.ContractiveHom.fixpoint_ne (α := α)).ne
    (x₁ := f.toContractiveHom) (x₂ := g.toContractiveHom) H

theorem fixpoint_proper [COFE α] [Inhabited α] {f g : α → α} [Contractive f] [Contractive g]
    (H : ∀ x, f x = g x) : fixpoint f = fixpoint g :=
  funext H ▸ rfl

@[elab_as_elim]
theorem OFE.ContractiveHom.fixpoint_ind [COFE α] [Inhabited α] (f : α -c> α)
    (P : α → Prop) (x : α) (Hbase : P x)
    (Hind : ∀ x, P x → P (f x)) (Hlim : LimitPreserving P) :
    P f.fixpoint := by
  let chain : Chain α := by
    refine ⟨fun i => Nat.repeat f (i + 1) x, fun {n i} H => ?_⟩
    induction n generalizing i with
    | zero => simp [Nat.repeat]
    | succ _ IH =>
      cases i <;> simp only [Nat.le_zero_eq, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false,
          Nat.add_le_add_iff_right] at H
      exact Contractive.succ _ <| IH H
  refine Eq.mp (congrArg P (fixpoint_unique (f := f) (x := COFE.compl chain) ?_)) ?_
  · refine eq_dist_2 fun n => ?_
    apply COFE.conv_compl.trans
    refine .trans ?_ (f.ne.ne COFE.conv_compl).symm
    induction n
    · exact Contractive.zero f.f
    · rename_i IH; apply Contractive.succ _ IH
  · apply Hlim.compl; intro n
    induction n with
    | zero => exact Hind (Nat.repeat f.f 0 x) Hbase
    | succ _ IH => apply Hind (Nat.repeat f.f _ x) IH

theorem repeat_dist [OFE α] (f g : α → α) [NonExpansive f] {n} (Hfg : ∀ z, f z ≡{n}≡ g z) :
    ∀ k z, Nat.repeat f k z ≡{n}≡ Nat.repeat g k z :=
  Nat.repeat_rel dist_eqv (fun h => NonExpansive.ne h) Hfg

/-- The fixed point obtained when a specified iterate is contractive. -/
def fixpointK [COFE α] [Inhabited α] (k : Nat) (f : α → α)
    [Contractive (Nat.repeat f k)] : α := fixpoint (Nat.repeat f k)

theorem fixpointK_unfold [COFE α] [Inhabited α] (k : Nat) (f : α → α)
    [Contractive (Nat.repeat f k)] : fixpointK k f = f (fixpointK k f) := by
  refine (fixpoint_unique (f := (Nat.repeat f k).toContractiveHom) ?_).symm
  change f (fixpointK k f) = Nat.repeat f k (f (fixpointK k f))
  refine ((Nat.repeat_apply_comm f k (fixpointK k f)).trans (congrArg f ?_)).symm
  exact (fixpoint_unfold (Nat.repeat f k).toContractiveHom).symm

theorem fixpointK_unique [COFE α] [Inhabited α] (k : Nat) (f : α → α)
    [Contractive (Nat.repeat f k)] {x : α} (H : x = f x) : x = fixpointK k f :=
  fixpoint_unique (f := (Nat.repeat f k).toContractiveHom) (Nat.repeat_fixed f H k)

theorem fixpointK_ne [COFE α] [Inhabited α] (k : Nat) (f g : α → α)
    [Contractive (Nat.repeat f k)] [Contractive (Nat.repeat g k)] [NonExpansive f] {n}
    (Hfg : ∀ z, f z ≡{n}≡ g z) : fixpointK k f ≡{n}≡ fixpointK k g :=
  fixpoint_dist (repeat_dist f g Hfg k)

theorem fixpointK_proper [COFE α] [Inhabited α] (k : Nat) (f g : α → α)
    [Contractive (Nat.repeat f k)] [Contractive (Nat.repeat g k)]
    (Hfg : ∀ z, f z = g z) : fixpointK k f = fixpointK k g :=
  funext Hfg ▸ rfl

@[elab_as_elim]
theorem fixpointK_ind [COFE α] [Inhabited α] (k : Nat) (f : α → α) [Contractive (Nat.repeat f k)]
    (P : α → Prop) (x : α) (Hbase : P x)
    (Hind : ∀ x, P x → P (f x)) (Hlim : LimitPreserving P) : P (fixpointK k f) :=
  OFE.ContractiveHom.fixpoint_ind (Nat.repeat f k).toContractiveHom P x Hbase
    (fun _ Hy => Nat.repeat_ind f Hind Hy k) Hlim

end Fixpoint

section FixpointAB

open OFE

instance [OFE α] [OFE β] [OFE γ] : CoeFun (α -c> β -n> γ) (fun _ => α → β → γ) := ⟨fun f x => (f.f
    x).f⟩
instance [OFE α] [OFE β] [OFE γ] : CoeFun (α -c> β -c> γ) (fun _ => α → β → γ) := ⟨fun f x => (f.f
    x).f⟩

/-- A Contractive function with NonExpansive function codomain is NonExpansive₂. -/
instance ne₂_of_contractive_ne [OFE α] [OFE β] [OFE γ] (fA : α -c> β -n> γ) : NonExpansive₂ fA where
  ne n x₁ x₂ Hx y₁ y₂ Hy := by
    refine .trans ?_ ((fA.f x₂).ne.ne Hy)
    apply fA.ne.ne Hx

/-- A Contractive function with Contractive function codomain is NonExpansive₂. -/
instance ne₂_of_contractive [OFE α] [OFE β] [OFE γ] (fB : α -c> β -c> γ) : NonExpansive₂ fB where
  ne n x₁ x₂ Hx y₁ y₂ Hy := by
    refine .trans ?_ ((fB.f x₂).ne.ne Hy)
    apply fB.ne.ne Hx

/-- The fixed point in the second variable for a given first argument. -/
def fixpointAB [OFE α] [COFE β] [Inhabited β] (fB : α -c> β -c> β) (x : α) : β := by
  let con_hom : β -c> β := {
    f := fB x,
    contractive := ⟨fB.f x |>.contractive.distLater_dist⟩
  }
  exact con_hom.fixpoint

theorem fixpointAB_contractive [OFE α] [COFE β] [Inhabited β] (fB : α -c> β -c> β) :
    Contractive (fixpointAB fB) where
  distLater_dist {n _ _} Dl := by
    apply ContractiveHom.fixpoint_ne.ne
    apply fB.contractive.distLater_dist
    exact Dl

/-- Substitute the second-variable fixed point into the first component. -/
def fixpointAA [OFE α] [COFE β] [Inhabited β] (fA : α -c> β -n> α)
    (fB : α -c> β -c> β) (x : α) : α :=
  fA x (fixpointAB fB x)

theorem fixpointAA_contractive [OFE α] [COFE β] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) : Contractive (fixpointAA fA fB) where
  distLater_dist {_ _ x₂} Dl := by
    refine .trans ?_ ((fA.f x₂).ne.ne ((fixpointAB_contractive fB).distLater_dist Dl))
    apply fA.contractive.distLater_dist
    exact Dl

/-- The first component of a simultaneous guarded fixed point. -/
def fixpointA [COFE α] [COFE β] [Inhabited α] [Inhabited β] (fA : α -c> β -n> α)
    (fB : α -c> β -c> β) : α := by
  let con_hom : α -c> α := {
    f := fixpointAA fA fB,
    contractive := ⟨(fixpointAA_contractive fA fB).distLater_dist⟩
  }
  exact con_hom.fixpoint

/-- The second component of a simultaneous guarded fixed point. -/
def fixpointB [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) : β :=
  fixpointAB fB <| fixpointA fA fB

theorem fixpointA_unfold [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) :
    fA (fixpointA fA fB) (fixpointB fA fB) = (fixpointA fA fB) := by
  exact .symm (fixpoint_unfold _)

theorem fixpointB_unfold [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) :
    fB (fixpointA fA fB) (fixpointB fA fB) = (fixpointB fA fB) := by
  exact .symm (fixpoint_unfold _)

theorem fixpointA_unique [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) (Hp : fA p q = p) (Hq : fB p q = q) :
    p = (fixpointA fA fB) :=
    fixpoint_unique <| Hp.symm.trans <| congrArg (fA p) (fixpoint_unique Hq.symm)

theorem fixpointB_unique [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) (Hp : fA p q = p) (Hq : fB p q = q) :
    q = (fixpointB fA fB) := by
  apply fixpoint_unique
  exact Hq.symm.trans (congrArg (fun z => fB z q) (fixpointA_unique fA fB Hp Hq))

instance fixpointA_ne [COFE α] [COFE β] [Inhabited α] [Inhabited β] :
    NonExpansive₂ (fixpointA (α := α) (β := β)) where
  ne n fA fA' HfA fB fB' HfB := by
    apply OFE.ContractiveHom.fixpoint_ne.ne
    intro z₁
    refine ((ne₂_of_contractive_ne fA).ne .rfl ?_).trans (HfA z₁ _)
    exact ContractiveHom.fixpoint_ne.ne (HfB z₁)

instance fixpointB_ne [COFE α] [COFE β] [Inhabited α] [Inhabited β] :
    NonExpansive₂ (fixpointB (α := α) (β := β)) where
  ne n fA fA' HfA fB fB' HfB := by
    apply ContractiveHom.fixpoint_ne.ne
    intro z₁
    refine ((ne₂_of_contractive fB).ne ?_ .rfl).trans (HfB _ z₁)
    exact fixpointA_ne.ne HfA HfB

theorem fixpointA_proper [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA fA' : α -c> β -n> α) (fB fB' : α -c> β -c> β)
    (HA : ∀ x y, fA x y = fA' x y) (HB : ∀ x y, fB x y = fB' x y) :
    fixpointA fA fB = fixpointA fA' fB' :=
  eq_dist.mpr fun _ => fixpointA_ne.ne (fun x y => (HA x y).dist) (fun x y => (HB x y).dist)

theorem fixpointB_proper [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA fA' : α -c> β -n> α) (fB fB' : α -c> β -c> β)
    (HA : ∀ x y, fA x y = fA' x y) (HB : ∀ x y, fB x y = fB' x y) :
    fixpointB fA fB = fixpointB fA' fB' :=
  eq_dist.mpr fun _ => fixpointB_ne.ne (fun x y => (HA x y).dist) (fun x y => (HB x y).dist)

end FixpointAB

section Later

/-- Delay equivalence by one step index. -/
structure Later (A : Type u) : Type u where
  next ::
  /-- The underlying value of a delayed equivalence space. -/
  car : A

instance isOFELater [OFE A] : OFE (Later A) where
  Dist n x y := DistLater n x.car y.car
  dist_eqv := ⟨fun _ => .rfl, .symm, .trans⟩
  eq_dist' {x y} := by
    obtain ⟨a⟩ := x; obtain ⟨b⟩ := y
    simp only [Later.next.injEq, eq_dist]
    exact ⟨fun H n => (H n).distLater, fun H n => (H (n+1)).dist_lt (Nat.lt_succ_self n)⟩
  dist_lt Hxy Hmn _ Hkm := Hxy _ (Nat.lt_trans Hkm Hmn)

instance NextContractive {A : Type _} [OFE A] : Contractive (@Later.next A) where
  distLater_dist := id

theorem Later.uninj {A : Type _} (x : Later A) : ∃ a, x = Later.next a := ⟨x.car, rfl⟩

theorem contractive_alt [OFE A] [OFE B] (f : A → B) :
    Contractive f ↔ ∃ g : Later A → B, NonExpansive g ∧ ∀ x, f x = g (Later.next x) := by
  refine ⟨fun hf => ⟨fun x => f x.car, ⟨fun _ _ _ h => hf.distLater_dist h⟩, fun _ => rfl⟩, ?_⟩
  rintro ⟨g, hg, hf⟩
  refine ⟨fun {n x y} h => ?_⟩
  rw [hf, hf]; exact hg.ne h

/-- Remove the delay from a chain by advancing every index. -/
def laterChain [OFE A] (c : Chain (Later A)) : Chain A where
  chain n := (c (Nat.succ n)).car
  cauchy Hle := c.cauchy (Nat.succ_le_succ Hle) _ (Nat.lt_succ_self _)

instance isCOFELater [OFE A] [IsCOFE A] : IsCOFE (Later A) where
  compl c := Later.next (IsCOFE.compl (laterChain c))
  conv_compl {n} c := by
    rcases n with _|n' <;> simp only [Dist, DistLater, Nat.not_lt_zero, false_implies, implies_true]
    intros m Hlt
    exact (IsCOFE.conv_compl (n := n') (c := laterChain c)).le (Nat.le_of_lt_succ Hlt)

/-- Lift a non-expansive map through the one-step delay. -/
def laterMap [OFE A] [OFE B] (f : A -n> B) : Later A -n> Later B := by
  refine ⟨fun x => Later.next (f x.car), ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H; simp_all only [OFE.Dist, DistLater]
  intros m Hlt; exact f.ne.ne (H m Hlt)

@[simp]
theorem laterMap_next [OFE A] [OFE B] (f : A -n> B) (x : A) :
    laterMap f (Later.next x) = Later.next (f x) := rfl

theorem laterMap_id [OFE A] (x : Later A) : laterMap Hom.id x = x := rfl

theorem laterMap_compose [OFE A] [OFE B] [OFE C] (f : A -n> B) (g : B -n> C) (x : Later A) :
    laterMap (g.comp f) x = laterMap g (laterMap f x) := rfl

theorem laterMap_ext [OFE A] [OFE B] {f g : A -n> B} (x : Later A) (h : ∀ a, f a = g a) :
    laterMap f x = laterMap g x := congrArg Later.next (h x.car)

instance laterMap_contractive [OFE A] [OFE B] :
    Contractive (laterMap : (A -n> B) → Later A -n> Later B) where
  distLater_dist H x m hm := H m hm x.car

end Later

section LaterOF
open COFE

/-- Apply one-step delay to a mixed-variance space functor. -/
abbrev LaterOF (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _)) : (∀ (α
    : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _) :=
  fun A B _ _ => Later (F A B)

variable (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))

instance instOFunctorLater [OFunctor F] : OFunctor (LaterOF F) where
  ofe := _
  map f g := laterMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := (OFunctor.map_ne.ne Hx Hy _).lt
  map_id x := congrArg Later.next (OFunctor.map_id x.car)
  map_comp f g f' g' x := congrArg Later.next (OFunctor.map_comp f g f' g' x.car)

instance instOFunctorContractiveLater [OFunctor F] : OFunctorContractive (LaterOF F) where
  map_contractive.1 H _ _ hlt :=
    OFunctor.map_ne.ne (DistLater.dist_lt H hlt).1 (DistLater.dist_lt H hlt).2 _

end LaterOF

section IsoCofe
open OFE COFE

variable {α β : Type _}

/-- Transport completeness through a map onto a completion-closed subtype. -/
@[reducible]
def isoCofeSubtype [COFE α] [OFE β] (P : α → Prop) (f : ∀ x, P x → β) (g : β -n> α)
    (g_dist : ∀ n (y1 y2 : β), y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x (Hx : P x), g (f x Hx) = x)
    (Hlimit : ∀ c : Chain β, P (COFE.compl (c.map g))) : IsCOFE β where
  compl c := f (COFE.compl (c.map g)) (Hlimit c)
  conv_compl {n c} := by
    refine (g_dist n _ _).mpr ?_
    rw [gf]; exact COFE.conv_compl

/-- Transport completeness using a limit-preserving predicate on the source. -/
@[reducible]
def isoCofeSubtype' [COFE α] [OFE β] (P : α → Prop) (f : ∀ x, P x → β) (g : β -n> α)
    (Pg : ∀ y, P (g y))
    (g_dist : ∀ n (y1 y2 : β), y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x (Hx : P x), g (f x Hx) = x) (Hlimit : LimitPreserving P) : IsCOFE β :=
  isoCofeSubtype P f g g_dist gf fun c => Hlimit.compl (c.map g) fun n => Pg (c n)

/-- Transport completeness along an isomorphism of ordered equivalence spaces. -/
@[reducible]
def isoCofe [COFE α] [OFE β] (f : α → β) (g : β -n> α)
    (g_dist : ∀ n (y1 y2 : β), y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x, g (f x) = x) : IsCOFE β :=
  isoCofeSubtype (fun _ => True) (fun x _ => f x) g g_dist (fun x _ => gf x) fun _ => trivial

/-- Completeness of a subtype defined by a limit-preserving predicate. -/
@[reducible]
def sigCofe [COFE α] {P : α → Prop} (H : LimitPreserving P) : IsCOFE (Subtype P) :=
  isoCofeSubtype' P (fun x h => ⟨x, h⟩) ⟨Subtype.val, inferInstance⟩ (fun y => y.property)
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) H

instance [OFE α] [OFE β] : OFE (Iso α β) where
  Dist n I1 I2 := I1.hom ≡{n}≡ I2.hom ∧ I1.inv ≡{n}≡ I2.inv
  dist_eqv := ⟨fun _ => ⟨.rfl, .rfl⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩,
    fun ⟨a1, a2⟩ ⟨b1, b2⟩ => ⟨a1.trans b1, a2.trans b2⟩⟩
  eq_dist' {_ _} := ⟨fun h _ => h ▸ ⟨.rfl, .rfl⟩,
    fun H => Iso.ext (eq_dist.mpr fun n => (H n).1) (eq_dist.mpr fun n => (H n).2)⟩
  dist_lt h hlt := ⟨h.1.lt hlt, h.2.lt hlt⟩

instance ofeIsoCofe [COFE α] [COFE β] : IsCOFE (Iso α β) := by
  refine isoCofeSubtype'
    (P := fun I : (α -n> β) × (β -n> α) => (∀ y, I.1 (I.2 y) = y) ∧ (∀ x, I.2 (I.1 x) = x))
    (fun I HI => ⟨I.1, I.2, fun {x} => HI.1 x, fun {x} => HI.2 x⟩)
    ⟨fun I => (I.hom, I.inv), ⟨fun _ _ _ h => h⟩⟩
    (fun I => ⟨fun _ => I.hom_inv, fun _ => I.inv_hom⟩)
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) ?_
  refine LimitPreserving.and ?_ ?_
  · refine LimitPreserving.forall _ fun y => ?_
    refine LimitPreserving.equiv
      ⟨fun I : (α -n> β) × (β -n> α) => I.1 (I.2 y), ⟨fun _ I I' h => ?_⟩⟩ (Hom.const y)
    exact (h.1 _).trans (I'.1.ne.ne (h.2 y))
  · refine LimitPreserving.forall _ fun x => ?_
    refine LimitPreserving.equiv
      ⟨fun I : (α -n> β) × (β -n> α) => I.2 (I.1 x), ⟨fun _ I I' h => ?_⟩⟩ (Hom.const x)
    exact (h.2 _).trans (I'.2.ne.ne (h.1 x))

/-- Lift an isomorphism through both arguments of a mixed-variance space functor. -/
def isoOfeCong (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))
    [OFunctor F] {A B : Type _} [COFE A] [COFE B] (I : Iso A B) :
    Iso (F A A) (F B B) where
  hom := OFunctor.map I.inv I.hom
  inv := OFunctor.map I.hom I.inv
  hom_inv {x} := by
    rw [← OFunctor.map_comp I.hom I.inv I.inv I.hom x,
      show I.hom.comp I.inv = Hom.id from Hom.ext (funext fun _ => I.hom_inv), OFunctor.map_id]
  inv_hom {x} := by
    rw [← OFunctor.map_comp I.inv I.hom I.hom I.inv x,
      show I.inv.comp I.hom = Hom.id from Hom.ext (funext fun _ => I.inv_hom), OFunctor.map_id]

instance isoOfeCong_ne (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] → Type _))
    [OFunctor F] {A B : Type _} [COFE A] [COFE B] :
    NonExpansive (isoOfeCong F (A := A) (B := B)) where
  ne _ _ _ h := ⟨OFunctor.map_ne.ne h.2 h.1, OFunctor.map_ne.ne h.1 h.2⟩

instance isoOfeCong_contractive (F : (∀ (α : Type _) (β : Type _), [Iris.COFE α] → [Iris.COFE β] →
    Type _)) [OFunctorContractive F] {A B : Type _}
    [COFE A] [COFE B] : Contractive (isoOfeCong F (A := A) (B := B)) where
  distLater_dist H :=
    ⟨fun x => OFunctorContractive.map_distLater (fun m hm => (H m hm).2) (fun m hm => (H m hm).1) x,
     fun x => OFunctorContractive.map_distLater (fun m hm => (H m hm).1) (fun m hm => (H m hm).2) x⟩

end IsoCofe

theorem OFE.cast_dist [Iα : OFE α] [Iβ : OFE β] {x y : α}
    (Ht : α = β) (HIt : Iα = Ht ▸ Iβ) (H : x ≡{n}≡ y) :
    (Ht ▸ x) ≡{n}≡ (Ht ▸ y) := by
  subst Ht; subst HIt; exact H

end Iris
