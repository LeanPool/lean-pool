/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Control.Rig
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Protocol.Focus
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transport.Table
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Protocol.Wired
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Packets

/-!
# Local profiles of a branch

The inventory protocol computes a local linear kernel in abstract
coordinates. Read its demand coordinates in the two exterior arrays
and its supply coordinates at their assigned physical sockets.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig

open Coloring Transport

variable {F : Type} [Field F] {m h : ℕ} (T : Routes F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h))

open scoped Classical in
/-- The value specified by `letI := T.action h σ T.params.balls (Site h)`. -/
abbrev arena :=
  letI := T.action h σ
  T.params.balls (Site h)

open scoped Classical in
/-- The value specified by `letI := T.action h σ s.clock.path (Site h)`. -/
abbrev Path :=
  letI := T.action h σ
  s.clock.path (Site h)

open scoped Classical in
/-- The value specified by `letI := T.action h σ s.widthAt u`. -/
abbrev requests (u : Path T s σ) : (arena T σ).Edge → ℕ :=
  letI := T.action h σ
  s.widthAt u

open scoped Classical in
/-- The value specified by `letI := T.action h σ s.clock.selector u`. -/
abbrev choose (u : Path T s σ) : Site h → B s.clock.bits :=
  letI := T.action h σ
  s.clock.selector u

open scoped Classical in
/-- Embeds `Protocol.End (requests T s σ u)` into `Port h s.p`. -/
abbrev place (u : Path T s σ) : Protocol.End (requests T s σ u) ↪ Port h s.p :=
  letI := T.action h σ
  s.endpoints u

open scoped Classical in
/-- The value specified by `(arena T σ).name e.1 e.2.val.1`. -/
abbrev src (e : (arena T σ).Edge) := (arena T σ).name e.1 e.2.val.1
open scoped Classical in
/-- The value specified by `(arena T σ).name e.1 e.2.val.2`. -/
abbrev dst (e : (arena T σ).Edge) := (arena T σ).name e.1 e.2.val.2

open scoped Classical in
/-- Uses `Protocol.Demand F σ s.clock.width` as the representation. -/
abbrev initial := Protocol.Demand F σ s.clock.width
open scoped Classical in
/-- The value specified by `Protocol.Links F (src T σ) (dst T σ) (requests T s σ u)`. -/
abbrev result (u : Path T s σ) := Protocol.Links F (src T σ) (dst T σ) (requests T s σ u)

open scoped Classical in
theorem target_at (i : Site h) :
    (arena T σ).name i ((arena T σ).shape i).dst = inflate h σ i := by
  let _ := T.action h σ
  change (market _ _ _ _ _).name i ((market _ _ _ _ _).shape i).dst = _
  rw [market_dst, inv_inv]
  exact T.target_action h σ i

open scoped Classical in
/-- The execute of type `let b` for the given inputs. -/
def execute {G J I : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [Fintype I] [Nonempty I] [MulAction G I] :
    let b := a.balls I
    (Protocol.Board.orders (Protocol.request b a.table)
      (Stock.copies (b.payload a.table) s.clock.width)).Expansion
      (fun u : s.clock.path I => Protocol.Board.orders (Protocol.edge F b) (s.widthAt u)) :=
  Protocol.program (a.balls I) a.offers
    (marketPorts (I := I) a.core a.radius a.unit g a.reach s.w s.hw)
    s.clock.height a.nz s.clock.room s.clock.μ a.path s.clock.width
    (a.ready I) a.local_supply (s.clock.runs I)

open scoped Classical in
/-- The indexed operation `(s.execute (I := Site h)).rename (Protocol.demandRename (a.balls
(Site h)) a.table σ s.clock.width hc) (fun _ => .refl _)`. -/
def transfer {G J : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [MulAction G (Site h)]
    (hc : ∀ i : Site h, (a.balls (Site h)).name i ((a.balls (Site h)).shape i).dst
      = inflate h σ i) :
    (Protocol.Demand F σ s.clock.width).Expansion
      (fun u : s.clock.path (Site h) =>
        Protocol.Board.orders (Protocol.edge F (a.balls (Site h))) (s.widthAt u)) :=
  (s.execute (I := Site h)).rename
    (Protocol.demandRename (a.balls (Site h)) a.table σ s.clock.width hc) (fun _ => .refl _)

open scoped Classical in
/-- The operator of type `(initial T s σ).Expansion (result T s σ)`, constructed using `T.action
h σ`. -/
def operator : (initial T s σ).Expansion (result T s σ) := by
  let _ := T.action h σ
  exact transfer σ s (target_at T σ)

open scoped Classical in
/-- Returns `.inr x.val.1.2` when `(x.val.2 : Bool) = true` holds, and `.inl x.val.1.2`
otherwise. -/
def side (i : Site h) (x : (initial T s σ).localPort i) : Fin s.clock.width ⊕ Fin s.clock.width :=
  if (x.val.2 : Bool) = true then .inr x.val.1.2 else .inl x.val.1.2

open scoped Classical in
/-- The value specified by `(place T s σ u x.val).2`. -/
def channel (u : Path T s σ) (i : Site h) (x : (result T s σ u).localPort i) : B s.p :=
  (place T s σ u x.val).2

open scoped Classical in
/-- The data for the example construction, including `h`, `σ`, `u`, `i`. -/
structure Example where
  /-- The `Example` field of type `ℕ`. -/
  h : ℕ
  /-- The `Example` component of type `Equiv.Perm (B h)`. -/
  σ : Equiv.Perm (B h)
  /-- The `Example` component of type `Path T s σ`. -/
  u : Path T s σ
  /-- The `Example` component of type `Site h`. -/
  i : Site h

open scoped Classical in
/-- The value specified by `((operator T s t.σ).kernel t.u t.i).pull (side T s t.σ t.i) (channel
T s t.σ t.u t.i)`. -/
def sample (t : Example T s) : Profile F s.p s.clock.width :=
  ((operator T s t.σ).kernel t.u t.i).pull (side T s t.σ t.i) (channel T s t.σ t.u t.i)

open scoped Classical in
/-- Uses `⟨@Root.mk _ _ _ (T.action t.h t.σ) t.i, choose T s t.σ t.u⟩` as the representation. -/
def observed (t : Example T s) : s.clock.Input :=
  ⟨@Root.mk _ _ _ (T.action t.h t.σ) t.i, choose T s t.σ t.u⟩

open scoped Classical in
/-- The compatible of type `Prop`, constructed using `observed T s x`. -/
def Compatible : Prop :=
  ∃ E : Finset (controllers F T.embed), ∀ x y : Example T s,
    let u := observed T s x
    let v := observed T s y
    Root.Agree E u.toRoot v.toRoot →
    (∀ i ∈ E, u.mark (u.label i) = v.mark (v.label i)) → sample T s x = sample T s y

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
end

/-
# The finite menu of local profiles

A profile can depend on the branch only through finitely many
observations. Record these observations, the local guard, and the
enable mask. A class with no representative receives weight zero.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig

open Coloring Transport

variable {F : Type} [Field F] {m : ℕ} (T : Routes F m) (s : Rig T.params)

open scoped Classical in
/-- The value specified by `(s.bank.program T.params.unit _ T.params.reach s.count x j).1`. -/
abbrev active (x : s.clock.Input) (j : B s.p) :=
  (s.bank.program T.params.unit _ T.params.reach s.count x j).1

open scoped Classical in
/-- The value specified by `(sample T s v).mask (s.clock.guard s.w (observed T s v)) (active T s
(observed T s v))`. -/
def masked (v : Example T s) : Profile F s.p s.clock.width :=
  (sample T s v).mask (s.clock.guard s.w (observed T s v)) (active T s (observed T s v))

open scoped Classical in
/-- The data for the palette construction, including `l`, `key`, `local_key`, `table`, `fast`. -/
structure Palette where
  /-- The `Palette` field of type `ℕ`. -/
  l : ℕ
  /-- The `Palette` component of type `s.clock.Input → B l`. -/
  key : s.clock.Input → B l
  local_key : Decor.Local key
  /-- The local table at each indexed position carried by `Palette`, with type `B l → Profile F
  s.p s.clock.width`. -/
  table : B l → Profile F s.p s.clock.width
  fast : ∀ i, Protocol.Frame.Fast (table i)
  agrees : ∀ v, table (key (observed T s v)) = masked T s v
  valid : ∀ x z a c, table (key x) z a c ≠ 0 →
    s.clock.guard s.w x = true ∧ ∀ j, active T s x j ≠ true → ∀ i, c j i = false

open scoped Classical in
private abbrev Pattern (E : Finset (controllers F T.embed)) :=
  ((↥E → ↥E → Bool) × (↥E → B s.clock.bits)) × Bool × (B s.p → Bool)

open scoped Classical in
private def pattern (E : Finset (controllers F T.embed)) (x : s.clock.Input) : Pattern T s E :=
  ((fun i j => x.see i j, fun i => x.mark (x.label i)), s.clock.guard s.w x, active T s x)

open scoped Classical in
private theorem pattern_local (E : Finset (controllers F T.embed)) :
    Decor.Local (pattern T s E) := by
  have ho : Decor.Local (fun x : s.clock.Input => (pattern T s E x).1) :=
    ⟨E, fun _ _ hh hm => Prod.ext (funext fun i => funext fun j => hh _ i.property _ j.property)
      (funext fun i => hm _ i.property)⟩
  have he := s.bank.program_local T.params.unit _ T.params.reach s.count
    (s.clock.count_local s.w s.j₀)
  exact ho.pair ((s.clock.guard_local s.w).pair (he.map (fun v j => (v j).1)))

open scoped Classical in
theorem palette (he : Compatible T s) : Nonempty (Palette T s) := by
  obtain ⟨E, hE⟩ := he
  let code := Coloring.encode (Pattern T s E)
  let k := code ∘ pattern T s E
  have same (x y : Example T s) (eq : k (observed T s x) = k (observed T s y)) :
      masked T s x = masked T s y := by
    have e := code.injective eq
    have hs := hE x y
      (fun i hi j hj => congrArg (fun z => z.1.1 ⟨i, hi⟩ ⟨j, hj⟩) e)
      (fun i hi => congrArg (fun z => z.1.2 ⟨i, hi⟩) e)
    exact congrArg₂ (fun (f : Profile F s.p s.clock.width) v => f.mask v.1 v.2)
      hs (congrArg Prod.snd e)
  let off : Profile F s.p s.clock.width := Protocol.Frame.diagonal (fun _ _ => 0)
  let f i := if h : ∃ v, k (observed T s v) = i then masked T s h.choose else off
  refine ⟨⟨_, k, (pattern_local T s E).map code, f, ?_, ?_, ?_⟩⟩
  · intro i
    dsimp only [f]
    split
    · rename_i hh
      apply Profile.mask_fast
      exact ((operator T s hh.choose.σ).fast _ _).pull _ _
    · exact Protocol.Frame.fast_diagonal _
  · intro v
    have hv : ∃ u, k (observed T s u) = k (observed T s v) := ⟨v, rfl⟩
    simp only [f, dite_eq_left hv]
    exact same _ _ hv.choose_spec
  · intro x z a c hn
    dsimp only [f] at hn
    split at hn
    · rename_i hv
      have eq := congrArg Prod.snd (code.injective hv.choose_spec)
      obtain ⟨hg, ha⟩ := Prod.mk.inj eq
      unfold masked Profile.mask at hn
      rw [hg, ha] at hn
      by_contra hh
      exact hn (ite_eq_right hh)
    · simp [off, Protocol.Frame.diagonal] at hn

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
end

/- # Resolving profile and slot commands at every site -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
open Coloring Transport

variable {F : Type} [Field F] {m h : ℕ} (T : Routes F m) (s : Rig T.params)
    (P : Palette T s)

open scoped Classical in
/-- The quantity computed by `Format.vec (h + 1) (.addr s.clock.bits)`. -/
abbrev Selectors (h : ℕ) := Format.vec (h + 1) (.addr s.clock.bits)
open scoped Classical in
/-- Computes the commands by the application `Controls h s.p (.addr P.l)`. -/
abbrev Commands (h : ℕ) := Controls h s.p (.addr P.l)

open scoped Classical in
/-- Uses `⟨@Root.mk _ _ _ (T.action h σ) i, z⟩` as the representation. -/
def atSite (σ : Equiv.Perm (B h)) (z : (Selectors T s h).obj) (i : Site h) : s.clock.Input :=
  ⟨@Root.mk _ _ _ (T.action h σ) i, z⟩

open scoped Classical in
/-- The data for the engine construction, including `f`, `group`, `resolves`, `groups`. -/
structure Engine (h : ℕ) where
  /-- The `Engine` component of type `((Perm h).pair (Selectors T s h)).obj → (Commands T s P
  h).obj`. -/
  f : ((Perm h).pair (Selectors T s h)).obj → (Commands T s P h).obj
  /-- The `Engine` component of type `Port h s.p → ℕ`. -/
  group : Port h s.p → ℕ
  resolves : ∀ σ : Equiv.Perm (B h), ∀ z i, f (σ, z) i =
    Decor.resolve (s.program P.key (atSite T s σ z i))
      (fun j => (T.action h σ).smul (s.bank.hop j) i)
  groups : ∀ σ x y i j, s.bank.generator T.params.unit i = s.bank.generator T.params.unit j →
    (T.action h σ).smul (s.bank.generator T.params.unit i).val x = y →
    group (x, i) = group (y, j)

namespace Engine

variable {T s P} (H : Engine T s P h) (σ : Equiv.Perm (B h))

open scoped Classical in
/-- Builds `System F h s.p s.clock.width (2 ^ z) where selector` with the specified `selector`,
`config`, `group`, `dispatch`. -/
abbrev system (z : ℕ) : System F h s.p s.clock.width (2 ^ z) where
  selector := Selectors T s h
  config := .addr P.l
  group := H.group
  dispatch := H.f
  kernel i := (P.table i).apply z

open scoped Classical in
theorem key (z : (Selectors T s h).obj) (i : Site h) :
    (H.f (σ, z) i).1 = P.key (atSite T s σ z i) := by rw [H.resolves]; rfl

open scoped Classical in
theorem orders (z : (Selectors T s h).obj) :
    letI := T.action h σ
    commands (H.f (σ, z)) = s.bank.orders T.params.unit _ T.params.reach s.count z := by
  funext ⟨i, j⟩
  unfold commands
  rw [H.resolves]
  rfl

open scoped Classical in
theorem enabled (z : (Selectors T s h).obj) (i : Site h) (j : B s.p) :
    (i, j) ∈ Enabled (commands (H.f (σ, z))) ↔ active T s (atSite T s σ z i) j = true := by
  simp only [Enabled, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [H.orders]
  rfl

open scoped Classical in
/-- The placement of type `Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) H.group
(commands (H.f (σ, choose T s σ u)))`, constructed using `T.action h σ`. -/
def placement (u : Path T s σ) :
    Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) H.group
      (commands (H.f (σ, choose T s σ u))) := by
  let _ := T.action h σ
  exact s.bank.placement T.params.unit _ T.params.reach s.count (s.clock.selector u) (s.widthAt u)
    (s.bounded u) (s.clock.count_branch s.w s.j₀ s.hw s.h₀ u)
    H.group (H.groups σ) _ (H.orders σ _)

end Engine
end MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
end

/- # Reading a branch kernel at its physical pins -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
open Coloring Transport

variable {F : Type} [Field F] {m h z : ℕ} (T : Routes F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h)) (u : Path T s σ) (i : Site h)

open scoped Classical in
theorem sample_apply {group : Port h s.p → ℕ} {a : Orders h s.p}
    (P : Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) group a)
    (hP : P.embed = place T s σ u) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) :
    (sample T s ⟨h, σ, u, i⟩).apply z (x i) (y i) (c i) =
      (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y))
        ((result T s σ u).view i (P.inside c)) := by
  unfold sample Profile.apply Protocol.Frame.pull
  refine congrArg₂ ((operator T s σ).kernel u i z) ?_ ?_
  · funext ⟨⟨⟨j, k⟩, b⟩, e⟩ t
    let v := Sum.elim (Function.curry (x i)) (Function.curry (y i))
    cases b
    · have hs : side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩ = .inl k := ite_eq_right Bool.false_ne_true
      change v (side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩) t = x j (k, t)
      rw [hs]
      exact congrArg (fun l => x l (k, t)) (show j = i from e).symm
    · have hs : side T s σ i ⟨⟨⟨j, k⟩, true⟩, e⟩ = .inr k := ite_eq_left rfl
      change v (side T s σ i ⟨⟨⟨j, k⟩, true⟩, e⟩) t = y (inflate h σ j) (k, t)
      rw [hs]
      exact congrArg (fun l => y l (k, t)) (show inflate h σ j = i from e).symm
  · funext k t
    have he : (P.embed k.val).1 = i := (P.owner _).trans k.property
    change c i ((place T s σ u k.val).2, t) = c (P.embed k.val).1 ((P.embed k.val).2, t)
    rw [he, hP]

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
end

/-
# Correctness of the programmed transport

Every surviving selector describes exactly one legal branch. Its
disabled slots are pinned to zero. On all other slots the program
executes the physical copy of the branch kernel.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
open Coloring Transport

variable {F : Type} [Field F] {m h z : ℕ}

open scoped Classical in
private theorem injective_selector {G J I : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [Fintype I] [MulAction G I] :
    Function.Injective (s.clock.selector (I := I)) :=
  (a.balls I).selector_injective a.offers s.clock.batch s.clock.bound s.clock.μ a.path s.clock.width

namespace Engine
variable {T : Routes F m} {s : Rig T.params} {P : Palette T s} (H : Engine T s P h)
    (σ : Equiv.Perm (B h))

open scoped Classical in
private def codes : Path T s σ ↪ (Selectors T s h).obj := by
  let _ := T.action h σ
  exact ⟨choose T s σ, s.injective_selector⟩

open scoped Classical in
private theorem eligible (t : (Selectors T s h).obj) :
    (∀ i, s.clock.guard s.w (atSite T s σ t i) = true) ↔ ∃ u, choose T s σ u = t := by
  let _ := T.action h σ
  have ht := s.clock.guard_iff s.w s.hw t
  refine ⟨fun h => (ht.mp h).exists, fun ⟨u, hu⟩ => ht.mpr ⟨u, hu, ?_⟩⟩
  exact fun v hv => s.injective_selector (hv.trans hu.symm)

open scoped Classical in
theorem agrees (u : Path T s σ) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) (hc : Protocol.Padded (commands (H.f (σ,
      choose T s σ u))) c)
    (i : Site h) :
    (P.table (H.f (σ, choose T s σ u) i).1).apply z (x i) (y i) (c i) =
      (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y))
        ((result T s σ u).view i ((H.placement σ u).inside c)) := by
  let e : Example T s := ⟨h, σ, u, i⟩
  rw [H.key]
  change (P.table (P.key (observed T s e))).apply _ _ _ _ = _
  rw [P.agrees]
  have hg : s.clock.guard s.w (observed T s e) = true :=
    (eligible σ (choose T s σ u)).mpr ⟨u, rfl⟩ i
  have hy : ∀ j, active T s (observed T s e) j ≠ true → ∀ k, c i (j, k) = false := by
    intro j hj
    exact hc (i, j) (mt (H.enabled σ _ i j).mp hj)
  trans (sample T s e).apply z (x i) (y i) (c i)
  · exact ite_eq_left ⟨hg, hy⟩
  · exact sample_apply T s σ u i _ rfl x y c

open scoped Classical in
private theorem surviving (t : (Selectors T s h).obj) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) (hne : (H.system z).value (H.f (σ, t)) x y c ≠ 0) :
    (∃ u, choose T s σ u = t) ∧ Protocol.Padded (commands (H.f (σ, t))) c := by
  have hi (i : Site h) : s.clock.guard s.w (atSite T s σ t i) = true ∧
      ∀ j, active T s (atSite T s σ t i) j ≠ true → ∀ k, c i (j, k) = false := by
    have hw := Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ _)
    change (P.table (H.f (σ, t) i).1).apply z (x i) (y i) (c i) ≠ 0 at hw
    rw [H.key] at hw
    exact P.valid _ _ _ _ hw
  refine ⟨(eligible σ t).mp (fun i => (hi i).1), ?_⟩
  rintro ⟨i, j⟩ hij k
  exact (hi i).2 _ (mt (H.enabled σ t i j).mpr hij) k

open scoped Classical in
theorem width (u : Path T s σ) :
    2 * (∑ e, requests T s σ u e) ≤ 4812 * s.clock.width * 2 ^ h := by
  let _ := T.action h σ
  have he := s.clock.width_total s.w s.hw u
  change (∑ e, requests T s σ u e) ≤ 1203 * Fintype.card (Site h) * s.clock.width at he
  rw [show Fintype.card (Site h) = 2 ^ h * 2 by simp [pow_succ]] at he
  exact (Nat.mul_le_mul_left 2 he).trans_eq (by ring)

open scoped Classical in
theorem correct (z : ℕ) : (H.system z).Correct 4812 := by
  apply Protocol.system_correct
  intro σ
  exact ⟨{
    E := (arena T σ).Edge
    I := Path T s σ
    src := src T σ
    dst := dst T σ
    m := requests T s σ
    proc := operator T s σ
    choose := codes σ
    place := H.placement σ
    cost := width σ
    agrees := H.agrees σ
    invalid := H.surviving σ
  }⟩

end Engine
end MatrixMultiplicationAllFields.MatrixExponent.Routing.Rig
end

/-
# Uniform routing across widths

Choose a height ratio before fixing the menu. All overhead depending
on the menu can be absorbed into the eventual height cutoff and a
polynomial cost exponent. The bound on transported width stays 4812.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Coloring Transport

open scoped Classical in
private theorem heights (τ : ℝ) (hτ : 0 < τ) :
    ∃ m : ℕ, 0 < m ∧ ∀ K : ℕ, ∀ᶠ h : ℕ in Filter.atTop,
      h / m + K ≤ h ∧ (↑(h / m + K) : ℝ) ≤ τ * h := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (2 / τ))
  have hm' : 2 < m := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hm)
  have ht : 2 ≤ (m : ℝ) * τ := ((div_lt_iff₀ hτ).mp ((le_max_right _ _).trans_lt hm)).le
  refine ⟨m, by omega, fun K => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (K * m)] with h hh
  have he : (h / m + K) * m ≤ 2 * h := by
    rw [add_mul, two_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self h m) hh
  constructor
  · have := (Nat.mul_le_mul_left (h / m + K) hm'.le).trans he
    omega
  · apply le_of_mul_le_mul_right _ (by exact_mod_cast (by omega : 0 < m) : (0 : ℝ) < m)
    have hh' : (↑(h / m + K) : ℝ) * m ≤ 2 * h := by exact_mod_cast he
    exact hh'.trans (by nlinarith only [mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg h)])

variable {F : Type} [Field F]

open scoped Classical in
theorem local_of_routes
    (routes : ∀ m : ℕ, 0 < m → ∃ (T : Routes F m) (s : Rig T.params), Rig.Compatible T s) :
    LocalProtocol F := by
  refine ⟨4812, fun τ hτ => ?_⟩
  obtain ⟨m, hm, hcut⟩ := heights τ hτ
  obtain ⟨T, s, hr⟩ := routes m hm
  obtain ⟨P⟩ := Rig.palette T s hr
  obtain ⟨d, k, hd⟩ := (s.program_local P.local_key).dispatch (T := T) s.bank.hop
  obtain ⟨c, hc⟩ := profile_weight P.table P.fast
  refine ⟨s.p, s.clock.width, max d c, s.clock.wide, ?_⟩
  filter_upwards [hcut (T.overhead + s.p + 22), Filter.eventually_ge_atTop k] with h hb hk
  obtain ⟨f, hf, he⟩ := hd h hk
  let b := h / m + T.overhead
  obtain ⟨g, hg, hm⟩ := T.portGroup h b s.p le_rfl (by dsimp [b]; omega)
    (s.bank.generator T.params.unit)
  let engine : Rig.Engine T s P h := ⟨f, g, he, hm⟩
  refine ⟨b + s.p + 22, Nat.add_le_add_right (Nat.le_add_left ..) 22,
    by dsimp [b]; omega, ?_, fun j _ => ?_⟩
  · simpa [b, Nat.add_assoc] using hb.2
  · refine ⟨engine.system j, engine.correct j, ?_, hf.mono (le_max_left ..), ?_⟩
    · exact fun i => (hg i).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact (hc j).mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right ..)))

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end
