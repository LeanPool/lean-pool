/-
Copyright (c) 2019 Jesse Michael Han and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han, Floris van Doorn, and Flypitch4 contributors
-/

module

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/colimit.lean -/

public import LeanPool.NFWeakPartition.Flypitch4.ToMathlib

/-! NF weak partition development: Flypitch4.Colimit. -/


public section

namespace NFChoice

/-! ## Lean 3 → Lean 4 Port: Notes for Colimit.lean

### Scope
Only declarations needed by `src/henkin.lean` are ported. The
following are dropped:
- `constant_functor` — 0 uses outside colimit.lean
- `trans` (the colimit lemma) — 0 uses outside colimit.lean;
`Trans` in Lean 4 is a typeclass

### Quotient API choices
- `colimit` is `@[reducible]` so that `Quotient.lift`,
`Quotient.sound`, etc. can unify with it
- Lean 3 `quotient.mk`   → Lean 4 `Quotient.mk (coproduct_setoid
F)`
- Lean 3 `quotient.lift` → Lean 4 `Quotient.lift`
- Lean 3 `quotient.eq`   → Lean 4 `Quotient.exact` /
`Quotient.sound`

### `cocone_of_colimit` kept as an internal helper
Used internally to prove `same_fiber_as_push_to_r/l`, which
henkin.lean uses directly.

### Structures: `Reflexive` / `Transitive` deprecated in Lean 4
Use explicit `∀` hypotheses in `directed_type`.
-/


universe u v

namespace colimit

structure directed_type : Type (u + 1) where
  carrier : Type u
  rel : carrier → carrier → Prop
  h_reflexive : ∀ x : carrier, rel x x
  h_transitive : ∀ {x y z : carrier}, rel x y → rel y z → rel x z
  h_directed : ∀ x y : carrier, ∃ z : carrier, rel x z ∧ rel y z

structure directed_diagram (D : directed_type.{u}) : Type (max (u + 1) (v + 1)) where
  obj : D.carrier → Type v
  mor : ∀ {x y : D.carrier}, D.rel x y → (obj x → obj y)
  h_mor :
    ∀ {x y z : D.carrier} {f1 : D.rel x y} {f2 : D.rel y z} {f3 : D.rel x z},
      mor f3 = mor f2 ∘ mor f1

@[reducible, expose]
def directed_type_of_nat : directed_type
    where
  carrier := ℕ
  rel := (· ≤ ·)
  h_reflexive := Nat.le_refl
  h_transitive := Nat.le_trans
  h_directed := fun x y => ⟨x + y, Nat.le_add_right x y, Nat.le_add_left y x⟩

notation "ℕ'" => directed_type_of_nat

@[expose]
def coproduct_of_directed_diagram {D : directed_type.{u}}
    (F : directed_diagram.{u, v} D) : Type (max u v) :=
  Σ a : D.carrier, F.obj a

@[expose]
def canonical_inclusion_coproduct {D : directed_type} {F : directed_diagram D}
    (i : D.carrier) : F.obj i → coproduct_of_directed_diagram F := fun x => ⟨i, x⟩

@[expose]
def germ_relation {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    coproduct_of_directed_diagram F → coproduct_of_directed_diagram F → Prop :=
  fun ⟨i, x⟩ ⟨j, y⟩ =>
  ∃ k : D.carrier,
    ∃ z : F.obj k, ∃ f_x : D.rel i k, ∃ f_y : D.rel j k, F.mor f_x x = z ∧ F.mor f_y y = z

lemma germ_equivalence {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    Equivalence (germ_relation F)
    where
  refl := fun ⟨i, x⟩ => by
    have h_refl := D.h_reflexive i
    exact ⟨i, F.mor h_refl x, h_refl, h_refl, rfl, rfl⟩
  symm := fun {a b} h => by
    obtain ⟨i, x⟩ := a; obtain ⟨j, y⟩ := b
    obtain ⟨ℓ, z, f_x, f_y, H1, H2⟩ := h
    exact ⟨ℓ, z, f_y, f_x, H2, H1⟩
  trans := fun {a b c} hab hbc => by
    obtain ⟨i, x⟩ := a; obtain ⟨j, y⟩ := b; obtain ⟨k, z⟩ := c
    obtain ⟨ℓ₁, _w₁, fi, fj1, Hil, Hjl1⟩ := hab
    obtain ⟨ℓ₂, _w₂, fj2, fk, Hjl2, Hkl2⟩ := hbc
    obtain ⟨ℓ₃, g1, g2⟩ := D.h_directed ℓ₁ ℓ₂
    have f1 : D.rel i ℓ₃ := D.h_transitive fi g1
    have f2 : D.rel j ℓ₃ := D.h_transitive fj1 g1
    have f3 : D.rel k ℓ₃ := D.h_transitive fk g2
    have H1 : F.mor f1 = F.mor g1 ∘ F.mor fi := F.h_mor
    have H2l : F.mor f2 = F.mor g1 ∘ F.mor fj1 := F.h_mor
    have H2r : F.mor f2 = F.mor g2 ∘ F.mor fj2 := F.h_mor
    have H3 : F.mor f3 = F.mor g2 ∘ F.mor fk := F.h_mor
    have Hf1_f2 : F.mor f1 x = F.mor f2 y := by
      rw [H1, H2l];
      simp only [Function.comp_apply];
      rw [Hil, Hjl1]
        -- F.mor f3 z = F.mor g2 (F.mor fk z) = F.mor g2 w₂ = F.mor g2
            -- (F.mor fj2 y) = F.mor f2 y

    have Hf3_f2 : F.mor f3 z = F.mor f2 y := by
      rw [H3, H2r];
      simp only [Function.comp_apply]; rw [Hkl2, Hjl2]
    exact ⟨ℓ₃, F.mor f2 y, f1, f3, Hf1_f2, Hf3_f2⟩

/-- The setoid on the coproduct given by germ equivalence -/
@[expose]
def coproduct_setoid {D : directed_type} (F : directed_diagram D) :
    Setoid (coproduct_of_directed_diagram F) :=
  ⟨germ_relation F, germ_equivalence F⟩

@[reducible, expose]
def LimitCarrier {D : directed_type.{u}} (F : directed_diagram.{u, v} D) :
    Type (max u v) :=
  Quotient (coproduct_setoid F)

@[expose]
def canonical_map {D : directed_type} {F : directed_diagram D} (i : D.carrier) :
    F.obj i → LimitCarrier F := fun x => Quotient.mk (coproduct_setoid F) ⟨i, x⟩

lemma canonical_map_inj_of_transition_maps_inj {D : directed_type}
    {F : directed_diagram D} (i : D.carrier)
    (H : ∀ {i j : D.carrier}, ∀ h : D.rel i j, Function.Injective (F.mor h)) :
    Function.Injective (@canonical_map D F i) :=
  by
  intro x y heq
  simp only [canonical_map] at heq
  have heq' := Quotient.exact heq
  change germ_relation F ⟨i, x⟩ ⟨i, y⟩ at heq'
  obtain ⟨j, _z, edge_x, edge_y, H1, H2⟩ := heq'
  exact H edge_x (by rw [H1, H2])

structure cocone {D : directed_type} (F : directed_diagram D) where
  vertex : Type*
  map : ∀ i : D.carrier, F.obj i → vertex
  h_compat : ∀ {i j : D.carrier}, ∀ h : D.rel i j, map i = map j ∘ F.mor h

/- The colimit is itself a cocone over its diagram -/
@[expose]
def cocone_of_colimit {D : directed_type} (F : directed_diagram D) : cocone F
    where
  vertex := LimitCarrier F
  map := canonical_map
  h_compat := by
    intro i j H
    funext x
    simp only [canonical_map, Function.comp_apply]
    apply Quotient.sound
    change germ_relation F ⟨i, x⟩ ⟨j, F.mor H x⟩
    have h_refl_j := D.h_reflexive j
    refine
      ⟨j, F.mor H x, H, h_refl_j, rfl, ?_⟩
        -- F.mor h_refl_j (F.mor H x) = F.mor H x
            -- By h_mor with f1=H, f2=h_refl_j, f3=H: F.mor H = F.mor
            -- h_refl_j ∘ F.mor H

    have hmor : F.mor H = F.mor h_refl_j ∘ F.mor H := @F.h_mor i j j H h_refl_j H
    exact (congr_fun hmor x).symm

/- Given a cocone V over a diagram D, return the canonical map
colim D → V -/
@[expose]
def universal_map {D : directed_type} {F : directed_diagram D} {V : cocone F} :
    LimitCarrier F → V.vertex :=
  Quotient.lift (fun p => V.map p.1 p.2)
    (by
      intro ⟨i, x⟩ ⟨j, y⟩ h
      change germ_relation F ⟨i, x⟩ ⟨j, y⟩ at h
      obtain ⟨k, _z, f1, f2, H1, H2⟩ := h
      change V.map i x = V.map j y
      have e1 : V.map i x = V.map k (F.mor f1 x) := congr_fun (V.h_compat f1) x
      have e2 : V.map j y = V.map k (F.mor f2 y) := congr_fun (V.h_compat f2) y
      rw [e1, e2, H1, H2])

@[simp]
lemma universal_map_property {D : directed_type} {F : directed_diagram D} {V : cocone F}
    (i : D.carrier) (x : F.obj i) :
    universal_map (V := V) (canonical_map i x) = V.map i x :=
  rfl

lemma universal_map_inj_of_components_inj {D : directed_type} {F : directed_diagram D}
    {V : cocone F} (h_inj : ∀ i : D.carrier, Function.Injective (V.map i)) :
    Function.Injective (universal_map (V := V) : LimitCarrier F → V.vertex) :=
  by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ p => ?_
  induction b using Quotient.inductionOn with
  | _ q => ?_
  obtain ⟨i, x⟩ := p; obtain ⟨j, y⟩ := q
  simp only [universal_map] at h
  apply Quotient.sound
  change germ_relation F ⟨i, x⟩ ⟨j, y⟩
  obtain ⟨k, Hik, Hjk⟩ := D.h_directed i j
  refine
    ⟨k, F.mor Hik x, Hik, Hjk, rfl, ?_⟩
      -- Goal: F.mor Hjk y = F.mor Hik x

  apply h_inj k
  have e1 : V.map i x = V.map k (F.mor Hik x) := congr_fun (V.h_compat Hik) x
  have e2 : V.map j y = V.map k (F.mor Hjk y) := congr_fun (V.h_compat Hjk) y
  rw [← e2, ← e1]; exact h.symm

/- Given a germ-equivalence class from the colimit, return a
representative from the coproduct
   and a proof that this is a lift -/
@[expose]
noncomputable def germ_rep {D : directed_type} {F : directed_diagram D}
    (a : LimitCarrier F) :
    Σ' x : coproduct_of_directed_diagram F, Quotient.mk (coproduct_setoid F) x = a :=
  Classical.psigma_of_exists (Quotient.exists_rep a)

@[simp]
lemma canonical_map_quotient {D : directed_type} {F : directed_diagram D}
    (a : coproduct_of_directed_diagram F) :
    canonical_map a.1 a.2 = Quotient.mk (coproduct_setoid F) a :=
  by
  simp only [canonical_map]
  congr 1
    /- Assuming canonical maps into the colimit are injective, ⟨i,x⟩
    and ⟨j,y⟩ in the same fiber
       over a z : colimit F are related by any transition map i → j. -/


/- Assuming canonical maps into the colimit are injective, ⟨i,x⟩
and ⟨j,y⟩ in the same fiber
   over a z : colimit F are related by any transition map i → j. -/
@[simp]
lemma eq_mor_of_same_fiber {D : directed_type} {F : directed_diagram D}
    (a b : coproduct_of_directed_diagram F) {z : LimitCarrier F}
    (Ha : Quotient.mk (coproduct_setoid F) a = z)
    (Hb : Quotient.mk (coproduct_setoid F) b = z)
    (H_inj : ∀ i : D.carrier, Function.Injective (@canonical_map D F i))
    (H_rel : D.rel a.1 b.1) : F.mor H_rel a.2 = b.2 := by
  -- The cocone_of_colimit h_compat gives:
    -- canonical_map a.1 a.2 = canonical_map b.1 (F.mor H_rel a.2)

  have H_eq : z = canonical_map b.1 (F.mor H_rel a.2) :=
    by
    have hcompat := (cocone_of_colimit F).h_compat H_rel
    have hcf := congr_fun hcompat a.2
    simp only [cocone_of_colimit, Function.comp_apply] at hcf
    rw [canonical_map_quotient a, Ha] at hcf
    exact hcf
  have heq : canonical_map b.1 b.2 = canonical_map b.1 (F.mor H_rel a.2) := by
    rw [canonical_map_quotient b, Hb, H_eq]
  exact (H_inj b.1 heq).symm

@[simp]
lemma eq_mor_of_same_fiber' {D : directed_type} {F : directed_diagram D}
    (a_fst b_fst : D.carrier) (a_snd : F.obj a_fst) (b_snd : F.obj b_fst)
    {z : LimitCarrier F}
    (Ha : Quotient.mk (coproduct_setoid F) (⟨a_fst, a_snd⟩ : coproduct_of_directed_diagram F) =
        z)
    (Hb : Quotient.mk (coproduct_setoid F) (⟨b_fst, b_snd⟩ : coproduct_of_directed_diagram F) =
        z)
    (H_inj : ∀ i : D.carrier, Function.Injective (@canonical_map D F i))
    (H_rel : D.rel a_fst b_fst) : F.mor H_rel a_snd = b_snd :=
  eq_mor_of_same_fiber ⟨a_fst, a_snd⟩ ⟨b_fst, b_snd⟩ Ha Hb H_inj H_rel

/- Given an x : F_i and j : ℕ, apply the transition map to obtain
x' : F_{i+j} -/
@[reducible, expose]
def push_to_sum_r {F : directed_diagram ℕ'} {i : ℕ} (x : F.obj i) (j : ℕ) :
    F.obj (i + j) :=
  F.mor (D := ℕ') (Nat.le_add_right i j) x

@[reducible, expose]
def push_to_sum_l {F : directed_diagram ℕ'} {j : ℕ} (x : F.obj j) (i : ℕ) :
    F.obj (i + j) :=
  F.mor (D := ℕ') (Nat.le_add_left j i) x

/- The push_to of x is in the same germ-equivalence class as x -/
lemma same_fiber_as_push_to_r {F : directed_diagram ℕ'} {i : ℕ} (x : F.obj i) (j : ℕ) :
    @canonical_map ℕ' F i x = @canonical_map ℕ' F (i + j) (push_to_sum_r x j) :=
  congr_fun ((cocone_of_colimit F).h_compat (D := ℕ') (Nat.le_add_right i j)) x

lemma same_fiber_as_push_to_l {F : directed_diagram ℕ'} {j : ℕ} (x : F.obj j) (i : ℕ) :
    @canonical_map ℕ' F j x = @canonical_map ℕ' F (i + j) (push_to_sum_l x i) :=
  congr_fun ((cocone_of_colimit F).h_compat (D := ℕ') (Nat.le_add_left j i)) x

end colimit

namespace omega_colimit

open colimit

/- Facts about directed colimits indexed by ℕ'. -/

/- Build transition maps from a successor-step map by induction
on the target.
   Uses an auxiliary explicit-argument version to avoid
   implicit-argument
   inference failures in recursive calls. -/
@[expose]
def map_aux (F : ℕ → Type*) (h_succ : ∀ {i : ℕ}, F i → F (i + 1)) :
    ∀ (x y : ℕ), x ≤ y → F x → F y
  | x, 0, h => by rw [Nat.eq_zero_of_le_zero h]; exact id
  | x, y + 1, h =>
    if hx : x = y + 1 then by rw [hx]; exact id
    else h_succ ∘ map_aux F h_succ x y (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx))

@[expose]
def diagram.mk.map {F : ℕ → Type*} {h_succ : ∀ {i : ℕ}, F i → F (i + 1)} (x y : ℕ)
    (h : x ≤ y) : F x → F y :=
  map_aux F h_succ x y h

@[simp]
lemma diagram.mk.map_self_id {F : ℕ → Type*} {h_succ : ∀ (i : ℕ), F i → F (i + 1)}
    (x : ℕ) : @diagram.mk.map F (fun {i} => h_succ i) x x (Nat.le_refl x) = id := by
  induction x with
  | zero => simp [diagram.mk.map, map_aux]
  | succ n ih =>
    simp only [diagram.mk.map, map_aux]
    rfl
      /- If the successive maps of h_succ are injective, then all their
      compositions are injective -/


/- If the successive maps of h_succ are injective, then all their
compositions are injective -/
lemma diagram.mk.map_inj {F : ℕ → Type*} {h_succ : ∀ (i : ℕ), F i → F (i + 1)}
    {h_inj : ∀ {i : ℕ}, Function.Injective (h_succ i)} (x y : ℕ) (h : x ≤ y) :
    Function.Injective (@diagram.mk.map F (fun {i} => h_succ i) x y h) :=
  by
  simp only [diagram.mk.map]
  induction y with
  | zero =>
    have hx : x = 0 := Nat.eq_zero_of_le_zero h
    subst hx
    simp only [map_aux]
    exact fun _ _ h => h
  | succ n ih =>
    by_cases hx : x = n + 1
    · subst hx
      simp only [map_aux]
      exact fun _ _ h => h
    · have hle : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx)
      simp only [map_aux, dite_eq_right hx]
      exact
        Function.Injective.comp h_inj
          (ih hle)
            /- Functoriality lemma for map_aux -/


/- Functoriality lemma for map_aux -/
private lemma map_aux_functorial (F : ℕ → Type*) (h_succ : ∀ {i : ℕ}, F i → F (i + 1))
    (x y z : ℕ) (H1 : x ≤ y) (H2 : y ≤ z) (H3 : x ≤ z) :
    map_aux F h_succ x z H3 = map_aux F h_succ y z H2 ∘ map_aux F h_succ x y H1 := by
  induction z with
  | zero =>
    have hy0 : y = 0 := Nat.eq_zero_of_le_zero H2
    have hx0 : x = 0 := Nat.eq_zero_of_le_zero (hy0 ▸ H1)
    subst hx0; subst hy0; simp [map_aux]
  | succ n ih =>
    by_cases hy : y = n + 1
    · subst hy
      by_cases hx : x = n + 1
      · subst hx; simp [map_aux]
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H1 hx)
        simp only [map_aux, dite_eq_right hx]
        ext; simp [Function.comp]
    · have hyn : y ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H2 hy)
      by_cases hx : x = n + 1
      · have : x ≤ n := Nat.le_trans H1 hyn; omega
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H3 hx)
        have ih' := ih hyn hxn
        simp only [map_aux, dite_eq_right hy, dite_eq_right hx, Function.comp_assoc]
        exact ih'.symm ▸ rfl

/- Given a ℕ-indexed family of types and a way of assigning maps
between successive objects
   in this family, return the induced directed_diagram over ℕ'. -/
@[expose]
def diagram.mk (F : ℕ → Type*) (h_succ : ∀ {i : ℕ}, F i → F (i + 1)) : directed_diagram ℕ'
    where
  obj := F
  mor := fun {x y} h => @diagram.mk.map F h_succ x y h
  h_mor := by
    intro x y z H1 H2 H3
    simp only [diagram.mk.map]
    exact map_aux_functorial F h_succ x y z H1 H2 H3

end omega_colimit

end NFChoice
