/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Semantics

/-!
# The normal form of geometric formulas: syntax

Every geometric formula `φ` in the context `Fin n` is equivalent, in every structure on a
type, to a `u`-small disjunction `⋁ᵢ ∃ yᵢ, θᵢ (x, yᵢ)` of existential quantifications of
Horn formulas (finite conjunctions of atomic formulas). This file constructs the normal form
(`GeometricFormula.normalForm`) by induction on `φ` and proves the equivalence for the
set-theoretic semantics (`GeometricFormula.realize_normalForm`,
`GeometricFormula.realize_iSup_exs_normalForm`). The categorical form, in every sheaf topos,
is `GeometricFormula.exists_interp_eq_iSup_exs` (roadmap 2.2 (b)), in
`LeanPool.ClassifyingTopoi.NormalFormSemantics`.

## Main definitions

* `LeanPool.ClassifyingTopoi.GeometricFormula.relabel`: renaming of variables along
  `Fin n → Fin n'`, with `realize_relabel`;
* `LeanPool.ClassifyingTopoi.GeometricFormula.NormalForm`, `normalForm`: the normal form. A
  conjunction of two disjunctions becomes the disjunction over pairs of the conjunctions, the
  quantified variables of both sides placed one after the other (`relabelLeft`,
  `relabelRight`); an existential quantification of a disjunction becomes the disjunction of the
  quantifications, with one more quantified variable, moved to the front of the quantified
  block (`Fin.append_left_snoc`).
-/

@[expose] public section

universe w u₁ u₂ v u

namespace LeanPool.ClassifyingTopoi

variable {L : FirstOrder.Language.{u₁, u₂}}

namespace GeometricFormula

/-- Renaming of the variables of a geometric formula along `ρ : Fin n → Fin n'`; under an
existential quantifier, the bound last variable is sent to the last variable. -/
def relabel : {n n' : ℕ} → (Fin n → Fin n') → GeometricFormula.{w} L n →
    GeometricFormula.{w} L n'
  | _, _, _, .top => .top
  | _, _, ρ, .and φ ψ => .and (φ.relabel ρ) (ψ.relabel ρ)
  | _, _, ρ, .iSup φ => .iSup fun i => (φ i).relabel ρ
  | _, _, ρ, .equal t₁ t₂ => .equal (t₁.relabel ρ) (t₂.relabel ρ)
  | _, _, ρ, .rel R ts => .rel R fun i => (ts i).relabel ρ
  | _, n', ρ, .ex φ => .ex (φ.relabel (Fin.lastCases (Fin.last n') fun i => (ρ i).castSucc))

/-- Satisfaction of a renamed formula. -/
theorem realize_relabel {M : Type v} [L.Structure M] {n n' : ℕ} (ρ : Fin n → Fin n')
    (φ : GeometricFormula.{w} L n) (x : Fin n' → M) :
    (φ.relabel ρ).Realize x ↔ φ.Realize (x ∘ ρ) := by
  induction φ generalizing n' with
  | top => exact Iff.rfl
  | and φ ψ ihφ ihψ => exact and_congr (ihφ ρ x) (ihψ ρ x)
  | iSup φ ih => exact exists_congr fun i => ih i ρ x
  | equal t₁ t₂ =>
    change (t₁.relabel ρ).realize x = (t₂.relabel ρ).realize x ↔ t₁.realize (x ∘ ρ) = _
    simp only [FirstOrder.Language.Term.realize_relabel]
  | rel R ts =>
    change FirstOrder.Language.Structure.RelMap R (fun i => ((ts i).relabel ρ).realize x) ↔
      FirstOrder.Language.Structure.RelMap R (fun i => (ts i).realize (x ∘ ρ))
    simp only [FirstOrder.Language.Term.realize_relabel]
  | ex φ ih =>
    refine exists_congr fun a => ?_
    rw [ih]
    have : (Fin.snoc x a : Fin _ → M) ∘
        (Fin.lastCases (Fin.last n') fun i => (ρ i).castSucc) = Fin.snoc (x ∘ ρ) a := by
      funext i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp
    rw [this]

/-- A renaming of a Horn formula is a Horn formula. -/
theorem IsHorn.relabel {n n' : ℕ} (ρ : Fin n → Fin n') {φ : GeometricFormula.{w} L n}
    (h : φ.IsHorn) : (φ.relabel ρ).IsHorn := by
  induction φ generalizing n' with
  | top => trivial
  | and φ ψ ihφ ihψ => exact ⟨ihφ ρ h.1, ihψ ρ h.2⟩
  | iSup φ ih => exact h.elim
  | equal t₁ t₂ => trivial
  | rel R ts => trivial
  | ex φ ih => exact h.elim

/-- Satisfaction of an iterated existential quantification. -/
theorem realize_exs {M : Type v} [L.Structure M] {n : ℕ} :
    ∀ {m : ℕ} (θ : GeometricFormula.{w} L (n + m)) (x : Fin n → M),
      (exs θ).Realize x ↔ ∃ y : Fin m → M, θ.Realize (Fin.append x y)
  | 0, θ, x => by
    refine ⟨fun h => ⟨Fin.elim0, by rwa [Fin.append_elim0]⟩, fun ⟨y, hy⟩ => ?_⟩
    rwa [Subsingleton.elim y Fin.elim0, Fin.append_elim0] at hy
  | m + 1, θ, x => by
    change (exs (m := m) (.ex θ)).Realize x ↔ _
    rw [realize_exs]
    constructor
    · rintro ⟨y, a, h⟩
      exact ⟨Fin.snoc y a, by rwa [Fin.append_snoc]⟩
    · rintro ⟨y, h⟩
      refine ⟨Fin.init y, y (Fin.last m), ?_⟩
      change θ.Realize (Fin.snoc (Fin.append x (Fin.init y)) (y (Fin.last m)))
      rwa [← Fin.append_snoc, Fin.snoc_init_self]

variable (L) in
/-- A normal form in the context `Fin n`: a `u`-small family of Horn formulas `θ i` in the
contexts `Fin (n + m i)`, standing for the disjunction of the `∃ yᵢ, θ i (x, yᵢ)`. -/
structure NormalForm (n : ℕ) where
  /-- The index type of the disjunction. -/
  ι : Type u
  /-- The number of quantified variables of each disjunct. -/
  m : ι → ℕ
  /-- The Horn formulas. -/
  θ : ∀ i, GeometricFormula.{u} L (n + m i)
  /-- The disjuncts are Horn formulas. -/
  isHorn : ∀ i, (θ i).IsHorn

/-- The renaming `Fin (n + a) → Fin (n + (a + b))` of the first `n + a` variables. -/
def relabelLeft (n a b : ℕ) : Fin (n + a) → Fin (n + (a + b)) :=
  fun k => Fin.cast (Nat.add_assoc ..) (Fin.castAdd b k)

/-- The renaming `Fin (n + b) → Fin (n + (a + b))` of the first `n` and the last `b`
variables. -/
def relabelRight (n a b : ℕ) : Fin (n + b) → Fin (n + (a + b)) :=
  Fin.addCases (fun k => Fin.castAdd (a + b) k) fun j => Fin.natAdd n (Fin.natAdd a j)

/-- `relabelLeft` selects the first two blocks of a concatenation of three tuples. -/
theorem append_comp_relabelLeft {M : Type v} {n a b : ℕ} (x : Fin n → M) (y : Fin a → M)
    (z : Fin b → M) : Fin.append x (Fin.append y z) ∘ relabelLeft n a b = Fin.append x y := by
  funext k
  have := congrFun (Fin.append_assoc x y z) (Fin.castAdd b k)
  rw [Fin.append_left] at this
  exact this.symm

/-- `relabelRight` selects the first and the last blocks of a concatenation of three tuples. -/
theorem append_comp_relabelRight {M : Type v} {n a b : ℕ} (x : Fin n → M) (y : Fin a → M)
    (z : Fin b → M) : Fin.append x (Fin.append y z) ∘ relabelRight n a b = Fin.append x z := by
  funext k
  induction k using Fin.addCases with
  | left k => simp [relabelRight]
  | right j => simp [relabelRight]

/-- The normal form of a geometric formula, by induction: conjunctions distribute over
disjunctions and existential quantifications, existential quantifications commute with
disjunctions. -/
def normalForm : {n : ℕ} → GeometricFormula.{u} L n → NormalForm.{u₁, u₂, u} L n
  | _, .top => ⟨PUnit, fun _ => 0, fun _ => .top, fun _ => trivial⟩
  | n, .and φ ψ =>
    let P := normalForm φ
    let Q := normalForm ψ
    ⟨P.ι × Q.ι, fun i => P.m i.1 + Q.m i.2,
      fun i => .and ((P.θ i.1).relabel (relabelLeft n _ _))
        ((Q.θ i.2).relabel (relabelRight n _ _)),
      fun i => ⟨(P.isHorn i.1).relabel _, (Q.isHorn i.2).relabel _⟩⟩
  | _, .iSup φ =>
    ⟨Σ j, (normalForm (φ j)).ι, fun i => (normalForm (φ i.1)).m i.2,
      fun i => (normalForm (φ i.1)).θ i.2, fun i => (normalForm (φ i.1)).isHorn i.2⟩
  | _, .equal t₁ t₂ => ⟨PUnit, fun _ => 0, fun _ => .equal t₁ t₂, fun _ => trivial⟩
  | _, .rel R ts => ⟨PUnit, fun _ => 0, fun _ => .rel R ts, fun _ => trivial⟩
  | n, .ex φ =>
    let P := normalForm φ
    ⟨P.ι, fun i => P.m i + 1,
      fun i => (P.θ i).relabel (Fin.cast (Nat.succ_add_eq_add_succ n (P.m i))),
      fun i => (P.isHorn i).relabel _⟩

/-- Quantifying over no variables changes nothing. -/
theorem exists_realize_append_zero {M : Type v} [L.Structure M] {n : ℕ}
    (θ : GeometricFormula.{w} L n) (x : Fin n → M) :
    (∃ y : Fin 0 → M, θ.Realize (Fin.append x y)) ↔ θ.Realize x := by
  refine ⟨fun ⟨y, h⟩ => ?_, fun h => ⟨Fin.elim0, by rwa [Fin.append_elim0]⟩⟩
  rwa [Subsingleton.elim y Fin.elim0, Fin.append_elim0] at h

/-- The normal form is equivalent to the formula in every structure on a type. -/
theorem realize_normalForm {M : Type v} [L.Structure M] {n : ℕ}
    (φ : GeometricFormula.{u} L n) (x : Fin n → M) :
    φ.Realize x ↔ ∃ i, ∃ y : Fin ((normalForm φ).m i) → M,
      ((normalForm φ).θ i).Realize (Fin.append x y) := by
  induction φ with
  | top => exact ⟨fun _ => ⟨PUnit.unit, Fin.elim0, trivial⟩, fun _ => trivial⟩
  | @and n φ ψ ihφ ihψ =>
    change φ.Realize x ∧ ψ.Realize x ↔ ∃ i : (normalForm φ).ι × (normalForm ψ).ι,
      ∃ y : Fin ((normalForm φ).m i.1 + (normalForm ψ).m i.2) → M,
        (((normalForm φ).θ i.1).relabel (relabelLeft n _ _)).Realize (Fin.append x y) ∧
        (((normalForm ψ).θ i.2).relabel (relabelRight n _ _)).Realize (Fin.append x y)
    simp only [realize_relabel, ihφ, ihψ]
    constructor
    · rintro ⟨⟨i, y, h⟩, ⟨j, z, h'⟩⟩
      refine ⟨(i, j), Fin.append y z, ?_, ?_⟩
      · rwa [append_comp_relabelLeft]
      · rwa [append_comp_relabelRight]
    · rintro ⟨⟨i, j⟩, w, h, h'⟩
      rw [← Fin.append_castAdd_natAdd (f := w)] at h h'
      rw [append_comp_relabelLeft] at h
      rw [append_comp_relabelRight] at h'
      exact ⟨⟨i, _, h⟩, ⟨j, _, h'⟩⟩
  | iSup φ ih =>
    change (∃ j, (φ j).Realize x) ↔ _
    simp only [ih]
    exact ⟨fun ⟨j, i, y, h⟩ => ⟨(⟨j, i⟩ : Σ j, (normalForm (φ j)).ι), y, h⟩,
      fun ⟨i, y, h⟩ => ⟨i.1, i.2, y, h⟩⟩
  | equal t₁ t₂ =>
    exact ⟨fun h => ⟨PUnit.unit, (exists_realize_append_zero _ x).2 h⟩,
      fun ⟨_, h⟩ => (exists_realize_append_zero (.equal t₁ t₂) x).1 h⟩
  | rel R ts =>
    exact ⟨fun h => ⟨PUnit.unit, (exists_realize_append_zero _ x).2 h⟩,
      fun ⟨_, h⟩ => (exists_realize_append_zero (.rel R ts) x).1 h⟩
  | @ex n φ ih =>
    change (∃ a, φ.Realize (Fin.snoc x a)) ↔ ∃ i : (normalForm φ).ι,
      ∃ y : Fin ((normalForm φ).m i + 1) → M,
        (((normalForm φ).θ i).relabel (Fin.cast (Nat.succ_add_eq_add_succ n _))).Realize
          (Fin.append x y)
    simp only [realize_relabel, ih]
    constructor
    · rintro ⟨a, i, y, h⟩
      exact ⟨i, Fin.cons a y, by rwa [← Fin.append_left_snoc]⟩
    · rintro ⟨i, w, h⟩
      refine ⟨w 0, i, Fin.tail w, ?_⟩
      rwa [Fin.append_left_snoc, Fin.cons_self_tail]

/-- The normal form, as a geometric formula, is equivalent to the formula in every structure on
a type. -/
theorem realize_iSup_exs_normalForm {M : Type v} [L.Structure M] {n : ℕ}
    (φ : GeometricFormula.{u} L n) (x : Fin n → M) :
    φ.Realize x ↔ (GeometricFormula.iSup fun i => ((normalForm φ).θ i).exs).Realize x := by
  rw [realize_normalForm]
  exact exists_congr fun i => (realize_exs _ x).symm

end GeometricFormula

end LeanPool.ClassifyingTopoi
