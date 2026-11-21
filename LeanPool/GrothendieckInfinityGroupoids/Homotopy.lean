/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckInfinityGroupoids.Extension
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Structural operations, the homotopy relation and weak equivalences (roadmap 3.2, 4.1, 4.3)

For a pseudo-coherator `C` and a presheaf `X` on `C`, the `n`-cells of `X` are `X(D_n)`; two
`n`-cells are homotopic, `a ∼_n b`, when some `(n+1)`-cell goes from `a` to `b` (D. Ara, « On the
homotopy theory of Grothendieck ∞-groupoids », J. Pure Appl. Algebra 217 (2013), 1237–1278, 4.2).
Weak equivalences are the morphisms inducing bijections on `π₀` and on every `π_{n+1}(X, x)` at a
`0`-cell `x`, the `(n+1)`-cells from the iterated identity `1^n_x` to itself modulo `∼_{n+1}`
(Ara 2013, 4.11 and 4.17).

The structural operations of roadmap 3.2 come from liftings of admissible pairs: the identity
`1_a` from the lifting of `(1_{D_n}, 1_{D_n})` carried by the pseudo-coherator, the inverse from a
lifting of `(τ_n, σ_n)`, and the composite from a lifting on the globular sum `D_{n+1} ⊔_{D_n}
D_{n+1}` (Ara 2013, 3.2–3.5). With them, `∼_n` is an equivalence relation on the `n`-cells of an
∞-groupoid of type `C` (`cellJoined_equivalence`, part of Ara 2013, Lemma 4.3), identities are
weak equivalences (`isWeakEquivalence_id`), and weak equivalences between ∞-groupoids compose
(`IsWeakEquivalence.comp`).
-/

@[expose] public section

namespace LeanPool.GrothendieckInfinityGroupoids

open CategoryTheory Limits Opposite

universe u v w

namespace GlobularExtension

variable (C : GlobularExtension)

/-- The `n`-cells `X(D_n)` of a presheaf on `C`. -/
abbrev Cell (X : C.Objᵒᵖ ⥤ Type w) (n : ℕ) : Type w := X.obj (op (C.disks.disk n))

/-- The source of an `(n+1)`-cell. -/
abbrev cellSrc (X : C.Objᵒᵖ ⥤ Type w) (n : ℕ) : C.Cell X (n + 1) → C.Cell X n :=
  fun a => X.map (C.disks.σ n).op a

/-- The target of an `(n+1)`-cell. -/
abbrev cellTgt (X : C.Objᵒᵖ ⥤ Type w) (n : ℕ) : C.Cell X (n + 1) → C.Cell X n :=
  fun a => X.map (C.disks.τ n).op a

/-- **Roadmap 4.1.** Two `n`-cells are homotopic, `a ∼_n b`: some `(n+1)`-cell goes from `a` to `b`
(Ara 2013, 4.2). -/
def CellJoined (X : C.Objᵒᵖ ⥤ Type w) (n : ℕ) (a b : C.Cell X n) : Prop :=
  ∃ h : C.Cell X (n + 1), C.cellSrc X n h = a ∧ C.cellTgt X n h = b

/-- `φ` induces a bijection `π₀ X → π₀ Y`, written out on `0`-cells modulo `∼₀` (Ara 2013, 4.11). -/
def BijectiveOnComponents {X Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) : Prop :=
  (∀ y : C.Cell Y 0, ∃ x : C.Cell X 0, C.CellJoined Y 0 (φ.app _ x) y) ∧
    ∀ x x' : C.Cell X 0, C.CellJoined Y 0 (φ.app _ x) (φ.app _ x') → C.CellJoined X 0 x x'

/-- `φ` induces a bijection `π_{n+1}(X, u) → π_{n+1}(Y, φ u)` for an `n`-cell `u`, where
`π_{n+1}(X, u)` is the set of `(n+1)`-cells from `u` to `u` modulo `∼_{n+1}` (Ara 2013, 4.11). -/
def BijectiveOnLoops {X Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) (n : ℕ) (u : C.Cell X n) : Prop :=
  (∀ β : C.Cell Y (n + 1), C.cellSrc Y n β = φ.app _ u → C.cellTgt Y n β = φ.app _ u →
      ∃ α : C.Cell X (n + 1), C.cellSrc X n α = u ∧ C.cellTgt X n α = u ∧
        C.CellJoined Y (n + 1) (φ.app _ α) β) ∧
    ∀ α α' : C.Cell X (n + 1), C.cellSrc X n α = u → C.cellTgt X n α = u →
      C.cellSrc X n α' = u → C.cellTgt X n α' = u →
      C.CellJoined Y (n + 1) (φ.app _ α) (φ.app _ α') → C.CellJoined X (n + 1) α α'

end GlobularExtension

namespace PseudoCoherator

variable (C : PseudoCoherator)

/-- **Roadmap 3.2.** The structural map `D_{n+1} ⟶ D_n` of identities: the chosen lifting `idLift n`
of the admissible pair `(1_{D_n}, 1_{D_n})`. -/
def identityMap (n : ℕ) : C.disks.disk (n + 1) ⟶ C.disks.disk n :=
  C.idLift n ≫ eqToHom (C.ofTable_globe n)

/-- **Roadmap 4.1.** The iterated identity `1^n_x` of a `0`-cell `x` (Ara's `k⁰_n(x)`, 2013,
4.11). -/
noncomputable def iteratedIdentity (X : C.Objᵒᵖ ⥤ Type w) : (n : ℕ) → C.Cell X 0 → C.Cell X n
  | 0, x => x
  | n + 1, x => X.map (C.identityMap n).op (iteratedIdentity X n x)

/-- **Roadmap 4.3.** Weak equivalences (Ara 2013, 4.17): a bijection on `π₀` and on every
`π_{n+1}(X, x) = π_{n+1}(X, 1^n_x)`. Since `φ` commutes with the structural maps,
`φ (1^n_x) = 1^n_{φ x}`, so the target loops are Ara's. -/
def IsWeakEquivalence {X Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) : Prop :=
  C.BijectiveOnComponents φ ∧
    ∀ (n : ℕ) (x : C.Cell X 0), C.BijectiveOnLoops φ n (C.iteratedIdentity X n x)

/-- **Roadmap 7.1.** The class `W_C` of weak equivalences, on presheaves; `W_C` on `∞-Gpd_C` is its
inverse image under the inclusion. -/
def weakEquivalences : MorphismProperty (C.Objᵒᵖ ⥤ Type w) := fun _ _ φ => C.IsWeakEquivalence φ

end PseudoCoherator


namespace CoglobularObject

variable {K : Type u} [Category.{v} K] (D : CoglobularObject K)

/-- The face `D_n ⟶ D_{n+1}` of side `ε` is `σ_n` or `τ_n`. -/
theorem faceTo_succ (n : ℕ) (ε : Bool) (h : n < n + 1) :
    D.faceTo h ε = if ε then D.τ n else D.σ n := by
  unfold faceTo
  suffices H : ∀ k (_ : k = 0) (e : D.disk (n + k + 1) = D.disk (n + 1)),
      D.face n k ε ≫ eqToHom e = if ε then D.τ n else D.σ n from H _ (by omega) _
  rintro k rfl e
  cases ε <;> simp [face]

end CoglobularObject

/-- The table `(n + 1, n, n + 1)` of two `(n+1)`-disks glued along an `n`-disk. -/
abbrev Table.pair (n : ℕ) : Table where
  width := 1
  top := fun _ => n + 1
  bot := fun _ => n
  bot_lt_left := fun _ => Nat.lt_succ_self n
  bot_lt_right := fun _ => Nat.lt_succ_self n

theorem Table.dim_pair (n : ℕ) : (Table.pair n).dim ≤ n + 1 :=
  Finset.sup_le fun _ _ => le_rfl

theorem Table.dim_globe (n : ℕ) : (Table.globe n).dim ≤ n :=
  Finset.sup_le fun _ _ => le_rfl

namespace GlobularExtension

variable (C : GlobularExtension.{u, v}) (X : C.Objᵒᵖ ⥤ Type w)

/-- The two inclusions into the sum `D_{n+1} ⊔_{D_n} D_{n+1}` agree on the gluing disk. -/
theorem σ_incl_pair (n : ℕ) :
    C.disks.σ n ≫ C.incl (Table.pair n) 0 = C.disks.τ n ≫ C.incl (Table.pair n) 1 := by
  have := C.sums.incl_compatible (Table.pair n) ⟨0, Nat.zero_lt_one⟩
  rw [CoglobularObject.faceTo_succ, CoglobularObject.faceTo_succ] at this
  exact this

theorem cellSrc_map (n : ℕ) {S : C.Obj} (f : C.disks.disk (n + 1) ⟶ S) (a : X.obj (op S)) :
    C.cellSrc X n (X.map f.op a) = X.map (C.disks.σ n ≫ f).op a := by
  simp [cellSrc]

theorem cellTgt_map (n : ℕ) {S : C.Obj} (f : C.disks.disk (n + 1) ⟶ S) (a : X.obj (op S)) :
    C.cellTgt X n (X.map f.op a) = X.map (C.disks.τ n ≫ f).op a := by
  simp [cellTgt]

variable {C X} in
/-- Morphisms of presheaves preserve sources. -/
theorem cellSrc_app {Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) (n : ℕ) (a : C.Cell X (n + 1)) :
    C.cellSrc Y n (φ.app _ a) = φ.app _ (C.cellSrc X n a) :=
  (NatTrans.naturality_apply φ _ a).symm

variable {C X} in
/-- Morphisms of presheaves preserve targets. -/
theorem cellTgt_app {Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) (n : ℕ) (a : C.Cell X (n + 1)) :
    C.cellTgt Y n (φ.app _ a) = φ.app _ (C.cellTgt X n a) :=
  (NatTrans.naturality_apply φ _ a).symm

variable {C X} in
/-- Morphisms of presheaves preserve the homotopy relation. -/
theorem CellJoined.map {Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) {n : ℕ} {a b : C.Cell X n}
    (h : C.CellJoined X n a b) : C.CellJoined Y n (φ.app _ a) (φ.app _ b) := by
  obtain ⟨c, rfl, rfl⟩ := h
  exact ⟨φ.app _ c, cellSrc_app φ n c, cellTgt_app φ n c⟩

end GlobularExtension

namespace PseudoCoherator

variable (C : PseudoCoherator.{u, v}) (X : C.Objᵒᵖ ⥤ Type w)

/-- The identity map is a retraction of the source inclusion. -/
theorem σ_identityMap (n : ℕ) : C.disks.σ n ≫ C.identityMap n = 𝟙 _ := by
  have h : C.disks.σ n ≫ C.idLift n = eqToHom (C.ofTable_globe n).symm := (C.isLifting_idLift n).1
  change C.disks.σ n ≫ C.idLift n ≫ eqToHom (C.ofTable_globe n) = _
  rw [← Category.assoc, h, eqToHom_trans, eqToHom_refl]

/-- The identity map is a retraction of the target inclusion. -/
theorem τ_identityMap (n : ℕ) : C.disks.τ n ≫ C.identityMap n = 𝟙 _ := by
  have h : C.disks.τ n ≫ C.idLift n = eqToHom (C.ofTable_globe n).symm := (C.isLifting_idLift n).2
  change C.disks.τ n ≫ C.idLift n ≫ eqToHom (C.ofTable_globe n) = _
  rw [← Category.assoc, h, eqToHom_trans, eqToHom_refl]

/-- **Roadmap 3.2.** The identity `1_a` of an `n`-cell `a`. -/
def idCell {n : ℕ} (a : C.Cell X n) : C.Cell X (n + 1) := X.map (C.identityMap n).op a

/-- **Roadmap 3.2.** `1_a` goes from `a` to `a`. -/
theorem cellSrc_idCell {n : ℕ} (a : C.Cell X n) : C.cellSrc X n (C.idCell X a) = a := by
  rw [idCell, GlobularExtension.cellSrc_map, σ_identityMap]
  simp

theorem cellTgt_idCell {n : ℕ} (a : C.Cell X n) : C.cellTgt X n (C.idCell X a) = a := by
  rw [idCell, GlobularExtension.cellTgt_map, τ_identityMap]
  simp

/-- The admissible pair `(τ_n, σ_n) : D_n ⟶ D_{n+1}`, whose liftings give the inverses. -/
abbrev invPair (n : ℕ) : C.AdmissiblePair where
  n := n
  T := Table.globe (n + 1)
  dim_le := Table.dim_globe (n + 1)
  f := C.disks.τ n ≫ eqToHom (C.ofTable_globe (n + 1)).symm
  g := C.disks.σ n ≫ eqToHom (C.ofTable_globe (n + 1)).symm
  parallel := by
    cases n with
    | zero => trivial
    | succ m =>
      refine ⟨?_, ?_⟩
      · rw [← Category.assoc, ← Category.assoc, C.disks.σ_σ]
      · rw [← Category.assoc, ← Category.assoc, C.disks.τ_σ]

/-- The admissible pair `(σ_n ≫ ε₂, τ_n ≫ ε₁) : D_n ⟶ D_{n+1} ⊔_{D_n} D_{n+1}`, whose liftings
give the compositions (Ara 2013, 3.2 and 3.4). -/
abbrev compPair (n : ℕ) : C.AdmissiblePair where
  n := n
  T := Table.pair n
  dim_le := Table.dim_pair n
  f := C.disks.σ n ≫ C.incl (Table.pair n) 1
  g := C.disks.τ n ≫ C.incl (Table.pair n) 0
  parallel := by
    cases n with
    | zero => trivial
    | succ m =>
      have hc := C.σ_incl_pair (m + 1)
      refine ⟨?_, ?_⟩
      · rw [← Category.assoc, C.disks.σ_σ, Category.assoc, ← hc, ← Category.assoc,
          C.disks.σ_σ, Category.assoc]
      · rw [← Category.assoc, C.disks.τ_σ, Category.assoc, ← hc, ← Category.assoc,
          C.disks.τ_σ, Category.assoc]

/-- **Roadmap 3.2.** Every `(n+1)`-cell has an inverse, going from its target to its source. -/
theorem exists_inverse {n : ℕ} (c : C.Cell X (n + 1)) :
    ∃ c' : C.Cell X (n + 1), C.cellSrc X n c' = C.cellTgt X n c ∧
      C.cellTgt X n c' = C.cellSrc X n c := by
  obtain ⟨h, h₁, h₂⟩ := C.contractible (C.invPair n)
  let h' : C.disks.disk (n + 1) ⟶ C.disks.disk (n + 1) := h ≫ eqToHom (C.ofTable_globe (n + 1))
  have e₁ : C.disks.σ n ≫ h' = C.disks.τ n := by
    have : C.disks.σ n ≫ h = C.disks.τ n ≫ eqToHom (C.ofTable_globe (n + 1)).symm := h₁
    change C.disks.σ n ≫ h ≫ _ = _
    rw [← Category.assoc, this, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have e₂ : C.disks.τ n ≫ h' = C.disks.σ n := by
    have : C.disks.τ n ≫ h = C.disks.σ n ≫ eqToHom (C.ofTable_globe (n + 1)).symm := h₂
    change C.disks.τ n ≫ h ≫ _ = _
    rw [← Category.assoc, this, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine ⟨X.map h'.op c, ?_, ?_⟩
  · rw [GlobularExtension.cellSrc_map, e₁]
  · rw [GlobularExtension.cellTgt_map, e₂]

/-- **Roadmap 3.2.** In an ∞-groupoid of type `C`, an `(n+1)`-cell `u` from `a` to `b` and an
`(n+1)`-cell `v` from `b` to `c` have a composite, from `a` to `c` (Ara 2013, 3.2). -/
theorem exists_comp (hX : IsGlobularPresheaf C.toGlobularExtension X) {n : ℕ}
    (u v : C.Cell X (n + 1)) (huv : C.cellTgt X n u = C.cellSrc X n v) :
    ∃ w : C.Cell X (n + 1), C.cellSrc X n w = C.cellSrc X n u ∧
      C.cellTgt X n w = C.cellTgt X n v := by
  obtain ⟨h, h₁, h₂⟩ := C.contractible (C.compPair n)
  let fam : ∀ k : Fin ((Table.pair n).width + 1),
      X.obj (op (C.disks.disk ((Table.pair n).top k))) := fun k => if k = 0 then v else u
  have hfam : ∀ j : Fin (Table.pair n).width,
      X.map (C.disks.faceTo ((Table.pair n).bot_lt_left j) false).op (fam j.castSucc) =
        X.map (C.disks.faceTo ((Table.pair n).bot_lt_right j) true).op (fam j.succ) := by
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [CoglobularObject.faceTo_succ, CoglobularObject.faceTo_succ]
    simp only [fam, Fin.castSucc_zero, Fin.succ_zero_eq_one, ↓reduceIte, Bool.false_eq_true,
      one_ne_zero]
    exact huv.symm
  obtain ⟨s, hs, -⟩ := hX (Table.pair n) fam hfam
  let h' : C.disks.disk (n + 1) ⟶ C.ofTable (Table.pair n) := h
  have e₁ : C.disks.σ n ≫ h' = C.disks.σ n ≫ C.incl (Table.pair n) 1 := h₁
  have e₂ : C.disks.τ n ≫ h' = C.disks.τ n ≫ C.incl (Table.pair n) 0 := h₂
  refine ⟨X.map h'.op s, ?_, ?_⟩
  · rw [GlobularExtension.cellSrc_map, e₁, op_comp, Functor.map_comp]
    change X.map (C.disks.σ n).op (X.map (C.incl (Table.pair n) 1).op s) = _
    rw [hs 1]
    rfl
  · rw [GlobularExtension.cellTgt_map, e₂, op_comp, Functor.map_comp]
    change X.map (C.disks.τ n).op (X.map (C.incl (Table.pair n) 0).op s) = _
    rw [hs 0]
    rfl

variable {C X}

theorem cellJoined_refl {n : ℕ} (a : C.Cell X n) : C.CellJoined X n a a :=
  ⟨C.idCell X a, C.cellSrc_idCell X a, C.cellTgt_idCell X a⟩

theorem cellJoined_symm {n : ℕ} {a b : C.Cell X n} (h : C.CellJoined X n a b) :
    C.CellJoined X n b a := by
  obtain ⟨c, rfl, rfl⟩ := h
  obtain ⟨c', h₁, h₂⟩ := C.exists_inverse X c
  exact ⟨c', h₁, h₂⟩

theorem cellJoined_trans (hX : IsGlobularPresheaf C.toGlobularExtension X) {n : ℕ}
    {a b c : C.Cell X n} (h₁ : C.CellJoined X n a b) (h₂ : C.CellJoined X n b c) :
    C.CellJoined X n a c := by
  obtain ⟨u, rfl, rfl⟩ := h₁
  obtain ⟨v, hv, rfl⟩ := h₂
  obtain ⟨w, hw₁, hw₂⟩ := C.exists_comp X hX u v hv.symm
  exact ⟨w, hw₁, hw₂⟩

/-- **Roadmap 4.1.** On the `n`-cells of an ∞-groupoid of type `C`, the homotopy relation `∼_n` is
an equivalence relation (part of Ara 2013, Lemma 4.3). -/
theorem cellJoined_equivalence (hX : IsGlobularPresheaf C.toGlobularExtension X) (n : ℕ) :
    Equivalence (C.CellJoined X n) :=
  ⟨cellJoined_refl, cellJoined_symm, cellJoined_trans hX⟩

/-- Morphisms of presheaves commute with the iterated identities. -/
theorem app_iteratedIdentity {Y : C.Objᵒᵖ ⥤ Type w} (φ : X ⟶ Y) (x : C.Cell X 0) :
    ∀ n, φ.app _ (C.iteratedIdentity X n x) = C.iteratedIdentity Y n (φ.app _ x)
  | 0 => rfl
  | n + 1 => by
    rw [iteratedIdentity, iteratedIdentity, ← app_iteratedIdentity φ x n]
    exact NatTrans.naturality_apply φ _ _

/-- **Roadmap 4.3.** Identities are weak equivalences. -/
theorem isWeakEquivalence_id : C.IsWeakEquivalence (𝟙 X) := by
  refine ⟨⟨fun y => ⟨y, cellJoined_refl y⟩, fun x x' h => h⟩, fun n x => ⟨fun β h₁ h₂ =>
    ⟨β, h₁, h₂, cellJoined_refl β⟩, fun α α' _ _ _ _ h => h⟩⟩

theorem bijectiveOnComponents_comp {Y Z : C.Objᵒᵖ ⥤ Type w}
    (hZ : IsGlobularPresheaf C.toGlobularExtension Z) {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    (hφ : C.BijectiveOnComponents φ) (hψ : C.BijectiveOnComponents ψ) :
    C.BijectiveOnComponents (φ ≫ ψ) := by
  refine ⟨fun z => ?_, fun x x' h => hφ.2 x x' (hψ.2 _ _ h)⟩
  obtain ⟨y, hy⟩ := hψ.1 z
  obtain ⟨x, hx⟩ := hφ.1 y
  exact ⟨x, cellJoined_trans hZ (hx.map ψ) hy⟩

theorem bijectiveOnLoops_comp {Y Z : C.Objᵒᵖ ⥤ Type w}
    (hZ : IsGlobularPresheaf C.toGlobularExtension Z) {φ : X ⟶ Y} {ψ : Y ⟶ Z} {n : ℕ}
    {u : C.Cell X n} (hφ : C.BijectiveOnLoops φ n u) (hψ : C.BijectiveOnLoops ψ n (φ.app _ u)) :
    C.BijectiveOnLoops (φ ≫ ψ) n u := by
  refine ⟨fun β h₁ h₂ => ?_, fun α α' h₁ h₂ h₁' h₂' h => ?_⟩
  · obtain ⟨α', hα'₁, hα'₂, hα'⟩ := hψ.1 β h₁ h₂
    obtain ⟨α, hα₁, hα₂, hα⟩ := hφ.1 α' hα'₁ hα'₂
    exact ⟨α, hα₁, hα₂, cellJoined_trans hZ (hα.map ψ) hα'⟩
  · refine hφ.2 α α' h₁ h₂ h₁' h₂' (hψ.2 _ _ ?_ ?_ ?_ ?_ h)
    · rw [GlobularExtension.cellSrc_app, h₁]
    · rw [GlobularExtension.cellTgt_app, h₂]
    · rw [GlobularExtension.cellSrc_app, h₁']
    · rw [GlobularExtension.cellTgt_app, h₂']

/-- **Roadmap 4.3.** Weak equivalences towards an ∞-groupoid of type `C` compose. -/
theorem IsWeakEquivalence.comp {Y Z : C.Objᵒᵖ ⥤ Type w}
    (hZ : IsGlobularPresheaf C.toGlobularExtension Z) {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    (hφ : C.IsWeakEquivalence φ) (hψ : C.IsWeakEquivalence ψ) :
    C.IsWeakEquivalence (φ ≫ ψ) := by
  refine ⟨bijectiveOnComponents_comp hZ hφ.1 hψ.1, fun n x => ?_⟩
  refine bijectiveOnLoops_comp hZ (hφ.2 n x) ?_
  rw [app_iteratedIdentity]
  exact hψ.2 n (φ.app _ x)

/-- **Roadmap 4.3.** The constant presheaf with value `Bool` is an ∞-groupoid of type `C`, and its
map to the terminal one is not a weak equivalence: `π₀` has two elements. -/
theorem not_isWeakEquivalence_const_bool :
    IsGlobularPresheaf C.toGlobularExtension ((Functor.const _).obj (ULift.{w} Bool)) ∧
      ¬ C.IsWeakEquivalence
        (((Functor.const _).map (TypeCat.ofHom fun _ => PUnit.unit)) :
          (Functor.const C.Objᵒᵖ).obj (ULift.{w} Bool) ⟶ (Functor.const _).obj PUnit.{w + 1}) := by
  refine ⟨fun T v hv => ⟨v 0, fun k => ?_, fun a ha => ha 0⟩, fun h => ?_⟩
  · change v 0 = v k
    induction k using Fin.induction with
    | zero => rfl
    | succ j ih => exact ih.trans (hv j)
  · obtain ⟨c, hc₁, hc₂⟩ := h.1.2 ⟨false⟩ ⟨true⟩ ⟨PUnit.unit, rfl, rfl⟩
    exact Bool.false_ne_true (congrArg ULift.down (hc₁.symm.trans hc₂))

end PseudoCoherator

end LeanPool.GrothendieckInfinityGroupoids
