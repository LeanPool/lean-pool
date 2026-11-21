/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.Torsors
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Intervals (roadmap 3.4)

The language of intervals (`LeanPool.ClassifyingTopoi.intervalLanguage`: two constants `0`, `1`
and a binary relation `≤`), the theory of intervals (`LeanPool.ClassifyingTopoi.intervalTheory`:
linear orders with a least element `0` and a greatest element `1` distinct) and the generic
interval (`LeanPool.ClassifyingTopoi.genericInterval`), the standard `1`-simplex.

## Main results

* `LeanPool.ClassifyingTopoi.isModel_genericInterval`: the standard `1`-simplex is an interval in
  simplicial sets. The interpretation is computed fiberwise: the `n`-simplices of `Δ[1]` are the
  monotone maps `[n] ⟶ [1]`, ordered pointwise (a pair `a ≤ b` is the image of the `2`-simplex
  `a + b`), which is a linear order with least and greatest elements the constant maps.

## Not formalised

The classification of intervals by simplicial sets (`isClassifyingSite_genericInterval`) is not
formalised. The existence half of Diaconescu's theorem it uses is
`LeanPool.ClassifyingTopoi.exists_leftAdjoint_of_isLocallyFiltering`; missing are the proof that
the functor `[n] ↦ {x₁ ≤ ⋯ ≤ xₙ}` defined by an interval in a sheaf topos is locally filtering,
and the uniqueness part of the universal property.
-/

@[expose] public section

universe u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] Sheaf.instHasColimitsOfShape

/-- **3.4.** The language of intervals: two constants `0` (`false`) and `1` (`true`) and a
binary relation `≤`. -/
def intervalLanguage : FirstOrder.Language.{0, 0} :=
  ⟨fun | 0 => Bool | _ => Empty, fun | 2 => Unit | _ => Empty⟩

/-- **3.4.** The constant `0` (for `false`) or `1` (for `true`). -/
def intervalConst {n : ℕ} (b : Bool) : intervalLanguage.Term (Fin n) :=
  FirstOrder.Language.Term.func (l := 0) (b : intervalLanguage.Functions 0) Fin.elim0

/-- **3.4.** The atomic formula `t ≤ s`. -/
def intervalLE {n : ℕ} (t s : intervalLanguage.Term (Fin n)) :
    GeometricFormula.{u} intervalLanguage n :=
  .rel (k := 2) (() : intervalLanguage.Relations 2) ![t, s]

/-- **3.4.** The theory of intervals: linear orders with a least element `0` and a greatest
element `1` such that `0 = 1 ⊢ ⊥`. -/
def intervalTheory : GeometricTheory.{u} intervalLanguage :=
  {⟨1, .top, intervalLE (.var 0) (.var 0)⟩,
   ⟨3, .and (intervalLE (.var 0) (.var 1)) (intervalLE (.var 1) (.var 2)),
     intervalLE (.var 0) (.var 2)⟩,
   ⟨2, .and (intervalLE (.var 0) (.var 1)) (intervalLE (.var 1) (.var 0)),
     .equal (.var 0) (.var 1)⟩,
   ⟨2, .top, .iSup fun b : ULift.{u} Bool =>
     if b.down then intervalLE (.var 0) (.var 1) else intervalLE (.var 1) (.var 0)⟩,
   ⟨1, .top, .and (intervalLE (intervalConst false) (.var 0))
     (intervalLE (.var 0) (intervalConst true))⟩,
   ⟨0, .equal (intervalConst false) (intervalConst true), .bot⟩}

/-- **3.4.** The Yoneda embedding of the simplex category into simplicial sets. -/
noncomputable abbrev simplexYoneda :
    SimplexCategory ⥤ Sheaf (⊥ : GrothendieckTopology (AsSmall.{u} SimplexCategory)) (Type u) :=
  AsSmall.up ⋙ yoneda ⋙ (sheafBotEquivalence (Type u)).inverse

open Simplicial in
/-- **3.4.** The standard `0`-simplex is terminal among simplicial sets. -/
noncomputable def isTerminalSimplexYonedaZero : IsTerminal (simplexYoneda.{u}.obj ⦋0⦌) :=
  IsTerminal.isTerminalObj (sheafBotEquivalence (Type u)).inverse _
    (IsTerminal.isTerminalObj yoneda _
      (IsTerminal.isTerminalObj
        (AsSmall.equiv : SimplexCategory ≌ AsSmall.{u} SimplexCategory).functor _
        SimplexCategory.isTerminalZero))

open Simplicial in
/-- **3.4.** The generic interval: the standard `1`-simplex `Δ[1]`, with `0` and `1` its two
vertices `δ 1` and `δ 0`, and `≤` the image of `(σ 0, σ 1) : Δ[2] ⟶ Δ[1] × Δ[1]`. -/
noncomputable def genericInterval :
    CatStructure intervalLanguage
      (Sheaf (⊥ : GrothendieckTopology (AsSmall.{u} SimplexCategory)) (Type u)) where
  carrier := simplexYoneda.obj ⦋1⦌
  funMap {k} f := match k, f with
    | 0, b => isTerminalSimplexYonedaZero.from _ ≫
        simplexYoneda.map (SimplexCategory.δ (if (show Bool from b) then 0 else 1))
  relMap {k} R := match k, R with
    | 2, () => Over.mk (Pi.lift fun i : Fin 2 => simplexYoneda.map (SimplexCategory.σ i))

namespace Interval

open Simplicial

/-- The standard `0`-simplex is terminal among presheaves on the simplex category. -/
noncomputable def isTerminalYonedaZero :
    IsTerminal
      (yoneda.obj ((AsSmall.up : SimplexCategory ⥤ AsSmall.{u} SimplexCategory).obj ⦋0⦌)) :=
  IsTerminal.isTerminalObj yoneda _ (IsTerminal.isTerminalObj
    (AsSmall.equiv : SimplexCategory ≌ AsSmall.{u} SimplexCategory).functor _
    SimplexCategory.isTerminalZero)

/-- The vertex `δ 1` (for `false`) or `δ 0` (for `true`) of the standard `1`-simplex. -/
def vertex (b : Bool) : (⦋0⦌ : SimplexCategory) ⟶ ⦋1⦌ :=
  SimplexCategory.δ (if b then 0 else 1)

/-- The constant symbol `0` (for `false`) or `1` (for `true`). -/
def constSymbol (b : Bool) : intervalLanguage.Functions 0 :=
  b

/-- The relation symbol `≤`. -/
def leSymbol : intervalLanguage.Relations 2 :=
  ()

/-- The pair of degeneracies `(σ 0, σ 1) : Δ[2] ⟶ Δ[1] × Δ[1]`. -/
noncomputable def degeneracies :
    yoneda.obj ((AsSmall.up : SimplexCategory ⥤ AsSmall.{u} SimplexCategory).obj ⦋2⦌) ⟶
      ∏ᶜ fun _ : Fin 2 =>
        yoneda.obj ((AsSmall.up : SimplexCategory ⥤ AsSmall.{u} SimplexCategory).obj ⦋1⦌) :=
  Pi.lift fun i : Fin 2 => yoneda.map (AsSmall.up.map (SimplexCategory.σ i))

/-- The generic interval as a structure in the presheaf topos. -/
noncomputable abbrev genericPsh :
    CatStructure intervalLanguage ((AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u) where
  carrier := yoneda.obj (AsSmall.up.obj ⦋1⦌)
  funMap {k} f := match k, f with
    | 0, b => isTerminalYonedaZero.from _ ≫ yoneda.map (AsSmall.up.map (vertex b))
  relMap {k} R := match k, R with
    | 2, () => Over.mk degeneracies

variable {d : (AsSmall.{u} SimplexCategory)ᵒᵖ}

/-- The value of a simplex of `Δ[1]` at a vertex. -/
def val (x : (genericPsh.{u}).carrier.obj d) (j : Fin ((AsSmall.down.obj d.unop).len + 1)) :
    Fin 2 :=
  x.down.toOrderHom j

/-- The value of a simplex of `Δ[1]` composed with a map of the simplex category. -/
theorem val_comp {e : SimplexCategory} (x : (genericPsh.{u}).carrier.obj d)
    (f : (⦋1⦌ : SimplexCategory) ⟶ e) (j : Fin ((AsSmall.down.obj d.unop).len + 1)) :
    (x ≫ AsSmall.up.map f).down.toOrderHom j = f.toOrderHom (val x j) :=
  rfl

/-- Two simplices of `Δ[1]` with the same values are equal. -/
theorem ext_val {x y : (genericPsh.{u}).carrier.obj d} (h : ∀ j, val x j = val y j) : x = y :=
  ULift.ext (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext h)))

/-- The constants of the fibers of the generic interval are the constant simplices. -/
theorem val_funMap (b : Bool) (x : Fin 0 → (genericPsh.{u}).carrier.obj d)
    (j : Fin ((AsSmall.down.obj d.unop).len + 1)) :
    val (@Structure.funMap _ _ ((genericPsh.{u}).fiberStr d) 0 (constSymbol b) x) j =
      if b then 1 else 0 := by
  rw [CatStructure.fiberStr_funMap]
  have key : ∀ k : Fin 1, (vertex b).toOrderHom k = if b then 1 else 0 := fun k => by
    rw [Subsingleton.elim k 0]
    cases b <;> rfl
  exact key _

/-- The `2`-simplex `a + b` of a pair `a ≤ b` of maps `[n] ⟶ [1]`. -/
def sumHom {n : SimplexCategory} (a b : n ⟶ ⦋1⦌) : n ⟶ ⦋2⦌ :=
  SimplexCategory.Hom.mk (⟨fun j => (⟨(a.toOrderHom j).val + (b.toOrderHom j).val, by
      have h₁ : (a.toOrderHom j).val < 2 := (a.toOrderHom j).isLt
      have h₂ : (b.toOrderHom j).val < 2 := (b.toOrderHom j).isLt
      omega⟩ : Fin 3), fun j j' h => by
      have h₁ : a.toOrderHom j ≤ a.toOrderHom j' := a.toOrderHom.monotone h
      have h₂ : b.toOrderHom j ≤ b.toOrderHom j' := b.toOrderHom.monotone h
      rw [Fin.le_iff_val_le_val] at h₁ h₂ ⊢
      dsimp only
      omega⟩ : Fin (n.len + 1) →o Fin 3)

/-- The degeneracies of the `2`-simplex `a + b` are `a` and `b`. -/
theorem sigma_sum (a b : Fin 2) (h : a ≤ b) :
    (SimplexCategory.σ (n := 1) 0).toOrderHom
        ⟨a.val + b.val, show a.val + b.val < 3 by omega⟩ = a ∧
      (SimplexCategory.σ (n := 1) 1).toOrderHom
        ⟨a.val + b.val, show a.val + b.val < 3 by omega⟩ = b := by
  revert a b
  decide

/-- The components of the image of a `2`-simplex in `Δ[1] × Δ[1]`. -/
theorem secEquiv_degeneracies
    (c : (yoneda.obj ((AsSmall.up : SimplexCategory ⥤ AsSmall.{u} SimplexCategory).obj
      ⦋2⦌)).obj d) (i : Fin 2) :
    Syntactic.secEquiv (genericPsh.{u}).carrier 2 d (degeneracies.app d c) i =
      c ≫ AsSmall.up.map (SimplexCategory.σ i) := by
  rw [Syntactic.secEquiv_apply]
  change (degeneracies ≫ Pi.π (fun _ : Fin 2 =>
    yoneda.obj ((AsSmall.up : SimplexCategory ⥤ AsSmall.{u} SimplexCategory).obj ⦋1⦌)) i).app d
      c = _
  rw [degeneracies, Pi.lift_comp_π]
  rfl

/-- The relation `≤` on the fibers of the generic interval is the pointwise order. -/
theorem relMap_iff (x : Fin 2 → (genericPsh.{u}).carrier.obj d) :
    @Structure.RelMap _ _ ((genericPsh.{u}).fiberStr d) 2 leSymbol x ↔
      ∀ j, val (x 0) j ≤ val (x 1) j := by
  rw [CatStructure.fiberStr_relMap]
  constructor
  · rintro ⟨(c : (yoneda.obj ((AsSmall.up : SimplexCategory ⥤ AsSmall.{u} SimplexCategory).obj
      ⦋2⦌)).obj d), hc⟩ j
    have h₀ := congrArg (fun z => Syntactic.secEquiv _ 2 d z 0) hc
    have h₁ := congrArg (fun z => Syntactic.secEquiv _ 2 d z 1) hc
    simp only [Equiv.apply_symm_apply] at h₀ h₁
    rw [← h₀, ← h₁]
    change val ((Syntactic.secEquiv _ 2 d) (degeneracies.app d c) 0) j ≤
      val ((Syntactic.secEquiv _ 2 d) (degeneracies.app d c) 1) j
    rw [secEquiv_degeneracies, secEquiv_degeneracies]
    change (SimplexCategory.σ 0).toOrderHom (c.down.toOrderHom j) ≤
      (SimplexCategory.σ 1).toOrderHom (c.down.toOrderHom j)
    generalize c.down.toOrderHom j = k
    revert k
    decide
  · intro h
    refine ⟨⟨sumHom (x 0).down (x 1).down⟩, (Syntactic.secEquiv _ 2 d).injective ?_⟩
    rw [Equiv.apply_symm_apply]
    funext i
    change (Syntactic.secEquiv _ 2 d) (degeneracies.app d _) i = _
    rw [secEquiv_degeneracies]
    refine ext_val fun j => ?_
    have hj := h j
    unfold val at hj ⊢
    change (SimplexCategory.σ i).toOrderHom ((sumHom (x 0).down (x 1).down).toOrderHom j) = _
    match i with
    | 0 => exact (sigma_sum _ _ hj).1
    | 1 => exact (sigma_sum _ _ hj).2

/-- The atomic formula `t ≤ s` in the fibers of the generic interval. -/
theorem realize_intervalLE {n : ℕ} (t s : intervalLanguage.Term (Fin n))
    (x : Fin n → (genericPsh.{u}).carrier.obj d) :
    @GeometricFormula.Realize _ _ ((genericPsh.{u}).fiberStr d) _ (intervalLE.{u} t s) x ↔
      ∀ j, val (@Term.realize _ _ ((genericPsh.{u}).fiberStr d) _ x t) j ≤
        val (@Term.realize _ _ ((genericPsh.{u}).fiberStr d) _ x s) j :=
  relMap_iff _

/-- The constants in the fibers of the generic interval. -/
theorem val_realize_intervalConst {n : ℕ} (b : Bool) (x : Fin n → (genericPsh.{u}).carrier.obj d)
    (j : Fin ((AsSmall.down.obj d.unop).len + 1)) :
    val (@Term.realize _ _ ((genericPsh.{u}).fiberStr d) _ x (intervalConst b)) j =
      if b then 1 else 0 :=
  val_funMap b _ j

/-- The values of a simplex of `Δ[1]` are monotone. -/
theorem val_mono (x : (genericPsh.{u}).carrier.obj d) : Monotone (val x) :=
  x.down.toOrderHom.monotone

/-- The fibers of the generic interval are intervals. -/
theorem isSetModel_fiberStr (d : (AsSmall.{u} SimplexCategory)ᵒᵖ) :
    letI := (genericPsh.{u}).fiberStr d
    intervalTheory.{u}.IsSetModel ((genericPsh.{u}).carrier.obj d) := by
  let := (genericPsh.{u}).fiberStr d
  intro σ hσ
  simp only [intervalTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · intro (x : Fin 1 → (genericPsh.{u}).carrier.obj d) _
    exact (realize_intervalLE _ _ x).2 fun j => le_rfl
  · intro (x : Fin 3 → (genericPsh.{u}).carrier.obj d) ⟨h₁, h₂⟩
    rw [realize_intervalLE] at h₁ h₂ ⊢
    exact fun j => (h₁ j).trans (h₂ j)
  · intro (x : Fin 2 → (genericPsh.{u}).carrier.obj d) ⟨h₁, h₂⟩
    rw [realize_intervalLE] at h₁ h₂
    exact ext_val fun j => le_antisymm (h₁ j) (h₂ j)
  · intro (x : Fin 2 → (genericPsh.{u}).carrier.obj d) _
    by_cases h : ∀ j, val (x 0) j ≤ val (x 1) j
    · exact ⟨⟨true⟩, (realize_intervalLE _ _ x).2 h⟩
    · refine ⟨⟨false⟩, (realize_intervalLE _ _ x).2 fun j => ?_⟩
      push Not at h
      obtain ⟨j₀, hj₀⟩ := h
      change val (x 1) j ≤ val (x 0) j
      rcases le_total j j₀ with hj | hj
      · have := val_mono (x 1) hj
        rw [Fin.lt_def] at hj₀
        rw [Fin.le_iff_val_le_val] at this ⊢
        omega
      · have := val_mono (x 0) hj
        have h₁ := (val (x 1) j).isLt
        rw [Fin.lt_def] at hj₀
        rw [Fin.le_iff_val_le_val] at this ⊢
        omega
  · intro (x : Fin 1 → (genericPsh.{u}).carrier.obj d) _
    refine ⟨(realize_intervalLE _ _ x).2 fun j => ?_, (realize_intervalLE _ _ x).2 fun j => ?_⟩
    · rw [val_realize_intervalConst]
      exact Fin.zero_le _
    · rw [val_realize_intervalConst]
      exact Fin.le_last _
  · intro (x : Fin 0 → (genericPsh.{u}).carrier.obj d) hx
    have := congrArg (fun y => val y 0) hx
    dsimp only at this
    rw [val_realize_intervalConst, val_realize_intervalConst] at this
    exact absurd this (by decide)

/-- The generic interval in the presheaf topos is a model of the theory of intervals. -/
theorem isModel_genericPsh : (genericPsh.{u}).IsModel intervalTheory.{u} :=
  CatStructure.isModel_of_forall_fiberStr _ isSetModel_fiberStr

/-- The constants of the generic interval, through the inclusion of presheaves as sheaves. -/
theorem genericPsh_map_funMap_constSymbol (b : Bool) :
    ((genericPsh.{u}).map (sheafBotEquivalence (Type u)).inverse).funMap (constSymbol b) =
      (genericInterval.{u}).funMap (constSymbol b) :=
  (congrArg _ ((sheafBotEquivalence (Type u)).inverse.map_comp _ _)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ simplexYoneda.map (vertex b)) (isTerminalSimplexYonedaZero.hom_ext _ _)))

/-- The function symbols of the generic interval, through the inclusion of presheaves as
sheaves. -/
theorem genericPsh_map_funMap {k : ℕ} (f : intervalLanguage.Functions k) :
    ((genericPsh.{u}).map (sheafBotEquivalence (Type u)).inverse).funMap f =
      (genericInterval.{u}).funMap f :=
  match k, f with
  | 0, b => genericPsh_map_funMap_constSymbol b
  | _ + 1, f => Empty.elim f

/-- The relation of the generic interval, through the inclusion of presheaves as sheaves. -/
theorem genericPsh_map_relMap_leSymbol :
    ((genericPsh.{u}).map (sheafBotEquivalence (Type u)).inverse).relMap leSymbol =
      (genericInterval.{u}).relMap leSymbol :=
  congrArg Over.mk (map_lift_piComparison _ _ _ _)

end Interval

/-- **3.4.** The standard `1`-simplex is an interval in simplicial sets. -/
theorem isModel_genericInterval : (genericInterval.{u}).IsModel intervalTheory.{u} := by
  have h := (Interval.isModel_genericPsh.{u}).map_of_preserves
    (sheafBotEquivalence (Type u)).inverse
  have key : ∀ {k : ℕ} (R : intervalLanguage.Relations k),
      ((Interval.genericPsh.{u}).map (sheafBotEquivalence (Type u)).inverse).relMap R =
        (genericInterval.{u}).relMap R := fun {k} R =>
    match k, R with
    | 2, () => Interval.genericPsh_map_relMap_leSymbol
    | 0, R => Empty.elim R
    | 1, R => Empty.elim R
    | _ + 3, R => Empty.elim R
  refine (show ((Interval.genericPsh.{u}).map (sheafBotEquivalence (Type u)).inverse).Isomorphic
    genericInterval.{u} from ⟨Iso.refl _, ⟨fun f => ?_, fun R => ?_⟩,
      ⟨fun f => ?_, fun R => ?_⟩⟩).isModel h
  · exact (Category.comp_id _).trans ((Interval.genericPsh_map_funMap f).trans
      ((Category.id_comp _).symm.trans (congrArg (· ≫ _) Limits.Pi.map_id.symm)))
  · rw [key]
    exact (CatStructure.IsHom.id _).relMap R
  · exact (Category.comp_id _).trans ((Interval.genericPsh_map_funMap f).symm.trans
      ((Category.id_comp _).symm.trans (congrArg (· ≫ _) Limits.Pi.map_id.symm)))
  · rw [key]
    exact (CatStructure.IsHom.id _).relMap R

end LeanPool.ClassifyingTopoi
