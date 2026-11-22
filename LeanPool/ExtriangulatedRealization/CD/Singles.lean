/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Exact

/-!
# Single objects of `C(D)`

The single objects `X`, `Y`, `A i`, `P i` of `C(D)`, the morphisms between them used in the
manuscript (`u : X → A j` for `u ∈ D_j`, and `a_{ji}`, `b_i`, `c_i`, `p_{ji}`), the value of `ρ`
on them, and realizations of short exact sequences between objects without copies of `X`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

attribute [local instance] HasExt.standard

/-- The value of `ρ` on a single object. -/
noncomputable def rhoSingleIso (l : IndCat D) : (rho D).obj (single D l) ≅ (rho0 D).obj l :=
  (Mat_.embeddingLiftIso (𝟭 (Rep k I))).app ((rho0 D).obj l)

lemma rhoSingleIso_hom_naturality {l l' : IndCat D} (f : l ⟶ l') :
    (rho D).map ((Mat_.embedding _).map f) ≫ (rhoSingleIso D l').hom =
      (rhoSingleIso D l).hom ≫ (rho0 D).map f :=
  (Mat_.embeddingLiftIso (𝟭 (Rep k I))).hom.naturality ((rho0 D).map f)

/-- An object of `C(D)` without copies of `X`. -/
def XFree (M : CD D) : Prop := ∀ i, (M.X i).isSome

lemma isZero_xPart {M : CD D} (hM : XFree D M) : IsZero (xPart D M) := by
  have : IsEmpty (xPart D M).ι := ⟨fun i => by
    have h1 : (M.X i.1).isNone = true := i.2
    have h2 : (M.X i.1).isSome = true := hM i.1
    cases h : M.X i.1 <;> simp_all⟩
  refine ⟨fun N => ⟨⟨0⟩, fun f => ?_⟩, fun N => ⟨⟨0⟩, fun f => ?_⟩⟩
  · ext i
    exact isEmptyElim i
  · ext _ j
    exact isEmptyElim j

lemma xFree_single (l : IntervalCat k I) : XFree D (single D (some l)) := fun _ => rfl

/-- A short exact sequence (after `ρ`) between objects without copies of `X` realizes its
class. -/
lemma realizes_of_xFree {A B C : CD D} (hA : XFree D A) (hB : XFree D B) (hC : XFree D C)
    (x : A ⟶ B) (y : B ⟶ C) (w : x ≫ y = 0)
    (hS : (ShortComplex.mk ((rho D).map x) ((rho D).map y)
      (by rw [← Functor.map_comp, w, Functor.map_zero])).ShortExact) :
    Realizes D hS.extClass x y := by
  have hZ : IsZero (xPart D A ⊞ xPart D C) :=
    (biprod_isZero_iff _ _).mpr ⟨isZero_xPart D hA, isZero_xPart D hC⟩
  refine ⟨w, ⟨hS, rfl⟩, B, hB, isoBiprodZero hZ, x, y, (isZero_xPart D hA).eq_of_src _ _, ?_, ?_⟩
  · apply biprod.hom_ext
    · simp [isoBiprodZero]
    · exact hZ.eq_of_tgt _ _
  · simp [isoBiprodZero]

/-! ### Morphisms between single objects -/

/-- The indecomposable of `C(D)` attached to an interval label. -/
abbrev indI (l : IntervalCat k I) : IndCat D := some l

/-- The indecomposable `X`. -/
abbrev indX : IndCat D := none

/-- The single object of `C(D)` attached to an interval label. -/
noncomputable abbrev sI (l : IntervalCat k I) : CD D := single D (indI D l)

/-- The single object `X`. -/
noncomputable abbrev sX : CD D := single D (indX D)

/-- A morphism of interval representations, as a morphism of single objects of `C(D)`. -/
noncomputable def sMap {l l' : IntervalCat k I} (f : l.rep k ⟶ l'.rep k) : sI D l ⟶ sI D l' :=
  (Mat_.embedding (IndCat D)).map (show indI D l ⟶ indI D l' from ⟨f⟩)

lemma sMap_comp {l l' l'' : IntervalCat k I} (f : l.rep k ⟶ l'.rep k) (g : l'.rep k ⟶ l''.rep k) :
    sMap D (f ≫ g) = sMap D f ≫ sMap D g :=
  (Mat_.embedding (IndCat D)).map_comp
    (show indI D l ⟶ indI D l' from ⟨f⟩) (show indI D l' ⟶ indI D l'' from ⟨g⟩)

/-- The morphism `X ⟶ A j` given by `d ∈ D_j`. -/
noncomputable def xHom {j : I} (d : D.obj (op j)) : sX D ⟶ sI D (A j) :=
  (Mat_.embedding (IndCat D)).map (show indX D ⟶ indI D (A j) from d)

lemma xHom_comp_aMap {i j : I} (hij : i ≤ j) (d : D.obj (op j)) :
    xHom D d ≫ sMap D (aMap hij) = xHom D ((D.map (homOfLE hij).op).hom d) := by
  rw [xHom, sMap, ← Functor.map_comp, xHom]
  congr 1
  change (if h : i ≤ j then coeffRep (aMap (k := k) hij) • D.map (homOfLE h).op else 0).hom d = _
  rw [dite_eq_left hij, coeffRep_aMap, one_smul]

lemma xHom_comp_bMap {i : I} (d : D.obj (op i)) : xHom D d ≫ sMap D (bMap i) = 0 := by
  rw [xHom, sMap, ← Functor.map_comp]
  exact (congrArg (Mat_.embedding (IndCat D)).map (Subsingleton.elim (α := PUnit) _ 0)).trans
    (Functor.map_zero _ _ _)

lemma xHom_injective {j : I} : Function.Injective (xHom D (j := j)) := fun _ _ h =>
  (Mat_.embedding (IndCat D)).map_injective h

lemma xHom_surjective {j : I} (f : sX D ⟶ sI D (A j)) : ∃ d, xHom D d = f :=
  ⟨(Mat_.embedding (IndCat D)).preimage f, (Mat_.embedding (IndCat D)).map_preimage f⟩

/-! ### The interval conflations `A i → P i → Y` -/

lemma sMap_b_comp_c (i : I) : sMap D (bMap (k := k) i) ≫ sMap D (cMap i) = 0 := by
  rw [← sMap_comp, bMap_comp_cMap]
  exact (Mat_.embedding (IndCat D)).map_zero _ _

/-- The image under `ρ` of `A i → P i → Y` in `C(D)`. -/
noncomputable def rhoIntervalSeq (i : I) : ShortComplex (Rep k I) :=
  ShortComplex.mk ((rho D).map (sMap D (bMap i))) ((rho D).map (sMap D (cMap i)))
    (by rw [← Functor.map_comp, sMap_b_comp_c, Functor.map_zero])

/-- `ρ` of the interval sequence is isomorphic to the interval sequence. -/
noncomputable def rhoIntervalSeqIso (i : I) : rhoIntervalSeq D i ≅ intervalSeq i :=
  ShortComplex.isoMk (rhoSingleIso D (indI D (A i))) (rhoSingleIso D (indI D (P i)))
    (rhoSingleIso D (indI D Y))
    (rhoSingleIso_hom_naturality D (show indI D (A i) ⟶ indI D (P i) from ⟨bMap i⟩)).symm
    (rhoSingleIso_hom_naturality D (show indI D (P i) ⟶ indI D Y from ⟨cMap i⟩)).symm

lemma rhoIntervalSeq_shortExact (i : I) : (rhoIntervalSeq D i).ShortExact :=
  ShortComplex.shortExact_of_iso (rhoIntervalSeqIso D i).symm (intervalSeq_shortExact i)

/-- The class `ε_i ∈ E(Y, A i)` of the interval conflation `A i → P i → Y`. -/
noncomputable def epsClass (i : I) : (cdData D).Ext (sI D Y) (sI D (A i)) :=
  (rhoIntervalSeq_shortExact D i).extClass

lemma realizes_epsClass (i : I) :
    (cdData D).Realizes (epsClass D i) (sMap D (bMap i)) (sMap D (cMap i)) :=
  realizes_of_xFree D (xFree_single D _) (xFree_single D _) (xFree_single D _) _ _
    (sMap_b_comp_c D i) (rhoIntervalSeq_shortExact D i)

/-- (3.1): `(a_{ji})_* ε_j = ε_i`. -/
lemma push_epsClass {i j : I} (hij : i ≤ j) :
    (cdData D).push (sMap D (aMap hij)) (epsClass D j) = epsClass D i := by
  let φ : rhoIntervalSeq D j ⟶ rhoIntervalSeq D i :=
    { τ₁ := (rho D).map (sMap D (aMap hij))
      τ₂ := (rho D).map (sMap D (pMap hij))
      τ₃ := 𝟙 _
      comm₁₂ := by
        change (rho D).map (sMap D (aMap hij)) ≫ (rho D).map (sMap D (bMap i)) =
          (rho D).map (sMap D (bMap j)) ≫ (rho D).map (sMap D (pMap hij))
        rw [← Functor.map_comp, ← Functor.map_comp, ← sMap_comp, ← sMap_comp, aMap_comp_bMap,
          bMap_comp_pMap]
      comm₂₃ := by
        change (rho D).map (sMap D (pMap hij)) ≫ (rho D).map (sMap D (cMap i)) =
          (rho D).map (sMap D (cMap j)) ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp, ← sMap_comp, pMap_comp_cMap] }
  have h := (rhoIntervalSeq_shortExact D j).extClass_naturality
    (rhoIntervalSeq_shortExact D i) φ
  change (epsClass D j).comp (Abelian.Ext.mk₀ ((rho D).map (sMap D (aMap hij)))) (add_zero 1) =
    epsClass D i
  exact h.trans (Abelian.Ext.mk₀_id_comp _)

end ExtriangulatedRealization
