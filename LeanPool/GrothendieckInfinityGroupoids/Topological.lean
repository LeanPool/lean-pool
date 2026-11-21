/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckInfinityGroupoids.Homotopy
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# The fundamental ∞-groupoid of a space and its `π₀` (roadmap 5.2, 5.3, 5.4)

For a globular extension `C` and a functor `R : C ⥤ TopCat`, the fundamental ∞-groupoid
presheaf `Π_∞^R(X) = TopCat(R(−), X)` (`piPresheaf`, D. Ara, « On the homotopy theory of
Grothendieck ∞-groupoids », J. Pure Appl. Algebra 217 (2013), 1237–1278, 5.2). When `R` is a
globular functor into the coglobular space of disks, `Π_∞^R(X)` sends globular sums to globular
products, so it is an ∞-groupoid of type `C` when `C` is a pseudo-coherator
(`isGlobularPresheaf_piPresheaf`); its `0`-cells are the points of `X` and two of them are homotopic
exactly when they are joined by a path (`cellJoined_zero_piPresheaf_iff`), so that `Π_∞^R f` is a
bijection on `π₀` exactly when `f` is a bijection on path components
(`bijectiveOnComponents_piPresheaf_iff`): the `π₀` part of Ara 2013, Theorem 8.7 and Corollaries
8.9–8.11.
-/

@[expose] public section

namespace LeanPool.GrothendieckInfinityGroupoids

open CategoryTheory Limits Opposite

universe u v w

/-- **Roadmap 5.2.** The fundamental ∞-groupoid presheaf `Π_∞^R(X) = TopCat(R(−), X)` for a functor
`R : C ⥤ TopCat` out of a globular extension (Ara 2013, 5.2); when `R` is a globular functor into
`stdDisks` (`IsGlobularFunctor`) it sends globular sums to globular products, and it is an
∞-groupoid of type `C` when `C` is a pseudo-coherator. -/
def piPresheaf (C : GlobularExtension) (R : C.Obj ⥤ TopCat.{0}) :
    TopCat.{0} ⥤ (C.Objᵒᵖ ⥤ Type) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj R.op

section Disks

/-- The point of the disk `D^0`. -/
noncomputable def disk0Point : TopCat.disk.{0} 0 :=
  ULift.up ⟨0, Metric.mem_closedBall_self zero_le_one⟩

instance : Subsingleton (TopCat.disk.{0} 0) :=
  ⟨fun a b => by
    obtain ⟨⟨a, ha⟩⟩ := a
    obtain ⟨⟨b, hb⟩⟩ := b
    congr
    exact Subsingleton.elim a b⟩

/-- The first coordinate of a point of `D^1`. -/
noncomputable def disk1Coord (y : TopCat.disk.{0} 1) : ℝ := y.down.1 0

theorem continuous_disk1Coord : Continuous disk1Coord :=
  (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
    (continuous_subtype_val.comp continuous_uliftDown)

theorem disk1Coord_hemisphere (ε : Bool) :
    disk1Coord (hemisphere 0 ε disk0Point) = if ε then -1 else 1 := by
  rw [show disk1Coord (hemisphere 0 ε disk0Point) = (hemiPoint 0 ε 0) (Fin.last 0) from rfl]
  simp only [hemiPoint, PiLp.toLp_apply, Fin.snoc_last, norm_zero]
  cases ε <;> simp

/-- Any two points of `D^1` are joined by a path. -/
theorem joined_disk1 (y z : TopCat.disk.{0} 1) : Joined y z := by
  have hc : IsPathConnected (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    (convex_closedBall _ _).isPathConnected ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have := (hc.joinedIn y.down.1 y.down.2 z.down.1 z.down.2).joined_subtype
  exact this.map continuous_uliftUp

end Disks

variable (C : GlobularExtension.{u, v}) (R : C.Obj ⥤ TopCat.{0})

theorem piPresheaf_map_apply (X : TopCat.{0}) {S S' : C.Obj} (g : S ⟶ S')
    (a : R.obj S' ⟶ X) : ((piPresheaf C R).obj X).map g.op a = R.map g ≫ a := rfl

theorem piPresheaf_app_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (S : C.Obj) (a : R.obj S ⟶ X) :
    ((piPresheaf C R).map f).app (op S) a = a ≫ f := rfl

namespace IsGlobularFunctor

variable {C R} (hR : IsGlobularFunctor C stdDisks R)
include hR

theorem map_face (m : ℕ) : ∀ (k : ℕ) (ε : Bool),
    R.map (C.disks.face m k ε) =
      eqToHom (hR.obj_disk m) ≫ stdDisks.face m k ε ≫ eqToHom (hR.obj_disk (m + k + 1)).symm
  | 0, ε => by cases ε <;> simp [CoglobularObject.face, hR.map_σ, hR.map_τ]
  | k + 1, ε => by
    simp only [CoglobularObject.face, Functor.map_comp, map_face m k ε, hR.map_σ,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem map_faceTo {m n : ℕ} (h : m < n) (ε : Bool) :
    R.map (C.disks.faceTo h ε) =
      eqToHom (hR.obj_disk m) ≫ stdDisks.faceTo h ε ≫ eqToHom (hR.obj_disk n).symm := by
  simp only [CoglobularObject.faceTo, Functor.map_comp, hR.map_face, eqToHom_map,
    Category.assoc, eqToHom_trans]

end IsGlobularFunctor

/-- **Roadmap 5.2.** For a globular functor `R` into the coglobular space of disks, the
fundamental ∞-groupoid presheaf `Π_∞^R(X)` sends globular sums to globular products. If `C`
is a pseudo-coherator, it is an ∞-groupoid of type `C` (Ara 2013, 5.2). -/
theorem isGlobularPresheaf_piPresheaf (hR : IsGlobularFunctor C stdDisks R)
    (X : TopCat.{0}) : IsGlobularPresheaf C ((piPresheaf C R).obj X) := by
  intro T v hv
  let v' : ∀ k, R.obj (C.disks.disk (T.top k)) ⟶ X := v
  have hv' : ∀ j, R.map (C.disks.faceTo (T.bot_lt_left j) false) ≫ v' j.castSucc =
      R.map (C.disks.faceTo (T.bot_lt_right j) true) ≫ v' j.succ := hv
  let φ : ∀ k, stdDisks.disk (T.top k) ⟶ X := fun k => eqToHom (hR.obj_disk _).symm ≫ v' k
  have hφ : stdDisks.Compatible T φ := by
    intro j
    have := hv' j
    rw [hR.map_faceTo, hR.map_faceTo, Category.assoc, Category.assoc] at this
    exact (cancel_epi _).1 this
  obtain ⟨u, hu, huniq⟩ := hR.isGlobularSum T X φ hφ
  refine ⟨u, fun k => ?_, fun a ha => huniq a fun k => ?_⟩
  · change R.map (C.incl T k) ≫ u = v' k
    rw [hu k]
    simp [φ]
  · have : R.map (C.incl T k) ≫ a = v' k := ha k
    rw [this]
    simp [φ]

section Pi0

variable {C R} (hR : IsGlobularFunctor C stdDisks R)

/-- The point of `X` underlying a `0`-cell of `Π_∞^R(X)`. -/
noncomputable def cellPoint {X : TopCat.{0}} (c : R.obj (C.disks.disk 0) ⟶ X) : X :=
  c (eqToHom (hR.obj_disk 0).symm disk0Point)

include hR in
theorem subsingleton_obj_disk0 : Subsingleton (R.obj (C.disks.disk 0)) := by
  refine ⟨fun a b => ?_⟩
  have h := congrArg (eqToHom (hR.obj_disk 0).symm)
    (Subsingleton.elim (α := TopCat.disk.{0} 0) (eqToHom (hR.obj_disk 0) a)
      (eqToHom (hR.obj_disk 0) b))
  simpa only [← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl,
    ConcreteCategory.id_apply] using h

/-- The `0`-cell of `Π_∞^R(X)` at a point. -/
noncomputable def pointCell {X : TopCat.{0}} (x : X) : R.obj (C.disks.disk 0) ⟶ X :=
  TopCat.ofHom (ContinuousMap.const _ x)

theorem cellPoint_pointCell {X : TopCat.{0}} (x : X) : cellPoint hR (pointCell (R := R) x) = x :=
  rfl

theorem eq_pointCell {X : TopCat.{0}} (c : R.obj (C.disks.disk 0) ⟶ X) :
    c = pointCell (cellPoint hR c) := by
  have := subsingleton_obj_disk0 hR
  ext y
  change c y = c _
  rw [Subsingleton.elim y (eqToHom (hR.obj_disk 0).symm disk0Point)]

theorem cellPoint_comp {X Y : TopCat.{0}} (c : R.obj (C.disks.disk 0) ⟶ X) (f : X ⟶ Y) :
    cellPoint hR (c ≫ f) = f (cellPoint hR c) := rfl

theorem eqToHom_apply_symm {A B : TopCat.{0}} (e : A = B) (z : B) :
    eqToHom e (eqToHom e.symm z) = z := by
  subst e
  rfl

/-- **Roadmap 5.3.** Two `0`-cells of `Π_∞^R(X)` are homotopic exactly when their points are joined
by a path of `X`. -/
theorem cellJoined_zero_piPresheaf_iff {X : TopCat.{0}} (a b : R.obj (C.disks.disk 0) ⟶ X) :
    C.CellJoined ((piPresheaf C R).obj X) 0 a b ↔ Joined (cellPoint hR a) (cellPoint hR b) := by
  have hσ : ∀ ε : Bool, ∀ h : R.obj (C.disks.disk 1) ⟶ X,
      cellPoint hR (R.map (if ε then C.disks.τ 0 else C.disks.σ 0) ≫ h) =
        h (eqToHom (hR.obj_disk 1).symm (hemisphere 0 ε disk0Point)) := by
    intro ε h
    cases ε <;>
    · simp only [cellPoint, Bool.false_eq_true, ↓reduceIte, hR.map_σ, hR.map_τ,
        ConcreteCategory.comp_apply]
      congr 3
      exact Subsingleton.elim (α := TopCat.disk.{0} 0) _ _
  constructor
  · rintro ⟨h, rfl, rfl⟩
    have h₁ := hσ false h
    have h₂ := hσ true h
    simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
    change Joined (cellPoint hR (R.map (C.disks.σ 0) ≫ h))
      (cellPoint hR (R.map (C.disks.τ 0) ≫ h))
    rw [h₁, h₂]
    exact ((joined_disk1 _ _).map (eqToHom (hR.obj_disk 1).symm).hom.continuous).map
      h.hom.continuous
  · rintro ⟨p⟩
    let γ : stdDisks.disk 1 ⟶ X := TopCat.ofHom
      ⟨fun y => p.extend ((1 - disk1Coord y) / 2),
        p.continuous_extend.comp ((continuous_const.sub continuous_disk1Coord).div_const 2)⟩
    have hγ : ∀ ε : Bool, γ (hemisphere 0 ε disk0Point) = if ε then cellPoint hR b
        else cellPoint hR a := by
      intro ε
      change p.extend ((1 - disk1Coord (hemisphere 0 ε disk0Point)) / 2) = _
      rw [disk1Coord_hemisphere]
      cases ε
      · norm_num
      · norm_num
    refine ⟨eqToHom (hR.obj_disk 1) ≫ γ, ?_, ?_⟩
    · change R.map (C.disks.σ 0) ≫ eqToHom (hR.obj_disk 1) ≫ γ = a
      rw [eq_pointCell hR (R.map (C.disks.σ 0) ≫ _), eq_pointCell hR a]
      congr 1
      have := hσ false (eqToHom (hR.obj_disk 1) ≫ γ)
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [this]
      refine (ConcreteCategory.comp_apply _ _ _).trans ?_
      exact (congrArg γ (eqToHom_apply_symm _ _)).trans (by simpa using hγ false)
    · change R.map (C.disks.τ 0) ≫ eqToHom (hR.obj_disk 1) ≫ γ = b
      rw [eq_pointCell hR (R.map (C.disks.τ 0) ≫ _), eq_pointCell hR b]
      congr 1
      have := hσ true (eqToHom (hR.obj_disk 1) ≫ γ)
      simp only [↓reduceIte] at this
      rw [this]
      refine (ConcreteCategory.comp_apply _ _ _).trans ?_
      exact (congrArg γ (eqToHom_apply_symm _ _)).trans (by simpa using hγ true)

/-- The map induced by `f` on path components. -/
def mapZerothHomotopy {X Y : TopCat.{0}} (f : X ⟶ Y) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f.hom x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map f.hom.continuous))

theorem mk_eq_mk_iff {X : Type*} [TopologicalSpace X] (x y : X) :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y ↔ Joined x y :=
  Quotient.eq (r := pathSetoid X)

include hR in
/-- **Roadmap 5.4.** `Π_∞^R f` is a bijection on `π₀` exactly when `f` is a bijection on path
components, the first condition of a weak homotopy equivalence (`π₀` part of Ara 2013,
Corollaries 8.9–8.11). -/
theorem bijectiveOnComponents_piPresheaf_iff {X Y : TopCat.{0}} (f : X ⟶ Y) :
    C.BijectiveOnComponents ((piPresheaf C R).map f) ↔
      Function.Bijective (mapZerothHomotopy f) := by
  have key : ∀ c c' : R.obj (C.disks.disk 0) ⟶ X,
      C.CellJoined ((piPresheaf C R).obj Y) 0 (c ≫ f) (c' ≫ f) ↔
        Joined (f (cellPoint hR c)) (f (cellPoint hR c')) := fun c c' =>
    cellJoined_zero_piPresheaf_iff hR (c ≫ f) (c' ≫ f)
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · induction a with | mk x => induction b with | mk x' =>
      have hj : Joined (f x) (f x') := (mk_eq_mk_iff _ _).1 hab
      have := hi (pointCell x) (pointCell x') ((key _ _).2 hj)
      exact (mk_eq_mk_iff _ _).2 ((cellJoined_zero_piPresheaf_iff hR _ _).1 this)
    · induction y with | mk y =>
      obtain ⟨c, hc⟩ := hs (pointCell y)
      exact ⟨ZerothHomotopy.mk (cellPoint hR c),
        (mk_eq_mk_iff _ _).2 ((cellJoined_zero_piPresheaf_iff hR (c ≫ f) _).1 hc)⟩
  · rintro ⟨hi, hs⟩
    refine ⟨fun c => ?_, fun c c' h => ?_⟩
    · obtain ⟨a, ha⟩ := hs (ZerothHomotopy.mk (cellPoint hR c))
      induction a with | mk x =>
      refine ⟨pointCell x, (cellJoined_zero_piPresheaf_iff hR (pointCell x ≫ f) c).2 ?_⟩
      exact (mk_eq_mk_iff _ _).1 ha
    · have h' := (key c c').1 h
      have := hi (a₁ := ZerothHomotopy.mk (cellPoint hR c))
        (a₂ := ZerothHomotopy.mk (cellPoint hR c')) ((mk_eq_mk_iff _ _).2 h')
      exact (cellJoined_zero_piPresheaf_iff hR c c').2 ((mk_eq_mk_iff _ _).1 this)

end Pi0

section WeakEquivalence

variable {C : PseudoCoherator.{u, v}} {R : C.Obj ⥤ TopCat.{0}}
  (hR : IsGlobularFunctor C.toGlobularExtension stdDisks R)

include hR in
/-- **Roadmap 5.4.** If `Π_∞^R f` is a weak equivalence of ∞-groupoids of type `C`, then `f` is a
bijection on path components. -/
theorem IsWeakEquivalence.bijective_mapZerothHomotopy {X Y : TopCat.{0}} {f : X ⟶ Y}
    (h : C.IsWeakEquivalence ((piPresheaf C.toGlobularExtension R).map f)) :
    Function.Bijective (mapZerothHomotopy f) :=
  (bijectiveOnComponents_piPresheaf_iff hR f).1 h.1

include hR in
/-- **Roadmap 5.4.** `Π_∞^R` of the inclusion of a point into the two-point discrete space is not a
weak equivalence. -/
theorem not_isWeakEquivalence_piPresheaf_point_bool :
    ¬ C.IsWeakEquivalence ((piPresheaf C.toGlobularExtension R).map
      (TopCat.ofHom ⟨fun _ : PUnit.{1} => false, continuous_const⟩ :
        TopCat.of PUnit.{1} ⟶ TopCat.of Bool)) := by
  intro h
  obtain ⟨a, ha⟩ := (IsWeakEquivalence.bijective_mapZerothHomotopy hR h).2 (ZerothHomotopy.mk true)
  induction a with | mk x =>
  obtain ⟨p⟩ := (mk_eq_mk_iff _ _).1 ha
  have := (p.continuous.isConst_of_preconnectedSpace) 0 1
  simp at this

end WeakEquivalence

end LeanPool.GrothendieckInfinityGroupoids
