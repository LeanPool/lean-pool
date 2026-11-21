/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckInfinityGroupoids.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Globular sums (roadmap 1.2)

A choice of globular sum for every table of dimensions (`GlobularSums`): an object, the inclusions
of the disks of the table and the universal property of the iterated pushout
`D_{i₁} ⊔_{D_{i'₁}} D_{i₂} ⊔ ⋯ ⊔_{D_{i'_{m−1}}} D_{i_m}`, the sum of the one-disk table `(n)`
being the disk itself (D. Ara, « On the homotopy theory of Grothendieck ∞-groupoids », J. Pure
Appl. Algebra 217 (2013), 1237–1278, 1.3).

In a category with pushouts every coglobular object has globular sums
(`GlobularSums.nonempty_of_hasPushouts`, Ara 2013, Examples 1.5.1): the sum of a table of width
`w + 1` is the pushout of the sum of its first `w + 1` disks and of its last disk along the last
gluing disk (`sumAux`), and the universal property follows by induction on the width. In
particular `TopCat` with the coglobular space of disks has globular sums
(`nonempty_globularSums_stdDisks`).
-/

@[expose] public section

namespace LeanPool.GrothendieckInfinityGroupoids

open CategoryTheory Limits

universe u v

/-- **Roadmap 1.2.** A choice of globular sum for every table (Ara 2013, 1.3): an object, the
inclusions of the disks of the table, and the universal property of the iterated pushout; the sum
of the one-disk table `(n)` is `D n` itself. -/
structure GlobularSums {K : Type u} [Category.{v} K] (D : CoglobularObject K) where
  /-- The globular sum of a table. -/
  sum : Table → K
  /-- The inclusion of the `k`-th disk of a table. -/
  incl : ∀ (T : Table) (k : Fin (T.width + 1)), D.disk (T.top k) ⟶ sum T
  incl_compatible : ∀ T, D.Compatible T (incl T)
  isGlobularSum : ∀ (T : Table) (Y : K) (φ : ∀ k, D.disk (T.top k) ⟶ Y),
    D.Compatible T φ → ∃! u : sum T ⟶ Y, ∀ k, incl T k ≫ u = φ k
  sum_globe : ∀ n, sum (Table.globe n) = D.disk n
  incl_globe : ∀ n, incl (Table.globe n) ⟨0, Nat.zero_lt_succ 0⟩ = eqToHom (sum_globe n).symm

namespace CoglobularObject

variable {K : Type u} [Category.{v} K] [HasPushouts K] (D : CoglobularObject K)

/-- The iterated pushout of the disks of a table, with the inclusions of its disks, by recursion
on the width. -/
noncomputable def sumAux : (w : ℕ) → (top : Fin (w + 1) → ℕ) → (bot : Fin w → ℕ) →
    (∀ k, bot k < top k.castSucc) → (∀ k, bot k < top k.succ) →
    Σ S : K, ∀ k, D.disk (top k) ⟶ S
  | 0, top, _, _, _ => ⟨D.disk (top 0), fun k => eqToHom (by
    rw [show k = 0 from Fin.ext (by have := k.2; omega)])⟩
  | w + 1, top, bot, hl, hr =>
    let P := sumAux w (fun k => top k.castSucc) (fun k => bot k.castSucc)
      (fun k => hl k.castSucc) (fun k => hr k.castSucc)
    let f : D.disk (bot (Fin.last w)) ⟶ P.1 := D.faceTo (hl (Fin.last w)) false ≫ P.2 (Fin.last w)
    let g : D.disk (bot (Fin.last w)) ⟶ D.disk (top (Fin.last (w + 1))) :=
      D.faceTo (hr (Fin.last w)) true
    ⟨pushout f g, fun k => Fin.lastCases (motive := fun k => D.disk (top k) ⟶ pushout f g)
      (pushout.inr f g) (fun i => P.2 i ≫ pushout.inl f g) k⟩

/-- The inclusions of the iterated pushout are compatible, and it has the universal property of
the globular sum. -/
theorem sumAux_spec : ∀ (w : ℕ) (top : Fin (w + 1) → ℕ) (bot : Fin w → ℕ)
    (hl : ∀ k, bot k < top k.castSucc) (hr : ∀ k, bot k < top k.succ),
    (∀ j, D.faceTo (hl j) false ≫ (D.sumAux w top bot hl hr).2 j.castSucc =
      D.faceTo (hr j) true ≫ (D.sumAux w top bot hl hr).2 j.succ) ∧
    ∀ (Y : K) (φ : ∀ k, D.disk (top k) ⟶ Y),
      (∀ j, D.faceTo (hl j) false ≫ φ j.castSucc = D.faceTo (hr j) true ≫ φ j.succ) →
      ∃! u : (D.sumAux w top bot hl hr).1 ⟶ Y, ∀ k, (D.sumAux w top bot hl hr).2 k ≫ u = φ k
  | 0, top, bot, hl, hr => by
    refine ⟨fun j => j.elim0, fun Y φ _ => ⟨φ 0, fun k => ?_, fun u hu => ?_⟩⟩
    · obtain rfl : k = 0 := Fin.ext (by have := k.2; omega)
      simp [sumAux]
    · have := hu 0
      simp only [sumAux, eqToHom_refl] at this
      exact (Category.id_comp u).symm.trans this
  | w + 1, top, bot, hl, hr => by
    obtain ⟨hcomp, huniv⟩ := sumAux_spec w (fun k => top k.castSucc) (fun k => bot k.castSucc)
      (fun k => hl k.castSucc) (fun k => hr k.castSucc)
    set P := D.sumAux w (fun k => top k.castSucc) (fun k => bot k.castSucc)
      (fun k => hl k.castSucc) (fun k => hr k.castSucc)
    set f := D.faceTo (hl (Fin.last w)) false ≫ P.2 (Fin.last w)
    set g := D.faceTo (hr (Fin.last w)) true
    refine ⟨fun j => ?_, fun Y φ hφ => ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [sumAux, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc,
          ← Category.assoc]
        exact pushout.condition
      · have := hcomp i
        simp only [sumAux, Fin.succ_castSucc, Fin.lastCases_castSucc, ← Category.assoc]
          at this ⊢
        rw [this]
    · obtain ⟨u', hu', huniq'⟩ := huniv Y (fun k => φ k.castSucc) fun j => hφ j.castSucc
      have hw : f ≫ u' = g ≫ φ (Fin.last (w + 1)) := by
        change (D.faceTo (hl (Fin.last w)) false ≫ P.2 (Fin.last w)) ≫ u' = _
        rw [Category.assoc, hu' (Fin.last w)]
        exact hφ (Fin.last w)
      refine ⟨pushout.desc u' (φ (Fin.last (w + 1))) hw, fun k => ?_, fun u hu => ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) k
        · simp only [sumAux, Fin.lastCases_last, pushout.inr_desc]
        · simp only [sumAux, Fin.lastCases_castSucc, Category.assoc, pushout.inl_desc]
          exact hu' i
      · apply pushout.hom_ext
        · rw [pushout.inl_desc]
          refine huniq' _ fun i => ?_
          have := hu i.castSucc
          simp only [sumAux, Fin.lastCases_castSucc] at this
          exact (Category.assoc _ _ _).symm.trans this
        · rw [pushout.inr_desc]
          have := hu (Fin.last (w + 1))
          simp only [sumAux, Fin.lastCases_last] at this
          exact this

/-- **Roadmap 1.2.** The globular sums of a coglobular object in a category with pushouts, as the
iterated pushouts `sumAux`. -/
noncomputable def globularSums : GlobularSums D where
  sum T := (D.sumAux T.width T.top T.bot T.bot_lt_left T.bot_lt_right).1
  incl T := (D.sumAux T.width T.top T.bot T.bot_lt_left T.bot_lt_right).2
  incl_compatible T := (D.sumAux_spec T.width T.top T.bot T.bot_lt_left T.bot_lt_right).1
  isGlobularSum T := (D.sumAux_spec T.width T.top T.bot T.bot_lt_left T.bot_lt_right).2
  sum_globe _ := rfl
  incl_globe _ := rfl

end CoglobularObject

/-- **Roadmap 1.2.** In a category with pushouts every coglobular object has globular sums (Ara
2013, Examples 1.5.1). -/
theorem GlobularSums.nonempty_of_hasPushouts {K : Type u} [Category.{v} K] [HasPushouts K]
    (D : CoglobularObject K) : Nonempty (GlobularSums D) :=
  ⟨D.globularSums⟩

/-- **Roadmap 1.2.** The coglobular space of disks has globular sums in `TopCat`. -/
theorem nonempty_globularSums_stdDisks : Nonempty (GlobularSums stdDisks) :=
  GlobularSums.nonempty_of_hasPushouts stdDisks

end LeanPool.GrothendieckInfinityGroupoids
