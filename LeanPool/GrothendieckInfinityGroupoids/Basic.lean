/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.CategoryTheory.EqToHom

/-!
# Globular sets, coglobular objects and tables (roadmap 0.1, 1.1)

The globe category `𝔾` (`Globe`), globular sets as presheaves on it (`GlobularPresheaf`) and in
explicit form (`GlobularSet`), coglobular objects of a category (`CoglobularObject`) with their
faces, the coglobular space `stdDisks` of disks `D^n` and hemisphere inclusions
`x ↦ (x, ±√(1 − ‖x‖²))`, and tables of dimensions (`Table`) with the compatibility condition of
a family of maps out of the disks of a table (`CoglobularObject.Compatible`). The conventions are
those of D. Ara, « On the homotopy theory of Grothendieck ∞-groupoids », J. Pure Appl. Algebra 217
(2013), 1237–1278, §1: 1.1–1.2 for globular sets, Examples 1.5.2 for the disks, 1.3 for tables,
with the left disk of each gluing attached by its source face and the right disk by its target
face.

The globe category and explicit globular-set definitions adapt
`lean/OAI/CategoryTheory/Globular/Model.lean` from `openai/math` (Apache-2.0),
commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. See the same repository's
`lean/OAI/CategoryTheory/Globular/Coglobular.lean` for the coglobular-object construction.
-/

@[expose] public section

namespace LeanPool.GrothendieckInfinityGroupoids

open CategoryTheory

universe u v w

/-! ## Roadmap layer 0: globular sets -/

/-- **Roadmap 0.1.** The objects of the globe category `𝔾`: the natural numbers, wrapped so that the
category structure below is not confused with the order category of `ℕ`. -/
structure Globe where
  /-- The dimension `n` of the object `n` of `𝔾`. -/
  dim : ℕ

namespace Globe

/-- The morphisms `m ⟶ n` of `𝔾`: the identity of `n`, and for `m < n` the two sides
(`false` = source `σ`, `true` = target `τ`). A morphism `m ⟶ n` with `m < n` is determined by its
side. -/
inductive Hom : ℕ → ℕ → Type
  /-- The identity of `n`. -/
  | id (n : ℕ) : Hom n n
  /-- The side `ε` from `m` to `n`, for `m < n`. -/
  | side {m n : ℕ} (h : m < n) (ε : Bool) : Hom m n

/-- Composition in `𝔾`: the composite of the side `ε` then the side `δ` is `ε`. -/
def Hom.comp {l m n : ℕ} : Hom l m → Hom m n → Hom l n
  | .id _, g => g
  | .side h ε, .id _ => .side h ε
  | .side h ε, .side h' _ => .side (h.trans h') ε

/-- **Roadmap 0.1.** The globe category `𝔾`. -/
instance : Category Globe where
  Hom m n := Hom m.dim n.dim
  id m := .id m.dim
  comp := Hom.comp
  id_comp _ := rfl
  comp_id {X Y} f := by cases X; cases Y; cases f <;> rfl
  assoc {W X Y Z} f g h := by
    cases W; cases X; cases Y; cases Z
    cases f <;> cases g <;> cases h <;> rfl

/-- The source `σ_n : n ⟶ n + 1`. -/
def σ (n : ℕ) : (⟨n⟩ : Globe) ⟶ ⟨n + 1⟩ := Hom.side (Nat.lt_succ_self n) false

/-- The target `τ_n : n ⟶ n + 1`. -/
def τ (n : ℕ) : (⟨n⟩ : Globe) ⟶ ⟨n + 1⟩ := Hom.side (Nat.lt_succ_self n) true

end Globe

/-- **Roadmap 0.1.** Globular sets as presheaves on `𝔾`. -/
abbrev GlobularPresheaf := Globeᵒᵖ ⥤ Type u

/-- A globular set, in explicit form: cells in each dimension, with source and target maps
satisfying the globular identities. -/
structure GlobularSet where
  /-- The `n`-cells. -/
  Cell : ℕ → Type u
  /-- The source of an `(n+1)`-cell. -/
  src : ∀ n, Cell (n + 1) → Cell n
  /-- The target of an `(n+1)`-cell. -/
  tgt : ∀ n, Cell (n + 1) → Cell n
  src_src : ∀ n c, src n (src (n + 1) c) = src n (tgt (n + 1) c)
  tgt_src : ∀ n c, tgt n (src (n + 1) c) = tgt n (tgt (n + 1) c)

namespace GlobularSet

/-- Two `n`-cells are joined if some `(n+1)`-cell goes from the first to the second. -/
def Joined (X : GlobularSet.{u}) (n : ℕ) (a b : X.Cell n) : Prop :=
  ∃ h : X.Cell (n + 1), X.src n h = a ∧ X.tgt n h = b

end GlobularSet

/-! ## Roadmap layer 1: coglobular objects and tables -/

/-- A coglobular object of a category `K`: disks `D n` with source and target inclusions
`σ n, τ n : D n ⟶ D (n+1)` satisfying the coglobular identities. -/
structure CoglobularObject (K : Type u) [Category.{v} K] where
  /-- The `n`-disk. -/
  disk : ℕ → K
  /-- The source inclusion. -/
  σ : ∀ n, disk n ⟶ disk (n + 1)
  /-- The target inclusion. -/
  τ : ∀ n, disk n ⟶ disk (n + 1)
  σ_σ : ∀ n, σ n ≫ σ (n + 1) = σ n ≫ τ (n + 1)
  τ_σ : ∀ n, τ n ≫ σ (n + 1) = τ n ≫ τ (n + 1)

namespace CoglobularObject

variable {K : Type u} [Category.{v} K] (D : CoglobularObject K)

/-- The face `D m ⟶ D (m + k + 1)` of side `ε` (`false` = source, `true` = target): the first
step is `σ` or `τ`, the later ones `σ` (any choice gives the same map, by the identities). -/
def face (m : ℕ) : (k : ℕ) → Bool → (D.disk m ⟶ D.disk (m + k + 1))
  | 0, ε => if ε then D.τ m else D.σ m
  | k + 1, ε => face m k ε ≫ D.σ (m + k + 1)

/-- The face `D m ⟶ D n` of side `ε`, for `m < n`. -/
def faceTo {m n : ℕ} (h : m < n) (ε : Bool) : D.disk m ⟶ D.disk n :=
  D.face m (n - m - 1) ε ≫ eqToHom (congrArg D.disk (by omega))

end CoglobularObject

/-- **Roadmap 1.1.** The point `(x, √(1 − ‖x‖²))` (side `ε = false`, the source) or
`(x, −√(1 − ‖x‖²))` (side `ε = true`, the target) of `ℝ^{n+1}`, for `x ∈ ℝ^n` (Ara 2013,
Examples 1.5.2). -/
noncomputable def hemiPoint (n : ℕ) (ε : Bool) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => x i)
    ((if ε then -1 else 1) * Real.sqrt (1 - ‖x‖ ^ 2)))

/-- **Roadmap 1.1.** A point of the closed unit ball goes to the unit sphere. -/
theorem norm_hemiPoint (n : ℕ) (ε : Bool) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    ‖hemiPoint n ε x‖ = 1 := by
  have h0 : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hs : ((if ε then (-1 : ℝ) else 1) * Real.sqrt (1 - ‖x‖ ^ 2)) ^ 2 = 1 - ‖x‖ ^ 2 := by
    cases ε <;> simp [Real.sq_sqrt h0]
  have hx2 := EuclideanSpace.real_norm_sq_eq x
  have hsq : ‖hemiPoint n ε x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    simp only [hemiPoint, PiLp.toLp_apply, Fin.snoc_castSucc, Fin.snoc_last]
    linarith [hs, hx2]
  rw [← Real.sqrt_sq (norm_nonneg (hemiPoint n ε x)), hsq, Real.sqrt_one]

/-- **Roadmap 1.1.** The map `x ↦ (x, ±√(1 − ‖x‖²))` is continuous. -/
theorem continuous_hemiPoint (n : ℕ) (ε : Bool) : Continuous (hemiPoint n ε) := by
  have hg : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      (if ε then (-1 : ℝ) else 1) * Real.sqrt (1 - ‖x‖ ^ 2) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))
  have hf : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Fin.snoc (α := fun _ => ℝ) (fun i => x i)
        ((if ε then (-1 : ℝ) else 1) * Real.sqrt (1 - ‖x‖ ^ 2)) := by
    refine continuous_pi fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hg
    · simpa using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)
  exact (PiLp.continuous_toLp 2 _).comp hf

/-- **Roadmap 1.1.** On the unit sphere the last coordinate `±√(1 − ‖y‖²)` is `0`, so both sides
give the same point. -/
theorem hemiPoint_eq_of_norm_eq_one (m : ℕ) (ε ε' : Bool) {y : EuclideanSpace ℝ (Fin m)}
    (hy : ‖y‖ = 1) : hemiPoint m ε y = hemiPoint m ε' y := by
  simp only [hemiPoint, hy, one_pow, sub_self, Real.sqrt_zero, mul_zero]

/-- **Roadmap 1.1.** The coglobular identities on points: `hemiPoint n δ x` lies on the unit sphere,
so both maps of dimension `n + 1` send it to the point with last coordinate `0`. -/
theorem hemiPoint_hemiPoint (n : ℕ) (δ ε ε' : Bool) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ≤ 1) :
    hemiPoint (n + 1) ε (hemiPoint n δ x) = hemiPoint (n + 1) ε' (hemiPoint n δ x) :=
  hemiPoint_eq_of_norm_eq_one (n + 1) ε ε' (norm_hemiPoint n δ hx)

/-- **Roadmap 1.1.** The hemisphere inclusion `D^n → D^{n+1}` of side `ε` on Mathlib's disks
`TopCat.disk` (Ara 2013, Examples 1.5.2). -/
noncomputable def hemisphere (n : ℕ) (ε : Bool) : TopCat.disk.{0} n ⟶ TopCat.disk.{0} (n + 1) :=
  TopCat.ofHom
    ⟨ULift.map (fun p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        (⟨hemiPoint n ε p.1, mem_closedBall_zero_iff.2
          (norm_hemiPoint n ε (mem_closedBall_zero_iff.1 p.2)).le⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)),
      continuous_uliftMap _
        (Continuous.subtype_mk ((continuous_hemiPoint n ε).comp continuous_subtype_val) _)⟩

/-- **Roadmap 1.1.** The coglobular identities for the hemisphere inclusions. -/
theorem hemisphere_hemisphere (n : ℕ) (δ ε ε' : Bool) :
    hemisphere n δ ≫ hemisphere (n + 1) ε = hemisphere n δ ≫ hemisphere (n + 1) ε' :=
  TopCat.ext fun x => congrArg ULift.up (Subtype.ext
    (hemiPoint_hemiPoint n δ ε ε' (mem_closedBall_zero_iff.1 x.down.2)))

/-- **Roadmap 1.1.** The coglobular space of disks `D^n` and hemisphere inclusions `σ, τ` (Ara 2013,
Examples 1.5.2), the coglobular object of `TopCat` used throughout. -/
noncomputable def stdDisks : CoglobularObject TopCat.{0} where
  disk n := TopCat.disk.{0} n
  σ n := hemisphere n false
  τ n := hemisphere n true
  σ_σ n := hemisphere_hemisphere n false false true
  τ_σ n := hemisphere_hemisphere n true false true

/-- A table of dimensions `(i₁, i'₁, i₂, …, i'_{m−1}, i_m)` with `i_k > i'_k < i_{k+1}` (Ara 2013,
1.3): `top` has one more entry than `bot`. -/
structure Table where
  /-- The number of gluings `m − 1`. -/
  width : ℕ
  /-- The top dimensions `i_k`. -/
  top : Fin (width + 1) → ℕ
  /-- The gluing dimensions `i'_k`. -/
  bot : Fin width → ℕ
  bot_lt_left : ∀ k, bot k < top k.castSucc
  bot_lt_right : ∀ k, bot k < top k.succ

namespace Table

/-- The table `(n)` of the disk `D_n`. -/
def globe (n : ℕ) : Table where
  width := 0
  top := fun _ => n
  bot := Fin.elim0
  bot_lt_left := fun k => k.elim0
  bot_lt_right := fun k => k.elim0

/-- The dimension of a table: its largest top dimension. -/
def dim (T : Table) : ℕ := Finset.univ.sup T.top

end Table

namespace CoglobularObject

variable {K : Type u} [Category.{v} K] (D : CoglobularObject K)

/-- A family of maps out of the disks of a table is compatible when it agrees on each gluing, in
Ara's orientation (2013, 1.3): the source face of the left disk equals the target face of the
right disk. -/
def Compatible (T : Table) {Y : K} (φ : ∀ k, D.disk (T.top k) ⟶ Y) : Prop :=
  ∀ j, D.faceTo (T.bot_lt_left j) false ≫ φ j.castSucc =
    D.faceTo (T.bot_lt_right j) true ≫ φ j.succ

end CoglobularObject

end LeanPool.GrothendieckInfinityGroupoids
