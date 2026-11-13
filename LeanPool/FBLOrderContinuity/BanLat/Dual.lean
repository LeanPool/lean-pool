/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.NormedWeak
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import LeanPool.FBLOrderContinuity.BanLat.Operators.Regular
public import LeanPool.FBLOrderContinuity.BanLat.Operators.RieszKantorovich
public import Mathlib.Analysis.Convex.Cone.Dual



/-!
# The order dual and strong dual of a vector or Banach lattice

The **order dual** `OrderDualSpace X` of a vector lattice `X` is the space of order
bounded real-valued linear functionals on `X`. Since `ℝ` is order complete, the
Riesz–Kantorovich machinery equips it with a canonical order complete vector
lattice structure. The **strong dual** `StrongDual ℝ X` of a normed vector lattice
`X` is the mathlib abbreviation for the space `X →L[ℝ] ℝ` of continuous linear
functionals. For a Banach lattice the two duals coincide as sets — every
continuous functional is order bounded and every order bounded functional is
automatically continuous — and the strong dual inherits the structure of a
Banach lattice.
-/

@[expose] public section

/-! ### The order dual -/

/-- The **order dual** of a vector lattice: order bounded real-valued
linear functionals. -/
abbrev OrderDualSpace (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Type _ :=
  OrderBoundedHom X ℝ

namespace OrderDualSpace

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- Order on the order dual: `φ ≤ ψ` iff `φ x ≤ ψ x` for all positive `x`. -/
theorem le_iff {φ ψ : OrderDualSpace X} :
    φ ≤ ψ ↔ ∀ x : X, 0 ≤ x → φ x ≤ ψ x :=
  OrderBoundedHom.le_iff

/-- A dual element is positive iff it sends positive elements of `X` to
non-negative reals. -/
theorem nonneg_iff {φ : OrderDualSpace X} :
    0 ≤ φ ↔ ∀ x : X, 0 ≤ x → 0 ≤ φ x :=
  OrderBoundedHom.le_iff

/-- Riesz–Kantorovich: positive part of a dual functional at a positive
element is the supremum of `φ y` over `0 ≤ y ≤ x`. -/
theorem isLUB_posPart_apply {φ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB {r : ℝ | ∃ y, 0 ≤ y ∧ y ≤ x ∧ r = φ y} (φ⁺ x) :=
  OrderBoundedHom.isLUB_posPart_apply hx

/-- Negative part of a dual functional at a positive element. -/
theorem isLUB_negPart_apply {φ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB {r : ℝ | ∃ y, 0 ≤ y ∧ y ≤ x ∧ r = -(φ y)} (φ⁻ x) :=
  OrderBoundedHom.isLUB_negPart_apply hx

/-- Modulus of a dual functional at a positive element. -/
theorem isLUB_abs_apply {φ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB {r : ℝ | ∃ y, |y| ≤ x ∧ r = |φ y|} (|φ| x) :=
  OrderBoundedHom.isLUB_abs_apply hx

/-- Riesz–Kantorovich formula for the supremum of two dual functionals. -/
theorem isLUB_sup_apply {φ ψ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB
      {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x ∧ r = φ y + ψ z}
      ((φ ⊔ ψ) x) :=
  OrderBoundedHom.isLUB_sup_apply hx

/-- Riesz–Kantorovich formula for the infimum of two dual functionals. -/
theorem isGLB_inf_apply {φ ψ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsGLB
      {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x ∧ r = φ y + ψ z}
      ((φ ⊓ ψ) x) :=
  OrderBoundedHom.isGLB_inf_apply hx

/-- Every order dual element is regular: it can be written as a difference of
two positive functionals. -/
theorem isRegularOp (φ : OrderDualSpace X) :
    IsRegularOp φ.toLinearMap :=
  IsOrderBounded.isRegularOp φ.isOrderBounded'

variable (X) in
/-- The order dual separates points of `X`: every nonzero element is detected by
some order bounded functional. -/
def SeparatesPoints : Prop :=
  ∀ x : X, (∀ φ : OrderDualSpace X, φ x = 0) → x = 0

/-- Suprema in the order dual are supplied by the Riesz-Kantorovich
order-completeness theorem for order bounded operators. -/
noncomputable instance instSupSet : SupSet (OrderDualSpace X) where
  sSup S := by
    classical
    exact if h : S.Nonempty ∧ BddAbove S then
      (OrderBoundedHom.exists_isLUB h.1 h.2).choose
    else 0

/-- The chosen supremum in the order dual is the least upper bound of every
non-empty bounded-above set. -/
theorem isLUB_sSup (S : Set (OrderDualSpace X)) (hbdd : BddAbove S)
    (hne : S.Nonempty) : IsLUB S (sSup S) := by
  classical
  change IsLUB S (if h : S.Nonempty ∧ BddAbove S then
      (OrderBoundedHom.exists_isLUB h.1 h.2).choose
    else 0)
  rw [dite_eq_left ⟨hne, hbdd⟩]
  exact (OrderBoundedHom.exists_isLUB hne hbdd).choose_spec

/-- The order dual is conditionally complete. -/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice (OrderDualSpace X) :=
  conditionallyCompleteLatticeOfLatticeOfsSup _ isLUB_sSup

end OrderDualSpace

/-! ### The strong dual -/

namespace StrongDual

section NormedVectorLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [NormedVectorLattice X]

/-- Every continuous linear functional on a normed vector lattice is order
bounded. -/
theorem isOrderBounded (φ : StrongDual ℝ X) :
    IsOrderBounded φ.toLinearMap := by
  intro x hx
  refine ⟨‖φ‖ * ‖x‖, mul_nonneg (norm_nonneg _) (norm_nonneg _), fun z hz => ?_⟩
  have hzx : ‖z‖ ≤ ‖x‖ :=
    norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx]; exact hz)
  have h1 : |φ.toLinearMap z| = ‖φ z‖ := (Real.norm_eq_abs _).symm
  rw [h1]
  exact (φ.le_opNorm z).trans (by gcongr)

/-- The order bounded functional underlying a continuous linear functional. -/
def toOrderDualSpace (φ : StrongDual ℝ X) : OrderDualSpace X where
  toLinearMap := φ.toLinearMap
  isOrderBounded' := isOrderBounded φ

@[simp]
theorem toOrderDualSpace_apply (φ : StrongDual ℝ X) (x : X) :
    toOrderDualSpace φ x = φ x := rfl

/-- Bundling `toOrderDualSpace` as a real-linear map. -/
def toOrderDualSpaceLinear : StrongDual ℝ X →ₗ[ℝ] OrderDualSpace X where
  toFun := toOrderDualSpace
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Order on the strong dual, transported through the order dual. -/
instance instLE : LE (StrongDual ℝ X) where
  le f g := toOrderDualSpace f ≤ toOrderDualSpace g

instance instLT : LT (StrongDual ℝ X) where
  lt f g := toOrderDualSpace f < toOrderDualSpace g

/-- Order on the strong dual: `φ ≤ ψ` iff `φ x ≤ ψ x` for all positive `x`. -/
theorem le_iff {φ ψ : StrongDual ℝ X} :
    φ ≤ ψ ↔ ∀ x : X, 0 ≤ x → φ x ≤ ψ x := by
  change toOrderDualSpace φ ≤ toOrderDualSpace ψ ↔ ∀ x : X, 0 ≤ x → φ x ≤ ψ x
  simpa [toOrderDualSpace_apply] using OrderDualSpace.le_iff (φ := toOrderDualSpace φ)
    (ψ := toOrderDualSpace ψ)

/-- A continuous linear functional is positive iff it sends positive elements
of `X` to non-negative reals. -/
theorem nonneg_iff {φ : StrongDual ℝ X} :
    0 ≤ φ ↔ ∀ x : X, 0 ≤ x → 0 ≤ φ x := by
  simpa using (le_iff (φ := 0) (ψ := φ))

/-- A positive continuous linear functional is non-negative on positive elements. -/
theorem apply_nonneg_of_nonneg {φ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) {x : X} (hx : 0 ≤ x) : 0 ≤ φ x :=
  (nonneg_iff.mp hφ) x hx

/-- A positive continuous linear functional is monotone. -/
theorem apply_le_apply_of_nonneg {φ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) {x y : X} (hxy : x ≤ y) : φ x ≤ φ y :=
  (Positive.monotone_iff.mpr (nonneg_iff.mp hφ)) hxy

/-- A positive continuous linear functional is dominated by its value on the modulus. -/
theorem abs_apply_le_apply_abs {φ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) (x : X) : |φ x| ≤ φ |x| :=
  Positive.abs_le_map_abs (nonneg_iff.mp hφ) x

theorem toOrderDualSpace_injective :
    Function.Injective (toOrderDualSpace (X := X)) := by
  intro f g h
  ext x
  have := congrArg (fun (ψ : OrderDualSpace X) => ψ x) h
  simpa using this

theorem toOrderDualSpace_le {f g : StrongDual ℝ X} :
    toOrderDualSpace f ≤ toOrderDualSpace g ↔ f ≤ g := Iff.rfl

theorem toOrderDualSpace_lt {f g : StrongDual ℝ X} :
    toOrderDualSpace f < toOrderDualSpace g ↔ f < g := Iff.rfl

end NormedVectorLattice

section WeakConvergence

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [NormedVectorLattice X]

/-- Every positive element of a normed vector lattice attains its norm at a
positive continuous linear functional of norm at most one. -/
theorem exists_positive_dual_norming {x : X} (hx : 0 ≤ x) :
    ∃ φ : StrongDual ℝ X, 0 ≤ φ ∧ ‖φ‖ ≤ 1 ∧ φ x = ‖x‖ := by
  by_cases hx0 : x = 0
  · refine ⟨0, ?_, by simp, by simp [hx0]⟩
    exact nonneg_iff.mpr fun _ _ => by simp
  · let N : X → ℝ := fun y => ‖y⁺‖
    have hN_hom : ∀ c : ℝ, 0 < c → ∀ y : X, N (c • y) = c * N y := by
      intro c hc y
      simp [N, posPart_smul_nonneg hc.le y, norm_smul, Real.norm_of_nonneg hc.le]
    have hN_add : ∀ y z : X, N (y + z) ≤ N y + N z := by
      intro y z
      have hle : |(y + z)⁺| ≤ |y⁺ + z⁺| := by
        rw [abs_of_nonneg (posPart_nonneg (y + z)),
          abs_of_nonneg (add_nonneg (posPart_nonneg y) (posPart_nonneg z))]
        exact posPart_add_le y z
      exact (norm_le_norm_of_abs_le_abs hle).trans (norm_add_le y⁺ z⁺)
    let p : Subspace ℝ X := ℝ ∙ x
    let coord : StrongDual ℝ p := ContinuousLinearEquiv.coord ℝ x hx0
    let f : p →L[ℝ] ℝ := (‖x‖ : ℝ) • coord
    have hf_le : ∀ y : (⟨p, f⟩ : X →ₗ.[ℝ] ℝ).domain,
        (⟨p, f⟩ : X →ₗ.[ℝ] ℝ) y ≤ N y := by
      intro y
      let a : ℝ := coord y
      have hy_eq : (y : X) = a • x := by
        dsimp [a, coord]
        exact (congrArg Subtype.val
          ((ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ x hx0).apply_symm_apply y)).symm
      by_cases ha : 0 ≤ a
      · have hpos : ((y : X))⁺ = a • x := by
          rw [hy_eq, posPart_smul_nonneg ha, posPart_of_nonneg hx]
        simp [f, a, N, hpos, norm_smul, Real.norm_of_nonneg ha, mul_comm]
      · have ha' : a ≤ 0 := le_of_not_ge ha
        have hnonpos : (y : X) ≤ 0 := by
          rw [hy_eq]
          exact smul_nonpos_of_nonpos_of_nonneg ha' hx
        have hpos : ((y : X))⁺ = 0 := posPart_eq_zero.mpr hnonpos
        have hleft : (⟨p, f⟩ : X →ₗ.[ℝ] ℝ) y = ‖x‖ * a := by
          simp [f, a]
        rw [hleft]
        change ‖x‖ * a ≤ ‖((y : X))⁺‖
        rw [hpos, norm_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg x) ha'
    obtain ⟨g, hg_eq, hg_le⟩ :=
      exists_extension_of_le_sublinear (⟨p, f⟩ : X →ₗ.[ℝ] ℝ) N hN_hom hN_add hf_le
    have hg_abs : ∀ y : X, |g y| ≤ ‖y‖ := by
      intro y
      refine abs_le.mpr ⟨?_, ?_⟩
      · have hneg := hg_le (-y)
        have hNneg : N (-y) ≤ ‖y‖ := by
          exact (NormedVectorLattice.norm_posPart_le (-y)).trans (by rw [norm_neg])
        have : g (-y) ≤ ‖y‖ := hneg.trans hNneg
        rwa [map_neg, neg_le] at this
      · exact (hg_le y).trans (NormedVectorLattice.norm_posPart_le y)
    let φ : StrongDual ℝ X := g.mkContinuous 1 fun y => by
      simpa [one_mul] using hg_abs y
    refine ⟨φ, ?_, ?_, ?_⟩
    · exact nonneg_iff.mpr fun y hy => by
        have hneg := hg_le (-y)
        have hNneg : N (-y) = 0 := by
          simp [N, posPart_eq_zero.mpr (neg_nonpos.mpr hy)]
        rw [hNneg, map_neg] at hneg
        simpa [φ] using (show 0 ≤ g y by linarith)
    · exact g.mkContinuous_norm_le zero_le_one fun y => by
        simpa [one_mul] using hg_abs y
    · have hxmem : x ∈ p := Submodule.mem_span_singleton_self x
      have hval := hg_eq (⟨x, hxmem⟩ : (⟨p, f⟩ : X →ₗ.[ℝ] ℝ).domain)
      have hcoord : coord (⟨x, hxmem⟩ : p) = 1 := by
        change (ContinuousLinearEquiv.coord ℝ x hx0) (⟨x, hxmem⟩ : ℝ ∙ x) = 1
        exact ContinuousLinearEquiv.coord_self (𝕜 := ℝ) x hx0
      simpa [φ, f, coord, hcoord] using hval

/-- **Dini's theorem**: a monotone net in a normed lattice that converges weakly
converges in norm. -/
theorem tendsto_of_monotone_weak_tendsto {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x : X}
    (hmono : Monotone u ∨ Antitone u)
    (hweak : Filter.Tendsto (fun i => (toWeakSpace ℝ X) (u i)) Filter.atTop
      (nhds ((toWeakSpace ℝ X) x))) :
    Filter.Tendsto u Filter.atTop (nhds x) :=
  NormedVectorLattice.tendsto_of_monotone_weak_tendsto hmono hweak

end WeakConvergence

section BanachLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- For a Banach lattice, every order bounded functional is continuous. -/
noncomputable def ofOrderDualSpace (f : OrderDualSpace X) : StrongDual ℝ X :=
  ⟨f.toLinearMap, IsOrderBounded.continuous f.isOrderBounded'⟩

@[simp]
theorem ofOrderDualSpace_apply (f : OrderDualSpace X) (x : X) :
    ofOrderDualSpace f x = f x := rfl

/-- For a Banach lattice, the order dual and the strong dual are linearly
equivalent: continuous functionals are exactly the order bounded ones. -/
noncomputable def equivOrderDualSpace : StrongDual ℝ X ≃ₗ[ℝ] OrderDualSpace X where
  toFun := toOrderDualSpace
  invFun := ofOrderDualSpace
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

noncomputable instance instMax : Max (StrongDual ℝ X) where
  max f g := ofOrderDualSpace (toOrderDualSpace f ⊔ toOrderDualSpace g)

noncomputable instance instMin : Min (StrongDual ℝ X) where
  min f g := ofOrderDualSpace (toOrderDualSpace f ⊓ toOrderDualSpace g)

theorem toOrderDualSpace_sup (f g : StrongDual ℝ X) :
    toOrderDualSpace (f ⊔ g) = toOrderDualSpace f ⊔ toOrderDualSpace g := by
  ext x; rfl

theorem toOrderDualSpace_inf (f g : StrongDual ℝ X) :
    toOrderDualSpace (f ⊓ g) = toOrderDualSpace f ⊓ toOrderDualSpace g := by
  ext x; rfl

/-- The induced lattice structure on the strong dual: `φ ≤ ψ` iff `φ x ≤ ψ x`
for all positive `x`, with sup/inf transported from the order dual. -/
noncomputable instance instLattice : Lattice (StrongDual ℝ X) :=
  toOrderDualSpace_injective.lattice _ toOrderDualSpace_le
    toOrderDualSpace_lt toOrderDualSpace_sup toOrderDualSpace_inf

/-- Suprema in the strong dual are transported from the order dual. -/
noncomputable instance instSupSet : SupSet (StrongDual ℝ X) where
  sSup S := ofOrderDualSpace (sSup (toOrderDualSpace '' S : Set (OrderDualSpace X)))

/-- The chosen supremum in the strong dual is the least upper bound of every
non-empty bounded-above set. -/
theorem isLUB_sSup (S : Set (StrongDual ℝ X)) (hbdd : BddAbove S)
    (hne : S.Nonempty) : IsLUB S (sSup S) := by
  change IsLUB S (ofOrderDualSpace
    (sSup (toOrderDualSpace '' S : Set (OrderDualSpace X))))
  have hne' : (toOrderDualSpace '' S : Set (OrderDualSpace X)).Nonempty :=
    hne.image _
  have hbdd' : BddAbove (toOrderDualSpace '' S : Set (OrderDualSpace X)) := by
    obtain ⟨u, hu⟩ := hbdd
    exact ⟨toOrderDualSpace u, by
      rintro _ ⟨v, hv, rfl⟩
      exact hu hv⟩
  have hLUB' := OrderDualSpace.isLUB_sSup
    (toOrderDualSpace '' S : Set (OrderDualSpace X)) hbdd' hne'
  have hround : toOrderDualSpace
      (ofOrderDualSpace (sSup (toOrderDualSpace '' S : Set (OrderDualSpace X)))) =
        sSup (toOrderDualSpace '' S : Set (OrderDualSpace X)) := by
    ext x
    rfl
  constructor
  · intro a ha
    change toOrderDualSpace a ≤ toOrderDualSpace
      (ofOrderDualSpace (sSup (toOrderDualSpace '' S : Set (OrderDualSpace X))))
    rw [hround]
    exact hLUB'.1 ⟨a, ha, rfl⟩
  · intro u hu
    change toOrderDualSpace
      (ofOrderDualSpace (sSup (toOrderDualSpace '' S : Set (OrderDualSpace X)))) ≤
        toOrderDualSpace u
    rw [hround]
    exact hLUB'.2 (by
      rintro _ ⟨a, ha, rfl⟩
      exact hu ha)

/-- The strong dual is conditionally complete. -/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice (StrongDual ℝ X) :=
  conditionallyCompleteLatticeOfLatticeOfsSup _ isLUB_sSup

theorem toOrderDualSpace_add (f g : StrongDual ℝ X) :
    toOrderDualSpace (f + g) = toOrderDualSpace f + toOrderDualSpace g := by
  ext; rfl

theorem toOrderDualSpace_smul (r : ℝ) (f : StrongDual ℝ X) :
    toOrderDualSpace (r • f) = r • toOrderDualSpace f := by
  ext; rfl

/-- The strong dual of a Banach lattice is an ordered additive group. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (StrongDual ℝ X) where
  add_le_add_left f g hfg c := by
    change toOrderDualSpace f ≤ toOrderDualSpace g at hfg
    change toOrderDualSpace (f + c) ≤ toOrderDualSpace (g + c)
    rw [toOrderDualSpace_add, toOrderDualSpace_add]
    exact IsOrderedAddMonoid.add_le_add_left _ _ hfg c.toOrderDualSpace

instance instPosSMulMono : PosSMulMono ℝ (StrongDual ℝ X) where
  smul_le_smul_of_nonneg_left {r} hr {f g} hfg := by
    change toOrderDualSpace f ≤ toOrderDualSpace g at hfg
    change toOrderDualSpace (r • f) ≤ toOrderDualSpace (r • g)
    rw [toOrderDualSpace_smul, toOrderDualSpace_smul]
    exact smul_le_smul_of_nonneg_left hfg hr

/-- The strong dual of a Banach lattice is a vector lattice. -/
noncomputable instance instVectorLattice : VectorLattice (StrongDual ℝ X) where

theorem coe_abs_apply (φ : StrongDual ℝ X) (x : X) :
    (|φ| : StrongDual ℝ X) x = |toOrderDualSpace φ| x := rfl

theorem abs_apply_le_abs_apply_abs (φ : StrongDual ℝ X) (x : X) :
    |φ x| ≤ (|φ| : StrongDual ℝ X) (|x|) := by
  rw [coe_abs_apply]
  exact (OrderBoundedHom.isLUB_abs_apply (f := toOrderDualSpace φ)
    (abs_nonneg x)).1 ⟨x, le_refl _, rfl⟩

theorem abs_apply_nonneg (φ : StrongDual ℝ X) {x : X} (hx : 0 ≤ x) :
    0 ≤ (|φ| : StrongDual ℝ X) x := by
  rw [coe_abs_apply]
  exact (OrderBoundedHom.isLUB_abs_apply (f := toOrderDualSpace φ) hx).1
    ⟨0, by simp [hx], by simp⟩

/-- For a positive `x`, `|φ| x` is bounded by `‖φ‖ * ‖x‖`. -/
theorem abs_apply_le_norm_mul (φ : StrongDual ℝ X) {x : X} (hx : 0 ≤ x) :
    (|φ| : StrongDual ℝ X) x ≤ ‖φ‖ * ‖x‖ := by
  rw [coe_abs_apply]
  refine (OrderBoundedHom.isLUB_abs_apply (f := toOrderDualSpace φ) hx).2 ?_
  rintro _ ⟨y, hyx, rfl⟩
  have hy : ‖y‖ ≤ ‖x‖ :=
    norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx]; exact hyx)
  calc |φ y| = ‖φ y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ‖ * ‖y‖ := φ.le_opNorm y
    _ ≤ ‖φ‖ * ‖x‖ := by gcongr

/-- The strong dual carries a solid lattice norm: `|φ| ≤ |ψ|` implies
`‖φ‖ ≤ ‖ψ‖`. -/
instance instHasSolidNorm : HasSolidNorm (StrongDual ℝ X) where
  solid {φ ψ} hφψ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h1 : |φ x| ≤ (|φ| : StrongDual ℝ X) (|x|) :=
      abs_apply_le_abs_apply_abs φ x
    have hOD : (|φ| : StrongDual ℝ X) (|x|) ≤ (|ψ| : StrongDual ℝ X) (|x|) := by
      exact le_iff.mp hφψ _ (abs_nonneg x)
    have h2 : (|ψ| : StrongDual ℝ X) (|x|) ≤ ‖ψ‖ * ‖x‖ := by
      have := abs_apply_le_norm_mul ψ (abs_nonneg x)
      rwa [norm_abs_eq_norm] at this
    calc ‖φ x‖ = |φ x| := Real.norm_eq_abs _
      _ ≤ (|ψ| : StrongDual ℝ X) (|x|) := h1.trans hOD
      _ ≤ ‖ψ‖ * ‖x‖ := h2

/-- The strong dual of a Banach lattice is itself a normed vector lattice. -/
noncomputable instance instNormedVectorLattice :
    NormedVectorLattice (StrongDual ℝ X) where
  norm_smul := norm_smul

/-- The strong dual of a Banach lattice is a Banach lattice. -/
noncomputable instance instBanachLattice : BanachLattice (StrongDual ℝ X) where

/-- The dual norm of the modulus equals the dual norm: `‖|φ|‖ = ‖φ‖`. -/
theorem norm_abs (φ : StrongDual ℝ X) : ‖|φ|‖ = ‖φ‖ :=
  le_antisymm
    (HasSolidNorm.solid (by rw [abs_abs]))
    (HasSolidNorm.solid (by rw [abs_abs]))

/-- For a positive functional, the dual norm is the supremum of `φ x` over the
intersection of the unit ball with the positive cone. -/
theorem norm_of_nonneg {φ : StrongDual ℝ X} (hφ : 0 ≤ φ) :
    ‖φ‖ = sSup ((φ : X → ℝ) '' ({x | ‖x‖ ≤ 1} ∩ {x | 0 ≤ x})) := by
  set S := (φ : X → ℝ) '' ({x | ‖x‖ ≤ 1} ∩ {x | 0 ≤ x})
  have hpos : ∀ {x : X}, 0 ≤ x → 0 ≤ φ x := fun {x} hx =>
    nonneg_iff.mp hφ x hx
  have habs_eq : (|φ| : StrongDual ℝ X) = φ := abs_of_nonneg hφ
  have hub : ∀ s ∈ S, s ≤ ‖φ‖ := by
    rintro _ ⟨x, ⟨hx1, hx0⟩, rfl⟩
    have h1 : ‖φ x‖ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    have h2 : φ x = ‖φ x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos hx0)]
    rw [h2]
    exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hx1 (norm_nonneg _))
  have hbdd : BddAbove S := ⟨‖φ‖, hub⟩
  have hne : S.Nonempty := ⟨0, 0, ⟨by simp, le_refl _⟩, by simp⟩
  have hsup_nn : 0 ≤ sSup S :=
    Real.sSup_nonneg (by rintro _ ⟨y, ⟨_, hy0⟩, rfl⟩; exact hpos hy0)
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ hsup_nn fun x => ?_
    -- ‖φ x‖ ≤ φ |x| (positivity)
    have hbound : ‖φ x‖ ≤ φ (|x|) := by
      rw [Real.norm_eq_abs]
      have h := abs_apply_le_abs_apply_abs φ x
      rw [habs_eq] at h; exact h
    by_cases hx0 : x = 0
    · subst hx0
      simp only [map_zero, norm_zero, mul_zero]
      exact le_refl _
    -- normalise
    have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
    set y : X := ‖x‖⁻¹ • |x|
    have hy_nn : 0 ≤ y := smul_nonneg (inv_nonneg.mpr hxn.le) (abs_nonneg x)
    have hy_norm : ‖y‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hxn.le,
        norm_abs_eq_norm]
      exact (inv_mul_cancel₀ hxn.ne').le
    have hyS : φ y ∈ S := ⟨y, ⟨hy_norm, hy_nn⟩, rfl⟩
    have hyS_le : φ y ≤ sSup S := le_csSup hbdd hyS
    have hφy : φ y = ‖x‖⁻¹ * φ (|x|) := by
      change φ.toLinearMap (‖x‖⁻¹ • |x|) = _
      rw [map_smul]; rfl
    have hφabs : φ (|x|) ≤ ‖x‖ * sSup S := by
      have h1 := mul_le_mul_of_nonneg_left hyS_le hxn.le
      rw [hφy, ← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul] at h1
      exact h1
    exact hbound.trans (hφabs.trans (by rw [mul_comm]))
  · exact csSup_le hne hub

/-- For a Banach lattice, the order dual separates points. -/
theorem orderDual_separatesPoints :
    OrderDualSpace.SeparatesPoints X := by
  intro x hx
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun f => ?_
  simpa using hx (toOrderDualSpace f)

/-- If two functionals are disjoint, every positive vector admits a
positive decomposition on which the sum of their values is arbitrarily small. -/
theorem exists_decomposition_apply_add_apply_lt
    {φ ψ : StrongDual ℝ X} (hdisj : φ ⊓ ψ = 0)
    {u : X} (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ u₁ u₂ : X, 0 ≤ u₁ ∧ 0 ≤ u₂ ∧ u₁ + u₂ = u ∧
      φ u₁ + ψ u₂ < ε := by
  let φ' : OrderDualSpace X := toOrderDualSpace φ
  let ψ' : OrderDualSpace X := toOrderDualSpace ψ
  have hglb : IsGLB
      {r : ℝ | ∃ y z : X, 0 ≤ y ∧ 0 ≤ z ∧ y + z = u ∧
        r = φ' y + ψ' z} 0 := by
    have h := OrderDualSpace.isGLB_inf_apply (φ := φ') (ψ := ψ') hu
    have hzero : (φ' ⊓ ψ') u = 0 := by
      dsimp [φ', ψ']
      change (φ ⊓ ψ) u = 0
      rw [hdisj]
      rfl
    simpa [hzero] using h
  by_contra hno
  have hlower : ε ∈ lowerBounds
      {r : ℝ | ∃ y z : X, 0 ≤ y ∧ 0 ≤ z ∧ y + z = u ∧
        r = φ' y + ψ' z} := by
    rintro r ⟨y, z, hy, hz, hyz, rfl⟩
    exact le_of_not_gt (fun hlt => hno ⟨y, z, hy, hz, hyz, hlt⟩)
  have hε_le_zero : ε ≤ 0 := hglb.2 hlower
  exact (not_lt_of_ge hε_le_zero) hε

end BanachLattice

end StrongDual
