/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.OrderClosures.BanLat.Operators.Positive



/-!
# Order bounded operators

A linear map between vector lattices is **order bounded** if it maps order bounded
sets to order bounded sets. Equivalently, for every positive `x`, there exists a
positive `y` such that `|z| ≤ x` implies `|T z| ≤ y`. Every positive operator is
order bounded, and every order bounded operator from a Banach lattice to a normed
vector lattice is continuous. The bundled type `OrderBoundedHom X Y` carries
the basic algebraic and order instances.
-/

@[expose] public section

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A linear map is *order bounded* if for every positive `x`, the image of the
symmetric order interval `{z | |z| ≤ x}` is order bounded. -/
def IsOrderBounded (f : X →ₗ[ℝ] Y) : Prop :=
  ∀ x : X, 0 ≤ x → ∃ y : Y, 0 ≤ y ∧ ∀ z : X, |z| ≤ x → |f z| ≤ y

namespace Positive

/-- Every positive operator is order bounded. -/
theorem isOrderBounded {f : X →ₗ[ℝ] Y} (hf : Positive f) :
    IsOrderBounded f := by
  intro x hx
  refine ⟨f x, hf x hx, fun z hz => ?_⟩
  exact (abs_le_map_abs hf z).trans ((monotone_iff.mpr hf) hz)

end Positive

namespace IsOrderBounded

/-- The sum of order bounded operators is order bounded. -/
theorem add {f g : X →ₗ[ℝ] Y} (hf : IsOrderBounded f)
    (hg : IsOrderBounded g) :
    IsOrderBounded (f + g) := by
  intro x hx
  obtain ⟨yf, hyf, hbf⟩ := hf x hx
  obtain ⟨yg, hyg, hbg⟩ := hg x hx
  refine ⟨yf + yg, add_nonneg hyf hyg, fun z hz => ?_⟩
  simp only [LinearMap.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hbf z hz) (hbg z hz))

/-- The negation of an order bounded operator is order bounded. -/
theorem neg {f : X →ₗ[ℝ] Y} (hf : IsOrderBounded f) :
    IsOrderBounded (-f) := by
  intro x hx
  obtain ⟨y, hy, hb⟩ := hf x hx
  exact ⟨y, hy, fun z hz => by
    simp only [LinearMap.neg_apply, abs_neg]; exact hb z hz⟩

/-- The difference of order bounded operators is order bounded. -/
theorem sub {f g : X →ₗ[ℝ] Y} (hf : IsOrderBounded f)
    (hg : IsOrderBounded g) :
    IsOrderBounded (f - g) := by
  rw [sub_eq_add_neg]; exact add hf (neg hg)

/-- A scalar multiple of an order bounded operator is order
bounded. -/
theorem smul {f : X →ₗ[ℝ] Y} (hf : IsOrderBounded f)
    (r : ℝ) : IsOrderBounded (r • f) := by
  intro x hx
  obtain ⟨y, hy, hb⟩ := hf x hx
  refine ⟨|r| • y, smul_nonneg (abs_nonneg r) hy, fun z hz => ?_⟩
  simp only [LinearMap.smul_apply]
  rw [abs_smul' (f z) r]
  exact smul_le_smul_of_nonneg_left (hb z hz) (abs_nonneg r)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]

/-- Every order bounded operator from a Banach lattice to a normed vector lattice
is continuous. -/
theorem continuous {f : X →ₗ[ℝ] Y} (hf : IsOrderBounded f) :
    Continuous f := by
  by_contra hcont
  have hunb : ∀ C : ℝ, ∃ x : X, C * ‖x‖ < ‖f x‖ := by
    by_contra h; push Not at h; obtain ⟨C, hC⟩ := h
    exact hcont (continuous_of_linear_of_bound f.map_add f.map_smul hC)
  have hseq : ∀ n : ℕ, ∃ x : X, ‖x‖ ≤ (1 / 2 : ℝ) ^ n ∧ (n : ℝ) < ‖f x‖ := by
    intro n
    obtain ⟨z, hz⟩ := hunb ((n : ℝ) * (2 : ℝ) ^ n)
    have hznz : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨((2 : ℝ) ^ n * ‖z‖)⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      simp [one_div, mul_comm]
    · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [lt_inv_mul_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      linarith [mul_comm ((n : ℝ) * (2 : ℝ) ^ n) ‖z‖]
  choose x hxn hxf using hseq
  have habs : Summable (fun n => |x n|) :=
    .of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (fun n => by rw [norm_abs_eq_norm]; exact hxn n)
  set y := ∑' n, |x n|
  have hy : 0 ≤ y := tsum_nonneg (fun n => abs_nonneg _)
  have hle : ∀ n, |x n| ≤ y :=
    fun n => habs.le_tsum n (fun j _ => abs_nonneg _)
  obtain ⟨u, _hu, hbound⟩ := hf y hy
  obtain ⟨N, hN⟩ := exists_nat_gt ‖u‖
  have hfN : ‖f (x N)‖ ≤ ‖u‖ := by
    have hab : |f (x N)| ≤ u := hbound (x N) (hle N)
    exact norm_le_norm_of_abs_le_abs (hab.trans (le_abs_self u))
  exact absurd (lt_of_lt_of_le (hxf N) hfN) (not_lt.mpr hN.le)

end IsOrderBounded

/-! ### The space of order bounded operators -/

/-- The type of order bounded linear operators from `X` to `Y`. -/
structure OrderBoundedHom (X : Type*) (Y : Type*)
    [AddCommGroup X] [AddCommGroup Y] [Lattice X]
    [Lattice Y] [IsOrderedAddMonoid X]
    [IsOrderedAddMonoid Y] [VectorLattice X]
    [VectorLattice Y] extends X →ₗ[ℝ] Y where
  isOrderBounded' : IsOrderBounded toLinearMap

namespace OrderBoundedHom

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X]
  [VectorLattice Y]

/-- Coercion from `OrderBoundedHom` to functions. -/
instance instFunLike :
    FunLike (OrderBoundedHom X Y) X Y where
  coe f := f.toFun
  coe_injective := by
    intro f g h; cases f; cases g; congr 1
    exact LinearMap.ext (congrFun h)

@[ext]
theorem ext {f g : OrderBoundedHom X Y}
    (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

@[simp]
theorem coe_toLinearMap (f : OrderBoundedHom X Y) :
    ⇑f.toLinearMap = ⇑f := rfl

/-- The underlying linear map of an order-bounded operator has the same values. -/
@[simp]
theorem toLinearMap_apply (f : OrderBoundedHom X Y) (x : X) :
    f.toLinearMap x = f x := rfl

theorem toLinearMap_injective :
    Function.Injective (OrderBoundedHom.toLinearMap :
      OrderBoundedHom X Y → X →ₗ[ℝ] Y) := fun _ _ h =>
  ext fun x => congrFun (congrArg DFunLike.coe h) x

/-- Bundle a positive linear operator as an `OrderBoundedHom`. -/
def ofPositive (f : X →ₗ[ℝ] Y) (hf : Positive f) : OrderBoundedHom X Y :=
  ⟨f, hf.isOrderBounded⟩

@[simp]
theorem ofPositive_apply (f : X →ₗ[ℝ] Y) (hf : Positive f) (x : X) :
    ofPositive f hf x = f x := rfl

instance instZero : Zero (OrderBoundedHom X Y) :=
  ⟨ofPositive 0 fun _ _ => by simp⟩

/-- The zero order-bounded operator vanishes at every point. -/
@[simp]
theorem zero_apply (x : X) : (0 : OrderBoundedHom X Y) x = (0 : Y) := rfl

instance instAdd : Add (OrderBoundedHom X Y) :=
  ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap,
    IsOrderBounded.add f.isOrderBounded' g.isOrderBounded'⟩⟩

instance instNeg : Neg (OrderBoundedHom X Y) :=
  ⟨fun f => ⟨-f.toLinearMap,
    IsOrderBounded.neg f.isOrderBounded'⟩⟩

instance instSub : Sub (OrderBoundedHom X Y) :=
  ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap,
    IsOrderBounded.sub f.isOrderBounded' g.isOrderBounded'⟩⟩

instance instSMulNat : SMul ℕ (OrderBoundedHom X Y) :=
  ⟨fun n f => ⟨n • f.toLinearMap, by
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    exact IsOrderBounded.smul f.isOrderBounded' n⟩⟩

instance instSMulInt : SMul ℤ (OrderBoundedHom X Y) :=
  ⟨fun n f => ⟨n • f.toLinearMap, by
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact IsOrderBounded.smul f.isOrderBounded' n⟩⟩

noncomputable instance :
    AddCommGroup (OrderBoundedHom X Y) :=
  toLinearMap_injective.addCommGroup _
    rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

noncomputable instance :
    Module ℝ (OrderBoundedHom X Y) where
  smul r f := ⟨r • f.toLinearMap,
    IsOrderBounded.smul f.isOrderBounded' r⟩
  one_smul f := ext fun x => one_smul ℝ (f x)
  mul_smul r s f := ext fun x => mul_smul r s (f x)
  smul_zero r := ext fun _ => smul_zero r
  smul_add r f g := ext fun x => smul_add r (f x) (g x)
  add_smul r s f := ext fun x => add_smul r s (f x)
  zero_smul f := ext fun x => zero_smul ℝ (f x)

noncomputable instance :
    PartialOrder (OrderBoundedHom X Y) :=
  PartialOrder.lift OrderBoundedHom.toLinearMap toLinearMap_injective

/-- The operator ordering: `f ≤ g` iff for every `x ≥ 0` we have
`f x ≤ g x`. -/
theorem le_iff {f g : OrderBoundedHom X Y} :
    f ≤ g ↔ ∀ x : X, 0 ≤ x → f x ≤ g x :=
  Positive.le_iff

instance :
    IsOrderedAddMonoid (OrderBoundedHom X Y) where
  add_le_add_left _ _ hab c := le_iff.mpr fun x hx =>
    add_le_add_left (le_iff.mp hab x hx) (c x)

instance :
    PosSMulMono ℝ (OrderBoundedHom X Y) where
  smul_le_smul_of_nonneg_left _ hr _ _ hfg := le_iff.mpr fun x hx =>
    smul_le_smul_of_nonneg_left (le_iff.mp hfg x hx) hr

end OrderBoundedHom
