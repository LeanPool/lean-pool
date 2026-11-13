/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.FBLOrderContinuity.BanLat.Operators.OrderBounded
public import LeanPool.FBLOrderContinuity.BanLat.Operators.Regular
public import LeanPool.OrderClosures.BanLat.OrderComplete
public import LeanPool.FBLOrderContinuity.BanLat.RieszDec
public import LeanPool.FBLOrderContinuity.BanLat.Substructures.Band.PPP



/-!
# The Riesz-Kantorovich theorem

When the codomain `Y` is order complete, the space `OrderBoundedHom X Y` of
order bounded operators is an order complete vector lattice, with explicit
formulas for the lattice operations (the **Riesz-Kantorovich formulas**).
-/

@[expose] public section

namespace OrderBoundedHom

open scoped Pointwise

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X]
  [VectorLattice Y]

/-! ### Positive part construction for the Riesz-Kantorovich theorem -/

/-- Values of an order-bounded operator on the interval from zero to `x`. -/
def ppSet (f : OrderBoundedHom X Y) (x : X) : Set Y :=
  { w | ∃ y, 0 ≤ y ∧ y ≤ x ∧ w = f y }


lemma ppSet_nonempty (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : (ppSet f x).Nonempty :=
  ⟨0, 0, le_rfl, hx, (map_zero f.toLinearMap).symm⟩


lemma ppSet_bddAbove (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : BddAbove (ppSet f x) := by
  obtain ⟨u, _, hbound⟩ := f.isOrderBounded' x hx
  exact ⟨u, fun _ ⟨y, hy, hyx, hw⟩ => hw ▸
    (le_abs_self _).trans
      (hbound y (sup_le hyx (neg_nonpos_of_nonneg hy |>.trans hx)))⟩

/-- The Riesz–Kantorovich supremum on positive vectors, extended by zero elsewhere. -/
noncomputable def ppFun (f : OrderBoundedHom X Y)
    (x : X) : Y := by
  classical
  exact if 0 ≤ x then sSup (ppSet f x) else 0

lemma ppFun_isLUB (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : IsLUB (ppSet f x) (ppFun f x) := by
  simp only [ppFun, ite_eq_left hx]
  exact isLUB_csSup (ppSet_nonempty f hx) (ppSet_bddAbove f hx)

lemma ppFun_nonneg (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : 0 ≤ ppFun f x :=
  (ppFun_isLUB f hx).1
    ⟨0, le_rfl, hx, (map_zero f.toLinearMap).symm⟩

lemma le_ppFun (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : f x ≤ ppFun f x :=
  (ppFun_isLUB f hx).1 ⟨x, hx, le_refl x, rfl⟩

lemma ppFun_le (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) {u : Y}
    (hu : u ∈ upperBounds (ppSet f x)) : ppFun f x ≤ u :=
  (ppFun_isLUB f hx).2 hu

lemma ppFun_add (f : OrderBoundedHom X Y) {x y : X}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ppFun f (x + y) = ppFun f x + ppFun f y := by
  apply le_antisymm
  · -- ≤: Riesz decomposition
    apply ppFun_le f (add_nonneg hx hy)
    intro w ⟨z, hz, hzxy, hw⟩
    obtain ⟨z₁, z₂, hz₁, hz₁x, hz₂, hz₂y, hsum⟩ :=
      riesz_decomposition z x y hz hx hy hzxy
    rw [hw, hsum]
    change f.toLinearMap (z₁ + z₂) ≤ ppFun f x + ppFun f y
    rw [map_add]
    exact add_le_add
      ((ppFun_isLUB f hx).1 ⟨z₁, hz₁, hz₁x, rfl⟩)
      ((ppFun_isLUB f hy).1 ⟨z₂, hz₂, hz₂y, rfl⟩)
  · -- ≥: double LUB argument
    have step1 : ∀ w₁ ∈ ppSet f x, ∀ w₂ ∈ ppSet f y,
        w₁ + w₂ ≤ ppFun f (x + y) := by
      intro w₁ ⟨z₁, hz₁, hz₁x, hw₁⟩ w₂ ⟨z₂, hz₂, hz₂y, hw₂⟩
      rw [hw₁, hw₂]
      change f.toLinearMap z₁ + f.toLinearMap z₂ ≤ ppFun f (x + y)
      rw [← map_add]
      exact (ppFun_isLUB f (add_nonneg hx hy)).1
        ⟨z₁ + z₂, add_nonneg hz₁ hz₂, add_le_add hz₁x hz₂y, rfl⟩
    have step2 : ∀ w₂ ∈ ppSet f y,
        ppFun f x + w₂ ≤ ppFun f (x + y) := by
      intro w₂ hw₂
      have hub : ppFun f (x + y) - w₂ ∈ upperBounds (ppSet f x) :=
        fun w₁ hw₁ =>
          le_sub_iff_add_le.mpr (step1 w₁ hw₁ w₂ hw₂)
      exact le_sub_iff_add_le.mp (ppFun_le f hx hub)
    have hub : ppFun f (x + y) - ppFun f x ∈
        upperBounds (ppSet f y) :=
      fun w₂ hw₂ => le_sub_iff_add_le.mpr
        (by rw [add_comm]; exact step2 w₂ hw₂)
    rw [add_comm]
    exact le_sub_iff_add_le.mp (ppFun_le f hy hub)

/-! ### The positive part operator -/

/-- The linear extension of the Riesz–Kantorovich positive-cone formula. -/
noncomputable def ppOp (f : OrderBoundedHom X Y) :
    X →ₗ[ℝ] Y := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension (fun x hx => ppFun_nonneg f hx)
    (fun _ _ hx hy => ppFun_add f hx hy)

lemma ppOp_apply_nonneg (f : OrderBoundedHom X Y)
    {x : X} (hx : 0 ≤ x) : ppOp f x = ppFun f x := by
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension_nonneg (fun x hx => ppFun_nonneg f hx)
    (fun _ _ hx hy => ppFun_add f hx hy) hx

lemma ppOp_positive (f : OrderBoundedHom X Y) :
    Positive (ppOp f) := by
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension_positive
    (fun x hx => ppFun_nonneg f hx)
    (fun _ _ hx hy => ppFun_add f hx hy)

lemma le_ppOp (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : f x ≤ ppOp f x :=
  ppOp_apply_nonneg f hx ▸ le_ppFun f hx

lemma ppOp_le (f g : OrderBoundedHom X Y)
    (hg0 : ∀ x : X, 0 ≤ x → 0 ≤ g x)
    (hgf : ∀ x : X, 0 ≤ x → f x ≤ g x)
    {x : X} (hx : 0 ≤ x) : ppOp f x ≤ g x := by
  rw [ppOp_apply_nonneg f hx]
  apply ppFun_le f hx
  intro _ ⟨y, hy, hyx, hw⟩
  rw [hw]
  exact (hgf y hy).trans
    ((Positive.monotone_iff.mpr
      (show Positive g.toLinearMap from hg0)) hyx)

/-! ### Sup, inf and lattice laws -/

/-- The positive part of an order-bounded operator. -/
noncomputable def obPosPart
    (f : OrderBoundedHom X Y) : OrderBoundedHom X Y :=
  ⟨ppOp f, Positive.isOrderBounded (ppOp_positive f)⟩

lemma obPosPart_apply (f : OrderBoundedHom X Y) (x : X) :
    obPosPart f x = ppOp f x := rfl

lemma obPosPart_nonneg (f : OrderBoundedHom X Y) :
    (0 : OrderBoundedHom X Y) ≤ obPosPart f :=
  le_iff.mpr fun x hx => by
    simpa only [zero_apply, obPosPart_apply] using ppOp_positive f x hx

lemma le_obPosPart (f : OrderBoundedHom X Y) :
    f ≤ obPosPart f :=
  le_iff.mpr fun _ hx => le_ppOp f hx

lemma obPosPart_le {f g : OrderBoundedHom X Y}
    (hg0 : (0 : OrderBoundedHom X Y) ≤ g) (hgf : f ≤ g) :
    obPosPart f ≤ g :=
  le_iff.mpr fun x hx => by
    apply ppOp_le f g _ _ hx
    · intro y hy
      simpa only [zero_apply] using le_iff.mp hg0 y hy
    · intro y hy; exact le_iff.mp hgf y hy

/-- Supremum of two order-bounded operators, constructed from the positive part. -/
noncomputable def obSup
    (f g : OrderBoundedHom X Y) : OrderBoundedHom X Y :=
  g + obPosPart (f - g)

/-- Infimum of two order-bounded operators, constructed from their supremum. -/
noncomputable def obInf
    (f g : OrderBoundedHom X Y) : OrderBoundedHom X Y :=
  f + g - obSup f g

lemma le_obSup_left (f g : OrderBoundedHom X Y) :
    f ≤ obSup f g := by
  change f ≤ g + obPosPart (f - g)
  have h1 := add_le_add_left (le_obPosPart (f - g)) g
  rw [sub_add_cancel, add_comm] at h1
  exact h1

lemma le_obSup_right (f g : OrderBoundedHom X Y) :
    g ≤ obSup f g := by
  change g ≤ g + obPosPart (f - g)
  exact le_add_of_nonneg_right (obPosPart_nonneg (f - g))

lemma obSup_le {f g h : OrderBoundedHom X Y}
    (hfh : f ≤ h) (hgh : g ≤ h) :
    obSup f g ≤ h := by
  change g + obPosPart (f - g) ≤ h
  have h1 : obPosPart (f - g) ≤ h - g :=
    obPosPart_le (sub_nonneg.mpr hgh)
      (sub_le_sub_right hfh g)
  have h2 := add_le_add_left h1 g
  rw [sub_add_cancel, add_comm] at h2
  exact h2

lemma obInf_le_left (f g : OrderBoundedHom X Y) :
    obInf f g ≤ f := by
  have : obInf f g = f - obPosPart (f - g) := by
    change f + g - (g + obPosPart (f - g)) =
      f - obPosPart (f - g); abel
  rw [this]
  exact sub_le_self f (obPosPart_nonneg (f - g))

lemma obInf_le_right (f g : OrderBoundedHom X Y) :
    obInf f g ≤ g := by
  have h1 : obInf f g = f - obPosPart (f - g) := by
    change f + g - (g + obPosPart (f - g)) =
      f - obPosPart (f - g); abel
  rw [h1]
  calc f - obPosPart (f - g)
      ≤ f - (f - g) :=
        sub_le_sub_left (le_obPosPart (f - g)) f
    _ = g := by abel

lemma le_obInf {f g h : OrderBoundedHom X Y}
    (hhf : h ≤ f) (hhg : h ≤ g) :
    h ≤ obInf f g := by
  have key : obPosPart (f - g) ≤ f - h :=
    obPosPart_le (sub_nonneg.mpr hhf)
      (sub_le_sub_left hhg f)
  have h2 : obInf f g = f - obPosPart (f - g) := by
    change f + g - (g + obPosPart (f - g)) =
      f - obPosPart (f - g); abel
  rw [h2]
  calc h = f - (f - h) := by abel
    _ ≤ f - obPosPart (f - g) :=
        sub_le_sub_left key f

/-- When the codomain is order complete, the space of order bounded
operators is a lattice. -/
noncomputable instance instLattice :
    Lattice (OrderBoundedHom X Y) :=
  { (inferInstance :
      PartialOrder (OrderBoundedHom X Y)) with
    sup := obSup
    inf := obInf
    le_sup_left := le_obSup_left
    le_sup_right := le_obSup_right
    sup_le := fun _ _ _ hfh hgh => obSup_le hfh hgh
    inf_le_left := obInf_le_left
    inf_le_right := obInf_le_right
    le_inf := fun _ _ _ hhf hhg => le_obInf hhf hhg }

/-- When the codomain is order complete, the space of order bounded
operators is a vector lattice. -/
noncomputable instance instVectorLattice :
    VectorLattice (OrderBoundedHom X Y) :=
  { (inferInstance : Module ℝ (OrderBoundedHom X Y)),
    (inferInstance :
      PosSMulMono ℝ (OrderBoundedHom X Y)) with }

/-! ### Riesz-Kantorovich formulas -/


lemma sub_apply (f g : OrderBoundedHom X Y) (y : X) :
    (f - g : OrderBoundedHom X Y) y = f y - g y :=
  show (f.toLinearMap - g.toLinearMap) y = _ from
  LinearMap.sub_apply _ _ _


lemma add_apply' (f g : OrderBoundedHom X Y) (y : X) :
    (f + g : OrderBoundedHom X Y) y = f y + g y :=
  show (f.toLinearMap + g.toLinearMap) y = _ from
  LinearMap.add_apply _ _ _


lemma map_sub_val (f : OrderBoundedHom X Y) (a b : X) :
    f (a - b) = f a - f b :=
  show f.toLinearMap (a - b) = _ from map_sub f.toLinearMap a b

private lemma map_neg_value (f : OrderBoundedHom X Y) (x : X) : f (-x) = -f x :=
  map_neg f.toLinearMap x

lemma sup_zero_eq_obPosPart
    (f : OrderBoundedHom X Y) :
    f ⊔ 0 = obPosPart f := by
  have : f ⊔ (0 : OrderBoundedHom X Y) =
      (0 : OrderBoundedHom X Y) + obPosPart (f - 0) := rfl
  rw [sub_zero, zero_add] at this; exact this

lemma posPart_apply_eq_ppFun
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    f⁺ x = ppFun f x := by
  rw [posPart_def, sup_zero_eq_obPosPart]
  simpa only [obPosPart_apply] using ppOp_apply_nonneg f hx

/-- The positive part at a positive element is the supremum over
the order interval `[0, x]`. -/
theorem isLUB_posPart_apply
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y, 0 ≤ y ∧ y ≤ x ∧ w = f y}
      (f⁺ x) := by
  rw [posPart_apply_eq_ppFun hx]; exact ppFun_isLUB f hx

/-- The negative part at a positive element. -/
theorem isLUB_negPart_apply
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y, 0 ≤ y ∧ y ≤ x ∧ w = -(f y)}
      (f⁻ x) := by
  have h : f⁻ = (-f)⁺ := by rw [negPart_def, posPart_def]
  rw [h, posPart_apply_eq_ppFun hx]
  exact ppFun_isLUB (-f) hx

/-- The supremum of order bounded operators at a positive element
is given by the Riesz-Kantorovich formula. -/
theorem isLUB_sup_apply
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB
      {w | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊔ g) x) := by
  have hval : (f ⊔ g) x = g x + (f - g)⁺ x := by
    have h := sup_eq_add_posPart_sub f g; rw [h, add_apply']
  have hbridge : ∀ y : X, f y + g (x - y) = g x + (f - g) y := by
    intro y; rw [sub_apply, map_sub_val]; abel
  rw [hval, posPart_apply_eq_ppFun hx]
  have hPP := ppFun_isLUB (f - g) hx
  constructor
  · intro w ⟨y, z, hy, hz, hyz, hw⟩
    have hyx : y ≤ x := hyz ▸ le_add_of_nonneg_right hz
    rw [hw, show z = x - y from eq_sub_of_add_eq' hyz, hbridge]
    gcongr; exact hPP.1 ⟨y, hy, hyx, rfl⟩
  · intro u hu
    rw [show g x + ppFun (f - g) x =
        ppFun (f - g) x + g x from add_comm _ _,
      ← le_sub_iff_add_le]
    apply hPP.2
    intro v ⟨y, hy, hyx, hv⟩
    rw [le_sub_iff_add_le, hv, add_comm, ← hbridge]
    exact hu ⟨y, x - y, hy, sub_nonneg.mpr hyx, by abel, rfl⟩


lemma map_add_val (f : OrderBoundedHom X Y) (a b : X) :
    f (a + b) = f a + f b :=
  show f.toLinearMap _ = _ from map_add f.toLinearMap a b


lemma neg_apply' (f : OrderBoundedHom X Y) (y : X) :
    (-f : OrderBoundedHom X Y) y = -(f y) :=
  show (-f.toLinearMap) y = _ from LinearMap.neg_apply _ _

/-- The infimum of order bounded operators at a positive element. -/
theorem isGLB_inf_apply
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsGLB
      {w | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊓ g) x) := by
  set S := {w : Y | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x
      ∧ w = f y + g z}
  set c := f x + g x
  have hsym : ∀ w ∈ S, c - w ∈ S := by
    intro w ⟨y, z, hy, hz, hyz, hw⟩
    refine ⟨z, y, hz, hy, by rw [add_comm]; exact hyz, ?_⟩
    rw [hw]; simp only [c]
    rw [← hyz, map_add_val f y z, map_add_val g y z]; abel
  have hinf : (f ⊓ g) x = c - (f ⊔ g) x := by
    have h : (f ⊓ g : OrderBoundedHom X Y) = f + g - (f ⊔ g) :=
      eq_sub_of_add_eq' ((add_comm _ _).trans (inf_add_sup f g))
    rw [h, sub_apply, add_apply']
  rw [hinf]
  have hLUB : IsLUB S ((f ⊔ g) x) := isLUB_sup_apply hx
  exact ⟨fun _ hw => sub_le_comm.mp (hLUB.1 (hsym _ hw)),
    fun _ hb => le_sub_comm.mpr
      (hLUB.2 fun _ hw => le_sub_comm.mp (hb (hsym _ hw)))⟩

omit [VectorLattice X] in
lemma nonneg_of_disjoint_add_eq {y z x : X}
    (hx : 0 ≤ x) (hdisj : IsVLDisjoint y z) (hsum : y + z = x) :
    0 ≤ y ∧ 0 ≤ z := by
  have habs : |y| + |z| = x := by
    calc
      |y| + |z| = |y + z| := (abs_add_of_isVLDisjoint hdisj).symm
      _ = x := by rw [hsum, abs_of_nonneg hx]
  rw [← hsum] at habs
  have hsub : (|y| - y) + (|z| - z) = 0 := by
    calc
      (|y| - y) + (|z| - z) = (|y| + |z|) - (y + z) := by abel
      _ = 0 := by rw [habs, sub_self]
  have hy' : 0 ≤ |y| - y := sub_nonneg.mpr (le_abs_self y)
  have hz' : 0 ≤ |z| - z := sub_nonneg.mpr (le_abs_self z)
  have hy0 : |y| - y = 0 := by
    apply le_antisymm
    · calc
        |y| - y ≤ (|y| - y) + (|z| - z) := le_add_of_nonneg_right hz'
        _ = 0 := hsub
    · exact hy'
  have hz0 : |z| - z = 0 := by
    rw [hy0, zero_add] at hsub
    exact hsub
  constructor
  · rw [(sub_eq_zero.mp hy0).symm]
    exact abs_nonneg y
  · rw [(sub_eq_zero.mp hz0).symm]
    exact abs_nonneg z

lemma isGLB_inf_apply_disjoint_zero
    [HasPrincipalProjectionProperty X]
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x)
    (hfg0 : f ⊓ g = 0) :
    IsGLB
      {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
        ∧ w = f y + g z}
      0 := by
  let S : Set Y := {w | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x ∧ w = f y + g z}
  let D : Set Y := {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x ∧ w = f y + g z}
  have hf0 : (0 : OrderBoundedHom X Y) ≤ f := by
    simpa [hfg0] using (inf_le_left : f ⊓ g ≤ f)
  have hg0 : (0 : OrderBoundedHom X Y) ≤ g := by
    simpa [hfg0] using (inf_le_right : f ⊓ g ≤ g)
  have hS : IsGLB S 0 := by
    simpa only [S, hfg0, zero_apply] using (isGLB_inf_apply (f := f) (g := g) hx)
  refine ⟨?_, ?_⟩
  · intro w hw
    rcases hw with ⟨y, z, hdisj, hyz, rfl⟩
    obtain ⟨hy, hz⟩ := nonneg_of_disjoint_add_eq hx hdisj hyz
    exact add_nonneg (le_iff.mp hf0 y hy) (le_iff.mp hg0 z hz)
  · intro b hb
    have hhalf_lb : (1 / 2 : ℝ) • b ∈ lowerBounds S := by
      intro w hw
      rcases hw with ⟨y, z, hy, hz, hyz, rfl⟩
      obtain ⟨u, v, huv, hu, hv, hu_le, hv_le, huvsum⟩ :=
        exists_disjoint_add_eq_add_of_hasPrincipalProjectionProperty hy hz
      have hbuv : b ≤ f u + g v :=
        hb ⟨u, v, huv, huvsum.trans hyz, rfl⟩
      have hfu : f u ≤ (2 : ℕ) • f y := by
        have hmono : Monotone f.toLinearMap :=
          Positive.monotone_iff.mpr (show Positive f.toLinearMap from le_iff.mp hf0)
        calc
          f u ≤ f ((2 : ℕ) • y) := hmono hu_le
          _ = (2 : ℕ) • f y := by
            change f.toLinearMap ((2 : ℕ) • y) = (2 : ℕ) • f.toLinearMap y
            rw [map_nsmul]
      have hgv : g v ≤ (2 : ℕ) • g z := by
        have hmono : Monotone g.toLinearMap :=
          Positive.monotone_iff.mpr (show Positive g.toLinearMap from le_iff.mp hg0)
        calc
          g v ≤ g ((2 : ℕ) • z) := hmono hv_le
          _ = (2 : ℕ) • g z := by
            change g.toLinearMap ((2 : ℕ) • z) = (2 : ℕ) • g.toLinearMap z
            rw [map_nsmul]
      calc
        (1 / 2 : ℝ) • b ≤ (1 / 2 : ℝ) • (f u + g v) :=
          smul_le_smul_of_nonneg_left hbuv (by positivity)
        _ ≤ (1 / 2 : ℝ) • ((2 : ℕ) • f y + (2 : ℕ) • g z) :=
          smul_le_smul_of_nonneg_left (add_le_add hfu hgv) (by positivity)
        _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • f y +
            (((1 / 2 : ℝ) + (1 / 2 : ℝ)) : ℝ) • g z := by
          rw [two_nsmul, two_nsmul, smul_add, smul_add, smul_add, ← add_smul, ← add_smul]
        _ = (1 : ℝ) • f y + (1 : ℝ) • g z := by
          rw [show ((1 / 2 : ℝ) + (1 / 2 : ℝ)) = 1 by norm_num]
        _ = f y + g z := by simp
    have hhalf_le : (1 / 2 : ℝ) • b ≤ 0 := hS.2 hhalf_lb
    have htwo :
        (2 : ℝ) • ((1 / 2 : ℝ) • b) ≤ (2 : ℝ) • (0 : Y) :=
      smul_le_smul_of_nonneg_left hhalf_le (show (0 : ℝ) ≤ 2 by positivity)
    simpa using htwo

lemma isGLB_inf_apply_disjoint_aux
    [HasPrincipalProjectionProperty X]
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsGLB
      {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊓ g) x) := by
  let h : OrderBoundedHom X Y := f ⊓ g
  let f' : OrderBoundedHom X Y := f - h
  let g' : OrderBoundedHom X Y := g - h
  let D' : Set Y := {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x ∧ w = f' y + g' z}
  have hf'0 : (0 : OrderBoundedHom X Y) ≤ f' := by
    refine le_iff.mpr ?_
    intro y hy
    dsimp [f', h]
    rw [sub_apply]
    exact sub_nonneg.mpr (le_iff.mp inf_le_left y hy)
  have hg'0 : (0 : OrderBoundedHom X Y) ≤ g' := by
    refine le_iff.mpr ?_
    intro y hy
    dsimp [g', h]
    rw [sub_apply]
    exact sub_nonneg.mpr (le_iff.mp inf_le_right y hy)
  have hdisj' : IsVLDisjoint f' g' := by
    dsimp [f', g', h]
    exact isVLDisjoint_sub_inf f g
  have hfg'0 : f' ⊓ g' = 0 :=
    inf_eq_zero_of_isVLDisjoint hf'0 hg'0 hdisj'
  have hD' : IsGLB D' 0 :=
    isGLB_inf_apply_disjoint_zero (f := f') (g := g') hx hfg'0
  have hset :
      ((fun w => h x + w) '' D') =
        {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
          ∧ w = f y + g z} := by
    ext w
    constructor
    · rintro ⟨w', ⟨y, z, hdisj, hyz, hw'⟩, rfl⟩
      refine ⟨y, z, hdisj, hyz, ?_⟩
      rw [hw']
      dsimp [f', g', h]
      rw [sub_apply, sub_apply, ← hyz, map_add_val (f ⊓ g) y z]
      abel
    · rintro ⟨y, z, hdisj, hyz, rfl⟩
      refine ⟨f' y + g' z, ⟨y, z, hdisj, hyz, rfl⟩, ?_⟩
      dsimp [f', g', h]
      rw [sub_apply, sub_apply, ← hyz, map_add_val (f ⊓ g) y z]
      abel
  rw [← hset]
  simpa [h] using isGLB_const_add (h x) hD'

/-- **Disjoint Riesz-Kantorovich formula for the supremum.** If `X` has the
Principal Projection Property, then for `x ≥ 0` the value `(f ⊔ g) x` is the
supremum of `f y + g z` over all disjoint decompositions `x = y + z`. -/
theorem isLUB_sup_apply_disjoint [HasPrincipalProjectionProperty X]
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB
      {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊔ g) x) := by
  have hneg :
      IsGLB
        {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
          ∧ w = (-f) y + (-g) z}
        (((-f) ⊓ (-g)) x) :=
    isGLB_inf_apply_disjoint_aux (f := -f) (g := -g) hx
  have hval : (((-f) ⊓ (-g)) x) = -((f ⊔ g) x) := by
    rw [show ((-f) ⊓ (-g) : OrderBoundedHom X Y) = -(f ⊔ g) by rw [neg_sup], neg_apply']
  refine ⟨?_, ?_⟩
  · rintro w ⟨y, z, hdisj, hyz, rfl⟩
    have hw :
        - (f y + g z) ∈
          {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
            ∧ w = (-f) y + (-g) z} := by
      refine ⟨y, z, hdisj, hyz, ?_⟩
      rw [neg_apply', neg_apply']
      abel
    have hle := hneg.1 hw
    rw [hval] at hle
    exact neg_le_neg_iff.mp hle
  · intro u hu
    have hulb :
        -u ∈ lowerBounds
          {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
            ∧ w = (-f) y + (-g) z} := by
      rintro _ ⟨y, z, hdisj, hyz, rfl⟩
      have hle : f y + g z ≤ u := hu ⟨y, z, hdisj, hyz, rfl⟩
      simpa [neg_apply', neg_add, add_comm, add_left_comm, add_assoc]
        using (neg_le_neg hle)
    have hle := hneg.2 hulb
    rw [hval] at hle
    exact neg_le_neg_iff.mp hle

/-- **Disjoint Riesz-Kantorovich formula for the infimum.** If `X` has the
Principal Projection Property, then for `x ≥ 0` the value `(f ⊓ g) x` is the
infimum of `f y + g z` over all disjoint decompositions `x = y + z`. -/
theorem isGLB_inf_apply_disjoint [HasPrincipalProjectionProperty X]
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsGLB
      {w | ∃ y z, IsVLDisjoint y z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊓ g) x) := by
  exact isGLB_inf_apply_disjoint_aux hx

/-- The modulus at a positive element. -/
theorem isLUB_abs_apply
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y, |y| ≤ x ∧ w = |f y|}
      (|f| x) := by
  have habs_val : |f| x = f⁺ x + f⁻ x := by
    have h : (|f| : OrderBoundedHom X Y) = f⁺ + f⁻ :=
      (posPart_add_negPart f).symm
    rw [h]; exact add_apply' f⁺ f⁻ x
  constructor
  · -- Upper bound: |f y| ≤ |f| x for |y| ≤ x
    intro w ⟨y, hyx, hw⟩
    rw [hw, habs_val]
    have hPP := isLUB_posPart_apply (f := f) hx
    have hNP := isLUB_negPart_apply (f := f) hx
    have hpos_le : y⁺ ≤ x :=
      (sup_le (le_abs_self y) (abs_nonneg y)).trans hyx
    have hneg_le : y⁻ ≤ x :=
      (sup_le (neg_le_abs y) (abs_nonneg y)).trans hyx
    have hfy : f y = f y⁺ - f y⁻ := by
      rw [← map_sub_val]; congr 1; exact (posPart_sub_negPart y).symm
    have hfyle : f y ≤ f⁺ x + f⁻ x := by
      rw [hfy, sub_eq_add_neg]
      exact add_le_add
        (hPP.1 ⟨y⁺, posPart_nonneg y, hpos_le, rfl⟩)
        (hNP.1 ⟨y⁻, negPart_nonneg y, hneg_le, rfl⟩)
    have hnfyle : -(f y) ≤ f⁺ x + f⁻ x := by
      rw [hfy, neg_sub, sub_eq_add_neg]
      exact add_le_add
        (hPP.1 ⟨y⁻, negPart_nonneg y, hneg_le, rfl⟩)
        (hNP.1 ⟨y⁺, posPart_nonneg y, hpos_le, rfl⟩)
    exact sup_le hfyle hnfyle
  · -- LUB: any upper bound u of B satisfies |f| x ≤ u
    intro u hu
    change (f ⊔ (-f : OrderBoundedHom X Y)) x ≤ u
    have hLUB : IsLUB _ ((f ⊔ (-f : OrderBoundedHom X Y)) x) :=
      isLUB_sup_apply hx
    exact hLUB.2 fun w ⟨a, b, ha, hb, hab, hw⟩ => by
      have habsle : |a - b| ≤ x :=
        sup_le
          ((sub_le_self a hb).trans (hab ▸ le_add_of_nonneg_right hb))
          ((neg_sub a b ▸ (sub_le_self b ha).trans
            (hab ▸ le_add_of_nonneg_left ha)))
      have hweq : w = f (a - b) := by
        rw [hw, neg_apply', map_sub_val]; abel
      rw [hweq]
      exact (le_abs_self _).trans (hu ⟨a - b, habsle, rfl⟩)

/-! ### Dual Riesz-Kantorovich formulas

The **dual** Riesz-Kantorovich formulas are companions to those above: instead
of computing the lattice operations of varying operators at a fixed positive
element of `X`, they fix a positive operator `f : X → Y` and describe `f`
applied to a lattice expression in `X` (`x⁺`, `x ⊔ y`, `|x|`, ...) as a
supremum or infimum taken over the order interval `[0, f]` of operators
dominated by `f`.
-/

/-! #### Witness operator construction

For a positive operator `f` and a positive element `x₀`, we build an operator
`wit f x₀` with `0 ≤ wit f x₀ ≤ f`, equal to `f` at `x₀`, and vanishing on
elements disjoint from `x₀`. Concretely we set
`wit f x₀ y = sup_n f (y ⊓ n • x₀)` on the positive cone and extend linearly. -/


lemma f_mono_of_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) : Monotone f.toLinearMap :=
  Positive.monotone_iff.mpr fun y hy => by
    have := le_iff.mp hf y hy
    simpa only [zero_apply, toLinearMap_apply] using this


lemma f_apply_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {y : X} (hy : 0 ≤ y) : 0 ≤ f y := by
  have := le_iff.mp hf y hy
  simpa only [zero_apply] using this

/-- The value of the witness operator on the positive cone:
`witFun f x₀ y = sup_n f (y ⊓ n • x₀)`. Defaults to `0` outside the regime where
the supremum exists. -/
noncomputable def witFun (f : OrderBoundedHom X Y) (x₀ y : X) : Y :=
  sSup (Set.range fun n : ℕ => f (y ⊓ n • x₀))

lemma witFun_isLUB {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (_hx₀ : 0 ≤ x₀) (_hy : 0 ≤ y) :
    IsLUB (Set.range fun n : ℕ => f (y ⊓ n • x₀)) (witFun f x₀ y) := by
  refine isLUB_csSup ⟨_, 0, rfl⟩ ⟨f y, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact f_mono_of_nonneg hf inf_le_left

lemma witFun_le_f {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : witFun f x₀ y ≤ f y := by
  apply (witFun_isLUB hf hx₀ hy).2
  rintro _ ⟨n, rfl⟩
  exact f_mono_of_nonneg hf inf_le_left

lemma witFun_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : 0 ≤ witFun f x₀ y := by
  refine (witFun_isLUB hf hx₀ hy).1 ⟨0, ?_⟩
  change f (y ⊓ (0 : ℕ) • x₀) = 0
  rw [zero_nsmul, inf_of_le_right hy]
  exact map_zero f.toLinearMap

lemma witFun_eq_at {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witFun f x₀ x₀ = f x₀ := by
  refine le_antisymm (witFun_le_f hf hx₀ hx₀) ?_
  refine (witFun_isLUB hf hx₀ hx₀).1 ⟨1, ?_⟩
  change f (x₀ ⊓ (1 : ℕ) • x₀) = f x₀
  rw [one_nsmul, inf_idem]

lemma witFun_zero_of_disjoint {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) (hd : y ⊓ x₀ = 0) :
    witFun f x₀ y = 0 := by
  have hyn : ∀ n : ℕ, y ⊓ n • x₀ = 0 := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, inf_of_le_right hy]
    | succ n ih =>
      have hle : y ⊓ (n + 1) • x₀ ≤ y ⊓ (n • x₀) + y ⊓ x₀ := by
        rw [succ_nsmul]
        exact inf_le_inf_add_inf_of_nonneg y (n • x₀) x₀ hy
          (nsmul_nonneg hx₀ n) hx₀
      rw [ih, hd, add_zero] at hle
      exact le_antisymm hle (le_inf hy (nsmul_nonneg hx₀ (n + 1)))
  refine le_antisymm ?_ (witFun_nonneg hf hx₀ hy)
  apply (witFun_isLUB hf hx₀ hy).2
  rintro _ ⟨n, rfl⟩
  change f (y ⊓ n • x₀) ≤ 0
  rw [hyn n]
  exact (map_zero f.toLinearMap).le

lemma witFun_add {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y₁ y₂ : X}
    (hx₀ : 0 ≤ x₀) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    witFun f x₀ (y₁ + y₂) = witFun f x₀ y₁ + witFun f x₀ y₂ := by
  refine le_antisymm ?_ ?_
  · apply (witFun_isLUB hf hx₀ (add_nonneg hy₁ hy₂)).2
    rintro _ ⟨n, rfl⟩
    have hznn : 0 ≤ (y₁ + y₂) ⊓ n • x₀ :=
      le_inf (add_nonneg hy₁ hy₂) (nsmul_nonneg hx₀ n)
    have hzy : (y₁ + y₂) ⊓ n • x₀ ≤ y₁ + y₂ := inf_le_left
    obtain ⟨z₁, z₂, hz₁nn, hz₁y₁, hz₂nn, hz₂y₂, hzeq⟩ :=
      riesz_decomposition (x := (y₁ + y₂) ⊓ n • x₀) y₁ y₂ hznn hy₁ hy₂ hzy
    have hz_le : (y₁ + y₂) ⊓ n • x₀ ≤ n • x₀ := inf_le_right
    have hz₁_nx : z₁ ≤ n • x₀ :=
      ((le_add_of_nonneg_right hz₂nn).trans hzeq.symm.le).trans hz_le
    have hz₂_nx : z₂ ≤ n • x₀ :=
      ((le_add_of_nonneg_left hz₁nn).trans hzeq.symm.le).trans hz_le
    have hz₁_inf : z₁ ≤ y₁ ⊓ n • x₀ := le_inf hz₁y₁ hz₁_nx
    have hz₂_inf : z₂ ≤ y₂ ⊓ n • x₀ := le_inf hz₂y₂ hz₂_nx
    calc f ((y₁ + y₂) ⊓ n • x₀)
        = f (z₁ + z₂) := by rw [hzeq]
      _ = f z₁ + f z₂ := map_add f.toLinearMap z₁ z₂
      _ ≤ f (y₁ ⊓ n • x₀) + f (y₂ ⊓ n • x₀) :=
          add_le_add (f_mono_of_nonneg hf hz₁_inf) (f_mono_of_nonneg hf hz₂_inf)
      _ ≤ witFun f x₀ y₁ + witFun f x₀ y₂ :=
          add_le_add ((witFun_isLUB hf hx₀ hy₁).1 ⟨n, rfl⟩)
            ((witFun_isLUB hf hx₀ hy₂).1 ⟨n, rfl⟩)
  · have step1 : ∀ n m : ℕ,
        f (y₁ ⊓ n • x₀) + f (y₂ ⊓ m • x₀) ≤ witFun f x₀ (y₁ + y₂) := by
      intro n m
      have hsum : (y₁ ⊓ n • x₀) + (y₂ ⊓ m • x₀) ≤ (y₁ + y₂) ⊓ ((n + m) • x₀) := by
        refine le_inf (add_le_add inf_le_left inf_le_left) ?_
        rw [add_nsmul]; exact add_le_add inf_le_right inf_le_right
      calc f (y₁ ⊓ n • x₀) + f (y₂ ⊓ m • x₀)
          = f ((y₁ ⊓ n • x₀) + (y₂ ⊓ m • x₀)) :=
            (map_add f.toLinearMap _ _).symm
        _ ≤ f ((y₁ + y₂) ⊓ (n + m) • x₀) := f_mono_of_nonneg hf hsum
        _ ≤ witFun f x₀ (y₁ + y₂) :=
            (witFun_isLUB hf hx₀ (add_nonneg hy₁ hy₂)).1 ⟨n + m, rfl⟩
    have step2 : ∀ m : ℕ,
        witFun f x₀ y₁ + f (y₂ ⊓ m • x₀) ≤ witFun f x₀ (y₁ + y₂) := by
      intro m
      have hub : witFun f x₀ (y₁ + y₂) - f (y₂ ⊓ m • x₀) ∈
          upperBounds (Set.range fun n : ℕ => f (y₁ ⊓ n • x₀)) := by
        rintro _ ⟨n, rfl⟩
        exact le_sub_iff_add_le.mpr (step1 n m)
      exact le_sub_iff_add_le.mp ((witFun_isLUB hf hx₀ hy₁).2 hub)
    have hub : witFun f x₀ (y₁ + y₂) - witFun f x₀ y₁ ∈
        upperBounds (Set.range fun n : ℕ => f (y₂ ⊓ n • x₀)) := by
      rintro _ ⟨m, rfl⟩
      rw [le_sub_iff_add_le, add_comm]; exact step2 m
    have h := (witFun_isLUB hf hx₀ hy₂).2 hub
    have h2 := le_sub_iff_add_le.mp h
    rwa [add_comm] at h2

/-- The witness linear map for `f` and `x₀ ≥ 0`. -/
noncomputable def witLin {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    X →ₗ[ℝ] Y := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension
    (fun y hy => witFun_nonneg hf hx₀ hy)
    (fun y₁ y₂ hy₁ hy₂ => witFun_add hf hx₀ hy₁ hy₂)

lemma witLin_apply_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : witLin hf hx₀ y = witFun f x₀ y := by
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension_nonneg _ _ hy

lemma witLin_positive {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    Positive (witLin hf hx₀) := by
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  exact Positive.extension_positive _ _

/-- The witness operator as an `OrderBoundedHom`. -/
noncomputable def witOp {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    OrderBoundedHom X Y :=
  ⟨witLin hf hx₀, Positive.isOrderBounded (witLin_positive hf hx₀)⟩

lemma witOp_apply {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) (y : X) :
    witOp hf hx₀ y = witLin hf hx₀ y := rfl

lemma witOp_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    (0 : OrderBoundedHom X Y) ≤ witOp hf hx₀ :=
  le_iff.mpr fun y hy => by
    have h := witLin_positive hf hx₀ y hy
    change (0 : Y) ≤ witLin hf hx₀ y at h
    simpa only [zero_apply, witOp_apply] using h

lemma witOp_le_f {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witOp hf hx₀ ≤ f :=
  le_iff.mpr fun y hy => by
    change witLin hf hx₀ y ≤ f y
    rw [witLin_apply_nonneg hf hx₀ hy]
    exact witFun_le_f hf hx₀ hy

lemma witOp_apply_self {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witOp hf hx₀ x₀ = f x₀ := by
  change witLin hf hx₀ x₀ = f x₀
  rw [witLin_apply_nonneg hf hx₀ hx₀, witFun_eq_at hf hx₀]

lemma witOp_apply_disjoint {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X} (hx₀ : 0 ≤ x₀)
    (hy : 0 ≤ y) (hd : y ⊓ x₀ = 0) : witOp hf hx₀ y = 0 := by
  change witLin hf hx₀ y = 0
  rw [witLin_apply_nonneg hf hx₀ hy, witFun_zero_of_disjoint hf hx₀ hy hd]

/-- The witness operator at `x = x⁺ - x⁻` recovers `f x⁺`. -/
lemma witOp_apply_eq_posPart {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    witOp hf (posPart_nonneg x) x = f x⁺ := by
  have hlin : (witOp hf (posPart_nonneg x)).toLinearMap x =
      (witOp hf (posPart_nonneg x)).toLinearMap x⁺ -
      (witOp hf (posPart_nonneg x)).toLinearMap x⁻ := by
    rw [← map_sub, posPart_sub_negPart]
  change (witOp hf (posPart_nonneg x)).toLinearMap x = f x⁺
  rw [hlin]
  have h1 : (witOp hf (posPart_nonneg x)).toLinearMap x⁺ = f x⁺ :=
    witOp_apply_self hf (posPart_nonneg x)
  have h2 : (witOp hf (posPart_nonneg x)).toLinearMap x⁻ = 0 := by
    apply witOp_apply_disjoint hf (posPart_nonneg x) (negPart_nonneg x)
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero x
  rw [h1, h2, sub_zero]

/-! #### Dual Riesz–Kantorovich theorems -/

/-- **Dual Riesz-Kantorovich for the positive part.** For a positive order
bounded operator `f : X → Y` and an arbitrary `x : X`, the value `f x⁺` is the
supremum of `g x` taken over all order bounded operators `g` with `0 ≤ g ≤ f`.
-/
theorem isLUB_apply_posPart {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x}
      (f x⁺) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have hg_neg : 0 ≤ g x⁻ := f_apply_nonneg hg0 (negPart_nonneg x)
    have key : g x = g x⁺ - g x⁻ := by
      change g.toLinearMap x = g.toLinearMap x⁺ - g.toLinearMap x⁻
      rw [← map_sub, posPart_sub_negPart]
    rw [key]
    exact (sub_le_self _ hg_neg).trans (le_iff.mp hgf x⁺ (posPart_nonneg x))
  · intro u hu
    have hwit_in :
        witOp hf (posPart_nonneg x) x ∈
          {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x} :=
      ⟨witOp hf (posPart_nonneg x), witOp_nonneg hf (posPart_nonneg x),
        witOp_le_f hf (posPart_nonneg x), rfl⟩
    have hub := hu hwit_in
    rwa [witOp_apply_eq_posPart hf x] at hub

/-- **Dual Riesz-Kantorovich for the negative part.** For a positive order
bounded operator `f` and `x : X`, `f x⁻ = sup {-(g x) | 0 ≤ g ≤ f}`. -/
theorem isLUB_apply_negPart {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = -(g x)}
      (f x⁻) := by
  have hpp := isLUB_apply_posPart hf (-x)
  rw [posPart_neg] at hpp
  have hgneg : ∀ g : OrderBoundedHom X Y, g (-x) = -(g x) := fun g => by
    change g.toLinearMap (-x) = -(g.toLinearMap x); rw [map_neg]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have hmem : g (-x) ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g (-x)} :=
      ⟨g, hg0, hgf, rfl⟩
    have h1 := hpp.1 hmem
    rw [hgneg] at h1; exact h1
  · intro u hu
    apply hpp.2
    rintro _ ⟨g, hg0, hgf, rfl⟩
    have hin : -(g x) ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = -(g x)} :=
      ⟨g, hg0, hgf, rfl⟩
    have h1 := hu hin
    rw [hgneg]; exact h1

/-- **Dual Riesz-Kantorovich for the supremum.** For a positive order bounded
operator `f` and `x y : X`,
`f (x ⊔ y) = sup {g x + (f - g) y | 0 ≤ g ≤ f}`. -/
theorem isLUB_apply_sup {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x y : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y,
        0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y}
      (f (x ⊔ y)) := by
  -- Use x ⊔ y = y + (x - y)⁺
  have hxy : (x ⊔ y) = y + (x - y)⁺ := by
    rw [posPart_def, add_sup, add_sub_cancel, add_zero, sup_comm]
  have hfxy : f (x ⊔ y) = f y + f ((x - y)⁺) := by
    rw [hxy]; exact map_add_val f y _
  rw [hfxy]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have hgxy : g x + (f - g) y = f y + g (x - y) := by
      rw [sub_apply, map_sub_val g]; abel
    rw [hgxy]
    have hgneg : 0 ≤ g (x - y)⁻ := f_apply_nonneg hg0 (negPart_nonneg _)
    have hgsplit : g (x - y) = g (x - y)⁺ - g (x - y)⁻ := by
      change g.toLinearMap (x - y) = g.toLinearMap (x - y)⁺ - g.toLinearMap (x - y)⁻
      rw [← map_sub, posPart_sub_negPart]
    have h1 : g (x - y) ≤ g (x - y)⁺ := by rw [hgsplit]; exact sub_le_self _ hgneg
    have h2 : g (x - y)⁺ ≤ f (x - y)⁺ := le_iff.mp hgf _ (posPart_nonneg _)
    exact add_le_add (le_refl (f y)) (h1.trans h2)
  · intro u hu
    set g := witOp hf (posPart_nonneg (x - y)) with hgdef
    have hg0 : (0 : OrderBoundedHom X Y) ≤ g := witOp_nonneg hf _
    have hgf : g ≤ f := witOp_le_f hf _
    have hgxy : g (x - y) = f (x - y)⁺ := witOp_apply_eq_posPart hf (x - y)
    have hin : g x + (f - g) y ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y} :=
      ⟨g, hg0, hgf, rfl⟩
    have hub := hu hin
    have hcalc : g x + (f - g) y = f y + f (x - y)⁺ := by
      have h0 : g x + (f - g) y = f y + g (x - y) := by
        rw [sub_apply, map_sub_val g]; abel
      rw [h0, hgxy]
    rw [hcalc] at hub; exact hub

/-- **Dual Riesz-Kantorovich for the infimum.** For a positive order bounded
operator `f` and `x y : X`,
`f (x ⊓ y) = inf {g x + (f - g) y | 0 ≤ g ≤ f}`. -/
theorem isGLB_apply_inf {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x y : X) :
    IsGLB {w | ∃ g : OrderBoundedHom X Y,
        0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y}
      (f (x ⊓ y)) := by
  simpa only [Set.neg_ofPred, map_neg_value, ← neg_inf, ← neg_add, neg_neg, neg_inj] using
    (isLUB_apply_sup hf (-x) (-y)).neg

lemma sum_apply_finset {ι : Type*} (s : Finset ι)
    (g : ι → OrderBoundedHom X Y) (x : X) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  induction s using Finset.cons_induction with
  | empty =>
      change (0 : X →ₗ[ℝ] Y) x = 0
      simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, add_apply', ih]

/-- **Dual Riesz-Kantorovich for finite suprema.** For a positive order bounded
operator `f` and a non-empty finite family `x`, `f` applied to the supremum of
the family is the supremum of the sums `∑ i ∈ s, g i (x i)`, where the positive
operators `g i` form a finite decomposition of `f`. -/
theorem isLUB_apply_finset_sup {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : OrderBoundedHom X Y} (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : ι → X) :
    IsLUB {w | ∃ g : ι → OrderBoundedHom X Y,
        (∀ i ∈ s, (0 : OrderBoundedHom X Y) ≤ g i) ∧
          (∑ i ∈ s, g i = f) ∧
          w = ∑ i ∈ s, g i (x i)}
      (f (s.sup' hs x)) := by
  classical
  revert f x
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro f hf x
      refine ⟨?_, ?_⟩
      · rintro _ ⟨g, _hg0, hgsum, rfl⟩
        exact le_of_eq (by
          simpa using congrArg (fun h : OrderBoundedHom X Y => h (x a)) hgsum)
      · intro u hu
        exact hu ⟨fun _ => f, by simpa using hf, by simp, by simp⟩
  | cons a t ha ht ih =>
      intro f hf x
      refine ⟨?_, ?_⟩
      · rintro _ ⟨g, hg0, hgsum, rfl⟩
        let x₀ := (Finset.cons a t ha).sup' (Finset.cons_nonempty ha) x
        calc
          (∑ i ∈ Finset.cons a t ha, g i (x i)) ≤
              ∑ i ∈ Finset.cons a t ha, g i x₀ := by
            refine Finset.sum_le_sum fun i hi => ?_
            exact f_mono_of_nonneg (hg0 i hi) (Finset.le_sup' (f := x) hi)
          _ = f x₀ := by rw [← sum_apply_finset, hgsum]
      · intro u hu
        rw [Finset.sup'_cons ht x]
        have hsup := isLUB_apply_sup hf (x a) (t.sup' ht x)
        apply hsup.2
        rintro _ ⟨g, hg0, hgf, rfl⟩
        have hrest := ih (f := f - g) (sub_nonneg.mpr hgf) x
        have hle : (f - g) (t.sup' ht x) ≤ u - g (x a) := by
          apply hrest.2
          rintro _ ⟨k, hk0, hksum, rfl⟩
          rw [le_sub_iff_add_le]
          let G : ι → OrderBoundedHom X Y := fun i => if i = a then g else k i
          have hG0 : ∀ i ∈ Finset.cons a t ha, (0 : OrderBoundedHom X Y) ≤ G i := by
            intro i hi
            rcases Finset.mem_cons.mp hi with rfl | hit
            · simp [G, hg0]
            · have hia : i ≠ a := fun h => ha (h ▸ hit)
              simp [G, hia, hk0 i hit]
          have hGsum : ∑ i ∈ Finset.cons a t ha, G i = f := by
            rw [Finset.sum_cons]
            have hsum_t : ∑ i ∈ t, G i = f - g := by
              rw [← hksum]
              refine Finset.sum_congr rfl fun i hit => ?_
              have hia : i ≠ a := fun h => ha (h ▸ hit)
              simp [G, hia]
            rw [hsum_t]
            rw [show G a = g by simp [G]]
            abel
          have hfull : (∑ i ∈ Finset.cons a t ha, G i (x i)) ≤ u :=
            hu ⟨G, hG0, hGsum, rfl⟩
          rw [Finset.sum_cons] at hfull
          have hsum_t : ∑ i ∈ t, G i (x i) = ∑ i ∈ t, k i (x i) := by
            refine Finset.sum_congr rfl fun i hit => ?_
            have hia : i ≠ a := fun h => ha (h ▸ hit)
            simp [G, hia]
          rw [hsum_t] at hfull
          simpa [G, add_comm] using hfull
        have := le_sub_iff_add_le.mp hle
        rwa [add_comm] at this

/-- **Dual Riesz-Kantorovich for finite infima.** For a positive order bounded
operator `f` and a non-empty finite family `x`, `f` applied to the infimum of
the family is the infimum of the sums `∑ i ∈ s, g i (x i)`, where the positive
operators `g i` form a finite decomposition of `f`. -/
theorem isGLB_apply_finset_inf {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : OrderBoundedHom X Y} (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : ι → X) :
    IsGLB {w | ∃ g : ι → OrderBoundedHom X Y,
        (∀ i ∈ s, (0 : OrderBoundedHom X Y) ≤ g i) ∧
          (∑ i ∈ s, g i = f) ∧
          w = ∑ i ∈ s, g i (x i)}
      (f (s.inf' hs x)) := by
  have hsup : s.sup' hs (fun i => -x i) = -(s.inf' hs x) :=
    (map_finset_inf' (OrderIso.neg X) hs x).symm
  simpa only [Set.neg_ofPred, map_neg_value, hsup, Finset.sum_neg_distrib, neg_neg, neg_inj] using
    (isLUB_apply_finset_sup hs hf (fun i => -x i)).neg

/-- **Dual Riesz-Kantorovich for the modulus.** For a positive order bounded
operator `f` and `x : X`,
`f |x| = sup {g x - (f - g) x | 0 ≤ g ≤ f}`. -/
theorem isLUB_apply_abs {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y,
        0 ≤ g ∧ g ≤ f ∧ w = g x - (f - g) x}
      (f |x|) := by
  -- |x| = x⁺ + x⁻ and g x - (f - g) x = 2 g x - f x. Reduce to posPart formula.
  have habs : |x| = x⁺ + x⁻ := (posPart_add_negPart x).symm
  -- Note: x = x⁺ - x⁻, so f x = f x⁺ - f x⁻, and 2 f x⁺ - f x = f x⁺ + f x⁻ = f |x|.
  have hfabs : f |x| = 2 • f x⁺ - f x := by
    rw [habs, map_add_val]
    have : f x = f x⁺ - f x⁻ := by rw [← map_sub_val, posPart_sub_negPart]
    rw [this]; abel
  rw [hfabs]
  have hpp := isLUB_apply_posPart hf x
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have heq : g x - (f - g) x = 2 • g x - f x := by
      rw [sub_apply, two_smul]; abel
    rw [heq]
    have hgx : g x ≤ f x⁺ := hpp.1 ⟨g, hg0, hgf, rfl⟩
    have h2 : 2 • g x ≤ 2 • f x⁺ := by
      rw [two_smul, two_smul]; exact add_le_add hgx hgx
    exact sub_le_sub_right h2 _
  · intro u hu
    set g := witOp hf (posPart_nonneg x) with hgdef
    have hg0 : (0 : OrderBoundedHom X Y) ≤ g := witOp_nonneg hf _
    have hgf : g ≤ f := witOp_le_f hf _
    have hgx : g x = f x⁺ := witOp_apply_eq_posPart hf x
    have hin : g x - (f - g) x ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x - (f - g) x} :=
      ⟨g, hg0, hgf, rfl⟩
    have hub := hu hin
    have heq : g x - (f - g) x = 2 • f x⁺ - f x := by
      rw [sub_apply, hgx, two_smul]; abel
    rw [heq] at hub; exact hub

/-- The supremum of a non-empty upward-directed bounded above set of order
bounded operators exists and is computed pointwise on the positive cone:
its value at any positive `x` is the supremum of `{g x | g ∈ S}`. -/
theorem isLUB_of_directedOn
    {S : Set (OrderBoundedHom X Y)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (hbdd : BddAbove S) :
    ∃ f : OrderBoundedHom X Y, IsLUB S f ∧
      ∀ {x : X}, 0 ≤ x →
        IsLUB ((fun g : OrderBoundedHom X Y => g x) '' S) (f x) := by
  classical
  have : IsVLArchimedean Y := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨h, hh⟩ := hbdd
  have aux : ∀ {x : X}, 0 ≤ x →
      ∃ s : Y, IsLUB ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) s := by
    intro x hx
    refine ⟨_, isLUB_csSup ⟨0, g₀, hg₀, sub_self _⟩ ⟨h x - g₀ x, ?_⟩⟩
    rintro _ ⟨g, hg, rfl⟩
    exact sub_le_sub_right (le_iff.mp (hh hg) x hx) _
  let σ : X → Y := fun x => if hx : 0 ≤ x then (aux hx).choose else 0
  have σ_isLUB : ∀ {x : X} (hx : 0 ≤ x),
      IsLUB ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) (σ x) := by
    intro x hx
    change IsLUB _ (if hx : 0 ≤ x then (aux hx).choose else 0)
    rw [dite_eq_left hx]
    exact (aux hx).choose_spec
  have σ_nn : ∀ x, 0 ≤ x → 0 ≤ σ x := fun x hx => by
    have h1 := (σ_isLUB hx).1 ⟨g₀, hg₀, sub_self _⟩
    simpa using h1
  have σ_add : ∀ x y, 0 ≤ x → 0 ≤ y → σ (x + y) = σ x + σ y := by
    intro x y hx hy
    refine le_antisymm ?_ ?_
    · apply (σ_isLUB (add_nonneg hx hy)).2
      rintro _ ⟨g, hg, rfl⟩
      change g (x + y) - g₀ (x + y) ≤ σ x + σ y
      have hgxy : g (x + y) - g₀ (x + y) = (g x - g₀ x) + (g y - g₀ y) := by
        rw [map_add_val g, map_add_val g₀]; abel
      rw [hgxy]
      exact add_le_add ((σ_isLUB hx).1 ⟨g, hg, rfl⟩)
        ((σ_isLUB hy).1 ⟨g, hg, rfl⟩)
    · have step1 : ∀ w₁ ∈ ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S),
          ∀ w₂ ∈ ((fun g : OrderBoundedHom X Y => g y - g₀ y) '' S),
          w₁ + w₂ ≤ σ (x + y) := by
        rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
        obtain ⟨g, hg, hg₁g, hg₂g⟩ := hdir g₁ hg₁ g₂ hg₂
        have h1 : g₁ x - g₀ x ≤ g x - g₀ x :=
          sub_le_sub_right (le_iff.mp hg₁g x hx) _
        have h2 : g₂ y - g₀ y ≤ g y - g₀ y :=
          sub_le_sub_right (le_iff.mp hg₂g y hy) _
        have h3 : (g x - g₀ x) + (g y - g₀ y) = g (x + y) - g₀ (x + y) := by
          rw [map_add_val g, map_add_val g₀]; abel
        calc g₁ x - g₀ x + (g₂ y - g₀ y)
            ≤ (g x - g₀ x) + (g y - g₀ y) := add_le_add h1 h2
          _ = g (x + y) - g₀ (x + y) := h3
          _ ≤ σ (x + y) :=
            (σ_isLUB (add_nonneg hx hy)).1 ⟨g, hg, rfl⟩
      have step2 : ∀ w₂ ∈ ((fun g : OrderBoundedHom X Y => g y - g₀ y) '' S),
          σ x + w₂ ≤ σ (x + y) := by
        intro w₂ hw₂
        have hub : σ (x + y) - w₂ ∈ upperBounds
            ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) :=
          fun w₁ hw₁ => le_sub_iff_add_le.mpr (step1 w₁ hw₁ w₂ hw₂)
        exact le_sub_iff_add_le.mp ((σ_isLUB hx).2 hub)
      have hub2 : σ (x + y) - σ x ∈ upperBounds
          ((fun g : OrderBoundedHom X Y => g y - g₀ y) '' S) := by
        intro w₂ hw₂
        rw [le_sub_iff_add_le, add_comm]
        exact step2 w₂ hw₂
      have h3 := (σ_isLUB hy).2 hub2
      have := le_sub_iff_add_le.mp h3
      rwa [add_comm] at this
  let T : X →ₗ[ℝ] Y := Positive.extension σ_nn σ_add
  have hT_pos : Positive T := Positive.extension_positive σ_nn σ_add
  have hT_apply : ∀ {x : X}, 0 ≤ x → T x = σ x :=
    fun {x} hx => Positive.extension_nonneg σ_nn σ_add hx
  let Tob : OrderBoundedHom X Y := ⟨T, hT_pos.isOrderBounded⟩
  refine ⟨Tob + g₀, ?_, ?_⟩
  · refine ⟨fun g hg => le_iff.mpr fun x hx => ?_,
      fun k hk => le_iff.mpr fun x hx => ?_⟩
    · rw [add_apply']
      change g x ≤ T x + g₀ x
      rw [hT_apply hx]
      have : g x - g₀ x ≤ σ x := (σ_isLUB hx).1 ⟨g, hg, rfl⟩
      exact sub_le_iff_le_add.mp this
    · rw [add_apply']
      change T x + g₀ x ≤ k x
      rw [hT_apply hx]
      have hub : k x - g₀ x ∈ upperBounds
          ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) := by
        rintro _ ⟨g, hg, rfl⟩
        exact sub_le_sub_right (le_iff.mp (hk hg) x hx) _
      have h1 := (σ_isLUB hx).2 hub
      exact le_sub_iff_add_le.mp h1
  · intro x hx
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      rw [add_apply']
      change g x ≤ T x + g₀ x
      rw [hT_apply hx]
      have : g x - g₀ x ≤ σ x := (σ_isLUB hx).1 ⟨g, hg, rfl⟩
      exact sub_le_iff_le_add.mp this
    · intro u hu
      rw [add_apply']
      change T x + g₀ x ≤ u
      rw [hT_apply hx]
      have hub : u - g₀ x ∈ upperBounds
          ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) := by
        rintro _ ⟨g, hg, rfl⟩
        exact sub_le_sub_right (hu ⟨g, hg, rfl⟩) _
      have h1 := (σ_isLUB hx).2 hub
      exact le_sub_iff_add_le.mp h1

/-- When the codomain is order complete, every non-empty bounded above set
of order bounded operators admits a least upper bound. -/
theorem exists_isLUB
    {S : Set (OrderBoundedHom X Y)} (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ f : OrderBoundedHom X Y, IsLUB S f := by
  classical
  let S' : Set (OrderBoundedHom X Y) :=
    {f | ∃ F : Finset (OrderBoundedHom X Y), ∃ hF : F.Nonempty,
      ↑F ⊆ S ∧ f = F.sup' hF id}
  have hS'_ne : S'.Nonempty := by
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, {g}, Finset.singleton_nonempty g, ?_, ?_⟩
    · simpa using hg
    · simp
  have hS'_bdd : BddAbove S' := by
    obtain ⟨h, hh⟩ := hbdd
    refine ⟨h, ?_⟩
    rintro _ ⟨F, hF, hFS, rfl⟩
    exact Finset.sup'_le hF id (fun g hgF => hh (hFS hgF))
  have hS'_dir : DirectedOn (· ≤ ·) S' := by
    rintro _ ⟨F₁, hF₁, hF₁S, rfl⟩ _ ⟨F₂, hF₂, hF₂S, rfl⟩
    have hU : (F₁ ∪ F₂).Nonempty := hF₁.mono Finset.subset_union_left
    refine ⟨(F₁ ∪ F₂).sup' hU id, ⟨F₁ ∪ F₂, hU, ?_, rfl⟩, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_union.mp hg with h | h
      · exact hF₁S h
      · exact hF₂S h
    · exact Finset.sup'_le hF₁ id (fun g hg =>
        Finset.le_sup' id (Finset.mem_union_left _ hg))
    · exact Finset.sup'_le hF₂ id (fun g hg =>
        Finset.le_sup' id (Finset.mem_union_right _ hg))
  obtain ⟨f, hLUB, _⟩ := isLUB_of_directedOn hS'_ne hS'_dir hS'_bdd
  refine ⟨f, ?_, ?_⟩
  · intro g hg
    exact hLUB.1 ⟨{g}, Finset.singleton_nonempty g,
      by simpa using hg, by simp⟩
  · intro k hk
    apply hLUB.2
    rintro _ ⟨F, hF, hFS, rfl⟩
    exact Finset.sup'_le hF id (fun g hgF => hk (hFS hgF))

/-- The Riesz-Kantorovich conditional completeness structure on order bounded
operators. This packages `OrderBoundedHom.exists_isLUB`; files can opt into it
locally as a typeclass instance. -/
@[reducible]
noncomputable def conditionallyCompleteLattice :
    ConditionallyCompleteLattice (OrderBoundedHom X Y) := by
  classical
  letI : SupSet (OrderBoundedHom X Y) :=
    ⟨fun S => if h : S.Nonempty ∧ BddAbove S then (exists_isLUB h.1 h.2).choose else 0⟩
  have hsSup : ∀ (S : Set (OrderBoundedHom X Y)), BddAbove S → S.Nonempty →
      IsLUB S (sSup S) := by
    intro S hbdd hne
    change IsLUB S
      (if h : S.Nonempty ∧ BddAbove S then (exists_isLUB h.1 h.2).choose else 0)
    rw [dite_eq_left ⟨hne, hbdd⟩]
    exact (exists_isLUB hne hbdd).choose_spec
  exact conditionallyCompleteLatticeOfLatticeOfsSup _ hsSup

end OrderBoundedHom

/-- When the codomain is order complete, every order bounded operator
is regular. -/
theorem IsOrderBounded.isRegularOp
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Lattice X] [ConditionallyCompleteLattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [VectorLattice X] [VectorLattice Y]
    {f : X →ₗ[ℝ] Y} (hf : IsOrderBounded f) :
    IsRegularOp f := by
  let F : OrderBoundedHom X Y := ⟨f, hf⟩
  refine ⟨F⁺.toLinearMap, F⁻.toLinearMap, ?_, ?_, ?_⟩
  · intro x hx
    change (0 : Y) ≤ F⁺ x
    have h := OrderBoundedHom.le_iff.mp (posPart_nonneg F) x hx
    change (0 : Y) ≤ F⁺ x at h
    exact h
  · intro x hx
    change (0 : Y) ≤ F⁻ x
    have h := OrderBoundedHom.le_iff.mp (negPart_nonneg F) x hx
    change (0 : Y) ≤ F⁻ x at h
    exact h
  · exact (congrArg OrderBoundedHom.toLinearMap (posPart_sub_negPart F)).symm
