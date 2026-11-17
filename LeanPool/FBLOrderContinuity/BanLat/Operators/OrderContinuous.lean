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
public import LeanPool.OrderClosures.BanLat.Convergences.Order
public import LeanPool.OrderClosures.BanLat.OrderContinuous.Basic
public import LeanPool.FBLOrderContinuity.BanLat.Operators.RieszKantorovich
public import Mathlib.Data.List.TFAE



/-!
# Order continuous operators

This file introduces order continuous linear operators between vector lattices. For order bounded
operators with order complete codomain, it states the characterisation by decreasing zero nets and
by the positive part, negative part, and modulus.
-/

@[expose] public section

universe u v w

variable {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

/-- A linear operator is **order continuous** if it preserves order convergence of nets.

The index set is constrained to live in the same universe as the domain, matching the convention
used for order continuous norms. -/
def IsOrderContinuousOp (T : X →ₗ[ℝ] Y) : Prop :=
  ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {x : ι → X} {a : X},
    OrderConvergesTo x a → OrderConvergesTo (fun i => T (x i)) (T a)

namespace OrderContinuousOp

/-- The set of order-continuous order bounded operators. -/
def OrderContinuousOperator : Set (OrderBoundedHom X Y) :=
  {T | IsOrderContinuousOp T.toLinearMap}

@[simp]
theorem mem_OrderContinuousOperator (T : OrderBoundedHom X Y) :
    T ∈ OrderContinuousOperator (X := X) (Y := Y) ↔ IsOrderContinuousOp T.toLinearMap := by
  rfl

private lemma obAdd_apply (S T : OrderBoundedHom X Y) (x : X) :
    (S + T) x = S x + T x := rfl

private lemma obNeg_apply (T : OrderBoundedHom X Y) (x : X) :
    (-T) x = -T x := rfl

private lemma obSmul_apply (c : ℝ) (T : OrderBoundedHom X Y) (x : X) :
    (c • T) x = c • T x := rfl

private lemma zero_mem_OrderContinuousOperator :
    (0 : OrderBoundedHom X Y) ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  rw [mem_OrderContinuousOperator]
  intro ι _ _ _ x a hx
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    exact le_rfl
  · intro _
    exact le_rfl
  · simp
  · intro _
    filter_upwards with i
    change |(0 : Y) - 0| ≤ 0
    simp

private lemma add_mem_OrderContinuousOperator {S T : OrderBoundedHom X Y}
    (hS : S ∈ OrderContinuousOperator (X := X) (Y := Y))
    (hT : T ∈ OrderContinuousOperator (X := X) (Y := Y)) :
    S + T ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  rw [mem_OrderContinuousOperator] at hS hT ⊢
  intro ι _ _ _ x a hx
  simpa only [OrderBoundedHom.toLinearMap_apply, obAdd_apply] using (hS hx).add (hT hx)

private lemma neg_mem_OrderContinuousOperator {T : OrderBoundedHom X Y}
    (hT : T ∈ OrderContinuousOperator (X := X) (Y := Y)) :
    -T ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  rw [mem_OrderContinuousOperator] at hT ⊢
  intro ι _ _ _ x a hx
  simpa only [OrderBoundedHom.toLinearMap_apply, obNeg_apply] using (hT hx).neg

private lemma smul_mem_OrderContinuousOperator (c : ℝ) {T : OrderBoundedHom X Y}
    (hT : T ∈ OrderContinuousOperator (X := X) (Y := Y)) :
    c • T ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  rw [mem_OrderContinuousOperator] at hT ⊢
  intro ι _ _ _ x a hx
  simpa only [OrderBoundedHom.toLinearMap_apply, obSmul_apply] using (hT hx).smul c

private lemma isGLB_range_abs_of_orderConvergesTo_zero
    {Z : Type w} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {x : ι → Z}
    (hx : OrderConvergesTo x 0) :
    IsGLB (Set.range fun i => |x i|) 0 := by
  rcases hx with ⟨κ, hκpre, hκdir, hκnon, r, _hranti, _hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact abs_nonneg _
  · intro w hw
    apply hrglb.2
    intro y hy
    rcases hy with ⟨k, rfl⟩
    have hevent := hrevent k
    rcases hevent.exists with ⟨i, hi⟩
    calc
      w ≤ |x i| := hw ⟨i, rfl⟩
      _ = |x i - 0| := by rw [sub_zero]
      _ ≤ r k := hi

private lemma orderConvergesTo_abs_sub_zero
    {Z : Type w} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    {ι : Type u} [Preorder ι]
    {x : ι → Z} {a : Z} (hx : OrderConvergesTo x a) :
    OrderConvergesTo (fun i => |x i - a|) 0 := by
  rcases hx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnn, hrglb, ?_⟩
  intro k
  exact (hrevent k).mono fun i hi => by
    simpa [sub_zero, abs_abs] using hi

private lemma orderConvergesTo_of_sub_zero
    {Z : Type w} [AddCommGroup Z] [Lattice Z]
    {ι : Type u} [Preorder ι]
    {x : ι → Z} {a : Z} (hx : OrderConvergesTo (fun i => x i - a) 0) :
    OrderConvergesTo x a := by
  rcases hx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnn, hrglb, ?_⟩
  intro k
  exact (hrevent k).mono fun i hi => by
    simpa [sub_zero] using hi

private lemma orderConvergesTo_zero_of_abs_le
    {Z : Type w} [AddCommGroup Z] [Lattice Z]
    {ι : Type u} [Preorder ι] {x y : ι → Z}
    (hy : OrderConvergesTo y 0) (hle : ∀ i, |x i| ≤ y i) :
    OrderConvergesTo x 0 := by
  rcases hy with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnn, hrglb, ?_⟩
  intro k
  exact (hrevent k).mono fun i hi => by
    calc
      |x i - 0| = |x i| := by rw [sub_zero]
      _ ≤ y i := hle i
      _ ≤ |y i| := le_abs_self _
      _ = |y i - 0| := by rw [sub_zero]
      _ ≤ r k := hi

variable {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

private lemma abs_apply_le_modulus_apply_abs (T : OrderBoundedHom X Y) (x : X) :
    |T x| ≤ (|T| : OrderBoundedHom X Y) |x| := by
  exact (OrderBoundedHom.isLUB_abs_apply (f := T) (x := |x|) (abs_nonneg x)).1
    ⟨x, le_rfl, rfl⟩

private lemma positive_orderContinuous_of_decreasing_abs_glb_zero {S : OrderBoundedHom X Y}
    (hS : (0 : OrderBoundedHom X Y) ≤ S)
    (hcrit : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {x : ι → X},
      Antitone x → (∀ i, 0 ≤ x i) → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun i => |S (x i)|) 0) :
    IsOrderContinuousOp S.toLinearMap := by
  intro ι _ _ _ x a hx
  rcases hx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  have hSpos : Positive S.toLinearMap := fun y hy => by
    simpa only [OrderBoundedHom.zero_apply, OrderBoundedHom.toLinearMap_apply] using
      OrderBoundedHom.le_iff.mp hS y hy
  have hSmono : Monotone S.toLinearMap := Positive.monotone_iff.mpr hSpos
  have hglb_abs : IsGLB (Set.range fun k => |S (r k)|) 0 :=
    hcrit hranti hrnn hrglb
  have hglb : IsGLB (Set.range fun k => S (r k)) 0 := by
    have hrange : Set.range (fun k => |S (r k)|) = Set.range (fun k => S (r k)) := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, (abs_of_nonneg (hSpos (r k) (hrnn k))).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, abs_of_nonneg (hSpos (r k) (hrnn k))⟩
    rwa [hrange] at hglb_abs
  let rangeIdx : Type v := Set.range fun k => S (r k)
  let lambdaIdx : Type v := OrderDual rangeIdx
  let : IsDirected lambdaIdx (· ≤ ·) := ⟨fun a b => by
    rcases (OrderDual.ofDual a : rangeIdx).2 with ⟨ka, hka⟩
    rcases (OrderDual.ofDual b : rangeIdx).2 with ⟨kb, hkb⟩
    obtain ⟨m, hkam, hkbm⟩ := directed_of (· ≤ ·) ka kb
    refine ⟨OrderDual.toDual (⟨S (r m), ⟨m, rfl⟩⟩ : rangeIdx), ?_, ?_⟩
    · change (⟨S (r m), ⟨m, rfl⟩⟩ : rangeIdx) ≤ OrderDual.ofDual a
      change S (r m) ≤ ((OrderDual.ofDual a : rangeIdx) : Y)
      rw [← hka]
      exact hSmono (hranti hkam)
    · change (⟨S (r m), ⟨m, rfl⟩⟩ : rangeIdx) ≤ OrderDual.ofDual b
      change S (r m) ≤ ((OrderDual.ofDual b : rangeIdx) : Y)
      rw [← hkb]
      exact hSmono (hranti hkbm)⟩
  let : Nonempty lambdaIdx := by
    obtain ⟨k⟩ := hκnon
    exact ⟨OrderDual.toDual (⟨S (r k), ⟨k, rfl⟩⟩ : rangeIdx)⟩
  have hglb_lift :
      IsGLB (Set.range fun k : lambdaIdx => ((OrderDual.ofDual k : rangeIdx) : Y)) 0 := by
    have hrange :
        Set.range (fun k : lambdaIdx => ((OrderDual.ofDual k : rangeIdx) : Y)) =
          Set.range fun k => S (r k) := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact (OrderDual.ofDual k : rangeIdx).2
      · rintro ⟨k, rfl⟩
        exact ⟨OrderDual.toDual (⟨S (r k), ⟨k, rfl⟩⟩ : rangeIdx), rfl⟩
    rwa [hrange]
  refine ⟨lambdaIdx, inferInstance, inferInstance, inferInstance,
    fun k => ((OrderDual.ofDual k : rangeIdx) : Y), ?_, ?_, hglb_lift, ?_⟩
  · intro k l hkl
    exact hkl
  · intro k
    rcases (OrderDual.ofDual k : rangeIdx).2 with ⟨m, hm⟩
    change 0 ≤ ((OrderDual.ofDual k : rangeIdx) : Y)
    rw [← hm]
    exact hSpos (r m) (hrnn m)
  · intro k
    rcases (OrderDual.ofDual k : rangeIdx).2 with ⟨m, hmk⟩
    exact (hrevent m).mono fun i hi => by
      calc
        |S.toLinearMap (x i) - S.toLinearMap a| = |S.toLinearMap (x i - a)| := by
          rw [map_sub]
        _ ≤ S.toLinearMap |x i - a| := Positive.abs_le_map_abs hSpos (x i - a)
        _ ≤ S.toLinearMap (r m) := hSmono hi
        _ = ((OrderDual.ofDual k : rangeIdx) : Y) := hmk

private lemma posPart_decreasing_abs_glb_zero (T : OrderBoundedHom X Y)
    (hcrit : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {x : ι → X},
      Antitone x → (∀ i, 0 ≤ x i) → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun i => |T (x i)|) 0)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {x : ι → X} (hanti : Antitone x) (hnn : ∀ i, 0 ≤ x i)
    (hglb : IsGLB (Set.range x) 0) :
    IsGLB (Set.range fun i => |T⁺ (x i)|) 0 := by
  have hTpos_pos : Positive T⁺.toLinearMap := fun y hy => by
    simpa only [OrderBoundedHom.zero_apply, OrderBoundedHom.toLinearMap_apply] using
      OrderBoundedHom.le_iff.mp (posPart_nonneg T) y hy
  have hTpos_mono : Monotone T⁺.toLinearMap := Positive.monotone_iff.mpr hTpos_pos
  have hglb_pos : IsGLB (Set.range fun i => T⁺ (x i)) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact hTpos_pos (x i) (hnn i)
    · intro z hz
      obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
      let x0 := x i0
      have hx0 : 0 ≤ x0 := hnn i0
      have hz_le_sub : ∀ u : X, 0 ≤ u → u ≤ x0 → z ≤ T⁺ x0 - T u := by
        intro u hu0 hux
        let τ : Type u := {j : ι // i0 ≤ j}
        let : Preorder τ := inferInstance
        let : IsDirected τ (· ≤ ·) := ⟨fun a b => by
          obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
          exact ⟨⟨k, le_trans a.2 hak⟩, hak, hbk⟩⟩
        let : Nonempty τ := ⟨⟨i0, le_rfl⟩⟩
        let y : τ → X := fun j => u ⊓ x j.1
        have hy_anti : Antitone y := fun a b hab => by
          exact inf_le_inf_left u (hanti hab)
        have hy_nn : ∀ j, 0 ≤ y j := fun j => le_inf hu0 (hnn j.1)
        have hy_glb : IsGLB (Set.range y) 0 := by
          refine ⟨?_, ?_⟩
          · rintro _ ⟨j, rfl⟩
            exact hy_nn j
          · intro w hw
            apply hglb.2
            rintro _ ⟨i, rfl⟩
            obtain ⟨k, hi0k, hik⟩ := directed_of (· ≤ ·) i0 i
            calc
              w ≤ y ⟨k, hi0k⟩ := hw ⟨⟨k, hi0k⟩, rfl⟩
              _ ≤ x k := inf_le_right
              _ ≤ x i := hanti hik
        have hTy_glb : IsGLB (Set.range fun j : τ => |T (y j)|) 0 :=
          hcrit hy_anti hy_nn hy_glb
        have hz_lower :
            z - (T⁺ x0 - T u) ∈ lowerBounds (Set.range fun j : τ => |T (y j)|) := by
          rintro _ ⟨j, rfl⟩
          have hxj_le_x0 : x j.1 ≤ x0 := hanti j.2
          have hy_le_u : y j ≤ u := inf_le_left
          have hdiff_nn : 0 ≤ u - y j := sub_nonneg.mpr hy_le_u
          have hdiff_le : u - y j ≤ x0 - x j.1 := by
            rw [show u - y j = (u - x j.1)⁺ from sub_inf_eq_posPart u (x j.1)]
            have hmono : (u - x j.1)⁺ ≤ (x0 - x j.1)⁺ :=
              posPart_mono (sub_le_sub_right hux (x j.1))
            rwa [posPart_of_nonneg (sub_nonneg.mpr hxj_le_x0)] at hmono
          have hTdiff : T (u - y j) ≤ T⁺ (x0 - x j.1) := by
            calc
              T (u - y j) ≤ T⁺ (u - y j) :=
                OrderBoundedHom.le_iff.mp (le_posPart T) (u - y j) hdiff_nn
              _ ≤ T⁺ (x0 - x j.1) := hTpos_mono hdiff_le
          have hlin : T u - T (y j) ≤ T⁺ x0 - T⁺ (x j.1) := by
            change T.toLinearMap u - T.toLinearMap (y j) ≤
              T⁺.toLinearMap x0 - T⁺.toLinearMap (x j.1)
            rw [← map_sub T.toLinearMap, ← map_sub T⁺.toLinearMap]
            exact hTdiff
          have hsum : T⁺ (x j.1) + T u ≤ T⁺ x0 + T (y j) := by
            have hTu : T u ≤ T⁺ x0 - T⁺ (x j.1) + T (y j) :=
              sub_le_iff_le_add.mp hlin
            calc
              T⁺ (x j.1) + T u = T u + T⁺ (x j.1) := by abel
              _ ≤ (T⁺ x0 - T⁺ (x j.1) + T (y j)) + T⁺ (x j.1) :=
                add_le_add_left hTu _
              _ = T⁺ x0 + T (y j) := by abel
          have hzj : z ≤ T⁺ (x j.1) := hz ⟨j.1, rfl⟩
          have hz_to : z ≤ T⁺ x0 + T (y j) - T u := by
            exact hzj.trans (le_sub_iff_add_le.mpr hsum)
          have hz_sub : z - (T⁺ x0 - T u) ≤ T (y j) := by
            rw [sub_le_iff_le_add]
            convert hz_to using 1
            abel
          exact hz_sub.trans (le_abs_self _)
        have hz_sub_nonpos : z - (T⁺ x0 - T u) ≤ 0 := hTy_glb.2 hz_lower
        exact sub_nonpos.mp hz_sub_nonpos
      have hLUB := OrderBoundedHom.isLUB_posPart_apply (f := T) hx0
      have hupper : T⁺ x0 - z ∈ upperBounds {w | ∃ y, 0 ≤ y ∧ y ≤ x0 ∧ w = T y} := by
        rintro _ ⟨u, hu0, hux, rfl⟩
        have hzle := hz_le_sub u hu0 hux
        exact le_sub_iff_add_le.mpr (by
          have h := le_sub_iff_add_le.mp hzle
          simpa [add_comm] using h)
      have hle := hLUB.2 hupper
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at hle
  have hrange : Set.range (fun i => |T⁺ (x i)|) = Set.range (fun i => T⁺ (x i)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (abs_of_nonneg (hTpos_pos (x i) (hnn i))).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, abs_of_nonneg (hTpos_pos (x i) (hnn i))⟩
  rwa [hrange]

private lemma decreasing_abs_glb_zero_of_orderContinuous {T : OrderBoundedHom X Y}
    (hT : IsOrderContinuousOp T.toLinearMap) :
    ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {x : ι → X},
      Antitone x → (∀ i, 0 ≤ x i) → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun i => |T (x i)|) 0 := by
  intro ι _ _ _ x hanti hnn hglb
  have hx := orderConvergesTo_of_antitone_isGLB hanti hglb
  have hTx : OrderConvergesTo (fun i => T (x i)) 0 := by
    simpa [map_zero] using hT hx
  exact isGLB_range_abs_of_orderConvergesTo_zero hTx

private lemma parts_orderContinuous_of_decreasing_abs_glb_zero (T : OrderBoundedHom X Y)
    (hcrit : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {x : ι → X},
      Antitone x → (∀ i, 0 ≤ x i) → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun i => |T (x i)|) 0) :
    IsOrderContinuousOp T⁺.toLinearMap ∧ IsOrderContinuousOp T⁻.toLinearMap := by
  constructor
  · exact positive_orderContinuous_of_decreasing_abs_glb_zero (posPart_nonneg T)
      (posPart_decreasing_abs_glb_zero T hcrit)
  · have hcrit_neg :
        ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
          {x : ι → X},
          Antitone x → (∀ i, 0 ≤ x i) → IsGLB (Set.range x) 0 →
            IsGLB (Set.range fun i => |(-T : OrderBoundedHom X Y) (x i)|) 0 := by
      intro ι _ _ _ x hanti hnn hglb
      have hbase := hcrit hanti hnn hglb
      have hrange :
          Set.range (fun i => |(-T : OrderBoundedHom X Y) (x i)|) =
            Set.range (fun i => |T (x i)|) := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨i, ?_⟩
          change |T.toLinearMap (x i)| = |(-T.toLinearMap) (x i)|
          rw [LinearMap.neg_apply, abs_neg]
        · rintro ⟨i, rfl⟩
          refine ⟨i, ?_⟩
          change |(-T.toLinearMap) (x i)| = |T.toLinearMap (x i)|
          rw [LinearMap.neg_apply, abs_neg]
      rwa [hrange]
    have hneg : IsOrderContinuousOp ((-T : OrderBoundedHom X Y)⁺).toLinearMap :=
      positive_orderContinuous_of_decreasing_abs_glb_zero
        (S := (-T : OrderBoundedHom X Y)⁺) (posPart_nonneg (-T : OrderBoundedHom X Y))
        (posPart_decreasing_abs_glb_zero (-T : OrderBoundedHom X Y) hcrit_neg)
    have hneg_eq : (-T : OrderBoundedHom X Y)⁺ = T⁻ := by
      rw [negPart_def, posPart_def]
    rwa [← hneg_eq]

private lemma modulus_orderContinuous_of_parts (T : OrderBoundedHom X Y)
    (hparts : IsOrderContinuousOp T⁺.toLinearMap ∧ IsOrderContinuousOp T⁻.toLinearMap) :
    IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap := by
  intro ι _ _ _ x a hx
  have hsum := (hparts.1 hx).add (hparts.2 hx)
  have habs : (|T| : OrderBoundedHom X Y) = T⁺ + T⁻ := (posPart_add_negPart T).symm
  simpa only [habs, OrderBoundedHom.toLinearMap_apply, obAdd_apply] using hsum

private lemma orderContinuous_of_modulus_orderContinuous (T : OrderBoundedHom X Y)
    (hmod : IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap) :
    IsOrderContinuousOp T.toLinearMap := by
  intro ι _ _ _ x a hx
  have hxabs := orderConvergesTo_abs_sub_zero hx
  have hmod_abs :
      OrderConvergesTo (fun i => (|T| : OrderBoundedHom X Y).toLinearMap |x i - a|) 0 := by
    simpa [map_zero] using hmod hxabs
  have hsub : OrderConvergesTo (fun i => T.toLinearMap (x i) - T.toLinearMap a) 0 :=
    orderConvergesTo_zero_of_abs_le hmod_abs fun i => by
      calc
        |T.toLinearMap (x i) - T.toLinearMap a| = |T.toLinearMap (x i - a)| := by
          rw [← map_sub T.toLinearMap]
        _ ≤ (|T| : OrderBoundedHom X Y) |x i - a| := by
          simpa using abs_apply_le_modulus_apply_abs T (x i - a)
  exact orderConvergesTo_of_sub_zero hsub

/-- For an order bounded operator into an order complete vector lattice, order continuity is
characterised by the infimum of `|T x_i|` on decreasing zero nets, and equivalently by
order continuity of the positive part, negative part, or modulus. -/
theorem characterization
    (T : OrderBoundedHom X Y) :
    List.TFAE [
      IsOrderContinuousOp T.toLinearMap,
      (∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        {x : ι → X},
        Antitone x → (∀ i, 0 ≤ x i) → IsGLB (Set.range x) 0 →
          IsGLB (Set.range fun i => |T (x i)|) 0),
      IsOrderContinuousOp T⁺.toLinearMap ∧ IsOrderContinuousOp T⁻.toLinearMap,
      IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap] := by
  refine List.tfae_of_cycle ?_ (orderContinuous_of_modulus_orderContinuous T)
  simp only [List.isChain_cons_cons]
  exact ⟨decreasing_abs_glb_zero_of_orderContinuous,
    parts_orderContinuous_of_decreasing_abs_glb_zero T,
    modulus_orderContinuous_of_parts T, List.IsChain.singleton _⟩

section Functional

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X] [CompleteSpace X] [IsOrderContinuousNorm X]

private lemma real_orderConvergesTo_of_tendsto
    {ι : Type u} [Preorder ι]
    {x : ι → ℝ} {a : ℝ} (hx : Filter.Tendsto x Filter.atTop (nhds a)) :
    OrderConvergesTo x a := by
  let Pos : Type := {ε : ℝ // 0 < ε}
  let κ : Type := OrderDual Pos
  have : Nonempty κ := ⟨OrderDual.toDual (⟨1, by norm_num⟩ : Pos)⟩
  have : IsDirected κ (· ≤ ·) := by
    refine ⟨fun p q => ?_⟩
    let p' : Pos := OrderDual.ofDual p
    let q' : Pos := OrderDual.ofDual q
    let δ : ℝ := min (p' : ℝ) (q' : ℝ) / 2
    have hmin : 0 < min (p' : ℝ) (q' : ℝ) := lt_min p'.property q'.property
    have hδ_pos : 0 < δ := by
      exact half_pos hmin
    refine ⟨OrderDual.toDual (⟨δ, hδ_pos⟩ : Pos), ?_, ?_⟩
    · change (⟨δ, hδ_pos⟩ : Pos) ≤ OrderDual.ofDual p
      change δ ≤ (p' : ℝ)
      have hδ_le_min : δ ≤ min (p' : ℝ) (q' : ℝ) := by
        dsimp [δ]
        linarith [le_of_lt hmin]
      exact hδ_le_min.trans (min_le_left _ _)
    · change (⟨δ, hδ_pos⟩ : Pos) ≤ OrderDual.ofDual q
      change δ ≤ (q' : ℝ)
      have hδ_le_min : δ ≤ min (p' : ℝ) (q' : ℝ) := by
        dsimp [δ]
        linarith [le_of_lt hmin]
      exact hδ_le_min.trans (min_le_right _ _)
  refine ⟨κ, inferInstance, inferInstance, inferInstance,
    fun p => ((OrderDual.ofDual p : Pos) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    change ((OrderDual.ofDual q : Pos) : ℝ) ≤ ((OrderDual.ofDual p : Pos) : ℝ)
    exact hpq
  · intro p
    exact le_of_lt (OrderDual.ofDual p : Pos).property
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨p, rfl⟩
      exact le_of_lt (OrderDual.ofDual p : Pos).property
    · intro w hw
      by_contra hle
      have hw_pos : 0 < w := lt_of_not_ge hle
      let p : κ := OrderDual.toDual (⟨w / 2, half_pos hw_pos⟩ : Pos)
      have hwp := hw ⟨p, rfl⟩
      change w ≤ w / 2 at hwp
      linarith
  · intro p
    have hp_pos : 0 < ((OrderDual.ofDual p : Pos) : ℝ) :=
      (OrderDual.ofDual p : Pos).property
    have h_event := Metric.tendsto_nhds.mp hx ((OrderDual.ofDual p : Pos) : ℝ) hp_pos
    exact h_event.mono fun i hi => by
      exact le_of_lt (by simpa [Real.dist_eq] using hi)

/-- On a Banach lattice with order-continuous norm, every order bounded real-valued
functional is order continuous. -/
theorem functional_orderContinuous_of_orderContinuousNorm (f : OrderBoundedHom X ℝ) :
    IsOrderContinuousOp f.toLinearMap := by
  intro ι _ _ _ x a hx
  have hx_tend : Filter.Tendsto x Filter.atTop (nhds a) :=
    tendsto_of_orderConvergesTo_of_isOrderContinuousNorm hx
  let : BanachLattice X := {}
  have hf_cont : Continuous f.toLinearMap := IsOrderBounded.continuous f.isOrderBounded'
  have hf_tend : Filter.Tendsto (fun i => f.toLinearMap (x i)) Filter.atTop
      (nhds (f.toLinearMap a)) :=
    (hf_cont.tendsto a).comp hx_tend
  exact real_orderConvergesTo_of_tendsto hf_tend

end Functional

private lemma orderContinuous_of_abs_le_abs {S T : OrderBoundedHom X Y}
    (hT : T ∈ OrderContinuousOperator (X := X) (Y := Y)) (hST : |S| ≤ |T|) :
    S ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  rw [mem_OrderContinuousOperator] at hT ⊢
  have hmodT : IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap :=
    modulus_orderContinuous_of_parts T
      (parts_orderContinuous_of_decreasing_abs_glb_zero T
        (decreasing_abs_glb_zero_of_orderContinuous hT))
  apply orderContinuous_of_modulus_orderContinuous S
  intro ι _ _ _ x a hx
  have hxabs := orderConvergesTo_abs_sub_zero hx
  have hdom :
      OrderConvergesTo (fun i => (|T| : OrderBoundedHom X Y).toLinearMap |x i - a|) 0 := by
    simpa [map_zero] using hmodT hxabs
  have hsub : OrderConvergesTo
      (fun i => (|S| : OrderBoundedHom X Y).toLinearMap (x i) -
        (|S| : OrderBoundedHom X Y).toLinearMap a) 0 :=
    orderConvergesTo_zero_of_abs_le hdom fun i => by
      calc
        |(|S| : OrderBoundedHom X Y).toLinearMap (x i) -
            (|S| : OrderBoundedHom X Y).toLinearMap a| =
            |(|S| : OrderBoundedHom X Y).toLinearMap (x i - a)| := by
          rw [← map_sub]
        _ ≤ (|(|S| : OrderBoundedHom X Y)| : OrderBoundedHom X Y) |x i - a| := by
          simpa using abs_apply_le_modulus_apply_abs (|S| : OrderBoundedHom X Y) (x i - a)
        _ = (|S| : OrderBoundedHom X Y) |x i - a| := by
          have hSabs_nonneg : (0 : OrderBoundedHom X Y) ≤ |S| := abs_nonneg S
          rw [abs_of_nonneg hSabs_nonneg]
        _ ≤ (|T| : OrderBoundedHom X Y) |x i - a| :=
          OrderBoundedHom.le_iff.mp hST _ (abs_nonneg _)
  exact orderConvergesTo_of_sub_zero hsub

private lemma exists_orderIdeal_coe_eq_OrderContinuousOperator :
    ∃ J : OrderIdeal (OrderBoundedHom X Y),
      (J : Set (OrderBoundedHom X Y)) = OrderContinuousOperator (X := X) (Y := Y) := by
  let M : Submodule ℝ (OrderBoundedHom X Y) :=
    { carrier := OrderContinuousOperator (X := X) (Y := Y)
      zero_mem' := zero_mem_OrderContinuousOperator
      add_mem' := fun {S T} hS hT => add_mem_OrderContinuousOperator hS hT
      smul_mem' := fun c {T} hT => smul_mem_OrderContinuousOperator c hT }
  refine ⟨OrderIdeal.ofSolid M ?_, rfl⟩
  intro T S hT hST
  exact orderContinuous_of_abs_le_abs hT hST

private lemma isGLB_range_sub_apply_of_isLUB {S : Set (OrderBoundedHom X Y)}
    {T : OrderBoundedHom X Y} {x : X}
    (hLUB : IsLUB ((fun A : OrderBoundedHom X Y => A x) '' S) (T x)) :
    IsGLB (Set.range fun A : S => (T - A.1) x) 0 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    change 0 ≤ T.toLinearMap x - A.1.toLinearMap x
    exact sub_nonneg.mpr (hLUB.1 ⟨A.1, A.2, rfl⟩)
  · intro y hy
    have hub : T x - y ∈ upperBounds ((fun A : OrderBoundedHom X Y => A x) '' S) := by
      rintro _ ⟨A, hA, rfl⟩
      have hyA : y ≤ (T - A) x := hy ⟨⟨A, hA⟩, rfl⟩
      change y ≤ T.toLinearMap x - A.toLinearMap x at hyA
      exact le_sub_iff_add_le.mpr (by
        have h := le_sub_iff_add_le.mp hyA
        simpa [add_comm] using h)
    have hle := hLUB.2 hub
    have hneg : 0 ≤ -y := by
      have h := sub_nonneg.mpr hle
      convert h using 1
      abel
    exact neg_nonneg.mp hneg

private lemma positive_directed_isLUB_mem_OrderContinuousOperator
    {S : Set (OrderBoundedHom X Y)}
    (hS : S ⊆ OrderContinuousOperator (X := X) (Y := Y))
    (hpos : ∀ A ∈ S, (0 : OrderBoundedHom X Y) ≤ A) (hdir : DirectedOn (· ≤ ·) S)
    (hne : S.Nonempty) {T : OrderBoundedHom X Y} (hT : IsLUB S T) :
    T ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  rw [mem_OrderContinuousOperator]
  have hT_nonneg : (0 : OrderBoundedHom X Y) ≤ T := by
    obtain ⟨A, hA⟩ := hne
    exact (hpos A hA).trans (hT.1 hA)
  apply positive_orderContinuous_of_decreasing_abs_glb_zero (S := T)
  · exact hT_nonneg
  intro ι _ _ _ x hanti hnn hglb
  have hTpos_fun : Positive T.toLinearMap := fun z hz => by
    simpa only [OrderBoundedHom.zero_apply, OrderBoundedHom.toLinearMap_apply] using
      OrderBoundedHom.le_iff.mp hT_nonneg z hz
  have hglb_T : IsGLB (Set.range fun i => T (x i)) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact hTpos_fun (x i) (hnn i)
    · intro y hy
      obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
      have hx0 : 0 ≤ x i0 := hnn i0
      obtain ⟨U, hU, hpoint⟩ :=
        OrderBoundedHom.isLUB_of_directedOn (X := X) (Y := Y) hne hdir ⟨T, hT.1⟩
      have hUT : U = T := hU.unique hT
      have hpoint_T :
          IsLUB ((fun A : OrderBoundedHom X Y => A (x i0)) '' S) (T (x i0)) := by
        simpa [hUT] using hpoint hx0
      have hdiff_glb :=
        isGLB_range_sub_apply_of_isLUB (S := S) (T := T) hpoint_T
      apply hdiff_glb.2
      intro d hd
      rcases hd with ⟨A, rfl⟩
      have hAoc : IsOrderContinuousOp A.1.toLinearMap :=
        (mem_OrderContinuousOperator A.1).mp (hS A.2)
      have hA_nonneg : (0 : OrderBoundedHom X Y) ≤ A.1 := hpos A.1 A.2
      have hApos_fun : Positive A.1.toLinearMap := fun z hz => by
        simpa only [OrderBoundedHom.zero_apply, OrderBoundedHom.toLinearMap_apply] using
          OrderBoundedHom.le_iff.mp hA_nonneg z hz
      have hA_glb_abs := decreasing_abs_glb_zero_of_orderContinuous hAoc hanti hnn hglb
      have hA_glb : IsGLB (Set.range fun i => A.1 (x i)) 0 := by
        have hrange : Set.range (fun i => |A.1 (x i)|) =
            Set.range (fun i => A.1 (x i)) := by
          ext z
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨i, (abs_of_nonneg (hApos_fun (x i) (hnn i))).symm⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i, abs_of_nonneg (hApos_fun (x i) (hnn i))⟩
        rwa [hrange] at hA_glb_abs
      have hy_lower :
          y - (T - A.1) (x i0) ∈ lowerBounds (Set.range fun i => A.1 (x i)) := by
        rintro _ ⟨k, rfl⟩
        obtain ⟨m, hi0m, hkm⟩ := directed_of (· ≤ ·) i0 k
        have hx0m_nonneg : 0 ≤ x i0 - x m := sub_nonneg.mpr (hanti hi0m)
        have hA_le_T := hT.1 A.2
        have hAT_diff : A.1 (x i0 - x m) ≤ T (x i0 - x m) :=
          OrderBoundedHom.le_iff.mp hA_le_T _ hx0m_nonneg
        have hTm_le : T (x m) ≤ (T - A.1) (x i0) + A.1 (x m) := by
          have hAT_diff' :
              A.1.toLinearMap (x i0) - A.1.toLinearMap (x m) ≤
                T.toLinearMap (x i0) - T.toLinearMap (x m) := by
            change A.1.toLinearMap (x i0 - x m) ≤ T.toLinearMap (x i0 - x m) at hAT_diff
            simpa [map_sub] using hAT_diff
          change T.toLinearMap (x m) ≤
            T.toLinearMap (x i0) - A.1.toLinearMap (x i0) + A.1.toLinearMap (x m)
          rw [show T.toLinearMap (x i0) - A.1.toLinearMap (x i0) +
                A.1.toLinearMap (x m) =
              T.toLinearMap (x i0) -
                (A.1.toLinearMap (x i0) - A.1.toLinearMap (x m)) by abel]
          exact le_sub_iff_add_le.mpr (by
            rw [add_comm]
            exact le_sub_iff_add_le.mp hAT_diff')
        have hy_m : y ≤ T (x m) := hy ⟨m, rfl⟩
        have hy_to_m : y - (T - A.1) (x i0) ≤ A.1 (x m) :=
          sub_le_iff_le_add.mpr (by simpa [add_comm] using hy_m.trans hTm_le)
        exact hy_to_m.trans (Positive.monotone_iff.mpr hApos_fun (hanti hkm))
      exact sub_nonpos.mp (hA_glb.2 hy_lower)
  have hrange : Set.range (fun i => |T (x i)|) = Set.range (fun i => T (x i)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (abs_of_nonneg (hTpos_fun (x i) (hnn i))).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, abs_of_nonneg (hTpos_fun (x i) (hnn i))⟩
  rwa [hrange]

private lemma isLUB_mem_OrderContinuousOperator {S : Set (OrderBoundedHom X Y)}
    (hS : S ⊆ OrderContinuousOperator (X := X) (Y := Y)) (hne : S.Nonempty)
    {T : OrderBoundedHom X Y} (hT : IsLUB S T) :
    T ∈ OrderContinuousOperator (X := X) (Y := Y) := by
  obtain ⟨J, hJ⟩ := exists_orderIdeal_coe_eq_OrderContinuousOperator (X := X) (Y := Y)
  let B : Band (OrderBoundedHom X Y) :=
    Band.ofPosDirectedSSupMem J fun S hSJ hpos hdir hneS T hT => by
      change T ∈ (J : Set (OrderBoundedHom X Y))
      rw [hJ]
      exact positive_directed_isLUB_mem_OrderContinuousOperator
        (fun A hA => by rw [← hJ]; exact hSJ hA) hpos hdir hneS hT
  rw [← hJ]
  exact B.sSup_mem (fun A hA => by
    change A ∈ (J : Set (OrderBoundedHom X Y))
    rw [hJ]
    exact hS hA) hne hT

private lemma exists_band_coe_eq_OrderContinuousOperator :
    ∃ B : Band (OrderBoundedHom X Y),
      (B : Set (OrderBoundedHom X Y)) = OrderContinuousOperator (X := X) (Y := Y) := by
  obtain ⟨J, hJ⟩ := exists_orderIdeal_coe_eq_OrderContinuousOperator (X := X) (Y := Y)
  refine ⟨{ toOrderIdeal := J, sSup_mem' := ?_ }, hJ⟩
  intro S hS hne T hT
  change T ∈ (J : Set (OrderBoundedHom X Y))
  rw [hJ]
  exact isLUB_mem_OrderContinuousOperator (X := X) (Y := Y)
    (fun A hA => by rw [← hJ]; exact hS hA) hne hT

private lemma decomposition_OrderContinuousOperator (T : OrderBoundedHom X Y) :
    ∃ S R : OrderBoundedHom X Y,
      S ∈ OrderContinuousOperator (X := X) (Y := Y) ∧
        R ∈ disjointComplement (OrderContinuousOperator (X := X) (Y := Y)) ∧ T = S + R := by
  let : ConditionallyCompleteLattice (OrderBoundedHom X Y) :=
    @conditionallyCompleteLatticeOfPosSet (OrderBoundedHom X Y) _ _ _
      (fun {S} _ hne hbdd => OrderBoundedHom.exists_isLUB (S := S) hne hbdd)
  have : HasProjectionProperty (OrderBoundedHom X Y) :=
    HasProjectionProperty.of_isOrderComplete
  obtain ⟨B, hB⟩ := exists_band_coe_eq_OrderContinuousOperator (X := X) (Y := Y)
  obtain ⟨P, hP⟩ := HasProjectionProperty.exists_projectionBand B
  obtain ⟨S, R, hS, hR, hT⟩ := P.decomposition T
  refine ⟨S, R, ?_, ?_, hT⟩
  · rw [← hB, ← hP]
    exact hS
  · rw [← hB, ← hP]
    exact hR

/-- Ogasawara's theorem: The order-continuous order bounded operators
  form a projection band in the lattice of order bounded operators. -/
theorem ogasawara_theorem
    {Y : Type v} [AddCommGroup Y] [ConditionallyCompleteLattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] :
    ∃ B : ProjectionBand (OrderBoundedHom X Y),
      (B : Set (OrderBoundedHom X Y)) = OrderContinuousOperator (X := X) (Y := Y) := by
  let : ConditionallyCompleteLattice (OrderBoundedHom X Y) :=
    @conditionallyCompleteLatticeOfPosSet (OrderBoundedHom X Y) _ _ _
      (fun {S} _ hne hbdd => OrderBoundedHom.exists_isLUB (S := S) hne hbdd)
  have : HasProjectionProperty (OrderBoundedHom X Y) :=
    HasProjectionProperty.of_isOrderComplete
  obtain ⟨B, hB⟩ := exists_band_coe_eq_OrderContinuousOperator (X := X) (Y := Y)
  obtain ⟨P, hP⟩ := HasProjectionProperty.exists_projectionBand B
  exact ⟨P, hP.trans hB⟩

end OrderContinuousOp
