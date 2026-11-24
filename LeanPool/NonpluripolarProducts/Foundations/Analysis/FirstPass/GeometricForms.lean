/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HermitianGeometry

/-!
# Geometric equality of chartwise differential forms

Only coefficients on the open chart targets represent a differential form.
`GeometricallyEq` forgets arbitrary extensions outside those targets. Its
quotient is optional: the representative API and all the properties below
already respect this relation. No coordinate naturality of exterior
differentiation is needed to prove locality under this equality.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace SmoothRealForm

/-- Equality of geometric forms, independent of off-target extensions. -/
def GeometricallyEq (a b : SmoothRealForm n M k) : Prop :=
  ∀ e, EqOn (a.coeff e) (b.coeff e) e.val.target

theorem GeometricallyEq.refl (a : SmoothRealForm n M k) : a.GeometricallyEq a :=
  fun _ _ _ => rfl

theorem GeometricallyEq.symm {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : b.GeometricallyEq a :=
  fun e => (h e).symm

theorem GeometricallyEq.trans {a b c : SmoothRealForm n M k}
    (hab : a.GeometricallyEq b) (hbc : b.GeometricallyEq c) : a.GeometricallyEq c :=
  fun e => (hab e).trans (hbc e)

theorem geometricallyEq_equivalence :
    Equivalence (GeometricallyEq (n := n) (M := M) (k := k)) :=
  ⟨GeometricallyEq.refl, GeometricallyEq.symm, GeometricallyEq.trans⟩

/-- Targetwise equality is exactly equality of all geometric evaluations. -/
theorem geometricallyEq_iff {a b : SmoothRealForm n M k} :
    a.GeometricallyEq b ↔
      ∀ e z, z ∈ e.val.target → ∀ v, a.coeff e z v = b.coeff e z v := by
  constructor
  · intro h e z hz v
    rw [h e hz]
  · intro h e z hz
    ext v
    exact h e z hz v

/-- Open targets make equal coefficients equal as germs at every target point. -/
theorem GeometricallyEq.coeff_eventuallyEq {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) : a.coeff e =ᶠ[𝓝 z] b.coeff e :=
  eventually_of_mem (e.val.open_target.mem_nhds hz) (fun _ hw => h e hw)

/-- Exterior differentiation is local, even though coefficients are total functions. -/
theorem GeometricallyEq.extDeriv_eqOn {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) (e : ComplexChart n M) :
    EqOn (extDeriv (a.coeff e)) (extDeriv (b.coeff e)) e.val.target :=
  fun _ hz => (h.coeff_eventuallyEq e hz).extDeriv_eq

theorem GeometricallyEq.isClosed_iff {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : a.IsClosed ↔ b.IsClosed := by
  constructor
  · intro ha e z hz
    rw [← h.extDeriv_eqOn e hz]
    exact ha e z hz
  · intro hb e z hz
    rw [h.extDeriv_eqOn e hz]
    exact hb e z hz

/-- Type `(1,1)` for a given global real two-form. -/
def IsTypeOneOne (a : SmoothRealForm n M 2) : Prop :=
  ∀ e z, z ∈ e.val.target → IsOneOne (a.coeff e z)

/-- The usual semipositivity cone, evaluated on actual complex tangent lines. -/
def IsSemipositive (a : SmoothRealForm n M 2) : Prop :=
  ∀ e z, z ∈ e.val.target → ∀ v, 0 ≤ a.coeff e z ![v, Complex.I • v]

theorem GeometricallyEq.isTypeOneOne_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsTypeOneOne ↔ b.IsTypeOneOne := by
  unfold IsTypeOneOne
  exact forall_congr' fun e => forall_congr' fun z =>
    forall_congr' fun hz => by rw [h e hz]

theorem GeometricallyEq.isSemipositive_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsSemipositive ↔ b.IsSemipositive := by
  unfold IsSemipositive
  exact forall_congr' fun e => forall_congr' fun z =>
    forall_congr' fun hz => by rw [h e hz]

theorem GeometricallyEq.isHermitian_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsHermitian ↔ b.IsHermitian := by
  unfold IsHermitian
  exact forall_congr' fun e => forall_congr' fun z =>
    forall_congr' fun hz => by rw [h e hz]

theorem GeometricallyEq.isKahler_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsKahler ↔ b.IsKahler :=
  and_congr h.isHermitian_iff h.isClosed_iff

/-- An explicit setoid, without changing Lean's equality of representatives. -/
def geometricSetoid : Setoid (SmoothRealForm n M k) where
  r := GeometricallyEq
  iseqv := geometricallyEq_equivalence

end SmoothRealForm

/-- Geometric forms with off-target coefficient extensions identified. -/
def GeometricRealForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (k : ℕ) :=
  Quotient (SmoothRealForm.geometricSetoid (n := n) (M := M) (k := k))

namespace GeometricRealForm

/-- The geometric form represented by smooth chart data. -/
def ofRepresentative (a : SmoothRealForm n M k) : GeometricRealForm n M k :=
  Quotient.mk _ a

theorem ofRepresentative_eq_iff (a b : SmoothRealForm n M k) :
    ofRepresentative a = ofRepresentative b ↔ a.GeometricallyEq b :=
  Quotient.eq

/-- Closedness descends to geometric forms. -/
def IsClosed (a : GeometricRealForm n M k) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) SmoothRealForm.IsClosed
    (fun _ _ h => propext h.isClosed_iff) a

/-- Hermitian positivity descends to geometric forms. -/
def IsHermitian (a : GeometricRealForm n M 2) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) SmoothRealForm.IsHermitian
    (fun _ _ h => propext h.isHermitian_iff) a

/-- Kählerness descends without asserting the existence of any Kähler form. -/
def IsKahler (a : GeometricRealForm n M 2) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) SmoothRealForm.IsKahler
    (fun _ _ h => propext h.isKahler_iff) a

@[simp] theorem isClosed_ofRepresentative (a : SmoothRealForm n M k) :
    (ofRepresentative a).IsClosed ↔ a.IsClosed := Iff.rfl

@[simp] theorem isHermitian_ofRepresentative (a : SmoothRealForm n M 2) :
    (ofRepresentative a).IsHermitian ↔ a.IsHermitian := Iff.rfl

@[simp] theorem isKahler_ofRepresentative (a : SmoothRealForm n M 2) :
    (ofRepresentative a).IsKahler ↔ a.IsKahler := Iff.rfl

end GeometricRealForm

end

end SGPT.Foundations.Analysis.FirstPass
