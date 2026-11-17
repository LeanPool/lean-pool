/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.UniversalPlaneSpecialization

/-! Exact incidence averaging over every affine-plane parameter triple,
including degenerate triples. No divisibility correction for plane charts
is needed because points and directions are kept as coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A parameter triple and a coordinate pair mapping into the hypersurface. -/
private def PlaneIncidence {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :=
  {vt : (PlaneParameters σ → K) × (Fin 2 → K) //
    bivariateEval (vt.2 0) (vt.2 1) (universalPlaneSection f vt.1) = 0}

/-- Once the image point, both directions and the two plane coordinates are
fixed, the base point is determined uniquely. -/
private def planeIncidenceEquiv {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    PlaneIncidence f ≃
      ({z : σ → K // eval z f = 0} × (σ → K) × (σ → K) × (Fin 2 → K)) where
  toFun vt :=
    (⟨fun i => vt.val.1 (i,0) + vt.val.1 (i,1) * vt.val.2 0 + vt.val.1 (i,2) * vt.val.2 1,
      by rw [← universalPlaneSection_eval]; exact vt.property⟩,
      fun i => vt.val.1 (i,1), fun i => vt.val.1 (i,2), vt.val.2)
  invFun z :=
    ⟨(fun i => ![z.1.val i.1 - z.2.1 i.1 * z.2.2.2 0 - z.2.2.1 i.1 * z.2.2.2 1,
        z.2.1 i.1, z.2.2.1 i.1] i.2, z.2.2.2), by
      rw [universalPlaneSection_eval]
      convert z.1.property using 1
      congr 2
      funext i
      simp
      ring⟩
  left_inv vt := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      rcases i with ⟨i,j⟩
      fin_cases j <;> simp
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp
      ring
    · rfl

/-- Exact incidence identity: q^(2*m+2) incidences per hypersurface point. -/
private theorem planeIncidence_card {K σ : Type*} [CommRing K] [Fintype K] [Fintype σ]
    (f : MvPolynomial σ K) :
    Nat.card (PlaneIncidence f) =
      Nat.card {z : σ → K // eval z f = 0} * Fintype.card K ^ (2 * Fintype.card σ + 2) := by
  classical
  rw [Nat.card_congr (planeIncidenceEquiv f)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_add, ← pow_add]
  congr 2
  omega

/-- All plane coordinates whose image lies on the hypersurface. -/
def PlaneSectionPoints {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) :=
  {t : Fin 2 → K // bivariateEval (t 0) (t 1) (universalPlaneSection f v) = 0}

private def planeIncidenceSigmaEquiv {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    PlaneIncidence f ≃ Σ v, PlaneSectionPoints f v where
  toFun vt := ⟨vt.val.1, ⟨vt.val.2, vt.property⟩⟩
  invFun vt := ⟨(vt.1, vt.2.val), vt.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The section counts sum to the exact incidence count. -/
theorem sum_planeSectionPoints_card {K σ : Type*} [CommRing K] [Fintype K] [Fintype σ]
    [DecidableEq σ] (f : MvPolynomial σ K) :
    ∑ v : PlaneParameters σ → K, Nat.card (PlaneSectionPoints f v) =
      Nat.card {z : σ → K // eval z f = 0} * Fintype.card K ^ (2 * Fintype.card σ + 2) := by
  classical
  rw [← planeIncidence_card f, Nat.card_congr (planeIncidenceSigmaEquiv f)]
  let (v : PlaneParameters σ → K) : Fintype (PlaneSectionPoints f v) :=
    inferInstanceAs (Fintype {t : Fin 2 → K //
      bivariateEval (t 0) (t 1) (universalPlaneSection f v) = 0})
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]

end
end CCDN
