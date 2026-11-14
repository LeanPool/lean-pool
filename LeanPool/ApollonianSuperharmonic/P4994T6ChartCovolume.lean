/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TilingLatticeIndex

-- [TABLET NODE: P4994T6ChartCovolume]

/-!
# P4994T6ChartCovolume

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6ChartCovolume (C : BandCircle) (e f : GaussianInt)
    (hdet : 0 < e.re * f.im - e.im * f.re)
    (he : e ∈ TilingLattice C) (hf : f ∈ TilingLattice C)
    (hcoord : ∀ w : TilingLattice C, ∃! z : Int × Int,
      (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f = (w : GaussianInt)) :
    e.re * f.im - e.im * f.re = C.1.1.1 := by
-- BODY
  classical
  let K := TilingLattice C
  let chart : (Fin 2 → ℤ) →ₗ[ℤ] K :=
    { toFun := fun x => ⟨x 0 • e + x 1 • f,
        K.add_mem (K.zsmul_mem he _) (K.zsmul_mem hf _)⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [zsmul_eq_mul, Int.cast_add]
        ring
      map_smul' := by
        intro n x
        apply Subtype.ext
        simp [zsmul_eq_mul, Int.cast_mul]
        ring }
  have chart_injective : Function.Injective chart := by
    intro x y hxy
    have eqv := congrArg Subtype.val hxy
    have hx : ((x 0 : ℤ) : GaussianInt) * e + (x 1 : GaussianInt) * f =
        (chart x : GaussianInt) := by simp [chart, zsmul_eq_mul]
    have hy : ((y 0 : ℤ) : GaussianInt) * e + (y 1 : GaussianInt) * f =
        (chart x : GaussianInt) := by simpa [chart, zsmul_eq_mul] using eqv.symm
    have eqp : (x 0, x 1) = (y 0, y 1) := (hcoord (chart x)).unique hx hy
    funext j
    fin_cases j
    · exact congrArg Prod.fst eqp
    · exact congrArg Prod.snd eqp
  have chart_surjective : Function.Surjective chart := by
    intro w
    obtain ⟨p, hp, _⟩ := hcoord w
    refine ⟨![p.1, p.2], Subtype.ext ?_⟩
    simpa [chart, zsmul_eq_mul] using hp
  let coordinates : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    { toFun := fun z => ![z.re, z.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := by intro z; ext <;> simp
      right_inv := by intro x; funext i; fin_cases i <;> simp
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro n x; funext i; fin_cases i <;> simp }
  let chartEquiv := LinearEquiv.ofBijective chart ⟨chart_injective, chart_surjective⟩
  let basisK : Module.Basis (Fin 2) ℤ K := (Pi.basisFun ℤ (Fin 2)).map chartEquiv
  let basisG : Module.Basis (Fin 2) ℤ GaussianInt :=
    Module.Basis.ofEquivFun coordinates
  have index_value : K.index = Int.natAbs (e.re * f.im - e.im * f.re) := by
    rw [AddSubgroup.index_eq_natAbs_det basisG K basisK]
    congr 1
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply, basisG, basisK, chartEquiv, chart, coordinates]
    ring
  obtain ⟨S, hS, hcard⟩ := TilingLatticeIndex C
  let quotientMap : GaussianInt → GaussianInt ⧸ K := QuotientAddGroup.mk' K
  have bijective : Function.Bijective (fun s : ↥S => quotientMap s) := by
    constructor
    · intro s t hst
      apply Subtype.ext
      exact (hS s).unique ⟨s.property, by simp⟩
        ⟨t.property, QuotientAddGroup.eq_iff_sub_mem.mp hst⟩
    · intro w
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective K w
      obtain ⟨s, hs, _⟩ := hS z
      exact ⟨⟨s, hs.1⟩, (QuotientAddGroup.eq_iff_sub_mem.mpr hs.2).symm⟩
  have index_card : K.index = S.card := by
    rw [K.index_eq_card, ← Nat.card_congr (Equiv.ofBijective _ bijective)]
    simp
  have abs_eq : Int.natAbs (e.re * f.im - e.im * f.re) = C.1.1.1.natAbs := by
    rw [← index_value, index_card, hcard]
  have cast_eq := congrArg (fun n : Nat => (n : Int)) abs_eq
  simpa [Int.natCast_natAbs, abs_of_pos hdet, abs_of_pos C.2] using cast_eq

end ApollonianSuperharmonic

end
