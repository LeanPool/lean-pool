/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint


-- [TABLET NODE: BandOrderedGeneralSubtileCanonicalRows]

/-!
# BandOrderedGeneralSubtileCanonicalRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralSubtileCanonicalRows
    (P : Fin 3 → Bool → ProtoTile) (T : ProtoTile)
    (u v : GaussianInt) (parentSlot : Fin 3) (turn : Fin 4)
    (edge incoming outgoing : Fin 3 → GaussianInt)
    (hsuper : edge 0 + edge 1 + edge 2 = 0)
    (hin0 : incoming 0 = edge 1 - (⟨0, 1⟩ : GaussianInt) * edge 2)
    (hin1 : incoming 1 = edge 2 - (⟨0, 1⟩ : GaussianInt) * edge 0)
    (hin2 : incoming 2 = edge 0 - (⟨0, 1⟩ : GaussianInt) * edge 1)
    (hflip : ∀ j, outgoing j = (⟨0, 1⟩ : GaussianInt) * incoming j)
    (hu : u = outgoing 0) (hv : v = outgoing 1)
    (hcentroid : ∀ j e,
      TileCentroid (P j e) - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) •
          ((1 / 2 : ℝ) •
            (GaussianRealPoint (edge j) -
              (-((GaussianRealPoint (edge j)).2),
                (GaussianRealPoint (edge j)).1)))) :
    let uIndex : PeriodicSubtileIndex :=
      if parentSlot = 0 then
        if turn = 0 then ⟨.A, 0, -1⟩
        else if turn = 1 then ⟨.B, 1, 1⟩
        else if turn = 2 then ⟨.B, 0, 1⟩
        else ⟨.A, -1, -1⟩
      else if parentSlot = 1 then
        if turn = 0 then ⟨.C, 1, 1⟩
        else if turn = 1 then ⟨.D, -1, 0⟩
        else if turn = 2 then ⟨.D, -1, -1⟩
        else ⟨.C, 1, 0⟩
      else
        if turn = 0 then ⟨.E, -1, 0⟩
        else if turn = 1 then ⟨.F, 0, -1⟩
        else if turn = 2 then ⟨.F, 1, 0⟩
        else ⟨.E, 0, 1⟩
    let vIndex : PeriodicSubtileIndex :=
      if parentSlot = 0 then
        if turn = 0 then ⟨.C, 1, 0⟩
        else if turn = 1 then ⟨.F, 1, 0⟩
        else if turn = 2 then ⟨.D, -1, 0⟩
        else ⟨.E, -1, 0⟩
      else if parentSlot = 1 then
        if turn = 0 then ⟨.E, 0, 1⟩
        else if turn = 1 then ⟨.B, 0, 1⟩
        else if turn = 2 then ⟨.F, 0, -1⟩
        else ⟨.A, 0, -1⟩
      else
        if turn = 0 then ⟨.A, -1, -1⟩
        else if turn = 1 then ⟨.D, -1, -1⟩
        else if turn = 2 then ⟨.B, 1, 1⟩
        else ⟨.C, 1, 1⟩
    let U := SubtileOccurrenceInterpretation P u v uIndex
    let V := SubtileOccurrenceInterpretation P u v vIndex
    TileCentroid U - TileCentroid T = (1 / 2 : ℝ) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ turn.val *
          (incoming parentSlot + outgoing parentSlot)) ∧
    TileCentroid V - TileCentroid T = (1 / 2 : ℝ) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ turn.val *
          (if Even turn.val then
            incoming (parentSlot + 1) - outgoing (parentSlot + 1)
          else
            outgoing (parentSlot - 1) - incoming (parentSlot - 1))) := by
-- BODY
  have hf0 := hflip 0
  have hf1 := hflip 1
  have hf2 := hflip 2
  have smul_fst (r : ℝ) (p : ℝ × ℝ) : (r • p).1 = r * p.1 := rfl
  have smul_snd (r : ℝ) (p : ℝ × ℝ) : (r • p).2 = r * p.2 := rfl
  have translatedCentroid (j : Fin 3) (e : Bool) (d z : GaussianInt)
      (hz : (if e = true then (1 : GaussianInt) else -1) *
          (edge j - (⟨0, 1⟩ : GaussianInt) * edge j) + 2 * d = z) :
      TileCentroid (TileTranslation (P j e) d) - TileCentroid T =
        (2 : ℝ)⁻¹ • GaussianRealPoint z := by
    have hc := hcentroid j e
    rw [(TileTranslationFormulas (P j e) d).2.2.2.2.1]
    have hzre := congrArg (fun w : GaussianInt => w.re) hz
    have hzim := congrArg (fun w : GaussianInt => w.im) hz
    have hreInt :
        ((if e = true then (1 : GaussianInt) else -1) *
              (edge j - (⟨0, 1⟩ : GaussianInt) * edge j)).re +
            2 * d.re = z.re := by simpa using hzre
    have himInt :
        ((if e = true then (1 : GaussianInt) else -1) *
              (edge j - (⟨0, 1⟩ : GaussianInt) * edge j)).im +
            2 * d.im = z.im := by simpa using hzim
    rw [Prod.ext_iff] at hc ⊢
    rcases hc with ⟨hc1, hc2⟩
    rw [Prod.fst_sub] at hc1
    rw [Prod.snd_sub] at hc2
    rw [Prod.fst_sub, Prod.snd_sub]
    rw [smul_fst] at hc1 ⊢
    rw [smul_snd] at hc2 ⊢
    fin_cases e
    · simp only [Int.reduceNeg, ↓reduceIte, one_mul, Zsqrtd.re_sub, Zsqrtd.re_mul, zero_mul,
        mul_one, neg_mul, zero_add, sub_neg_eq_add, Zsqrtd.im_sub, Zsqrtd.im_mul]
        at hreInt himInt
      norm_num only [Bool.true_eq, ↓reduceIte, GaussianRealPoint] at hc1 hc2 ⊢
      dsimp at hc1 hc2 ⊢
      constructor
      · have hre : ((edge j).re : ℝ) + ((edge j).im : ℝ) +
            2 * (d.re : ℝ) = (z.re : ℝ) := by exact_mod_cast hreInt
        linarith
      · have him : ((edge j).im : ℝ) - ((edge j).re : ℝ) +
            2 * (d.im : ℝ) = (z.im : ℝ) := by exact_mod_cast himInt
        linarith
    · simp only [Int.reduceNeg, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, neg_sub,
        Zsqrtd.re_sub, Zsqrtd.re_mul, zero_mul, mul_one, zero_add, Zsqrtd.im_sub,
        Zsqrtd.im_mul] at hreInt himInt
      norm_num only [Bool.false_eq_true, ↓reduceIte, GaussianRealPoint] at hc1 hc2 ⊢
      dsimp at hc1 hc2 ⊢
      constructor
      · have hre : -((edge j).im : ℝ) - ((edge j).re : ℝ) +
            2 * (d.re : ℝ) = (z.re : ℝ) := by exact_mod_cast hreInt
        linarith
      · have him : ((edge j).re : ℝ) - ((edge j).im : ℝ) +
            2 * (d.im : ℝ) = (z.im : ℝ) := by exact_mod_cast himInt
        linarith
  have hsre := congrArg (fun z : GaussianInt => z.re) hsuper
  have hsim := congrArg (fun z : GaussianInt => z.im) hsuper
  have h0re := congrArg (fun z : GaussianInt => z.re) hin0
  have h0im := congrArg (fun z : GaussianInt => z.im) hin0
  have h1re := congrArg (fun z : GaussianInt => z.re) hin1
  have h1im := congrArg (fun z : GaussianInt => z.im) hin1
  have h2re := congrArg (fun z : GaussianInt => z.re) hin2
  have h2im := congrArg (fun z : GaussianInt => z.im) hin2
  have f0re := congrArg (fun z : GaussianInt => z.re) hf0
  have f0im := congrArg (fun z : GaussianInt => z.im) hf0
  have f1re := congrArg (fun z : GaussianInt => z.re) hf1
  have f1im := congrArg (fun z : GaussianInt => z.im) hf1
  have f2re := congrArg (fun z : GaussianInt => z.re) hf2
  have f2im := congrArg (fun z : GaussianInt => z.im) hf2
  have notEven3 : ¬ Even 3 := by
    rintro ⟨r, hr⟩
    omega
  generalize hp : parentSlot = ps
  generalize ht : turn = t
  fin_cases ps <;>
    fin_cases t <;>
    simp only [] <;>
    norm_num
  all_goals
    focus
      refine ⟨?_, ?_⟩
      · simp only [SubtileOccurrenceInterpretation, Fin.isValue, Int.cast_one, one_mul,
          Int.cast_zero, zero_mul, add_zero, one_div, Int.reduceNeg, zero_add, Int.cast_neg,
          neg_mul]
        norm_num
        rw [one_div]
        apply translatedCentroid
        apply Zsqrtd.ext <;>
          simp at hsre hsim h0re h0im h1re h1im h2re h2im <;>
          simp [hu, hv, pow_succ] at f0re f0im f1re f1im f2re f2im ⊢ <;>
          omega
      · simp only [SubtileOccurrenceInterpretation, Fin.isValue, Int.cast_one, one_mul,
          Int.cast_zero, zero_mul, add_zero, one_div, Int.reduceNeg, zero_add, Int.cast_neg,
          neg_mul]
        norm_num
        rw [one_div]
        apply translatedCentroid
        apply Zsqrtd.ext <;>
          simp at hsre hsim h0re h0im h1re h1im h2re h2im <;>
          simp [hu, hv, pow_succ, notEven3, show (-1 : Fin 3) = 2 by decide]
            at f0re f0im f1re f1im f2re f2im ⊢ <;>
          omega

end ApollonianSuperharmonic

end
