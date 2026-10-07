/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselEmbedding
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeat
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierLeray
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis

/-!
# Ordered derivatives of Sobolev distributions

Each distributional spatial derivative lowers the Bessel order by one.
The ordered form supplies the Fourier-integrability threshold for the
classical positive-time representative.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap LineDeriv

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- An ordered finite list of spatial directions lowers the Sobolev order
by the number of directional derivatives. -/
theorem regularised_orderedLineDeriv_memSobolev
    (D : 𝓢'(L2Vec3, ComplexVec3)) (s : ℝ)
    (hD : D.MemSobolev s 2) (α : List L2Vec3) :
    (α.foldl (fun F m => ∂_{m} F) D).MemSobolev
      (s - (α.length : ℝ)) 2 := by
  induction α using List.reverseRecOn with
  | nil => simpa using hD
  | append_singleton α m ih =>
      have hnext := ih.lineDerivOp (m := m)
      simpa only [List.foldl_append, List.foldl_cons,
        List.foldl_nil, List.length_append, List.length_singleton,
        Nat.cast_add, Nat.cast_one, sub_sub] using hnext

/-- Every ordered derivative through the Bessel order is represented by
a spatial L² field as a tempered distribution. -/
theorem regularisedBesselEven_orderedLineDeriv_L2
    (k : ℕ)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2)
    (α : List L2Vec3) (hα : α.length ≤ 2 * k) :
    ∃ g : ComplexVectorL2,
      (α.foldl (fun D m => ∂_{m} D) v.toDistr) =
        (g : 𝓢'(L2Vec3, ComplexVec3)) := by
  have hlen : (α.length : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
    exact_mod_cast hα
  have horder : 0 ≤ ((2 * k : ℕ) : ℝ) - (α.length : ℝ) := by
    linarith only [hlen]
  have hSobolev := regularised_orderedLineDeriv_memSobolev
    v.toDistr ((2 * k : ℕ) : ℝ)
    (BesselPotentialSpace.memSobolev_toDistr v) α
  obtain ⟨G, hG⟩ :=
    TemperedDistribution.memSobolev_zero_iff_exists_fourier.mp
      (hSobolev.mono horder)
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  refine ⟨ℱ.symm G, ?_⟩
  have hInv := congrArg
    (fun D : 𝓢'(L2Vec3, ComplexVec3) => 𝓕⁻ D) hG
  have hFourier : ℱ.symm G = 𝓕⁻ G := rfl
  rw [hFourier]
  simpa only [fourierInv_fourier_eq,
    MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq] using hInv

end CKN.Leray

end
