/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGain

/-!
# Uniqueness and restriction of Sobolev families

`prop:lps-smoothing`: a Sobolev family through order `M` is a Sobolev family through every
smaller order, and two space-time Sobolev families of the same function, of possibly different
orders, agree almost everywhere on the slab through the smaller order.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A Sobolev family through order `M` is a Sobolev family through every smaller order
(`prop:lps-smoothing`). -/
theorem _root_.CKN.IsSobolevFamilyOn.mono_order {m M : ℕ} {U : Set Vec3} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (h : IsSobolevFamilyOn M U f D) (hm : m ≤ M) :
    IsSobolevFamilyOn m U f D :=
  ⟨h.zero, fun α hα => h.memL2 α (hα.trans hm), fun α j hα => h.weak α j (lt_of_lt_of_le hα hm)⟩

/-- Uniqueness of weak spatial derivatives on a slab: two space-time Sobolev families of the same
function, through orders `M` and `M'`, agree almost everywhere on the slab through every order
at most `M` and `M'` (`prop:lps-smoothing`). -/
theorem lps_l2SobolevFamily_unique {M M' : ℕ} {I : Set ℝ} (hI : IsOpen I)
    {z : Vec3 × ℝ → ℝ} {D D' : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsL2SobolevFamilyOn M (Set.univ : Set Vec3) I z D)
    (h' : IsL2SobolevFamilyOn M' (Set.univ : Set Vec3) I z D') (α : List (Fin 3)) :
    α.length ≤ M → α.length ≤ M' →
      D α =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ I)] D' α := by
  induction α using List.reverseRecOn with
  | nil => intro _ _; exact h.zero.trans h'.zero.symm
  | append_singleton β j ih =>
    intro h1 h2
    rw [List.length_append, List.length_singleton] at h1 h2
    have ih' := ih (by omega) (by omega)
    have hU : IsOpen ((Set.univ : Set Vec3) ×ˢ I) := isOpen_univ.prod hI
    set μ : Measure (Vec3 × ℝ) := volume.restrict ((Set.univ : Set Vec3) ×ˢ I) with hμ
    have hL : ∀ (Dx : Vec3 × ℝ → ℝ), MemLp Dx 2 μ → LocallyIntegrable Dx μ :=
      fun Dx hDx => hDx.locallyIntegrable (by norm_num)
    have hf : LocallyIntegrableOn (D (β ++ [j]) - D' (β ++ [j])) ((Set.univ : Set Vec3) ×ˢ I) μ :=
      ((hL _ (h.memL2 _ (by simpa only [List.length_append, List.length_singleton] using h1))).sub
        (hL _ (h'.memL2 _ (by simpa only [List.length_append, List.length_singleton] using h2))))
        |>.locallyIntegrableOn _
    have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf (fun g hg hgc hgs => by
      have e1 := h.weak β j (by omega) g hg hgc hgs
      have e2 := h'.weak β j (by omega) g hg hgc hgs
      have e3 : ∫ p in (Set.univ : Set Vec3) ×ˢ I, D β p * spatialPartial g j p =
          ∫ p in (Set.univ : Set Vec3) ×ˢ I, D' β p * spatialPartial g j p :=
        integral_congr_ae (by filter_upwards [ih'] with p hp using by rw [hp])
      have hi1 : Integrable (fun p => D (β ++ [j]) p * g p) μ := by
        have hlocal := hL _ (h.memL2 (β ++ [j])
          (by simpa only [List.length_append, List.length_singleton] using h1))
        have := hlocal.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
        simpa [smul_eq_mul, mul_comm] using this
      have hi2 : Integrable (fun p => D' (β ++ [j]) p * g p) μ := by
        have hlocal := hL _ (h'.memL2 (β ++ [j])
          (by simpa only [List.length_append, List.length_singleton] using h2))
        have := hlocal.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
        simpa [smul_eq_mul, mul_comm] using this
      have : ∫ p, g p • (D (β ++ [j]) - D' (β ++ [j])) p ∂μ =
          ∫ p, D (β ++ [j]) p * g p ∂μ - ∫ p, D' (β ++ [j]) p * g p ∂μ := by
        rw [← integral_sub hi1 hi2]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [Pi.sub_apply, smul_eq_mul]; ring
      rw [this]
      have e4 : ∫ p, D (β ++ [j]) p * g p ∂μ = ∫ p, D' (β ++ [j]) p * g p ∂μ := by
        change ∫ p in (Set.univ : Set Vec3) ×ˢ I, D (β ++ [j]) p * g p =
          ∫ p in (Set.univ : Set Vec3) ×ˢ I, D' (β ++ [j]) p * g p
        have := e1.symm.trans (e3.trans e2)
        linarith only [this]
      rw [e4]; ring)
    filter_upwards [hz, ae_restrict_mem hU.measurableSet] with p hp hpU
    have := hp hpU
    simpa [sub_eq_zero] using this

end ESS

end
