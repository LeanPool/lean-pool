/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLerayProjection
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier

/-!
# The Leray projection acting on triples of functions

`prop:lps-smoothing`: the projection of `lps_leray_exists`, fixed once and for all, acting on a
vector field given by three square-integrable functions on `ℝ³`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Leray projection of `L²(ℝ³;ℝ³)`, a fixed choice from `lps_leray_exists`
(`prop:lps-smoothing`). -/
@[expose] def lpsLerayP : LpsL2Field →L[ℝ] LpsL2Field := Classical.choose lps_leray_exists

theorem lpsLerayP_norm_le (g : LpsL2Field) : ‖lpsLerayP g‖ ≤ ‖g‖ :=
  (Classical.choose_spec lps_leray_exists).1 g

theorem lpsLerayP_eq_self {g : LpsL2Field}
    (hg : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∑ i, ∫ x, g i x * spatialDeriv φ i x = 0) : lpsLerayP g = g :=
  (Classical.choose_spec lps_leray_exists).2.1 g hg

theorem lpsLerayP_mem (g : LpsL2Field) (φ : Vec3 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : ∑ i, ∫ x, lpsLerayP g i x * spatialDeriv φ i x = 0 :=
  (Classical.choose_spec lps_leray_exists).2.2.1 g φ hφ hφc

theorem lpsLerayP_gradient {q : Vec3 → ℝ} {G : LpsL2Field} (hq : MemLp q 2 volume)
    (hG : ∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i q (⇑(G i))) : lpsLerayP G = 0 :=
  (Classical.choose_spec lps_leray_exists).2.2.2.1 q G hq hG

theorem lpsLerayP_weakPartial {g G : LpsL2Field} (k : Fin 3)
    (h : ∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) k (⇑(g i)) (⇑(G i))) (i : Fin 3) :
    HasWeakPartialDerivOn (Set.univ : Set Vec3) k (⇑(lpsLerayP g i)) (⇑(lpsLerayP G i)) :=
  (Classical.choose_spec lps_leray_exists).2.2.2.2.1 g G k h i

/-- The field of three square-integrable functions as an element of `L²(ℝ³;ℝ³)`. -/
@[expose] def lpsFieldOf (g : Fin 3 → Vec3 → ℝ) (hg : ∀ j, MemLp (g j) 2 volume) : LpsL2Field :=
  WithLp.toLp 2 fun j => (hg j).toLp (g j)

/-- The Leray projection of a vector field given by three square-integrable functions, as
functions. -/
@[expose] def lpsLerayApply (g : Fin 3 → Vec3 → ℝ) (hg : ∀ j, MemLp (g j) 2 volume) (i : Fin 3) :
    Vec3 → ℝ :=
  ⇑(lpsLerayP (lpsFieldOf g hg) i)

/-- Weak partial derivatives are insensitive to almost-everywhere changes of the function and of
its derivative (`prop:lps-smoothing`). -/
theorem lps_hasWeakPartialDerivOn_congr {U : Set Vec3} {i : Fin 3} {f f' df df' : Vec3 → ℝ}
    (hf : HasWeakPartialDerivOn U i f df) (hff' : f =ᵐ[volume.restrict U] f')
    (hdd : df =ᵐ[volume.restrict U] df') : HasWeakPartialDerivOn U i f' df' := by
  intro φ hφ hφc hφU
  have hweak := hf φ hφ hφc hφU
  calc (∫ x in U, f' x * spatialDeriv φ i x)
      = ∫ x in U, f x * spatialDeriv φ i x := by
        refine integral_congr_ae ?_
        filter_upwards [hff'] with x hx
        rw [hx]
    _ = -(∫ x in U, df x * φ x) := by simpa [spatialDeriv] using hweak
    _ = -(∫ x in U, df' x * φ x) := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hdd] with x hx
        rw [hx]

theorem lpsLerayApply_eq {g : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume) (i : Fin 3) :
    lpsLerayApply g hg i = ⇑(lpsLerayP (lpsFieldOf g hg) i) :=
  rfl

theorem lpsLerayApply_memLp {g : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume) (i : Fin 3) :
    MemLp (lpsLerayApply g hg i) 2 volume := by
  rw [lpsLerayApply_eq hg]
  exact Lp.memLp _

/-- The projection only depends on the almost-everywhere class of the components. -/
theorem lpsLerayApply_congr_ae {g g' : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume)
    (hg' : ∀ j, MemLp (g' j) 2 volume)
    (hgg' : ∀ j, g j =ᵐ[volume] g' j) (i : Fin 3) :
    lpsLerayApply g hg i =ᵐ[volume] lpsLerayApply g' hg' i := by
  have : lpsFieldOf g hg = lpsFieldOf g' hg' := by
    unfold lpsFieldOf
    congr 1
    funext j
    exact MemLp.toLp_congr _ _ (hgg' j)
  rw [lpsLerayApply_eq hg, lpsLerayApply_eq hg', this]

/-- Square integral of an `L²` class equals its squared norm. -/
theorem lpsLp_norm_sq_eq_integral (f : Lp ℝ 2 (volume : Measure Vec3)) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 := by
  rw [Lp.norm_def, ← vl_integral_sq_eq (Lp.memLp f)]

/-- The projection is a contraction on square integrals of the components. -/
theorem lpsLerayApply_normSq_le {g : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume) :
    ∑ i, ∫ x, (lpsLerayApply g hg i x) ^ 2 ≤ ∑ i, ∫ x, (g i x) ^ 2 := by
  have h := lpsLerayP_norm_le (lpsFieldOf g hg)
  have hsq : ‖lpsLerayP (lpsFieldOf g hg)‖ ^ 2 ≤ ‖lpsFieldOf g hg‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at hsq
  have e1 : ∀ i, ‖lpsLerayP (lpsFieldOf g hg) i‖ ^ 2 = ∫ x, (lpsLerayApply g hg i x) ^ 2 := by
    intro i
    rw [lpsLerayApply_eq hg, lpsLp_norm_sq_eq_integral]
  have e2 : ∀ i, ‖lpsFieldOf g hg i‖ ^ 2 = ∫ x, (g i x) ^ 2 := by
    intro i
    rw [lpsLp_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [(hg i).coeFn_toLp] with x hx
    change (((hg i).toLp (g i)) x) ^ 2 = _
    rw [hx]
  simpa only [e1, e2] using hsq

/-- The projection fixes weakly divergence-free fields. -/
theorem lpsLerayApply_eq_self {g : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume)
    (hdiv : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∑ i, ∫ x, g i x * spatialDeriv φ i x = 0) (i : Fin 3) :
    lpsLerayApply g hg i =ᵐ[volume] g i := by
  rw [lpsLerayApply_eq hg]
  have h : lpsLerayP (lpsFieldOf g hg) = lpsFieldOf g hg := by
    refine lpsLerayP_eq_self fun φ hφ hφc => ?_
    have := hdiv φ hφ hφc
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
    filter_upwards [(hg j).coeFn_toLp] with x hx
    change (((hg j).toLp (g j)) x) * _ = _
    rw [hx]
  rw [h]
  exact (hg i).coeFn_toLp

/-- The projection annihilates gradients of `H¹` functions. -/
theorem lpsLerayApply_gradient {q : Vec3 → ℝ} {G : Fin 3 → Vec3 → ℝ}
    (hG : ∀ j, MemLp (G j) 2 volume) (hq : MemLp q 2 volume)
    (hw : ∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i q (G i)) (i : Fin 3) :
    lpsLerayApply G hG i =ᵐ[volume] 0 := by
  rw [lpsLerayApply_eq hG]
  have h : lpsLerayP (lpsFieldOf G hG) = 0 := by
    refine lpsLerayP_gradient hq fun j => ?_
    refine lps_hasWeakPartialDerivOn_congr (hw j) Filter.EventuallyEq.rfl ?_
    exact ae_restrict_of_ae (hG j).coeFn_toLp.symm
  rw [h]
  exact Filter.Eventually.of_forall fun x => by simp

/-- The projection commutes with weak spatial derivatives. -/
theorem lpsLerayApply_weakPartial {g G : Fin 3 → Vec3 → ℝ} (hg : ∀ j, MemLp (g j) 2 volume)
    (hG : ∀ j, MemLp (G j) 2 volume) (k : Fin 3)
    (h : ∀ j, HasWeakPartialDerivOn (Set.univ : Set Vec3) k (g j) (G j)) (i : Fin 3) :
    HasWeakPartialDerivOn (Set.univ : Set Vec3) k (lpsLerayApply g hg i) (lpsLerayApply G hG i)
      := by
  rw [lpsLerayApply_eq hg, lpsLerayApply_eq hG]
  refine lpsLerayP_weakPartial k (fun j => ?_) i
  refine lps_hasWeakPartialDerivOn_congr (h j) ?_ ?_
  · exact ae_restrict_of_ae (hg j).coeFn_toLp.symm
  · exact ae_restrict_of_ae (hG j).coeFn_toLp.symm

end ESS
