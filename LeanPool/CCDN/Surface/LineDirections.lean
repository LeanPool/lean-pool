/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.AffineLineLeading
public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import LeanPool.CCDN.Plane.IntegralAffineLine
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Surface.TopFormIrreducibility

/-! Directions of rational affine lines on a surface. Lines with two
bounded integer points have a bounded projective direction and a spacing
bound expressed using its representative-independent projective height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating the restriction `affineLinePolynomial a v f` of `f` to the line through `a` with
direction `v` at `t` gives the value of `f` at `a + t • v`. -/
lemma eval_affineLinePolynomial {K σ : Type*} [Field K]
    (a v : σ → K) (f : MvPolynomial σ K) (t : K) :
    (affineLinePolynomial a v f).eval t = eval (a + t • v) f := by
  have he : (Polynomial.evalRingHom t).comp (affineLinePolynomial a v) =
      eval (a + t • v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [affineLinePolynomial]
    · intro i
      simp [affineLinePolynomial]
      ring
  exact RingHom.congr_fun he f

private theorem affineLinePolynomial_eq_zero_of_contained {n : ℕ}
    (a v : RatPoint n) (f : CoordinatePolynomial n)
    (hline : rationalAffineLine a v ⊆ zeroLocus f) :
    affineLinePolynomial a v f = 0 := by
  apply Polynomial.zero_of_eval_zero
  intro t
  rw [eval_affineLinePolynomial]
  exact hline ⟨t, rfl⟩

private theorem rationalAffineLine_direction_top_zero {n : ℕ}
    (a v : RatPoint n) (f : MvPolynomial (Fin n) ℤ)
    (hline : rationalAffineLine a v ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) :
    eval v (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) = 0 := by
  have hpoly := affineLinePolynomial_eq_zero_of_contained a v _ hline
  have hdegree : (map (Int.castRingHom ℚ) f).totalDegree ≤ f.totalDegree := totalDegree_map_le _ _
  have hc := affineLinePolynomial_top_coefficient a v (map (Int.castRingHom ℚ) f)
    f.totalDegree hdegree
  rw [hpoly, Polynomial.coeff_zero, ← map_homogeneousComponent] at hc
  exact hc.symm

private lemma rationalAffineLine_eq_projective_rep {n : ℕ}
    (a v : RatPoint (n + 1)) (hv : v ≠ 0) (p : ProjectivePoint n)
    (hp : Projectivization.mk ℚ v hv = p) :
    rationalAffineLine a v = rationalAffineLine a p.rep := by
  have he : Projectivization.mk ℚ v hv =
      Projectivization.mk ℚ p.rep p.rep_nonzero := hp.trans p.mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ v p.rep hv p.rep_nonzero).mp he
  have heq : v = (c : ℚ) • p.rep := hc.symm
  rw [heq]
  exact rationalAffineLine_smul_direction a p.rep c.ne_zero

/-- A line with more than one bounded integer point has a projective
direction on the leading form. Its integer point count is bounded using the
height of that projective point, independently of all chosen representatives. -/
theorem surface_line_projective_direction {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (L : Set (RatPoint (n + 1)))
    (hL : ∃ a v, L = rationalAffineLine a v)
    (hLf : L ⊆ zeroLocus (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 0 ≤ B) (hcount : 1 < count L B) :
    ∃ p : ProjectivePoint n,
      p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      0 < p.mulHeight ∧ p.mulHeight ≤ 2 * B ∧
      (∃ a, L = rationalAffineLine a p.rep) ∧
      (count L B : ℝ) ≤ 4 * B / p.mulHeight := by
  obtain ⟨a, v, rfl⟩ := hL
  obtain ⟨z, w, hw, hprim, _, hheight, hline, hcnt⟩ :=
    rationalAffineLine_integer_rep_and_count a v hB hcount
  let p := Projectivization.mk ℚ (rationalPoint w) (rationalPoint_ne_zero hw)
  have hpheight : p.mulHeight = (integerDirectionHeight w : ℝ) :=
    projective_direction_height w hw hprim
  have hp0 : 0 < p.mulHeight := by
    rw [hpheight]
    exact_mod_cast integerDirectionHeight_pos hw
  have hzero := rationalAffineLine_direction_top_zero
    (rationalPoint z) (rationalPoint w) f (by rwa [← hline])
  refine ⟨p, ?_, hp0, hpheight ▸ hheight, ?_, ?_⟩
  · exact (mem_projectiveZeroLocus_mk ((homogeneousComponent_isHomogeneous _ _).map _)
      (rationalPoint w) (rationalPoint_ne_zero hw)).mpr hzero
  · exact ⟨rationalPoint z, hline.trans
      (rationalAffineLine_eq_projective_rep _ _ (rationalPoint_ne_zero hw) p rfl)⟩
  · rw [← hpheight] at hcnt
    have htwo : 1 ≤ 2 * B / p.mulHeight :=
      (le_div_iff₀ hp0).mpr (by simpa only [one_mul, hpheight] using hheight)
    calc
      _ ≤ 1 + 2 * B / p.mulHeight := hcnt
      _ ≤ 2 * B / p.mulHeight + 2 * B / p.mulHeight := by linarith
      _ = _ := by ring

end
end CCDN
