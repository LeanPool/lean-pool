/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Surface.CongruenceFamily
public import LeanPool.CCDN.Surface.CongruencePrimeWindow
public import LeanPool.CCDN.Surface.CurveComponents
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Surface.CurveCrossing
import LeanPool.CCDN.Surface.ResidueSubsetBoundary
import LeanPool.CCDN.Surface.SmoothPrimeWindow

/-! A nonsingular point on a large-degree initial curve must cross a
proper auxiliary section along a one-prime deletion edge. This constructs
the residual cover from smooth reductions and auxiliaries. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The quantity `1 + log B + (log 4 + 4) c L`, with `c` the constant `scalingPrimeRatio`,
which bounds `1 + log B + ∑ p ∈ R, log p` for every set `R` of primes in the prime window of
logarithmic size `L`. -/
def surfaceResidueLogBudget (B L : ℝ) : ℝ :=
  1 + Real.log B + (Real.log 4 + 4) * scalingPrimeRatio * L

/-- The parameters of the residue cover of the surface `f = 0` in the box of radius `B ≥ 1`:
the coefficients of `f` are bounded by `H ≥ 1`; the logarithmic prime window `L ≥ 1` dominates
`4 log(d + 1) + log H + d log B`, which bounds the logarithm of a partial derivative of `f` at
a point of the box, where `d` is the degree of `f`; and the residue-modulus cutoff `X`
satisfies `1 < X`, `B^(1/√d) ≤ X` and `X ≤ e^L`. -/
structure IsSurfaceResidueWindow (f : MvPolynomial (Fin 3) ℤ) (B H L X : ℝ) : Prop where
  /-- The box radius is at least one. -/
  one_le_radius : 1 ≤ B
  /-- The height bound is at least one. -/
  one_le_height : 1 ≤ H
  /-- The logarithmic size of the prime window is at least one. -/
  one_le_window : 1 ≤ L
  /-- The coefficients of `f` are bounded by `H` in absolute value. -/
  coeff_le : CoefficientHeightLE f H
  /-- The window dominates the logarithmic size of a partial derivative of `f` on the
  box. -/
  log_le_window : 4 * Real.log ((f.totalDegree : ℝ) + 1) +
    Real.log H + f.totalDegree * Real.log B ≤ L
  /-- The modulus cutoff exceeds one. -/
  one_lt_cutoff : 1 < X
  /-- The modulus cutoff is at least `B^(1/√d)`. -/
  root_le_cutoff : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X
  /-- The modulus cutoff is at most `exp L`. -/
  cutoff_le_exp : X ≤ Real.exp L

/-- For a finite set `P` of primes, the exponential of `∑ p ∈ P, log p` is `∏ p ∈ P, p`. -/
lemma exp_sum_log_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, Real.log p) = ∏ p ∈ P, (p : ℝ) := by
  rw [Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  exact Real.exp_log (by exact_mod_cast (hP p hp).pos)

private lemma SurfaceCongruenceFamily.terminal_degree_le
    {f : MvPolynomial (Fin 3) ℤ} {B A L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hB : 1 ≤ B) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (P : Finset ℕ) (hPW : P ⊆ congruencePrimeWindow L)
    (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P)
    (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hprod : X ≤ ∏ p ∈ P, (p : ℝ)) :
    ((F.auxiliary P hP r).totalDegree : ℝ) ≤ 2 * A * surfaceResidueLogBudget B L := by
  have hQ : 0 ≤ ∑ p ∈ P, Real.log p := sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hlogB := Real.log_nonneg hB
  have hlog : (∑ p ∈ P, Real.log p) ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L :=
    (sum_le_sum_of_subset_of_nonneg hPW (fun p _ _ => Real.log_natCast_nonneg p)).trans
      (congruencePrimeWindow_log_upper hL)
  have hden : 0 < ∏ p ∈ P, (p : ℝ) := prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  have hratio : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) ≤ 1 := by
    rw [exp_sum_log_primes P hP]
    exact (div_le_one hden).mpr (hX.trans hprod)
  have hT : 0 ≤ surfaceResidueLogBudget B L := by
    unfold surfaceResidueLogBudget
    have hlogB := Real.log_nonneg hB
    linarith
  have hd := F.degree_le P hP r
  calc
    _ ≤ A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
        Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) := hd
    _ ≤ A * 2 * surfaceResidueLogBudget B L := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hA
      · dsimp only [surfaceResidueLogBudget]
        linarith
      · positivity
      · positivity
    _ = _ := by ring

private lemma surface_prime_curve_degree_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (I : Ideal (CoordinatePolynomial 3)) {d : ℕ} (hI : IsSurfaceCurve f I d) (hgI : g ∈ I) :
    d ≤ f.totalDegree * g.totalDegree := by
  have hh := surface_prime_curve_degree_sum_le f g hf hfg {I} (fun _ => d)
    (fun P hP => by
      have he : P = I := mem_singleton.mp hP
      subst P
      exact ⟨hI, hgI⟩)
  simpa only [sum_singleton] using hh

/-- A one-prime deletion edge `R.erase p ⊂ R` of the congruence family `F`, at the smooth
residues `r`, crossing the curve `I` near the point `x`: the primes of `R` lie in the window of
log-size `L`, the modulus of `R` is less than `c L X` and that of `R.erase p` is less than `X`
(where `c` is `scalingPrimeRatio`), the parent auxiliary lies in `I`, the child auxiliary does
not, and the child vanishes at `x`. -/
structure IsSurfaceResidueEdge {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (I : Ideal (CoordinatePolynomial 3)) (L X : ℝ)
    (x : IntPoint 3) (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) : Prop where
  /-- The primes of `R` lie in the prime window of logarithmic size `L`. -/
  subset_window : R ⊆ congruencePrimeWindow L
  /-- The product of the primes of `R` is less than `c L X`, with `c` the constant
  `scalingPrimeRatio`. -/
  prod_lt : (∏ q ∈ R, (q : ℝ)) < scalingPrimeRatio * L * X
  /-- The product of the primes of `R.erase p` is less than `X`. -/
  erase_prod_lt : (∏ q ∈ R.erase p, (q : ℝ)) < X
  /-- The auxiliary attached to `R.erase p`, over `ℚ`, lies in the ideal `I` of the curve. -/
  parent_mem : map (Int.castRingHom ℚ)
    (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
      (r.restrict (erase_subset p R))) ∈ I
  /-- The auxiliary attached to `R`, over `ℚ`, does not lie in the ideal `I`. -/
  child_not_mem : map (Int.castRingHom ℚ) (F.auxiliary R hR r) ∉ I
  /-- The auxiliary attached to `R` vanishes at `x`. -/
  child_vanishes : eval x (F.auxiliary R hR r) = 0

/-- A point on an initial prime curve above the terminal degree cutoff
lies in a proper section across a bounded-modulus residue edge. -/
theorem surface_residue_boundary_of_large_curve
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    {A B H L X : ℝ} (hA : 0 ≤ A) (hW : IsSurfaceResidueWindow f B H L X)
    (F : SurfaceCongruenceFamily f B A)
    (I : Ideal (CoordinatePolynomial 3)) {d : ℕ}
    (hI : IsSurfaceCurve (map (Int.castRingHom ℚ) f) I d)
    (hinitI : map (Int.castRingHom ℚ) F.initial ∈ I)
    (hlarge : 2 * f.totalDegree * A * surfaceResidueLogBudget B L < d)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ R : Finset ℕ, ∃ hR : ∀ p ∈ R, p.Prime,
      ∃ p ∈ R, ∃ r : SmoothAffineResidueFamily f R, IsSurfaceResidueEdge F I L X x R hR p r := by
  classical
  have hL := hW.one_le_window
  obtain ⟨P, hPW, hPprod, hPsmooth⟩ := exists_smooth_prime_window_subset f hW.one_le_height
    hW.one_le_radius hL hW.coeff_le (by norm_num; exact hW.log_le_window) x hx hsmooth
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime :=
    ((mem_congruencePrimeWindow hL).mp (hPW hp)).1
  obtain ⟨R₀, hR₀P, _, hR₀prod, hR₀proper, hR₀upper⟩ :=
    exists_minimal_product_subset P hW.one_lt_cutoff
      (fun p hp => by exact_mod_cast (hPprime p hp).pos)
      (fun p hp => ((mem_congruencePrimeWindow hL).mp (hPW hp)).2.2)
      (hW.cutoff_le_exp.trans hPprod)
  have hR₀W : R₀ ⊆ congruencePrimeWindow L := hR₀P.trans hPW
  have hR₀prime (q : ℕ) (hq : q ∈ R₀) : q.Prime := hPprime q (hR₀P hq)
  have hR₀smooth (q : ℕ) (hq : q ∈ R₀) := hPsmooth q (hR₀P hq)
  let aux (T : Finset ℕ) : MvPolynomial (Fin 3) ℤ :=
    if hT : T ⊆ R₀ then F.auxiliary T (fun q hq => hR₀prime q (hT hq))
      (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) else 1
  have haux (T : Finset ℕ) (hT : T ⊆ R₀) :
      aux T = F.auxiliary T (fun q hq => hR₀prime q (hT hq))
        (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) := by
    simp only [aux, dite_eq_left hT]
  have hterminal : map (Int.castRingHom ℚ) (aux R₀) ∉ I := by
    intro hmem
    rw [haux R₀ (Subset.refl _)] at hmem
    have hdeg := F.terminal_degree_le hW.one_le_radius hA hL R₀ hR₀W hR₀prime
      (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth) hW.root_le_cutoff hR₀prod
    have hcurve := surface_prime_curve_degree_le (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (F.auxiliary R₀ hR₀prime
        (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth))) hir (F.proper _ _ _)
      I hI hmem
    rw [rational_map_totalDegree, rational_map_totalDegree] at hcurve
    have hcurveR : (d : ℝ) ≤ (f.totalDegree : ℝ) *
        (F.auxiliary R₀ hR₀prime
          (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth)).totalDegree := by exact_mod_cast hcurve
    have hh := mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg (α := ℝ) f.totalDegree)
    nlinarith
  have hempty : ¬ (map (Int.castRingHom ℚ) (aux ∅) ∉ I) := by
    rw [haux ∅ (empty_subset _), F.initial_eq]
    exact not_not.mpr hinitI
  obtain ⟨R, hRR₀, p, hp, hchild, hparent⟩ := exists_subset_erase_boundary R₀
    (fun T => map (Int.castRingHom ℚ) (aux T) ∉ I) hempty hterminal
  have hRprime (q : ℕ) (hq : q ∈ R) : q.Prime := hR₀prime q (hRR₀ hq)
  have hRsmooth (q : ℕ) (hq : q ∈ R) := hR₀smooth q (hRR₀ hq)
  let r := smoothResidueFamilyOfPoint x hxf R hRsmooth
  have hparentSub : R.erase p ⊆ R₀ := (erase_subset p R).trans hRR₀
  have hparentEq : aux (R.erase p) =
      F.auxiliary (R.erase p) (fun q hq => hRprime q (mem_of_mem_erase hq))
        (r.restrict (erase_subset p R)) := by
    rw [haux (R.erase p) hparentSub]
    rfl
  have hchildEq : aux R = F.auxiliary R hRprime r := haux R hRR₀
  refine ⟨R, hRprime, p, hp, r, hRR₀.trans hR₀W, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : (∏ q ∈ R, (q : ℝ)) ≤ ∏ q ∈ R₀, (q : ℝ) :=
      prod_le_prod_of_subset_of_one_le₀ hRR₀ (fun _ _ => Nat.cast_nonneg _)
        (fun q hq _ => by exact_mod_cast (hR₀prime q hq).one_le)
    exact hm.trans_lt hR₀upper
  · exact hR₀proper _ ((erase_ssubset hp).trans_le hRR₀)
  · rw [← hparentEq]
    exact not_not.mp hparent
  · rwa [← hchildEq]
  · exact F.point_vanishes x hx hxf R hRprime hRsmooth

end
end CCDN
