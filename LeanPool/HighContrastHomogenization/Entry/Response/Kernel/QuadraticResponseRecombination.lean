/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.HeadCellDeficitInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm

/-!
# High-contrast homogenization: Entry.Response.Kernel.QuadraticResponseRecombination

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quadratic response, recombined over an almost-everywhere partition

The averaging identity for an exact finite cover is restated here for an almost-everywhere cover,
since the adapted grid's cells meet their parent only up to the Lebesgue-null grid seams. On a
domain carrying a pointwise elliptic coefficient, the quadratic part of the response functional
evaluated at a response maximizer against any competitor obtained by restricting a harmonic
function from a larger set equals twice the response deficit between them; this file recombines
that identity, first over a single partition and then over an almost-everywhere one, and evaluates
the scalar response `ResponseJ U p r a` of AK.HC (2.9) at the canonical coarse-block quadratic
expression on an aligned adapted cell and subcell.  The module serves the response-transfer
proposition `p.response.transfer`.
-/

section
/-!
## Averaging over an almost-everywhere finite partition

The partition identity holds for an exact cover
`U = ⋃ w ∈ Z, V w`.  The cells produced by the adapted grid are open, so they meet their
parent cell only up to the grid seams, a Lebesgue-null set; the exact cover is therefore
not available.  This file restates the identity for an almost-everywhere cover: `U` and the
disjoint union of the `V w` agree up to a null set, and the integral over `U` may be
replaced by the integral over that union.

The identity survives `volume (V w) = 0` for no `w ∈ Z`: `hvolw` with `hUpos` and
`Z.card > 0` gives `(volume (V w)).toReal = (volume U).toReal / |Z| > 0`, so every cell
has nonzero (and, in particular, non-infinite) volume and `volumeAverage` never divides by
zero.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **Averaging over an almost-everywhere finite equal-volume partition.**  If the
measurable sets `V w` (`w ∈ Z`) are pairwise disjoint and contained in `U`, if `U`
differs from their union by a null set, and if every cell has the same volume
`|V w| = |U| / |Z|` (stated in `toReal` form), then for any `g` integrable on `U`
the flat average over `Z` of the cell averages `⨍_{V w} g` equals the average
`⨍_U g`:

  `|Z|⁻¹ ∑_{w ∈ Z} ⨍_{V w} g = ⨍_U g`.

The null-set hypothesis is what the open adapted cells supply: they cover the parent
only up to the grid seams.  The integral over `U` is transferred to the union with
`setIntegral_congr_set`, whose two sides have the same restricted measure; the union is
then split with `integral_biUnion_finset` exactly as in the exact-cover statement. -/
theorem average_over_aePartition {iota : Type*} (Z : Finset iota) (V : iota → Set (Vec d))
    (U : Set (Vec d)) (g : Vec d → ℝ)
    (hmeas : ∀ w ∈ Z, MeasurableSet (V w))
    (hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → Disjoint (V w) (V w'))
    (hsub : ∀ w ∈ Z, V w ⊆ U)
    (hnull : volume (U \ ⋃ w ∈ Z, V w) = 0)
    (hvolw : ∀ w ∈ Z, ((Z.card : ℝ)) * (volume (V w)).toReal = (volume U).toReal)
    (hint : IntegrableOn g U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ⊤) (hZ : Z.Nonempty) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, volumeAverage (V w) g = volumeAverage U g := by
  classical
  have hUpos' : 0 < (volume U).toReal := hUpos
  have hUtop : volume U ≠ ⊤ := hUfin
  have hZpos : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hZ)
  have hdisj' : Set.Pairwise (↑Z : Set iota) (Function.onFun Disjoint V) := by
    intro a ha b hb hab
    exact hdisj a ha b hb hab
  have hVint : ∀ w ∈ Z, IntegrableOn g (V w) :=
    fun w hw => hint.mono_set (hsub w hw)
  have hsubU : (⋃ w ∈ Z, V w) ⊆ U := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨w, hw, hxw⟩
    exact hsub w hw hxw
  have hU_ae : U =ᵐ[volume] ⋃ w ∈ Z, V w := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hnull, by rw [Set.sdiff_eq_empty.mpr hsubU]; simp⟩
  have hInt : ∫ x in U, g x = ∑ w ∈ Z, ∫ x in V w, g x := by
    calc ∫ x in U, g x
        = ∫ x in ⋃ w ∈ Z, V w, g x := MeasureTheory.setIntegral_congr_set hU_ae
      _ = ∑ w ∈ Z, ∫ x in V w, g x :=
          MeasureTheory.integral_biUnion_finset Z hmeas hdisj' hVint
  have hcell : ∀ w ∈ Z, volumeAverage (V w) g =
      (Z.card : ℝ) * (volume U).toReal⁻¹ * ∫ x in V w, g x := by
    intro w hw
    have hvolw' : (volume (V w)).toReal = (volume U).toReal / (Z.card : ℝ) := by
      rw [eq_div_iff (ne_of_gt hZpos), mul_comm]
      exact hvolw w hw
    rw [volumeAverage, hvolw', div_eq_mul_inv, mul_inv, inv_inv]
    ring
  have hsum : ∑ w ∈ Z, volumeAverage (V w) g =
      (Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
    calc ∑ w ∈ Z, volumeAverage (V w) g
        = ∑ w ∈ Z, (Z.card : ℝ) * (volume U).toReal⁻¹ * ∫ x in V w, g x :=
          Finset.sum_congr rfl (fun w hw => hcell w hw)
      _ = (Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
          rw [Finset.mul_sum]
  have hcancel : (Z.card : ℝ)⁻¹ *
        ((Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x) =
      (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
    have hc0 : (Z.card : ℝ) ≠ 0 := ne_of_gt hZpos
    calc (Z.card : ℝ)⁻¹ *
          ((Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x)
        = ((Z.card : ℝ)⁻¹ * (Z.card : ℝ)) *
            ((volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x) := by ring
      _ = (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
            rw [inv_mul_cancel₀ hc0, one_mul]
  rw [volumeAverage, hInt, hsum]
  exact hcancel

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Quadratic response: the difference energy is twice the response deficit

On a domain `V` carrying a pointwise elliptic coefficient `a`, let `v` be a
response maximizer for the load `(p, q)` and let `uV` be any other admissible
competitor (the restriction of a harmonic function from a larger set `U ⊇ V`).
Writing `X = (∇w, a ∇w)` for the doubled state of a field `w`, the quadratic
part of the response functional is exact at a maximizer: the first variation
vanishes, so the difference energy of the two states is

  `⨍_V (X_{uV} − X_v) · A (X_{uV} − X_v) = 4 (J(V) − ⨍_V g_V(uV))`

with `A` the pointwise block of `a` and `g_V` the response integrand.  Because
the pointwise block energy is twice the `symmPart` variation energy
(`X · A X = 2 ∇w · symmPart(a) ∇w`), this is equivalently the statement below:
the variation energy of the difference equals twice the response deficit.

The deficit is measured against the *value of the competitor on `V`*, not
against the parent-domain supremum `J(U)`: the two differ in general, since the
average of the parent integrand over a proper subset need not equal its average
over `U`.  The identity is the single-domain engine behind the recent-cell
response estimate; the recombination over a partition of `U` is a separate
step.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **Quadratic response on one domain pair.**  Let `V ⊆ U` be open sets, `a` be
pointwise elliptic on `V`, `v` a response maximizer on `V` for the load
`(p, q)`, and `u` any `a`-harmonic function on `U`.  Then the `symmPart`
variation energy on `V` of the difference between the restricted parent `u` and
the maximizer `v` is twice the response deficit of the restricted parent:

  `⨍_V (∇u − ∇v) · symmPart(a) (∇u − ∇v) = 2 (J(V) − ⨍_V g_V(u))`.

Only the maximizer on `V` is used; the parent need not be a maximizer on `U`.
The four integrability side conditions are those required by the first- and
second-variation identities. -/
theorem difference_energy_eq_response_deficit {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hU : IsOpen U) (hV : IsOpen V) [IsFiniteMeasure (volumeMeasureOn V)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam V a)
    {p q : Vec d} {u : AHarmonicFunction a U} {v : AHarmonicFunction a V}
    (hmaxV : IsResponseMaximizer V p q a v)
    (huV_int : weakFluxIntegrable V a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : IntegrableOn (scalarResponseIntegrand V a p q v) V)
    (hlin : IntegrableOn (scalarFirstVariationIntegrand V a p q v
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy : IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V) :
    volumeAverage V (fun x => vecDot
        ((u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad x - v.toH1.grad x)
        (matVecMul (symmPart (a x))
          ((u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad x - v.toH1.grad x))) =
      2 * (ResponseJ V p q a - volumeAverage V (scalarResponseIntegrand V a p q
          (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))) := by
  set uV : AHarmonicFunction a V := u.restrictOfIsEllipticFieldOn hU hV hVU hEll
    with huVdef
  set w : AHarmonicFunction a V :=
    AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1) with hwdef
  have hwgrad : ∀ x, w.toH1.grad x = uV.toH1.grad x - v.toH1.grad x := by
    intro x
    rw [hwdef, AHarmonicFunction.grad_addSMulOfIntegrable]
    simp [sub_eq_add_neg]
  have hw_int : weakFluxIntegrable V a w := by
    intro φ
    have h1 : IntegrableOn (fun x => vecDot (matVecMul (a x) (uV.toH1.grad x))
        (φ.toH1Function.grad x)) V := huV_int φ
    have h2 : IntegrableOn (fun x => vecDot (matVecMul (a x) (v.toH1.grad x))
        (φ.toH1Function.grad x)) V := hv_int φ
    have heq : (fun x => vecDot (matVecMul (a x) (w.toH1.grad x))
          (φ.toH1Function.grad x)) =
        fun x => vecDot (matVecMul (a x) (uV.toH1.grad x)) (φ.toH1Function.grad x) -
          vecDot (matVecMul (a x) (v.toH1.grad x)) (φ.toH1Function.grad x) := by
      funext x
      rw [hwgrad x, sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
        vecDot_neg_left]
      ring
    rw [heq]
    exact h1.sub h2
  have hsecond := responseJ_second_variation_line_of_isResponseMaximizer
    V a p q v hmaxV w 1 hv_int hw_int hresp_v hlin henergy
  have hpert : scalarResponseIntegrand V a p q (scalarPerturbation v w 1 hv_int hw_int) =
      scalarResponseIntegrand V a p q uV := by
    funext x
    have hg : (scalarPerturbation v w 1 hv_int hw_int).toH1.grad x = uV.toH1.grad x := by
      rw [scalarPerturbation_grad]
      simp only [Pi.add_apply, one_smul]
      rw [hwgrad x]
      abel
    simp only [scalarResponseIntegrand]
    rw [hg]
  rw [hpert] at hsecond
  have hE : volumeAverage V (scalarVariationEnergyIntegrand a w) =
      2 * (ResponseJ V p q a - volumeAverage V (scalarResponseIntegrand V a p q uV)) := by
    have h' : volumeAverage V (scalarResponseIntegrand V a p q uV) =
        ResponseJ V p q a - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a w) := by
      simpa using hsecond
    linarith only [h']
  have hfun : scalarVariationEnergyIntegrand a w =
      fun x => vecDot (uV.toH1.grad x - v.toH1.grad x)
        (matVecMul (symmPart (a x)) (uV.toH1.grad x - v.toH1.grad x)) := by
    funext x
    simp only [scalarVariationEnergyIntegrand, hwgrad]
  rw [hfun] at hE
  rw [huVdef] at hE ⊢
  exact hE

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Quadratic response recombined over the cells

On a single child cell `V` of a parent `U`, the variation energy of the
difference between the parent field and the cell maximizer equals twice the
response deficit of the parent field on that cell
(`difference_energy_eq_response_deficit`).  The present file averages that
identity over the finitely many cells of a partition and uses
`average_over_aePartition` to turn the flat average of the per-cell parent
integrands into the parent average.  When the parent field is itself the
maximizer on `U`, `responseJ_eq_of_isResponseMaximizer` identifies that parent
average with `ResponseJ U p q a`, so the flat average of the cell difference
energies equals twice the difference between the flat average of the cell
responses and the parent response.

The per-cell average of the parent integrand depends on the cell, so the abstract
recombination below carries `gavg : iota → ℝ`, not a single constant.  A constant
`gavg` would be correct only when every cell has the same parent integrand,
which the partition step does not provide, and it would not typecheck against
`average_over_aePartition`, whose right-hand side is the parent average.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **Averaging a per-cell deficit identity over a finite index set.**  Suppose
the cells are indexed by the nonempty finite set `Z`, each cell carries the
deficit identity `Eng w = 2 (Jchild w − gavg w)` for its own parent average
`gavg w`, and the flat average of those parent averages is `Jparent`.  Then the
flat average of `Eng` is twice the difference between the flat average of
`Jchild` and `Jparent`.  The index set is required nonempty only so that the
inverse cardinality behaves; the statement is an identity in the sums. -/
theorem avg_difference_energy_eq_deficit {iota : Type*} (Z : Finset iota)
    (Eng Jchild gavg : iota → ℝ) (Jparent : ℝ)
    (hZ : Z.Nonempty)
    (hpair : ∀ w ∈ Z, Eng w = 2 * (Jchild w - gavg w))
    (hrecomb : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, gavg w = Jparent) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Eng w
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Jchild w - Jparent) := by
  have hEng : ∑ w ∈ Z, Eng w = 2 * (∑ w ∈ Z, Jchild w - ∑ w ∈ Z, gavg w) := by
    rw [Finset.sum_congr rfl (fun w hw => hpair w hw), ← Finset.mul_sum,
      Finset.sum_sub_distrib]
  have hcard : (Z.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hZ)
  have hrecomb' : Jparent * (Z.card : ℝ) = ∑ w ∈ Z, gavg w := by
    rw [← hrecomb, mul_right_comm, inv_mul_cancel₀ hcard, one_mul]
  have hP : Jparent = (∑ w ∈ Z, gavg w) * (Z.card : ℝ)⁻¹ := by
    calc Jparent = (Jparent * (Z.card : ℝ)) * (Z.card : ℝ)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hcard, mul_one]
      _ = (∑ w ∈ Z, gavg w) * (Z.card : ℝ)⁻¹ := by rw [hrecomb']
  rw [hEng, hP]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The recombined quadratic-response identity on an almost-everywhere partition

The recombined quadratic-response identity is stated over an exact finite cover
`U = ⋃ w ∈ Z, V w` with equal cell volumes.  The adapted
cells the response estimate uses are open, so they meet their parent cell only up to the grid
seams; the exact cover is not available at those carriers and the identity cannot be
instantiated there.  This file restates the two statements with the almost-everywhere
hypotheses of `average_over_aePartition`: the cells are contained in `U`, `U` differs from
their union by a null set, and the equal-volume condition is stated through `.toReal`.

The new hypotheses are implied by the old ones — `hcover` gives containment and a null
difference, and the equal-volume identity in `ℝ≥0∞` gives its `.toReal` form once `U` has
finite measure — so these statements are strictly stronger than the exact-cover originals.

The per-cell average of the parent integrand depends on the cell, so the abstract recombination
carries `gavg : iota → ℝ`; the right-hand side is the parent average.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **Averaging a per-cell deficit identity over an almost-everywhere finite equal-volume
partition.**  Suppose the measurable cells `V w` (`w ∈ Z`) are pairwise disjoint and contained
in `U`, that `U` differs from their union by a null set, and that each cell has the same volume
`|V w| = |U| / |Z|` stated in `.toReal` form.  If each cell carries the deficit identity
`Eng w = 2 (Jchild w − gavg w)` for its own parent average `gavg w`, and the flat average of
those parent averages is `Jparent`, then the flat average of `Eng` is twice the difference
between the flat average of `Jchild` and `Jparent`.  The exact equal-volume cover is replaced
here by the almost-everywhere cover `average_over_aePartition`. -/
theorem avg_difference_energy_eq_deficit_adapted_ae {iota : Type*}
    (Z : Finset iota) (V : iota → Set (Vec d)) (U : Set (Vec d))
    (g : Vec d → ℝ) (Eng Jchild : iota → ℝ)
    (hZ : Z.Nonempty)
    (hmeas : ∀ w ∈ Z, MeasurableSet (V w))
    (hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → Disjoint (V w) (V w'))
    (hsub : ∀ w ∈ Z, V w ⊆ U)
    (hnull : volume (U \ ⋃ w ∈ Z, V w) = 0)
    (hvolw : ∀ w ∈ Z, ((Z.card : ℝ)) * (volume (V w)).toReal = (volume U).toReal)
    (hint : IntegrableOn g U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ⊤)
    (hpair : ∀ w ∈ Z, Eng w = 2 * (Jchild w - volumeAverage (V w) g)) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Eng w
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Jchild w - volumeAverage U g) := by
  exact avg_difference_energy_eq_deficit Z Eng Jchild
    (fun w => volumeAverage (V w) g) (volumeAverage U g) hZ hpair
    (average_over_aePartition Z V U g hmeas hdisj hsub hnull hvolw hint hUpos hUfin hZ)

omit [NeZero d] in
/-- **The cell instance of the quadratic response recombination over an almost-everywhere
partition.**  The exact cover of the recombination is replaced here by the almost-everywhere
hypotheses: the cells `V w` (`w ∈ Z`) are contained in `U`,
`U` differs from their union by a null set, and the equal-volume condition is stated through
`.toReal`.  The result is the flat average of the cell difference energies in terms of the flat
average of the cell responses and the parent response:

  `|Z|⁻¹ ∑_w ⨍_{V w} (∇u − ∇v_w) · symmPart(a) (∇u − ∇v_w)
     = 2 (|Z|⁻¹ ∑_w J(V w) − J(U))`.

Because the difference energy is written with the parent gradient `∇u`, the gradients of the
restrictions of `u` agree with `∇u` definitionally and no separate rewriting hypothesis is
needed. -/
theorem avg_difference_energy_eq_responseJ_deficit_ae {iota : Type*}
    (Z : Finset iota) (V : iota → Set (Vec d)) (U : Set (Vec d))
    {a : CoeffField d} {lam Lam : ℝ} {p q : Vec d}
    (u : AHarmonicFunction a U) (v : (w : iota) → AHarmonicFunction a (V w))
    [hfin : ∀ w, IsFiniteMeasure (volumeMeasureOn (V w))]
    (hZ : Z.Nonempty)
    (hU : IsOpen U) (hVopen : ∀ w ∈ Z, IsOpen (V w))
    (hVU : ∀ w ∈ Z, V w ⊆ U)
    (hsub : ∀ w ∈ Z, V w ⊆ U)
    (hnull : volume (U \ ⋃ w ∈ Z, V w) = 0)
    (hvolw : ∀ w ∈ Z, ((Z.card : ℝ)) * (volume (V w)).toReal = (volume U).toReal)
    (hEll : ∀ w ∈ Z, IsEllipticFieldOn lam Lam (V w) a)
    (hmaxV : ∀ w ∈ Z, IsResponseMaximizer (V w) p q a (v w))
    (huV_int : ∀ w (hw : w ∈ Z), weakFluxIntegrable (V w) a
      (u.restrictOfIsEllipticFieldOn hU (hVopen w hw) (hVU w hw) (hEll w hw)))
    (hv_int : ∀ w ∈ Z, weakFluxIntegrable (V w) a (v w))
    (hresp_v : ∀ w ∈ Z, IntegrableOn (scalarResponseIntegrand (V w) a p q (v w)) (V w))
    (hlin : ∀ w (hw : w ∈ Z), IntegrableOn (scalarFirstVariationIntegrand (V w) a p q (v w)
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU (hVopen w hw) (hVU w hw) (hEll w hw)) (v w)
        (huV_int w hw) (hv_int w hw) (-1))) (V w))
    (henergy : ∀ w (hw : w ∈ Z), IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU (hVopen w hw) (hVU w hw) (hEll w hw)) (v w)
        (huV_int w hw) (hv_int w hw) (-1))) (V w))
    (hmeas : ∀ w ∈ Z, MeasurableSet (V w))
    (hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → Disjoint (V w) (V w'))
    (hint : IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ⊤)
    (hmaxU : IsResponseMaximizer U p q a u) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        volumeAverage (V w) (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x)))
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, ResponseJ (V w) p q a - ResponseJ U p q a) := by
  have hpair : ∀ w ∈ Z,
      volumeAverage (V w) (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x)))
      = 2 * (ResponseJ (V w) p q a
        - volumeAverage (V w) (scalarResponseIntegrand U a p q u)) := by
    intro w hw
    exact difference_energy_eq_response_deficit (hVU w hw) hU (hVopen w hw)
      (hEll w hw) (hmaxV w hw) (huV_int w hw) (hv_int w hw) (hresp_v w hw)
      (hlin w hw) (henergy w hw)
  have hmain := avg_difference_energy_eq_deficit_adapted_ae Z V U
    (scalarResponseIntegrand U a p q u)
    (fun w => volumeAverage (V w) (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x))))
    (fun w => ResponseJ (V w) p q a)
    hZ hmeas hdisj hsub hnull hvolw hint hUpos hUfin hpair
  rw [hmain, ← responseJ_eq_of_isResponseMaximizer U p q a hmaxU]

omit [NeZero d] in
/-- **The recombined quadratic-response identity at the aligned adapted cells.**  For an
invertible grid `q`, generation `t` and depth `n`, the partition geometry of
`avg_difference_energy_eq_responseJ_deficit_ae` is supplied by the tree's cell lemmas: the
depth-`n` subcells of `HighContrast.adaptedCell q t` are open hence measurable, pairwise disjoint,
contained in the parent, omit only the null grid seams, and have equal volume, and the parent
cell has positive finite volume.  The elliptic, maximizer and integrability data are not
available from `IsUnit q` alone and remain explicit hypotheses. -/
theorem avg_difference_energy_eq_responseJ_deficit_adaptedCell_ae
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    {a : CoeffField d} {lam Lam : ℝ} {p r : Vec d}
    (u : AHarmonicFunction a (HighContrast.adaptedCell q t))
    (v : (w : Fin d → ℤ) → AHarmonicFunction a (adaptedCellAtCenter q (t - (n : ℤ)) w))
    [hfin : ∀ w, IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w))]
    (hEll : ∀ w ∈ triadicIndexBox d n,
      IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) a)
    (hmaxV : ∀ w ∈ triadicIndexBox d n,
      IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r a (v w))
    (huV_int : ∀ w (hw : w ∈ triadicIndexBox d n),
      weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) a
        (u.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hq t)
          (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
          (adaptedCellAtCenter_subset_adaptedCell q t n hw) (hEll w hw)))
    (hv_int : ∀ w ∈ triadicIndexBox d n,
      weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) a (v w))
    (hresp_v : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (scalarResponseIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) a p r (v w))
        (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hlin : ∀ w (hw : w ∈ triadicIndexBox d n),
      IntegrableOn (scalarFirstVariationIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) a p r (v w)
        (AHarmonicFunction.addSMulOfIntegrable
          (u.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hq t)
            (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
            (adaptedCellAtCenter_subset_adaptedCell q t n hw) (hEll w hw)) (v w)
          (huV_int w hw) (hv_int w hw) (-1)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (henergy : ∀ w (hw : w ∈ triadicIndexBox d n),
      IntegrableOn (scalarVariationEnergyIntegrand a
        (AHarmonicFunction.addSMulOfIntegrable
          (u.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hq t)
            (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
            (adaptedCellAtCenter_subset_adaptedCell q t n hw) (hEll w hw)) (v w)
          (huV_int w hw) (hv_int w hw) (-1)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hint : IntegrableOn (scalarResponseIntegrand (HighContrast.adaptedCell q t) a p r u)
      (HighContrast.adaptedCell q t))
    (hmaxU : IsResponseMaximizer (HighContrast.adaptedCell q t) p r a u) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x)))
      = 2 * (((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r a
        - ResponseJ (HighContrast.adaptedCell q t) p r a) := by
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hZne : (triadicIndexBox d n).Nonempty := by
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  exact avg_difference_energy_eq_responseJ_deficit_ae
    (triadicIndexBox d n) (fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
    (HighContrast.adaptedCell q t) u v hZne
    (isOpen_adaptedCell_of_isUnit hq t)
    (fun w _ => isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (adaptedCell_diff_biUnion_null q hq t n)
    (fun w _ => volume_adaptedCellAtCenter_card_eq q hq t n w)
    hEll hmaxV huV_int hv_int hresp_v hlin henergy
    (fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet)
    (fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww')
    hint hUpos hUfin hmaxU

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The response functional as a coarse-block quadratic form on an aligned subcell

The scalar response `ResponseJ U p r a` of AK.HC (2.9) is evaluated at the canonical
coarse-block quadratic expression `p·(A(-p, r))/2 - p·r` whenever `U` is an open bounded
convex domain carrying an elliptic representative of `a`, by
`responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain`
(`HCPoly/Entry/CG/Proofs/AdaptedDomainRecovery.lean`).  The recentred coefficients `a_- = a - g` and
`a_+ = aᵀ + g` carry such a representative on the parent adapted cell `⋄_t^q` and, via
`exists_elliptic_representative_respCoeffMinusAt` / `…PlusAt`, on every aligned triadic
subcell `adaptedCellAtCenter q k w`.

This module exposes that evaluation publicly, for the parent cell and for each aligned
subcell, so that the cell-average estimate of AK.HC (2.15) can be consumed downstream.  Nothing
new is proved here: each statement is the general bounded-convex-domain formula transported
along the a.e. equality of the elliptic representative.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The aligned subcell -/

/-- **AK.HC (2.15) on an aligned subcell, minus sign.**  For the recentred coefficient
`a_- = a - g`, the response functional on the aligned adapted subcell `adaptedCellAtCenter q k w`
equals the coarse-block quadratic expression `(-p, r)·(A_{kw}(-p, r))/2 - p·r`, where
`A_{kw}` is the coarse block matrix of `a_-` on that subcell. -/
theorem responseJ_adaptedCellAtCenter_respCoeffMinus (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (adaptedCellAtCenter q k w) p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffMinus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt q hq k w F a
  rw [HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae]
  exact HCPolySupport.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w) hEll
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) p r

/-- **AK.HC (2.15) on an aligned subcell, plus sign.**  The adjoint twin for the transposed
recentred coefficient `a_+ = aᵀ + g`. -/
theorem responseJ_adaptedCellAtCenter_respCoeffPlus (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (adaptedCellAtCenter q k w) p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffPlus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt q hq k w F a
  rw [HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae]
  exact HCPolySupport.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w) hEll
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) p r

/-! ## The parent adapted cell -/

/-- **AK.HC (2.15) on the parent adapted cell, minus sign.**  The public counterpart of the
parent-cell evaluation, for the recentred coefficient `a_- = a - g`. -/
theorem responseJ_adaptedCell_respCoeffMinus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (HighContrast.adaptedCell q t) p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  rw [HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae]
  exact HCPolySupport.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (adaptedCell_isOpenBoundedConvexDomain q hq t) hEll hvol p r

/-- **AK.HC (2.15) on the parent adapted cell, plus sign.**  The adjoint twin for the
transposed recentred coefficient `a_+ = aᵀ + g`. -/
theorem responseJ_adaptedCell_respCoeffPlus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (HighContrast.adaptedCell q t) p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  rw [HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae]
  exact HCPolySupport.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (adaptedCell_isOpenBoundedConvexDomain q hq t) hEll hvol p r

end

end HCPolySupport.HighContrast.Multiscale
end
