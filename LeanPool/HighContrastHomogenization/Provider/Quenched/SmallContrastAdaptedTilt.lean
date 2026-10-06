/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHomogenizedComparison
public import LeanPool.HighContrastHomogenization.Provider.Window.ScaledStandardToAdapted
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCentring

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAdaptedTilt

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted-to-Euclidean tilt comparison

This file formalizes the first display of Lemma 2.15 of HC, equation (2.127),

> `𝐀hom(y + cus_n) ≤ 𝐀hom(cu_k) + C Π^{1/2}(1-γ)^{-1}(1 + K²3^{-k})^γ 3^{-(n-k)}𝐄`,

in the construction's carriers, and combines it with the Euclidean envelope of
`SmallContrastHomogenizedComparison` to produce the *adapted-cube* form of
HC (4.18).

The construction is the base-scale refinement of the Whitney bridge
`Window.adapted_scaled_of_standard`.  That bridge fills the adapted cell of
scale `r` with Euclidean cells starting at scale `r` itself, and pays
`boundaryConst = C_d 𝔢_q ζ_g` on *every* row, including the top one — which is
exactly the `Π`-dependence that has to be isolated.  Here the maximal
filling is started at a *lower* base scale `k ≤ r`.  Then

* the top row consists of Euclidean cells of scale `k`; its weights sum to at
  most one, and — this is the step the printed proof performs and the construction
  never did — its annealed value is `𝐀hom(cu_k)` by stationarity
  (`Quenched.annealedBlock_standardCell_eq_centeredCube`), *not* a Dagger
  envelope.  No geometric constant is paid on it at all;
* every lower row `k - u`, `u ≥ 1`, is a boundary row: its relative volume is at
  most `C_d 𝔢_q 3^{(k-u)-r}`, so the whole tail is charged
  `boundaryConst · 3^{-(1-g)(r-k)} · 3^{gG}`, which is a *decaying* function of
  the gap `r - k`.

Consequently all of the adapted geometry — `𝔢_q` and the grid enlargement `G`,
i.e. all of `Π` — appears only inside a quantity that the gap `r - k` can be
chosen to make smaller than any prescribed dimensional tolerance, and the gap
enters only through `log₃`.  This is the printed design principle and the
`(1-γ)^{-1} + 2 log Π` part of the printed threshold `n₁`: the `(1-g)` in the
exponent is the source of the printed `(1-γ)^{-1}` factor.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The burn scale -/

/-- **The burn scale of a sample.**  At every sample there is a scale `m ≥ t` at
which the source has burned and whose Dagger discount relative to `t` is at most
`1 + 1_bad·nss`: the good event uses `m = t` and pays nothing, and the bad event
uses the source's own scale and pays the normalized source scale.  This is the
Markov step the construction's entry envelope performs inline, isolated. -/
theorem exists_burnScale {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {S : CoeffSpace d → ℝ} {sK t : ℤ} (hDelta : 0 ≤ t - 1 - sK)
    (a : CoeffSpace d) :
    ∃ m : ℤ, t ≤ m ∧ S a ≤ (3 : ℝ) ^ m ∧
      (3 : ℝ) ^ (g * ((m : ℝ) - (t : ℝ))) ≤
        1 + ({b | (3 : ℝ) ^ t < S b}).indicator (normalizedSourceScale S sK) a := by
  classical
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {b | (3 : ℝ) ^ t < S b} with hbaddef
  have hnss1 : ∀ b, 1 ≤ nss b := fun b => one_le_normalizedSourceScale S sK b
  by_cases hS' : S a ≤ (3 : ℝ) ^ t
  · refine ⟨t, le_rfl, hS', ?_⟩
    have hind : bad.indicator nss a = 0 := by
      refine Set.indicator_of_notMem ?_ nss
      rw [hbaddef, Set.mem_ofPred_eq]
      exact not_lt.mpr hS'
    rw [hind, sub_self, mul_zero, Real.rpow_zero]
    norm_num
  · push Not at hS'
    have hS0 : 0 < S a := lt_trans (zpow_pos (by norm_num) _) hS'
    set m : ℤ := ⌈Real.logb 3 (S a)⌉ with hmdef
    refine ⟨m, ?_, ?_, ?_⟩
    · have hlogS : ((t : ℤ) : ℝ) < Real.logb 3 (S a) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) hS0]
        rw [← Real.rpow_intCast (3 : ℝ) t] at hS'
        exact hS'
      have h := le_trans hlogS.le (Int.le_ceil (Real.logb 3 (S a)))
      rw [hmdef]
      exact_mod_cast h
    · have h1 : S a = (3 : ℝ) ^ Real.logb 3 (S a) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hS0).symm
      rw [h1, ← Real.rpow_intCast (3 : ℝ) m]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hmdef ▸ Int.le_ceil _)
    · have hind : bad.indicator nss a = nss a := by
        refine Set.indicator_of_mem ?_ nss
        rw [hbaddef, Set.mem_ofPred_eq]
        exact hS'
      rw [hind]
      have hup : ((m : ℤ) : ℝ) ≤ Real.logb 3 (S a) + 1 := by
        have h := Int.ceil_lt_add_one (Real.logb 3 (S a))
        rw [hmdef]
        exact_mod_cast h.le
      have hmS : (3 : ℝ) ^ (((m : ℤ) : ℝ) - (t : ℝ)) ≤ nss a := by
        have h1 : (3 : ℝ) ^ (((m : ℤ) : ℝ) - (t : ℝ)) ≤
            (3 : ℝ) ^ (Real.logb 3 (S a) + 1 - (t : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          linarith only [hup]
        refine h1.trans ?_
        have h2 : (3 : ℝ) ^ (Real.logb 3 (S a) + 1 - (t : ℝ)) =
            S a * (3 : ℝ) ^ (1 - (t : ℝ)) := by
          rw [show Real.logb 3 (S a) + 1 - (t : ℝ) =
              Real.logb 3 (S a) + (1 - (t : ℝ)) from by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 3),
            Real.rpow_logb (by norm_num) (by norm_num) hS0]
        rw [h2]
        have h3 : S a * (3 : ℝ) ^ (1 - (t : ℝ)) ≤ S a * (3 : ℝ) ^ (-(sK : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS0.le
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hcast : (0 : ℝ) ≤ ((t - 1 - sK : ℤ) : ℝ) := by exact_mod_cast hDelta
          push_cast at hcast ⊢
          linarith only [hcast]
        refine h3.trans ?_
        rw [show (3 : ℝ) ^ (-(sK : ℝ)) = (3 : ℝ) ^ (-sK : ℤ) from by
          rw [← Real.rpow_intCast (3 : ℝ) (-sK)]
          norm_num]
        rw [hnssdef, normalizedSourceScale]
        exact le_max_right _ _
      have hfactor : (3 : ℝ) ^ (g * (((m : ℤ) : ℝ) - (t : ℝ))) ≤
          nss a := by
        calc
          (3 : ℝ) ^ (g * (((m : ℤ) : ℝ) - (t : ℝ))) =
              ((3 : ℝ) ^ (((m : ℤ) : ℝ) - (t : ℝ))) ^ g := by
            rw [mul_comm g, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ ≤ nss a ^ g :=
            Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hmS hg.1
          _ ≤ nss a ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (hnss1 a) hg.2.le
          _ = nss a := Real.rpow_one _
      have hnss0 : 0 ≤ nss a := le_trans zero_le_one (hnss1 a)
      linarith only [hfactor, hnss0]

/-! ## The boundary-row series -/

/-- The boundary Whitney tail `Σ_{u ≥ 1} 3^{-(1-g)u} ≤ ζ_g`, in the shifted form
in which the rows below the base scale appear. -/
private theorem summable_tail_and_tsum_le {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    Summable (fun u : ℕ =>
      (3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1))) ∧
      ∑' u : ℕ, (3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1)) ≤
        zetaG g := by
  have hterm : ∀ u : ℕ,
      (3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1)) =
        ((3 : ℝ) ^ (-(1 - g))) ^ u * (3 : ℝ) ^ (-(1 - g)) := by
    intro u
    rw [← Real.rpow_intCast (3 : ℝ) (-((u : ℤ) + 1)),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - g))) u,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(1 - g)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr1 : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg.2])
  constructor
  · have hgeom : Summable fun u : ℕ =>
        ((3 : ℝ) ^ (-(1 - g))) ^ u * (3 : ℝ) ^ (-(1 - g)) :=
      Summable.mul_right ((3 : ℝ) ^ (-(1 - g)))
        (summable_geometric_of_lt_one hr0 hr1)
    exact hgeom.congr fun u => (hterm u).symm
  · rw [tsum_congr hterm, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, zetaG]
    have hinv : (0 : ℝ) < (1 - (3 : ℝ) ^ (-(1 - g)))⁻¹ := by
      refine inv_pos.mpr ?_
      linarith only [hr1]
    nlinarith only [hr0, hr1, hinv]

/-! ## The tilt defect -/

/-- The boundary defect of the tilt comparison: the construction's rendering of the
printed error `CΠ^{1/2}(1-γ)^{-1}(1 + K²3^{-k})^γ3^{-(n-k)}` of HC (2.127).
All the adapted geometry sits in the prefactor `boundaryConst · 3^{gG}`, and the
gap `r - k` discounts it geometrically at rate `1 - g`. -/
@[expose]
def tiltDefect (Cd g : ℝ) (m : Mat d) (G : ℕ) (k r : ℤ) : ℝ :=
  2 * boundaryConst Cd g m *
    (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ))

theorem tiltDefect_nonneg [Nonempty (Fin d)] {Cd g : ℝ} (hCd : 1 ≤ Cd)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {m : Mat d} (hm : m.PosDef) (G : ℕ) (k r : ℤ) :
    0 ≤ tiltDefect Cd g m G k r := by
  rw [tiltDefect]
  have hb : (1 : ℝ) ≤ boundaryConst Cd g m := Initialization.one_le_boundaryConst hCd hg hm
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hb0 : (0 : ℝ) ≤ boundaryConst Cd g m := by linarith only [hb]
  positivity

/-! ## The bad-event first moment -/

/-- The first moment of the bad-event indicator of the normalized source scale,
by Markov at the second moment: this is the Markov step of the entry envelope,
isolated for reuse. -/
theorem integral_indicator_normalizedSourceScale_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK) (t : ℤ) :
    ∫ a, ({b | (3 : ℝ) ^ t < S b}).indicator (normalizedSourceScale S sK) a ∂P ≤
      euclideanEntryDefect K sK t := by
  classical
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {b | (3 : ℝ) ^ t < S b} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_lt measurable_const hdag.source_measurable
  have hnss1 : ∀ b, 1 ≤ nss b := fun b => one_le_normalizedSourceScale S sK b
  set tau : ℝ := (3 : ℝ) ^ (t - sK) with htaudef
  have htau0 : 0 < tau := zpow_pos (by norm_num) _
  have hnss_tau : ∀ a ∈ bad, tau ≤ nss a := by
    intro a ha
    rw [hbaddef, Set.mem_ofPred_eq] at ha
    have h1 : tau * (3 : ℝ) ^ sK ≤ S a := by
      rw [htaudef, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      have heq : t - sK + sK = t := by ring
      rw [heq]
      exact ha.le
    have h2 : tau ≤ S a * (3 : ℝ) ^ (-sK) := by
      calc
        tau = tau * (3 : ℝ) ^ sK * (3 : ℝ) ^ (-sK) := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
        _ ≤ S a * (3 : ℝ) ^ (-sK) := by
          refine mul_le_mul_of_nonneg_right h1 ?_
          positivity
    refine le_trans h2 ?_
    rw [hnssdef, normalizedSourceScale]
    exact le_max_right _ _
  have hindsq : ∀ a, bad.indicator nss a ≤ tau⁻¹ * nss a ^ 2 := by
    intro a
    by_cases ha : a ∈ bad
    · rw [Set.indicator_of_mem ha]
      have h1 := hnss_tau a ha
      have hnss0 : 0 ≤ nss a := le_trans zero_le_one (hnss1 a)
      rw [← sub_nonneg] at h1
      rw [← sub_nonneg]
      have hkey : tau⁻¹ * nss a ^ 2 - nss a = tau⁻¹ * (nss a * (nss a - tau)) := by
        field_simp
      rw [hkey]
      exact mul_nonneg (inv_nonneg.mpr htau0.le)
        (mul_nonneg hnss0 (by linarith only [h1]))
    · rw [Set.indicator_of_notMem ha]
      positivity
  have hindint : Integrable (fun a => bad.indicator nss a) P := by
    refine (Integrable.indicator ?_ hbadmeas).congr
      (_root_.Filter.Eventually.of_forall fun a => rfl)
    exact integrable_normalizedSourceScale hdag hsK
  have h1 : ∫ a, bad.indicator nss a ∂P ≤ ∫ a, tau⁻¹ * nss a ^ 2 ∂P := by
    refine integral_mono hindint ?_ hindsq
    exact (integrable_sq_normalizedSourceScale hdag hsK).const_mul _
  refine le_trans h1 ?_
  rw [integral_const_mul]
  have h2 := integral_sq_normalizedSourceScale_le hdag hsK
  have h3 : tau⁻¹ * (∫ a, nss a ^ 2 ∂P) ≤ tau⁻¹ * sourceMomentTwo K :=
    mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr htau0.le)
  refine le_trans h3 (le_of_eq ?_)
  rw [euclideanEntryDefect, htaudef, ← zpow_neg]
  have heq : -(t - sK) = sK - t := by ring
  rw [heq]
  ring


/-! ## The tilt comparison -/


private theorem adapted_filling_tail_row_bound [NeZero d]
     {g : ℝ}
    {E : BlockMat d} {S : CoeffSpace d → ℝ}
    {l : ℤ}
    {Cd : ℝ}
    {nu : Mat d}
    {sK : ℤ}
    {k r : ℤ} {G : ℕ}
    {Z : ℤ → Finset (Fin d → ℤ)} {X : BlockVec d}
    {a : CoeffSpace d} {m : ℤ}
    (hZ : ∀ b, ↑(Z b) = Transport.fillingIndex (1 : Mat d) k
      (adaptedCellTranslate (roundedGrid l nu) r (0 : Vec d)) b)
    (hm3 : (3 : ℝ) ^ (g * ((m : ℝ) - ((r + (G : ℤ) : ℤ) : ℝ))) ≤
      1 + ({b | (3 : ℝ) ^ (r + (G : ℤ)) < S b}).indicator
        (normalizedSourceScale S sK) a)
    (hp : (roundedGrid l nu).PosDef)
    (hCd1 : (1 : ℝ) ≤ Cd)
    (hecc : 1 ≤ witnessEccentricity nu)
    (hidentity : ∀ (b : ℤ) (w : Fin d → ℤ),
      adaptedCellAt (1 : Mat d) b w = standardCell d b w)
    (hdim : 6 * (d : ℝ) * Real.sqrt d * ‖(roundedGrid l nu)⁻¹ * (1 : Mat d)‖ ≤
      Cd * witnessEccentricity nu)
    (heQuad0 : 0 ≤ (1 / 2 * blockVecDot X (blockMatVecMul E X)))
    (hDcore0 : (0 : ℝ) < ((3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ))))
    (hcellbound : ∀ (b : ℤ) (w : Fin d → ℤ), w ∈ Z b →
        1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (standardCell d b w) a) X) ≤
          (3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * (1 / 2 * blockVecDot X (blockMatVecMul E X)))
    : (∀ u : ℕ,
        (∑' w : {w // w ∈ Z (k - ((u + 1 : ℕ) : ℤ))}, (fun i =>
      (volume (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1)).toReal /
          (volume (adaptedCellTranslate (roundedGrid l nu) r 0)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul
            (coarseBlock (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) a) X))) ⟨u + 1, w⟩) ≤
          (Cd * witnessEccentricity nu * ((3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)))
            * (1 + ({b | (3 : ℝ) ^ (r + (G : ℤ)) < S b}).indicator (normalizedSourceScale S sK) a)
            * (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
            ((3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1)))) := by
  classical
  set p : Mat d := roundedGrid l nu with hpdef
  set eQuad : ℝ := 1 / 2 * blockVecDot X (blockMatVecMul E X) with heQdef
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {b | (3 : ℝ) ^ (r + (G : ℤ)) < S b} with hbaddef
  set Dcore : ℝ :=
    (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)) with hDcoredef
  set term : (Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))}) → ℝ := fun i =>
    (volume (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1)).toReal /
        (volume (adaptedCellTranslate p r 0)).toReal *
      (1 / 2 * blockVecDot X
        (blockMatVecMul
          (coarseBlock (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) a) X))
    with htermdef
  have hrowTail : ∀ u : ℕ,
      (∑' w : {w // w ∈ Z (k - ((u + 1 : ℕ) : ℤ))}, term ⟨u + 1, w⟩) ≤
        (Cd * witnessEccentricity nu * Dcore * (1 + bad.indicator nss a) * eQuad) *
          ((3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1))) := by
    intro u
    rw [tsum_fintype]
    have hbk : k - ((u + 1 : ℕ) : ℤ) < k := by omega
    set b : ℤ := k - ((u + 1 : ℕ) : ℤ) with hbdef
    set rowTerm : (Fin d → ℤ) → ℝ := fun w =>
      (volume (adaptedCellAt (1 : Mat d) b w)).toReal /
          (volume (adaptedCellTranslate p r 0)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) b w) a) X))
      with hrowTermdef
    have hchange : (∑ w : {w // w ∈ Z b}, term ⟨u + 1, w⟩) =
        ∑ w ∈ Z b, rowTerm w := by
      rw [← Finset.sum_subtype (Z b) (fun _ => Iff.rfl) rowTerm]
    rw [hchange]
    have henv : ∀ w ∈ Z b, rowTerm w ≤
        ((volume (adaptedCellAt (1 : Mat d) b w)).toReal /
            (volume (adaptedCellTranslate p r 0)).toReal) *
          ((3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * eQuad) := by
      intro w hw
      rw [hrowTermdef]
      refine mul_le_mul_of_nonneg_left ?_
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      rw [hidentity b w]
      exact hcellbound b w hw
    have hrowsum := Transport.sum_relative_volume_row_le hp Matrix.PosDef.one hbk (hZ b)
    have hexp : (3 : ℝ) ^ ((b - r : ℤ)) *
        (3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) =
        Dcore * (3 : ℝ) ^ (g * ((m : ℝ) - ((r + (G : ℤ) : ℤ) : ℝ))) *
          ((3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1))) := by
      rw [hDcoredef, ← Real.rpow_intCast (3 : ℝ) (b - r),
        ← Real.rpow_intCast (3 : ℝ) (-((u : ℤ) + 1)),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      rw [hbdef]
      push_cast
      ring
    have hgeo0 : (0 : ℝ) ≤
        (3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1)) :=
      mul_nonneg (zpow_pos (by norm_num) _).le (Real.rpow_nonneg (by norm_num) _)
    have hCdecc0 : (0 : ℝ) ≤ Cd * witnessEccentricity nu * eQuad := by
      have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd1]
      have hecc0 : (0 : ℝ) ≤ witnessEccentricity nu := by linarith only [hecc]
      positivity
    calc
      ∑ w ∈ Z b, rowTerm w ≤
          ∑ w ∈ Z b, ((volume (adaptedCellAt (1 : Mat d) b w)).toReal /
              (volume (adaptedCellTranslate p r 0)).toReal) *
            ((3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * eQuad) :=
        Finset.sum_le_sum henv
      _ = (∑ w ∈ Z b, (volume (adaptedCellAt (1 : Mat d) b w)).toReal /
            (volume (adaptedCellTranslate p r 0)).toReal) *
          ((3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * eQuad) := by
        rw [Finset.sum_mul]
      _ ≤ (6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ *
            (3 : ℝ) ^ ((b - r : ℤ))) *
          ((3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * eQuad) := by
        refine mul_le_mul_of_nonneg_right hrowsum ?_
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) heQuad0
      _ ≤ (Cd * witnessEccentricity nu * (3 : ℝ) ^ ((b - r : ℤ))) *
          ((3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * eQuad) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdim (zpow_pos (by norm_num) _).le) ?_
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) heQuad0
      _ = (Cd * witnessEccentricity nu * eQuad) *
          ((3 : ℝ) ^ ((b - r : ℤ)) * (3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ)))) := by
        ring
      _ = (Cd * witnessEccentricity nu * eQuad) *
          (Dcore * (3 : ℝ) ^ (g * ((m : ℝ) - ((r + (G : ℤ) : ℤ) : ℝ))) *
            ((3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1)))) := by
        rw [hexp]
      _ ≤ (Cd * witnessEccentricity nu * eQuad) *
          (Dcore * (1 + bad.indicator nss a) *
            ((3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCdecc0
        refine mul_le_mul_of_nonneg_right ?_ hgeo0
        exact mul_le_mul_of_nonneg_left hm3 hDcore0.le
      _ = (Cd * witnessEccentricity nu * Dcore * (1 + bad.indicator nss a) * eQuad) *
            ((3 : ℝ) ^ (-((u : ℤ) + 1)) * (3 : ℝ) ^ (g * ((u : ℝ) + 1))) := by
        ring
  exact hrowTail

private theorem adapted_filling_union_reindex [NeZero d]
    {k : ℤ}
    {Z : ℤ → Finset (Fin d → ℤ)}
    : ((⋃ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
        adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) =
      ⋃ b ∈ Set.Iic k, ⋃ w ∈ (Z b : Set (Fin d → ℤ)),
        adaptedCellAt (1 : Mat d) b w) := by
  classical
  have hcover : (⋃ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
        adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) =
      ⋃ b ∈ Set.Iic k, ⋃ w ∈ (Z b : Set (Fin d → ℤ)),
        adaptedCellAt (1 : Mat d) b w := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨u, w⟩, hx⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨k - (u : ℤ), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Set.mem_Iic.mpr (by omega)
      · exact Set.mem_iUnion.mpr ⟨w.1, Set.mem_iUnion.mpr ⟨w.2, hx⟩⟩
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hbk, hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hb
      obtain ⟨hwZ, hx⟩ := Set.mem_iUnion.mp hw
      have hscale : k - (((k - b).toNat : ℕ) : ℤ) = b := by
        rw [Int.toNat_of_nonneg (sub_nonneg.mpr (Set.mem_Iic.mp hbk))]
        omega
      have hwZ' : w ∈ Z (k - (((k - b).toNat : ℕ) : ℤ)) := by
        rw [hscale]
        exact hwZ
      refine Set.mem_iUnion.mpr ⟨⟨(k - b).toNat, ⟨w, hwZ'⟩⟩, ?_⟩
      show x ∈ adaptedCellAt (1 : Mat d) (k - (((k - b).toNat : ℕ) : ℤ)) w
      rwa [hscale]
  exact hcover

private theorem adapted_filling_integral_identity [NeZero d]
     {g : ℝ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {S : CoeffSpace d → ℝ}
    {l : ℤ}
    {Cd : ℝ}
    {nu : Mat d}
    {sK : ℤ}
    {k r : ℤ} {G : ℕ}
    {Z : ℤ → Finset (Fin d → ℤ)} {X : BlockVec d}
    (hintCell : ∀ w : Fin d → ℤ, HasIntegrableCoarseBlock P (standardCell d k w))
    (hmeanCell : ∀ w : Fin d → ℤ,
      annealedBlock P (standardCell d k w) = annealedBlock P (centeredCube d k))
    (hindint : Integrable (fun a => ({b | (3 : ℝ) ^ (r + (G : ℤ)) < S b}).indicator
      (normalizedSourceScale S sK) a) P)
    : (∫ a,
      ((∑ w ∈ Z k, (fun w =>
    (volume (standardCell d k w)).toReal /
      (volume (adaptedCellTranslate (roundedGrid l nu) r 0)).toReal) w *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (standardCell d k w) a) X))) +
        boundaryConst Cd g nu * ((3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ))) * (1 +
          ({b | (3 : ℝ) ^ (r + (G : ℤ)) < S b}).indicator (normalizedSourceScale S sK) a) * (1 / 2
          * blockVecDot X (blockMatVecMul E X))) ∂P =
      (∑ w ∈ Z k, (fun w =>
    (volume (standardCell d k w)).toReal /
      (volume (adaptedCellTranslate (roundedGrid l nu) r 0)).toReal) w) *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (annealedBlock P (centeredCube d k)) X)) +
        boundaryConst Cd g nu * ((3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ))) *
          (1 + ∫ a, ({b | (3 : ℝ) ^ (r + (G : ℤ)) < S b}).indicator (normalizedSourceScale S sK) a
            ∂P) * (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
  classical
  set p : Mat d := roundedGrid l nu with hpdef
  set eQuad : ℝ := 1 / 2 * blockVecDot X (blockMatVecMul E X) with heQdef
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {b | (3 : ℝ) ^ (r + (G : ℤ)) < S b} with hbaddef
  set Dcore : ℝ :=
    (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)) with hDcoredef
  set wt : (Fin d → ℤ) → ℝ := fun w =>
    (volume (standardCell d k w)).toReal /
      (volume (adaptedCellTranslate p r 0)).toReal with hwtdef
  have hReq : ∫ a,
      ((∑ w ∈ Z k, wt w *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (standardCell d k w) a) X))) +
        boundaryConst Cd g nu * Dcore * (1 + bad.indicator nss a) * eQuad) ∂P =
      (∑ w ∈ Z k, wt w) *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (annealedBlock P (centeredCube d k)) X)) +
        boundaryConst Cd g nu * Dcore *
          (1 + ∫ a, bad.indicator nss a ∂P) * eQuad := by
    rw [integral_add
      (integrable_finsetSum _ fun w _ =>
        ((integrable_blockVecDot_coarseBlock (hintCell w) X).const_mul _).const_mul _)
      (by
        have h := (((integrable_const (1 : ℝ)).add hindint).const_mul
          (boundaryConst Cd g nu * Dcore)).mul_const eQuad
        refine h.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
        simp only [Pi.add_apply])]
    congr 1
    · rw [integral_finsetSum _ fun w _ =>
        ((integrable_blockVecDot_coarseBlock (hintCell w) X).const_mul _).const_mul _,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [integral_const_mul, integral_const_mul,
        ← blockVecDot_blockMatVecMul_annealedBlock (hintCell w) X, hmeanCell w]
    · rw [show (fun a => boundaryConst Cd g nu * Dcore *
          (1 + bad.indicator nss a) * eQuad) =
          fun a => boundaryConst Cd g nu * Dcore * eQuad +
            (boundaryConst Cd g nu * Dcore * eQuad) * bad.indicator nss a from by
        funext a
        ring]
      rw [integral_add (integrable_const _) (hindint.const_mul _),
        integral_const, probReal_univ, one_smul, integral_const_mul]
      ring
  exact hReq

private theorem adapted_filling_pathwise_quadratic_bound [NeZero d]
     {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ}
    {Cd : ℝ}
    {nu : Mat d}
    {sK : ℤ}
    {k r : ℤ} {G : ℕ}
    (hDelta : 0 ≤ r + (G : ℤ) - 1 - sK)
    {Z : ℤ → Finset (Fin d → ℤ)} {X : BlockVec d}
    (hZ : ∀ b, ↑(Z b) = Transport.fillingIndex (1 : Mat d) k
      (adaptedCellTranslate (roundedGrid l nu) r (0 : Vec d)) b)
    (hgeomSummable : Summable (fun u : ℕ => (3 : ℝ) ^ (-((u : ℤ) + 1)) *
      (3 : ℝ) ^ (g * ((u : ℝ) + 1))))
    (hgeomTsum : (∑' u : ℕ, (3 : ℝ) ^ (-((u : ℤ) + 1)) *
      (3 : ℝ) ^ (g * ((u : ℝ) + 1))) ≤ zetaG g)
    (hd0 : 0 < d)
    (hp : (roundedGrid l nu).PosDef)
    (hCd1 : (1 : ℝ) ≤ Cd)
    (hecc : 1 ≤ witnessEccentricity nu)
    (hparent : adaptedCellTranslate (roundedGrid l nu) r (0 : Vec d) = adaptedCell (roundedGrid l
      nu) r)
    (hidentity : ∀ (b : ℤ) (w : Fin d → ℤ),
      adaptedCellAt (1 : Mat d) b w = standardCell d b w)
    (hcellsub : ∀ (b : ℤ) (w : Fin d → ℤ), w ∈ Z b →
      standardCell d b w ⊆ centeredCube d (r + (G : ℤ)))
    (hc : ∀ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
      IsOpenBoundedConvexDomain (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1))
    (hcsub : ∀ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
      adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1 ⊆
        adaptedCellTranslate (roundedGrid l nu) r 0)
    (hcpair : Pairwise fun i j : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))} =>
      Disjoint (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1)
        (adaptedCellAt (1 : Mat d) (k - (j.1 : ℤ)) j.2.1))
    (hc0 : ∀ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
      volume (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) ≠ 0)
    (hcnull : volume (adaptedCellTranslate (roundedGrid l nu) r 0 \
      ⋃ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
        adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) = 0)
    (hparent0 : volume (adaptedCellTranslate (roundedGrid l nu) r 0) ≠ 0)
    (hdim : 6 * (d : ℝ) * Real.sqrt d * ‖(roundedGrid l nu)⁻¹ * (1 : Mat d)‖ ≤
      Cd * witnessEccentricity nu)
    (heQuad0 : 0 ≤ (1 / 2 * blockVecDot X (blockMatVecMul E X)))
    (hDcore0 : (0 : ℝ) < ((3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ))))
    : (∀ᵐ a ∂P,
      1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCell (roundedGrid l nu) r) a) X) ≤
        (∑ w ∈ Z k, (fun w =>
    (volume (standardCell d k w)).toReal /
      (volume (adaptedCellTranslate (roundedGrid l nu) r 0)).toReal) w *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (standardCell d k w) a) X))) +
          boundaryConst Cd g nu * ((3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ))) * (1 +
            ({b | (3 : ℝ) ^ (r + (G : ℤ)) < S b}).indicator (normalizedSourceScale S sK) a) * (1 /
            2 * blockVecDot X (blockMatVecMul E X))) := by
  classical
  set p : Mat d := roundedGrid l nu with hpdef
  set eQuad : ℝ := 1 / 2 * blockVecDot X (blockMatVecMul E X) with heQdef
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {b | (3 : ℝ) ^ (r + (G : ℤ)) < S b} with hbaddef
  set Dcore : ℝ :=
    (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)) with hDcoredef
  set wt : (Fin d → ℤ) → ℝ := fun w =>
    (volume (standardCell d k w)).toReal /
      (volume (adaptedCellTranslate p r 0)).toReal with hwtdef
  have hpath : ∀ᵐ a ∂P,
      1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCell p r) a) X) ≤
        (∑ w ∈ Z k, wt w *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (standardCell d k w) a) X))) +
          boundaryConst Cd g nu * Dcore * (1 + bad.indicator nss a) * eQuad := by
    filter_upwards [hdag.coarse_bound] with a hbound
    obtain ⟨m, hm1, hm2, hm3⟩ :=
      exists_burnScale (S := S) (sK := sK) (t := r + (G : ℤ)) hg hDelta a
    set term : (Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))}) → ℝ := fun i =>
      (volume (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1)).toReal /
          (volume (adaptedCellTranslate p r 0)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul
            (coarseBlock (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) a) X))
      with htermdef
    have hterm0 : ∀ i, 0 ≤ term i := by
      intro i
      have hquad0 : 0 ≤ 1 / 2 *
          blockVecDot X (blockMatVecMul
            (coarseBlock (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) a) X) := by
        by_cases hX : X = 0
        · subst X
          simp [blockMatVecMul, blockVecDot, vecDot]
        · exact mul_nonneg (by norm_num)
            ((Recurrence.blockPosDef_coarseBlock_adaptedCellAt Matrix.PosDef.one _ _ a) X hX).le
      exact mul_nonneg
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hquad0
    have hcellbound : ∀ (b : ℤ) (w : Fin d → ℤ), w ∈ Z b →
        1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (standardCell d b w) a) X) ≤
          (3 : ℝ) ^ (g * ((m : ℝ) - (b : ℝ))) * eQuad := by
      intro b w hw
      have hsubm : standardCell d b w ⊆ centeredCube d m :=
        (hcellsub b w hw).trans (Window.centeredCube_mono hm1)
      have hbm : b ≤ m :=
        Window.scale_le_of_standardCell_subset_centeredCube hd0 hsubm
      have hcenter : standardCellCenter b w ∈ centeredCube d m :=
        hsubm (Recurrence.standardCellCenter_mem_standardCell b w)
      have h := hbound m hm2 b hbm w hcenter X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h
      rw [heQdef]
      linarith only [h]
    have hCoef0 : (0 : ℝ) ≤
        Cd * witnessEccentricity nu * Dcore * (1 + bad.indicator nss a) * eQuad := by
      have hind0 : 0 ≤ bad.indicator nss a := by
        refine Set.indicator_nonneg (fun b _ => ?_) a
        exact le_trans zero_le_one (one_le_normalizedSourceScale S sK b)
      have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd1]
      have hecc0 : (0 : ℝ) ≤ witnessEccentricity nu := by linarith only [hecc]
      have hone : (0 : ℝ) ≤ 1 + bad.indicator nss a := by linarith only [hind0]
      have hDc : (0 : ℝ) ≤ Dcore := hDcore0.le
      positivity
    have hrowTail :=
      adapted_filling_tail_row_bound hZ hm3
        hp hCd1 hecc hidentity hdim heQuad0 hDcore0 hcellbound
    have hrow0 : ∀ u : ℕ, 0 ≤ ∑' w : {w // w ∈ Z (k - (u : ℤ))}, term ⟨u, w⟩ :=
      fun u => tsum_nonneg fun w => hterm0 ⟨u, w⟩
    have hTailSummable : Summable
        (fun u : ℕ => ∑' w : {w // w ∈ Z (k - ((u + 1 : ℕ) : ℤ))}, term ⟨u + 1, w⟩) :=
      Summable.of_nonneg_of_le (fun u => hrow0 (u + 1)) hrowTail
        (hgeomSummable.mul_left _)
    have hrowSummable : Summable
        (fun u : ℕ => ∑' w : {w // w ∈ Z (k - (u : ℤ))}, term ⟨u, w⟩) :=
      (summable_nat_add_iff 1).mp hTailSummable
    have htermSummable : Summable term :=
      (summable_sigma_of_nonneg hterm0).2
        ⟨fun _ => (hasSum_fintype _).summable, hrowSummable⟩
    have hsubadd : 1 / 2 * blockVecDot X
        (blockMatVecMul (coarseBlock (adaptedCellTranslate p r 0) a) X) ≤
        ∑' i, term i :=
      Window.blockQuadratic_le_tsum_weight_of_countable_aePartition
        (Transport.isOpenBoundedConvexDomain_adaptedCellTranslate hp r 0) hparent0 a
        hc hcsub hcpair hcnull hc0 X htermSummable
    have hsigma : ∑' i, term i =
        (∑' w : {w // w ∈ Z (k - ((0 : ℕ) : ℤ))}, term ⟨0, w⟩) +
          ∑' u : ℕ, ∑' w : {w // w ∈ Z (k - ((u + 1 : ℕ) : ℤ))}, term ⟨u + 1, w⟩ := by
      rw [htermSummable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
      exact hrowSummable.tsum_eq_zero_add
    have htailbound : (∑' u : ℕ,
        ∑' w : {w // w ∈ Z (k - ((u + 1 : ℕ) : ℤ))}, term ⟨u + 1, w⟩) ≤
        boundaryConst Cd g nu * Dcore * (1 + bad.indicator nss a) * eQuad := by
      refine le_trans (hTailSummable.tsum_le_tsum hrowTail (hgeomSummable.mul_left _)) ?_
      rw [tsum_mul_left]
      have hmul := mul_le_mul_of_nonneg_left hgeomTsum hCoef0
      refine le_trans hmul (le_of_eq ?_)
      rw [boundaryConst]
      ring
    have hhead : (∑' w : {w // w ∈ Z (k - ((0 : ℕ) : ℤ))}, term ⟨0, w⟩) =
        ∑ w ∈ Z k, wt w *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (standardCell d k w) a) X)) := by
      rw [tsum_fintype]
      have hz : k - ((0 : ℕ) : ℤ) = k := by omega
      set headTerm : (Fin d → ℤ) → ℝ := fun w =>
        (volume (adaptedCellAt (1 : Mat d) (k - ((0 : ℕ) : ℤ)) w)).toReal /
            (volume (adaptedCellTranslate p r 0)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul
              (coarseBlock (adaptedCellAt (1 : Mat d) (k - ((0 : ℕ) : ℤ)) w) a) X))
        with hheadTermdef
      have hchange : (∑ w : {w // w ∈ Z (k - ((0 : ℕ) : ℤ))}, term ⟨0, w⟩) =
          ∑ w ∈ Z (k - ((0 : ℕ) : ℤ)), headTerm w := by
        rw [← Finset.sum_subtype (Z (k - ((0 : ℕ) : ℤ))) (fun _ => Iff.rfl) headTerm]
      rw [hchange, hz]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hheadTermdef, hwtdef]
      simp only [hz, hidentity]
    rw [hparent] at hsubadd
    rw [hsigma, hhead] at hsubadd
    linarith only [hsubadd, htailbound]
  -- integrate the pathwise split
  exact hpath
/-- **The adapted-to-Euclidean tilt comparison** (Lemma 2.15 of HC,
equation (2.127)).  For `0 ≤ k ≤ r` the annealed adapted cell of scale `r` is
dominated by the annealed *Euclidean* cube of scale `k` plus a boundary defect
which carries all of the adapted geometry but decays geometrically in the gap
`r - k`.

The top row of the maximal filling is charged by stationarity — its
annealed value is exactly `𝐀hom(cu_k)` — and only the rows strictly below the
base scale are charged by the Dagger, at total relative volume
`C_d𝔢_q3^{-(r-k)}`. -/
theorem adaptedMean_quadratic_le_add_tiltDefect [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k r : ℤ} {G : ℕ} (hk0 : 0 ≤ k)
    (hDelta : 0 ≤ r + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (r + (G : ℤ) - sK))
    (hsub : adaptedCell (roundedGrid l nu) r ⊆ centeredCube d (r + (G : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l nu) r) :
    ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul (adaptedMean P (roundedGrid l nu) r) X) ≤
        blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d k)) X) +
          tiltDefect Cd g nu G k r * blockVecDot X (blockMatVecMul E X) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hd0 : 0 < d := by omega
  set p : Mat d := roundedGrid l nu with hpdef
  have hp : p.PosDef := Recurrence.posDef_roundedGrid hl hnu
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hCdDim : 12 * (d : ℝ) * Real.sqrt d ≤ Cd := (le_max_right _ _).trans hCd
  have hecc : 1 ≤ witnessEccentricity nu := Initialization.one_le_witnessEccentricity hnu
  have hbC1 : (1 : ℝ) ≤ boundaryConst Cd g nu := Initialization.one_le_boundaryConst hCd1 hg hnu
  have hparent : adaptedCellTranslate p r (0 : Vec d) = adaptedCell p r := by
    simp [adaptedCellTranslate]
  obtain ⟨Z, hZ, hsubZ, hdomZ, _hvolZ, hdisjZ, _hrowZ, _hrowZ1, hnullZ⟩ :=
    Transport.maximal_filling hp Matrix.PosDef.one k r (0 : Vec d)
  have hidentity : ∀ (b : ℤ) (w : Fin d → ℤ),
      adaptedCellAt (1 : Mat d) b w = standardCell d b w := by
    intro b w
    rw [Recurrence.adaptedCellAt_eq_image]
    have hone : matVecMul (1 : Mat d) = fun x => x := by
      funext x i
      exact congrFun (Matrix.one_mulVec x) i
    rw [hone, Set.image_id']
  have hcellsub : ∀ (b : ℤ) (w : Fin d → ℤ), w ∈ Z b →
      standardCell d b w ⊆ centeredCube d (r + (G : ℤ)) := by
    intro b w hw
    rw [← hidentity]
    exact (hsubZ b w hw).trans (by rw [hparent]; exact hsub)
  have hc : ∀ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
      IsOpenBoundedConvexDomain (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) :=
    fun i => hdomZ _ _ i.2.2
  have hcsub : ∀ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
      adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1 ⊆
        adaptedCellTranslate p r 0 := fun i => hsubZ _ _ i.2.2
  have hcpair : Pairwise fun i j : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))} =>
      Disjoint (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1)
        (adaptedCellAt (1 : Mat d) (k - (j.1 : ℤ)) j.2.1) := by
    intro i j hij
    apply hdisjZ _ _ _ i.2.2 _ j.2.2
    intro heq
    apply hij
    rcases i with ⟨u, w⟩
    rcases j with ⟨v, z⟩
    have huv : u = v := by
      have hs := congrArg Prod.fst heq
      dsimp at hs
      omega
    subst v
    have hwz : w = z := Subtype.ext (congrArg Prod.snd heq)
    subst z
    rfl
  have hc0 : ∀ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
      volume (adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) ≠ 0 := fun i =>
    (Recurrence.volume_adaptedCellAt_pos Matrix.PosDef.one _ _).ne'
  have hcover :=
    adapted_filling_union_reindex
  have hcnull : volume (adaptedCellTranslate p r 0 \
      ⋃ i : Σ u : ℕ, {w // w ∈ Z (k - (u : ℤ))},
        adaptedCellAt (1 : Mat d) (k - (i.1 : ℤ)) i.2.1) = 0 := by
    rw [hcover]
    exact hnullZ
  have hparent0 : volume (adaptedCellTranslate p r 0) ≠ 0 :=
    Transport.volume_adaptedCellTranslate_ne_zero hp r 0
  have hnorm : ‖p⁻¹ * (1 : Mat d)‖ ≤ 2 := by
    rw [Matrix.mul_one, hpdef]
    exact (Window.norm_inv_roundedGrid_le hl hnu).trans (by norm_num)
  have hdim : 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ ≤
      Cd * witnessEccentricity nu := by
    have hbase : 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ ≤
        12 * (d : ℝ) * Real.sqrt d := by
      have hnonneg : 0 ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
      have hmul := mul_le_mul_of_nonneg_left hnorm hnonneg
      linarith only [hmul]
    exact hbase.trans <| hCdDim.trans <|
      (le_mul_of_one_le_right (by linarith only [hCd1]) hecc)
  intro X
  set eQuad : ℝ := 1 / 2 * blockVecDot X (blockMatVecMul E X) with heQdef
  have heQuad0 : 0 ≤ eQuad := by
    rw [heQdef]
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact mul_nonneg (by norm_num) (hdag.refBlock_posDef X hX).le
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  set bad : Set (CoeffSpace d) := {b | (3 : ℝ) ^ (r + (G : ℤ)) < S b} with hbaddef
  set Dcore : ℝ :=
    (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)) with hDcoredef
  have hDcore0 : (0 : ℝ) < Dcore := Real.rpow_pos_of_pos (by norm_num) _
  set wt : (Fin d → ℤ) → ℝ := fun w =>
    (volume (standardCell d k w)).toReal /
      (volume (adaptedCellTranslate p r 0)).toReal with hwtdef
  obtain ⟨hgeomSummable, hgeomTsum⟩ := summable_tail_and_tsum_le hg
  -- the pathwise split of the filling
  have hpath :=
    adapted_filling_pathwise_quadratic_bound hg hdag
      hDelta hZ hgeomSummable hgeomTsum hd0 hp hCd1 hecc hparent hidentity hcellsub hc hcsub hcpair
      hc0 hcnull hparent0 hdim heQuad0 hDcore0
  have hintCube : HasIntegrableCoarseBlock P (centeredCube d k) :=
    hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag k
  have hintCell : ∀ w : Fin d → ℤ, HasIntegrableCoarseBlock P (standardCell d k w) := by
    intro w
    rw [standardCell_eq_translateSet_centeredCube hk0 w]
    exact Recurrence.hasIntegrableCoarseBlock_translateSet hstat hintCube _
  have hmeanCell : ∀ w : Fin d → ℤ,
      annealedBlock P (standardCell d k w) = annealedBlock P (centeredCube d k) :=
    fun w => annealedBlock_standardCell_eq_centeredCube hstat hk0 w
      (hasMeasurableCoarseBlock_centeredCube P k)
  have hindint : Integrable (fun a => bad.indicator nss a) P := by
    refine (Integrable.indicator ?_ (measurableSet_lt measurable_const
      hdag.source_measurable)).congr (_root_.Filter.Eventually.of_forall fun a => rfl)
    exact integrable_normalizedSourceScale hdag hsK
  have hLint : Integrable (fun a => 1 / 2 * blockVecDot X
      (blockMatVecMul (coarseBlock (adaptedCell p r) a) X)) P :=
    (integrable_blockVecDot_coarseBlock hint X).const_mul _
  have hRint : Integrable (fun a =>
      (∑ w ∈ Z k, wt w *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (standardCell d k w) a) X))) +
        boundaryConst Cd g nu * Dcore * (1 + bad.indicator nss a) * eQuad) P := by
    refine Integrable.add ?_ ?_
    · refine integrable_finsetSum _ fun w _ => ?_
      exact ((integrable_blockVecDot_coarseBlock (hintCell w) X).const_mul _).const_mul _
    · have h := (((integrable_const (1 : ℝ)).add hindint).const_mul
        (boundaryConst Cd g nu * Dcore)).mul_const eQuad
      refine h.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
      simp only [Pi.add_apply]
  have hmono := integral_mono_ae hLint hRint hpath
  have hLeq : ∫ a, 1 / 2 * blockVecDot X
      (blockMatVecMul (coarseBlock (adaptedCell p r) a) X) ∂P =
      1 / 2 * blockVecDot X
        (blockMatVecMul (adaptedMean P p r) X) := by
    rw [integral_const_mul, ← blockVecDot_blockMatVecMul_annealedBlock hint X]
    rfl
  have hReq :=
    adapted_filling_integral_identity hintCell hmeanCell hindint
  rw [hLeq, hReq] at hmono
  -- the head weight is at most one and the tail moment at most one
  have hwtsum : (∑ w ∈ Z k, wt w) ≤ 1 := by
    have h := Transport.sum_relative_volume_row_le_one hp Matrix.PosDef.one (a := k) (hZ k)
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hwtdef, hidentity]
  have hwt0 : ∀ w ∈ Z k, 0 ≤ wt w := fun w _ => by
    rw [hwtdef]
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hcubequad0 : 0 ≤ 1 / 2 * blockVecDot X
      (blockMatVecMul (annealedBlock P (centeredCube d k)) X) := by
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact mul_nonneg (by norm_num)
        ((blockPosDef_annealedBlock_centeredCube k hintCube) X hX).le
  have hhead_le : (∑ w ∈ Z k, wt w) *
      (1 / 2 * blockVecDot X
        (blockMatVecMul (annealedBlock P (centeredCube d k)) X)) ≤
      1 / 2 * blockVecDot X
        (blockMatVecMul (annealedBlock P (centeredCube d k)) X) := by
    have h := mul_le_mul_of_nonneg_right hwtsum hcubequad0
    linarith only [h]
  have hmomle : (∫ a, bad.indicator nss a ∂P) ≤ 1 := by
    refine le_trans (integral_indicator_normalizedSourceScale_le hdag hsK
      (r + (G : ℤ))) ?_
    rw [euclideanEntryDefect]
    have hT : (0 : ℝ) < (3 : ℝ) ^ (r + (G : ℤ) - sK) := zpow_pos (by norm_num) _
    have hinv : (3 : ℝ) ^ (sK - (r + (G : ℤ))) =
        ((3 : ℝ) ^ (r + (G : ℤ) - sK))⁻¹ := by
      rw [← zpow_neg]
      congr 1
      ring
    rw [hinv]
    have h := mul_le_mul_of_nonneg_right hentry (inv_nonneg.mpr hT.le)
    rwa [mul_inv_cancel₀ hT.ne'] at h
  have hDbase0 : (0 : ℝ) ≤ boundaryConst Cd g nu * Dcore * eQuad := by
    have hb0 : (0 : ℝ) ≤ boundaryConst Cd g nu := by linarith only [hbC1]
    have hDc : (0 : ℝ) ≤ Dcore := hDcore0.le
    positivity
  have htail_le : boundaryConst Cd g nu * Dcore *
      (1 + ∫ a, bad.indicator nss a ∂P) * eQuad ≤
      tiltDefect Cd g nu G k r * eQuad := by
    rw [tiltDefect, ← hDcoredef]
    nlinarith only [hmomle, hDbase0]
  rw [heQdef] at hmono htail_le
  linarith only [hmono, hhead_le, htail_le]

/-! ## The threshold and the adapted near-identity comparison -/

/-- The adapted part of the printed entry threshold `n₁`: the scale gap `r - k`
that discounts the boundary defect below the tolerance.  It is
`(1-g)^{-1}·log₃(2·boundaryConst·3^{gG}/cEnt)`, i.e. exactly the printed
`(1-γ)^{-1} + 2 log Π + A(d)` terms — the aspect ratio enters here, inside a
logarithm, and nowhere else. -/
@[expose]
def tiltGap (Cd g cEnt : ℝ) (m : Mat d) (G : ℕ) : ℤ :=
  max 1
    ⌈Real.logb 3
        (2 * boundaryConst Cd g m * (3 : ℝ) ^ (g * (G : ℝ)) / cEnt) / (1 - g)⌉

/-- Past the gap the tilt defect is at most the prescribed tolerance. -/
theorem tiltDefect_le [Nonempty (Fin d)] {Cd g cEnt : ℝ} (hCd : 1 ≤ Cd)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {nu : Mat d} (hnu : nu.PosDef)
    (hcEnt : 0 < cEnt) {G : ℕ} {k r : ℤ} (hgap : tiltGap Cd g cEnt nu G ≤ r - k) :
    tiltDefect Cd g nu G k r ≤ cEnt := by
  have hbC1 : (1 : ℝ) ≤ boundaryConst Cd g nu := Initialization.one_le_boundaryConst hCd hg hnu
  set A : ℝ := 2 * boundaryConst Cd g nu * (3 : ℝ) ^ (g * (G : ℝ)) with hAdef
  have hA0 : (0 : ℝ) < A := by
    rw [hAdef]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (g * (G : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hb0 : (0 : ℝ) < boundaryConst Cd g nu := by linarith only [hbC1]
    positivity
  have hg1 : (0 : ℝ) < 1 - g := by linarith only [hg.2]
  have hratio : (0 : ℝ) < A / cEnt := div_pos hA0 hcEnt
  have hceil : ⌈Real.logb 3 (A / cEnt) / (1 - g)⌉ ≤ r - k := by
    rw [tiltGap, ← hAdef] at hgap
    have h1 : ⌈Real.logb 3 (A / cEnt) / (1 - g)⌉ ≤
        max 1 ⌈Real.logb 3 (A / cEnt) / (1 - g)⌉ := le_max_right _ _
    omega
  have hlog : Real.logb 3 (A / cEnt) / (1 - g) ≤ (((r - k : ℤ)) : ℝ) := by
    refine le_trans (Int.le_ceil _) ?_
    exact_mod_cast hceil
  have hlog' : Real.logb 3 (A / cEnt) ≤ (1 - g) * (((r - k : ℤ)) : ℝ) := by
    rw [div_le_iff₀ hg1] at hlog
    linarith only [hlog]
  have hpow : A / cEnt ≤ (3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)) := by
    rw [← Real.rpow_logb (b := 3) (by norm_num) (by norm_num) hratio]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog'
  have hT : (0 : ℝ) < (3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hAle : A ≤ (3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)) * cEnt :=
    (div_le_iff₀ hcEnt).mp hpow
  have hexp : (3 : ℝ) ^ (-(1 - g) * ((r : ℝ) - (k : ℝ)) + g * (G : ℝ)) =
      (3 : ℝ) ^ (g * (G : ℝ)) * ((3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hsplit : tiltDefect Cd g nu G k r =
      A * ((3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)))⁻¹ := by
    rw [tiltDefect, hAdef, hexp]
    ring
  rw [hsplit]
  have h := mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr hT.le)
  have hclean : (3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)) * cEnt *
      ((3 : ℝ) ^ ((1 - g) * (((r - k : ℤ)) : ℝ)))⁻¹ = cEnt := by
    field_simp
  rwa [hclean] at h

/-- **The construction form of HC (4.18) on adapted cubes.**
Once the base scale `k` is past the source-moment threshold
and the gap `r - k` is past the geometric threshold, the annealed adapted block
of scale `r` is a near identity in the reference normalization, at a defect
that depends only on the prescribed tolerance and on the reference contrast
excess.

Both thresholds are logarithmic in the data — `log₃ M₂(K)` and
`(1-g)^{-1}log₃(boundaryConst·3^{gG})` — and the conclusion's constant carries
neither the eccentricity of the adapted geometry nor the grid enlargement `G`,
hence neither carries the reference aspect ratio `Π`.  This is the routing the
printed proof performs and the construction's `Π`-carrying entry envelope does
not. -/
theorem adaptedMean_near_reference [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k r : ℤ} {G : ℕ} (hk0 : 0 ≤ k)
    {sigma cEnt : ℝ} (hsigma : refContrast E - 1 ≤ sigma) (hsigma0 : 0 ≤ sigma)
    (hcEnt : 0 < cEnt)
    (hkthr : euclideanEntryThreshold K (cEnt / 2) sK ≤ k)
    (hgap : tiltGap Cd g (cEnt / 2) nu G ≤ r - k)
    (hDelta : 0 ≤ r + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (r + (G : ℤ) - sK))
    (hsub : adaptedCell (roundedGrid l nu) r ⊆ centeredCube d (r + (G : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l nu) r) :
    BlockMatLoewnerLE (blockScale (1 - nearIdentityDefect cEnt sigma) E)
        (adaptedMean P (roundedGrid l nu) r) ∧
      BlockMatLoewnerLE (adaptedMean P (roundedGrid l nu) r)
        (blockScale (1 + nearIdentityDefect cEnt sigma) E) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hq : (roundedGrid l nu).PosDef := Recurrence.posDef_roundedGrid hl hnu
  have hcEnt2 : (0 : ℝ) < cEnt / 2 := by linarith only [hcEnt]
  have hkDelta : 0 ≤ k - 1 - sK := by
    have h1 : (1 : ℤ) ≤ max 1 ⌈Real.logb 3 (sourceMomentTwo K / (cEnt / 2))⌉ :=
      le_max_left _ _
    rw [euclideanEntryThreshold] at hkthr
    omega
  -- the Euclidean envelope at the base scale
  have hcube := annealedBlock_centeredCube_le_one_add_entryDefect hdag hsK hkDelta
  have hcubedef : euclideanEntryDefect K sK k ≤ cEnt / 2 :=
    euclideanEntryDefect_le (K := K) hcEnt2 hkthr
  -- the tilt comparison
  have htilt := adaptedMean_quadratic_le_add_tiltDefect hd hg hdag hstat hl hCd hnu
    hsK hk0 hDelta hentry hsub hint
  have htiltdef : tiltDefect Cd g nu G k r ≤ cEnt / 2 :=
    tiltDefect_le hCd1 hg hnu hcEnt2 hgap
  have htilt0 : 0 ≤ tiltDefect Cd g nu G k r := tiltDefect_nonneg hCd1 hg hnu G k r
  have hquadE : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul E X) := by
    intro X
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact (hdag.refBlock_posDef X hX).le
  -- the one-sided adapted envelope at the tolerance
  have hupper : BlockMatLoewnerLE (adaptedMean P (roundedGrid l nu) r)
      (blockScale (1 + cEnt) E) := by
    intro X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
    have h1 := htilt X
    have h2 := hcube X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h2
    have h3 := mul_le_mul_of_nonneg_right
      (by linarith only [htiltdef] :
        tiltDefect Cd g nu G k r ≤ cEnt / 2) (hquadE X)
    have h4 : euclideanEntryDefect K sK k * blockVecDot X (blockMatVecMul E X) ≤
        cEnt / 2 * blockVecDot X (blockMatVecMul E X) :=
      mul_le_mul_of_nonneg_right hcubedef (hquadE X)
    nlinarith only [h1, h2, h3, h4, hquadE X]
  -- the two-sided conclusion
  have hEsymm := hdag.refBlock_isSymm
  have hEpd := hdag.refBlock_posDef
  have hEsharp : BlockMatLoewnerLE (blockSharp E) E :=
    Initialization.blockMatLoewnerLE_blockSharp_reference hdag
  have hAsymm : IsSymmetricBlockMat (adaptedMean P (roundedGrid l nu) r) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P _ r
  have hApd : BlockPosDef (adaptedMean P (roundedGrid l nu) r) :=
    Recurrence.blockPosDef_adaptedMean hq r hint
  have hAself : BlockMatLoewnerLE (blockSharp (adaptedMean P (roundedGrid l nu) r))
      (adaptedMean P (roundedGrid l nu) r) := by
    simpa only [adaptedMean] using
      Sharp.blockSharp_annealedBlock_le_of_nonempty
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq r)
        (Recurrence.adaptedCell_nonempty (roundedGrid l nu) r) hint
  have hkappa : kappaRef E ≤ 1 + 6 * sigma := by
    have h :=
      Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one_of_coarseEllipticityDagger
      hdag
    linarith only [h, hsigma]
  have hprod : (1 + cEnt) * kappaRef E ≤ 1 + nearIdentityDefect cEnt sigma := by
    rw [nearIdentityDefect]
    have hpos : (0 : ℝ) ≤ 1 + cEnt := by linarith only [hcEnt]
    nlinarith only [hkappa, hpos]
  exact near_identity_of_le_blockScale hEsymm hEpd hEsharp hAsymm hApd hAself
    hcEnt.le (nearIdentityDefect_nonneg hcEnt.le hsigma0) hupper hprod

end

end HCPolySupport.HighContrast.Quenched
