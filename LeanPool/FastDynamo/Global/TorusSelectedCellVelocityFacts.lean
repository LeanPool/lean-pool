/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusBackgroundVelocity
public import LeanPool.FastDynamo.Global.TorusCellPlacedCutoffs

/-!
# Velocity facts at one placed cell, in the Euclidean metric of the paper

§3.3 of the paper places the cores `C_m = supp u_m^loc` inside the pairwise disjoint cells
(buffer discs) `D(p_m, R_m)` and records, as a consequence of `eq:local-support-in-buffer`,
`supp u_m^loc ⊂ D(p_m, R_m/10)`.  The proof of `lem:parametrix-error` (§7.1) consumes that
placement through three velocity statements about the *global* field
`u = Σ_m (u_m^loc + u_m^ax)`:

* `TransverseVelocityLocalized p_n (R_n/10) (R_n/2) u` — the transverse velocity vanishes
  outside the union of the cores, the selected core lies in `D(p_n, R_n/10)` and every other
  core lies outside `closedBall(p_n, R_n/2)`;
* the agreement of `u` with the background velocity `u^bg_n = u - u_n^loc` off `closedBall(p_n,
R_n/10)`;
* the no-wrap condition for the closed three-quarter buffer disc, the support of the auxiliary
  cut-off `auxiliaryCutoff_n` of `Global/TorusChartC2AuxiliaryCutoff.lean`.

All three are proved here for an arbitrary placement `P`, with **no loss of a factor two**: the
repository's `localCoreDisk` is a product-metric ball, but the placed profile vanishes
once the *Euclidean* distance reaches `(1+h) ell_m`, and the placement's `supportFit` bounds the
number `(1+h) ell_m` by `R_m/10` regardless of the metric in which it is read.  Working with the
Euclidean support statement directly is what avoids that loss.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set
open TransverseSmoothBumpPeriodization
open scoped LineDeriv

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {sp : LocalSeedParameters} {r : ScaleRatios sp}

/-! ## The canonical representative in pair and whole-plane coordinates -/

/-- The pair-valued and whole-plane-valued canonical `(0,1]²` representatives agree. -/
theorem pairToWholePlane_transverseIocRepresentative (q : TransverseTorus) :
    pairToWholePlane (transverseIocRepresentative q) = wholePlaneIocRepresentative q := by
  ext j
  fin_cases j <;> rfl

/-- The first coordinate of the canonical representative lies in `(0,1]`. -/
theorem transverseIocRepresentative_fst_mem (q : TransverseTorus) :
    (transverseIocRepresentative q).1 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
  (AddCircle.equivIoc 1 0 (q 0)).property

/-- The second coordinate of the canonical representative lies in `(0,1]`. -/
theorem transverseIocRepresentative_snd_mem (q : TransverseTorus) :
    (transverseIocRepresentative q).2 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
  (AddCircle.equivIoc 1 0 (q 1)).property

/-- The whole-plane distance from the canonical representative to a placed centre is the
Euclidean chart distance of the corresponding pair coordinates. -/
theorem dist_wholePlaneIocRepresentative_cellCenter (f : ScaleFamily r) (m : ℕ)
    (q : TransverseTorus) :
    dist (wholePlaneIocRepresentative q) (pairToWholePlane (f.cellCenter m)) =
      pairEuclideanDist (transverseIocRepresentative q) (f.cellCenter m) := by
  rw [pairEuclideanDist_eq_dist, pairToWholePlane_transverseIocRepresentative]

/-! ## Separation of the placed centres in the Euclidean metric -/

/-- Distinct placed centres are further apart, in the paper's Euclidean metric, than the
sum of the two buffer radii (§3.3). -/
theorem bufferRadius_add_lt_pairEuclideanDist_cellCenter (f : ScaleFamily r) {n m : ℕ}
    (hnm : n ≠ m) :
    f.bufferRadius n + f.bufferRadius m <
      pairEuclideanDist (f.cellCenter n) (f.cellCenter m) := by
  have hsup : dist (f.cellCenter n) (f.cellCenter m) =
      |f.cellCenterCoordinate n - f.cellCenterCoordinate m| := by
    rw [Prod.dist_eq]
    simp [ScaleFamily.cellCenter, Real.dist_eq]
  have hle := dist_le_pairEuclideanDist (f.cellCenter n) (f.cellCenter m)
  rw [hsup] at hle
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · have := f.bufferRadii_sum_lt_centerCoordinate_gap hlt
    linarith
  · have := f.bufferRadii_sum_lt_centerCoordinate_gap hlt
    rw [abs_sub_comm] at this
    linarith

/-! ## The no-wrap condition on the closed three-quarter buffer disc -/

/-- A whole-plane point within the closed three-quarter buffer distance of the placed centre has
its coordinate pair inside the full Euclidean buffer disc of the cell. -/
theorem coordinatePair_mem_bufferDisk_of_dist_le_three_quarters {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) {x : WholePlane}
    (hx : dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤
      3 * P.scaleFamily.bufferRadius n / 4) :
    (x 0, x 1) ∈ P.scaleFamily.bufferDisk n := by
  have hpair : dist (x 0, x 1) (P.scaleFamily.cellCenter n) ≤
      dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) := by
    calc
      dist (x 0, x 1) (P.scaleFamily.cellCenter n) ≤
          ‖pairToWholePlane (x 0, x 1) -
            pairToWholePlane (P.scaleFamily.cellCenter n)‖ :=
        dist_le_norm_pairToWholePlane_sub _ _
      _ = ‖x - pairToWholePlane (P.scaleFamily.cellCenter n)‖ := by
        rw [pairToWholePlane_coordinatePair' x]
      _ = dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) := by rw [dist_eq_norm]
  change dist (x 0, x 1) (P.scaleFamily.cellCenter n) < P.scaleFamily.bufferRadius n
  have hR : 0 < P.scaleFamily.bufferRadius n := P.scaleFamily.bufferRadius_pos n
  linarith

/-- **The no-wrap hypothesis for the auxiliary cut-off `psi-tilde_n`**: the closed disc
`closedBall(p_n, 3 R_n/4)`, the support of `psi-tilde_n`, lies in the half-open unit box, because
it lies
inside the buffer disc and hence in the fixed coordinate square introduced after
`eq:chart-packing` (§3.3). -/
theorem closedThreeQuarterBufferBall_subset_iocFundamentalBox {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    closedBall (pairToWholePlane (P.scaleFamily.cellCenter n))
        (3 * P.scaleFamily.bufferRadius n / 4) ⊆ wholePlaneIocFundamentalBox := by
  intro x hx
  have hxle : dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
    simpa [mem_closedBall] using hx
  have hbuffer := coordinatePair_mem_bufferDisk_of_dist_le_three_quarters P n hxle
  have hchart := P.bufferDisk_subset_chart n hbuffer
  rcases hchart with ⟨⟨hx0lo, hx0hi⟩, ⟨hx1lo, hx1hi⟩⟩
  have hx0lo' : 0 < x 0 := by simpa using hx0lo
  have hx0hi' : x 0 < 1 / 4 := by simpa using hx0hi
  have hx1lo' : 1 / 4 < x 1 := by simpa using hx1lo
  have hx1hi' : x 1 < 3 / 4 := by simpa using hx1hi
  intro j
  fin_cases j
  · simpa using
      (show x (0 : Fin 2) ∈ Set.Ioc (0 : ℝ) (0 + 1) from ⟨hx0lo', by linarith⟩)
  · simpa using
      (show x (1 : Fin 2) ∈ Set.Ioc (0 : ℝ) (0 + 1) from ⟨by linarith, by linarith⟩)

/-! ## The Euclidean support of one placed cell -/

variable (h : PonomarenkoSmoothingWidth)

/-- The rescaled cell coordinate has norm the Euclidean chart distance divided by `ell_n`. -/
theorem norm_helicalCellCoordinate (P : TorusCellPlacement (r := r) (1 + (h : ℝ))) (n : ℕ)
    (x : ℝ × ℝ) :
    ‖helicalCellCoordinate h P n x‖ =
      pairEuclideanDist x (P.scaleFamily.cellCenter n) / P.scaleFamily.ell n := by
  have hell : 0 < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
  simp only [helicalCellCoordinate, Pi.smul_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hell), pairEuclideanDist,
    ← div_eq_inv_mul]

/-- The profile support radius is reached by the rescaled cell coordinate exactly when the
Euclidean chart distance reaches `(1+h) ell_n`. -/
theorem supportRadius_le_norm_helicalCellCoordinate (P : TorusCellPlacement (r := r)
    (1 + (h : ℝ))) (n : ℕ) {x : ℝ × ℝ}
    (hx : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      pairEuclideanDist x (P.scaleFamily.cellCenter n)) :
    1 + (h : ℝ) ≤ ‖helicalCellCoordinate h P n x‖ := by
  have hell : 0 < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
  rw [norm_helicalCellCoordinate h P n x, le_div_iff₀ hell]
  exact hx

/-- **`eq:local-support-in-buffer`, Euclidean form**: the placed local copy
vanishes once the Euclidean chart distance to the centre reaches `(1+h) ell_n`. -/
theorem parameterizedHelicalCellSource_eq_zero_of_le_pairEuclideanDist
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ))) (angularSpeed axialSpeed : ℝ) (n : ℕ)
    {x : ℝ × ℝ}
    (hx : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      pairEuclideanDist x (P.scaleFamily.cellCenter n)) :
    parameterizedHelicalCellSource h P angularSpeed axialSpeed n x = 0 := by
  simp only [parameterizedHelicalCellSource, Pi.smul_apply, Function.comp_apply]
  rw [parameterizedSmoothedVelocity_eq_zero_of_radius_le_norm h angularSpeed axialSpeed
    (supportRadius_le_norm_helicalCellCoordinate h P n hx), smul_zero]

/-- The same Euclidean support statement for the two stored first derivatives of the placed
local copy. -/
theorem parameterizedHelicalCellSourceDeriv_eq_zero_of_le_pairEuclideanDist
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ))) (angularSpeed axialSpeed : ℝ) (n : ℕ)
    (j : Fin 2) {x : ℝ × ℝ}
    (hx : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      pairEuclideanDist x (P.scaleFamily.cellCenter n)) :
    parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j x = 0 := by
  have hy : 1 + (h : ℝ) ≤ ‖helicalCellCoordinate h P n x‖ :=
    supportRadius_le_norm_helicalCellCoordinate h P n hx
  set y := helicalCellCoordinate h P n x with hydef
  apply PiLp.ext
  intro i
  change ((∂_{wholePlaneBasis j}
    (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed)) y i) = 0
  fin_cases i
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 0) = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_zero]
    simp [parameterizedRadialProfile_value_zero h hy,
      parameterizedRadialProfile_slope_zero h hy]
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 1) = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_one]
    simp [parameterizedRadialProfile_value_zero h hy,
      parameterizedRadialProfile_slope_zero h hy]
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 2) = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_two]
    simp [parameterizedRadialProfile_slope_zero h hy]

/-! ## The torus representatives of one placed cell -/

variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ))) (angularSpeed axialSpeed : ℝ)

/-- The descended cell source evaluated at a torus point is the Euclidean cell source evaluated
at the canonical `(0,1]²` representative. -/
theorem torusSource_eq_source_transverseIocRepresentative (n : ℕ) (q : TransverseTorus) :
    (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed n).torusSource q =
      parameterizedHelicalCellSource h P angularSpeed axialSpeed n
        (transverseIocRepresentative q) := by
  have hq : transverseTorusPoint (transverseIocRepresentative q) = q :=
    transverseTorusPoint_transverseIocRepresentative q
  calc (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed n).torusSource q
      = (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed n).torusSource
          (transverseTorusPoint (transverseIocRepresentative q)) := by rw [hq]
    _ = parameterizedHelicalCellSource h P angularSpeed axialSpeed n
          (transverseIocRepresentative q) :=
        EuclideanCellSourceCertificate.torusSource_transverseTorusPoint_eq_source_of_mem_Ioc _
          (transverseIocRepresentative_fst_mem q) (transverseIocRepresentative_snd_mem q)

/-- The same identity for each descended first derivative of a placed cell. -/
theorem torusFirstDerivative_eq_firstDerivative_transverseIocRepresentative (n : ℕ) (j : Fin 2)
    (q : TransverseTorus) :
    (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
        n).torusFirstDerivative j q =
      parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j
        (transverseIocRepresentative q) := by
  have hq : transverseTorusPoint (transverseIocRepresentative q) = q :=
    transverseTorusPoint_transverseIocRepresentative q
  calc (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
          n).torusFirstDerivative j q
      = (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
          n).torusFirstDerivative j
            (transverseTorusPoint (transverseIocRepresentative q)) := by rw [hq]
    _ = parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j
          (transverseIocRepresentative q) :=
        (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
            n).torusFirstDerivative_transverseTorusPoint_eq_firstDerivative_of_mem_Ioc
          j (transverseIocRepresentative_fst_mem q) (transverseIocRepresentative_snd_mem q)

/-- The descended cell source vanishes at every torus point whose canonical representative is
Euclidean-far from the placed centre. -/
theorem torusSource_eq_zero_of_le_dist (n : ℕ) {q : TransverseTorus}
    (hq : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      dist (wholePlaneIocRepresentative q)
        (pairToWholePlane (P.scaleFamily.cellCenter n))) :
    (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed n).torusSource q
      = 0 := by
  rw [torusSource_eq_source_transverseIocRepresentative h P angularSpeed axialSpeed n q]
  refine parameterizedHelicalCellSource_eq_zero_of_le_pairEuclideanDist h P angularSpeed
    axialSpeed n ?_
  rwa [← dist_wholePlaneIocRepresentative_cellCenter P.scaleFamily n q]

/-- The descended cell derivative vanishes at every torus point whose canonical representative
is Euclidean-far from the placed centre. -/
theorem torusFirstDerivative_eq_zero_of_le_dist (n : ℕ) (j : Fin 2) {q : TransverseTorus}
    (hq : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      dist (wholePlaneIocRepresentative q)
        (pairToWholePlane (P.scaleFamily.cellCenter n))) :
    (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      n).torusFirstDerivative j q = 0 := by
  rw [torusFirstDerivative_eq_firstDerivative_transverseIocRepresentative h P angularSpeed
    axialSpeed n j q]
  refine parameterizedHelicalCellSourceDeriv_eq_zero_of_le_pairEuclideanDist h P angularSpeed
    axialSpeed n j ?_
  rwa [← dist_wholePlaneIocRepresentative_cellCenter P.scaleFamily n q]

/-- A point at which the placed cell `n` is nonzero lies strictly inside the tenth buffer disc
of that cell: this is `eq:local-support-in-buffer` read in the Euclidean metric. -/
theorem dist_lt_tenth_bufferRadius_of_torusSource_ne_zero (n : ℕ) {q : TransverseTorus}
    (hq : (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      n).torusSource q ≠ 0) :
    dist (wholePlaneIocRepresentative q) (pairToWholePlane (P.scaleFamily.cellCenter n)) <
      P.scaleFamily.bufferRadius n / 10 := by
  by_contra hcon
  exact hq (torusSource_eq_zero_of_le_dist h P angularSpeed axialSpeed n
    (le_trans (le_of_lt (P.supportFit n)) (not_lt.mp hcon)))

/-- A point at which a *different* placed cell is nonzero lies strictly outside the closed
buffer disc of the selected cell: the buffer discs are pairwise disjoint (§3.3) and
each core occupies at most a tenth of its own buffer. -/
theorem bufferRadius_lt_dist_of_ne_of_torusSource_ne_zero {n m : ℕ} (hmn : m ≠ n)
    {q : TransverseTorus}
    (hq : (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      m).torusSource q ≠ 0) :
    P.scaleFamily.bufferRadius n <
      dist (wholePlaneIocRepresentative q) (pairToWholePlane (P.scaleFamily.cellCenter n)) := by
  have hm := dist_lt_tenth_bufferRadius_of_torusSource_ne_zero h P angularSpeed axialSpeed m hq
  have hsep := bufferRadius_add_lt_pairEuclideanDist_cellCenter P.scaleFamily (Ne.symm hmn)
  rw [pairEuclideanDist_eq_dist] at hsep
  have htri : dist (pairToWholePlane (P.scaleFamily.cellCenter n))
        (pairToWholePlane (P.scaleFamily.cellCenter m)) ≤
      dist (pairToWholePlane (P.scaleFamily.cellCenter n)) (wholePlaneIocRepresentative q) +
        dist (wholePlaneIocRepresentative q)
          (pairToWholePlane (P.scaleFamily.cellCenter m)) :=
    dist_triangle _ _ _
  rw [dist_comm (pairToWholePlane (P.scaleFamily.cellCenter n))
    (wholePlaneIocRepresentative q)] at htri
  have hRm : 0 < P.scaleFamily.bufferRadius m := P.scaleFamily.bufferRadius_pos m
  linarith

/-! ## The assembled helical field away from every core -/

/-- If every placed cell vanishes at a torus point, so does the assembled helical velocity. -/
theorem parameterizedHelicalGlobalTorusSource_eq_zero_of_forall_cell {q : TransverseTorus}
    (hq : ∀ m : ℕ, (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      m).torusSource q = 0) :
    parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q = 0 := by
  by_cases hb : ∃ m : ℕ, q ∈ P.torusBufferDisk m
  · obtain ⟨m, hm⟩ := hb
    rw [parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer h P angularSpeed axialSpeed
      hm]
    exact hq m
  · exact parameterizedHelicalGlobalTorusSource_eq_zero_of_outside_buffers h P angularSpeed
      axialSpeed (not_exists.mp hb)

/-- **The paper's localization dichotomy at the cell `n`**: at every torus point the
assembled helical velocity either vanishes, or its canonical representative sits in the tenth
buffer disc of the selected cell, or strictly outside the selected buffer disc. -/
theorem parameterizedHelicalGlobalTorusSource_dichotomy (n : ℕ) (q : TransverseTorus) :
    parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q = 0 ∨
      dist (wholePlaneIocRepresentative q)
          (pairToWholePlane (P.scaleFamily.cellCenter n)) <
        P.scaleFamily.bufferRadius n / 10 ∨
      P.scaleFamily.bufferRadius n <
        dist (wholePlaneIocRepresentative q)
          (pairToWholePlane (P.scaleFamily.cellCenter n)) := by
  by_cases hall : ∀ m : ℕ, (parameterizedHelicalEuclideanCellCertificate h P angularSpeed
      axialSpeed m).torusSource q = 0
  · exact Or.inl (parameterizedHelicalGlobalTorusSource_eq_zero_of_forall_cell h P angularSpeed
      axialSpeed hall)
  · obtain ⟨m, hm⟩ := not_forall.mp hall
    by_cases hmn : m = n
    · subst hmn
      exact Or.inr (Or.inl (dist_lt_tenth_bufferRadius_of_torusSource_ne_zero h P angularSpeed
        axialSpeed m hm))
    · exact Or.inr (Or.inr (bufferRadius_lt_dist_of_ne_of_torusSource_ne_zero h P angularSpeed
        axialSpeed hmn hm))

/-! ## Pointwise representatives of the global velocity -/

/-- Every scalar coordinate of the global velocity `u` is represented a.e. by the corresponding
coordinate of the pointwise field `parameterizedFullGlobalTorusSource` (`eq:global-u`). -/
theorem transverseW1InfComplexValueCoord_parameterizedFullGlobalW1Inf_coe_ae (tau : ℝ)
    (htau : 0 ≤ tau) (i : Fin 3) :
    (transverseW1InfComplexValueCoordLInf i
        (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) :
      TransverseTorus → ℂ) =ᵐ[transverseMeasure] fun q ↦
      parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau q i := by
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (transverseW1InfComplexValueLInf
        (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)),
    transverseW1InfComplexValue_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau] with q hproj hvalue
  calc ((transverseCoordLInf i (transverseW1InfComplexValueLInf
        (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)) :
          TransverseScalarLInf) : TransverseTorus → ℂ) q
      = EuclideanSpace.proj i ((transverseW1InfComplexValueLInf
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) :
            TransverseTorus → C3) q) := hproj
    _ = parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau q i := by
        rw [hvalue]
        rfl

/-- The horizontal velocity gradient coefficient of `u` is represented a.e. by the horizontal
projection of the pointwise derivative. -/
theorem transverseW1InfHorizontalDeriv_parameterizedFullGlobalW1Inf_coe_ae (tau : ℝ)
    (htau : 0 ≤ tau) (j : Fin 2) :
    (transverseW1InfHorizontalDerivLInf j
        (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) :
      TransverseTorus → C2) =ᵐ[transverseMeasure] fun q ↦
      horizontalProjPoint
        (parameterizedFullGlobalTorusFirstDerivative h P angularSpeed axialSpeed tau j q) := by
  filter_upwards [horizontalProjLInf_coe_ae (transverseW1InfComplexDerivLInf j
      (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)),
    transverseW1InfComplexDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau j] with q hproj hderiv
  change ((horizontalProjLInf (transverseW1InfComplexDerivLInf j
      (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)) :
        TransverseC2LInf) : TransverseTorus → C2) q = _
  rw [hproj, hderiv]

/-- Each horizontal coordinate of the global velocity equals that of the assembled helical
field: the added axial velocities are purely `e₃`-valued (`eq:axial-offset`). -/
theorem parameterizedFullGlobalTorusSource_castSucc_eq (tau : ℝ) (i : Fin 2)
    (q : TransverseTorus) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau q i.castSucc =
      parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q i.castSucc := by
  rw [parameterizedFullGlobalTorusSource]
  have haxial : complexifyR3 (P.axialOffsetGlobalTorus tau q) i.castSucc = 0 := by
    simp [complexifyR3_apply,
      P.axialOffsetGlobalTorus_apply_eq_zero_of_ne_two tau q (castSucc_ne_two i)]
  simp [haxial]

/-! ## `TransverseVelocityLocalized` at the selected cell -/

/-- **The first velocity hypothesis of §7** ("the horizontal velocity vanishes on the transition
regions of both output cut-offs", proof of `lem:parametrix-error`): almost every torus point either
carries vanishing transverse velocity, or has its canonical representative strictly inside the
selected cell's own core disc `D(p_n, R_n/10)`, or strictly outside the selected buffer disc
`closedBall(p_n, R_n/2)`.  The inner radius `R_n/10` is the binding one: it is the plateau of the
background cut-off `chi_n`. -/
theorem transverseVelocityLocalized_parameterizedFullGlobalW1Inf (tau : ℝ) (htau : 0 ≤ tau)
    (n : ℕ) :
    TorusPlacedCutoffC2.TransverseVelocityLocalized
      (pairToWholePlane (P.scaleFamily.cellCenter n))
      (P.scaleFamily.bufferRadius n / 10) (P.scaleFamily.bufferRadius n / 2)
      (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) := by
  intro j
  filter_upwards [transverseW1InfComplexValueCoord_parameterizedFullGlobalW1Inf_coe_ae
    h P angularSpeed axialSpeed tau htau j.castSucc] with q hq
  rcases parameterizedHelicalGlobalTorusSource_dichotomy h P angularSpeed axialSpeed n q with
    hzero | hin | hout
  · refine Or.inl ?_
    rw [hq, parameterizedFullGlobalTorusSource_castSucc_eq h P angularSpeed axialSpeed tau j q,
      hzero]
    rfl
  · exact Or.inr (Or.inl hin)
  · refine Or.inr (Or.inr ?_)
    have hR : 0 < P.scaleFamily.bufferRadius n := P.scaleFamily.bufferRadius_pos n
    linarith

/-! ## Agreement with the background velocity off the selected core -/

/-- Where the selected cell vanishes, the global velocity and the background velocity
`u^bg_n = u - u_n^loc` have the same pointwise representative (`eq:background-velocity`). -/
theorem parameterizedFullGlobalTorusSource_eq_selectedBackground_of_cell_eq_zero (tau : ℝ)
    (n : ℕ) {q : TransverseTorus}
    (hq : (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      n).torusSource q = 0) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau q =
      selectedBackgroundTorusSource h P angularSpeed axialSpeed tau n q := by
  rw [selectedBackgroundTorusSource, selectedBackgroundHelicalSource, hq, sub_zero,
    parameterizedFullGlobalTorusSource]

/-- The derivative version of the previous identity. -/
theorem parameterizedFullGlobalTorusFirstDerivative_eq_selectedBackground_of_cell_eq_zero
    (tau : ℝ) (n : ℕ) (j : Fin 2) {q : TransverseTorus}
    (hq : (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      n).torusFirstDerivative j q = 0) :
    parameterizedFullGlobalTorusFirstDerivative h P angularSpeed axialSpeed tau j q =
      selectedBackgroundTorusFirstDerivative h P angularSpeed axialSpeed tau n j q := by
  rw [selectedBackgroundTorusFirstDerivative, selectedBackgroundHelicalFirstDerivative, hq,
    sub_zero, parameterizedFullGlobalTorusFirstDerivative]

/-- **The `backgroundAgreement` value hypothesis of §7** (proof of `lem:parametrix-error`): off
the closed core
disc `closedBall(p_n, R_n/10)` every scalar coordinate of the global velocity agrees with that of
the
background velocity, because only the selected cell was removed. -/
theorem value_agrees_selectedBackgroundVelocity_off_core (tau : ℝ) (htau : 0 ≤ tau) (n : ℕ)
    (i : Fin 3) :
    ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q)
          (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤
        P.scaleFamily.bufferRadius n / 10 ∨
      (transverseW1InfComplexValueCoordLInf i
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)) q =
        (transverseW1InfComplexValueCoordLInf i
          (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) q := by
  filter_upwards [transverseW1InfComplexValueCoord_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau i,
    transverseW1InfComplexValueCoord_selectedBackgroundVelocity_coe_ae
      h P angularSpeed axialSpeed tau htau n i] with q hfull hback
  by_cases hdist : dist (wholePlaneIocRepresentative q)
      (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤ P.scaleFamily.bufferRadius n / 10
  · exact Or.inl hdist
  · refine Or.inr ?_
    have hcell : (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
        n).torusSource q = 0 :=
      torusSource_eq_zero_of_le_dist h P angularSpeed axialSpeed n
        (le_trans (le_of_lt (P.supportFit n)) (le_of_lt (not_le.mp hdist)))
    rw [hfull, hback,
      parameterizedFullGlobalTorusSource_eq_selectedBackground_of_cell_eq_zero
        h P angularSpeed axialSpeed tau n hcell]

/-- **The `backgroundAgreement` gradient hypothesis of §7** (proof of `lem:parametrix-error`):
off the closed core
disc the two horizontal gradient coefficients agree. -/
theorem deriv_agrees_selectedBackgroundVelocity_off_core (tau : ℝ) (htau : 0 ≤ tau) (n : ℕ)
    (j : Fin 2) :
    ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q)
          (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤
        P.scaleFamily.bufferRadius n / 10 ∨
      (transverseW1InfHorizontalDerivLInf j
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)) q =
        (transverseW1InfHorizontalDerivLInf j
          (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) q := by
  filter_upwards [transverseW1InfHorizontalDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau j,
    transverseW1InfHorizontalDeriv_selectedBackgroundVelocity_coe_ae
      h P angularSpeed axialSpeed tau htau n j] with q hfull hback
  by_cases hdist : dist (wholePlaneIocRepresentative q)
      (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤ P.scaleFamily.bufferRadius n / 10
  · exact Or.inl hdist
  · refine Or.inr ?_
    have hcell : (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
        n).torusFirstDerivative j q = 0 :=
      torusFirstDerivative_eq_zero_of_le_dist h P angularSpeed axialSpeed n j
        (le_trans (le_of_lt (P.supportFit n)) (le_of_lt (not_le.mp hdist)))
    rw [hfull, hback,
      parameterizedFullGlobalTorusFirstDerivative_eq_selectedBackground_of_cell_eq_zero
        h P angularSpeed axialSpeed tau n j hcell]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
