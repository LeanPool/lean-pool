/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty

/-!
# High-contrast homogenization: Analytic.ClassPairing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# From class membership to absolute convergence of the flux pairing

Chaining the finite weighted energy of the coefficient-Sobolev classes through
the two-sided energy comparison puts the weak gradient in `L²`, which is exactly
what the absolute convergence of the flux pairing needs.  No integrability side
condition appears in the classes, and none has to be added where the weak
interior equation of `t.random.homogenization` is asserted
of a member of one of them.

Three readings are covered: `H¹_a(V)` on a bounded `V`; `H¹_{a,0}(V)` on an
arbitrary measurable `V`; and, at `V = ℝ^d`, the local class `H¹_{s,loc}(ℝ^d)`
through which the Liouville space
`e.random.liouville.growth` reads the
equation.  A fourth reading is the affine one of
`e.random.dirichlet`, which carries
membership of the *shifted* pair together with an essential bound on the
gradient of the boundary datum; the two together put the unshifted gradient in
`L²`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ### The chain: class membership implies absolute convergence of the pairing -/

/-- **The chain, for `H¹_a` on a bounded `V`.**  Membership in the class forces
finite weighted energy, hence `Du ∈ L²(V)`, hence absolute convergence of every
weak pairing of `Du` against a local test.  No integrability side condition
appears in the class, and none is needed at the statement. -/
theorem integrableOn_weakPairing_of_memH1a {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V) (hVb : Bornology.IsBounded V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V))
    (hu : MemH1a b V u Du) {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) V
      volume :=
  integrableOn_weakPairing hV hbmeas
    (ae_abs_entry_le_of_ae_isEllipticMatrix hlam hle hell) hφ hDmeas
    (integrableOn_vecNormSq_of_sEnergyOn_ne_top hlam hell hDmeas
      (sEnergyOn_ne_top_of_memH1a hlam hell hVb hu))

/-- **The chain, for `H¹_{a,0}` on an arbitrary `V`.** -/
theorem integrableOn_weakPairing_of_memH1a0 {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V))
    (hu : MemH1a0 b V u Du) {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) V
      volume :=
  integrableOn_weakPairing hV hbmeas
    (ae_abs_entry_le_of_ae_isEllipticMatrix hlam hle hell) hφ hDmeas
    (integrableOn_vecNormSq_of_sEnergyOn_ne_top hlam hell hDmeas
      (sEnergyOn_ne_top_of_memH1a0 hlam hell hu))

/-- **The design justification for `IsWeakSolutionOn` on the `H¹_a` class.** -/
theorem isWeakSolutionOn_iff_of_memH1a {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V) (hVb : Bornology.IsBounded V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V))
    (hu : MemH1a b V u Du) :
    IsWeakSolutionOn b V Du ↔
      ∀ φ : Vec d → ℝ, IsLocalTest V φ →
        ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (Du x)) ∂volume = 0 :=
  ⟨fun h φ hφ => (h φ hφ).2,
   fun h φ hφ =>
     ⟨integrableOn_weakPairing_of_memH1a hlam hle hell hV hVb hbmeas hDmeas hu hφ,
      h φ hφ⟩⟩

/-! ### The chain for the affine (Dirichlet) clause

The estimate `e.random.dirichlet` carries
`MemH1a0 b U (u - g₀) (Du - Dg)` for the *shifted* pair, together with an
essential bound on `Dg` on the bounded cell `U`.  Those two are enough for
`Du ∈ L²(U)`, hence for absolute convergence of the pairing that
`IsWeakSolutionOn b U Du` asserts. -/

/-- **The chain for the Dirichlet clause**: shifted class membership plus the
clause's own essential bound on the boundary datum give `Du ∈ L²(V)`. -/
theorem integrableOn_vecNormSq_of_memH1a0_sub {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u g : Vec d → ℝ} {Du Dg : Vec d → Vec d}
    {L : ℝ}
    (hDg : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)),
      Real.sqrt (vecNormSq (Dg x)) ≤ L)
    (hDgmeas : ∀ j, AEStronglyMeasurable (fun x => Dg x j) (volume.restrict V))
    (hDumeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V))
    (hu : MemH1a0 b V (fun x => u x - g x) (fun x => Du x - Dg x)) :
    IntegrableOn (fun x => vecNormSq (Du x)) V volume := by
  have hD : (∫⁻ x in V, ENNReal.ofReal (vecNormSq (Du x - Dg x)) ∂volume) ≠ ⊤ :=
    (sEnergyOn_ne_top_iff hlam hell _).1 (sEnergyOn_ne_top_of_memH1a0 hlam hell hu)
  have hG : (∫⁻ x in V, ENNReal.ofReal (vecNormSq (Dg x)) ∂volume) ≠ ⊤ := by
    refine lintegral_ofReal_vecNormSq_ne_top_of_ae_bounded (L := L ^ 2) hVb ?_
    filter_upwards [hDg] with x hx
    exact vecNormSq_le_sq_of_sqrt_le hx
  have hGmeas : AEMeasurable (fun x => ENNReal.ofReal (vecNormSq (Dg x)))
      (volume.restrict V) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aestronglyMeasurable_vecNormSq hDgmeas).aemeasurable
  exact (integrableOn_vecNormSq_iff_lintegral_ne_top hDumeas).2
    (lintegral_ofReal_vecNormSq_ne_top_of_add hGmeas hG hD)

/-- **Absolute convergence of the pairing for the Dirichlet clause.** -/
theorem integrableOn_weakPairing_of_memH1a0_sub {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hV : MeasurableSet V) (hVb : Bornology.IsBounded V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    {u g : Vec d → ℝ} {Du Dg : Vec d → Vec d} {L : ℝ}
    (hDg : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)),
      Real.sqrt (vecNormSq (Dg x)) ≤ L)
    (hDgmeas : ∀ j, AEStronglyMeasurable (fun x => Dg x j) (volume.restrict V))
    (hDumeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V))
    (hu : MemH1a0 b V (fun x => u x - g x) (fun x => Du x - Dg x))
    {φ : Vec d → ℝ} (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) V
      volume :=
  integrableOn_weakPairing hV hbmeas
    (ae_abs_entry_le_of_ae_isEllipticMatrix hlam hle hell) hφ hDumeas
    (integrableOn_vecNormSq_of_memH1a0_sub hlam hell hVb hDg hDgmeas hDumeas hu)

/-! ### The chain at `V = Set.univ`, through `H¹_{s,loc}`

The Liouville space `e.random.liouville.growth`
asserts `IsWeakSolutionOn b Set.univ Dv` for a pair that also lies in
`MemH1sLoc b v Dv`.  No global `L²` bound is available there, but
`MemH1sLoc` gives finite weighted energy on every centered Euclidean ball, and
every compact set sits inside such a ball; so the local `L²` hypothesis of
`integrableOn_weakPairing_of_integrableOn_compacts` is derivable. -/

/-- Every compact subset of `ℝ^d` sits inside a centered Euclidean ball. -/
theorem exists_euclideanBall_superset_of_isCompact {K : Set (Vec d)}
    (hK : IsCompact K) : ∃ R : ℝ, 0 < R ∧ K ⊆ euclideanBall d R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  set r' : ℝ := max r 0 with hr'def
  have hr'0 : (0 : ℝ) ≤ r' := le_max_right _ _
  have hKr' : ∀ x ∈ K, ∀ i, |x i| ≤ r' := by
    intro x hx i
    have hxr : ‖x‖ ≤ r' := by
      have := Metric.mem_closedBall.1 (hr hx)
      rw [dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hxr
  refine ⟨((d : ℝ) + 1) * (r' + 1), by positivity, fun x hx => ?_⟩
  have hsum : vecNormSq x ≤ (d : ℝ) * r' ^ 2 := by
    have : ∀ i : Fin d, x i * x i ≤ r' ^ 2 := by
      intro i
      have h := hKr' x hx i
      nlinarith only [abs_nonneg (x i), sq_abs (x i), h]
    calc vecNormSq x = ∑ i, x i * x i := rfl
      _ ≤ ∑ _i : Fin d, r' ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = (d : ℝ) * r' ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlt : (d : ℝ) * r' ^ 2 < (((d : ℝ) + 1) * (r' + 1)) ^ 2 := by
    nlinarith only [sq_nonneg r', mul_nonneg hd0 hr'0, hd0, hr'0]
  simp only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]
  exact lt_of_le_of_lt hsum hlt

/-- **The `H¹_{s,loc}` class gives local square integrability of the weak
gradient on every compact set**, with that set's ellipticity constants. -/
theorem integrableOn_vecNormSq_isCompact_of_memH1sLoc {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Dv x j) volume)
    (hv : MemH1sLoc b v Dv) {K : Set (Vec d)} (hK : IsCompact K) :
    IntegrableOn (fun x => vecNormSq (Dv x)) K volume := by
  obtain ⟨R, hR, hKR⟩ := exists_euclideanBall_superset_of_isCompact hK
  obtain ⟨lam, Lam, hlam, -, hell⟩ :=
    hb.exists_ae_isEllipticMatrix_euclideanBall hR
  have hball := (sEnergyOn_ne_top_iff_restrict (Lam := Lam) hlam hell Dv).1
    (sEnergyOn_ne_top_of_memH1sLoc hb hv hR)
  refine (integrableOn_vecNormSq_iff_lintegral_ne_top
    (fun j => (hDmeas j).restrict)).2 ?_
  exact ne_top_of_le_ne_top hball
    (lintegral_mono' (Measure.restrict_mono hKR le_rfl) le_rfl)

/-- **The chain at `V = Set.univ`, for the Liouville class.**  Membership in
`MemH1sLoc` makes the integrability conjunct of `IsWeakSolutionOn b Set.univ Dv`
derivable, so it is a consequence of the class rather than a further hypothesis
imposed on it. -/
theorem isWeakSolutionOn_univ_iff_of_memH1sLoc {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) volume)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Dv x j) volume)
    (hv : MemH1sLoc b v Dv) :
    IsWeakSolutionOn b Set.univ Dv ↔
      ∀ φ : Vec d → ℝ, IsLocalTest Set.univ φ →
        ∫ x in Set.univ, vecDot (smoothGrad φ x) (matVecMul (b x) (Dv x))
          ∂volume = 0 := by
  have hbdd : ∀ K : Set (Vec d), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume.restrict K, ∀ i j, |b x i j| ≤ M := by
    intro K hK
    obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
      hb.exists_ae_isEllipticMatrix_isCompact hK
    exact ae_abs_entry_le_isCompact_of_ae_isEllipticMatrix_restrict hlam hle hell
  refine ⟨fun h φ hφ => (h φ hφ).2, fun h φ hφ => ⟨?_, h φ hφ⟩⟩
  refine integrableOn_weakPairing_of_integrableOn_compacts_of_locallyBounded
    MeasurableSet.univ (fun i j => (hbmeas i j).restrict) hbdd hφ
    (fun j => (hDmeas j).restrict) ?_
  intro K hKc _
  exact integrableOn_vecNormSq_isCompact_of_memH1sLoc hb hDmeas hv hKc

end

end HighContrast
end HCPolySupport
