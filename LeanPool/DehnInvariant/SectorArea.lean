/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.PlaneCut
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
Lean study 3 of the shape-language canon (DICTO, 19 Nov 2026), part I: the angle evaluation.

Study 2 measured the angle of a wedge by area: `wedgeAngle T K` = 2π × (area of the wedge inside
the unit disc
of the plane perpendicular to the edge) / (area of that disc). This file proves that for the wedge
between two
planes this is the usual dihedral angle: π minus the angle between the outward normals
(`wedgeAngle_two_planes`, gap 1 of study 2).

Method. (1) In the complex plane, the sector `|arg z| ≤ β`, `|z| < 1` has area β
(`volume_sector`): Mathlib's
polar-coordinate change of variables `Complex.lintegral_comp_polarCoord_symm` turns the area into
the integral
of `r` over the rectangle `(0,1) × [-β, β]`. (2) The plane perpendicular to the edge is carried
onto the complex
plane by the linear isometry `Complex.isometryOfOrthonormal` built on the orthonormal pair
(minus the bisector of the two unit normals, their normalised difference); linear isometries keep
area
(`LinearIsometryEquiv.measurePreserving`), and the wedge goes to the sector with sin β = ‖u₁ + u₂‖
/ 2.
(3) Then π − angle(u₁, u₂) = 2β by `Real.arccos_cos`.

Mathlib has polar coordinates and the area of the disc, but a sector-area statement was not found
in the
pinned copy (grep), so it is proved here from those.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-! ### The area of a sector of the unit disc -/

lemma mul_nonpos_iff_pos {r s : ℝ} (hr : 0 < r) : r * s ≤ 0 ↔ s ≤ 0 := by
  constructor
  · intro h; by_contra hc; push Not at hc
    have := mul_pos hr hc; linarith
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hr.le h

lemma sin_nonpos_iff_of {x : ℝ} (h1 : -(2 * Real.pi) < x) (h2 : x < Real.pi) :
    Real.sin x ≤ 0 ↔ -Real.pi ≤ x ∧ x ≤ 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      have h3 : 0 < Real.sin (x + 2 * Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_add_two_pi] at h3; linarith
    · by_contra hc; push Not at hc
      have := Real.sin_pos_of_pos_of_lt_pi hc h2; linarith
  · rintro ⟨h3, h4⟩; exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h4 h3

/-- In polar coordinates the two half-plane conditions say `-β ≤ θ ≤ β`. -/
lemma sector_polar {β r θ : ℝ} (hβ0 : 0 < β) (hβ : β < Real.pi / 2) (hr : 0 < r)
    (h1 : -Real.pi < θ) (h2 : θ < Real.pi) :
    (-(Real.sin β) * (r * Real.cos θ) + Real.cos β * (r * Real.sin θ) ≤ 0 ∧
      -(Real.sin β) * (r * Real.cos θ) - Real.cos β * (r * Real.sin θ) ≤ 0) ↔ (-β ≤ θ ∧ θ ≤ β) := by
  have e1 : -(Real.sin β) * (r * Real.cos θ) + Real.cos β * (r * Real.sin θ)
      = r * Real.sin (θ - β) := by
    rw [Real.sin_sub]; ring
  have e2 : -(Real.sin β) * (r * Real.cos θ) - Real.cos β * (r * Real.sin θ) =
      r * Real.sin (-θ - β) := by
    rw [Real.sin_sub, Real.sin_neg, Real.cos_neg]; ring
  have hpi := Real.pi_pos
  rw [e1, e2, mul_nonpos_iff_pos hr, mul_nonpos_iff_pos hr,
    sin_nonpos_iff_of (by linarith) (by linarith), sin_nonpos_iff_of (by linarith) (by linarith)]
  constructor
  · rintro ⟨⟨_, h4⟩, ⟨_, h6⟩⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The sector of the open unit disc of ℂ between the directions `-β` and `β`, written with two
half-planes. -/
def sector (β : ℝ) : Set ℂ :=
  {z | (-(Real.sin β) * z.re + Real.cos β * z.im ≤ 0 ∧ -(Real.sin β) * z.re - Real.cos β * z.im
      ≤ 0) ∧
    ‖z‖ < 1}

lemma measurableSet_sector (β : ℝ) : MeasurableSet (sector β) := by
  have h1 : MeasurableSet {z : ℂ | -(Real.sin β) * z.re + Real.cos β * z.im ≤ 0} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have h2 : MeasurableSet {z : ℂ | -(Real.sin β) * z.re - Real.cos β * z.im ≤ 0} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have h3 : MeasurableSet {z : ℂ | ‖z‖ < 1} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  exact (h1.inter h2).inter h3

lemma lintegral_Ioo_id : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1 / 2) := by
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo 0 1) volume :=
    (continuous_id.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
    norm_num
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun r hr => hr.1.le

/-- **The area of a sector of the unit disc is half its angle**: the sector `|arg z| ≤ β` has area
`β`. -/
theorem volume_sector {β : ℝ} (hβ0 : 0 < β) (hβ : β < Real.pi / 2) :
    volume (sector β) = ENNReal.ofReal β := by
  have hpi := Real.pi_pos
  let F : ℝ × ℝ → ENNReal := fun p =>
    (Ioo (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal r) p.1 * (Icc (-β) β).indicator 1 p.2
  have hF : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • (sector β).indicator (1 : ℂ → ENNReal) (Complex.polarCoord.symm p)
          = F p := by
    rintro ⟨r, θ⟩ hp
    rw [Complex.polarCoord_target] at hp
    have hr : 0 < r := hp.1
    have hθ : -Real.pi < θ ∧ θ < Real.pi := hp.2
    have hmem : Complex.polarCoord.symm (r, θ) ∈ sector β ↔ (r < 1 ∧ (-β ≤ θ ∧ θ ≤ β)) := by
      have hre : (Complex.polarCoord.symm (r, θ)).re = r * Real.cos θ := by
        rw [Complex.polarCoord_symm_apply]; simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
      have him : (Complex.polarCoord.symm (r, θ)).im = r * Real.sin θ := by
        rw [Complex.polarCoord_symm_apply]; simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
      have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
        rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr
      change ((_ ∧ _) ∧ _) ↔ _
      rw [hre, him, hn, sector_polar hβ0 hβ hr hθ.1 hθ.2]
      tauto
    change ENNReal.ofReal r • (sector β).indicator (1 : ℂ → ENNReal) (Complex.polarCoord.symm (r,
        θ)) =
      (Ioo (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal r) r * (Icc (-β) β).indicator 1 θ
    by_cases hin : Complex.polarCoord.symm (r, θ) ∈ sector β
    · have h := hmem.1 hin
      rw [indicator_of_mem hin, indicator_of_mem (show r ∈ Ioo (0 : ℝ) 1 from ⟨hr, h.1⟩),
        indicator_of_mem (show θ ∈ Icc (-β) β from h.2)]
      simp
    · rw [indicator_of_notMem hin]
      by_cases h1 : r ∈ Ioo (0 : ℝ) 1
      · have h2 : θ ∉ Icc (-β) β := fun h2 => hin (hmem.2 ⟨h1.2, h2⟩)
        rw [indicator_of_notMem h2]; simp
      · rw [indicator_of_notMem h1]; simp
  have hsupp : Complex.polarCoord.target.indicator F = F := by
    rw [indicator_eq_self]
    rintro ⟨r, θ⟩ hp
    rw [Function.mem_support] at hp
    rw [Complex.polarCoord_target]
    by_contra hno
    apply hp
    change (Ioo (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal r) r * (Icc (-β) β).indicator 1 θ = 0
    by_cases h1 : r ∈ Ioo (0 : ℝ) 1
    · by_cases h2 : θ ∈ Icc (-β) β
      · exact absurd (show (r, θ) ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from
          ⟨h1.1, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩) hno
      · rw [indicator_of_notMem h2, mul_zero]
    · rw [indicator_of_notMem h1, zero_mul]
  have htm : MeasurableSet Complex.polarCoord.target := Complex.polarCoord.open_target.measurableSet
  calc volume (sector β) = ∫⁻ z, (sector β).indicator 1 z := by
        rw [lintegral_indicator_one (measurableSet_sector β)]
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (sector β).indicator (1 : ℂ → ENNReal) (Complex.polarCoord.symm p) :=
        (Complex.lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in Complex.polarCoord.target, F p := setLIntegral_congr_fun htm hF
    _ = ∫⁻ p, F p := by rw [← lintegral_indicator htm, hsupp]
    _ = (∫⁻ r, (Ioo (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal r) r) *
          ∫⁻ θ, (Icc (-β) β).indicator (1 : ℝ → ENNReal) θ := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul
          ((ENNReal.measurable_ofReal.indicator measurableSet_Ioo).aemeasurable)
          ((measurable_one.indicator measurableSet_Icc).aemeasurable)
    _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (2 * β) := by
        rw [lintegral_indicator measurableSet_Ioo, lintegral_Ioo_id,
          lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
        congr 2; ring
    _ = ENNReal.ofReal β := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-! ### Two half-spaces -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mem_cone_pair {a₁ a₂ v : E} : v ∈ cone ![a₁, a₂] Set.univ ↔ ⟪a₁, v⟫ ≤ 0 ∧ ⟪a₂, v⟫ ≤ 0 := by
  simp [cone, Fin.forall_fin_two]

lemma mem_linCone_pair {a₁ a₂ v : E} : v ∈ linCone ![a₁, a₂] Set.univ ↔ ⟪a₁, v⟫ = 0 ∧ ⟪a₂, v⟫
    = 0 := by
  rw [mem_linCone]; simp [Fin.forall_fin_two]

/-- Two independent normals: the common direction space of the two planes is a line. -/
lemma finrank_linCone_pair [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] {a₁ a₂ : E}
    (h : LinearIndependent ℝ ![a₁, a₂]) : finrank ℝ (linCone ![a₁, a₂] Set.univ) = 1 := by
  have hE : finrank ℝ E = 3 := Fact.out
  set S : Submodule ℝ E := Submodule.span ℝ (Set.range ![a₁, a₂]) with hS
  have hSf : finrank ℝ S = 2 := by rw [hS, finrank_span_eq_card h]; simp
  have hK : linCone ![a₁, a₂] Set.univ = Sᗮ := by
    ext v
    rw [mem_linCone_pair, Submodule.mem_orthogonal']
    constructor
    · rintro ⟨h1, h2⟩ u hu
      have hle : S ≤ (ℝ ∙ v)ᗮ := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
        fin_cases i
        · simpa [real_inner_comm] using h1
        · simpa [real_inner_comm] using h2
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hu)
    · intro hv
      have m1 : a₁ ∈ S := Submodule.subset_span ⟨0, rfl⟩
      have m2 : a₂ ∈ S := Submodule.subset_span ⟨1, rfl⟩
      exact ⟨by rw [real_inner_comm]; exact hv _ m1, by rw [real_inner_comm]; exact hv _ m2⟩
  have h1 := Submodule.finrank_add_finrank_orthogonal S
  rw [hK]; omega

/-- Gap 1 for unit normals. -/
theorem wedgeAngle_two_planes_unit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fact (finrank ℝ E = 3)] (u₁ u₂ : E) (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1)
    (h : LinearIndependent ℝ ![u₁, u₂]) :
    wedgeAngle (cone ![u₁, u₂] Set.univ) (linCone ![u₁, u₂] Set.univ) =
      Real.pi - InnerProductGeometry.angle u₁ u₂ := by
  have hE : finrank ℝ E = 3 := Fact.out
  have hpi := Real.pi_pos
  set K : Submodule ℝ E := linCone ![u₁, u₂] Set.univ with hKdef
  have hK1 : finrank ℝ K = 1 := finrank_linCone_pair h
  have hV : finrank ℝ Kᗮ = 2 := by
    have := Submodule.finrank_add_finrank_orthogonal K; omega
  have hpair := LinearIndependent.pair_iff.1 h
  -- inner products of the unit normals
  set g : ℝ := ⟪u₁, u₂⟫ with hg
  have i11 : ⟪u₁, u₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu₁]; norm_num
  have i22 : ⟪u₂, u₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu₂]; norm_num
  have i21 : ⟪u₂, u₁⟫ = g := real_inner_comm _ _
  -- the bisector and the difference
  set d₁ : E := u₁ + u₂ with hd₁
  set d₂ : E := u₁ - u₂ with hd₂
  have hd₁0 : d₁ ≠ 0 := by
    intro h0
    have := hpair 1 1 (by rw [one_smul, one_smul]; exact h0)
    exact one_ne_zero this.1
  have hd₂0 : d₂ ≠ 0 := by
    intro h0
    have := hpair 1 (-1) (by rw [one_smul, neg_one_smul, ← sub_eq_add_neg]; exact h0)
    exact one_ne_zero this.1
  set m : ℝ := ‖d₁‖ with hm
  set n : ℝ := ‖d₂‖ with hn
  have hm0 : 0 < m := norm_pos_iff.2 hd₁0
  have hn0 : 0 < n := norm_pos_iff.2 hd₂0
  have j11 : ⟪d₁, d₁⟫ = 2 + 2 * g := by
    rw [hd₁, inner_add_left, inner_add_right, inner_add_right, i11, i22, i21]; ring
  have j22 : ⟪d₂, d₂⟫ = 2 - 2 * g := by
    rw [hd₂, inner_sub_left, inner_sub_right, inner_sub_right, i11, i22, i21]; ring
  have j12 : ⟪d₁, d₂⟫ = 0 := by
    rw [hd₁, hd₂, inner_add_left, inner_sub_right, inner_sub_right, i11, i22, i21]; ring
  have hm2 : m ^ 2 = 2 + 2 * g := by rw [hm, ← real_inner_self_eq_norm_sq, j11]
  have hn2 : n ^ 2 = 2 - 2 * g := by rw [hn, ← real_inner_self_eq_norm_sq, j22]
  have k11 : ⟪u₁, d₁⟫ = m ^ 2 / 2 := by rw [hd₁, inner_add_right, i11, hm2]; ring
  have k12 : ⟪u₁, d₂⟫ = n ^ 2 / 2 := by rw [hd₂, inner_sub_right, i11, hn2]; ring
  have k21 : ⟪u₂, d₁⟫ = m ^ 2 / 2 := by rw [hd₁, inner_add_right, i22, i21, hm2]; ring
  have k22 : ⟪u₂, d₂⟫ = -(n ^ 2 / 2) := by rw [hd₂, inner_sub_right, i22, i21, hn2]; ring
  -- the orthonormal pair in the plane perpendicular to the edge
  have hu₁K : u₁ ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']; intro u hu; exact (mem_linCone_pair.1 hu).1
  have hu₂K : u₂ ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']; intro u hu; exact (mem_linCone_pair.1 hu).2
  set e₁ : E := (-m⁻¹) • d₁ with he₁
  set e₂ : E := n⁻¹ • d₂ with he₂
  have he₁K : e₁ ∈ Kᗮ := Kᗮ.smul_mem _ (Kᗮ.add_mem hu₁K hu₂K)
  have he₂K : e₂ ∈ Kᗮ := Kᗮ.smul_mem _ (Kᗮ.sub_mem hu₁K hu₂K)
  have o11 : ⟪e₁, e₁⟫ = 1 := by
    rw [he₁, inner_smul_left, inner_smul_right, j11, ← hm2]; simp only [conj_trivial]; field_simp
  have o22 : ⟪e₂, e₂⟫ = 1 := by
    rw [he₂, inner_smul_left, inner_smul_right, j22, ← hn2]; simp only [conj_trivial]; field_simp
  have o12 : ⟪e₁, e₂⟫ = 0 := by
    rw [he₁, he₂, inner_smul_left, inner_smul_right, j12]; simp
  let w : Fin 2 → Kᗮ := ![⟨e₁, he₁K⟩, ⟨e₂, he₂K⟩]
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact o11
    · exact o12
    · change ⟪e₂, e₁⟫ = 0
      rw [real_inner_comm]; exact o12
    · exact o22
  let B : OrthonormalBasis (Fin 2) ℝ Kᗮ :=
    (basisOfOrthonormalOfCardEqFinrank hw (by rw [hV]; simp)).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hw)
  have hB : ∀ i, B i = w i := by
    intro i
    change ((basisOfOrthonormalOfCardEqFinrank hw _).toOrthonormalBasis _) i = w i
    rw [Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  let ψ : ℂ ≃ₗᵢ[ℝ] Kᗮ := Complex.isometryOfOrthonormal B
  have hψ : ∀ z : ℂ, ((ψ z : Kᗮ) : E) = z.re • e₁ + z.im • e₂ := by
    intro z
    change ((Complex.isometryOfOrthonormal B z : Kᗮ) : E) = _
    rw [Complex.isometryOfOrthonormal_apply, hB, hB]
    rfl
  -- the angle β
  have hmn : m ^ 2 + n ^ 2 = 4 := by rw [hm2, hn2]; ring
  have hm_lt : m / 2 < 1 := by nlinarith
  set β : ℝ := Real.arcsin (m / 2) with hβdef
  have hβ0 : 0 < β := Real.arcsin_pos.2 (by positivity)
  have hβ1 : β < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hm_lt
  have hsin : Real.sin β = m / 2 := Real.sin_arcsin (by linarith) hm_lt.le
  have hcos : Real.cos β = n / 2 := by
    have hc0 : 0 ≤ Real.cos β := Real.cos_arcsin_nonneg _
    have hsq : Real.cos β ^ 2 = (n / 2) ^ 2 := by
      have := Real.sin_sq_add_cos_sq β
      rw [hsin] at this; nlinarith
    exact (sq_eq_sq₀ hc0 (by positivity)).1 hsq
  -- the wedge is carried to the sector
  have a1 : ∀ z : ℂ, ⟪u₁, z.re • e₁ + z.im • e₂⟫ = -(Real.sin β) * z.re + Real.cos β * z.im := by
    intro z
    rw [inner_add_right, he₁, he₂]
    simp only [inner_smul_right]
    rw [k11, k12, hsin, hcos]
    field_simp
  have a2 : ∀ z : ℂ, ⟪u₂, z.re • e₁ + z.im • e₂⟫ = -(Real.sin β) * z.re - Real.cos β * z.im := by
    intro z
    rw [inner_add_right, he₁, he₂]
    simp only [inner_smul_right]
    rw [k21, k22, hsin, hcos]
    field_simp
    ring
  let me : ℂ ≃ᵐ Kᗮ := ψ.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving me volume volume := ψ.measurePreserving
  have hpre : me ⁻¹' wedgeSet (cone ![u₁, u₂] Set.univ) K = sector β := by
    ext z
    change ((ψ z : Kᗮ) : E) ∈ cone ![u₁, u₂] Set.univ ∧ ‖ψ z‖ < 1 ↔ z ∈ sector β
    rw [hψ, mem_cone_pair, a1, a2, ψ.norm_map]
    rfl
  have hball : me ⁻¹' Metric.ball (0 : Kᗮ) 1 = Metric.ball (0 : ℂ) 1 := by
    ext z
    change ψ z ∈ Metric.ball (0 : Kᗮ) 1 ↔ z ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, ψ.norm_map]
  have hvol1 : volume (wedgeSet (cone ![u₁, u₂] Set.univ) K) = ENNReal.ofReal β := by
    rw [← hmp.measure_preimage_equiv, hpre, volume_sector hβ0 hβ1]
  have hvol2 : (volume (Metric.ball (0 : Kᗮ) 1)).toReal = Real.pi := by
    rw [← hmp.measure_preimage_equiv, hball, Complex.volume_ball]
    simp
  -- the angle between the normals
  have hang : InnerProductGeometry.angle u₁ u₂ = Real.pi - 2 * β := by
    unfold InnerProductGeometry.angle
    rw [hu₁, hu₂, mul_one, div_one, ← hg]
    have hgc : g = Real.cos (Real.pi - 2 * β) := by
      rw [Real.cos_pi_sub, Real.cos_two_mul, hcos]
      linarith [hn2]
    rw [hgc, Real.arccos_cos (by linarith) (by linarith)]
  simp only [wedgeAngle_formula]
  rw [hvol1, hvol2, hang, ENNReal.toReal_ofReal hβ0.le]
  field_simp
  ring

/-- Scaling the normals by positive factors changes neither the cone nor its line. -/
lemma cone_pair_smul {a₁ a₂ : E} {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    cone ![c₁ • a₁, c₂ • a₂] Set.univ = cone ![a₁, a₂] Set.univ := by
  ext v
  rw [mem_cone_pair, mem_cone_pair, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  rw [mul_nonpos_iff_pos h₁, mul_nonpos_iff_pos h₂]

lemma linCone_pair_smul {a₁ a₂ : E} {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    linCone ![c₁ • a₁, c₂ • a₂] Set.univ = linCone ![a₁, a₂] Set.univ := by
  ext v
  rw [mem_linCone_pair, mem_linCone_pair, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  rw [mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ⟨h3, h4⟩
    exact ⟨h3.resolve_left h₁.ne', h4.resolve_left h₂.ne'⟩
  · rintro ⟨h3, h4⟩; exact ⟨Or.inr h3, Or.inr h4⟩

/-- **Gap 1 of study 2, closed (angle evaluation).** Two half-spaces with outward normals `a₁`, `a₂`
(not parallel) meet in a wedge whose angle, as measured by `wedgeAngle` (area of a disc sector),
is π minus
the angle between the normals. -/
theorem wedgeAngle_two_planes [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fact (finrank ℝ E = 3)] (a₁ a₂ : E) (h : LinearIndependent ℝ ![a₁, a₂]) :
    wedgeAngle (cone ![a₁, a₂] Set.univ) (linCone ![a₁, a₂] Set.univ) =
      Real.pi - InnerProductGeometry.angle a₁ a₂ := by
  have ha₁ : a₁ ≠ 0 := by simpa using h.ne_zero 0
  have ha₂ : a₂ ≠ 0 := by simpa using h.ne_zero 1
  have n₁ : 0 < ‖a₁‖ := norm_pos_iff.2 ha₁
  have n₂ : 0 < ‖a₂‖ := norm_pos_iff.2 ha₂
  have c₁ : 0 < ‖a₁‖⁻¹ := inv_pos.2 n₁
  have c₂ : 0 < ‖a₂‖⁻¹ := inv_pos.2 n₂
  have hu : LinearIndependent ℝ ![‖a₁‖⁻¹ • a₁, ‖a₂‖⁻¹ • a₂] :=
    (LinearIndependent.pair_smul_smul_iff c₁.ne'.isUnit c₂.ne'.isUnit).2 h
  have key := wedgeAngle_two_planes_unit (‖a₁‖⁻¹ • a₁) (‖a₂‖⁻¹ • a₂)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n₁.ne'])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n₂.ne']) hu
  rw [cone_pair_smul c₁ c₂, linCone_pair_smul c₁ c₂,
    InnerProductGeometry.angle_smul_left_of_pos _ _ c₁,
    InnerProductGeometry.angle_smul_right_of_pos _ _ c₂] at key
  exact key

end DehnCanon.Library
