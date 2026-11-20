/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusGlobalVelocityRegularity
public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus

/-!
# The torus-side global velocity is Lipschitz, and periodised

`FastDynamo/Global/TorusGlobalVelocityRegularity.lean` proves that the chart-side representative

`U = parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau : ℝ × ℝ → R3`

is `LipschitzWith (Real.toNNReal (globalVelocityLipschitzBound …))`, that it vanishes outside the
pairwise disjoint buffer discs, that it is differentiable everywhere, smooth away from the
accumulation point `p_∞ = (0, 1/2)`, and that its derivative is discontinuous there.
`FastDynamo/Analysis/LiteralThreeTorus.lean` supplies the descent machinery for `ℤ²`-periodic
Lipschitz maps.  This module joins the two.

Since all buffer discs lie inside `ScaleFamily.placementChart = Ioo 0 (1/4) ×ˢ Ioo (1/4) (3/4)`,
the field `U` is supported in the *open unit box*, so distinct integer translates of a point can
never both lie in its support.  Consequently the periodisation

`Uper x = ∑' k : ℤ × ℤ, U (x - (k₁, k₂))`

has at most one nonzero term at every point; it is `ℤ²`-periodic, agrees with `U` on the
fundamental box `(0,1]²`, and is Lipschitz with twice the constant of `U` (the factor two is the
price of the two competing translates in the estimate
`‖U(x - k) - U(y - k')‖ ≤ ‖U(x - k) - U(y - k)‖ + ‖U(x - k') - U(y - k')‖`).  Because the chart is
a *proper* subbox of the unit box, more is true: near every point of the plane the series reduces
to a *single* translate, on a fixed open box, and at `p_∞` that translate is the trivial one.  So
`Uper` coincides with `U` on a neighbourhood of `p_∞`, and the whole qualitative package of
`TorusGlobalVelocityRegularity` transfers from `U` to `Uper` — which, unlike `U`, is the pullback
of the torus-side representative along the quotient map at *every* point of the plane.

The first half of the module develops this periodisation for an arbitrary field on the plane
(`namespace UnitBoxPeriodization`, kept out of the root namespace because the names are generic);
the second half applies it to the global velocity and identifies the descent of `Uper` with
`parameterizedFullGlobalRealTorusSource`, yielding

* `lipschitzWith_parameterizedFullGlobalRealTorusSource`, on the transverse two-torus,
* `lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource`, on `Torus 3`, and
* the differentiability, smoothness and non-`C¹` statements for the periodised representative.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter
open scoped NNReal Topology

/-! The lemmas of this section are stated for an arbitrary normed-group-valued field on the plane.
Their names are generic, so they live in the `UnitBoxPeriodization` namespace rather than in the
root namespace of the development. -/

namespace UnitBoxPeriodization

variable {F : Type*} [NormedAddCommGroup F]

/-- A field on the Euclidean plane is *supported in the open unit box* when it vanishes outside
the open square `(0,1) × (0,1)`. -/
def SupportedInOpenUnitBox (f : ℝ × ℝ → F) : Prop :=
  ∀ x : ℝ × ℝ, f x ≠ 0 → x.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ x.2 ∈ Set.Ioo (0 : ℝ) 1

/-- A field on the Euclidean plane is *supported in the placement chart* when it vanishes outside
`ScaleFamily.placementChart = Ioo 0 (1/4) ×ˢ Ioo (1/4) (3/4)`.  This is the sharper support
property of the construction's global velocity, and the one that makes the periodisation locally
equal to a single translate. -/
def SupportedInPlacementChart (f : ℝ × ℝ → F) : Prop :=
  ∀ x : ℝ × ℝ, f x ≠ 0 → x ∈ ScaleFamily.placementChart

/-- The placement chart is a subbox of the open unit box, so the sharper support property implies
the weaker one. -/
theorem SupportedInPlacementChart.supportedInOpenUnitBox {f : ℝ × ℝ → F}
    (hf : SupportedInPlacementChart f) : SupportedInOpenUnitBox f := by
  intro x hx
  obtain ⟨h1, h2⟩ := hf x hx
  simp only [Set.mem_Ioo] at h1 h2 ⊢
  exact ⟨⟨h1.1, by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

/-- The `ℤ²`-periodisation of a field on the plane: the sum of all its integer translates.  For a
field supported in the open unit box at most one summand is nonzero at each point, so the series
is trivially well defined. -/
def periodization (f : ℝ × ℝ → F) (x : ℝ × ℝ) : F :=
  ∑' k : ℤ × ℤ, f (x - ((k.1 : ℝ), (k.2 : ℝ)))

/-- Two integer translates of one point cannot both lie in the support of a field supported in the
open unit box: the periodisation has at most one nonzero term. -/
theorem eq_of_sub_intCast_ne_zero {f : ℝ × ℝ → F} (hf : SupportedInOpenUnitBox f) {x : ℝ × ℝ}
    {k k' : ℤ × ℤ} (hk : f (x - ((k.1 : ℝ), (k.2 : ℝ))) ≠ 0)
    (hk' : f (x - ((k'.1 : ℝ), (k'.2 : ℝ))) ≠ 0) : k = k' := by
  obtain ⟨hk1, hk2⟩ := hf _ hk
  obtain ⟨hk1', hk2'⟩ := hf _ hk'
  simp only [Prod.fst_sub, Prod.snd_sub, Set.mem_Ioo] at hk1 hk2 hk1' hk2'
  refine Prod.ext ?_ ?_
  · have hlt : ((k.1 - k'.1 : ℤ) : ℝ) < 1 := by
      push_cast
      linarith [hk1.1, hk1'.2]
    have hgt : ((-1 : ℤ) : ℝ) < ((k.1 - k'.1 : ℤ) : ℝ) := by
      push_cast
      linarith [hk1.2, hk1'.1]
    have hlt' : k.1 - k'.1 < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < k.1 - k'.1 := by exact_mod_cast hgt
    omega
  · have hlt : ((k.2 - k'.2 : ℤ) : ℝ) < 1 := by
      push_cast
      linarith [hk2.1, hk2'.2]
    have hgt : ((-1 : ℤ) : ℝ) < ((k.2 - k'.2 : ℤ) : ℝ) := by
      push_cast
      linarith [hk2.2, hk2'.1]
    have hlt' : k.2 - k'.2 < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < k.2 - k'.2 := by exact_mod_cast hgt
    omega

/-- Whenever one integer translate carries a nonzero value, the periodisation is exactly that
value. -/
theorem periodization_eq_of_ne_zero {f : ℝ × ℝ → F} (hf : SupportedInOpenUnitBox f)
    {x : ℝ × ℝ} {k : ℤ × ℤ} (hk : f (x - ((k.1 : ℝ), (k.2 : ℝ))) ≠ 0) :
    periodization f x = f (x - ((k.1 : ℝ), (k.2 : ℝ))) := by
  unfold periodization
  refine tsum_eq_single k fun k' hk' => ?_
  by_contra hne
  exact hk' (eq_of_sub_intCast_ne_zero hf hne hk)

/-- If every integer translate carries the value zero, so does the periodisation. -/
theorem periodization_eq_zero {f : ℝ × ℝ → F} {x : ℝ × ℝ}
    (hzero : ∀ k : ℤ × ℤ, f (x - ((k.1 : ℝ), (k.2 : ℝ))) = 0) :
    periodization f x = 0 := by
  unfold periodization
  simp_rw [hzero]
  exact tsum_zero

/-- The periodisation of a field supported in the open unit box is, at every point, the value at a
single integer translate, every other translate carrying the value zero.  This is the precise form
of "the defining series has at most one nonzero term". -/
theorem exists_periodization_eq {f : ℝ × ℝ → F} (hf : SupportedInOpenUnitBox f) (x : ℝ × ℝ) :
    ∃ k : ℤ × ℤ, periodization f x = f (x - ((k.1 : ℝ), (k.2 : ℝ))) ∧
      ∀ k' : ℤ × ℤ, k' ≠ k → f (x - ((k'.1 : ℝ), (k'.2 : ℝ))) = 0 := by
  by_cases hex : ∃ k : ℤ × ℤ, f (x - ((k.1 : ℝ), (k.2 : ℝ))) ≠ 0
  · obtain ⟨k, hk⟩ := hex
    refine ⟨k, periodization_eq_of_ne_zero hf hk, fun k' hk' => ?_⟩
    by_contra hne
    exact hk' (eq_of_sub_intCast_ne_zero hf hne hk)
  · push Not at hex
    exact ⟨0, by rw [periodization_eq_zero hex, hex 0], fun k' _ => hex k'⟩

/-- On the fundamental box `(0,1]²` the periodisation agrees with the field itself; in particular
both vanish wherever the field does. -/
theorem periodization_eq_self_of_mem_Ioc {f : ℝ × ℝ → F} (hf : SupportedInOpenUnitBox f)
    {x : ℝ × ℝ} (h1 : x.1 ∈ Set.Ioc (0 : ℝ) 1) (h2 : x.2 ∈ Set.Ioc (0 : ℝ) 1) :
    periodization f x = f x := by
  rw [Set.mem_Ioc] at h1 h2
  have hzero : ∀ k : ℤ × ℤ, k ≠ 0 → f (x - ((k.1 : ℝ), (k.2 : ℝ))) = 0 := by
    intro k hk
    by_contra hne
    obtain ⟨hb1, hb2⟩ := hf _ hne
    simp only [Prod.fst_sub, Prod.snd_sub, Set.mem_Ioo] at hb1 hb2
    refine hk (Prod.ext ?_ ?_)
    · have hlt : ((k.1 : ℤ) : ℝ) < 1 := by linarith [hb1.1, h1.2]
      have hgt : ((-1 : ℤ) : ℝ) < ((k.1 : ℤ) : ℝ) := by
        push_cast
        linarith [hb1.2, h1.1]
      have hlt' : k.1 < 1 := by exact_mod_cast hlt
      have hgt' : (-1 : ℤ) < k.1 := by exact_mod_cast hgt
      change k.1 = 0
      omega
    · have hlt : ((k.2 : ℤ) : ℝ) < 1 := by linarith [hb2.1, h2.2]
      have hgt : ((-1 : ℤ) : ℝ) < ((k.2 : ℤ) : ℝ) := by
        push_cast
        linarith [hb2.2, h2.1]
      have hlt' : k.2 < 1 := by exact_mod_cast hlt
      have hgt' : (-1 : ℤ) < k.2 := by exact_mod_cast hgt
      change k.2 = 0
      omega
  have hx0 : x - (((0 : ℤ × ℤ).1 : ℝ), ((0 : ℤ × ℤ).2 : ℝ)) = x := by
    refine Prod.ext ?_ ?_ <;> simp
  unfold periodization
  rw [tsum_eq_single 0 fun k' hk' => hzero k' hk', hx0]

/-- The periodisation is `ℤ²`-periodic, by reindexing the defining series. -/
theorem isPeriodic_periodization (f : ℝ × ℝ → F) :
    LatticePeriodic.IsPeriodic (periodization f) := by
  intro x m n
  unfold periodization
  refine ((Equiv.addRight ((m, n) : ℤ × ℤ)).tsum_eq
    (fun k : ℤ × ℤ => f (((x.1 + m, x.2 + n) : ℝ × ℝ) - ((k.1 : ℝ), (k.2 : ℝ))))).symm.trans ?_
  refine tsum_congr fun k => ?_
  congr 1
  refine Prod.ext ?_ ?_
  · change x.1 + (m : ℝ) - ((k.1 + m : ℤ) : ℝ) = x.1 - (k.1 : ℝ)
    push_cast
    ring
  · change x.2 + (n : ℝ) - ((k.2 + n : ℤ) : ℝ) = x.2 - (k.2 : ℝ)
    push_cast
    ring

/-- **The periodisation is Lipschitz, with twice the constant.**  At `x` and `y` only one integer
translate each can be active; if the two translates differ, both mixed differences are estimated
by the Lipschitz bound of the field, because the missing terms vanish and the triangle inequality
`‖a - b'‖ ≤ ‖a‖ + ‖b'‖` then reads `‖a - b'‖ ≤ ‖a - b‖ + ‖a' - b'‖`. -/
theorem lipschitzWith_periodization {L : ℝ≥0} {f : ℝ × ℝ → F}
    (hf : SupportedInOpenUnitBox f) (hL : LipschitzWith L f) :
    LipschitzWith (2 * L) (periodization f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  obtain ⟨k, hkx, hkx0⟩ := exists_periodization_eq hf x
  obtain ⟨k', hky, hky0⟩ := exists_periodization_eq hf y
  have hxy : ∀ j : ℤ × ℤ,
      dist (f (x - ((j.1 : ℝ), (j.2 : ℝ)))) (f (y - ((j.1 : ℝ), (j.2 : ℝ))))
        ≤ (L : ℝ) * dist x y := by
    intro j
    have hj := hL.dist_le_mul (x - ((j.1 : ℝ), (j.2 : ℝ))) (y - ((j.1 : ℝ), (j.2 : ℝ)))
    rwa [dist_sub_right] at hj
  have hcoe : ((2 * L : ℝ≥0) : ℝ) = 2 * (L : ℝ) := by
    push_cast
    ring
  have hdist : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  rw [hcoe, hkx, hky]
  by_cases hkk : k = k'
  · subst hkk
    have h := hxy k
    nlinarith [h, hdist, hLnonneg]
  · have hy0 : f (y - ((k.1 : ℝ), (k.2 : ℝ))) = 0 := hky0 k hkk
    have hx0 : f (x - ((k'.1 : ℝ), (k'.2 : ℝ))) = 0 := hkx0 k' (Ne.symm hkk)
    have e1 : ‖f (x - ((k.1 : ℝ), (k.2 : ℝ)))‖ ≤ (L : ℝ) * dist x y := by
      have h := hxy k
      rwa [dist_eq_norm, hy0, sub_zero] at h
    have e2 : ‖f (y - ((k'.1 : ℝ), (k'.2 : ℝ)))‖ ≤ (L : ℝ) * dist x y := by
      have h := hxy k'
      rwa [dist_eq_norm, hx0, zero_sub, norm_neg] at h
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)

/-! ### The active translate near a given point -/

/-- The integer translate that alone can be active near a given point of the plane, for a field
supported in the placement chart.  The shift `1/8` in the first coordinate keeps the point away
from the endpoints of the chart's first interval `(0, 1/4)`; the second coordinate needs no shift
because the chart's second interval `(1/4, 3/4)` is already centred. -/
def localTranslationIndex (x : ℝ × ℝ) : ℤ × ℤ := (⌈x.1 + 1 / 8⌉ - 1, ⌈x.2⌉ - 1)

/-- On the open box of half-widths `1/8` and `1/4` around `x`, the only integer translate that can
carry a nonzero value is `localTranslationIndex x`. -/
theorem eq_localTranslationIndex_of_ne_zero {f : ℝ × ℝ → F} (hf : SupportedInPlacementChart f)
    {x y : ℝ × ℝ} (hy1 : y.1 ∈ Set.Ioo (x.1 - 1 / 8) (x.1 + 1 / 8))
    (hy2 : y.2 ∈ Set.Ioo (x.2 - 1 / 4) (x.2 + 1 / 4)) {k : ℤ × ℤ}
    (hk : f (y - ((k.1 : ℝ), (k.2 : ℝ))) ≠ 0) : k = localTranslationIndex x := by
  obtain ⟨h1, h2⟩ := hf _ hk
  simp only [Prod.fst_sub, Prod.snd_sub, Set.mem_Ioo] at h1 h2
  simp only [Set.mem_Ioo] at hy1 hy2
  have hc1 : ⌈x.1 + 1 / 8⌉ = k.1 + 1 := by
    refine Int.ceil_eq_iff.2 ⟨?_, ?_⟩ <;> push_cast <;> linarith [h1.1, h1.2, hy1.1, hy1.2]
  have hc2 : ⌈x.2⌉ = k.2 + 1 := by
    refine Int.ceil_eq_iff.2 ⟨?_, ?_⟩ <;> push_cast <;> linarith [h2.1, h2.2, hy2.1, hy2.2]
  refine Prod.ext ?_ ?_
  · change k.1 = ⌈x.1 + 1 / 8⌉ - 1
    omega
  · change k.2 = ⌈x.2⌉ - 1
    omega

/-- **Near every point the periodisation is a single translate.**  For a field supported in the
placement chart, the defining series collapses, on a whole neighbourhood of any point, to the one
translate indexed by `localTranslationIndex`. -/
theorem eventuallyEq_translate {f : ℝ × ℝ → F} (hf : SupportedInPlacementChart f) (x : ℝ × ℝ) :
    periodization f =ᶠ[𝓝 x]
      fun y ↦ f (y - (((localTranslationIndex x).1 : ℝ), ((localTranslationIndex x).2 : ℝ))) := by
  have hopen : IsOpen (Set.Ioo (x.1 - 1 / 8) (x.1 + 1 / 8) ×ˢ
      Set.Ioo (x.2 - 1 / 4) (x.2 + 1 / 4)) := isOpen_Ioo.prod isOpen_Ioo
  have hmem : x ∈ Set.Ioo (x.1 - 1 / 8) (x.1 + 1 / 8) ×ˢ
      Set.Ioo (x.2 - 1 / 4) (x.2 + 1 / 4) := by
    constructor <;> simp only [Set.mem_Ioo] <;> constructor <;> linarith
  filter_upwards [hopen.mem_nhds hmem] with y hy
  unfold periodization
  refine tsum_eq_single (localTranslationIndex x) fun k' hk' => ?_
  by_contra hne
  exact hk' (eq_localTranslationIndex_of_ne_zero hf hy.1 hy.2 hne)

/-- Where the active translate is the trivial one, the periodisation agrees with the field itself
on a whole neighbourhood — not merely at the point. -/
theorem eventuallyEq_self_of_localTranslationIndex_eq_zero {f : ℝ × ℝ → F}
    (hf : SupportedInPlacementChart f) {x : ℝ × ℝ} (hx : localTranslationIndex x = 0) :
    periodization f =ᶠ[𝓝 x] f := by
  refine (eventuallyEq_translate hf x).trans ?_
  filter_upwards with y
  rw [hx]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

end UnitBoxPeriodization

/-! ## Elementary facts about the quotient map of the plane -/

namespace LatticePeriodic

/-- Every real number has an integer translate in the fundamental interval `(0,1]`. -/
theorem exists_int_sub_mem_Ioc (t : ℝ) : ∃ m : ℤ, t - m ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨⌈t⌉ - 1, ?_⟩
  rw [Set.mem_Ioc]
  constructor
  · have hceil := Int.ceil_lt_add_one t
    push_cast
    linarith
  · have hceil := Int.le_ceil t
    push_cast
    linarith

/-- A `ℤ²`-periodic field is unchanged by subtracting an integer vector. -/
theorem IsPeriodic.sub_int {G : Type*} {f : ℝ × ℝ → G} (hf : IsPeriodic f)
    (x : ℝ × ℝ) (m n : ℤ) : f ((x.1 - m, x.2 - n)) = f x := by
  have h := hf ((x.1 - m, x.2 - n)) m n
  simpa using h.symm

end LatticePeriodic

/-! ## The periodised global velocity -/

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

namespace FullVelocityConcrete

open UnitBoxPeriodization

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- The chart-side global velocity is supported in the placement chart: it vanishes outside the
buffer discs, and those lie in `placementChart = Ioo 0 (1/4) ×ˢ Ioo (1/4) (3/4)`. -/
theorem supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource :
    SupportedInPlacementChart
      (parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau) := by
  intro x hx
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    exact P.bufferDisk_subset_chart n hn
  · push Not at hbuffer
    exact absurd (parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed tau hbuffer) hx

/-- The chart-side global velocity is a fortiori supported in the open unit box. -/
theorem supportedInOpenUnitBox_parameterizedFullGlobalEuclideanRealSource :
    SupportedInOpenUnitBox
      (parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau) :=
  (supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource
    h P angularSpeed axialSpeed tau).supportedInOpenUnitBox

/-- The `ℤ²`-periodisation of the chart-side global velocity: the paper's global velocity,
repeated over the integer lattice.  At every point the defining series has at most one nonzero
term. -/
def parameterizedFullGlobalPeriodizedRealSource : ℝ × ℝ → R3 :=
  periodization (parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau)

/-- On the fundamental box `(0,1]²` the periodised velocity is the chart-side velocity. -/
theorem parameterizedFullGlobalPeriodizedRealSource_eq_of_mem_Ioc {x : ℝ × ℝ}
    (h1 : x.1 ∈ Set.Ioc (0 : ℝ) 1) (h2 : x.2 ∈ Set.Ioc (0 : ℝ) 1) :
    parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau x =
      parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau x :=
  periodization_eq_self_of_mem_Ioc
    (supportedInOpenUnitBox_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau) h1 h2

/-- The periodised velocity is `ℤ²`-periodic. -/
theorem isLatticePeriodic_parameterizedFullGlobalPeriodizedRealSource :
    LatticePeriodic.IsPeriodic
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) :=
  isPeriodic_periodization _

/-- The periodised velocity is Lipschitz with twice the chart-side constant. -/
theorem lipschitzWith_parameterizedFullGlobalPeriodizedRealSource (htau : 0 ≤ tau) :
    LipschitzWith
      (2 * Real.toNNReal (globalVelocityLipschitzBound h P angularSpeed axialSpeed tau))
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) :=
  lipschitzWith_periodization
    (supportedInOpenUnitBox_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau)
    (lipschitzWith_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau htau)

/-! ## Identification with the torus-side representative -/

/-- The torus-side global velocity, pulled back along the quotient map of the plane, is exactly the
periodised chart-side velocity — at *every* point of the plane, not only on the fundamental
box. -/
theorem parameterizedFullGlobalRealTorusSource_transverseTorusPoint (x : ℝ × ℝ) :
    parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint x) =
      parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau x := by
  obtain ⟨m, hm⟩ := LatticePeriodic.exists_int_sub_mem_Ioc x.1
  obtain ⟨n, hn⟩ := LatticePeriodic.exists_int_sub_mem_Ioc x.2
  rw [Set.mem_Ioc] at hm hn
  have hbox1 : ((x.1 - m, x.2 - n) : ℝ × ℝ).1 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨hm.1, by linarith [hm.2]⟩
  have hbox2 : ((x.1 - m, x.2 - n) : ℝ × ℝ).2 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨hn.1, by linarith [hn.2]⟩
  have hbox1' : ((x.1 - m, x.2 - n) : ℝ × ℝ).1 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hm.1, hm.2⟩
  have hbox2' : ((x.1 - m, x.2 - n) : ℝ × ℝ).2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hn.1, hn.2⟩
  rw [← transverseTorusPoint_sub_int x m n,
    parameterizedFullGlobalRealTorusSource_transverseTorusPoint_of_mem_Ioc
      h P angularSpeed axialSpeed tau hbox1 hbox2,
    ← parameterizedFullGlobalPeriodizedRealSource_eq_of_mem_Ioc
      h P angularSpeed axialSpeed tau hbox1' hbox2',
    (isLatticePeriodic_parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau).sub_int x m n]

/-- The torus-side global velocity *is* the descent of the periodised chart-side velocity, by the
uniqueness of the descent. -/
theorem parameterizedFullGlobalRealTorusSource_eq_transverseDescent :
    parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau =
      transverseDescent
        (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) :=
  eq_transverseDescent
    (isLatticePeriodic_parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau)
    (parameterizedFullGlobalRealTorusSource_transverseTorusPoint
      h P angularSpeed axialSpeed tau)

/-- **The torus-side global velocity is Lipschitz** on the transverse two-torus, with twice the
explicit chart-side constant `globalVelocityLipschitzBound`.  The constant is explicit but not
claimed to be optimal. -/
theorem lipschitzWith_parameterizedFullGlobalRealTorusSource (htau : 0 ≤ tau) :
    LipschitzWith
      (2 * Real.toNNReal (globalVelocityLipschitzBound h P angularSpeed axialSpeed tau))
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau) := by
  rw [parameterizedFullGlobalRealTorusSource_eq_transverseDescent
    h P angularSpeed axialSpeed tau]
  exact lipschitzWith_transverseDescent
    (lipschitzWith_parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau htau)
    (isLatticePeriodic_parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau)

/-- **The axially independent extension of the global velocity to the literal three-torus is
Lipschitz**, with the same explicit (non-optimal) constant. -/
theorem lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource (htau : 0 ≤ tau) :
    LipschitzWith
      (2 * Real.toNNReal (globalVelocityLipschitzBound h P angularSpeed axialSpeed tau))
      (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) :=
  lipschitzWith_literalVelocity
    (lipschitzWith_parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau htau)

/-! ## Qualitative regularity of the periodised velocity -/

/-- At the accumulation point the active integer translate is the trivial one: the shifted ceiling
of `0` and the ceiling of `1/2` are both `1`. -/
theorem localTranslationIndex_accumulationPoint :
    localTranslationIndex accumulationPoint = 0 := by
  unfold localTranslationIndex
  norm_num [accumulationPoint]

/-- **The periodised velocity coincides with the chart-side velocity near the accumulation
point.**  The competing translates would have to place the point inside the placement chart after
a nonzero integer shift, which the chart's width `1/4` forbids. -/
theorem parameterizedFullGlobalPeriodizedRealSource_eventuallyEq_accumulationPoint :
    parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
        =ᶠ[𝓝 accumulationPoint]
      parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau :=
  eventuallyEq_self_of_localTranslationIndex_eq_zero
    (supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau)
    localTranslationIndex_accumulationPoint

/-- **The periodised velocity is differentiable everywhere.**  Near any point it is a translate of
the chart-side velocity, which is differentiable everywhere. -/
theorem differentiable_parameterizedFullGlobalPeriodizedRealSource (htau : 0 ≤ tau) :
    Differentiable ℝ
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) := by
  intro x
  refine DifferentiableAt.congr_of_eventuallyEq ?_
    (eventuallyEq_translate
      (supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x)
  exact ((differentiable_parameterizedFullGlobalEuclideanRealSource
    h P angularSpeed axialSpeed tau htau) _).comp x (differentiableAt_id.sub_const _)

/-- **The periodised velocity is smooth away from the lattice orbit of the accumulation point.**
Unlike the chart-side velocity, the periodised one is singular at every integer translate of
`p_∞`, so the hypothesis quantifies over all of them. -/
theorem contDiffAt_parameterizedFullGlobalPeriodizedRealSource {x : ℝ × ℝ}
    (hx : ∀ k : ℤ × ℤ, x - ((k.1 : ℝ), (k.2 : ℝ)) ≠ accumulationPoint) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) x := by
  refine ContDiffAt.congr_of_eventuallyEq ?_
    (eventuallyEq_translate
      (supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x)
  exact (contDiffAt_parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau
    (hx (localTranslationIndex x))).comp x (contDiff_id.sub contDiff_const).contDiffAt

/-- The derivative of the periodised velocity vanishes at the accumulation point. -/
theorem fderiv_parameterizedFullGlobalPeriodizedRealSource_accumulationPoint (htau : 0 ≤ tau) :
    fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau)
      accumulationPoint = 0 := by
  rw [(parameterizedFullGlobalPeriodizedRealSource_eventuallyEq_accumulationPoint
    h P angularSpeed axialSpeed tau).fderiv_eq]
  exact fderiv_parameterizedFullGlobalEuclideanRealSource_accumulationPoint
    h P angularSpeed axialSpeed tau htau

/-- **The periodised velocity is differentiable but not `C¹`**: its derivative is discontinuous at
the accumulation point, exactly as the chart-side velocity's is. -/
theorem not_continuousAt_fderiv_parameterizedFullGlobalPeriodizedRealSource
    (htau : 0 ≤ tau) (hangularSpeed : angularSpeed ≠ 0) :
    ¬ ContinuousAt (fderiv ℝ
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau))
      accumulationPoint := by
  intro hcont
  exact not_continuousAt_fderiv_parameterizedFullGlobalEuclideanRealSource
    h P angularSpeed axialSpeed tau htau hangularSpeed
    (hcont.congr (parameterizedFullGlobalPeriodizedRealSource_eventuallyEq_accumulationPoint
      h P angularSpeed axialSpeed tau).fderiv)

end FullVelocityConcrete

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
