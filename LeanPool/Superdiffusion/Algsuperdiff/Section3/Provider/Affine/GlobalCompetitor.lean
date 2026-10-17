/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CommonCoarseMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SubadditiveDecomposition

/-!
# GlobalCompetitor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The global piecewise-affine competitor `ℓ̂_p` on `□_m`

* ** the global assembly.**  The competitor is no longer built on the window
  `𝒩(C)` alone: it is the affine extension of the **one global vertex datum**
  `competitorVertexData C p` of `CompetitorVertexData.lean` on the **uniform
  scale-`s` Kuhn mesh of the whole root cube `□_m`** (`rootCoarseMesh`), at the
  window's own common coarse scale `s = simplexScale m hn j`.  Because that
  mesh is single-scale and finite, the gluing of `GlobalGluing.lean` applies
  verbatim, and the resulting function is well defined and continuous on all of
  `□_m`, not merely on the window.
* **(b) the matching with `ℓ_p` across the outer boundary of the window.**  The
  outer-boundary matching is *proved*, not assumed:
  `globalCompetitor_eqOn_linearFn_closedCarrier_of_notMem_commonCoarseMesh`
  states that on the **closed** carrier of every root cell off the window mesh
  the global competitor **is** `ℓ_p`, and
  `notMem_commonCoarseMesh_of_mem_cubeSet` puts every root cell that meets a
  Whitney cube off `𝒩(C)` outside that mesh.  Together they pin the function as
  "the window competitor inside `𝒩(C)`, `ℓ_p` outside", i.e. the manuscript's
  own `ℓ̂_p`.  These are ordinary Provider results and do not settle either item
  as a source-node fraction.

## The engine: the closed-star lemma

The correction is a **geometric** one, and it is
`mem_commonCoarseMesh_of_vertex_mem_closedCubeCarrier`:

> if a vertex of a scale-`s` root cell lies in the closed carrier of `C`, then
> that cell already belongs to the window mesh `commonCoarseMesh 𝒩(C) s`.

Equivalently: a root cell **outside** the window mesh has *all* its vertices off
the closed bad cubes, so its interpolant of the global datum is exactly `ℓ_p`
(`eqOn_vertexSet_competitorVertexData_linearFn_of_notMem_commonCoarseMesh`).
Its proof is the locally-finite closed-star argument:

1. `exists_whitneyCube_inter_cubeSet_mem_closedBall` -- an interior point `v`
   in the closed realization of a triadic cube `B` lies in the *closed* cube of
   some Whitney cube whose half-open cube already meets `B`.  This is local
   finiteness of `𝒲(□_m)` in the interior, obtained from the **upper** half
   (`boundaryMargin_le_of_mem_whitneyLayer`): a point at boundary margin `≥ ε`
   can only be met by Whitney cubes of boundedly many layers, and each layer is
   a `Finset`.
2. that Whitney cube touches `C` (both closed cubes contain `v`), hence lies in
   `𝒩(C)`, hence has scale `≥ s` by the two-layer window hypothesis;
3. a scale-`s` root cube meeting a Whitney cube of scale `≥ s` is a descendant
   of it (`mem_descendantsAtScale_of_cubeSet_inter_nonempty`), so `B` sits in a
   window cube and the cell is a window cell.

No "extra collar layer" and no cutoff is needed; the mesh is the same
single-scale mesh, extended over the root cube.

## Scope: what this module does NOT do

* **One bad family only.**  Everything is stated at a single family `C` whose
  touching neighborhood occupies at most two consecutive layers.  What this
  module supplies for it is exactly what that superposition needs: each
  component correction `globalCompetitor − ℓ_p` is now known to be continuous
  on all of `□_m`, to vanish on the closed cube of every Whitney cube off that
  component's neighborhood, and to be affine on every final `e.SW.def` cell.
  The remaining work is the locally-finite sum over components (local
  finiteness of the component carriers, and the `finsum`), and the resulting
  clause bookkeeping at `badFamily M m hn omega` rather than at one `C`.
* **The two-layer window is a hypothesis, not a theorem** (as in
  `CommonCoarseMesh.lean`): `hNlayer` carries `𝒩(C) ⊆ 𝒲(□_m,j) ∪ 𝒲(□_m,j+1)`,
  the conclusion; the proved
  `Whitney.whitneyNeighborhood_finite_and_mem_leastLayer_or_succ` is what a
  caller discharges it with (it also supplies the finiteness behind the
  `Finset` `N`).  Nothing here proves it, and no three-layer window is used.
* /`-c1` are **read and not consumed**: no gradient estimate, no collar
  constant, no component diameter and no overlap count occurs here.  is read
  and not consumed: no connectivity statement is used -- the window is an
  explicit binder.

## References

* ABK26, (`e.SW.def`), labels (`l.piecewise.affine.approx`,
  `e.hat.linear.properties`; clause 1, clause 3), (the false disjointness),
  (Step 1, with "well-defined and continuous"), (the prescribed vertex values),
  (the layer/boundary distance), (`ℓ_e(x) = e·x`).
* The private nesting helper `mem_descendantsAtDepth_of_mem_cubeSet_inter'` is
  a re-proof of the private
  `PartitionCovering.mem_descendantsAtDepth_of_mem_cubeSet_inter` of this
  repository (private, hence not importable).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Local finiteness of the Whitney partition in the interior -/

private theorem exists_nat_zpow_sub_lt' (m : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (3 : ℝ) ^ (m - (N : ℤ)) < ε := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one (div_pos hε hpos) (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨N, ?_⟩
  have hrw : (3 : ℝ) ^ (m - (N : ℤ)) = (3 : ℝ) ^ m * (1 / 3 : ℝ) ^ N := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), div_pow, one_pow, ← zpow_natCast (3 : ℝ) N]
    field_simp
  rw [hrw]
  calc (3 : ℝ) ^ m * (1 / 3 : ℝ) ^ N < (3 : ℝ) ^ m * (ε / (3 : ℝ) ^ m) :=
        by exact mul_lt_mul_of_pos_left hN hpos
    _ = ε := by field_simp

/-- Whitney cubes carrying a point at boundary margin at least `ε` occupy only
finitely many layers, so they form a finite family. -/
private theorem finite_whitneyCubes_of_boundaryMargin_le {m : ℤ} {hn : ℕ → ℕ}
    {ε : ℝ} (hε : 0 < ε) :
    {Q : TriadicCube d | Q ∈ whitneyPartition m hn ∧
      ∃ x ∈ cubeSet Q, ε ≤ (3 : ℝ) ^ m / 2 - ‖x‖}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_zpow_sub_lt' m (by linarith : (0 : ℝ) < ε / 3)
  refine Set.Finite.subset
    ((Finset.range N).finite_toSet.biUnion
      (fun n _ => (whitneyLayer (d := d) m hn n).finite_toSet)) ?_
  rintro Q ⟨⟨n, hQn⟩, x, hxQ, hx⟩
  have hup := boundaryMargin_le_of_mem_whitneyLayer hQn hxQ
  have hlt : n < N := by
    by_contra hcon
    have hmono : (3 : ℝ) ^ (m - (n : ℤ)) ≤ (3 : ℝ) ^ (m - (N : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hlt))
    (Finset.mem_coe.mpr hQn)

/-- **The closed-star bridge.**  An interior point in the closed realization of
a triadic cube `B` is in the closed realization of some Whitney cube whose
half-open realization already meets `B`. -/
theorem exists_whitneyCube_inter_cubeSet_mem_closedBall [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    {B : TriadicCube d} {v : Vec d} (hv : v ∈ openCubeSet (originCube d m))
    (hvB : v ∈ Metric.closedBall (cubeCenter B) (HCPolySupport.cubeRadius B)) :
    ∃ Q ∈ whitneyPartition m hn,
      (cubeSet Q ∩ cubeSet B).Nonempty ∧
        v ∈ Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) := by
  classical
  set δ : ℝ := (3 : ℝ) ^ m / 2 - ‖v‖ with hδdef
  have hnormlt : ‖v‖ < (3 : ℝ) ^ m / 2 := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by positivity
    refine pi_norm_lt_iff hpos |>.mpr fun i => ?_
    have hi := mem_openCubeSet_originCube_iff.mp hv i
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hi.1, hi.2]
  have hδ : 0 < δ := by rw [hδdef]; linarith
  -- the bad Whitney cubes: those that meet a small ball about `v` but miss `v`
  set S : Set (TriadicCube d) :=
    {Q | Q ∈ whitneyPartition m hn ∧ (cubeSet Q ∩ Metric.ball v (δ / 2)).Nonempty ∧
      v ∉ Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q)} with hSdef
  have hSfin : S.Finite := by
    refine (finite_whitneyCubes_of_boundaryMargin_le (d := d) (m := m) (hn := hn)
      (ε := δ / 2) (by linarith)).subset ?_
    rintro Q ⟨hQ, ⟨y, hyQ, hyb⟩, -⟩
    refine ⟨hQ, y, hyQ, ?_⟩
    have hdist : ‖y - v‖ < δ / 2 := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hyb
    have : ‖y‖ ≤ ‖v‖ + ‖y - v‖ := by
      simpa using norm_le_norm_add_norm_sub' y v
    linarith
  have hFclosed : IsClosed (⋃ Q ∈ S, Metric.closedBall (cubeCenter Q)
      (HCPolySupport.cubeRadius Q)) :=
    hSfin.isClosed_biUnion fun _ _ => Metric.isClosed_closedBall
  have hvF : v ∉ ⋃ Q ∈ S, Metric.closedBall (cubeCenter Q)
      (HCPolySupport.cubeRadius Q) := by
    intro hmem
    obtain ⟨Q, hQS, hvQ⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hmem
    exact hQS.2.2 hvQ
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp hFclosed.isOpen_compl v hvF
  have hvball : v ∈ Metric.ball (cubeCenter (originCube d m))
      (HCPolySupport.cubeRadius (originCube d m)) := by
    rw [ball_cubeCenter_eq_openCubeSet]; exact hv
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball v hvball
  set r : ℝ := min r₀ (min r₁ (δ / 2)) with hrdef
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ (by linarith))
  -- a point of `B` within `r` of `v`
  have hvclos : v ∈ closure (cubeSet B) := by
    rw [closure_cubeSet_eq_closedBall]; exact hvB
  obtain ⟨y, hyB, hyd⟩ := Metric.mem_closure_iff.mp hvclos r hr
  have hyball : y ∈ Metric.ball v r := Metric.mem_ball.mpr (by rwa [dist_comm] at hyd)
  have hyroot : y ∈ openCubeSet (originCube d m) := by
    have := hr₁sub (Metric.ball_subset_ball (le_trans (min_le_right _ _)
      (min_le_left _ _)) hyball)
    rwa [ball_cubeCenter_eq_openCubeSet] at this
  obtain ⟨n, Q, hQn, hyQ⟩ := exists_mem_whitneyLayer_of_mem_openCubeSet m hn hyroot
  refine ⟨Q, ⟨n, hQn⟩, ⟨y, hyQ, hyB⟩, ?_⟩
  by_contra hvQ
  have hQS : Q ∈ S :=
    ⟨⟨n, hQn⟩, ⟨y, hyQ, Metric.ball_subset_ball
      (le_trans (min_le_right _ _) (min_le_right _ _)) hyball⟩, hvQ⟩
  exact hr₀sub (Metric.ball_subset_ball (min_le_left _ _) hyball)
    (Set.mem_biUnion hQS (cubeSet_subset_closedBall Q hyQ))

private theorem mem_descendantsAtDepth_of_mem_cubeSet_inter' {m : ℤ} {p q : ℕ}
    {U V : TriadicCube d} (hU : U ∈ descendantsAtDepth (originCube d m) p)
    (hV : V ∈ descendantsAtDepth (originCube d m) q) (hpq : p ≤ q)
    {x : Vec d} (hxU : x ∈ cubeSet U) (hxV : x ∈ cubeSet V) :
    V ∈ descendantsAtDepth U (q - p) := by
  exact Whitney.mem_descendantsAtDepth_of_mem_cubeSet_inter hU hV hpq hxU hxV

/-- A scale-`s` triadic cube of the root that meets a Whitney cube of scale at
least `s` is a descendant of it. -/
theorem mem_descendantsAtScale_of_cubeSet_inter_nonempty {m : ℤ} {hn : ℕ → ℕ} {s : ℤ}
    {Q B : TriadicCube d} (hQ : Q ∈ whitneyPartition m hn)
    (hB : B ∈ descendantsAtScale (originCube d m) s) (hs : s ≤ Q.scale)
    (hinter : (cubeSet Q ∩ cubeSet B).Nonempty) :
    B ∈ descendantsAtScale Q s := by
  obtain ⟨n, hQn⟩ := hQ
  have hQscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hQn
  have hsm : s ≤ (originCube d m).scale := by
    change s ≤ m
    omega
  have hQdepth : Q ∈ descendantsAtDepth (originCube d m) (n + hn n) :=
    mem_descendantsAtDepth_of_mem_whitneyLayer hQn
  have hBdepth : B ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - s)) := by
    have := hB
    rwa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hsm,
      show (originCube d m).scale = m from rfl] at this
  obtain ⟨x, hxQ, hxB⟩ := hinter
  have hple : n + hn n ≤ Int.toNat (m - s) := by omega
  have hstep := mem_descendantsAtDepth_of_mem_cubeSet_inter' hQdepth hBdepth hple hxQ hxB
  rw [descendantsAtScale_eq_descendantsAtDepth Q hs]
  have hcount : Int.toNat (m - s) - (n + hn n) = Int.toNat (Q.scale - s) := by omega
  rwa [hcount] at hstep

/-! ## The closed-star lemma -/

/-- **The closed-star lemma.**  If a vertex of a scale-`s` cell of the root mesh
lies in the closed carrier of a family `C` of Whitney cubes, then the cell
already belongs to the common coarse mesh of any window `N` containing every
Whitney cube touching `C`, provided the window sits at scale at least `s`. -/
theorem mem_commonCoarseMesh_of_vertex_mem_closedCubeCarrier [NeZero d]
    {m : ℤ} {hn : ℕ → ℕ} {s : ℤ} {C : Set (TriadicCube d)}
    (hC : C ⊆ whitneyPartition m hn) {N : Finset (TriadicCube d)}
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) {T : KuhnCell d}
    (hT : T.supportCube ∈ descendantsAtScale (originCube d m) s)
    {v : Vec d} (hv : v ∈ T.vertexSet) (hvC : v ∈ closedCubeCarrier C) :
    T ∈ commonCoarseMesh N s := by
  obtain ⟨R, hR, hvR⟩ := mem_closedCubeCarrier_iff.mp hvC
  obtain ⟨nR, hRlayer⟩ := hC hR
  have hvroot : v ∈ openCubeSet (originCube d m) :=
    closedBall_subset_openCubeSet_of_mem_whitneyLayer hRlayer hvR
  have hvB : v ∈ Metric.closedBall (cubeCenter T.supportCube)
      (HCPolySupport.cubeRadius T.supportCube) :=
    vertexSet_subset_closedBall_supportCube T hv
  obtain ⟨Q, hQ, hinter, hvQ⟩ :=
    exists_whitneyCube_inter_cubeSet_mem_closedBall (hn := hn) hvroot hvB
  have hQN : Q ∈ N := hN Q hQ ⟨R, hR, ⟨v, hvQ, hvR⟩⟩
  exact mem_commonCoarseMesh_iff.mpr
    ⟨Q, hQN,
      mem_descendantsAtScale_of_cubeSet_inter_nonempty hQ hT (hs Q hQN) hinter⟩

/-! ## The root mesh -/

/-- The uniform scale-`s` Kuhn mesh of the root cube `□_m`. -/
def rootCoarseMesh (m s : ℤ) : Finset (KuhnCell d) :=
  triadicSimplexPartition (originCube d m) s

theorem mem_rootCoarseMesh_iff {m s : ℤ} {T : KuhnCell d} :
    T ∈ rootCoarseMesh (d := d) m s ↔
      T.supportCube ∈ descendantsAtScale (originCube d m) s :=
  mem_triadicSimplexPartition_iff

theorem supportCube_scale_eq_of_mem_rootCoarseMesh {m s : ℤ} (hs : s ≤ m)
    {T : KuhnCell d} (hT : T ∈ rootCoarseMesh (d := d) m s) : T.supportCube.scale = s :=
  supportCube_scale_eq_of_mem_triadicSimplexPartition (Q := originCube d m) hs hT

theorem cubeSet_originCube_subset_iUnion_closedCarrier_rootCoarseMesh {m s : ℤ}
    (hs : s ≤ m) :
    cubeSet (originCube d m) ⊆
      ⋃ T ∈ (rootCoarseMesh (d := d) m s : Set (KuhnCell d)), T.closedCarrier := by
  intro x hx
  rw [cubeSet_eq_iUnion_triadicSimplexPartition (originCube d m) hs] at hx
  obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hx
  exact Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, T.carrier_subset_closedCarrier hxT⟩⟩

/-- A triadic descendant of a Whitney cube is a triadic descendant of the root
cube at the same scale. -/
theorem mem_descendantsAtScale_originCube_of_mem_descendantsAtScale {m : ℤ}
    {hn : ℕ → ℕ} {s : ℤ} {Q B : TriadicCube d} (hQ : Q ∈ whitneyPartition m hn)
    (hs : s ≤ Q.scale) (hB : B ∈ descendantsAtScale Q s) :
    B ∈ descendantsAtScale (originCube d m) s := by
  obtain ⟨n, hQn⟩ := hQ
  have hQscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hQn
  have hQdepth : Q ∈ descendantsAtDepth (originCube d m) (n + hn n) :=
    mem_descendantsAtDepth_of_mem_whitneyLayer hQn
  have hBdepth : B ∈ descendantsAtDepth Q (Int.toNat (Q.scale - s)) := by
    rwa [descendantsAtScale_eq_descendantsAtDepth Q hs] at hB
  have hsm : s ≤ (originCube d m).scale := by
    change s ≤ m
    omega
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hsm,
    show (originCube d m).scale = m from rfl,
    show Int.toNat (m - s) = (n + hn n) + Int.toNat (Q.scale - s) from by omega]
  exact mem_descendantsAtDepth_add hQdepth hBdepth

/-! ## The global competitor of one bad component -/

/-- **The global piecewise-affine competitor `ℓ̂_p`** of the bad family `C`. -/
def globalCompetitor (m s : ℤ) (C : Set (TriadicCube d)) (p : Vec d) : Vec d → ℝ :=
  gluedKuhnAffine (rootCoarseMesh m s) (competitorVertexData C p)

open Classical in
/-- **The global piecewise-constant gradient field `∇ℓ̂_p`.** -/
def globalCompetitorSlope (m s : ℤ) (C : Set (TriadicCube d)) (p : Vec d) :
    Vec d → Vec d := fun x =>
  if h : ∃ T ∈ rootCoarseMesh (d := d) m s, x ∈ T.openCarrier then
    kuhnSlope h.choose (competitorVertexData C p) else p

theorem globalCompetitorSlope_of_mem_openCarrier {m s : ℤ} (hs : s ≤ m)
    (C : Set (TriadicCube d)) (p : Vec d) {T : KuhnCell d}
    (hT : T ∈ rootCoarseMesh (d := d) m s) {x : Vec d} (hx : x ∈ T.openCarrier) :
    globalCompetitorSlope m s C p x = kuhnSlope T (competitorVertexData C p) := by
  classical
  have hex : ∃ U ∈ rootCoarseMesh (d := d) m s, x ∈ U.openCarrier := ⟨T, hT, hx⟩
  have hspec := hex.choose_spec
  change (if h : ∃ U ∈ rootCoarseMesh (d := d) m s, x ∈ U.openCarrier then
    kuhnSlope h.choose (competitorVertexData C p) else p) = _
  rw [dite_eq_left hex]
  by_cases hne : hex.choose = T
  · rw [hne]
  · exact absurd (Set.disjoint_left.mp
      (disjoint_openCarrier_of_supportCube_scale_eq
        ((supportCube_scale_eq_of_mem_rootCoarseMesh hs hspec.1).trans
          (supportCube_scale_eq_of_mem_rootCoarseMesh hs hT).symm) hne) hspec.2)
      (by simpa using hx)

theorem globalCompetitorSlope_of_forall_notMem {m s : ℤ} (C : Set (TriadicCube d))
    (p : Vec d) {x : Vec d} (hx : ∀ T ∈ rootCoarseMesh (d := d) m s, x ∉ T.openCarrier) :
    globalCompetitorSlope m s C p x = p := by
  classical
  change (if h : ∃ U ∈ rootCoarseMesh (d := d) m s, x ∈ U.openCarrier then
    kuhnSlope h.choose (competitorVertexData C p) else p) = p
  rw [dite_eq_right (by rintro ⟨T, hT, hxT⟩; exact hx T hT hxT)]

/-! ## The matching with `ℓ_p` off the window -/

/-- **The closed-star consequence**: on a root cell outside the window mesh the
global vertex datum is `ℓ_p` at every vertex. -/
theorem eqOn_vertexSet_competitorVertexData_linearFn_of_notMem_commonCoarseMesh
    [NeZero d] {m : ℤ} {hn : ℕ → ℕ} {s : ℤ} {C : Set (TriadicCube d)}
    (hC : C ⊆ whitneyPartition m hn) {N : Finset (TriadicCube d)}
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) {T : KuhnCell d}
    (hT : T ∈ rootCoarseMesh (d := d) m s) (hTnot : T ∉ commonCoarseMesh N s) :
    Set.EqOn (competitorVertexData C p) (linearFn p) T.vertexSet := by
  intro v hv
  refine competitorVertexData_of_notMem_closedCubeCarrier p fun hvC => hTnot ?_
  exact mem_commonCoarseMesh_of_vertex_mem_closedCubeCarrier hC hN hs
    (mem_rootCoarseMesh_iff.mp hT) hv hvC

theorem kuhnSlope_competitorVertexData_eq_of_notMem_commonCoarseMesh
    [NeZero d] {m : ℤ} {hn : ℕ → ℕ} {s : ℤ} {C : Set (TriadicCube d)}
    (hC : C ⊆ whitneyPartition m hn) {N : Finset (TriadicCube d)}
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) {T : KuhnCell d}
    (hT : T ∈ rootCoarseMesh (d := d) m s) (hTnot : T ∉ commonCoarseMesh N s) :
    kuhnSlope T (competitorVertexData C p) = p :=
  kuhnSlope_eq_of_eqOn_vertexSet T
    (eqOn_vertexSet_competitorVertexData_linearFn_of_notMem_commonCoarseMesh
      hC hN hs p hT hTnot)

theorem globalCompetitor_eqOn_linearFn_closedCarrier_of_notMem_commonCoarseMesh
    [NeZero d] {m : ℤ} {hn : ℕ → ℕ} {s : ℤ} (hsm : s ≤ m) {C : Set (TriadicCube d)}
    (hC : C ⊆ whitneyPartition m hn) {N : Finset (TriadicCube d)}
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) {T : KuhnCell d}
    (hT : T ∈ rootCoarseMesh (d := d) m s) (hTnot : T ∉ commonCoarseMesh N s) :
    Set.EqOn (globalCompetitor m s C p) (linearFn p) T.closedCarrier := by
  refine (gluedKuhnAffine_eqOn_closedCarrier
    (fun _ hU => supportCube_scale_eq_of_mem_rootCoarseMesh hsm hU) _ hT).trans ?_
  rw [kuhnInterp_eq_linearFn_of_eqOn_vertexSet T
    (eqOn_vertexSet_competitorVertexData_linearFn_of_notMem_commonCoarseMesh
      hC hN hs p hT hTnot)]
  exact fun _ _ => rfl

/-- A root cell meeting a Whitney cube outside the window is outside the window
mesh. -/
theorem notMem_commonCoarseMesh_of_mem_cubeSet {m : ℤ} {hn : ℕ → ℕ} {s : ℤ}
    {N : Finset (TriadicCube d)} (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) {R : TriadicCube d} (hR : R ∈ whitneyPartition m hn)
    (hRnot : R ∉ N) {T : KuhnCell d} {x : Vec d} (hxR : x ∈ cubeSet R)
    (hxT : x ∈ cubeSet T.supportCube) : T ∉ commonCoarseMesh N s := by
  intro hT
  obtain ⟨Q, hQN, hTQ⟩ := mem_commonCoarseMesh_iff.mp hT
  have hxQ : x ∈ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtScale (hs Q hQN) hTQ hxT
  exact hRnot
    (eq_of_mem_cubeSet_of_mem_whitneyPartition hR (hNsub Q hQN) hxR hxQ ▸ hQN)

/-! ## Continuity -/

/-- **"this extension is well-defined and continuous"** for the global competitor,
on the whole root cube. -/
theorem continuousOn_globalCompetitor {m s : ℤ} (hsm : s ≤ m)
    (C : Set (TriadicCube d)) (p : Vec d) :
    ContinuousOn (globalCompetitor m s C p) (cubeSet (originCube d m)) :=
  (continuousOn_gluedKuhnAffine
      (fun _ hU => supportCube_scale_eq_of_mem_rootCoarseMesh hsm hU)
      (competitorVertexData C p)).mono
    (cubeSet_originCube_subset_iUnion_closedCarrier_rootCoarseMesh hsm)

/-! ## Subordination to `SW(□_m)` -/

theorem simplexScale_succ_le (m : ℤ) {hn : ℕ → ℕ} {j : ℕ}
    (hstep' : hn (j + 1) ≤ hn (j + 2) + 1) :
    simplexScale m hn (j + 1) ≤ simplexScale m hn j := by
  simp only [simplexScale, show j + 1 + 1 = j + 2 from rfl]
  push_cast
  omega

theorem simplexScale_le_self (m : ℤ) (hn : ℕ → ℕ) (j : ℕ) : simplexScale m hn j ≤ m := by
  simp only [simplexScale]
  omega

/-- **The window sits at scale at least the common coarse scale.** -/
theorem simplexScale_le_scale_of_mem_window {m : ℤ} {hn : ℕ → ℕ} {j : ℕ}
    (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1) {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hNlayer : ∀ Q ∈ N, ∀ n : ℕ, Q ∈ whitneyLayer m hn n → n = j ∨ n = j + 1) :
    ∀ Q ∈ N, simplexScale m hn j ≤ Q.scale := by
  intro Q hQN
  obtain ⟨n, hQn⟩ := hNsub Q hQN
  rcases hNlayer Q hQN n hQn with rfl | rfl
  · exact simplexScale_le_scale_of_mem_whitneyLayer (hstep n) hQn
  · exact le_of_eq (scale_eq_simplexScale_of_mem_whitneyLayer_succ hQn).symm

/-- **The subordination step**: a final `e.SW.def` cell whose simplex scale is
not coarser than the common scale sits inside a single root cell. -/
theorem exists_rootCell_openCarrier_subset {m : ℤ} {hn : ℕ → ℕ} {j n : ℕ}
    (hstep : ∀ k : ℕ, hn k ≤ hn (k + 1) + 1)
    (hns : simplexScale m hn n ≤ simplexScale m hn j) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m hn n Q) :
    ∃ U ∈ rootCoarseMesh (d := d) m (simplexScale m hn j),
      T.openCarrier ⊆ U.openCarrier := by
  have hTroot : T ∈ triadicSimplexPartition (originCube d m) (simplexScale m hn n) :=
    mem_triadicSimplexPartition_iff.mpr
      (mem_descendantsAtScale_originCube_of_mem_descendantsAtScale ⟨n, hQ⟩
        (simplexScale_le_scale_of_mem_whitneyLayer (hstep n) hQ)
        (mem_whitneySimplexCells_iff.mp hT))
  exact triadicSimplexPartition_refines_openCarrier (originCube d m)
    (show simplexScale m hn j ≤ (originCube d m).scale from simplexScale_le_self m hn j)
    hns hTroot

/-! ## The `sum_of_a_decomp` binder shapes -/

/-- **The cell constant of `∇ℓ̂_p`** on a cell of `SW(□_m)`. -/
def globalCompetitorCellSlope (m s : ℤ) (C : Set (TriadicCube d)) (p : Vec d)
    (T : KuhnCell d) : Vec d :=
  globalCompetitorSlope m s C p (Multiscale.kuhnCellInteriorPoint T)

/-- **The three `sum_of_a_decomp` clauses at one cell of `SW(□_m)`.**  The gradient
field of the global competitor is constant on the open cell (`hFc`/`hGc`), the
constant is `0` when the cell's Whitney cube is bad (clause 1) and it is `p`
when the cell's Whitney cube lies off the neighborhood `𝒩(C)` (clause 3). -/
theorem globalCompetitorSlope_eq_cellSlope [NeZero d] {m : ℤ} {hn : ℕ → ℕ} {j : ℕ}
    (hstep : ∀ k : ℕ, hn k ≤ hn (k + 1) + 1) (hstep' : hn (j + 1) ≤ hn (j + 2) + 1)
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNmem : ∀ Q : TriadicCube d, Q ∈ N ↔ Q ∈ whitneyNeighborhood m hn C)
    (hNlayer : ∀ Q ∈ N, ∀ n : ℕ, Q ∈ whitneyLayer m hn n → n = j ∨ n = j + 1)
    (p : Vec d) {T : KuhnCell d} (hT : T ∈ simplexPartition m hn) :
    (∀ x ∈ T.openCarrier,
        globalCompetitorSlope m (simplexScale m hn j) C p x =
          globalCompetitorCellSlope m (simplexScale m hn j) C p T) ∧
      (Multiscale.whitneyCubeOf m hn T ∈ C →
        globalCompetitorCellSlope m (simplexScale m hn j) C p T = 0) ∧
      (Multiscale.whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn C →
        globalCompetitorCellSlope m (simplexScale m hn j) C p T = p) := by
  classical
  set s : ℤ := simplexScale m hn j with hsdef
  have hsm : s ≤ m := simplexScale_le_self m hn j
  have hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn := fun Q hQ => ((hNmem Q).mp hQ).1
  have hs : ∀ Q ∈ N, s ≤ Q.scale :=
    simplexScale_le_scale_of_mem_window hstep hNsub hNlayer
  have hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N :=
    fun Q hQ hex => (hNmem Q).mpr ⟨hQ, hex⟩
  obtain ⟨n, Q, hQlayer, hTQ⟩ := hT
  have hcube : Multiscale.whitneyCubeOf m hn T = Q :=
    Multiscale.whitneyCubeOf_of_mem_whitneySimplexCells hQlayer hTQ
  have hTcube : T.carrier ⊆ cubeSet Q :=
    carrier_subset_cubeSet_of_mem_whitneySimplexCells hTQ
  have hinner : Multiscale.kuhnCellInteriorPoint T ∈ T.openCarrier :=
    Multiscale.kuhnCellInteriorPoint_mem_openCarrier T
  by_cases hQN : Q ∈ N
  · -- the cell sits in a window cube: it lies inside a single root cell
    have hns : simplexScale m hn n ≤ s := by
      rcases hNlayer Q hQN n hQlayer with rfl | rfl
      · exact le_rfl
      · exact simplexScale_succ_le m hstep'
    obtain ⟨U, hU, hTU⟩ := exists_rootCell_openCarrier_subset hstep hns hQlayer hTQ
    have hconst : ∀ x ∈ T.openCarrier,
        globalCompetitorSlope m s C p x = kuhnSlope U (competitorVertexData C p) :=
      fun x hx => globalCompetitorSlope_of_mem_openCarrier hsm C p hU (hTU hx)
    have hcell : globalCompetitorCellSlope m s C p T =
        kuhnSlope U (competitorVertexData C p) := hconst _ hinner
    refine ⟨fun x hx => (hconst x hx).trans hcell.symm, ?_, ?_⟩
    · intro hQC
      rw [hcube] at hQC
      have hUQ : U.supportCube ∈ descendantsAtScale Q s :=
        mem_descendantsAtScale_of_cubeSet_inter_nonempty ⟨n, hQlayer⟩
          (mem_rootCoarseMesh_iff.mp hU) (hs Q hQN)
          ⟨Multiscale.kuhnCellInteriorPoint T,
            hTcube (T.openCarrier_subset_carrier hinner),
            openCubeSet_subset_cubeSet _
              (U.openCarrier_subset_openCubeSet (hTU hinner))⟩
      rw [hcell, kuhnSlope_competitorVertexData_eq_zero hQC p hUQ]
    · intro hQoff
      exact absurd ((hNmem Q).mp hQN) (hcube ▸ hQoff)
  · -- the cell sits off the window: the competitor is `ℓ_p` there
    have hval : ∀ x ∈ T.openCarrier, globalCompetitorSlope m s C p x = p := by
      intro x hx
      by_cases hex : ∃ U ∈ rootCoarseMesh (d := d) m s, x ∈ U.openCarrier
      · obtain ⟨U, hU, hxU⟩ := hex
        rw [globalCompetitorSlope_of_mem_openCarrier hsm C p hU hxU,
          kuhnSlope_competitorVertexData_eq_of_notMem_commonCoarseMesh hC hN hs p hU
            (notMem_commonCoarseMesh_of_mem_cubeSet hNsub hs ⟨n, hQlayer⟩ hQN
              (hTcube (T.openCarrier_subset_carrier hx))
              (openCubeSet_subset_cubeSet _ (U.openCarrier_subset_openCubeSet hxU)))]
      · push Not at hex
        exact globalCompetitorSlope_of_forall_notMem C p hex
    refine ⟨fun x hx => (hval x hx).trans (hval _ hinner).symm, ?_, fun _ => hval _ hinner⟩
    intro hQC
    exact absurd ((hNmem Q).mpr ⟨⟨n, hQlayer⟩, Q, hcube ▸ hQC, cubeTouch_refl Q⟩) hQN

end

end Algsuperdiff.Section3.Provider.Affine
