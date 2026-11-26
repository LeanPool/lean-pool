/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.Section9Regions
import LeanPool.GraphMinor.GM16.LineInFace
import LeanPool.GraphMinor.Surface.ArcErase
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM11.CurveArc
import LeanPool.GraphMinor.GM16.DrawingAtoms
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM15.Section4

import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Lines and regions between distant battlefield boundaries

XV (3.5), used in XVI (8.1), Claim (4), requires that no region touch
both boundary circuits. Four vertex-to-region comparisons would put
the two cleared regions at distance at most eight. The compression
bound and the original separation of the centres rule this out.
For the corrected line condition, split a normal line at its drawing
vertices. Each segment lies in one region closure and has endpoint
distance at most four. Compression then transfers the bound back
to the original centres.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- A normal line between drawing vertices crosses at most one region
between consecutive vertices. Each crossing costs at most four in the
metric, using the vertex-to-region bound two. -/
private theorem normal_line_vertex_distance
     (hS : IsClosedSurface S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric H θ T d)
    {L : Set S} {a b : S} (hl : IsLineWithEnds L a b)
    (hn : H.IsNormal L) (ha : a ∈ H.V) (hb : b ∈ H.V) :
    d {a} {b} + 4 ≤ 4 * (L ∩ H.V).ncard := by
  have hf : (L ∩ H.V).Finite := H.finite_V.subset inter_subset_right
  induction hcard : (L ∩ H.V).ncard using Nat.strong_induction_on generalizing L a b with
  | ind n ih =>
    have haL := Surface.IsLineWithEnds.left_mem hl
    have hbL := Surface.IsLineWithEnds.right_mem hl
    have hab := ends_ne hl
    have haA : ({a} : Set S) ∈ H.A := Or.inl (Or.inl ⟨a, ha, rfl⟩)
    have hbA : ({b} : Set S) ∈ H.A := Or.inl (Or.inl ⟨b, hb, rfl⟩)
    obtain ⟨_, _, _, hsym, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T d hS
      inferInstance hm
    by_cases hex : ∃ x ∈ L ∩ H.V, x ≠ a ∧ x ≠ b
    · obtain ⟨x, hx, hxa, hxb⟩ := hex
      obtain ⟨L₁, L₂, h₁, h₂, hu, hi⟩ := IsLineWithEnds.split hl hx.1 hxa hxb
      have hs₁ : L₁ ⊆ L := fun _ h => hu ▸ Or.inl h
      have hs₂ : L₂ ⊆ L := fun _ h => hu ▸ Or.inr h
      have hf₁ : (L₁ ∩ H.V).Finite := hf.subset (inter_subset_inter_left _ hs₁)
      have hf₂ : (L₂ ∩ H.V).Finite := hf.subset (inter_subset_inter_left _ hs₂)
      have haNot : a ∉ L₂ := by
        intro h
        have : a = x := mem_singleton_iff.mp (hi ▸ ⟨Surface.IsLineWithEnds.left_mem h₁, h⟩)
        exact hxa this.symm
      have hbNot : b ∉ L₁ := by
        intro h
        have : b = x := mem_singleton_iff.mp (hi ▸ ⟨h, Surface.IsLineWithEnds.right_mem h₂⟩)
        exact hxb this.symm
      have hlt₁ : (L₁ ∩ H.V).ncard < n := by
        rw [← hcard]
        exact ncard_lt_ncard ⟨inter_subset_inter_left _ hs₁,
          fun h => hbNot (h ⟨hbL, hb⟩).1⟩ hf
      have hlt₂ : (L₂ ∩ H.V).ncard < n := by
        rw [← hcard]
        exact ncard_lt_ncard ⟨inter_subset_inter_left _ hs₂,
          fun h => haNot (h ⟨haL, ha⟩).1⟩ hf
      have hn₁ := ih _ hlt₁ h₁ (fun _ h => hn ⟨hs₁ h.1, h.2⟩) ha hx.2 hf₁ rfl
      have hn₂ := ih _ hlt₂ h₂ (fun _ h => hn ⟨hs₂ h.1, h.2⟩) hx.2 hb hf₂ rfl
      have hc := ncard_union_add_ncard_inter (L₁ ∩ H.V) (L₂ ∩ H.V) hf₁ hf₂
      have heU : (L₁ ∩ H.V) ∪ (L₂ ∩ H.V) = L ∩ H.V := by
        rw [← union_inter_distrib_right, hu]
      have heI : (L₁ ∩ H.V) ∩ (L₂ ∩ H.V) = {x} := by
        rw [inter_inter_inter_comm, hi, inter_self, singleton_inter_of_mem hx.2]
      rw [heU, heI, ncard_singleton, hcard] at hc
      have ht := htri {a} haA {x} (Or.inl (Or.inl ⟨x, hx.2, rfl⟩)) {b} hbA
      omega
    · have havoid : Disjoint (L \ {a,b}) H.U := by
        apply disjoint_left.mpr
        intro x hx hxU
        have hxV := hn ⟨hx.1, hxU⟩
        exact hex ⟨x, ⟨hx.1, hxV⟩, fun h => hx.2 (Or.inl h), fun h => hx.2 (Or.inr h)⟩
      obtain ⟨r, hr, _, hcl⟩ := exists_face_containing_line hl havoid
      have hp := vertex_atom_dist_le_two hS hm
      have h₁ := hp a ha r (Or.inr hr) (hcl haL)
      have h₂ := hp b hb r (Or.inr hr) (hcl hbL)
      have ht := htri {a} haA r (Or.inr hr) {b} hbA
      rw [hsym r (Or.inr hr) {b} hbA] at ht
      have hc : 2 ≤ (L ∩ H.V).ncard := by
        have hs : {a,b} ⊆ L ∩ H.V := by
          rintro x (rfl | rfl) <;> exact ⟨by assumption, by assumption⟩
        have hc := ncard_le_ncard hs hf
        rw [ncard_pair hab] at hc
        exact hc
      omega

omit [ConnectedSpace S] in
private theorem subline_between {L : Set S} (hl : IsLine L)
    {a b : S} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    ∃ P ⊆ L, IsLineWithEnds P a b := by
  obtain ⟨f⟩ := hl
  let g : unitInterval → S := fun t => (f t).val
  have hg : IsArcMap g := ⟨continuous_subtype_val.comp f.continuous,
    Subtype.val_injective.comp f.injective⟩
  obtain ⟨s, hs⟩ := f.surjective ⟨a, ha⟩
  obtain ⟨t, ht⟩ := f.surjective ⟨b, hb⟩
  have hga : g s = a := congrArg Subtype.val hs
  have hgb : g t = b := congrArg Subtype.val ht
  have hst : s ≠ t := fun h => hab (hga.symm.trans ((congrArg g h).trans hgb))
  have hline := (hg.sub hst).isLineWithEnds
  rw [subArc_zero, subArc_one, hga, hgb] at hline
  refine ⟨range (subArc g s t), ?_, hline⟩
  rintro x ⟨u, rfl⟩
  exact (f _).property

/-- The extra line condition needed in the corrected XV (3.5).
A line with `n` drawing vertices puts the two cleared regions at
metric distance at most `4 n`. Compression adds at most `loss`.
Thus separation at least `4 φ + loss` forces at least `φ` vertices. -/
theorem normal_line_between_cleared_boundaries
     (hS : IsClosedSurface S)
    {H : Drawing S} {Y : Set S} {Λ : S → Set S} {γ θ loss sep φ : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hY : Y ⊆ H.V)
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H Y Λ) θ loss T T' d d')
    {y z : S} (hy : y ∈ Y) (hz : z ∈ Y) (hyz : y ≠ z)
    (hsep : sep ≤ d {y} {z}) (hbudget : 4 * φ + loss ≤ sep) :
    ∀ F : Set S, IsLine F → (clearEnvelopeDrawing H Y Λ).IsNormal F →
      F ⊆ univ \ (Λ y ∪ Λ z) →
      (F ∩ subBd (Λ y)).Nonempty → (F ∩ subBd (Λ z)).Nonempty →
      φ ≤ (F ∩ (clearEnvelopeDrawing H Y Λ).V).ncard := by
  let K := clearEnvelopeDrawing H Y Λ
  have hyA : Λ y ∈ K.A := Or.inr (zone_mem_R_clearFamily hZone hdis hy)
  have hzA : Λ z ∈ K.A := Or.inr (zone_mem_R_clearFamily hZone hdis
    hz)
  obtain ⟨_, _, _, hsym, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} K
    (θ - loss) T' d' hS inferInstance hComp.hasMetric'
  intro F hF hn _ ⟨a, haF, haBd⟩ ⟨b, hbF, hbBd⟩
  have haV : a ∈ K.V := hn ⟨haF, zone_boundary_subset_clearFamily hZone hdis hy haBd⟩
  have hbV : b ∈ K.V := hn ⟨hbF, zone_boundary_subset_clearFamily hZone hdis hz hbBd⟩
  have hab : a ≠ b := by
    intro h
    exact (hdis y hy z hz hyz).notMem_of_mem_left haBd.1 (h ▸ hbBd.1)
  obtain ⟨P, hPF, hP⟩ := subline_between hF haF hbF hab
  have hdist := normal_line_vertex_distance hS hComp.hasMetric' hP
    (fun _ h => hn ⟨hPF h.1, h.2⟩) haV hbV
  have hc := ncard_le_ncard (inter_subset_inter_left K.V hPF)
    (K.finite_V.subset inter_subset_right)
  change d' {a} {b} + 4 ≤ 4 * (P ∩ K.V).ncard at hdist
  change φ ≤ (F ∩ K.V).ncard
  have hp := vertex_atom_dist_le_two hS hComp.hasMetric'
  have h₁ := hp a haV (Λ y) hyA haBd.1
  have h₂ := hp b hbV (Λ z) hzA hbBd.1
  have haA : ({a} : Set S) ∈ K.A := Or.inl (Or.inl ⟨a, haV, rfl⟩)
  have hbA : ({b} : Set S) ∈ K.A := Or.inl (Or.inl ⟨b, hbV, rfl⟩)
  have ht₁ := htri (Λ y) hyA {a} haA (Λ z) hzA
  have ht₂ := htri {a} haA {b} hbA (Λ z) hzA
  rw [hsym (Λ y) hyA {a} haA] at ht₁
  have hOld := hComp.dist_le y z
  rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨y, hY hy, rfl⟩))
    (Or.inl (Or.inl ⟨z, hY hz, rfl⟩)) (mem_singleton y) (mem_singleton z),
    pointDist_eq_of_mem_atom hyA hzA ((hZone y hy).z_subset (mem_singleton y))
      ((hZone z hz).z_subset (mem_singleton z))] at hOld
  change d {y} {z} ≤ d' (Λ y) (Λ z) + loss at hOld
  omega

/-- The region-incidence side condition of XV (3.5) in the proof of
XVI (8.1), Claim (4), page 72. The constant eight uses the valid
vertex-to-incident-region bound two. -/
theorem no_region_incident_two_cleared_boundaries
     (hS : IsClosedSurface S)
    {H : Drawing S} {Y : Set S} {Λ : S → Set S} {γ θ loss sep : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hY : Y ⊆ H.V)
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H Y Λ) θ loss T T' d d')
    {y z : S} (hy : y ∈ Y) (hz : z ∈ Y)
    (hsep : sep ≤ d {y} {z}) (hbudget : loss + 8 < sep) :
    ∀ r ∈ (clearEnvelopeDrawing H Y Λ).R,
      ¬ ((∃ u ∈ ((clearEnvelopeDrawing H Y Λ).interSet (subBd (Λ y))).V, u ∈ closure r) ∧
        ∃ v ∈ ((clearEnvelopeDrawing H Y Λ).interSet (subBd (Λ z))).V, v ∈ closure r) := by
  let K := clearEnvelopeDrawing H Y Λ
  have hyR : Λ y ∈ K.R := zone_mem_R_clearFamily hZone hdis hy
  have hzR : Λ z ∈ K.R := zone_mem_R_clearFamily hZone hdis hz
  have hyA : Λ y ∈ K.A := Or.inr hyR
  have hzA : Λ z ∈ K.A := Or.inr
    hzR
  obtain ⟨_, _, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} K
    (θ - loss) T' d' hS inferInstance hComp.hasMetric'
  have hprox := vertex_atom_dist_le_two hS hComp.hasMetric'
  intro r hr ⟨⟨u, hu, hur⟩, v, hv, hvr⟩
  have hu' := (mem_interSet_V_iff (show IsClosed (subBd (Λ y)) by
    rw [subBd_eq_frontier]; exact isClosed_frontier)).mp hu
  have hv' := (mem_interSet_V_iff (show IsClosed (subBd (Λ z)) by
    rw [subBd_eq_frontier]; exact isClosed_frontier)).mp hv
  have huA : ({u} : Set S) ∈ K.A := Or.inl (Or.inl ⟨u, hu'.1, rfl⟩)
  have hvA : ({v} : Set S) ∈ K.A := Or.inl (Or.inl ⟨v, hv'.1, rfl⟩)
  have hrA : r ∈ K.A := Or.inr hr
  have h₁ := hprox u hu'.1 (Λ y) hyA hu'.2.1
  have h₂ := hprox u hu'.1 r hrA hur
  have h₃ := hprox v hv'.1 r hrA hvr
  have h₄ := hprox v hv'.1 (Λ z) hzA hv'.2.1
  have ht₁ := htri (Λ y) hyA {u} huA (Λ z) hzA
  have ht₂ := htri {u} huA r hrA (Λ z) hzA
  have ht₃ := htri r hrA {v} hvA (Λ z) hzA
  rw [hsymm (Λ y) hyA {u} huA] at ht₁
  rw [hsymm r hrA {v} hvA] at ht₃
  have hNear : d' (Λ y) (Λ z) ≤ 8 := by omega
  have hOld := hComp.dist_le y z
  rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨y, hY hy, rfl⟩))
    (Or.inl (Or.inl ⟨z, hY hz, rfl⟩)) (mem_singleton y) (mem_singleton z),
    pointDist_eq_of_mem_atom hyA hzA ((hZone y hy).z_subset (mem_singleton y))
      ((hZone z hz).z_subset (mem_singleton z))] at hOld
  change d {y} {z} ≤ d' (Λ y) (Λ z) + loss at hOld
  omega

end GraphMinor.GM16
