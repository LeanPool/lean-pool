/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Reset.Attachment.WriteNet
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Carry

/-! # Load, width and table budgets of the elected reset -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K) (q : (frame S T u Δ R).state)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

local notation "a" => (T.scheme.h - r)
local notation "U" => (poll h s hk q)
local notation "hf" => (fits h s hk q P hc cost)
local notation "Q" => (History.Reset.Setup.result U P hf)
local notation "G" => (History.Reset.Setup.graph U P hf)
local notation "D" => (degreeBound S T Δ)
local notation "B₁" => (gain t * R.load)
local notation "b" => (book S T u t R)
local notation "N" => (next P S T u Δ t R a)

omit [NeZero Y] [NeZero l] in
open scoped Classical in
theorem gain_eq (t : ℕ) (R : Budget) (z : ℕ) :
    89 * ((2 : ℝ) ^ t * (R.load * z : ℕ)) = (gain t * R.load : ℕ) * (z : ℝ) := by
  simp only [gain, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

open scoped Classical in
theorem estimates :
    (∀ x y, (G).diagram.eval x y = q.val.G.diagram.eval x y) ∧
    (G).Bounded 3 (3 + terminalWidth D Y) ((B₁ : ℕ) * (S.z : ℝ)) ∧
    ((G).X : ℝ) ≤ 2 * resetWidth κ l * R.width + 2 * resetWidth κ l * (S.fringe.Z + σ) ∧
    S.first.Preserves G ∧ ((G).mass : ℝ) ≤ R.mass + 2 * R.width ∧
    S.first.Tracks G ((resetPositions P Δ + 1) * R.reach) := by
  obtain ⟨eval, _, bounds, width, preserve, mass, tracks⟩ := (U).bounds P hf (slack h s hk q)
  refine ⟨eval, ?_, ?_, q.val.preserved.trans preserve, ?_,
    q.property.tracks.trans tracks h.height (Nat.sub_le ..)⟩
  · rw [← gain_eq]; exact bounds
  · have hσ : 0 ≤ σ :=
      nonneg_of_mul_nonneg_left (le_trans (by positivity) h.slack) (by positivity)
    have hc' : 0 ≤ resetWidth κ l := by unfold resetWidth; positivity
    refine width.trans ?_
    calc
      _ ≤ resetWidth κ l * (2 * σ + 2 * R.width + 2 * S.fringe.Z) :=
        mul_le_mul_of_nonneg_left (add_le_add_left
          (add_le_add (by linarith only [hσ]) (mul_le_mul_of_nonneg_left q.property.width (by
            norm_num))) _) hc'
      _ = _ := by ring
  · rw [mass]
    change ((q.val.G.mass + 2 * q.val.G.X : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact add_le_add q.property.mass (mul_le_mul_of_nonneg_left q.property.width (by norm_num))

open scoped Classical in
theorem mass : (G).mass ≤ S.cap :=
  Nat.cast_le.mp ((estimates h s hk q P hc cost).2.2.2.2.1.trans h.history)

open scoped Classical in
theorem valid : (meter S t R).Valid G := by
  have hU := (Nat.le_of_dvd h.vpos h.divides).trans h.ceiling
  have hn : 2 ^ S.discount * B₁ * S.z < 2 ^ (c S t R) :=
    (Nat.mul_le_mul_left _ hU).trans_lt (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _))
  have ht : (2 : ℝ) ^ S.discount * ((B₁ : ℕ) * (S.z : ℝ)) < 2 ^ (c S t R) := by
    rw [← mul_assoc]
    exact_mod_cast hn
  have scale : (B₁ : ℕ) * (S.z : ℝ) < 1 * (2 : ℝ) ^ (c S t R) := by
    rw [one_mul]
    exact (le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans_lt ht
  exact Template.Meter.valid_of_charge G (c S t R) _ (mass h s hk q P hc cost)
    (estimates h s hk q P hc cost).2.1.2.2 scale ht (fun _ => ⟨1, Nat.cast_one.symm⟩)

omit [NeZero Y] [NeZero l] in
open scoped Classical in
private theorem widths (j : q.val.encodes.post.toPresentation.BorderSpan) :
    q.val.encodes.post.toPresentation.borderWidth j = S.U :=
  q.val.exterior_width _ j.property.2 j.property.1

open scoped Classical in
theorem room (v : Cell a × (Q).vertex) :
    Fintype.card (History.Reset.Visible q.val.encodes.post Q v) ≤ 2 ^ (e t R) := by
  have ht := History.Reset.seats_fit q.val.encodes.post Q v h.zpos (Nat.le_of_dvd h.vpos h.divides)
    (fun j => h.ceiling.trans_eq (widths q j).symm) (gain_eq t R S.z).le
  exact ht.2.2.trans (Nat.le_pow_clog (by decide) _)

open scoped Classical in
theorem ready [Fintype F] (A : History.Reset.Allocation q.val.encodes.post Q (N).scheme)
    (nav : B (N).scheme.m → B (N).scheme.d → B (N).scheme.m)
    (hop : ∀ (i : (Q).Survivors) z,
      let host := History.Reset.Allocation.endHost (q := Q)
      nav (A.host (host i z)) (A.index (host i z) (host i (!z))) = A.host (host i (!z))) :
    (b).Ready A nav := by
  have tag : History.Reset.Charged q.val.encodes.post (b).ord S.z R.tag :=
    fun v => q.property.tagged v.1 v.2
  apply (b).ready A nav _ hop ((U).result_simple P hf) q.property.neutral
    tag h.zpos (Nat.le_of_dvd h.vpos h.divides) (fun j => h.ceiling.trans_eq (widths q j).symm)
    (mass h s hk q P hc cost) (gain_eq t R S.z).le (Nat.le_pow_clog (by decide) _) le_rfl
  intro j
  exact History.Reset.Book.represent T.scheme u (e t R) (cap S T t R) T.order {S.U}
    (Finset.mem_singleton.mpr (widths q j))

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Tracking the exterior and the accumulated history through a reset -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K) (q : (frame S T u Δ R).state)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

omit [Fintype F] in
open scoped Classical in
private theorem swept (M : Snapshot.Data S T u) (B : Budget) {D c : ℕ} (ht : c ≤ B.tag)
    (live : Nonempty M.G.V) (tag : History.Reset.Charged M.encodes.post T.order S.z c)
    (bd : M.G.Bounded 3 D (B.load * S.z)) (tracks : S.first.Tracks M.G B.reach)
    (width : (M.G.X : ℝ) ≤ B.width) (mass : (M.G.mass : ℝ) ≤ B.mass) : Ready 3 B M.sweep := by
  refine ⟨live, M.sweep_neutral, ?_, ⟨bd.1, ?_, bd.2.2⟩, tracks, width, mass⟩
  · apply (M.sweep_tagged _).mpr
    intro v j hv
    exact (tag (v, j) hv).trans (Nat.mul_le_mul_right _ ht)
  · intro j
    have he : Fintype.card M.sweep.G.V ≤ 2 ^ T.scheme.m := by
      simpa using Fintype.card_le_of_injective _ M.sweep.encodes.post.host.injective
    exact (Finset.card_le_univ _).trans (he.trans (Nat.le_add_left _ _))

local notation "a" => (T.scheme.h - r)
local notation "U" => (poll h s hk q)
local notation "hf" => (fits h s hk q P hc cost)
local notation "Q" => (History.Reset.Setup.result U P hf)
local notation "G" => (History.Reset.Setup.graph U P hf)
local notation "N" => (next P S T u Δ t R a)

open scoped Classical in
/-- Information produced by the reset writer on each valid input. -/
structure Print where
  /-- The indexed rows of type `(N).format.obj`. -/
  rows : (N).format.obj
  /-- The `Print` component of type `(N).Encodes rows G`. -/
  encodes : (N).Encodes rows G
  /-- The selected move of type `Trail.Move T.scheme (N).scheme 0`. -/
  move : Trail.Move T.scheme (N).scheme 0
  agrees : move.Agrees q.val.encodes.post.toPresentation encodes.post.toPresentation
  charged : History.Reset.Charged encodes.post (N).order S.z (R.tag + added S T Δ t R Y)

namespace Print

variable {h s hk q P hc cost} (m : Print h s hk q P hc cost)
  (hr : resetPositions P Δ + 1 ≤ K)

open scoped Classical in
/-- Builds `Snapshot.Data S N u where rows` with the specified `rows`, `encodes`, `trail`,
`tracks`. -/
def result : Snapshot.Data S N u where
  rows := m.rows
  «G» := G
  encodes := m.encodes
  trail := m.move.update S.d q.val.trail
  tracks := by
    obtain ⟨_, _, _, preserve, _, tracks⟩ := estimates h s hk q P hc cost
    have slots : 0 < S.d := by
      have hk' : 0 < K := (Nat.two_pow_pos _).trans_le hk
      exact (Nat.mul_pos (by norm_num) (Nat.mul_pos hk' h.reach)).trans_le h.origins
    have hu := h.vpos.trans_le h.ceiling
    refine q.val.tracks.update m.agrees hu slots ?_
    intro v
    exact (S.origins G m.encodes.post preserve (tracks.mono (Nat.mul_le_mul_right _ hr))
      hu h.trivalent v).trans h.origins
  preserved := (estimates h s hk q P hc cost).2.2.2.1

open scoped Classical in
private theorem result_bounds (hg : gain t ≤ K) :
    (m.result hr).G.Bounded 3 (3 + terminalWidth (degreeBound S T Δ) Y)
      ((K * R.load : ℕ) * (S.z : ℝ)) := by
  have bounds := (estimates h s hk q P hc cost).2.1
  change (G).Bounded 3 _ _
  refine ⟨bounds.1, bounds.2.1, fun v j => (bounds.2.2 v j).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Nat.mul_le_mul_right R.load hg)) (Nat.cast_nonneg _)

open scoped Classical in
private theorem result_tracks :
    S.first.Tracks (m.result hr).G (K * R.reach) := by
  have tracks := (estimates h s hk q P hc cost).2.2.2.2.2
  change S.first.Tracks G _
  exact tracks.mono (Nat.mul_le_mul_right R.reach hr)

open scoped Classical in
private theorem result_live : Nonempty (m.result hr).G.V :=
  ⟨((Q).owner (Classical.choice q.property.live, 0)).2⟩

open scoped Classical in
private theorem result_charged :
    History.Reset.Charged (m.result hr).encodes.post (N).order S.z
      (R.tag + added S T Δ t R Y) :=
  m.charged

open scoped Classical in
private theorem result_width :
    ((m.result hr).G.X : ℝ) ≤ 2 * resetWidth κ l * R.width +
      2 * resetWidth κ l * (S.fringe.Z + σ) :=
  (estimates h s hk q P hc cost).2.2.1

open scoped Classical in
private theorem result_mass :
    ((m.result hr).G.mass : ℝ) ≤ R.mass + 2 * R.width :=
  (estimates h s hk q P hc cost).2.2.2.2.1

open scoped Classical in
theorem preserved (hg : gain t ≤ K) (ht : added S T Δ t R Y ≤ (Phase.rate S T r R) ^ K) :
    Ready 3 (Phase.after S T r R K (2 * resetWidth κ l) (2 * resetWidth κ l) σ) (m.result hr).sweep
      := by
  exact swept (D := 3 + terminalWidth (degreeBound S T Δ) Y) (m.result hr)
    (Phase.after S T r R K (2 * resetWidth κ l) (2 * resetWidth κ l) σ)
    (Nat.add_le_add_left ht R.tag) (result_live m hr) (result_charged m hr)
    (result_bounds m hr hg) (result_tracks m hr) (result_width m hr) (result_mass m hr)

end Print
end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Validating one elected reset layout at the phase scale -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K) (q : (frame S T u Δ R).state)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

local notation "a" => (T.scheme.h - r)
local notation "U" => (poll h s hk q)
local notation "hf" => (fits h s hk q P hc cost)
local notation "Q" => (History.Reset.Setup.result U P hf)
local notation "G" => (History.Reset.Setup.graph U P hf)
local notation "D" => (degreeBound S T Δ)
local notation "b" => (book S T u t R)
local notation "N" => (next P S T u Δ t R a)
local notation "shift" => History.Reset.Child.extra P Δ (T.scheme.h - a)
local notation "mx" => T.scheme.m + shift
local notation "dx" => History.Reset.Child.width D Y T.full
local notation "M" => (meter S t R)
local notation "par" => (History.Reset.Setup.parent T shift)

open scoped Classical in
/-- The assemble of type `Print h s hk q P hc cost` for the given inputs. -/
def assemble (A : (U).Layout P hf b mx dx) (g : (History.Reset.Child.Graph mx dx).obj)
    (blk : A.block = (cellIndex a).toEmbedding)
    (parent : ∀ i, par (A.host i) = q.val.encodes.post.host ((Q).origin i))
    (head : History.Reset.Child.Describes (m := mx) (d := dx) T.full G A.host A.index g) :
    Print h s hk q P hc cost := by
  have H := ready h s hk q P hc cost A g.1 (History.Reset.Setup.hop A g head)
  refine ⟨History.Reset.Setup.printed M A g,
    History.Reset.Setup.outputEncodes M A g H blk head (valid h s hk q P hc cost),
    A.move par, A.move_agrees H.lengths H.agrees par parent, ?_⟩
  have tag : History.Reset.Charged q.val.encodes.post (b).ord S.z R.tag :=
    fun v => q.property.tagged v.1 v.2
  have floor : ∀ j, u ≤ q.val.encodes.post.toPresentation.borderWidth j :=
    fun j => h.ceiling.trans_eq (q.val.exterior_width _ j.property.2 j.property.1).symm
  rw [added, ← add_assoc]
  exact H.charged tag h.zpos (Nat.le_of_dvd h.vpos h.divides) floor

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # A deterministic reset followed by scalar withdrawal -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Coloring

variable {F : Type} [Field F] {x y : Wire} {S : Setup F x y} {T N : Template F}
  {u Δ : ℕ} {R R' : Budget} {L : Set (Table F)} {k size : ℕ}
local notation "X" => frame S T u Δ R

open scoped Classical in
private theorem transfer (f : (X).state → Snapshot.Data S N u)
    (hr : ∀ i, Ready 3 R' (f i).sweep)
    (he : ∀ i x y, (f i).G.diagram.eval x y = i.val.G.diagram.eval x y)
    (net : Computes F k L (S.format T) (S.format N) (fun i => i.val.code)
      (fun i => (f i).code) (fun _ => 1) size)
    (hk : 3 ≤ k) (hw : 2 * N.scheme.ℓ ≤ k) (hs : Snapshot.sweepTable N ∈ L) :
    Transforms F k L X (frame S N.sweep u 3 R') (size + Snapshot.sweepCost S N) := by
  let W := Snapshot.restrict (fun j : Snapshot.Data S N u => Ready 3 R' j.sweep)
  have hw' : Transforms F k L X W size := by
    obtain ⟨g, ng, hg⟩ := net
    refine ⟨g, ng, fun i => ⟨Unit, inferInstance, fun _ => ⟨f i, hr i⟩, fun _ => 1, ?_, ?_⟩⟩
    · intro x y
      rw [Fintype.sum_unique, one_mul]
      exact (he i x y).symm
    · intro x y r
      rw [Fintype.sum_unique]
      exact hg i r
  exact hw'.comp (Snapshot.sweep (fun _ h => h) hk hw hs)

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore

namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

local notation "N" => (next P S T u Δ t R (T.scheme.h - r))

open scoped Classical in
/-- The writing circuit has to work only on the valid phase states.
The three numerical bounds describe fresh tables and the network cost. -/
structure Writer (few arity size : ℕ) where
  /-- The `Writer` component of type `∀ q, Print h s hk q P hc cost`. -/
  emit : ∀ q, Print h s hk q P hc cost
  /-- Stores the scale associated with this `Writer`. -/
  scale : ℕ
  /-- The label data of type `Finset (Table F)`. -/
  labels : Finset (Table F)
  count : labels.card ≤ few
  bound : ∀ i ∈ labels, Processor.arity i ≤ arity
  net : Computes F scale (Allowed F w ∪ (labels : Set (Table F))) (S.format T) (S.format N)
    (fun i => i.val.code) (fun i => ((emit i).rows, (emit i).move.update S.d i.val.trail)) (fun _
      => 1) size

namespace Writer
variable {h s hk P hc cost} {few arity size : ℕ} (z : Writer h s hk P hc cost few arity size)

local notation "R'" => Phase.after S T r R K (2 * resetWidth κ l) (2 * resetWidth κ l) σ

open scoped Classical in
theorem finish (hr : resetPositions P Δ + 1 ≤ K) (hg : gain t ≤ K)
    (ht : added S T Δ t R Y ≤ (Phase.rate S T r R) ^ K) :
    Transforms F (3 + 2 * (N).scheme.ℓ + z.scale)
      (Allowed F w ∪ (↑(insert (Snapshot.sweepTable N) z.labels) : Set (Table F)))
      (frame S T u Δ R) (frame S (N).sweep u 3 R') (size + Snapshot.sweepCost S N) := by
  let k := 3 + 2 * (N).scheme.ℓ + z.scale
  let L := Allowed F w ∪ (↑(insert (Snapshot.sweepTable N) z.labels) : Set (Table F))
  let f (i : (frame S T u Δ R).state) := (z.emit i).result hr
  have net : Computes F k L (S.format T) (S.format N) (fun i => i.val.code)
      (fun i => (f i).code) (fun _ => 1) size := by
    obtain ⟨g, hg, eqn⟩ := z.net
    exact ⟨g, hg.widen (Nat.le_add_left ..) (Set.union_subset_union_right _ (fun _ ht =>
      Finset.mem_insert_of_mem ht)), eqn⟩
  exact transfer f (fun i => (z.emit i).preserved hr hg ht)
    (fun i => (estimates h s hk i P hc cost).1) net
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
    ((Nat.le_add_left ..).trans (Nat.le_add_right ..)) (Or.inr (Finset.mem_insert_self ..))

end Writer
end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/-
# Uniformizing the parameters of a reset

The next degree allowance is independent of the incoming degree
allowance. The constants in the resource bounds can depend on both.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Phase Phase.Case Coloring

variable {F : Type} [Field F] {x y : Wire} {S : Setup F x y} {T : Template F}
  {u d : ℕ} {R : Budget} {w r K : ℕ} {σ : ℝ}

open scoped Classical in
/-- Uses `⟨x, y, S, T, R, w, r, u, u, K, σ, h⟩` as the representation. -/
abbrev sample (h : Input S T R w r 1 u u d K σ) : Case F 1 d :=
  ⟨x, y, S, T, R, w, r, u, u, K, σ, h⟩

variable [Fintype F] {Y l : ℕ} [NeZero Y] [NeZero l] {Δ t : ℕ}
  (P : Rotor F Y l) (s : Slice Δ Y l t) {κ : ℝ}
  (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

local notation "I" => Case F 1 d

open scoped Classical in
theorem rule_of_bounds {few arity size : I → ℕ} (M : ℕ)
    (hcount : Short few) (hwidth : Short arity) (hsize : Cost size)
    (build : ∀ {x y : Wire} {S : Setup F x y} {T : Template F} {R : Budget}
      {w r u K : ℕ} {σ : ℝ} (h : Input S T R w r 1 u u d K σ) (hk : 2 ^ t ≤ K), M ≤ K →
      Nonempty (Writer h s hk P hc cost (few (sample h)) (arity (sample h)) (size (sample h)))) :
    ∃ K, 0 < K ∧ Phase F Δ 3 d 2 1 K (2 * resetWidth κ l) (2 * resetWidth κ l) := by
  have child := child_bound P Δ t d
  obtain ⟨j₁, h₁⟩ := (added_bound (F := F) Δ t d Y).bound
  obtain ⟨j₂, h₂⟩ := (spans_bound (F := F) t d).bound
  obtain ⟨j₃, h₃⟩ := (meter_bound (F := F) t d).bound
  obtain ⟨j₄, h₄⟩ := bits_bound P Δ t d
  obtain ⟨j₅, h₅⟩ := (hcount.add (short_const 1)).bound
  obtain ⟨j₆, h₆⟩ := (hwidth.add (child.bits.add child.bits)).bound
  obtain ⟨j₇, h₇⟩ := hsize.add child.sweep
  let K := M + (resetPositions P Δ + 1) + Nat.clog 2 (resetPositions P Δ)
    + gain t + 2 ^ t + j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + j₇
  have hp := Nat.two_pow_pos t
  have hk : 2 ^ t ≤ K := by unfold K; omega
  refine ⟨K, hp.trans_le hk, ?_⟩
  intro x y S T R w r u v σ h
  have he : u = v := h.units.trans (one_mul _)
  subst v
  let i := sample h
  let N := next P S T u Δ t R (T.scheme.h - r)
  obtain ⟨z⟩ := build h hk (by unfold K; omega)
  have raised {n j : ℕ} (hn : 2 ≤ n) (hj : j ≤ K) : n ^ j ≤ n ^ K :=
    Nat.pow_le_pow_right (by omega) hj
  have ht := (h₁ i).trans (raised i.rate_two (by unfold K; omega))
  have run := z.finish (by unfold K; omega) (by unfold K; omega) ht
  refine ⟨⟨N.sweep, Nat.sub_add_cancel h.group, Nat.le_add_right .., ?_, (child_degree Δ d i).le,
    h.core, rfl, ?_, ?_, ?_, insert (Snapshot.sweepTable N) z.labels, ?_, ?_, _, _, ?_, run⟩⟩
  · change T.scheme.m + (T.scheme.h - (T.scheme.h - r) + Nat.clog 2 (resetPositions P Δ)) ≤ _
    rw [Nat.sub_sub_self h.group]
    unfold K
    omega
  · exact (h₂ i).trans (raised i.base_two (by unfold K; omega))
  · exact (h₃ i).trans (raised i.base_two (by unfold K; omega))
  · exact (h₄ i).trans (Nat.mul_le_mul_left _ (raised i.rate_two (by unfold K; omega)))
  · exact (Finset.card_insert_le ..).trans ((Nat.add_le_add_right z.count 1).trans
      ((h₅ i).trans (raised i.short_two (by unfold K; omega))))
  · intro k hmem
    refine le_trans ?_ ((h₆ i).trans (raised i.short_two (by unfold K; omega)))
    change Processor.arity k ≤ arity i + (N.scheme.ℓ + N.scheme.ℓ)
    rcases Finset.mem_insert.mp hmem with rfl | h'
    · simp only [Snapshot.sweepTable, Processor.arity, weightTable, Assembly.lookup, wd_word,
      Format.width_addr]
      exact Nat.le_add_left ..
    · exact (z.bound k h').trans (Nat.le_add_right ..)
  · exact (h₇ i).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (raised i.long_two (by unfold K; omega)))
      (Nat.mul_le_mul_left _ (raised i.short_two (by unfold K; omega))))

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Input records, exchange capacity and local reset costs -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K) (q : (frame S T u Δ R).state)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

local notation "a" => (T.scheme.h - r)
local notation "N" => (next P S T u Δ t R a)
open History.Reset

open scoped Classical in
/-- Computes the board by the application `History.Reset.electedBoard q.val.encodes (ok h s hk
q) s.enough s.space (unit h s)`. -/
abbrev board := History.Reset.electedBoard q.val.encodes (ok h s hk q) s.enough s.space (unit h s)

include h in
omit [Fintype F] in
open scoped Classical in
theorem access (j v scale : ℕ) (hj : j ≤ K * (S.h + 1)) (L : Set (Table F))
    (hw : 2 * 2 ^ (2 * w) * (4 * w) ≤ scale) :
    Access F scale (Allowed F w ∪ L) (T.scheme.m + j) v (Beat.accessCost (T.scheme.m + j) v) := by
  have htop : T.scheme.m + j ≤ 2 * w := (Nat.add_le_add_left hj _).trans h.upper
  have pos : 0 < w := by
    have hh : 0 < K * (S.h + 1) := Nat.mul_pos h.positive (Nat.zero_lt_succ S.h)
    have := h.upper
    omega
  have big : 2 * 2 ^ (T.scheme.m + j) * (4 * w) ≤ scale :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) htop))).trans
      hw
  exact (exchange F v pos (h.lower.trans (Nat.le_add_right ..)) htop big).widen le_rfl
    (fun _ ht => Or.inl (sort_allowed ht))

open scoped Classical in
/-- The issue width used in the `Restore` construction. -/
abbrev issueWidth (i : Phase.Case F 1 d) :=
  Tile.printWidth i.T (next P i.S i.T i.u Δ t i.R i.a) (Nat.clog 2 (i.height + 1))
    (i.n + 8) (History.Reset.Child.extra P Δ i.n)

open scoped Classical in
/-- The least binary width whose power of two reaches the stated size. -/
abbrev issueCost (i : Phase.Case F 1 d) (head : ℕ) :=
  let U := next P i.S i.T i.u Δ t i.R i.a
  let p := Nat.clog 2 (i.height + 1)
  Tile.printCost i.T U p (i.n + 8) (History.Reset.Child.extra P Δ i.n)
    (Beat.accessCost (i.m + i.T.scheme.d) (Tile.volume i.T U p (i.n + 8))) head

variable {h s hk q P hc cost}

open scoped Classical in
/-- The value specified by `(z.rows, z.move.commands)`. -/
abbrev Print.whole (z : Print h s hk q P hc cost) : (Tile.whole T N).obj :=
  (z.rows, z.move.commands)

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Local information needed for one deterministic reset -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

open History.Reset
local notation "a" => (T.scheme.h - r)
local notation "N" => (next P S T u Δ t R a)
local notation "X" => (frame S T u Δ R)
local notation "k" => Nat.clog 2 (T.scheme.h + 1)
local notation "n" => (T.scheme.h - a + 8)
local notation "extra" => History.Reset.Child.extra P Δ (T.scheme.h - a)
local notation "mx" => T.scheme.m + extra
local notation "dx" => History.Reset.Child.width (degreeBound S T Δ) Y T.full
local notation "par" => (History.Reset.Setup.parent T extra)

open scoped Classical in
/-- The data for the local print construction, including `out`, `nav`, `fields`, `headers`,
`control`. -/
structure LocalPrint where
  /-- The `LocalPrint` component of type `∀ i : (X).state, Print h s hk i P hc cost`. -/
  out : ∀ i : (X).state, Print h s hk i P hc cost
  nav : ∀ i : (X).state, (out i).move.nav = fun j _ => par j
  fields : Tile.Local T N k n extra (Nat.sub_le ..) rfl
    (fun i : (X).state => (board h s hk i).tape) (fun i => (out i).whole)
  /-- The `LocalPrint` component of type `(X).state → (Tile.headers T N extra).obj`. -/
  headers : (X).state → (Tile.headers T N extra).obj
  control : Tile.HeaderLocal T N k n extra (Nat.sub_le ..)
    (fun i : (X).state => (board h s hk i).tape) headers
  build : ∀ i : (X).state, Child.build T.scheme.m T.scheme.d extra dx
    (T.nav i.val.rows, headers i) = Tile.header N (out i).rows

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Sufficient local allocation properties for the two dictionary gates -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

open History.Reset

open scoped Classical in
/-- The selection used in the `Restore` construction. -/
abbrev selection := History.Reset.Setup.Selection
  (poll h s hk) P (fun i => fits h s hk i P hc cost) (board h s hk)
  (book S T u t R) (meter S t R) (Nat.sub_le T.scheme.h r)

variable {h s hk P hc cost}

open scoped Classical in
/-- Builds `LocalPrint h s hk P hc cost where out i` with the specified `out`, `nav`, `fields`,
`intro`. -/
def arrange (A : selection h s hk P hc cost) : LocalPrint h s hk P hc cost where
  out i := assemble h s hk i P hc cost (A.layout i) (A.graph i)
    (A.placed i).block (A.placed i).parent (A.describes i)
  nav _ := rfl
  fields := by
    intro i
    have d := ok h s hk i
    exact A.fields (d.corePos.trans_le d.full) d.late (fun j => j.property.neutral)
      (fun j => ready h s hk j P hc cost (A.layout j) (A.graph j).1
        (History.Reset.Setup.hop _ _ (A.describes j))) i
  headers := A.headers
  control := A.control
  build := A.build

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Controller combining the mixer and the two local dictionary gates -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

open History.Reset
local notation "N" => (next P S T u Δ t R (T.scheme.h - r))
local notation "X" => (frame S T u Δ R)
local notation "k" => Nat.clog 2 (T.scheme.h + 1)
local notation "n" => (T.scheme.h - (T.scheme.h - r) + 8)
local notation "extra" => History.Reset.Child.extra P Δ (T.scheme.h - (T.scheme.h - r))
local notation "mx" => T.scheme.m + extra
local notation "dx" => History.Reset.Child.width (degreeBound S T Δ) Y T.full
local notation "par" => (History.Reset.Setup.parent T extra)

open scoped Classical in
/-- The value specified by `Template.Mix.arity i.T (keyBits d i) (indices i.S i.r i.R Δ)`. -/
abbrev setupWidth (i : Phase.Case F 1 d) := Template.Mix.arity i.T (keyBits d i) (indices i.S i.r
    i.R Δ)
open scoped Classical in
/-- The quantity computed by `Template.Mix.cost i.T (keyBits d i) (indices i.S i.r i.R Δ)
(i.height - t - i.a)`. -/
abbrev setupCost (i : Phase.Case F 1 d) :=
  Template.Mix.cost i.T (keyBits d i) (indices i.S i.r i.R Δ) (i.height - t - i.a)
open scoped Classical in
/-- The value specified by `Tile.headerWidth i.T (child P Δ t d i) (keyBits d i) (depth d i)
(expansion P Δ d i)`. -/
abbrev graphWidth (i : Phase.Case F 1 d) :=
  Tile.headerWidth i.T (child P Δ t d i) (keyBits d i) (depth d i) (expansion P Δ d i)
open scoped Classical in
/-- The graph cost used in the `Restore` construction. -/
abbrev graphCost (i : Phase.Case F 1 d) :=
  Tile.headerCost i.T (child P Δ t d i) (keyBits d i) (depth d i) (expansion P Δ d i) (readCost P Δ
    t d i) +
    4 * Child.buildCost i.m i.T.scheme.d (expansion P Δ d i) (child P Δ t d i).scheme.d

open scoped Classical in
/-- The quantity computed by `setupWidth (Δ:=Δ) i + graphWidth (Δ:=Δ) (t:=t) P i + issueWidth
(Δ:=Δ) (t:=t) P i`. -/
abbrev width (i : Phase.Case F 1 d) := setupWidth (Δ:=Δ) i + graphWidth (Δ:=Δ) (t:=t) P i +
    issueWidth (Δ:=Δ) (t:=t) P i
open scoped Classical in
/-- The value specified by `setupCost (Δ:=Δ) (t:=t) i + issueCost (Δ:=Δ) (t:=t) P i (graphCost
(Δ:=Δ) (t:=t) P i) + applyCost i.S i.T (child P Δ t d i)`. -/
abbrev total (i : Phase.Case F 1 d) := setupCost (Δ:=Δ) (t:=t) i +
    issueCost (Δ:=Δ) (t:=t) P i (graphCost (Δ:=Δ) (t:=t) P i) + applyCost i.S i.T (child P Δ t d i)

variable {h s hk P hc cost}
local notation "z" => indices S r R Δ
local notation "i₀" => sample h

open scoped Classical in
private theorem LocalPrint.write_computes (L : LocalPrint h s hk P hc cost)
    {v : ℕ} {allow : Set (Table F)} (three : 3 ≤ v)
    (pre : Computes F v allow T.format (Tile.pair T k)
      (fun i : (X).state => i.val.rows) (fun i => (board h s hk i).tape)
      (fun _ => 1) (setupCost (Δ := Δ) (t := t) i₀))
    (body : Computes F v allow (Tile.pair T k) (Tile.whole T N)
      (fun i : (X).state => (board h s hk i).tape) (fun i => (L.out i).whole)
      (fun _ => 1) (issueCost (Δ := Δ) (t := t) P i₀ (graphCost (Δ := Δ) (t := t) P i₀))) :
    Computes F v allow (S.format T) (S.format N) (fun i => i.val.code)
      (fun i => ((L.out i).rows, (L.out i).move.update S.d i.val.trail))
      (fun _ => 1) (total (Δ := Δ) (t := t) P i₀) := by
  have run := pre.comp body
  simp only [one_mul] at run
  exact apply_net three (fun i : (X).state => i.val) (fun i => (L.out i).rows)
    (fun i => (L.out i).move) par L.nav run

private abbrev mixParameters (S : Setup F x y) (T : Template F) (u Δ t r : ℕ) (R : Budget) :
    Template.Mix.Params :=
  ⟨T.scheme.h - r, u, Δ, degreeBound S T Δ, 2 ^ S.discount, Template.Encodes.margin Δ,
    (2 : ℝ) ^ t * (R.load * S.z : ℕ)⟩

omit [Fintype F] [NeZero Y] [NeZero l] in
open scoped Classical in
private theorem write_prepares {v : ℕ} {allow : Set (Table F)}
    (fits : Template.Mix.arity T k z ≤ v)
    (keys : (Template.Mix.keys T k z (mixParameters S T u Δ t r R) : Set (Table F)) ⊆ allow) :
    Computes F v allow T.format (Tile.pair T k)
      (fun i : (X).state => i.val.rows) (fun i => (board h s hk i).tape)
      (fun _ => 1) (setupCost (Δ := Δ) (t := t) i₀) := by
  have hkey : T.scheme.h < 2 ^ k := Nat.le_pow_clog (by decide : 1 < 2) _
  exact Computes.of_map
    (Template.Mix.prepare_net T k z (mixParameters S T u Δ t r R) fits keys t hkey)
    (fun _ => rfl)

omit [Field F] [Fintype F] in
open scoped Classical in
private theorem write_label_bounds (keys : Finset (Table F)) (body gate : Table F) {g f b : ℕ}
    (few : keys.card ≤ 12) (limited : ∀ j ∈ keys, Processor.arity j ≤ g)
    (bodyArity : Processor.arity body ≤ b) (gateArity : Processor.arity gate ≤ f) :
    (insert body (insert gate keys)).card ≤ 14 ∧
      ∀ j ∈ insert body (insert gate keys), Processor.arity j ≤ g + f + b := by
  constructor
  · iterate 2
      apply (Finset.card_insert_le ..).trans
      apply Nat.add_le_add_right
    exact few
  · intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact bodyArity.trans (Nat.le_add_left ..)
    · exact (gateArity.trans (Nat.le_add_left ..)).trans (Nat.le_add_right ..)
    · exact ((limited j hj).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

omit [NeZero Y] [NeZero l] in
open scoped Classical in
private theorem sample_width :
    width (Δ := Δ) (t := t) P i₀ =
      Template.Mix.arity T k z + Tile.headerWidth T N k n extra + Tile.printWidth T N k n extra :=
  rfl

open scoped Classical in
theorem LocalPrint.write (L : LocalPrint h s hk P hc cost) (hd : d ≤ K) :
    Nonempty (Writer h s hk P hc cost 14 (width (Δ:=Δ) (t:=t) P i₀) (total (Δ:=Δ) (t:=t) P i₀))
      := by
  obtain ⟨body, gate, hbody, eqn, net⟩ := Tile.writer_net T N k n extra (Nat.sub_le ..) rfl
    (fun i : (X).state => (board h s hk i).tape) (fun i : (X).state => (L.out i).whole)
    L.headers L.fields L.control L.build (fun i => i.val.encodes.reciprocal) (by omega)
  let C := mixParameters S T u Δ t r R
  let keys := Template.Mix.keys T k z C
  let labels := insert body (insert gate keys)
  let allow := Allowed F w ∪ (labels : Set (Table F))
  let g := Template.Mix.arity T k z
  let f := Tile.headerWidth T N k n extra
  let b := Tile.printWidth T N k n extra
  let v := 3 + g + f + b + 2 * 2 ^ (2 * w) * (4 * w)
  have three : 3 ≤ v := by unfold v; omega
  have gf : g ≤ v := by unfold v; omega
  have ff : f ≤ v := by unfold v; omega
  have bf : b ≤ v := by unfold v; omega
  have acc := access h T.scheme.d (Tile.volume T N k n) v
    (h.degree.trans (hd.trans (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _))))
    (↑labels) (Nat.le_add_left ..)
  have kernels : (keys : Set (Table F)) ⊆ allow :=
    fun _ ht => Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht))
  have pre := write_prepares (h := h) (s := s) (hk := hk) gf kernels
  have both : Computes F v allow (Tile.pair T k) (Tile.whole T N)
      (fun i : (X).state => (board h s hk i).tape) (fun i => (L.out i).whole)
      (fun _ => 1) (issueCost (Δ := Δ) (t := t) P i₀ (graphCost (Δ := Δ) (t := t) P i₀)) :=
    net (L := allow) three bf ff (Or.inr (Finset.mem_insert_self ..))
      (Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))) acc
  have final := L.write_computes three pre both
  obtain ⟨count, narrow⟩ := write_label_bounds keys body gate (Template.Mix.few T k z C)
    (fun _ hj => Template.Mix.narrow T k z C hj) hbody.le eqn.le
  refine ⟨⟨L.out, v, labels, count, ?_, ?_⟩⟩
  · rw [sample_width (h := h)]
    exact narrow
  · exact final

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/- # Closing the uniform reset bounds -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Phase Phase.Case
variable {F : Type} [Field F] [Fintype F]

theorem phase_of_local {Y l Δ t d : ℕ} [NeZero Y] [NeZero l] (P : Rotor F Y l)
    (s : Slice Δ Y l t) {κ : ℝ} (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)
    (build : ∀ {x y : Wire} {S : Setup F x y} {T : Template F} {R : Budget}
      {w r u K : ℕ} {σ : ℝ} (h : Input S T R w r 1 u u d K σ) (hk : 2 ^ t ≤ K),
      Nonempty (LocalPrint h s hk P hc cost)) :
    ∃ K, 0 < K ∧ Phase F Δ 3 d 2 1 K (2 * resetWidth κ l) (2 * resetWidth κ l) := by
  have hw : Short (width (Δ:=Δ) (t:=t) (d:=d) P) :=
    ((summaryWidth Δ d).add (headerWidth_bound P Δ t d)).add (printWidth_bound P Δ t d)
  have hm : Cost (total (Δ:=Δ) (t:=t) (d:=d) P) :=
    ((summaryCost Δ t d).add (printCost_bound P Δ t d (headerCost_bound P Δ t d))).add
      (applyCost_bound (child_bound P Δ t d))
  refine rule_of_bounds P s hc cost d (short_const 14) hw hm ?_
  intro x y S T R w r u K σ h hk hd
  obtain ⟨out⟩ := build h hk
  exact out.write hd

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
end

/-
# A controlled degree reset over a finite field

The elected layout supplies both the local tensor description and
the graph header. The two resulting gates work on every input
branch of the phase with the same cost bounds.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore
open Assembly Packing Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y l : ℕ} [NeZero Y] [NeZero l]
  {S : Setup F x y} {T : Template F} {u Δ t : ℕ} {R : Budget} {w r d K : ℕ} {σ κ : ℝ}
  (h : Phase.Input S T R w r 1 u u d K σ)
  (s : Slice Δ Y l t) (hk : 2 ^ t ≤ K)
  (P : Rotor F Y l) (hc : 1 ≤ κ) (cost : (Fintype.card P.E : ℝ) ≤ κ * Y * l)

open scoped Classical in
theorem choose_layout : Nonempty (LocalPrint h s hk P hc cost) := by
  have enough (i : (frame S T u Δ R).state) : (poll h s hk i).Room P (fits h s hk i P hc cost)
      (next P S T u Δ t R (T.scheme.h - r)).scheme := room h s hk i P hc cost
  let A : selection h s hk P hc cost := History.Reset.Setup.select
    (poll h s hk) P (fun i => fits h s hk i P hc cost) (board h s hk)
    (book S T u t R) (meter S t R) (Nat.sub_le T.scheme.h r) enough
  exact ⟨arrange A⟩

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent.Restore

namespace MatrixMultiplicationAllFields.MatrixExponent.BatchDescent
open Restore Packing

theorem resetRule (F : Type) [Field F] [Finite F] : ResetRule F := by
  let : Fintype F := Fintype.ofFinite F
  intro y w Δ P κ hw hΔ hy hc hcost
  let _ : NeZero w := ⟨hw.ne'⟩
  have cost : (Fintype.card P.E : ℝ) ≤ κ * (2 ^ y : ℕ) * w
    := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcost
  obtain ⟨t, s⟩ := exists_slice Δ (2 ^ y) w hy hΔ
  refine ⟨2, fun d => phase_of_local P s hc cost ?_⟩
  intro x y S T R w r u K σ h hk
  exact choose_layout h s hk P hc cost

end MatrixMultiplicationAllFields.MatrixExponent.BatchDescent
end
