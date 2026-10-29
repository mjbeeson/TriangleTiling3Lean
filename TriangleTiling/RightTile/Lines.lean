/-
Lines of a tiling (for the parity argument of `theorem:isosceles2`).

* `lineSet P Q`: the line through `P ≠ Q`; two distinct points on it span the same line, and the
  direction `dirC` is the same along it.
* `edge_internal_or_side`: a tile edge either runs (apart from its ends) through the interior of
  the tiled triangle, or lies on one of its sides.
* `line_balance`: on a line all of whose edges run through the interior, the edges of the tiles on
  the two sides have the same total length (both sides cover each edge exactly once, by
  Bonfioli's `Dissection.wall_partition`, so the two sums can be swapped).
* `side_sum`: the edges lying on a side of the tiled triangle add up to its length.
-/
import TriangleTiling.RightTile.Direction
import TriangleTiling.Isosceles.N4Helper
import TriangleTiling.Isosceles.QandR
import Erdos634.WallChain

namespace TriangleTiling

open Erdos634.Geometry MeasureTheory

/-! ### Lines -/

theorem cross_apply (u v : Plane) : cross u v = u 0 * v 1 - u 1 * v 0 := rfl

theorem coords_ne {v : Plane} (hv : v ≠ 0) : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  ext i; fin_cases i <;> simp [h.1, h.2]

/-- In the plane, two vectors parallel to a nonzero `v` are parallel. -/
theorem cross_trans {v w x : Plane} (hv : v ≠ 0) (hw : cross v w = 0) (hx : cross v x = 0) :
    cross w x = 0 := by
  rw [cross_apply] at *
  have e0 : v 0 * (w 0 * x 1 - w 1 * x 0) = 0 := by linear_combination w 0 * hx - x 0 * hw
  have e1 : v 1 * (w 0 * x 1 - w 1 * x 0) = 0 := by linear_combination w 1 * hx - x 1 * hw
  rcases coords_ne hv with h | h
  · exact (mul_eq_zero.mp e0).resolve_left h
  · exact (mul_eq_zero.mp e1).resolve_left h

theorem cross_comm_zero {v w : Plane} (h : cross v w = 0) : cross w v = 0 := by
  rw [cross_apply] at *; linarith

theorem cross_sub_eq (v x y z : Plane) : cross v (x - z) = cross v (x - y) + cross v (y - z) := by
  simp only [cross_apply, PiLp.sub_apply]; ring

/-- A vector parallel to a nonzero `v` is a multiple of it. -/
theorem eq_smul_of_cross {v w : Plane} (hv : v ≠ 0) (h : cross v w = 0) :
    ∃ t : ℝ, w = t • v := by
  rw [cross_apply] at h
  rcases coords_ne hv with h0 | h1
  · refine ⟨w 0 / v 0, ?_⟩
    ext i; fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp; field_simp; linarith
  · refine ⟨w 1 / v 1, ?_⟩
    ext i; fin_cases i
    · simp; field_simp; linarith
    · simp [div_mul_cancel₀ _ h1]

/-- The line through `P` and `Q`. -/
def lineSet (P Q : Plane) : Set Plane := {y | cross (Q - P) y = cross (Q - P) P}

theorem mem_lineSet_iff {P Q y : Plane} : y ∈ lineSet P Q ↔ cross (Q - P) (y - P) = 0 := by
  simp only [lineSet, Set.mem_setOf_eq, cross_apply, PiLp.sub_apply]
  constructor <;> intro h <;> linarith

theorem left_mem_lineSet (P Q : Plane) : P ∈ lineSet P Q := by
  rw [mem_lineSet_iff, sub_self]; exact cross_zero_right _

theorem right_mem_lineSet (P Q : Plane) : Q ∈ lineSet P Q := by
  rw [mem_lineSet_iff]; exact cross_self _

theorem segment_subset_lineSet (P Q : Plane) : segment ℝ P Q ⊆ lineSet P Q := by
  intro y hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [mem_lineSet_iff]
  simp only [cross_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have : a = 1 - b := by linarith
  subst this; ring

/-- Two distinct points of a line span it. -/
theorem lineSet_eq {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hP'Q' : P' ≠ Q')
    (hP' : P' ∈ lineSet P Q) (hQ' : Q' ∈ lineSet P Q) : lineSet P' Q' = lineSet P Q := by
  rw [mem_lineSet_iff] at hP' hQ'
  have hv : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hv' : Q' - P' ≠ 0 := sub_ne_zero.mpr hP'Q'.symm
  have hvv : cross (Q - P) (Q' - P') = 0 := by
    rw [cross_sub_eq _ Q' P P']
    have : cross (Q - P) (P - P') = - cross (Q - P) (P' - P) := by
      simp only [cross_apply, PiLp.sub_apply]; ring
    rw [this, hP', hQ']; ring
  ext y
  rw [mem_lineSet_iff, mem_lineSet_iff]
  constructor
  · intro h
    have h1 := cross_trans hv' (cross_comm_zero hvv) h
    rw [cross_sub_eq _ y P' P, h1, hP', add_zero]
  · intro h
    have h1 : cross (Q - P) (y - P') = 0 := by
      have := cross_sub_eq (Q - P) y P' P
      rw [h, hP'] at this; linarith
    exact cross_trans hv hvv h1

/-- The direction is the same along a line. -/
theorem dirC_lineSet {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hP'Q' : P' ≠ Q')
    (hP' : P' ∈ lineSet P Q) (hQ' : Q' ∈ lineSet P Q) : dirC (Q' - P') = dirC (Q - P) := by
  rw [mem_lineSet_iff] at hP' hQ'
  have hv : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hv' : Q' - P' ≠ 0 := sub_ne_zero.mpr hP'Q'.symm
  apply dirC_of_cross hv hv'
  rw [cross_sub_eq _ Q' P P']
  have : cross (Q - P) (P - P') = - cross (Q - P) (P' - P) := by
    simp only [cross_apply, PiLp.sub_apply]; ring
  rw [this, hP', hQ']; ring

/-- A point of the line `PQ` is `P + t (Q - P)`. -/
theorem eq_lineMap_of_mem_lineSet {P Q y : Plane} (hPQ : P ≠ Q) (hy : y ∈ lineSet P Q) :
    ∃ t : ℝ, y = P + t • (Q - P) := by
  rw [mem_lineSet_iff] at hy
  obtain ⟨t, ht⟩ := eq_smul_of_cross (sub_ne_zero.mpr hPQ.symm) hy
  exact ⟨t, by rw [← ht]; abel⟩

/-! ### Edges -/

variable {N : ℕ} (D : Dissection N)

theorem tile_pts_ne (i : Fin N) (k : Fin 3) : (D.tile i).pts k ≠ (D.tile i).pts (k + 1) := by
  intro h
  have h1 := (D.tile i).indep.injective h
  have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
  exact h2 k h1

/-- The line of a tile edge. -/
def edgeLine (e : Fin N × Fin 3) : Set Plane :=
  lineSet ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

theorem edge_subset_target (e : Fin N × Fin 3) : (D.tile e.1).edge e.2 ⊆ D.target.carrier :=
  ((D.tile e.1).edge_subset_carrier e.2).trans (tile_subset_target D e.1)

/-- If a point strictly inside `PQ` (with `P, Q` in the target) lies on side `i`, so does `PQ`. -/
theorem segment_subset_side_of_mem {P Q y : Plane} {i : Fin 3} (hP : P ∈ D.target.carrier)
    (hQ : Q ∈ D.target.carrier) (hy : y ∈ openSegment ℝ P Q)
    (hyi : y ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1))) :
    segment ℝ P Q ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨f, c, -, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  have hS := target_contact_side D.target f c hle hi hi1 hi2
  rw [← hS] at hyi ⊢
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hfy := hyi.2
  simp only [map_add, map_smul, smul_eq_mul] at hfy
  have hfP := hle P hP
  have hfQ := hle Q hQ
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  have h1 : a * f P ≤ a * c := mul_le_mul_of_nonneg_left hfP ha.le
  have h2 : b * f Q ≤ b * c := mul_le_mul_of_nonneg_left hfQ hb.le
  have e1 : f P = c := by
    by_contra h
    have := mul_lt_mul_of_pos_left (lt_of_le_of_ne hfP h) ha
    linarith
  have e2 : f Q = c := by
    by_contra h
    have := mul_lt_mul_of_pos_left (lt_of_le_of_ne hfQ h) hb
    linarith
  exact (Convex.segment_subset (by
    intro x hx z hz s t hs ht hst
    refine ⟨D.target.convex hx.1 hz.1 hs ht hst, ?_⟩
    simp only [map_add, map_smul, smul_eq_mul, hx.2, hz.2]
    rw [← add_mul, hst, one_mul]) ⟨hP, e1⟩ ⟨hQ, e2⟩)

/-- **A tile edge runs through the interior, or lies on a side.** -/
theorem edge_internal_or_side (e : Fin N × Fin 3) :
    openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆
        interior D.target.carrier ∨
      ∃ i : Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨hni, hside⟩ := h
  obtain ⟨y, hy, hyint⟩ := Set.not_subset.mp hni
  have hP := edge_subset_target D e (left_mem_segment ℝ _ _)
  have hQ := edge_subset_target D e (right_mem_segment ℝ _ _)
  have hyc : y ∈ D.target.carrier :=
    edge_subset_target D e (openSegment_subset_segment ℝ _ _ hy)
  have hfr : y ∈ frontier D.target.carrier := ⟨subset_closure hyc, hyint⟩
  rcases tri_frontier_subset_sides D.target hfr with h0 | h1 | h2
  · exact hside 0 (segment_subset_side_of_mem D hP hQ hy h0)
  · exact hside 1 (segment_subset_side_of_mem D hP hQ hy h1)
  · exact hside 2 (segment_subset_side_of_mem D (i := 2) hP hQ hy h2)

/-! ### The two sides of a line -/

/-- **Line balance.** If every edge on the line `{f = c}` runs through the interior, the edges of
the tiles on the two sides of the line have the same total length. -/
theorem line_balance (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hint : ∀ e ∈ D.lineChain f c ∪ D.lineChain (-f) (-c),
      openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆
        interior D.target.carrier) :
    ∑ e ∈ D.lineChain f c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      ∑ e ∈ D.lineChain (-f) (-c), dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  set μ := (Measure.hausdorffMeasure 1 : Measure Plane)
  set near := D.lineChain f c
  set far := D.lineChain (-f) (-c)
  have hnear : ∀ e ∈ near, ∑ e' ∈ far, μ ((D.tile e'.1).edge e'.2 ∩ (D.tile e.1).edge e.2) =
      μ ((D.tile e.1).edge e.2) := by
    intro e he
    have hE := D.lineChain_edge_subset he
    exact D.wall_partition (-f) (-c) (neg_ne_zero.mpr hf) (tile_pts_ne D e.1 e.2)
      (fun y hy => by simp [hE y hy]) (hint e (Finset.mem_union_left _ he))
      (fun y hy => D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy))
  have hfar : ∀ e ∈ far, ∑ e' ∈ near, μ ((D.tile e'.1).edge e'.2 ∩ (D.tile e.1).edge e.2) =
      μ ((D.tile e.1).edge e.2) := by
    intro e he
    have hE := D.lineChain_edge_subset he
    exact D.wall_partition f c hf (tile_pts_ne D e.1 e.2)
      (fun y hy => by have := hE y hy; simp at this; simpa using this)
      (hint e (Finset.mem_union_right _ he))
      (fun y hy => D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy))
  have hμ : ∑ e ∈ near, μ ((D.tile e.1).edge e.2) = ∑ e ∈ far, μ ((D.tile e.1).edge e.2) := by
    calc ∑ e ∈ near, μ ((D.tile e.1).edge e.2)
        = ∑ e ∈ near, ∑ e' ∈ far, μ ((D.tile e'.1).edge e'.2 ∩ (D.tile e.1).edge e.2) :=
          Finset.sum_congr rfl fun e he => (hnear e he).symm
      _ = ∑ e' ∈ far, ∑ e ∈ near, μ ((D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
            rw [Set.inter_comm]
      _ = ∑ e ∈ far, μ ((D.tile e.1).edge e.2) := Finset.sum_congr rfl fun e he => hfar e he
  have hconv : ∀ s : Finset (Fin N × Fin 3), ∑ e ∈ s, μ ((D.tile e.1).edge e.2) =
      ENNReal.ofReal (∑ e ∈ s, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)]
    exact Finset.sum_congr rfl fun e _ => by rw [Tri.hausdorff_edge, edist_dist]
  rw [hconv, hconv] at hμ
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun _ _ => dist_nonneg)
    (Finset.sum_nonneg fun _ _ => dist_nonneg)).mp hμ

open Classical in
/-- **The edges on a side add up to its length.** -/
theorem side_sum (i : Fin 3) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin N × Fin 3 =>
        (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1))),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.target.pts i) (D.target.pts (i + 1)) := by
  set Pt := Finset.univ.filter (fun e : Fin N × Fin 3 =>
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  have hS := target_contact_side D.target f c hle hi hi1 hi2
  obtain ⟨part, hcov, -, -⟩ := D.side_walk i
  have hline : ∀ e ∈ Pt, ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
    intro e he y hy
    have h1 := (Finset.mem_filter.mp he).2 hy
    rw [← hS] at h1
    exact h1.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hsum := sum_hausdorff_of_partition Pt (fun e => (D.tile e.1).edge e.2)
    (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) ∅ Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    (fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton f c hf hne (hleT e₁) (hleT e₂)
      (hline e₁ h₁) (hline e₂ h₂))
    (fun e he => (Finset.mem_filter.mp he).2)
    (by
      intro y hy
      rw [Set.diff_empty, ← hcov] at hy
      obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hye⟩
      intro z hz
      rw [← hcov]
      exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)
  rw [MeasureTheory.hausdorffMeasure_segment] at hsum
  have h1 : ENNReal.ofReal
      (∑ e ∈ Pt, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) =
      ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg), ← edist_dist, ← hsum]
    exact Finset.sum_congr rfl fun e _ => by rw [Tri.hausdorff_edge, edist_dist]
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun _ _ => dist_nonneg)
    dist_nonneg).mp h1

end TriangleTiling
