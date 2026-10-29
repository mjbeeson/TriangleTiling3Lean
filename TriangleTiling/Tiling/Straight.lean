/-
A straight line of edges through a point.

If edges leave `Q` in two opposite directions, no tile containing `Q` crosses their line: it would
contain, near `Q`, interior points on one of the two edges. So when `Q` is interior to the target,
the angles at `Q` of the tiles on one side of the line add up to `π`
(`half_angle_sum`).
-/
import TriangleTiling.Tiling.HalfPlaneAngle
import TriangleTiling.Tiling.EdgesAt

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N)

/-- **No tile crosses a straight line of edges.** -/
theorem no_straddle {Q : Plane} {x e : Fin N × Fin 3} (hx : x ∈ edgesAt D Q)
    (he : e ∈ edgesAt D Q) {t : ℝ} (ht : t < 0)
    (hfar : farEnd D Q e = AffineMap.lineMap Q (farEnd D Q x) t)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c) (hgF : g (farEnd D Q x) = c)
    (i : Fin N) (hQi : Q ∈ (D.tile i).carrier) :
    (∀ y ∈ (D.tile i).carrier, g y ≤ c) ∨ (∀ y ∈ (D.tile i).carrier, c ≤ g y) := by
  set F := farEnd D Q x
  have hQF : Q ≠ F := (farEnd_ne D hx).symm
  have hcont := continuous_functional g
  by_contra hno
  push Not at hno
  obtain ⟨⟨z₂, hz₂, hgz₂⟩, ⟨z₁, hz₁, hgz₁⟩⟩ := hno
  -- Interior points of the tile on both sides.
  have hcl := tri_closure_interior (D.tile i)
  have side_pt : ∀ z ∈ (D.tile i).carrier, ∀ (p : ℝ → Prop), IsOpen {y : Plane | p (g y)} →
      p (g z) → ∃ w ∈ interior (D.tile i).carrier, p (g w) := by
    intro z hz p hp hpz
    rw [← hcl] at hz
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hz _ hp hpz
    exact ⟨w, hw2, hw1⟩
  obtain ⟨w₁, hw₁, hg₁⟩ := side_pt z₁ hz₁ (fun s => s < c)
    (isOpen_lt hcont continuous_const) hgz₁
  obtain ⟨w₂, hw₂, hg₂⟩ := side_pt z₂ hz₂ (fun s => c < s)
    (isOpen_lt continuous_const hcont) hgz₂
  -- Their segment crosses the line at an interior point `w`.
  set s := (c - g w₁) / (g w₂ - g w₁)
  have hden : 0 < g w₂ - g w₁ := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).mpr (by linarith)
  set w := AffineMap.lineMap w₁ w₂ s
  have hgw : g w = c := by
    simp only [w, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, s]
    field_simp
    ring
  have hw : w ∈ interior (D.tile i).carrier := by
    refine (D.tile i).convex.interior.segment_subset hw₁ hw₂ ?_
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨hs0, hs1⟩, rfl⟩
  -- `w` is on the line, so `w = lineMap Q F r` with `r ≠ 0`.
  obtain ⟨r, hr⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgw
  have hQint : Q ∉ interior (D.tile i).carrier := by
    have : Q ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    exact D.edge_point_not_interior this i
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [AffineMap.lineMap_apply_zero] at hr
    exact hQint (hr ▸ hw)
  -- Points between `Q` and `w` are interior, yet on one of the two edges.
  have hseg : openSegment ℝ Q w ⊆ interior (D.tile i).carrier :=
    (D.tile i).convex.openSegment_closure_interior_subset_interior (subset_closure hQi) hw
  have hL0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have hOS : openSegment ℝ Q w = AffineMap.lineMap Q F '' openSegment ℝ (0 : ℝ) r := by
    rw [image_openSegment, hL0, hr]
  have hex : (D.tile x.1).edge x.2 = AffineMap.lineMap Q F '' segment ℝ (0 : ℝ) 1 := by
    rw [edgesAt_edge D hx, image_segment, hL0, AffineMap.lineMap_apply_one]
  have hee : (D.tile e.1).edge e.2 = AffineMap.lineMap Q F '' segment ℝ (0 : ℝ) t := by
    rw [edgesAt_edge D he, image_segment, hL0, hfar]
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · set u := max r t / 2
    have hm : max r t < 0 := max_lt hneg ht
    have hu : u ∈ openSegment ℝ (0 : ℝ) r := by
      rw [openSegment_symm, openSegment_eq_Ioo hneg]
      constructor <;> simp only [u] <;> linarith [le_max_left r t]
    have hue : u ∈ segment ℝ (0 : ℝ) t := by
      rw [segment_symm, segment_eq_Icc ht.le]
      constructor <;> simp only [u] <;> linarith [le_max_right r t]
    have hP : AffineMap.lineMap Q F u ∈ interior (D.tile i).carrier := hseg (hOS ▸ ⟨u, hu, rfl⟩)
    have hPe : AffineMap.lineMap Q F u ∈ (D.tile e.1).edge e.2 := hee ▸ ⟨u, hue, rfl⟩
    exact D.edge_point_not_interior hPe i hP
  · set u := min r 1 / 2
    have hm : 0 < min r 1 := lt_min hpos one_pos
    have hu : u ∈ openSegment ℝ (0 : ℝ) r := by
      rw [openSegment_eq_Ioo hpos]
      constructor <;> simp only [u] <;> linarith [min_le_left r 1]
    have hux : u ∈ segment ℝ (0 : ℝ) 1 := by
      rw [segment_eq_Icc zero_le_one]
      constructor <;> simp only [u] <;> linarith [min_le_right r 1]
    have hP : AffineMap.lineMap Q F u ∈ interior (D.tile i).carrier := hseg (hOS ▸ ⟨u, hu, rfl⟩)
    have hPx : AffineMap.lineMap Q F u ∈ (D.tile x.1).edge x.2 := hex ▸ ⟨u, hux, rfl⟩
    exact D.edge_point_not_interior hPx i hP

open Classical in
/-- **Angles beside a straight line of edges.** If `Q` is interior to the target and edges leave
`Q` in two opposite directions, the angles at `Q` of the tiles on one side add up to `π`. -/
theorem straight_angle_sum {Q : Plane} (hQ : Q ∈ interior D.target.carrier)
    {x e : Fin N × Fin 3} (hx : x ∈ edgesAt D Q) (he : e ∈ edgesAt D Q) {t : ℝ} (ht : t < 0)
    (hfar : farEnd D Q e = AffineMap.lineMap Q (farEnd D Q x) t) :
    ∃ S : Finset (Fin N), ∑ i ∈ S, (D.tile i).localAngle Q = Real.pi := by
  obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne D hx)
  exact ⟨_, half_angle_sum D hQ hg hgQ
    (fun i hQi => no_straddle D hx he ht hfar hg hgQ hgF i hQi)⟩

end TriangleTiling
