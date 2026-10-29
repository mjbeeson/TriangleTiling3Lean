/-
Local angles at a point of a tiling.

The tiles' local angles at a point add up to the target's (Bonfioli's `sum_localAngle_eq`), and
the target's local angle exceeds `π` only at interior points. So a point lying inside edges of two
tiles, or at a vertex of one tile and inside an edge of another, is interior to the target; and at
a vertex of the tiling at most one tile has the point inside one of its edges.
-/
import Erdos634.MarchFlank
import TriangleTiling.Isosceles.No28Lines

namespace TriangleTiling

open Erdos634.Geometry

theorem Tri.localAngle_le_two_pi (T : Tri) (p : Plane) : T.localAngle p ≤ 2 * Real.pi := by
  classical
  rw [Tri.localAngle]
  split
  · exact le_trans (EuclideanGeometry.angle_le_pi _ _ _) (by linarith [Real.pi_pos])
  · split
    · exact le_rfl
    · split <;> linarith [Real.pi_pos]

theorem Tri.localAngle_le_pi (T : Tri) {p : Plane} (hp : p ∉ interior T.carrier) :
    T.localAngle p ≤ Real.pi := by
  classical
  rw [Tri.localAngle]
  split
  · exact EuclideanGeometry.angle_le_pi _ _ _
  · split
    · rename_i h; exact absurd ((Tri.mem_interior_iff_coord_pos T p).mpr h) hp
    · split <;> linarith [Real.pi_pos]

/-- A vertex of a triangle is inside none of its edges. -/
theorem Tri.vertex_not_mem_openSegment (T : Tri) (k m : Fin 3) :
    T.pts k ∉ openSegment ℝ (T.pts m) (T.pts (m + 1)) := by
  intro h
  obtain ⟨h0, h1, h2⟩ := Tri.coord_openSegment T m h
  rw [Tri.coord_vertex] at h0 h1 h2
  rcases fin3_cases3 k m with rfl | rfl | rfl
  · have : ¬ (k + 1 = k) := by fin_cases k <;> decide
    simp [this] at h1
  · have : ¬ (m = m + 1) := by fin_cases m <;> decide
    simp [this] at h0
  · have : ¬ (m = m + 2) := by fin_cases m <;> decide
    simp [this] at h0

/-- A point lies inside at most one edge of a triangle. -/
theorem Tri.openSegment_edge_unique (T : Tri) {m m' : Fin 3} {p : Plane}
    (h : p ∈ openSegment ℝ (T.pts m) (T.pts (m + 1)))
    (h' : p ∈ openSegment ℝ (T.pts m') (T.pts (m' + 1))) : m = m' := by
  obtain ⟨a0, a1, a2⟩ := Tri.coord_openSegment T m h
  obtain ⟨b0, b1, b2⟩ := Tri.coord_openSegment T m' h'
  rcases fin3_cases3 m' m with rfl | rfl | rfl
  · rfl
  · rw [show m + 1 + 1 = m + 2 by fin_cases m <;> rfl, a2] at b1
    exact absurd b1 (lt_irrefl 0)
  · rw [show m + 2 + 2 = m + 1 by fin_cases m <;> rfl] at b2
    linarith

section Dissection

variable {N : ℕ} (D : Dissection N)

/-- A point where the tiles' local angles add up to more than `π` is interior to the target. -/
theorem mem_interior_of_sum_gt {p : Plane} (hp : Real.pi < ∑ i, (D.tile i).localAngle p) :
    p ∈ interior D.target.carrier := by
  by_contra h
  rw [D.sum_localAngle_eq] at hp
  linarith [Tri.localAngle_le_pi D.target h]

theorem sum_ge_two {i j : Fin N} (hij : i ≠ j) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p ≤ ∑ k, (D.tile k).localAngle p := by
  calc _ = ∑ k ∈ {i, j}, (D.tile k).localAngle p := (Finset.sum_pair hij).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ => (D.tile k).localAngle_nonneg p

theorem sum_ge_three {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ ∑ l, (D.tile l).localAngle p := by
  have h : ({i, j, k} : Finset (Fin N)).sum (fun l => (D.tile l).localAngle p)
      = (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p := by
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk, add_assoc]
  rw [← h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun l _ _ => (D.tile l).localAngle_nonneg p

/-- A point inside edges of two different tiles is interior to the target. -/
theorem interior_of_two_openSegment {i j : Fin N} (hij : i ≠ j) {m m' : Fin 3} {p : Plane}
    (hi : p ∈ openSegment ℝ ((D.tile i).pts m) ((D.tile i).pts (m + 1)))
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m') ((D.tile j).pts (m' + 1))) :
    p ∈ interior D.target.carrier := by
  apply mem_interior_of_sum_gt D
  have := sum_ge_two D hij p
  rw [Tri.localAngle_openSegment _ m hi, Tri.localAngle_openSegment _ m' hj] at this
  linarith [Real.pi_pos]

/-- A vertex of one tile inside an edge of another is interior to the target. -/
theorem interior_of_vertex_openSegment {i j : Fin N} {k m : Fin 3} {p : Plane}
    (hi : (D.tile i).pts k = p)
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1))) :
    p ∈ interior D.target.carrier := by
  have hij : i ≠ j := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m (hi ▸ hj)
  apply mem_interior_of_sum_gt D
  have := sum_ge_two D hij p
  rw [← hi, Tri.localAngle_vertex, hi, Tri.localAngle_openSegment _ m hj] at this
  have hc := Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
  rw [hi] at hc
  linarith

/-- At a vertex of the tiling, at most one tile has the point inside one of its edges. -/
theorem openSegment_tile_unique {i j j' : Fin N} {k m m' : Fin 3} {p : Plane}
    (hi : (D.tile i).pts k = p)
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    (hj' : p ∈ openSegment ℝ ((D.tile j').pts m') ((D.tile j').pts (m' + 1))) : j = j' := by
  by_contra hjj
  have hij : i ≠ j := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m (hi ▸ hj)
  have hij' : i ≠ j' := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m' (hi ▸ hj')
  have hsum := sum_ge_three D hij hij' hjj p
  rw [← hi, Tri.localAngle_vertex, hi, Tri.localAngle_openSegment _ m hj,
    Tri.localAngle_openSegment _ m' hj', D.sum_localAngle_eq] at hsum
  have hc := Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
  rw [hi] at hc
  linarith [Tri.localAngle_le_two_pi D.target p]

end Dissection

end TriangleTiling
