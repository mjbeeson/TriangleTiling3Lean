/-
Tile edges on a line, in parameters.

Fix a line through two points `Q ≠ W`, given as a level set `{g = c}` of a nonzero functional.
A point of the line is `lineMap Q W t` for a unique parameter `t`, and a tile edge lying on the
line is the image of a closed interval of parameters. Two edges of the same chain (tiles on the
same side of the line) whose intervals overlap are the same edge.
-/
import TriangleTiling.Tiling.OneSided
import TriangleTiling.Tiling.Chord

namespace TriangleTiling

open Erdos634.Geometry Set

open Classical in
/-- The parameter of `y` along the line `QW` (`0` off the line). -/
noncomputable def lineParam (Q W y : Plane) : ℝ :=
  if h : ∃ t : ℝ, y = AffineMap.lineMap Q W t then h.choose else 0

theorem lineMap_lineParam {Q W y : Plane} (h : ∃ t : ℝ, y = AffineMap.lineMap Q W t) :
    AffineMap.lineMap Q W (lineParam Q W y) = y := by
  classical
  rw [lineParam, dif_pos h]
  exact h.choose_spec.symm

theorem lineParam_lineMap {Q W : Plane} (hQW : Q ≠ W) (t : ℝ) :
    lineParam Q W (AffineMap.lineMap Q W t) = t :=
  AffineMap.lineMap_injective ℝ hQW (lineMap_lineParam ⟨t, rfl⟩)

/-- The lower parameter of edge `k` of `T` along `QW`. -/
noncomputable def edgeLo (Q W : Plane) (T : Tri) (k : Fin 3) : ℝ :=
  min (lineParam Q W (T.pts k)) (lineParam Q W (T.pts (k + 1)))

/-- The upper parameter of edge `k` of `T` along `QW`. -/
noncomputable def edgeHi (Q W : Plane) (T : Tri) (k : Fin 3) : ℝ :=
  max (lineParam Q W (T.pts k)) (lineParam Q W (T.pts (k + 1)))

section Line

variable {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q W : Plane}

/-- A point of the level line is on the line `QW`. -/
theorem eq_lineMap_lineParam (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {y : Plane} (hy : g y = c) : AffineMap.lineMap Q W (lineParam Q W y) = y :=
  lineMap_lineParam (eq_lineMap_of_level hg hQW hQ hW hy)

/-- The level of a point of the line `QW`. -/
theorem level_lineMap (hQ : g Q = c) (hW : g W = c) (t : ℝ) :
    g (AffineMap.lineMap Q W t) = c := by
  rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, hQ, hW, smul_eq_mul,
    smul_eq_mul]
  ring

/-- An edge with both ends on the line is the image of its parameter interval. -/
theorem edge_eq_image (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) (T : Tri)
    (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) :
    T.edge k = AffineMap.lineMap Q W '' Icc (edgeLo Q W T k) (edgeHi Q W T k) := by
  rw [edgeLo, edgeHi, ← segment_eq_Icc', image_segment, eq_lineMap_lineParam hg hQW hQ hW h1,
    eq_lineMap_lineParam hg hQW hQ hW h2]
  rfl

theorem lineMap_mem_edge_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    (T : Tri) (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ T.edge k ↔ t ∈ Icc (edgeLo Q W T k) (edgeHi Q W T k) := by
  rw [edge_eq_image hg hQW hQ hW T k h1 h2]
  exact (AffineMap.lineMap_injective ℝ hQW).mem_set_image

/-- The parameter interval of an edge is nondegenerate. -/
theorem edgeLo_lt_edgeHi (T : Tri) (k : Fin 3)
    (h1 : ∃ t : ℝ, T.pts k = AffineMap.lineMap Q W t)
    (h2 : ∃ t : ℝ, T.pts (k + 1) = AffineMap.lineMap Q W t) :
    edgeLo Q W T k < edgeHi Q W T k := by
  rw [edgeLo, edgeHi]
  have hne : lineParam Q W (T.pts k) ≠ lineParam Q W (T.pts (k + 1)) := by
    intro h
    have hk : T.pts k = T.pts (k + 1) := by
      rw [← lineMap_lineParam h1, ← lineMap_lineParam h2, h]
    have := T.indep.injective hk
    have hne : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact hne k this
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact h

theorem lineMap_mem_openSegment_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    (T : Tri) (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ openSegment ℝ (T.pts k) (T.pts (k + 1)) ↔
      t ∈ Ioo (edgeLo Q W T k) (edgeHi Q W T k) := by
  have hlt := edgeLo_lt_edgeHi T k (eq_lineMap_of_level hg hQW hQ hW h1)
    (eq_lineMap_of_level hg hQW hQ hW h2)
  have hab : lineParam Q W (T.pts k) ≠ lineParam Q W (T.pts (k + 1)) := by
    intro h
    rw [edgeLo, edgeHi, h, min_self, max_self] at hlt
    exact lt_irrefl _ hlt
  have e1 := (eq_lineMap_lineParam hg hQW hQ hW h1).symm
  have e2 := (eq_lineMap_lineParam hg hQW hQ hW h2).symm
  rw [e1, e2, ← image_openSegment, openSegment_eq_Ioo' hab,
    (AffineMap.lineMap_injective ℝ hQW).mem_set_image]
  rfl

end Line

section Chain

variable {N : ℕ} (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q W : Plane}

/-- The ends of a chain edge are on the line. -/
theorem lineChain_ends {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c :=
  ⟨(Dissection.mem_lineChain.mp he).1, (Dissection.mem_lineChain.mp he).2.1⟩

/-- A chain tile lies on its side of the line. -/
theorem lineChain_le {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
  (D.tile e.1).carrier_subset_halfplane g c (Dissection.mem_lineChain.mp he).2.2

theorem chain_mem_edge_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e.1) e.2) :=
  lineMap_mem_edge_iff hg hQW hQ hW _ _ (lineChain_ends D he).1 (lineChain_ends D he).2 t

theorem chain_lo_lt_hi (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    edgeLo Q W (D.tile e.1) e.2 < edgeHi Q W (D.tile e.1) e.2 :=
  edgeLo_lt_edgeHi _ _ (eq_lineMap_of_level hg hQW hQ hW (lineChain_ends D he).1)
    (eq_lineMap_of_level hg hQW hQ hW (lineChain_ends D he).2)

/-- Two edges of one chain sharing two points are the same edge. -/
theorem lineChain_eq_of_two (hg : g ≠ 0) {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (he' : e' ∈ D.lineChain g c) {y z : Plane} (hyz : y ≠ z)
    (hy : y ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2)
    (hz : z ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2) : e = e' := by
  by_contra hne
  exact hyz (D.sameside_edges_subsingleton g c hg hne (lineChain_le D he) (lineChain_le D he')
    (D.lineChain_edge_subset he) (D.lineChain_edge_subset he') hy hz)

/-- Two edges of one chain whose parameter intervals overlap are the same edge. -/
theorem lineChain_eq_of_overlap (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (he' : e' ∈ D.lineChain g c)
    (h : max (edgeLo Q W (D.tile e.1) e.2) (edgeLo Q W (D.tile e'.1) e'.2)
      < min (edgeHi Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e'.1) e'.2)) : e = e' := by
  set a := max (edgeLo Q W (D.tile e.1) e.2) (edgeLo Q W (D.tile e'.1) e'.2)
  set b := min (edgeHi Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e'.1) e'.2)
  have hmem : ∀ t, a ≤ t → t ≤ b → AffineMap.lineMap Q W t ∈
      (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 := by
    intro t h1 h2
    refine ⟨(chain_mem_edge_iff D hg hQW hQ hW he t).mpr ⟨?_, ?_⟩,
      (chain_mem_edge_iff D hg hQW hQ hW he' t).mpr ⟨?_, ?_⟩⟩
    · exact le_trans (le_max_left _ _) h1
    · exact le_trans h2 (min_le_left _ _)
    · exact le_trans (le_max_right _ _) h1
    · exact le_trans h2 (min_le_right _ _)
  refine lineChain_eq_of_two D hg he he' ?_ (hmem a le_rfl h.le) (hmem b h.le le_rfl)
  intro hab
  exact h.ne (AffineMap.lineMap_injective ℝ hQW hab)

/-- The points of the line that are vertices of the tiling have finitely many parameters. -/
theorem vertex_params_finite (hQW : Q ≠ W) :
    {t : ℝ | AffineMap.lineMap Q W t ∈ D.vertexSet}.Finite :=
  D.vertexSet_finite.preimage (AffineMap.lineMap_injective ℝ hQW).injOn

/-- **The wall cover, in parameters.** On a wall segment from `lineMap Q W a` to `lineMap Q W b`
inside the target, every parameter strictly between `a` and `b` that is not a vertex lies in the
interval of an edge of the chain. -/
theorem wall_cover_param (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {a b : ℝ}
    (hab : a < b)
    (hint : openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b)
      ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b),
      ∀ i, y ∉ interior (D.tile i).carrier)
    {t : ℝ} (ht : t ∈ Ioo a b) (hv : AffineMap.lineMap Q W t ∉ D.vertexSet) :
    ∃ e ∈ D.lineChain g c, t ∈ Icc (edgeLo Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e.1) e.2) := by
  have hne : AffineMap.lineMap Q W a ≠ (AffineMap.lineMap Q W b : Plane) :=
    fun h => hab.ne (AffineMap.lineMap_injective ℝ hQW h)
  have hS : segment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b) ⊆ {y | g y = c} := by
    rw [← image_segment]
    rintro _ ⟨s, -, rfl⟩
    exact level_lineMap hQ hW s
  have htmem : AffineMap.lineMap Q W t ∈
      openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b) := by
    rw [← image_openSegment, openSegment_eq_Ioo hab]
    exact ⟨t, ht, rfl⟩
  obtain ⟨e, he, hte⟩ := D.wall_cover g c hg hne hS hint hwall htmem hv
  exact ⟨e, he, (chain_mem_edge_iff D hg hQW hQ hW he t).mp hte⟩

end Chain

end TriangleTiling
