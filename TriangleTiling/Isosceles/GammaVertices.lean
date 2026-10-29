/-
The vertices met by the graphs `Γ_c` and `Γ_a` (`lemma:crelation4`, `lemma:essentialsegments`).

Let the isosceles triangle `ABC` with base angles `α` (`α ∉ ℚπ`) be tiled by the tile
`(α, β, 2α)`. Then:

* at every vertex inside the target or inside a side, the `c` edges are even in number;
* at the end of a link the `a` edges are even in number, unless the end is a star;
* at a center there is a ray carrying an `a` edge and another edge, and nothing runs from the
  center backwards along it.
-/
import TriangleTiling.Isosceles.MarkedCount
import TriangleTiling.Tiling.Degree
import TriangleTiling.Tiling.Straight

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : CongruentDissection N)

theorem localAngle_interior' {P : Plane} (hP : P ∈ interior D.target.carrier) :
    D.target.localAngle P = (0 : ℤ) * tileα D + (2 : ℤ) * Real.pi := by
  rw [Tri.localAngle_interior _ hP]; push_cast; ring

/-- A vertex of a tile has one of `α, β, γ` there. -/
theorem vertex_counts_pos {P : Plane} {i : Fin N} {k : Fin 3} (hk : (D.tile i).pts k = P) :
    1 ≤ angleCount D P (tileα D) + angleCount D P (tileβ D) + angleCount D P (tileγ D) := by
  rcases localAngle_at_own_vertex_mem' D i k with h | h | h <;> rw [hk] at h
  · have := angleCount_pos D h; omega
  · have := angleCount_pos D h; omega
  · have := angleCount_pos D h; omega

/-- The vertices of the tiling, as points. -/
theorem mem_tilingVertices {P : Plane} : P ∈ tilingVertices D ↔ ∃ i k, (D.tile i).pts k = P := by
  classical
  simp [tilingVertices]

variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr


open Classical in
/-- **`c` edges come in pairs** at a point where the target's angle is a multiple of `π`. -/
theorem c_count_even {P : Plane} {t : ℤ}
    (hP : D.target.localAngle P = (0 : ℤ) * tileα D + t * Real.pi) :
    Even ((edgesAt D.toDissection P).filter (edgeType D (tileγ D))).card := by
  have hcm := card_marked D (anglesSep_of_two_alpha D hγ hirr) P (φ := tileγ D) (Or.inr (Or.inr rfl))
  obtain ⟨h1, -⟩ := vertex_relations D hγ hirr P 0 t hP
  refine ⟨2 * angleCount D P (tileβ D) - angleCount D P (tileγ D), ?_⟩
  omega

open Classical in
/-- **At the end of a link** the `a` edges are even in number, unless the end is a star. -/
theorem link_end_a {isθ : Fin N × Fin 3 → Prop} {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (h : LinkData D.toDissection isθ Q R g c) :
    vertexType D R = (3, 1, 0) ∨
      Even ((edgesAt D.toDissection R).filter (edgeType D (tileα D))).card := by
  have hcm := card_marked D (anglesSep_of_two_alpha D hγ hirr) R (φ := tileα D) (Or.inl rfl)
  obtain ⟨h1, h2⟩ := vertex_relations D hγ hirr R 0 2 (localAngle_interior' D h.end_interior)
  obtain ⟨ε, -, hRε⟩ := h.across
  have hπ := angleCount_pos D (Tri.localAngle_openSegment _ ε.2 hRε)
  obtain ⟨i, k, hik⟩ := h.end_vertex
  have hpos := vertex_counts_pos D hik
  by_cases hγ0 : angleCount D R (tileγ D) = 0
  · left
    simp only [vertexType, Prod.mk.injEq]
    omega
  · right
    exact ⟨angleCount D R (tileβ D), by omega⟩

/-- **A center** is interior to the target and inside no tile edge. -/
theorem center_facts {Q : Plane} (hv : Q ∈ tilingVertices D)
    (hnc : Q ∉ Set.range D.target.pts) (ht : vertexType D Q = (0, 2, 3)) :
    Q ∈ interior D.target.carrier ∧ angleCount D Q Real.pi = 0 ∧
      angleCount D Q (2 * Real.pi) = 0 := by
  obtain ⟨i, k, hik⟩ := (mem_tilingVertices D).mp hv
  simp only [vertexType, Prod.mk.injEq] at ht
  obtain ⟨hα, hβ, hγ'⟩ := ht
  have hQt : Q ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, hik ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  by_cases hint : Q ∈ interior D.target.carrier
  · obtain ⟨-, h2⟩ := vertex_relations D hγ hirr Q 0 2 (localAngle_interior' D hint)
    exact ⟨hint, by omega, by omega⟩
  · exfalso
    have hfr : Q ∈ frontier D.target.carrier := by
      rw [frontier, D.target.isCompact.isClosed.closure_eq]; exact ⟨hQt, hint⟩
    have hloc : D.target.localAngle Q = (0 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
      rw [D.target.localAngle_frontier hfr hnc]; push_cast; ring
    obtain ⟨-, h2⟩ := vertex_relations D hγ hirr Q 0 1 hloc
    omega

/-- **No half at a center.** At a center, no set of tiles has angles adding up to `π`. -/
theorem center_no_half {Q : Plane} (hv : Q ∈ tilingVertices D)
    (hnc : Q ∉ Set.range D.target.pts) (ht : vertexType D Q = (0, 2, 3))
    (S : Finset (Fin N)) : ∑ i ∈ S, (D.tile i).localAngle Q ≠ Real.pi := by
  classical
  obtain ⟨-, hπ, h2π⟩ := center_facts D hγ hirr hv hnc ht
  simp only [vertexType, Prod.mk.injEq] at ht
  obtain ⟨hα0, -, -⟩ := ht
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  have hβγ : tileβ D ≠ tileγ D := by
    have ne : ∀ x y : Fin 5, x ≠ y →
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
          ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
    exact ne 1 2 (by decide)
  have hval : ∀ i, (D.tile i).localAngle Q = tileβ D ∨ (D.tile i).localAngle Q = tileγ D ∨
      (D.tile i).localAngle Q = 0 := by
    intro i
    rcases localAngle_mem D Q i with h | h | h | h | h | h
    · exfalso
      have := angleCount_pos D (show (D.tile i).localAngle Q = tileα D from h)
      omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exfalso; have := angleCount_pos D h; omega
    · exfalso; have := angleCount_pos D h; omega
    · exact Or.inr (Or.inr h)
  have hpt : ∀ i ∈ S, (D.tile i).localAngle Q =
      (if (D.tile i).localAngle Q = tileβ D then tileβ D else 0)
        + (if (D.tile i).localAngle Q = tileγ D then tileγ D else 0) := by
    intro i _
    rcases hval i with h | h | h
    · rw [if_pos h, if_neg (h ▸ hβγ), add_zero, h]
    · rw [if_neg (h ▸ hβγ.symm), if_pos h, zero_add, h]
    · rw [if_neg (by rw [h]; exact (hv0 1).symm), if_neg (by rw [h]; exact (hv0 2).symm), h,
        add_zero]
  intro hsum
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  set kβ := (S.filter fun i => (D.tile i).localAngle Q = tileβ D).card
  set kγ := (S.filter fun i => (D.tile i).localAngle Q = tileγ D).card
  rw [hβ, hγ] at hsum
  have key : (((2 * kγ - 3 * kβ : ℤ)) : ℝ) * tileα D + (((kβ - 1 : ℤ)) : ℝ) * Real.pi = 0 := by
    push_cast; linarith
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega

/-- **Out of a center**: a link of `Γ_a` leaves every center, unless there is a relation. -/
theorem center_out {Q : Plane} (hv : Q ∈ tilingVertices D)
    (hnc : Q ∉ Set.range D.target.pts) (ht : vertexType D Q = (0, 2, 3))
    (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileα D))) :
    ∃ R, IsLink D.toDissection (edgeType D (tileα D)) Q R := by
  classical
  obtain ⟨hQint, hπ0, -⟩ := center_facts D hγ hirr hv hnc ht
  have hnrel : ∀ j : Fin N, ∀ m : Fin 3,
      Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) := by
    intro j m hQ
    have := angleCount_pos D (Tri.localAngle_openSegment _ m hQ)
    omega
  -- No edge is alone on its ray.
  have hnolone : ∀ e ∈ edgesAt D.toDissection Q, ∃ e' ∈ edgesAt D.toDissection Q,
      Partners D.toDissection Q e e' := by
    intro e he
    by_contra hno
    push Not at hno
    obtain ⟨-, -, -, -, -, -, e₂, -, hQe₂⟩ := lonely_relint D.toDissection hQint he
      (fun e' he' hne hray => hno e' he' ⟨hne.symm, hray⟩)
    exact hnrel _ _ hQe₂
  -- Five `a` edges: a mixed ray.
  have hcm := card_marked D (anglesSep_of_two_alpha D hγ hirr) Q (φ := tileα D) (Or.inl rfl)
  simp only [vertexType, Prod.mk.injEq] at ht
  obtain ⟨hα0, hβ2, hγ3⟩ := ht
  obtain ⟨x, hx, y, hy, hxy, hθx, hθy⟩ : ∃ x ∈ edgesAt D.toDissection Q,
      ∃ y ∈ edgesAt D.toDissection Q, Partners D.toDissection Q x y ∧
        edgeType D (tileα D) x ∧ ¬ edgeType D (tileα D) y := by
    by_contra hno
    push Not at hno
    have hpar := card_filter_mod_two (edgesAt D.toDissection Q) (Partners D.toDissection Q)
      (edgeType D (tileα D)) (fun x _ y _ h => ⟨h.1.symm, sameRayAt_symm _ h.2⟩)
      (fun x h => h.1 rfl)
      (fun x hx y hy z hz hxy hxz => by
        by_contra hyz
        exact sameRayAt_unique _ hx hy hz hxy.1.symm hxz.1.symm hyz hxy.2 hxz.2)
      (fun x hx y hy hxy hθ => hno x hx y hy hxy hθ) ∅ (fun x => by
        simp only [Finset.notMem_empty, false_iff, not_and, not_forall, not_not]
        intro hx _
        obtain ⟨e', he', h'⟩ := hnolone x hx
        exact ⟨e', he', h'⟩)
    rw [Finset.card_empty] at hpar
    omega
  -- Nothing runs backwards from the center along that ray.
  have hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ z (farEnd D.toDissection Q x) := by
    intro e hQe z hz hQz
    set F := farEnd D.toDissection Q x
    have hQF : Q ≠ F := (farEnd_ne _ hx).symm
    -- `Q` is an end of `e`.
    have he : e ∈ edgesAt D.toDissection Q := by
      rw [Tri.edge, ← insert_endpoints_openSegment] at hQe
      rcases hQe with h | h | h
      · exact (mem_edgesAt _).mpr (Or.inl h.symm)
      · exact (mem_edgesAt _).mpr (Or.inr h.symm)
      · exact absurd h (hnrel e.1 e.2)
    obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne _ hx)
    -- `z` is on the line, behind `Q`.
    have hgz : g z = c := by
      obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hQz
      have h1 := hgQ
      rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hgF] at h1
      have : a * (g z - c) = 0 := by linear_combination h1 - c * hab
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    obtain ⟨tz, htz⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgz
    have htz0 : tz < 0 := by
      have h0 : AffineMap.lineMap Q F (0 : ℝ) ∈
          openSegment ℝ (AffineMap.lineMap Q F tz) (AffineMap.lineMap Q F (1 : ℝ)) := by
        rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, ← htz]; exact hQz
      rw [← image_openSegment, (AffineMap.lineMap_injective ℝ hQF).mem_set_image] at h0
      rcases lt_trichotomy tz 1 with h | h | h
      · rw [openSegment_eq_Ioo h] at h0; exact h0.1
      · rw [h, openSegment_same] at h0; norm_num at h0
      · rw [openSegment_symm, openSegment_eq_Ioo h] at h0; linarith [h0.1]
    -- The far end of `e` is on the line, behind `Q`.
    have hzQ : z ≠ Q := by
      intro h
      have : AffineMap.lineMap Q F tz = AffineMap.lineMap Q F (0 : ℝ) := by
        rw [← htz, h, AffineMap.lineMap_apply_zero]
      exact htz0.ne (AffineMap.lineMap_injective ℝ hQF this)
    rw [edgesAt_edge _ he, segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    have hs0 : 0 < s := by
      rcases hs.1.lt_or_eq with h | h
      · exact h
      · rw [← h, AffineMap.lineMap_apply_zero] at hzs; exact absurd hzs.symm hzQ
    have hgfe : g (farEnd D.toDissection Q e) = c := by
      have := congrArg g hzs
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, hgQ, hgz]
        at this
      have h' : s * (g (farEnd D.toDissection Q e) - c) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · linarith
      · linarith
    obtain ⟨te, hte⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgfe
    have hte0 : te < 0 := by
      rw [hte, lineMap_lineMap_eq, htz] at hzs
      have := AffineMap.lineMap_injective ℝ hQF hzs
      nlinarith
    obtain ⟨S, hS⟩ := straight_angle_sum D.toDissection hQint hx he hte0 hte
    exact center_no_half D hγ hirr hv hnc (by simp [vertexType, hα0, hβ2, hγ3]) S hS
  rcases extend_link D.toDissection (edgeType D (tileα D)) hx hy hxy.1.symm hxy.2 hθx hθy
    hback with h | h
  · exact h
  · exact absurd h hnorel

end TriangleTiling
