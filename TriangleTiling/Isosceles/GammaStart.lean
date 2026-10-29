/-
Where `Γ_c` starts (the boundary step of `lemma:crelation4`).

Let the side `AB` carry both a `c` edge and an edge of another type. Then somewhere on `AB` a `c`
edge and a non-`c` edge meet, at a point `Q₀` strictly inside `AB`. There the `c` edges are even
in number while exactly one of them, the `c` edge on `AB`, is alone on its ray. So a ray from `Q₀`
into the triangle carries a `c` edge and another edge, and extending it gives a link of `Γ_c`
starting on the boundary, unless there is a relation.
-/
import TriangleTiling.Isosceles.GammaVertices
import TriangleTiling.Isosceles.QandR

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N)

/-- The line of the side `AB`, with the triangle on the side `g ≥ c`. -/
theorem side_level :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g (D.target.pts 0) = c ∧ g (D.target.pts 1) = c ∧
      c < g (D.target.pts 2) ∧ ∀ y ∈ D.target.carrier, c ≤ g y := by
  obtain ⟨g, c, hg, hline, h2⟩ := edge_level_oriented D.target 0
  have h0 : g (D.target.pts 0) = c := hline _ (left_mem_segment _ _ _)
  have h1 : g (D.target.pts 1) = c := hline _ (right_mem_segment _ _ _)
  refine ⟨g, c, hg, h0, h1, h2, fun y hy => ?_⟩
  have := D.target.carrier_subset_halfplane (-g) (-c) (fun i => by
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases fin3_cases3 i 0 with rfl | rfl | rfl
    · exact h0.ge
    · exact h1.ge
    · exact h2.le) y hy
  simpa using this

/-- An edge on the line of `AB` is in the chain of the triangle's side. -/
theorem side_chain {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hside : ∀ y ∈ D.target.carrier, c ≤ g y)
    {e : Fin N × Fin 3} (h1 : g ((D.tile e.1).pts e.2) = c)
    (h2 : g ((D.tile e.1).pts (e.2 + 1)) = c) : e ∈ D.lineChain (-g) (-c) := by
  refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [h2], fun i => ?_⟩
  have hmem : (D.tile e.1).pts i ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨e.1, subset_convexHull ℝ _ ⟨i, rfl⟩⟩
  simpa using hside _ hmem

set_option maxHeartbeats 4000000 in
open Classical in
/-- **A link starts on the boundary.** Let the edges on `AB` include a marked edge and an unmarked
one, and suppose that at each vertex strictly inside `AB` no tile has the vertex inside an edge and
the marked edges are even in number. Then a link starts at a point of the boundary, unless there is
a relation. -/
theorem side_start (isθ : Fin N × Fin 3 → Prop) (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    {ec en : Fin N × Fin 3} (hec : ec ∈ part) (hen : en ∈ part)
    (hθc : isθ ec) (hθn : ¬ isθ en)
    (hgood : ∀ Q ∈ openSegment ℝ (D.target.pts 0) (D.target.pts 1),
      (∃ i k, (D.tile i).pts k = Q) →
        (∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
          ∧ Even ((edgesAt D Q).filter isθ).card)
    (hnorel : ¬ HasRelation D isθ) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D isθ Q₀ R := by
  obtain ⟨g, c, hg, hT0, hT1, hT2, hside⟩ := side_level D
  set T0 := D.target.pts 0
  set T1 := D.target.pts 1
  have hT01 : T0 ≠ T1 := tri_pts_succ_ne D.target 0
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnT0 : (-g) T0 = -c := by simp [hT0]
  have hnT1 : (-g) T1 = -c := by simp [hT1]
  have hL0 : AffineMap.lineMap T0 T1 (0 : ℝ) = T0 := AffineMap.lineMap_apply_zero T0 T1
  have hsegI : segment ℝ T0 T1 = AffineMap.lineMap T0 T1 '' Icc (0 : ℝ) 1 := by
    rw [← segment_eq_Icc zero_le_one, image_segment, hL0, AffineMap.lineMap_apply_one]
  -- The edges of `AB` are in the side chain, with parameters in `[0, 1]`.
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ T0 T1 := fun e he => by
    rw [← hcov]; exact Set.subset_biUnion_of_mem (u := fun e => (D.tile e.1).edge e.2) he
  have hline : ∀ y ∈ segment ℝ T0 T1, g y = c := by
    intro y hy
    rw [hsegI] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact level_lineMap hT0 hT1 t
  have hchain : ∀ e ∈ part, e ∈ D.lineChain (-g) (-c) := fun e he =>
    side_chain D hside (hline _ (hsub e he (left_mem_segment _ _ _)))
      (hline _ (hsub e he (right_mem_segment _ _ _)))
  have mem : ∀ e ∈ D.lineChain (-g) (-c), ∀ t,
      AffineMap.lineMap T0 T1 t ∈ (D.tile e.1).edge e.2 ↔
        t ∈ Icc (edgeLo T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hng hT01 hnT0 hnT1 he t
  have hlt : ∀ e ∈ D.lineChain (-g) (-c),
      edgeLo T0 T1 (D.tile e.1) e.2 < edgeHi T0 T1 (D.tile e.1) e.2 :=
    fun e he => chain_lo_lt_hi D hng hT01 hnT0 hnT1 he
  have ov : ∀ e ∈ D.lineChain (-g) (-c), ∀ e' ∈ D.lineChain (-g) (-c),
      max (edgeLo T0 T1 (D.tile e.1) e.2) (edgeLo T0 T1 (D.tile e'.1) e'.2)
        < min (edgeHi T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hng hT01 hnT0 hnT1 he he' h
  have hI : ∀ e ∈ part, 0 ≤ edgeLo T0 T1 (D.tile e.1) e.2 ∧ edgeHi T0 T1 (D.tile e.1) e.2 ≤ 1 := by
    intro e he
    have key : ∀ t, t ∈ Icc (edgeLo T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e.1) e.2) →
        t ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      have := hsub e he ((mem e (hchain e he) t).mpr ht)
      rw [hsegI] at this
      obtain ⟨s, hs, hst⟩ := this
      rwa [← AffineMap.lineMap_injective ℝ hT01 hst]
    have h := hlt e (hchain e he)
    exact ⟨(key _ ⟨le_rfl, h.le⟩).1, (key _ ⟨h.le, le_rfl⟩).2⟩
  -- A `c` edge and a non-`c` edge of `AB` meet, by connectedness.
  set U := ⋃ e ∈ part.filter (isθ), (D.tile e.1).edge e.2
  set V := ⋃ e ∈ part.filter (fun e => ¬ isθ e), (D.tile e.1).edge e.2
  have hclosed : ∀ e : Fin N × Fin 3, IsClosed ((D.tile e.1).edge e.2) := fun e => by
    rw [Tri.edge, segment_eq_image_lineMap]
    exact (isCompact_Icc.image (AffineMap.lineMap_continuous)).isClosed
  have hU : IsClosed U := isClosed_biUnion_finset fun e _ => hclosed e
  have hV : IsClosed V := isClosed_biUnion_finset fun e _ => hclosed e
  have hUV : segment ℝ T0 T1 ⊆ U ∪ V := by
    rw [← hcov]
    intro y hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    by_cases hθ : isθ e
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hθ⟩, hye⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hθ⟩, hye⟩)
  have hpt : ∀ e ∈ part, (D.tile e.1).pts e.2 ∈ segment ℝ T0 T1 ∩ (D.tile e.1).edge e.2 :=
    fun e he => ⟨hsub e he (left_mem_segment _ _ _), left_mem_segment _ _ _⟩
  obtain ⟨Q₀, hQ₀s, hQ₀U, hQ₀V⟩ := isPreconnected_closed_iff.mp
    (convex_segment T0 T1).isPreconnected U V hU hV hUV
    ⟨_, (hpt ec hec).1, Set.mem_iUnion₂.mpr ⟨ec, Finset.mem_filter.mpr ⟨hec, hθc⟩, (hpt ec hec).2⟩⟩
    ⟨_, (hpt en hen).1, Set.mem_iUnion₂.mpr ⟨en, Finset.mem_filter.mpr ⟨hen, hθn⟩, (hpt en hen).2⟩⟩
  obtain ⟨x, hx, hQx⟩ := Set.mem_iUnion₂.mp hQ₀U
  obtain ⟨y, hy, hQy⟩ := Set.mem_iUnion₂.mp hQ₀V
  obtain ⟨hxp, hθx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyp, hθy⟩ := Finset.mem_filter.mp hy
  have hxc := hchain x hxp
  have hyc := hchain y hyp
  have hxy : x ≠ y := fun h => hθy (h ▸ hθx)
  rw [hsegI] at hQ₀s
  obtain ⟨q, -, rfl⟩ := hQ₀s
  have hqx := (mem x hxc q).mp hQx
  have hqy := (mem y hyc q).mp hQy
  -- The two edges are on opposite sides of `q`.
  have hno := fun h => hxy (ov x hxc y hyc h)
  have hlx := hlt x hxc
  have hly := hlt y hyc
  have hsplit : (edgeHi T0 T1 (D.tile x.1) x.2 = q ∧ edgeLo T0 T1 (D.tile y.1) y.2 = q) ∨
      (edgeLo T0 T1 (D.tile x.1) x.2 = q ∧ edgeHi T0 T1 (D.tile y.1) y.2 = q) := by
    by_contra hc
    apply hno
    rcases le_total (edgeLo T0 T1 (D.tile x.1) x.2) (edgeLo T0 T1 (D.tile y.1) y.2) with h1 | h1 <;>
    rcases le_total (edgeHi T0 T1 (D.tile x.1) x.2) (edgeHi T0 T1 (D.tile y.1) y.2) with h2 | h2
    · rw [max_eq_right h1, min_eq_left h2]
      by_contra h; push Not at h
      exact hc (Or.inl ⟨by linarith [hqx.2, hqy.1], by linarith [hqx.2, hqy.1]⟩)
    · rw [max_eq_right h1, min_eq_right h2]; linarith
    · rw [max_eq_left h1, min_eq_left h2]; linarith
    · rw [max_eq_left h1, min_eq_right h2]
      by_contra h; push Not at h
      exact hc (Or.inr ⟨by linarith [hqx.1, hqy.2], by linarith [hqx.1, hqy.2]⟩)
  -- `q` is strictly inside `(0, 1)`.
  obtain ⟨hx0, hx1⟩ := hI x hxp
  obtain ⟨hy0, hy1⟩ := hI y hyp
  have hq0 : 0 < q := by rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hq1 : q < 1 := by rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  set Q₀ := AffineMap.lineMap T0 T1 q
  have hQ₀open : Q₀ ∈ openSegment ℝ T0 T1 := by
    rw [openSegment_eq_image_lineMap]; exact ⟨q, ⟨hq0, hq1⟩, rfl⟩
  have hgQ₀ : g Q₀ = c := level_lineMap hT0 hT1 q
  have hQ₀fr : Q₀ ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target 0 (openSegment_subset_segment _ _ _ hQ₀open)
  have hQ₀nc : Q₀ ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m 0 (hm ▸ hQ₀open)
  refine ⟨Q₀, hQ₀fr, ?_⟩
  -- Both edges end at `Q₀`.
  have hxe : x ∈ edgesAt D Q₀ := by
    rcases hsplit with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).1
    · exact (edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).1
  have hye : y ∈ edgesAt D Q₀ := by
    rcases hsplit with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact (edgesAt_of_lo D hng hT01 hnT0 hnT1 hyc h2).1
    · exact (edgesAt_of_hi D hng hT01 hnT0 hnT1 hyc h2).1
  -- Every edge at `Q₀` on the line of `AB` is `x` or `y`.
  have honline : ∀ e ∈ edgesAt D Q₀, g (farEnd D Q₀ e) = c →
      e = x ∨ e = y := by
    intro e he hgF
    obtain ⟨n1, n2⟩ := level_far D he hgQ₀ hgF
    have hec' := side_chain D hside n1 n2
    have hle := hlt e hec'
    rcases end_param_at D hT01 he with hl | hh
    · have he1 : q < edgeHi T0 T1 (D.tile e.1) e.2 := by rw [← hl]; exact hle
      rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; apply ov e hec' y hyc; rw [hl, h2, max_self]
        exact lt_min he1 (by rw [← h2]; exact hly)
      · left; apply ov e hec' x hxc; rw [hl, h1, max_self]
        exact lt_min he1 (by rw [← h1]; exact hlx)
    · have he1 : edgeLo T0 T1 (D.tile e.1) e.2 < q := by rw [← hh]; exact hle
      rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; apply ov e hec' x hxc; rw [hh, h1, min_self]
        exact max_lt he1 (by rw [← h1]; exact hlx)
      · right; apply ov e hec' y hyc; rw [hh, h2, min_self]
        exact max_lt he1 (by rw [← h2]; exact hly)
  -- Edges at `Q₀` leaving `AB` point into the triangle.
  have hcoord : ∀ z, g z - c = D.target.basis.coord (0 + 2) z * (g (D.target.pts (0 + 2)) - c) :=
    level_eq_coord D.target g c (0 + 2) (by rw [show (0 : Fin 3) + 2 + 1 = 0 from rfl]; exact hT0)
      (by rw [show (0 : Fin 3) + 2 + 2 = 0 + 1 from rfl]; exact hT1)
  have hinto : ∀ e ∈ edgesAt D Q₀, c < g (farEnd D Q₀ e) →
      ∃ τ ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap Q₀ (farEnd D Q₀ e) τ ∈
        interior D.target.carrier := by
    intro e he hF
    have hpos : 0 < D.target.basis.coord (0 + 2) (farEnd D Q₀ e) := by
      have := hcoord (farEnd D Q₀ e)
      have h2 : 0 < g (D.target.pts (0 + 2)) - c := by
        rw [show (0 : Fin 3) + 2 = 2 from rfl]; linarith
      by_contra hc; push Not at hc; nlinarith
    obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior D.target 0 hQ₀open hpos
    refine ⟨min τ0 1 / 2, ⟨by have := lt_min hτ0 one_pos; linarith,
      by have := min_le_right τ0 1; linarith⟩, hint _ (by have := lt_min hτ0 one_pos; linarith)
      (by have := min_le_left τ0 1; linarith)⟩
  -- No tile has `Q₀` inside an edge, and its marked edges are even in number.
  obtain ⟨hnrel, heven⟩ := hgood Q₀ hQ₀open (by
    rcases (mem_edgesAt _).mp hxe with h | h
    · exact ⟨_, _, h⟩
    · exact ⟨_, _, h⟩)
  -- An edge alone on its ray lies on `AB`.
  have hlone_line : ∀ e ∈ edgesAt D Q₀,
      (∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ e e') →
        g (farEnd D Q₀ e) = c := by
    intro e he hl
    have hFt : farEnd D Q₀ e ∈ D.target.carrier := by
      rw [← D.covers]
      refine Set.mem_iUnion.mpr ⟨e.1, (D.tile e.1).edge_subset_carrier e.2 ?_⟩
      rw [edgesAt_edge _ he]; exact right_mem_segment _ _ _
    rcases (hside _ hFt).lt_or_eq with hlt' | heq
    · exfalso
      obtain ⟨τ, hτ, hint⟩ := hinto e he hlt'
      obtain ⟨g₀, c₀, hg₀, hQ₀', hF₀⟩ := ray_level (farEnd_ne _ he)
      obtain ⟨g', c', hg', hQ', hF', hec'⟩ : ∃ (g' : Plane →ₗ[ℝ] ℝ) (c' : ℝ), g' ≠ 0 ∧
          g' Q₀ = c' ∧ g' (farEnd D Q₀ e) = c' ∧ e ∈ D.lineChain g' c' := by
        rcases edgesAt_chain _ he hQ₀' hF₀ with h' | h'
        · exact ⟨g₀, c₀, hg₀, hQ₀', hF₀, h'⟩
        · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀'], by simp [hF₀], h'⟩
      obtain ⟨e₂, -, hQe₂⟩ := lonely_openSegment _ he hg' hQ' hF' hec'
        (fun e' he' hne hray => hl e' he' ⟨hne.symm, hray⟩) hτ hint
      exact hnrel _ _ hQe₂
    · exact heq.symm
  -- `x` and `y` leave `Q₀` in opposite directions.
  have hgx : g (farEnd D Q₀ x) = c := by
    rcases hsplit with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [(edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).2]
      exact level_lineMap hT0 hT1 _
    · rw [(edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).2]
      exact level_lineMap hT0 hT1 _
  have hnxy : ¬ SameRayAt D Q₀ x y := by
    rintro ⟨t, ht, hFt⟩
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have fx := (edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).2
      have fy := (edgesAt_of_lo D hng hT01 hnT0 hnT1 hyc h2).2
      rw [fx, fy, lineMap_params] at hFt
      have := AffineMap.lineMap_injective ℝ hT01 hFt
      nlinarith
    · have fx := (edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).2
      have fy := (edgesAt_of_hi D hng hT01 hnT0 hnT1 hyc h2).2
      rw [fx, fy, lineMap_params] at hFt
      have := AffineMap.lineMap_injective ℝ hT01 hFt
      nlinarith
  -- `x` and `y` are alone on their rays.
  have hlone_xy : ∀ u ∈ ({x, y} : Finset (Fin N × Fin 3)),
      ∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ u e' := by
    intro u hu e' he' ⟨hne, hray⟩
    have hgu : g (farEnd D Q₀ u) = c := by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hgx
      · rw [Finset.mem_singleton.mp hu]
        obtain ⟨n1, n2⟩ := lineChain_ends D hyc
        rcases (mem_edgesAt _).mp hye with h | h
        · rw [farEnd, if_pos h]; simpa using n2
        · have hne' : (D.tile y.1).pts y.2 ≠ Q₀ := fun h0 =>
            tri_pts_succ_ne (D.tile y.1) y.2 (h0.trans h.symm)
          rw [farEnd, if_neg hne']; simpa using n1
    obtain ⟨t, ht, hFt⟩ := hray
    have hge : g (farEnd D Q₀ e') = c := by
      rw [hFt]; exact level_lineMap hgQ₀ hgu t
    have hray' : SameRayAt D Q₀ u e' := ⟨t, ht, hFt⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases honline e' he' hge with h | h
      · exact hne h.symm
      · exact hnxy (h ▸ hray')
    · rw [Finset.mem_singleton.mp hu] at hne hray'
      rcases honline e' he' hge with h | h
      · exact hnxy (sameRayAt_symm _ (h ▸ hray'))
      · exact hne h.symm
  have hxlone : ∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ x e' :=
    hlone_xy x (by simp)
  have huniq : ∀ e ∈ edgesAt D Q₀, isθ e →
      (∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ e e') → e = x := by
    intro e he hθ hl
    rcases honline e he (hlone_line e he hl) with h | h
    · exact h
    · exact absurd (h ▸ hθ) hθy
  -- A mixed ray, and nothing behind `Q₀`.
  obtain ⟨x', hx', y', hy', hxy', hθx', hθy'⟩ := mixed_of_parity D
    (isθ) hxe hθx hxlone huniq heven
  have hgx' : c < g (farEnd D Q₀ x') := by
    have hFt : farEnd D Q₀ x' ∈ D.target.carrier := by
      rw [← D.covers]
      refine Set.mem_iUnion.mpr ⟨x'.1, (D.tile x'.1).edge_subset_carrier x'.2 ?_⟩
      rw [edgesAt_edge _ hx']; exact right_mem_segment _ _ _
    rcases (hside _ hFt).lt_or_eq with h | h
    · exact h
    · exfalso
      rcases honline x' hx' h.symm with rfl | rfl
      · exact hlone_xy _ (by simp) y' hy' hxy'
      · exact hlone_xy _ (by simp) y' hy' hxy'
  have hback : ∀ e : Fin N × Fin 3, Q₀ ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, Q₀ ∉ openSegment ℝ z (farEnd D Q₀ x') := by
    intro e _ z hz hQz
    have hzt : z ∈ D.target.carrier := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨e.1, (D.tile e.1).edge_subset_carrier e.2 hz⟩
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hQz
    have h1 := hgQ₀
    rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    have h3 := mul_le_mul_of_nonneg_left (hside z hzt) ha.le
    have h4 := mul_lt_mul_of_pos_left hgx' hb
    have h5 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  rcases extend_link D (isθ) hx' hy' hxy'.1.symm hxy'.2 hθx' hθy'
    hback with h | h
  · exact h
  · exact absurd h hnorel


section Specific

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr

open Classical in
/-- **`Γ_c` starts on the boundary.** If the edges on `AB` include a `c` edge and a non-`c` edge,
a link of `Γ_c` starts at a point of the boundary, unless there is a relation. -/
theorem boundary_start (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    {ec en : Fin N × Fin 3} (hec : ec ∈ part) (hen : en ∈ part)
    (hθc : edgeType D (tileγ D) ec) (hθn : ¬ edgeType D (tileγ D) en)
    (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D.toDissection (edgeType D (tileγ D)) Q₀ R := by
  refine side_start D.toDissection (edgeType D (tileγ D)) part hcov hec hen hθc hθn ?_ hnorel
  intro Q hQ ⟨i, k, hik⟩
  have hQfr : Q ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target 0 (openSegment_subset_segment _ _ _ hQ)
  have hQnc : Q ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m 0 (hm ▸ hQ)
  have hloc : D.target.localAngle Q = (0 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [D.target.localAngle_frontier hQfr hQnc]; push_cast; ring
  have hrel := vertex_relations D hγ hirr Q 0 1 hloc
  have hpos := vertex_counts_pos D hik
  refine ⟨fun j m hQ' => ?_, c_count_even D hγ hirr hloc⟩
  have := angleCount_pos D (Tri.localAngle_openSegment _ m hQ')
  omega

end Specific

end TriangleTiling
