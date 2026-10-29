/-
Laczkovich's links (`definition:Gamma` of the paper).

Fix a class of tile edges, the *marked* edges (in the paper: the `a` edges, or the `c` edges).
A link from `Q` to `R` is a segment of a line, given as a level set `{g = c}`, such that on the
side `g ≤ c` (side 1):

* the segment is covered by edges, all of them marked and inside the segment;
* no marked edge on side 1 continues the segment backwards past `Q` (the paper's left-maximality);
* past `R` the line carries an unmarked edge on side 1 (the paper's condition (iii));

and on the other side (side 2) `R` lies strictly inside an edge (the paper's condition (iv)).

So the end `R` of a link is a vertex of the tiling inside the target lying strictly inside an edge
of a tile, and at most one link ends at any point.
-/
import TriangleTiling.Tiling.EdgesAt

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)

/-- A link from `Q` to `R` along the line `{g = c}`, with its marked side `g ≤ c`. -/
structure LinkData (Q R : Plane) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Prop where
  ne : Q ≠ R
  hg : g ≠ 0
  hQ : g Q = c
  hR : g R = c
  cov : ∀ y ∈ openSegment ℝ Q R, ∃ e ∈ D.lineChain g c, y ∈ (D.tile e.1).edge e.2
  inner : ∀ e ∈ D.lineChain g c, ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty →
    (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∧ isθ e
  start : ∀ e ∈ D.lineChain g c, isθ e → Q ∈ (D.tile e.1).edge e.2 →
    ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y R
  past : ∃ e ∈ D.lineChain g c, ¬ isθ e ∧ R ∈ (D.tile e.1).edge e.2 ∧
    ∃ y ∈ (D.tile e.1).edge e.2, R ∈ openSegment ℝ Q y
  across : ∃ e ∈ D.lineChain (-g) (-c),
    R ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

/-- A link from `Q` to `R`. -/
def IsLink (Q R : Plane) : Prop := ∃ g c, LinkData D isθ Q R g c

/-! ### Parameters along a segment -/

theorem openSegment_param {Q R y : Plane} :
    y ∈ openSegment ℝ Q R ↔ ∃ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap Q R t = y := by
  rw [openSegment_eq_image_lineMap]
  rfl

theorem segment_param {Q R y : Plane} :
    y ∈ segment ℝ Q R ↔ ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap Q R t = y := by
  rw [segment_eq_image_lineMap]
  rfl

theorem lineMap_mem_openSegment_params {Q R : Plane} (hQR : Q ≠ R) {a b t : ℝ} :
    AffineMap.lineMap Q R t ∈
        openSegment ℝ (AffineMap.lineMap Q R a) (AffineMap.lineMap Q R b) ↔
      t ∈ openSegment ℝ a b := by
  rw [← image_openSegment]
  exact (AffineMap.lineMap_injective ℝ hQR).mem_set_image

/-- A third vertex is off the line of an edge. -/
theorem third_off_line (T : Tri) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (k : Fin 3)
    (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) : g (T.pts (k + 2)) ≠ c := by
  intro h3
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hg (tri_pts_succ_ne T k) h1 h2 h3
  have hc := congrArg (T.basis.coord (k + 2)) ht
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at hc
  have n1 : ∀ k : Fin 3, ¬ (k + 2 = k) := by decide
  have n2 : ∀ k : Fin 3, ¬ (k + 2 = k + 1) := by decide
  simp [n1 k, n2 k] at hc

/-- **Two lines through one tile edge.** If a tile edge lies on both lines `{g₁ = c₁}` and
`{g₂ = c₂}`, with its tile on the side `gᵢ ≥ cᵢ` of both, the lines coincide and so do their
near sides. -/
theorem chain_transfer {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {ε : Fin N × Fin 3} (h₁ : ε ∈ D.lineChain (-g₁) (-c₁)) (h₂ : ε ∈ D.lineChain (-g₂) (-c₂)) :
    (∀ y, g₂ y = c₂ → g₁ y = c₁) ∧ (∀ e ∈ D.lineChain g₂ c₂, e ∈ D.lineChain g₁ c₁) := by
  obtain ⟨j, m⟩ := ε
  set S := D.tile j
  have i1 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  have i2 : ∀ m : Fin 3, m + 2 + 2 = m + 1 := by decide
  have lev : ∀ {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}, g ≠ 0 → (j, m) ∈ D.lineChain (-g) (-c) →
      g (S.pts (m + 2 + 1)) = c ∧ g (S.pts (m + 2 + 2)) = c ∧ 0 < g (S.pts (m + 2)) - c := by
    intro g c hg hε
    obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp hε
    simp only [LinearMap.neg_apply, neg_inj] at a1 a2
    have b3 := a3 (m + 2)
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at b3
    refine ⟨by rw [i1]; exact a1, by rw [i2]; exact a2, ?_⟩
    have := third_off_line S hg m a1 a2
    exact sub_pos.mpr (lt_of_le_of_ne b3 (Ne.symm this))
  obtain ⟨p1, p2, d1⟩ := lev hg₁ h₁
  obtain ⟨q1, q2, d2⟩ := lev hg₂ h₂
  have key1 := level_eq_coord S g₁ c₁ (m + 2) p1 p2
  have key2 := level_eq_coord S g₂ c₂ (m + 2) q1 q2
  have hon : ∀ y, g₂ y = c₂ → g₁ y = c₁ := by
    intro y hy
    have h2y := key2 y
    rw [hy, sub_self] at h2y
    have hc : S.basis.coord (m + 2) y = 0 := by
      rcases mul_eq_zero.mp h2y.symm with h | h
      · exact h
      · linarith
    have h1y := key1 y
    rw [hc, zero_mul] at h1y
    linarith
  refine ⟨hon, fun e he => ?_⟩
  obtain ⟨e1, e2, e3⟩ := Dissection.mem_lineChain.mp he
  refine Dissection.mem_lineChain.mpr ⟨hon _ e1, hon _ e2, fun i => ?_⟩
  have h2y := key2 ((D.tile e.1).pts i)
  have h1y := key1 ((D.tile e.1).pts i)
  have hle := e3 i
  have hc : S.basis.coord (m + 2) ((D.tile e.1).pts i) ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith

namespace LinkData

variable {D isθ} {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}

theorem mem_edge_iff (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (t : ℝ) : AffineMap.lineMap Q R t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) :=
  chain_mem_edge_iff D h.hg h.ne h.hQ h.hR he t

/-- The chain edges inside the segment have parameters in `[0, 1]`. -/
theorem params_of_inner (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) (hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ Q R) :
    0 ≤ edgeLo Q R (D.tile e.1) e.2 ∧ edgeHi Q R (D.tile e.1) e.2 ≤ 1 := by
  have hlt := chain_lo_lt_hi D h.hg h.ne h.hQ h.hR he
  have key : ∀ t ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2),
      t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := segment_param.mp (hsub ((h.mem_edge_iff he t).mpr ht))
    rwa [← AffineMap.lineMap_injective ℝ h.ne hst]
  exact ⟨(key _ ⟨le_rfl, hlt.le⟩).1, (key _ ⟨hlt.le, le_rfl⟩).2⟩

/-- **The arriving edge.** A marked side-1 edge inside the segment ends at `R`. -/
theorem arrive (h : LinkData D isθ Q R g c) :
    ∃ e ∈ D.lineChain g c, isθ e ∧ 0 ≤ edgeLo Q R (D.tile e.1) e.2 ∧
      edgeLo Q R (D.tile e.1) e.2 < 1 ∧ edgeHi Q R (D.tile e.1) e.2 = 1 := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_left (D.lineChain g c)
    (fun x => edgeLo Q R (D.tile x.1) x.2) (fun x => edgeHi Q R (D.tile x.1) x.2) 1
    one_pos Set.finite_empty (fun y hy _ => by
      rw [sub_self] at hy
      obtain ⟨e, he, hye⟩ := h.cov _ (openSegment_param.mpr ⟨y, hy, rfl⟩)
      exact ⟨e, he, (h.mem_edge_iff he y).mp hye⟩)
  set m := max (edgeLo Q R (D.tile e.1) e.2) 0
  have hm1 : m < 1 := max_lt hlo one_pos
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R ((m + 1) / 2), (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith
    · linarith [le_max_right (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith
  obtain ⟨hsub, hθ⟩ := h.inner e he hmeet
  obtain ⟨h0, h1⟩ := h.params_of_inner he hsub
  exact ⟨e, he, hθ, h0, hlo, le_antisymm h1 hhi⟩

/-- An end of an edge with parameter `t` is `lineMap Q R t`. -/
theorem end_of_param (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q R (edgeHi Q R (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases max_choice (lineParam Q R ((D.tile e.1).pts e.2))
    (lineParam Q R ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeHi, hm, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeHi, hm, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR n2]⟩

/-- The end of a link is a vertex of the tiling. -/
theorem end_vertex (h : LinkData D isθ Q R g c) : ∃ i k, (D.tile i).pts k = R := by
  obtain ⟨e, he, -, -, -, hhi⟩ := h.arrive
  obtain ⟨k, hk⟩ := h.end_of_param he
  exact ⟨e.1, k, by rw [hk, hhi, AffineMap.lineMap_apply_one]⟩

/-- The end of a link is interior to the target. -/
theorem end_interior (h : LinkData D isθ Q R g c) : R ∈ interior D.target.carrier := by
  obtain ⟨i, k, hk⟩ := h.end_vertex
  obtain ⟨e, -, he⟩ := h.across
  exact interior_of_vertex_openSegment D hk he

/-- **The leaving edge.** The unmarked side-1 edge past `R` starts at `R`. -/
theorem leave (h : LinkData D isθ Q R g c) :
    ∃ e ∈ D.lineChain g c, ¬ isθ e ∧ edgeLo Q R (D.tile e.1) e.2 = 1 ∧
      1 < edgeHi Q R (D.tile e.1) e.2 := by
  obtain ⟨e, he, hθ, hRe, y, hy, hRy⟩ := h.past
  have hR1 : (1 : ℝ) ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) := by
    rw [← h.mem_edge_iff he, AffineMap.lineMap_apply_one]; exact hRe
  -- `y` is past `R`.
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  obtain ⟨s, hs⟩ : ∃ s, AffineMap.lineMap Q R s = y := by
    have hgy : g y = c := D.lineChain_edge_subset he y hy
    exact ⟨_, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR hgy⟩
  have hs1 : 1 < s := by
    have hseg : openSegment ℝ Q y = AffineMap.lineMap Q R '' openSegment ℝ 0 s := by
      rw [image_openSegment, AffineMap.lineMap_apply_zero, hs]
    rw [hseg] at hRy
    obtain ⟨t, ht, hteq⟩ := hRy
    have ht1 : t = 1 :=
      AffineMap.lineMap_injective ℝ h.ne (hteq.trans (AffineMap.lineMap_apply_one Q R).symm)
    rw [ht1] at ht
    rcases lt_trichotomy 0 s with h0 | h0 | h0
    · rw [openSegment_eq_Ioo h0] at ht; exact ht.2
    · rw [← h0, openSegment_same] at ht; norm_num at ht
    · rw [openSegment_symm, openSegment_eq_Ioo h0] at ht; linarith [ht.1, ht.2]
  have hsI : s ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) := by
    rw [← h.mem_edge_iff he, hs]; exact hy
  refine ⟨e, he, hθ, ?_, lt_of_lt_of_le hs1 hsI.2⟩
  by_contra hne
  have hlo : edgeLo Q R (D.tile e.1) e.2 < 1 := lt_of_le_of_ne hR1.1 hne
  -- Otherwise the edge meets the open segment, where every edge is marked.
  set m := max (edgeLo Q R (D.tile e.1) e.2) 0
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R ((m + 1) / 2), (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q R (D.tile e.1) e.2) 0, max_lt hlo one_pos]
    · linarith [max_lt hlo one_pos, hR1.2]
    · linarith [le_max_right (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith [max_lt hlo one_pos]
  exact hθ (h.inner e he hmeet).2

section Two

variable {Q₁ Q₂ : Plane} {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ}

/-- **Two links ending at one point share their line and their marked side**: both see `R` inside
the same edge of the same tile, the only one at the vertex `R`. -/
theorem same_side (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂) :
    (∀ y, g₂ y = c₂ → g₁ y = c₁) ∧ (∀ e ∈ D.lineChain g₂ c₂, e ∈ D.lineChain g₁ c₁) := by
  obtain ⟨i, k, hik⟩ := h1.end_vertex
  obtain ⟨ε₁, hε₁, hR₁⟩ := h1.across
  obtain ⟨ε₂, hε₂, hR₂⟩ := h2.across
  have hj : ε₁.1 = ε₂.1 := openSegment_tile_unique D hik hR₁ hR₂
  obtain ⟨j, m⟩ := ε₁
  obtain ⟨j', m'⟩ := ε₂
  simp only at hj
  subst hj
  have hm : m = m' := Tri.openSegment_edge_unique (D.tile j) hR₁ hR₂
  subst hm
  exact chain_transfer D h1.hg h2.hg hε₁ hε₂

/-- A link cannot start strictly inside another link ending at the same point. -/
theorem not_between (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂)
    (hQ : Q₂ ∈ openSegment ℝ Q₁ R) : False := by
  obtain ⟨t2, ht2, hQ2⟩ := openSegment_param.mp hQ
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_left (D.lineChain g₁ c₁)
    (fun x => edgeLo Q₁ R (D.tile x.1) x.2) (fun x => edgeHi Q₁ R (D.tile x.1) x.2) t2
    ht2.1 Set.finite_empty (fun y hy _ => by
      rw [sub_self] at hy
      obtain ⟨e, he, hye⟩ := h1.cov _ (openSegment_param.mpr ⟨y, ⟨hy.1, hy.2.trans ht2.2⟩, rfl⟩)
      exact ⟨e, he, (h1.mem_edge_iff he y).mp hye⟩)
  set m := max (edgeLo Q₁ R (D.tile e.1) e.2) 0
  have hm : m < t2 := max_lt hlo ht2.1
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q₁ R).Nonempty := by
    refine ⟨AffineMap.lineMap Q₁ R ((m + t2) / 2), (h1.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q₁ R (D.tile e.1) e.2) 0]
    · linarith
    · linarith [le_max_right (edgeLo Q₁ R (D.tile e.1) e.2) 0]
    · linarith [ht2.2]
  obtain ⟨-, hθ⟩ := h1.inner e he hmeet
  have he2 : e ∈ D.lineChain g₂ c₂ := (same_side h2 h1).2 e he
  refine h2.start e he2 hθ ?_ (AffineMap.lineMap Q₁ R (edgeLo Q₁ R (D.tile e.1) e.2))
    ((h1.mem_edge_iff he _).mpr ⟨le_rfl, (hlo.trans_le hhi).le⟩) ?_
  · rw [← hQ2]; exact (h1.mem_edge_iff he _).mpr ⟨hlo.le, hhi⟩
  · rw [← hQ2]
    have := (lineMap_mem_openSegment_params h1.ne (a := edgeLo Q₁ R (D.tile e.1) e.2) (b := 1)
      (t := t2)).mpr (by rw [openSegment_eq_Ioo (hlo.trans ht2.2)]; exact ⟨hlo, ht2.2⟩)
    rwa [AffineMap.lineMap_apply_one] at this

/-- Two links cannot end at one point from opposite directions. -/
theorem not_opposite (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂)
    {t2 : ℝ} (ht2 : 1 < t2) (hQ2 : AffineMap.lineMap Q₁ R t2 = Q₂) : False := by
  obtain ⟨e, he, hθ, hlo, hhi⟩ := h1.leave
  have he2 : e ∈ D.lineChain g₂ c₂ := (same_side h2 h1).2 e he
  set s := (1 + min (edgeHi Q₁ R (D.tile e.1) e.2) t2) / 2
  have hs1 : 1 < s := by
    have := lt_min hhi ht2
    simp only [s]; linarith
  have hs2 : s < min (edgeHi Q₁ R (D.tile e.1) e.2) t2 := by
    have := lt_min hhi ht2
    simp only [s]; linarith
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q₂ R).Nonempty := by
    refine ⟨AffineMap.lineMap Q₁ R s, (h1.mem_edge_iff he _).mpr
      ⟨by rw [hlo]; exact hs1.le, (hs2.trans_le (min_le_left _ _)).le⟩, ?_⟩
    rw [← hQ2, openSegment_symm]
    have := (lineMap_mem_openSegment_params h1.ne (a := 1) (b := t2) (t := s)).mpr
      (by rw [openSegment_eq_Ioo ht2]; exact ⟨hs1, hs2.trans_le (min_le_right _ _)⟩)
    rwa [AffineMap.lineMap_apply_one] at this
  exact hθ (h2.inner e he2 hmeet).2

end Two

end LinkData

/-- **At most one link ends at a point.** -/
theorem link_unique {Q₁ Q₂ R : Plane} (h1 : IsLink D isθ Q₁ R) (h2 : IsLink D isθ Q₂ R) :
    Q₁ = Q₂ := by
  obtain ⟨g₁, c₁, h1⟩ := h1
  obtain ⟨g₂, c₂, h2⟩ := h2
  have hon := (h1.same_side h2).1 Q₂ h2.hQ
  obtain ⟨t2, ht2⟩ := eq_lineMap_of_level h1.hg h1.ne h1.hQ h1.hR hon
  rcases lt_trichotomy t2 0 with h0 | h0 | h0
  · exfalso
    refine h2.not_between h1 ?_
    rw [ht2]
    have := (lineMap_mem_openSegment_params h1.ne (a := t2) (b := 1) (t := 0)).mpr
      (by rw [openSegment_eq_Ioo (h0.trans one_pos)]; exact ⟨h0, one_pos⟩)
    rwa [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] at this
  · rw [ht2, h0, AffineMap.lineMap_apply_zero]
  · rcases lt_trichotomy t2 1 with h1' | h1' | h1'
    · exact (h1.not_between h2 (openSegment_param.mpr ⟨t2, ⟨h0, h1'⟩, ht2.symm⟩)).elim
    · exact absurd (by rw [ht2, h1', AffineMap.lineMap_apply_one]) h2.ne
    · exact (h1.not_opposite h2 h1' ht2.symm).elim

end TriangleTiling
