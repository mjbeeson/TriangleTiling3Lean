/-
At the two ends of a link.

A link starts at a vertex of the tiling. At its end `R`, where `R` lies inside an edge of a tile
`S` on side 2:

* every other tile at `R` lies on side 1;
* the only marked edge at `R` alone on its ray is the arriving one;
* two edges at `R` sharing a ray point into side 1, so no edge runs from `R` backwards along
  their ray (the backwards direction enters `S`).
-/
import TriangleTiling.Tiling.HalfDisk
import TriangleTiling.Tiling.Extension

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} {D : Dissection N} {isθ : Fin N × Fin 3 → Prop}

/-- The lower end of a chain edge, as a vertex. -/
theorem exists_pts_eq_lo (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0)
    {Q F : Plane} (hQF : Q ≠ F) (hQ : g Q = c) (hF : g F = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q F (edgeLo Q F (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases min_choice (lineParam Q F ((D.tile e.1).pts e.2))
    (lineParam Q F ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeLo, hm, eq_lineMap_lineParam hg hQF hQ hF n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeLo, hm, eq_lineMap_lineParam hg hQF hQ hF n2]⟩

theorem lineMap_params {Q R : Plane} (a b t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap Q R a) (AffineMap.lineMap Q R b) t
      = AffineMap.lineMap Q R (a + t * (b - a)) := by
  simp only [AffineMap.lineMap_apply_module']
  rw [show (b • (R - Q) + Q) - (a • (R - Q) + Q) = (b - a) • (R - Q) by
    rw [sub_smul]; abel]
  rw [smul_smul, add_smul]
  abel

/-- Two lines through one tile edge, with the tile on the far side of both: their near chains
coincide (both inclusions of `chain_transfer`). -/
theorem chain_iff {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {ε : Fin N × Fin 3} (h₁ : ε ∈ D.lineChain (-g₁) (-c₁)) (h₂ : ε ∈ D.lineChain (-g₂) (-c₂))
    (e : Fin N × Fin 3) : e ∈ D.lineChain g₁ c₁ ↔ e ∈ D.lineChain g₂ c₂ :=
  ⟨(chain_transfer D hg₂ hg₁ h₂ h₁).2 e, (chain_transfer D hg₁ hg₂ h₁ h₂).2 e⟩

/-- The level of a tile on the far side of a line, in its own coordinate. -/
theorem chain_coord {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c)) :
    0 < g ((D.tile ε.1).pts (ε.2 + 2)) - c ∧ ∀ z, g z - c =
      (D.tile ε.1).basis.coord (ε.2 + 2) z * (g ((D.tile ε.1).pts (ε.2 + 2)) - c) := by
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp hε
  simp only [LinearMap.neg_apply, neg_inj] at a1 a2
  have b3 := a3 (ε.2 + 2)
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at b3
  have i1 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  have i2 : ∀ m : Fin 3, m + 2 + 2 = m + 1 := by decide
  refine ⟨sub_pos.mpr (lt_of_le_of_ne b3 (Ne.symm (third_off_line _ hg ε.2 a1 a2))), fun z => ?_⟩
  exact level_eq_coord _ g c (ε.2 + 2) (by rw [i1]; exact a1) (by rw [i2]; exact a2) z

/-- An edge at a point of a line, with both ends on the line, has that point's parameter as its
lower or upper parameter. -/
theorem end_param_at (D : Dissection N) {Q W : Plane} (hQW : Q ≠ W) {q : ℝ} {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D (AffineMap.lineMap Q W q)) :
    edgeLo Q W (D.tile e.1) e.2 = q ∨ edgeHi Q W (D.tile e.1) e.2 = q := by
  have hq : lineParam Q W (AffineMap.lineMap Q W q) = q := lineParam_lineMap hQW q
  rcases (mem_edgesAt D).mp he with h1 | h1
  · rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with h2 | h2
    · left; rw [edgeLo, min_eq_left h2, h1, hq]
    · right; rw [edgeHi, max_eq_left h2, h1, hq]
  · rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with h2 | h2
    · right; rw [edgeHi, max_eq_right h2, h1, hq]
    · left; rw [edgeLo, min_eq_right h2, h1, hq]

/-- A chain edge with upper parameter `q` is an edge at the point `q`, with far end at its lower
parameter. -/
theorem edgesAt_of_hi (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q W : Plane}
    (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) {q : ℝ} (hhi : edgeHi Q W (D.tile e.1) e.2 = q) :
    e ∈ edgesAt D (AffineMap.lineMap Q W q) ∧
      farEnd D (AffineMap.lineMap Q W q) e = AffineMap.lineMap Q W (edgeLo Q W (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  have e1 := eq_lineMap_lineParam hg hQW hQ hW n1
  have e2 := eq_lineMap_lineParam hg hQW hQ hW n2
  rw [edgeHi] at hhi
  rw [edgeLo]
  rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with hle | hle
  · rw [max_eq_right hle] at hhi
    rw [min_eq_left hle]
    have hR : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q W q := by rw [← e2, hhi]
    have hne : (D.tile e.1).pts e.2 ≠ AffineMap.lineMap Q W q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans hR.symm)
    exact ⟨(mem_edgesAt D).mpr (Or.inr hR), by rw [farEnd, if_neg hne, e1]⟩
  · rw [max_eq_left hle] at hhi
    rw [min_eq_right hle]
    have hR : (D.tile e.1).pts e.2 = AffineMap.lineMap Q W q := by rw [← e1, hhi]
    exact ⟨(mem_edgesAt D).mpr (Or.inl hR), by rw [farEnd, if_pos hR, e2]⟩

/-- A chain edge with lower parameter `q` is an edge at the point `q`, with far end at its upper
parameter. -/
theorem edgesAt_of_lo (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q W : Plane}
    (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) {q : ℝ} (hlo : edgeLo Q W (D.tile e.1) e.2 = q) :
    e ∈ edgesAt D (AffineMap.lineMap Q W q) ∧
      farEnd D (AffineMap.lineMap Q W q) e = AffineMap.lineMap Q W (edgeHi Q W (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  have e1 := eq_lineMap_lineParam hg hQW hQ hW n1
  have e2 := eq_lineMap_lineParam hg hQW hQ hW n2
  rw [edgeLo] at hlo
  rw [edgeHi]
  rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with hle | hle
  · rw [min_eq_left hle] at hlo
    rw [max_eq_right hle]
    have hR : (D.tile e.1).pts e.2 = AffineMap.lineMap Q W q := by rw [← e1, hlo]
    exact ⟨(mem_edgesAt D).mpr (Or.inl hR), by rw [farEnd, if_pos hR, e2]⟩
  · rw [min_eq_right hle] at hlo
    rw [max_eq_left hle]
    have hR : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q W q := by rw [← e2, hlo]
    have hne : (D.tile e.1).pts e.2 ≠ AffineMap.lineMap Q W q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans hR.symm)
    exact ⟨(mem_edgesAt D).mpr (Or.inr hR), by rw [farEnd, if_neg hne, e1]⟩

/-- **A lonely edge at an interior point.** If `Q` is interior to the target and the edge `e`
at `Q` shares its ray with no other edge, then `Q` lies strictly inside an edge on the other side
of the line of `e`. -/
theorem lonely_relint (D : Dissection N) {Q : Plane} (hQ : Q ∈ interior D.target.carrier) {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D Q) (hlonely : ∀ e' ∈ edgesAt D Q, e' ≠ e → ¬ SameRayAt D Q e e') :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g (farEnd D Q e) = c ∧
      e ∈ D.lineChain g c ∧ ∃ e₂ ∈ D.lineChain (-g) (-c),
        Q ∈ openSegment ℝ ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) := by
  set F := farEnd D Q e
  have hQF : Q ≠ F := (farEnd_ne D he).symm
  obtain ⟨g₀, c₀, hg₀, hQ₀, hF₀⟩ := ray_level (farEnd_ne D he)
  obtain ⟨g, c, hg, hgQ, hgF, hec⟩ : ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧
      g F = c ∧ e ∈ D.lineChain g c := by
    rcases edgesAt_chain D he hQ₀ hF₀ with h' | h'
    · exact ⟨g₀, c₀, hg₀, hQ₀, hF₀, h'⟩
    · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀],
        by simp only [LinearMap.neg_apply, F, hF₀], h'⟩
  -- A point of `e` near `Q` is interior.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior Q hQ
  have hdQF : 0 < dist Q F := dist_pos.mpr hQF
  set τ := min (1 / 2) (r / (2 * dist Q F))
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hint : AffineMap.lineMap Q F τ ∈ interior D.target.carrier := by
    apply hball
    rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hτ0]
    have : τ ≤ r / (2 * dist Q F) := min_le_right _ _
    calc τ * dist Q F ≤ r / (2 * dist Q F) * dist Q F :=
          mul_le_mul_of_nonneg_right this hdQF.le
      _ = r / 2 := by field_simp
      _ < r := by linarith
  exact ⟨g, c, hg, hgQ, hgF, hec, lonely_openSegment D he hg hgQ hgF hec hlonely ⟨hτ0, hτ1⟩ hint⟩

namespace LinkData

variable {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}

theorem lineParam_R (h : LinkData D isθ Q R g c) : lineParam Q R R = 1 := by
  have := lineParam_lineMap h.ne 1
  rwa [AffineMap.lineMap_apply_one] at this

/-- A link starts at a vertex of the tiling. -/
theorem start_vertex (h : LinkData D isθ Q R g c) : ∃ i k, (D.tile i).pts k = Q := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_right (D.lineChain g c)
    (fun x => edgeLo Q R (D.tile x.1) x.2) (fun x => edgeHi Q R (D.tile x.1) x.2) 0
    one_pos Set.finite_empty (fun y hy _ => by
      rw [zero_add] at hy
      obtain ⟨e, he, hye⟩ := h.cov _ (openSegment_param.mpr ⟨y, hy, rfl⟩)
      exact ⟨e, he, (h.mem_edge_iff he y).mp hye⟩)
  have hm : 0 < min (edgeHi Q R (D.tile e.1) e.2) 1 := lt_min hhi one_pos
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R (min (edgeHi Q R (D.tile e.1) e.2) 1 / 2),
      (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩, openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith
    · linarith [min_le_left (edgeHi Q R (D.tile e.1) e.2) 1]
    · linarith
    · linarith [min_le_right (edgeHi Q R (D.tile e.1) e.2) 1]
  obtain ⟨hsub, -⟩ := h.inner e he hmeet
  have h0 := (h.params_of_inner he hsub).1
  obtain ⟨k, hk⟩ := exists_pts_eq_lo D h.hg h.ne h.hQ h.hR he
  exact ⟨e.1, k, by rw [hk, le_antisymm hlo h0, AffineMap.lineMap_apply_zero]⟩

/-- **Other tiles at the end are on side 1.** -/
theorem tiles_side (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {i : Fin N} (hi : i ≠ ε.1) (hRi : R ∈ (D.tile i).carrier) :
    ∀ z ∈ (D.tile i).carrier, g z ≤ c := by
  intro z hz
  have h1 := tile_side_of_openSegment D hRε hi hRi z hz
  obtain ⟨hpos, hcoord⟩ := chain_coord h.hg hε
  have := hcoord z
  nlinarith

/-- The edge of a chain at `R`, in parameters: `1` is one of its two ends. -/
theorem end_param (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ edgesAt D R) :
    edgeLo Q R (D.tile e.1) e.2 = 1 ∨ edgeHi Q R (D.tile e.1) e.2 = 1 := by
  rw [← AffineMap.lineMap_apply_one (k := ℝ) Q R] at he
  exact end_param_at D h.ne he

end LinkData

/-- The parameters of an edge at `R` along a line through `R`. -/
theorem edgesAt_params' {Q W R : Plane} (hQW : Q ≠ W) {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D R) {r p : ℝ} (hR : R = AffineMap.lineMap Q W r)
    (hfar : farEnd D R e = AffineMap.lineMap Q W p) :
    edgeLo Q W (D.tile e.1) e.2 = min r p ∧ edgeHi Q W (D.tile e.1) e.2 = max r p := by
  have hr : lineParam Q W R = r := by rw [hR, lineParam_lineMap hQW]
  have hp : lineParam Q W (farEnd D R e) = p := by rw [hfar, lineParam_lineMap hQW]
  rw [edgeLo, edgeHi]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hr, hp]; exact ⟨rfl, rfl⟩
  · rw [h1, h2, hr, hp, min_comm, max_comm]; exact ⟨rfl, rfl⟩

namespace LinkData

variable {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}

/-- The side-2 edge through `R`, in parameters. -/
theorem eps_params (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))) :
    edgeLo Q R (D.tile ε.1) ε.2 < 1 ∧ 1 < edgeHi Q R (D.tile ε.1) ε.2 := by
  have hng : -g ≠ 0 := neg_ne_zero.mpr h.hg
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  obtain ⟨b1, b2⟩ := lineChain_ends D hε
  have h1 : AffineMap.lineMap Q R (1 : ℝ) ∈
      openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) := by
    rw [AffineMap.lineMap_apply_one]; exact hRε
  exact (lineMap_mem_openSegment_iff hng h.ne hnQ hnR _ _ b1 b2 1).mp h1

/-- **No edge at the end lies on side 2**: it would overlap the side-2 edge through `R`. -/
theorem not_side2 (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {z : Fin N × Fin 3} (hz : z ∈ edgesAt D R) : z ∉ D.lineChain (-g) (-c) := by
  intro hz2
  have hng : -g ≠ 0 := neg_ne_zero.mpr h.hg
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  obtain ⟨hε1, hε2⟩ := h.eps_params hε hRε
  have hlt := chain_lo_lt_hi D hng h.ne hnQ hnR hz2
  rcases h.end_param hz with h1 | h1
  · have := lineChain_eq_of_overlap D hng h.ne hnQ hnR hz2 hε
      (lt_of_le_of_lt (max_le h1.le hε1.le) (lt_min (h1 ▸ hlt) hε2))
    rw [this] at h1
    linarith
  · have := lineChain_eq_of_overlap D hng h.ne hnQ hnR hz2 hε
      (lt_of_lt_of_le (max_lt (h1 ▸ hlt) hε1) (le_min h1.ge hε2.le))
    rw [this] at h1
    linarith

/-- The far end of an edge at `R` is on the link's line or strictly on side 1, according to
the side of its tile. -/
theorem far_le (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {x : Fin N × Fin 3} (hx : x ∈ edgesAt D R) : g (farEnd D R x) ≤ c := by
  have hRx : R ∈ (D.tile x.1).carrier := by
    have : R ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    exact (D.tile x.1).edge_subset_carrier x.2 this
  have hFx : farEnd D R x ∈ (D.tile x.1).carrier := by
    have : farEnd D R x ∈ (D.tile x.1).edge x.2 := by
      rw [edgesAt_edge D hx]; exact right_mem_segment ℝ _ _
    exact (D.tile x.1).edge_subset_carrier x.2 this
  have hne : x.1 ≠ ε.1 := by
    intro hxε
    rcases (mem_edgesAt D).mp hx with h1 | h1
    · have h2 : (D.tile ε.1).pts x.2 = R := by rw [← hxε]; exact h1
      exact Tri.vertex_not_mem_openSegment (D.tile ε.1) x.2 ε.2 (by rw [h2]; exact hRε)
    · have h2 : (D.tile ε.1).pts (x.2 + 1) = R := by rw [← hxε]; exact h1
      exact Tri.vertex_not_mem_openSegment (D.tile ε.1) (x.2 + 1) ε.2 (by rw [h2]; exact hRε)
  exact h.tiles_side hε hRε hne hRx _ hFx

/-- **Shared rays at the end point into side 1.** -/
theorem far_lt_of_partner (h : LinkData D isθ Q R g c) {x y : Fin N × Fin 3}
    (hx : x ∈ edgesAt D R) (hy : y ∈ edgesAt D R) (hxy : x ≠ y) (hray : SameRayAt D R x y) :
    g (farEnd D R x) < c := by
  obtain ⟨ε, hε, hRε⟩ := h.across
  rcases (h.far_le hε hRε hx).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨t, ht, hFy⟩ := hray
    set F := farEnd D R x
    have hgy : g (farEnd D R y) = c := by rw [hFy]; exact level_lineMap h.hR heq t
    have cx := edgesAt_chain D hx h.hR heq
    have cy := edgesAt_chain D hy h.hR hgy
    have nx := h.not_side2 hε hRε hx
    have ny := h.not_side2 hε hRε hy
    have cx' : x ∈ D.lineChain g c := cx.resolve_right nx
    have cy' : y ∈ D.lineChain g c := cy.resolve_right ny
    -- The two edges overlap near `R`.
    have hRF : R ≠ F := (farEnd_ne D hx).symm
    have hs : 0 < min 1 t := lt_min one_pos ht
    have hm1 := mem_edge_of_ray D hx (t := 1) (AffineMap.lineMap_apply_one R F).symm hs.le
      (min_le_left _ _)
    have hm2 := mem_edge_of_ray D hy hFy hs.le (min_le_right _ _)
    have hR1 : R ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    have hR2 : R ∈ (D.tile y.1).edge y.2 := by rw [edgesAt_edge D hy]; exact left_mem_segment ℝ _ _
    have hneq : R ≠ AffineMap.lineMap R F (min 1 t) := by
      intro h'
      have : AffineMap.lineMap R F (0 : ℝ) = AffineMap.lineMap R F (min 1 t) := by
        rw [AffineMap.lineMap_apply_zero]; exact h'
      exact hs.ne (AffineMap.lineMap_injective ℝ hRF this)
    exact hxy (lineChain_eq_of_two D h.hg cx' cy' hneq ⟨hR1, hR2⟩ ⟨hm1, hm2⟩)

/-- **Nothing runs backwards from the end along a shared ray**: it would enter the side-2 tile. -/
theorem back_of_partner (h : LinkData D isθ Q R g c) {x y : Fin N × Fin 3}
    (hx : x ∈ edgesAt D R) (hy : y ∈ edgesAt D R) (hxy : x ≠ y) (hray : SameRayAt D R x y) :
    ∀ e : Fin N × Fin 3, R ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, R ∉ openSegment ℝ z (farEnd D R x) := by
  intro e hRe z hz hRz
  obtain ⟨ε, hε, hRε⟩ := h.across
  have hlt := h.far_lt_of_partner hx hy hxy hray
  -- `z` lies strictly on side 2.
  have hgz : c < g z := by
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hRz
    have hR := h.hR
    rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hR
    have key : a * (g z - c) = b * (c - g (farEnd D R x)) := by
      linear_combination hR - c * hab
    have := mul_pos hb (sub_pos.mpr hlt)
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨hκ, hcoord⟩ := chain_coord h.hg hε
  have hcz : 0 < (D.tile ε.1).basis.coord (ε.2 + 2) z := by
    have := hcoord z
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior (D.tile ε.1) ε.2 hRε hcz
  set τ := min τ0 1 / 2
  have hτ : 0 < τ := by have := lt_min hτ0 one_pos; simp only [τ]; linarith
  have hττ : τ < τ0 := by have := min_le_left τ0 1; simp only [τ]; linarith
  have hτ1 : τ ≤ 1 := by have := min_le_right τ0 1; simp only [τ]; linarith
  have hmem : AffineMap.lineMap R z τ ∈ (D.tile e.1).edge e.2 := by
    rw [Tri.edge] at hRe hz ⊢
    refine (convex_segment (𝕜 := ℝ) _ _).segment_subset hRe hz ?_
    rw [segment_eq_image_lineMap]
    exact ⟨τ, ⟨hτ.le, hτ1⟩, rfl⟩
  exact D.edge_point_not_interior hmem _ (hint τ hτ hττ)

/-- An edge of side 1 whose upper parameter is `1` is an edge at `R`, with far end at its lower
parameter. -/
theorem arrive_at (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (hhi : edgeHi Q R (D.tile e.1) e.2 = 1) :
    e ∈ edgesAt D R ∧ farEnd D R e = AffineMap.lineMap Q R (edgeLo Q R (D.tile e.1) e.2) := by
  have := edgesAt_of_hi D h.hg h.ne h.hQ h.hR he hhi
  rwa [AffineMap.lineMap_apply_one] at this

/-- **The lonely marked edge at the end.** The arriving marked edge is alone on its ray, and it
is the only marked edge at `R` alone on its ray. -/
theorem lonely_marked (h : LinkData D isθ Q R g c) :
    ∃ e₀ ∈ edgesAt D R, isθ e₀ ∧
      (∀ e' ∈ edgesAt D R, ¬ (e₀ ≠ e' ∧ SameRayAt D R e₀ e')) ∧
      ∀ e ∈ edgesAt D R, isθ e → (∀ e' ∈ edgesAt D R, ¬ (e ≠ e' ∧ SameRayAt D R e e')) →
        e = e₀ := by
  obtain ⟨e₀, he₀, hθ₀, -, hlo₀, hhi₀⟩ := h.arrive
  obtain ⟨he₀R, hfar₀⟩ := h.arrive_at he₀ hhi₀
  obtain ⟨ε, hε, hRε⟩ := h.across
  obtain ⟨hε1, hε2⟩ := h.eps_params hε hRε
  obtain ⟨eo, heo, hθo, hloo, hhio⟩ := h.leave
  have hR1 : R = AffineMap.lineMap Q R (1 : ℝ) := (AffineMap.lineMap_apply_one Q R).symm
  refine ⟨e₀, he₀R, hθ₀, ?_, ?_⟩
  · -- `e₀` is alone on its ray.
    rintro e' he' ⟨hne, t, ht, hFt⟩
    set lo₀ := edgeLo Q R (D.tile e₀.1) e₀.2
    have hfar' : farEnd D R e' = AffineMap.lineMap Q R (1 + t * (lo₀ - 1)) := by
      rw [hFt, hfar₀]
      calc AffineMap.lineMap R (AffineMap.lineMap Q R lo₀) t
          = AffineMap.lineMap (AffineMap.lineMap Q R (1 : ℝ)) (AffineMap.lineMap Q R lo₀) t := by
            rw [AffineMap.lineMap_apply_one]
        _ = _ := lineMap_params 1 lo₀ t
    obtain ⟨plo, phi⟩ := edgesAt_params' h.ne he' hR1 hfar'
    have hp : 1 + t * (lo₀ - 1) < 1 := by nlinarith
    rw [min_eq_right hp.le] at plo
    rw [max_eq_left hp.le] at phi
    have hg' : g (farEnd D R e') = c := by rw [hfar']; exact level_lineMap h.hQ h.hR _
    rcases edgesAt_chain D he' h.hR hg' with c1 | c2
    · apply hne
      refine (lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR c1 he₀ ?_).symm
      rw [plo, phi, hhi₀, min_self]
      exact max_lt hp hlo₀
    · exact h.not_side2 hε hRε he' c2
  · -- Any marked edge alone on its ray is `e₀`.
    intro e he hθ hlonely
    obtain ⟨g', c', hg', -, -, hec, e₂, he₂, hRe₂⟩ := lonely_relint D h.end_interior he
      (fun e' he' hne hray => hlonely e' he' ⟨hne.symm, hray⟩)
    -- `e₂` is the side-2 edge through `R`.
    obtain ⟨i, k, hik⟩ := h.end_vertex
    have hj : e₂.1 = ε.1 := openSegment_tile_unique D hik hRe₂ hRε
    have hm : e₂.2 = ε.2 := by
      have := hRe₂
      rw [hj] at this
      exact Tri.openSegment_edge_unique (D.tile ε.1) this hRε
    have heq : e₂ = ε := Prod.ext hj hm
    rw [heq] at he₂
    have he1 : e ∈ D.lineChain g c := (chain_iff hg' h.hg he₂ hε e).mp hec
    have hlt := chain_lo_lt_hi D h.hg h.ne h.hQ h.hR he1
    rcases h.end_param he with h1 | h1
    · exfalso
      have := lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR he1 heo
        (lt_of_le_of_lt (max_le h1.le hloo.le) (lt_min (h1 ▸ hlt) hhio))
      rw [this] at hθ
      exact hθo hθ
    · exact lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR he1 he₀
        (lt_of_lt_of_le (max_lt (h1 ▸ hlt) hlo₀) (le_min h1.ge hhi₀.ge))

end LinkData

end TriangleTiling
