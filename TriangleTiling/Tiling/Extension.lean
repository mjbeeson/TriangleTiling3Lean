/-
Extending a mixed ray to a link (the step "extend that segment to the maximal segment `QR`
supporting only tiles with `c` edges" in the paper's `lemma:crelation4`, and its analogue for
`lemma:essentialsegments`).

Let a marked edge `e₁` and an unmarked edge `e₂` leave `Q` along the same ray, and suppose no edge
passes through `Q` backwards along that ray. Run along the ray as far as the marked side is covered
by marked edges, up to `R`. Either `R` is inside an edge on the other side, and `QR` is a link; or
the other side also has a vertex at `R`, and then the edges on the two sides of `QR` give a
relation between edge lengths: marked edges on one side, at least one unmarked edge on the other.
-/
import TriangleTiling.Tiling.Links
import TriangleTiling.Tiling.WallSum

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)

/-- The parameters of an edge at `Q` along a ray through it. -/
theorem edgesAt_params {Q F : Plane} (hQF : Q ≠ F) {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    {t : ℝ} (ht : 0 < t) (hfar : farEnd D Q e = AffineMap.lineMap Q F t) :
    edgeLo Q F (D.tile e.1) e.2 = 0 ∧ edgeHi Q F (D.tile e.1) e.2 = t := by
  have h0 : lineParam Q F Q = 0 := by
    have := lineParam_lineMap hQF 0
    rwa [AffineMap.lineMap_apply_zero] at this
  have ht' : lineParam Q F (farEnd D Q e) = t := by rw [hfar, lineParam_lineMap hQF]
  rw [edgeLo, edgeHi]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, h0, ht', min_eq_left ht.le, max_eq_right ht.le]; exact ⟨rfl, rfl⟩
  · rw [h1, h2, h0, ht', min_eq_right ht.le, max_eq_left ht.le]; exact ⟨rfl, rfl⟩

/-- A tile with edges in both chains of a line would be flat. -/
theorem tile_ne_of_chains {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {e₁ e₂ : Fin N × Fin 3}
    (h1 : e₁ ∈ D.lineChain g c) (h2 : e₂ ∈ D.lineChain (-g) (-c)) : e₁.1 ≠ e₂.1 := by
  intro h
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, b3⟩ := Dissection.mem_lineChain.mp h2
  apply third_off_line (D.tile e₁.1) hg e₁.2 a1 a2
  have := b3 (e₁.2 + 2)
  rw [← h] at this
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact le_antisymm (a3 _) this

/-- **The line of a mixed pair.** Two different edges at `Q` along one ray lie on opposite sides
of their line. -/
theorem pair_line {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (t₂ : ℝ), g ≠ 0 ∧ g Q = c ∧ g (farEnd D Q e₁) = c ∧
      e₁ ∈ D.lineChain g c ∧ e₂ ∈ D.lineChain (-g) (-c) ∧ 0 < t₂ ∧
      farEnd D Q e₂ = AffineMap.lineMap Q (farEnd D Q e₁) t₂ := by
  obtain ⟨t₂, ht₂, hF₂⟩ := hray
  set F := farEnd D Q e₁
  have hQF : Q ≠ F := (farEnd_ne D he₁).symm
  obtain ⟨g₀, c₀, hg₀, hQ₀, hF₀⟩ := ray_level (farEnd_ne D he₁)
  -- Orient the line so that `e₁` is on the side `g ≤ c`.
  obtain ⟨g, c, hg, hQ, hF, h1⟩ : ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g F = c ∧
      e₁ ∈ D.lineChain g c := by
    rcases edgesAt_chain D he₁ hQ₀ hF₀ with h | h
    · exact ⟨g₀, c₀, hg₀, hQ₀, hF₀, h⟩
    · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀], by simp only [LinearMap.neg_apply, F, hF₀], h⟩
  refine ⟨g, c, t₂, hg, hQ, hF, h1, ?_, ht₂, hF₂⟩
  have hF2 : g (farEnd D Q e₂) = c := by rw [hF₂]; exact level_lineMap hQ hF t₂
  rcases edgesAt_chain D he₂ hQ hF2 with h2 | h2
  · exfalso
    -- Same side: the two edges overlap near `Q`.
    have hs : 0 < min 1 t₂ := lt_min one_pos ht₂
    have hm1 := mem_edge_of_ray D he₁ (t := 1) (AffineMap.lineMap_apply_one Q F).symm hs.le
      (min_le_left _ _)
    have hm2 := mem_edge_of_ray D he₂ hF₂ hs.le (min_le_right _ _)
    have hQ1 : Q ∈ (D.tile e₁.1).edge e₁.2 := by
      rw [edgesAt_edge D he₁]; exact left_mem_segment ℝ _ _
    have hQ2 : Q ∈ (D.tile e₂.1).edge e₂.2 := by
      rw [edgesAt_edge D he₂]; exact left_mem_segment ℝ _ _
    have hneq : Q ≠ AffineMap.lineMap Q F (min 1 t₂) := by
      intro h
      have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F (min 1 t₂) := by
        rw [AffineMap.lineMap_apply_zero]; exact h
      exact hs.ne (AffineMap.lineMap_injective ℝ hQF this)
    exact hne (lineChain_eq_of_two D hg h1 h2 hneq ⟨hQ1, hQ2⟩ ⟨hm1, hm2⟩).symm
  · exact h2

/-- An interval either lies in `[0, T]` or meets it in at most one point, if every interval point
strictly inside `(0, T)` forces the first. -/
theorem param_dich {lo hi T : ℝ} (h : ∀ x ∈ Ioo 0 T, x ∈ Icc lo hi → 0 ≤ lo ∧ hi ≤ T) :
    Icc lo hi ⊆ Icc 0 T ∨ (Icc lo hi ∩ Icc 0 T).Subsingleton := by
  by_cases hx : ∃ x ∈ Ioo 0 T, x ∈ Icc lo hi
  · obtain ⟨x, hx, hxI⟩ := hx
    obtain ⟨h0, hT⟩ := h x hx hxI
    left
    exact fun y hy => ⟨h0.trans hy.1, hy.2.trans hT⟩
  · right
    push Not at hx
    intro a ha b hb
    by_contra hab
    apply hx ((a + b) / 2)
    · rcases lt_or_gt_of_ne hab with h' | h'
      · constructor <;> linarith [ha.2.1, hb.2.2]
      · constructor <;> linarith [ha.2.2, hb.2.1]
    · constructor <;> linarith [ha.1.1, hb.1.1, ha.1.2, hb.1.2]

/-- **The sides of a wall segment, in parameters.** If every chain edge meeting `(0, T)` lies in
`[0, T]`, the chain edges inside the segment add up to its length. -/
theorem wall_sum_param {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q F : Plane} (hQF : Q ≠ F)
    (hQ : g Q = c) (hF : g F = c) {T : ℝ} (hT : 0 < T)
    (hint : openSegment ℝ Q (AffineMap.lineMap Q F T) ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ Q (AffineMap.lineMap Q F T), ∀ i,
      y ∉ interior (D.tile i).carrier)
    (hin : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
      x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
        0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T) :
    open Classical in
    ∑ e ∈ (D.lineChain g c).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Q (AffineMap.lineMap Q F T)),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist Q (AffineMap.lineMap Q F T) := by
  classical
  have hseg : AffineMap.lineMap Q F '' Icc 0 T = segment ℝ Q (AffineMap.lineMap Q F T) := by
    rw [← segment_eq_Icc hT.le, image_segment, AffineMap.lineMap_apply_zero]
  have hQR : Q ≠ AffineMap.lineMap Q F T := by
    intro h
    have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F T := by
      rw [AffineMap.lineMap_apply_zero]; exact h
    exact hT.ne (AffineMap.lineMap_injective ℝ hQF this)
  refine wall_sum D g c hg hQR ?_ hint hwall ?_
  · rw [← hseg]
    rintro _ ⟨t, -, rfl⟩
    exact level_lineMap hQ hF t
  · intro e he
    have himg : (D.tile e.1).edge e.2 =
        AffineMap.lineMap Q F '' Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
      edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2
    rw [himg, ← hseg]
    rcases param_dich (hin e he) with h | h
    · left; exact Set.image_mono h
    · right
      rw [← Set.image_inter (AffineMap.lineMap_injective ℝ hQF)]
      exact h.image _

/-- The upper end of a chain edge, as a vertex. -/
theorem exists_pts_eq_hi {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q F : Plane} (hQF : Q ≠ F)
    (hQ : g Q = c) (hF : g F = c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q F (edgeHi Q F (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases max_choice (lineParam Q F ((D.tile e.1).pts e.2))
    (lineParam Q F ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeHi, hm, eq_lineMap_lineParam hg hQF hQ hF n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeHi, hm, eq_lineMap_lineParam hg hQF hQ hF n2]⟩

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Extension of a mixed ray.** Let a marked edge `e₁` and an unmarked edge `e₂` leave `Q`
along the same ray, and let no edge pass through `Q` backwards along it. Then a link starts at
`Q`, or there is a relation: a set of marked edges and a set of edges containing an unmarked one,
with equal total lengths. -/
theorem extend_link {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂)
    (hθ₁ : isθ e₁) (hθ₂ : ¬ isθ e₂)
    (hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y (farEnd D Q e₁)) :
    (∃ R, IsLink D isθ Q R) ∨
    ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
      ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  obtain ⟨g, c, t₂, hg, hQ, hF, h1, h2, ht₂, hF₂⟩ := pair_line D he₁ he₂ hne hray
  set F := farEnd D Q e₁ with hFdef
  have hQF : Q ≠ F := (farEnd_ne D he₁).symm
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnQ : (-g) Q = -c := by simp [hQ]
  have hnF : (-g) F = -c := by simp only [LinearMap.neg_apply, hF]
  have hQ0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have mem₁ : ∀ e ∈ D.lineChain g c, ∀ t, AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hg hQF hQ hF he t
  have mem₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ t,
      AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
        t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hng hQF hnQ hnF he t
  have lt₁ : ∀ e ∈ D.lineChain g c, edgeLo Q F (D.tile e.1) e.2 < edgeHi Q F (D.tile e.1) e.2 :=
    fun e he => chain_lo_lt_hi D hg hQF hQ hF he
  have ov₁ : ∀ e ∈ D.lineChain g c, ∀ e' ∈ D.lineChain g c,
      max (edgeLo Q F (D.tile e.1) e.2) (edgeLo Q F (D.tile e'.1) e'.2)
        < min (edgeHi Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hg hQF hQ hF he he' h
  have ov₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ e' ∈ D.lineChain (-g) (-c),
      max (edgeLo Q F (D.tile e.1) e.2) (edgeLo Q F (D.tile e'.1) e'.2)
        < min (edgeHi Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hng hQF hnQ hnF he he' h
  obtain ⟨p₁lo, p₁hi⟩ := edgesAt_params D hQF he₁ one_pos (AffineMap.lineMap_apply_one Q F).symm
  obtain ⟨p₂lo, p₂hi⟩ := edgesAt_params D hQF he₂ ht₂ hF₂
  -- Nothing reaches behind `Q`.
  have back : ∀ e : Fin N × Fin 3, (∀ t, AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2)) →
      edgeLo Q F (D.tile e.1) e.2 < 0 → edgeHi Q F (D.tile e.1) e.2 < 0 := by
    intro e hmem hlo
    by_contra hhi
    push Not at hhi
    have hQe : Q ∈ (D.tile e.1).edge e.2 := by
      have := (hmem 0).mpr ⟨hlo.le, hhi⟩
      rwa [hQ0] at this
    refine hback e hQe _ ((hmem _).mpr ⟨le_rfl, (hlo.trans_le hhi).le⟩) ?_
    have := (lineMap_mem_openSegment_params hQF (a := edgeLo Q F (D.tile e.1) e.2) (b := 1)
      (t := 0)).mpr (by rw [openSegment_eq_Ioo (hlo.trans one_pos)]; exact ⟨hlo, one_pos⟩)
    rwa [hQ0, AffineMap.lineMap_apply_one] at this
  -- The farthest point `T` up to which side 1 is covered by marked edges.
  let Good : ℝ → Prop := fun t => 0 < t ∧ ∀ x ∈ Icc (0 : ℝ) t, ∃ e ∈ D.lineChain g c, isθ e ∧
    0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ t ∧
    x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2)
  have good1 : Good 1 :=
    ⟨one_pos, fun x hx => ⟨e₁, h1, hθ₁, p₁lo.ge, p₁hi.le, by rw [p₁lo, p₁hi]; exact hx⟩⟩
  set Cand := ((D.lineChain g c).image fun e => edgeHi Q F (D.tile e.1) e.2).filter Good
  have h1C : (1 : ℝ) ∈ Cand := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e₁, h1, p₁hi⟩, good1⟩
  set T := Cand.max' ⟨1, h1C⟩ with hTdef
  have hTgood : Good T := (Finset.mem_filter.mp (Finset.max'_mem Cand ⟨1, h1C⟩)).2
  have hTpos : 0 < T := hTgood.1
  have hmax : ∀ t, Good t → t ∈ (D.lineChain g c).image (fun e => edgeHi Q F (D.tile e.1) e.2) →
      t ≤ T := fun t ht hti => Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hti, ht⟩)
  -- Side-1 edges meeting `(0, T)` are among the covering ones.
  have inner₁ : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
      x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
        isθ e ∧ 0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T := by
    intro e he x hx hxe
    set S := (D.lineChain g c).filter fun e => isθ e ∧ 0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧
      edgeHi Q F (D.tile e.1) e.2 ≤ T
    have hcovS : ∀ y ∈ Icc 0 T, ∃ e' ∈ S,
        y ∈ Icc (edgeLo Q F (D.tile e'.1) e'.2) (edgeHi Q F (D.tile e'.1) e'.2) := by
      intro y hy
      obtain ⟨e', he', hθ', hlo', hhi', hye'⟩ := hTgood.2 y hy
      exact ⟨e', Finset.mem_filter.mpr ⟨he', hθ', hlo', hhi'⟩, hye'⟩
    suffices hS : e ∈ S from (Finset.mem_filter.mp hS).2
    rcases hxe.2.lt_or_eq with hxhi | hxhi
    · obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_right S
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) x
        (δ₀ := T - x) (by linarith [hx.2]) Set.finite_empty
        (fun y hy _ => hcovS y ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩)
      have : e = e' := ov₁ e he e' (Finset.mem_filter.mp he').1
        (lt_of_le_of_lt (max_le hxe.1 hlo') (lt_min hxhi hhi'))
      rw [this]; exact he'
    · obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_left S
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) x
        (δ₀ := x) hx.1 Set.finite_empty
        (fun y hy _ => hcovS y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩)
      have : e = e' := ov₁ e he e' (Finset.mem_filter.mp he').1
        (lt_of_lt_of_le (max_lt (by rw [hxhi]; exact lt₁ e he) hlo') (le_min hxhi.le hhi'))
      rw [this]; exact he'
  -- The segment `QR`.
  set R := AffineMap.lineMap Q F T with hRdef
  have hOS : openSegment ℝ Q R = AffineMap.lineMap Q F '' Ioo 0 T := by
    rw [← openSegment_eq_Ioo hTpos, image_openSegment, hQ0]
  have hSeg : segment ℝ Q R = AffineMap.lineMap Q F '' Icc 0 T := by
    rw [← segment_eq_Icc hTpos.le, image_segment, hQ0]
  have hQR : Q ≠ R := by
    intro h
    have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F T := by rw [hQ0]; exact h
    exact hTpos.ne (AffineMap.lineMap_injective ℝ hQF this)
  have hRc : g R = c := level_lineMap hQ hF T
  -- `R` is a vertex of a covering tile, so in the target.
  obtain ⟨eR, heR, -, -, heRhi, heRT⟩ := hTgood.2 T ⟨hTpos.le, le_rfl⟩
  have hRhi : edgeHi Q F (D.tile eR.1) eR.2 = T := le_antisymm heRhi heRT.2
  obtain ⟨kR, hkR⟩ := exists_pts_eq_hi D hg hQF hQ hF heR
  rw [hRhi] at hkR
  have hRt : R ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨eR.1, (D.tile eR.1).edge_subset_carrier eR.2 ((mem₁ eR heR T).mpr heRT)⟩
  -- The open segment is interior and a wall.
  have hT12 : e₁.1 ≠ e₂.1 := tile_ne_of_chains D hg h1 h2
  have near : ∀ τ : ℝ, 0 < τ → τ < 1 → τ < t₂ →
      AffineMap.lineMap Q F τ ∈ interior D.target.carrier := by
    intro τ h0 h1' h2'
    obtain ⟨a1, a2⟩ := lineChain_ends D h1
    obtain ⟨b1, b2⟩ := lineChain_ends D h2
    have ha := (lineMap_mem_openSegment_iff hg hQF hQ hF _ _ a1 a2 τ).mpr
      (by rw [p₁lo, p₁hi]; exact ⟨h0, h1'⟩)
    have hb := (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 τ).mpr
      (by rw [p₂lo, p₂hi]; exact ⟨h0, h2'⟩)
    exact interior_of_two_openSegment D hT12 ha hb
  have hint : openSegment ℝ Q R ⊆ interior D.target.carrier := by
    rw [hOS]
    rintro _ ⟨x, hx, rfl⟩
    set τ := min (min x 1) t₂ / 2
    have hm : 0 < min (min x 1) t₂ := lt_min (lt_min hx.1 one_pos) ht₂
    have hτ0 : 0 < τ := by simp only [τ]; linarith
    have hτx : τ < x := by
      have := min_le_left (min x 1) t₂; have := min_le_left x 1; simp only [τ]; linarith
    have hτ1 : τ < 1 := by
      have := min_le_left (min x 1) t₂; have := min_le_right x 1; simp only [τ]; linarith
    have hτ2 : τ < t₂ := by
      have := min_le_right (min x 1) t₂; simp only [τ]; linarith
    have hxin : AffineMap.lineMap Q F x ∈ openSegment ℝ (AffineMap.lineMap Q F τ) R :=
      (lineMap_mem_openSegment_params hQF).mpr
        (by rw [openSegment_eq_Ioo (hτx.trans hx.2)]; exact ⟨hτx, hx.2⟩)
    exact D.target.convex.openSegment_interior_closure_subset_interior (near τ hτ0 hτ1 hτ2)
      (subset_closure hRt) hxin
  have hwall : ∀ y ∈ openSegment ℝ Q R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rw [hOS] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨e, he, -, -, -, hxe⟩ := hTgood.2 x ⟨hx.1.le, hx.2.le⟩
    exact D.edge_point_not_interior ((mem₁ e he x).mpr hxe)
  have hint0 : openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F T)
      ⊆ interior D.target.carrier := by rw [hQ0]; exact hint
  have hwall0 : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F T),
      ∀ i, y ∉ interior (D.tile i).carrier := by rw [hQ0]; exact hwall
  -- Side 2 at `R`.
  obtain ⟨ε, hε, hεlo, hεhi⟩ := exists_interval_left (D.lineChain (-g) (-c))
    (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) T
    hTpos (vertex_params_finite D hQF) (fun y hy hyv => by
      rw [sub_self] at hy
      exact wall_cover_param D hng hQF hnQ hnF hTpos hint0 hwall0 hy hyv)
  rcases hεhi.lt_or_eq with hεhi | hεhi
  · -- `R` is inside a side-2 edge: a link.
    left
    refine ⟨R, g, c, ⟨hQR, hg, hQ, hRc, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro y hy
      rw [hOS] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨e, he, -, -, -, hxe⟩ := hTgood.2 x ⟨hx.1.le, hx.2.le⟩
      exact ⟨e, he, (mem₁ e he x).mpr hxe⟩
    · intro e he hmeet
      obtain ⟨y, hye, hyo⟩ := hmeet
      rw [hOS] at hyo
      obtain ⟨x, hx, rfl⟩ := hyo
      obtain ⟨hθ, hlo, hhi⟩ := inner₁ e he x hx ((mem₁ e he x).mp hye)
      refine ⟨?_, hθ⟩
      rw [edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2, hSeg]
      exact Set.image_mono fun z hz => ⟨hlo.trans hz.1, hz.2.trans hhi⟩
    · intro e he _ hQe y hy hQy
      have hgy : g y = c := D.lineChain_edge_subset he y hy
      obtain ⟨s, rfl⟩ : ∃ s, AffineMap.lineMap Q F s = y :=
        ⟨_, eq_lineMap_lineParam hg hQF hQ hF hgy⟩
      have hs : s < 0 := by
        have hQy' : AffineMap.lineMap Q F (0 : ℝ) ∈
            openSegment ℝ (AffineMap.lineMap Q F s) (AffineMap.lineMap Q F T) := by
          rw [hQ0]; exact hQy
        have h0 := (lineMap_mem_openSegment_params hQF (a := s) (b := T) (t := 0)).mp hQy'
        rcases lt_trichotomy s T with h | h | h
        · rw [openSegment_eq_Ioo h] at h0; exact h0.1
        · rw [h, openSegment_same] at h0; exact absurd (Set.mem_singleton_iff.mp h0) hTpos.ne
        · rw [openSegment_symm, openSegment_eq_Ioo h] at h0; linarith [h0.1]
      refine hback e hQe _ hy ?_
      have := (lineMap_mem_openSegment_params hQF (a := s) (b := 1) (t := 0)).mpr
        (by rw [openSegment_eq_Ioo (hs.trans one_pos)]; exact ⟨hs, one_pos⟩)
      rwa [hQ0, AffineMap.lineMap_apply_one] at this
    · -- Past `R` on side 1.
      have hRint : R ∈ interior D.target.carrier := by
        obtain ⟨b1, b2⟩ := lineChain_ends D hε
        have hRε := (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 T).mpr ⟨hεlo, hεhi⟩
        exact interior_of_vertex_openSegment D hkR hRε
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior R hRint
      have hdQF : 0 < dist Q F := dist_pos.mpr hQF
      set δ₁ := min (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F) / 2 with hδ₁def
      have hδ₁ : 0 < δ₁ := by
        have : 0 < min (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F) :=
          lt_min (by linarith) (div_pos hr hdQF)
        simp only [δ₁]; linarith
      have hδ₁ε : T + δ₁ < edgeHi Q F (D.tile ε.1) ε.2 := by
        have := min_le_left (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F)
        simp only [δ₁]; linarith
      have hδ₁r : δ₁ * dist Q F < r := by
        have h := min_le_right (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F)
        have : δ₁ < r / dist Q F := by simp only [δ₁]; linarith [div_pos hr hdQF]
        calc δ₁ * dist Q F < r / dist Q F * dist Q F := mul_lt_mul_of_pos_right this hdQF
          _ = r := div_mul_cancel₀ r hdQF.ne'
      have hint' : openSegment ℝ (AffineMap.lineMap Q F T) (AffineMap.lineMap Q F (T + δ₁))
          ⊆ interior D.target.carrier := by
        rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
        rintro _ ⟨s, hs, rfl⟩
        apply hball
        rw [Metric.mem_ball, hRdef, dist_lineMap_lineMap, Real.dist_eq, abs_of_pos (by linarith [hs.1])]
        calc (s - T) * dist Q F < δ₁ * dist Q F :=
              mul_lt_mul_of_pos_right (by linarith [hs.2]) hdQF
          _ < r := hδ₁r
      have hwall' : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F T)
          (AffineMap.lineMap Q F (T + δ₁)), ∀ i, y ∉ interior (D.tile i).carrier := by
        rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
        rintro _ ⟨s, hs, rfl⟩
        exact D.edge_point_not_interior ((mem₂ ε hε s).mpr
          ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_right (D.lineChain g c)
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) T
        hδ₁ (vertex_params_finite D hQF)
        (fun y hy hyv => wall_cover_param D hg hQF hQ hF (by linarith) hint' hwall' hy hyv)
      have hθ' : ¬ isθ e' := by
        intro hθ'
        rcases hlo'.lt_or_eq with hlt | heq
        · set m := max (edgeLo Q F (D.tile e'.1) e'.2) 0
          have hm : m < T := max_lt hlt hTpos
          have := (inner₁ e' he' ((m + T) / 2)
            ⟨by linarith [le_max_right (edgeLo Q F (D.tile e'.1) e'.2) 0], by linarith⟩
            ⟨by linarith [le_max_left (edgeLo Q F (D.tile e'.1) e'.2) 0], by linarith⟩).2.2
          linarith
        · have hgood : Good (edgeHi Q F (D.tile e'.1) e'.2) := by
            refine ⟨hTpos.trans hhi', fun x hx => ?_⟩
            rcases le_or_gt x T with hxT | hxT
            · obtain ⟨e, he, hθ, h0, hT', hxe⟩ := hTgood.2 x ⟨hx.1, hxT⟩
              exact ⟨e, he, hθ, h0, hT'.trans hhi'.le, hxe⟩
            · exact ⟨e', he', hθ', by rw [heq]; exact hTpos.le, le_rfl,
                ⟨by rw [heq]; exact hxT.le, hx.2⟩⟩
          have := hmax _ hgood (Finset.mem_image.mpr ⟨e', he', rfl⟩)
          linarith
      refine ⟨e', he', hθ', (mem₁ e' he' T).mpr ⟨hlo', hhi'.le⟩,
        AffineMap.lineMap Q F (edgeHi Q F (D.tile e'.1) e'.2),
        (mem₁ e' he' _).mpr ⟨(hlo'.trans hhi'.le), le_rfl⟩, ?_⟩
      have := (lineMap_mem_openSegment_params hQF (a := 0)
        (b := edgeHi Q F (D.tile e'.1) e'.2) (t := T)).mpr
        (by rw [openSegment_eq_Ioo (hTpos.trans hhi')]; exact ⟨hTpos, hhi'⟩)
      rwa [hQ0] at this
    · obtain ⟨b1, b2⟩ := lineChain_ends D hε
      exact ⟨ε, hε, (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 T).mpr ⟨hεlo, hεhi⟩⟩
  · -- `R` is a vertex on side 2: a relation.
    right
    have inner₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ x ∈ Ioo 0 T,
        x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
          0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T := by
      intro e he x hx hxe
      constructor
      · by_contra hlo
        push Not at hlo
        have := back e (mem₂ e he) hlo
        linarith [hxe.2, hx.1]
      · by_contra hhi
        push Not at hhi
        have := ov₂ e he ε hε (lt_of_lt_of_le
          (max_lt (lt_of_le_of_lt hxe.1 hx.2) hεlo) (le_min hhi.le hεhi.le))
        rw [this] at hhi
        linarith
    have hin₁ : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
        x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
          0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T :=
      fun e he x hx hxe => (inner₁ e he x hx hxe).2
    have sum₁ := wall_sum_param D hg hQF hQ hF hTpos hint hwall hin₁
    have sum₂ := wall_sum_param D hng hQF hnQ hnF hTpos hint hwall inner₂
    refine ⟨_, _, ?_, ⟨e₂, ?_, hθ₂⟩, sum₁.trans sum₂.symm⟩
    · intro e he
      obtain ⟨he, hsub⟩ := Finset.mem_filter.mp he
      rw [edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2,
        ← hRdef, hSeg, Set.image_subset_image_iff (AffineMap.lineMap_injective ℝ hQF)] at hsub
      have hlt := lt₁ e he
      have hlo := (hsub ⟨le_rfl, hlt.le⟩).1
      have hhi := (hsub ⟨hlt.le, le_rfl⟩).2
      exact (inner₁ e he ((edgeLo Q F (D.tile e.1) e.2 + edgeHi Q F (D.tile e.1) e.2) / 2)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).1
    · refine Finset.mem_filter.mpr ⟨h2, ?_⟩
      have := (inner₂ e₂ h2 (min t₂ T / 2)
        ⟨by positivity, by linarith [min_le_right t₂ T]⟩
        (by rw [p₂lo, p₂hi]; exact ⟨by positivity, by linarith [min_le_left t₂ T]⟩)).2
      rw [p₂hi] at this
      rw [edge_eq_image hng hQF hnQ hnF _ _ (lineChain_ends D h2).1 (lineChain_ends D h2).2,
        ← hRdef, hSeg, p₂lo, p₂hi]
      exact Set.image_mono fun z hz => ⟨hz.1, hz.2.trans this⟩

end TriangleTiling
