/-
"The number of tiles on a side of ABC", from Section 10 of M. Beeson,
*Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:N/4helper` is `N_div_4_helper` (a Lean name cannot
contain `/`). The paper's rewrite of October 2026 removed this lemma, with the subsection that
used it; it is kept here, and nothing
else uses it. This file proves it for a tile with integer sides, as `N_div_4_helper_int`;
`TriangleTiling.Isosceles.Scaling` gives the general form.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2` and opposite sides
`a, b, c`.
-/
import TriangleTiling.Isosceles.NotSquarefree
import TriangleTiling.Tiling.Restrict
import Erdos634.BaseSelection

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- The frontier of a triangle lies on its edges. -/
theorem tri_frontier_subset_edges (T : Tri) {x : Plane} (hx : x ∈ frontier T.carrier) :
    ∃ k, x ∈ T.edge k := by
  let D₁ : Dissection 1 :=
    { target := T, tile := fun _ => T, covers := Set.iUnion_const _,
      interiors_disjoint := fun i j h => absurd (Subsingleton.elim i j) h }
  obtain ⟨_, k, hk⟩ := Erdos634.BaseSelection.frontier_subset_edges D₁ hx
  exact ⟨k, hk⟩

/-- The frontier of a triangle lies on its three sides. -/
theorem tri_frontier_subset_sides (T : Tri) {x : Plane} (hx : x ∈ frontier T.carrier) :
    x ∈ segment ℝ (T.pts 0) (T.pts 1) ∨ x ∈ segment ℝ (T.pts 1) (T.pts 2) ∨
      x ∈ segment ℝ (T.pts 2) (T.pts 0) := by
  obtain ⟨k, hk⟩ := tri_frontier_subset_edges T hx
  rw [Tri.edge] at hk
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr hk)

/-- An end `x` of a segment `[x, y]` that lies on a sub-segment `[u, v]` is `u` or `v`. -/
theorem eq_endpoint_of_mem_segment {x y u v : Plane} (hu : u ∈ segment ℝ x y)
    (hv : v ∈ segment ℝ x y) (hx : x ∈ segment ℝ u v) : x = u ∨ x = v := by
  by_cases hxy : x = y
  · subst hxy
    rw [segment_same] at hu
    exact Or.inl hu.symm
  have hL := AffineMap.lineMap_injective ℝ hxy
  rw [segment_eq_image_lineMap] at hu hv
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [← image_segment, segment_eq_Icc'] at hx
  obtain ⟨r, hr, hrx⟩ := hx
  have hr0 : r = 0 := hL (hrx.trans (AffineMap.lineMap_apply_zero x y).symm)
  subst hr0
  rcases le_total s t with h | h
  · left
    have h0 : s = 0 := le_antisymm (by have := hr.1; rwa [min_eq_left h] at this) hs.1
    rw [h0, AffineMap.lineMap_apply_zero]
  · right
    have h0 : t = 0 := le_antisymm (by have := hr.1; rwa [min_eq_right h] at this) ht.1
    rw [h0, AffineMap.lineMap_apply_zero]

/-- The angle sum at a point, by angle type: `n₀ α + n₁ β + n₂ γ + n₃ π + n₄ (2π)`. -/
theorem sum_localAngle_counts {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (P : Plane) :
    ∑ i, (D.tile i).localAngle P =
      (angleCount D P (tileα D) : ℝ) * tileα D + (angleCount D P (tileβ D) : ℝ) * tileβ D
      + (angleCount D P (tileγ D) : ℝ) * tileγ D + (angleCount D P Real.pi : ℝ) * Real.pi
      + (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) := by
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj hf
  rw [Fin.sum_univ_five] at hcount
  exact hcount

/-- A positive length cannot be a sum of at least two positive lengths that includes itself. -/
theorem self_sum_contra (v w z p q r : ℕ) (hv : 0 < v) (hw : 0 < w) (hz : 0 < z)
    (h2 : 2 ≤ p + q + r) (hn : v = p * v + q * w + r * z) (hp : 1 ≤ p) : False := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have h : p' * v + q * w + r * z = 0 := by
    apply Nat.add_left_cancel (n := v)
    calc v + (p' * v + q * w + r * z) = (p' + 1) * v + q * w + r * z := by ring
      _ = v := hn.symm
      _ = v + 0 := rfl
  simp only [Nat.add_eq_zero_iff, mul_eq_zero] at h
  omega

/-- **Lemma `lemma:N/4helper`, for a tile with integer sides.** Let the isosceles triangle `ABC` with base angles `α` (at `A`
and `C`) be `N`-tiled by a tile with angles `(α, β, 2α)`, `α` not a rational multiple of `π`,
with integer sides `(a, b, c)` without common factor. Then no tile has one vertex in the
interior of `AB` and another in the interior of `BC`.

The paper also assumes the tile is not a right triangle (not used), and gets integer sides from
`theorem:rationaltile` (the integer case is the one its proof treats). The proof: if a tile has
an edge `EF` with `E` inside `AB` and `F` inside `BC`, the tiles inside the triangle `BEF` tile it
(its sides lie on `AB`, `BC` and a tile edge). Its angle at `B` is that of `ABC`, so its angles
at `E` and `F` add up to `2α`; as `α ∉ ℚπ`, each is a single tile's `α`. So `EF` is not one edge
of a tile inside `BEF` (that tile would have two `α` angles); it is at least two edges, whose
lengths add up to the length of `EF`, one of `a, b, c`, contradicting `lemma:edgerelations`. -/
theorem N_div_4_helper_int {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (j : Fin N) (k k' : Fin 3) (hkk : k ≠ k')
    (hE : (D.tile j).pts k ∈ openSegment ℝ (D.target.pts 0) (D.target.pts 1))
    (hF : (D.tile j).pts k' ∈ openSegment ℝ (D.target.pts 1) (D.target.pts 2)) : False := by
  classical
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  set A := D.target.pts 0 with hAdef
  set B := D.target.pts 1 with hBdef
  set C := D.target.pts 2 with hCdef
  set E := (D.tile j).pts k with hEdef
  set F := (D.tile j).pts k' with hFdef
  set α := tileα D with hαdef
  have hpi := Real.pi_pos
  -- `0 < α < π/3`.
  have hα0 : 0 < α := by
    rcases (angle_nonneg (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [hαdef, tileα, ← h]; simp⟩ hirr
  have hβ0 : 0 < tileβ D := by
    rcases (angle_nonneg (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : tileβ D = 0 := h.symm
      rw [hβ] at this
      exact hirr ⟨1 / 3, by push_cast; linarith⟩
  rw [hβ] at hβ0
  have hAB : A ≠ B := D.target.indep.injective.ne (by decide)
  have hBC : B ≠ C := D.target.indep.injective.ne (by decide)
  have hEseg : E ∈ segment ℝ A B := openSegment_subset_segment _ _ _ hE
  have hFseg : F ∈ segment ℝ B C := openSegment_subset_segment _ _ _ hF
  have hEB : E ≠ B := fun h => hAB (right_mem_openSegment_iff.mp (h ▸ hE))
  have hFB : F ≠ B := fun h => hBC (left_mem_openSegment_iff.mp (h ▸ hF))
  have hEF : E ≠ F := (D.tile j).indep.injective.ne hkk
  -- The angle of `ABC` at `B` is `π - 2α`, and so is `∠EBF`.
  have hTsum := cornerAngle_sum D.target
  have eA' : cornerAngle B A C = α := hA
  have eC : cornerAngle A C B = α := by rw [cornerAngle, angle_comm]; exact hC
  have hABC : ∠ A B C = Real.pi - 2 * α := by
    have : cornerAngle C B A = Real.pi - 2 * α := by
      have h1 : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2)
        + cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0)
        + cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = Real.pi := hTsum
      have h2 : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = α := hA
      have h3 : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = α := eC
      show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
      linarith
    rw [cornerAngle, angle_comm] at this; exact this
  have hEBF : ∠ E B F = Real.pi - 2 * α := by
    rw [(mem_segment_iff_wbtw.mp hEseg).symm.angle_eq_left _ hEB,
      (mem_segment_iff_wbtw.mp hFseg).angle_eq_right _ hFB, hABC]
  -- The triangle `BEF`.
  have hcol : ¬ Collinear ℝ ({E, B, F} : Set Plane) := by
    rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
    push Not
    refine ⟨hEB, hFB, ?_, ?_⟩ <;> rw [hEBF] <;> intro h <;> linarith
  have hind : AffineIndependent ℝ ![B, E, F] := by
    rw [affineIndependent_iff_not_collinear_set, Set.insert_comm]; exact hcol
  let T' : Tri := ⟨![B, E, F], hind⟩
  have hT0 : T'.pts 0 = B := rfl
  have hT1 : T'.pts 1 = E := rfl
  have hT2 : T'.pts 2 = F := rfl
  have hsub : T'.carrier ⊆ D.target.carrier := by
    apply convexHull_min _ D.target.convex
    rintro _ ⟨i, rfl⟩
    have hAc : A ∈ D.target.carrier := subset_convexHull ℝ _ ⟨0, rfl⟩
    have hBc : B ∈ D.target.carrier := subset_convexHull ℝ _ ⟨1, rfl⟩
    have hCc : C ∈ D.target.carrier := subset_convexHull ℝ _ ⟨2, rfl⟩
    fin_cases i
    · exact hBc
    · exact D.target.convex.segment_subset hAc hBc hEseg
    · exact D.target.convex.segment_subset hBc hCc hFseg
  -- Its frontier meets no tile's interior.
  have hfrT : ∀ y ∈ frontier D.target.carrier, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i hyi
    have hint : interior (D.tile i).carrier ⊆ interior D.target.carrier :=
      interior_mono fun z hz => by rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨i, hz⟩
    exact hy.2 (hint hyi)
  have hwall : ∀ y ∈ frontier T'.carrier, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rcases tri_frontier_subset_sides T' hy with hm | hm | hm
    · -- `BE` lies on `AB`.
      have hm' : y ∈ segment ℝ B E := hm
      have hy' : y ∈ segment ℝ A B :=
        (convex_segment (𝕜 := ℝ) A B).segment_subset (right_mem_segment _ _ _) hEseg hm'
      exact hfrT y (tri_side_subset_frontier D.target 0 hy')
    · -- `EF` is an edge of tile `j`.
      have hm' : y ∈ segment ℝ E F := hm
      rcases fin3_cases k' k hkk.symm with h | h
      · have : y ∈ (D.tile j).edge k := by rw [Tri.edge, ← h]; exact hm'
        exact D.toDissection.edge_point_not_interior this
      · have hk : k = k' + 1 := by rw [h]; fin_cases k <;> rfl
        have : y ∈ (D.tile j).edge k' := by
          rw [Tri.edge, ← hk, segment_symm]; exact hm'
        exact D.toDissection.edge_point_not_interior this
    · -- `FB` lies on `BC`.
      have hm' : y ∈ segment ℝ F B := hm
      have hy' : y ∈ segment ℝ B C :=
        (convex_segment (𝕜 := ℝ) B C).segment_subset hFseg (left_mem_segment _ _ _) hm'
      exact hfrT y (tri_side_subset_frontier D.target 1 hy')
  -- The tiling of `BEF`.
  obtain ⟨M, D', hDmodel, hDtarget⟩ : ∃ (M : ℕ) (D' : CongruentDissection M),
      D'.model = D.model ∧ D'.target = T' :=
    ⟨_, CongruentDissection.restrict D T' hsub hwall, rfl, rfl⟩
  have hαα : tileα D' = α := by simp only [tileα, hDmodel]; rfl
  have hββ : tileβ D' = tileβ D := by simp only [tileβ, hDmodel]
  have hγγ : tileγ D' = tileγ D := by simp only [tileγ, hDmodel]
  have hγ' : tileγ D' = 2 * tileα D' := by rw [hγγ, hαα]; exact hγ
  have hirr' : ¬ ∃ r : ℚ, tileα D' = (r : ℝ) * Real.pi := by rw [hαα]; exact hirr
  -- Its angles at `E` and `F` add up to `2α` and are positive.
  have hsumT' := cornerAngle_sum T'
  have hE' : T'.localAngle E = ∠ F E B := by rw [← hT1, Tri.localAngle_vertex]; rfl
  have hF' : T'.localAngle F = ∠ B F E := by rw [← hT2, Tri.localAngle_vertex]; rfl
  have hangles : ∠ F E B + ∠ B F E = 2 * α := by
    have h1 : cornerAngle E B F + cornerAngle F E B + cornerAngle B F E = Real.pi := hsumT'
    rw [cornerAngle] at h1
    rw [hEBF] at h1
    simp only [cornerAngle] at h1
    linarith
  have hposE : 0 < ∠ F E B := angle_pos_of_not_collinear (by
    intro h; apply hcol
    have : ({F, E, B} : Set Plane) = {E, B, F} := by ext; simp; tauto
    rwa [this] at h)
  have hposF : 0 < ∠ B F E := angle_pos_of_not_collinear (by
    intro h; apply hcol
    have : ({B, F, E} : Set Plane) = {E, B, F} := by ext; simp; tauto
    rwa [this] at h)
  have hcE := sum_localAngle_counts D' hγ' hirr' E
  have hcF := sum_localAngle_counts D' hγ' hirr' F
  rw [D'.toDissection.sum_localAngle_eq E] at hcE
  rw [D'.toDissection.sum_localAngle_eq F] at hcF
  have htE : D'.target.localAngle E = ∠ F E B := by rw [hDtarget]; exact hE'
  have htF : D'.target.localAngle F = ∠ B F E := by rw [hDtarget]; exact hF'
  rw [htE] at hcE
  rw [htF] at hcF
  have hβ' : tileβ D' = Real.pi - 3 * tileα D' := by rw [hββ, hαα]; exact hβ
  -- Counting: at `E` and at `F` exactly one tile of `BEF`, with its `α`.
  set e0 := angleCount D' E (tileα D'); set e1 := angleCount D' E (tileβ D')
  set e2 := angleCount D' E (tileγ D'); set e3 := angleCount D' E Real.pi
  set e4 := angleCount D' E (2 * Real.pi)
  set f0 := angleCount D' F (tileα D'); set f1 := angleCount D' F (tileβ D')
  set f2 := angleCount D' F (tileγ D'); set f3 := angleCount D' F Real.pi
  set f4 := angleCount D' F (2 * Real.pi)
  rw [hβ', hγ', hαα] at hcE hcF
  have key : ((((e0 : ℤ) + f0 - 3 * (e1 + f1) + 2 * (e2 + f2) - 2) : ℤ) : ℝ) * α
      + ((((e1 : ℤ) + f1 + e3 + f3 + 2 * (e4 + f4)) : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linear_combination -hcE - hcF + hangles
  obtain ⟨hk1, hk2⟩ := angle_indep hirr _ _ key
  have he1 : e1 = 0 := by omega
  have he3 : e3 = 0 := by omega
  have he4 : e4 = 0 := by omega
  have hf1 : f1 = 0 := by omega
  have hf3 : f3 = 0 := by omega
  have hf4 : f4 = 0 := by omega
  have hEexp : ∠ F E B = ((e0 : ℝ) + 2 * e2) * α := by
    rw [hcE, he1, he3, he4]; push_cast; ring
  have hFexp : ∠ B F E = ((f0 : ℝ) + 2 * f2) * α := by
    rw [hcF, hf1, hf3, hf4]; push_cast; ring
  have hE0 : 0 < e0 + 2 * e2 := by
    have h' := hposE
    rw [hEexp] at h'
    have : (0 : ℝ) < e0 + 2 * e2 := pos_of_mul_pos_left h' hα0.le
    exact_mod_cast this
  have hF0 : 0 < f0 + 2 * f2 := by
    have h' := hposF
    rw [hFexp] at h'
    have : (0 : ℝ) < f0 + 2 * f2 := pos_of_mul_pos_left h' hα0.le
    exact_mod_cast this
  have he2 : e2 = 0 := by omega
  have hf2 : f2 = 0 := by omega
  -- So a tile of `BEF` with a vertex at `E` (or `F`) has its `α` there.
  have none : ∀ (P : Plane) (θ : ℝ), angleCount D' P θ = 0 →
      ∀ i, (D'.tile i).localAngle P ≠ θ := by
    intro P θ h i hi
    have : i ∈ Finset.univ.filter fun i => (D'.tile i).localAngle P = θ := by simp [hi]
    rw [angleCount, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  have hvertα : ∀ (P : Plane) (i : Fin M) (m : Fin 3),
      (D'.tile i).pts m = P → angleCount D' P (tileβ D') = 0 →
        angleCount D' P (tileγ D') = 0 →
          cornerAngle ((D'.tile i).pts (m + 1)) ((D'.tile i).pts m) ((D'.tile i).pts (m + 2))
            = tileα D' := by
    intro P i m hm h1 h2
    have hmem := localAngle_at_own_vertex_mem' D' i m
    rw [Tri.localAngle_vertex] at hmem
    rcases hmem with h | h | h
    · exact h
    · exact absurd (by rw [← Tri.localAngle_vertex, hm] at h; exact h) (none P _ h1 i)
    · exact absurd (by rw [← Tri.localAngle_vertex, hm] at h; exact h) (none P _ h2 i)
  -- The side `EF` of `BEF` as a chain of tile edges.
  obtain ⟨part, hcov, hdisj, hsum⟩ := D'.toDissection.side_walk 1
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h12] at hcov hsum
  have hcov' : (⋃ e ∈ part, (D'.tile e.1).edge e.2) = segment ℝ E F := by
    rw [← hT1, ← hT2, ← hDtarget]; exact hcov
  have hsum' : ∑ e ∈ part, dist ((D'.tile e.1).pts e.2) ((D'.tile e.1).pts (e.2 + 1))
      = dist E F := by
    rw [← hT1, ← hT2, ← hDtarget]; exact hsum
  -- `EF` is not a single edge: that tile would have its `α` at both `E` and `F`.
  have hcard2 : 2 ≤ part.card := by
    by_contra hlt
    push Not at hlt
    have hne : part.Nonempty := by
      by_contra h0
      rw [Finset.not_nonempty_iff_eq_empty] at h0
      rw [h0, Finset.sum_empty] at hsum'
      exact hEF (dist_le_zero.mp hsum'.symm.le)
    have hc1 : part.card = 1 := by have := Finset.card_pos.mpr hne; omega
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc1
    rw [he] at hcov'
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left] at hcov'
    set t := D'.tile e.1
    have hu : t.pts e.2 ∈ segment ℝ E F := hcov' ▸ left_mem_segment ℝ _ _
    have hv : t.pts (e.2 + 1) ∈ segment ℝ E F := hcov' ▸ right_mem_segment ℝ _ _
    have hEe : E ∈ segment ℝ (t.pts e.2) (t.pts (e.2 + 1)) := by
      have : E ∈ t.edge e.2 := hcov' ▸ left_mem_segment ℝ E F
      exact this
    have hFe : F ∈ segment ℝ (t.pts e.2) (t.pts (e.2 + 1)) := by
      have : F ∈ t.edge e.2 := hcov' ▸ right_mem_segment ℝ E F
      exact this
    rw [segment_symm] at hu hv
    have hE2 := eq_endpoint_of_mem_segment (y := F)
      (by rw [segment_symm]; exact hu) (by rw [segment_symm]; exact hv) hEe
    have hF2 := eq_endpoint_of_mem_segment (y := E) hu hv hFe
    -- The indices of `E` and `F` in `t`.
    obtain ⟨iE, hiE⟩ : ∃ i : Fin 3, t.pts i = E := by
      rcases hE2 with h | h
      · exact ⟨e.2, h.symm⟩
      · exact ⟨e.2 + 1, h.symm⟩
    obtain ⟨iF, hiF⟩ : ∃ i : Fin 3, t.pts i = F := by
      rcases hF2 with h | h
      · exact ⟨e.2, h.symm⟩
      · exact ⟨e.2 + 1, h.symm⟩
    have hiEF : iE ≠ iF := fun h => hEF (hiE.symm.trans (h ▸ hiF))
    have haE := hvertα E e.1 iE hiE he1 he2
    have haF := hvertα F e.1 iF hiF hf1 hf2
    have hcnt := (tile_angle_count D' hγ' hirr' e.1).1
    have : 1 < (Finset.univ.filter fun m : Fin 3 => cornerAngle ((D'.tile e.1).pts (m + 1))
        ((D'.tile e.1).pts m) ((D'.tile e.1).pts (m + 2)) = tileα D').card :=
      Finset.one_lt_card.mpr ⟨iE, by simp [haE], iF, by simp [haF], hiEF⟩
    omega
  -- The edge lengths: `|EF| = p a + q b + r c` with `p + q + r ≥ 2`, and `|EF|` is `a`, `b`
  -- or `c`.
  have hw := side_walk_counts D' hγ' hirr' part (dist E F) hsum'
  have ha' : dist (D'.model.pts 1) (D'.model.pts 2) = a := by rw [hDmodel]; exact ha
  have hb' : dist (D'.model.pts 2) (D'.model.pts 0) = b := by rw [hDmodel]; exact hb
  have hc' : dist (D'.model.pts 0) (D'.model.pts 1) = c := by rw [hDmodel]; exact hc
  rw [ha', hb', hc'] at hw
  set p := (part.filter fun e => (D'.tile e.1).localAngle ((D'.tile e.1).pts (e.2 + 2))
    = tileα D').card
  set q := (part.filter fun e => (D'.tile e.1).localAngle ((D'.tile e.1).pts (e.2 + 2))
    = tileβ D').card
  set r := (part.filter fun e => (D'.tile e.1).localAngle ((D'.tile e.1).pts (e.2 + 2))
    = tileγ D').card
  have hpqr : part.card = p + q + r := by
    obtain ⟨-, -, hinj'⟩ := angle_values D' hγ' hirr'
    have ne : ∀ x y : Fin 5, x ≠ y →
        ![tileα D', tileβ D', tileγ D', Real.pi, 2 * Real.pi] x ≠
          ![tileα D', tileβ D', tileγ D', Real.pi, 2 * Real.pi] y := fun x y h => hinj'.ne h
    have hαβ : tileα D' ≠ tileβ D' := ne 0 1 (by decide)
    have hαγ : tileα D' ≠ tileγ D' := ne 0 2 (by decide)
    have hβγ : tileβ D' ≠ tileγ D' := ne 1 2 (by decide)
    have hpt : ∀ e ∈ part, (1 : ℕ) =
        (if (D'.tile e.1).localAngle ((D'.tile e.1).pts (e.2 + 2)) = tileα D' then 1 else 0)
        + (if (D'.tile e.1).localAngle ((D'.tile e.1).pts (e.2 + 2)) = tileβ D' then 1 else 0)
        + (if (D'.tile e.1).localAngle ((D'.tile e.1).pts (e.2 + 2)) = tileγ D' then 1 else 0) := by
      intro e _
      rcases localAngle_at_own_vertex_mem' D' e.1 (e.2 + 2) with h | h | h
      · rw [if_pos h, if_neg (h ▸ hαβ), if_neg (h ▸ hαγ)]
      · rw [if_neg (h ▸ hαβ.symm), if_pos h, if_neg (h ▸ hβγ)]
      · rw [if_neg (h ▸ hαγ.symm), if_neg (h ▸ hβγ.symm), if_pos h]
    rw [Finset.card_eq_sum_ones, Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter]
  have hlam : dist E F = a ∨ dist E F = b ∨ dist E F = c := by
    rcases fin3_cases k' k hkk.symm with h | h
    · have := edge_len_mem D j k
      rw [← h, ha, hb, hc] at this
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · have hk : k = k' + 1 := by rw [h]; fin_cases k <;> rfl
      have := edge_len_mem D j k'
      rw [← hk, ha, hb, hc, dist_comm] at this
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  clear_value p q r
  -- The tile in ℕ: `lemma:edgerelations` applies.
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  have m1' : a < b + c := by exact_mod_cast m1
  have m2' : b < c + a := by exact_mod_cast m2
  have m3' : c < a + b := by exact_mod_cast m3
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega
  obtain ⟨er1, er2, er3⟩ := edgerelations a b c ha0 hb0 (by omega) hcab hcop
  have h2 : 2 ≤ p + q + r := hpqr ▸ hcard2
  rcases hlam with h | h | h
  · have hn : a = p * a + q * b + r * c := by
      have hw' : (a : ℝ) = p * a + q * b + r * c := h ▸ hw
      exact_mod_cast hw'
    rcases Nat.eq_zero_or_pos p with hp | hp
    · rw [hp] at hn; exact er3 ⟨q, r, by simpa using hn⟩
    · exact self_sum_contra a b c p q r ha0 hb0 hc0 h2 hn hp
  · have hn : b = p * a + q * b + r * c := by
      have hw' : (b : ℝ) = p * a + q * b + r * c := h ▸ hw
      exact_mod_cast hw'
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq] at hn; exact er2 ⟨p, r, by linarith⟩
    · exact self_sum_contra b a c q p r hb0 ha0 hc0 (by omega) (hn.trans (by ring)) hq
  · have hn : c = p * a + q * b + r * c := by
      have hw' : (c : ℝ) = p * a + q * b + r * c := h ▸ hw
      exact_mod_cast hw'
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hr] at hn; exact er1 ⟨p, q, by simpa using hn⟩
    · exact self_sum_contra c a b r p q hc0 ha0 hb0 (by omega) (hn.trans (by ring)) hr

end TriangleTiling
