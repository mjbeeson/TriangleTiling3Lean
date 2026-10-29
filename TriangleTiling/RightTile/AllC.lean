/-
The graph `Γ_c` for a right-angled tile: `lemma:Gamma`, `lemma:propagation` and
`corollary:allc` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*).

Let the isosceles triangle `ABC` with base angles `β` (at `A` and `C`) be tiled by the tile
`(α, β, π/2)` with sides `(a, b, c)`, `α` not a rational multiple of `π`, and suppose there is no
relation `j c = u a + v b` with `j > 0`. Then either the base `AC` consists of `c` edges and the
equal sides carry none, or the equal sides consist of `c` edges and the base carries none.

The paper also treats the case where `α` is an odd multiple of `β`; here only `α ∉ ℚπ` is
formalized, which is the case `lemma:isosceleshelper3` uses.
-/
import TriangleTiling.RightTile.Counts
import TriangleTiling.Isosceles.GammaStart
import TriangleTiling.Isosceles.LengthRelations
import TriangleTiling.Isosceles.N4Helper

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Set

variable {N : ℕ} (D : CongruentDissection N)

/-- The tiling with the corners of the target relabelled by `σ`. -/
noncomputable def relabelTarget (σ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  target := ⟨D.target.pts ∘ σ, D.target.indep.comp_embedding σ.toEmbedding⟩
  tile := D.tile
  covers := by
    rw [D.covers]
    show convexHull ℝ (Set.range D.target.pts) = convexHull ℝ (Set.range (D.target.pts ∘ σ))
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ]
  interiors_disjoint := D.interiors_disjoint
  model := D.model
  tiles_congruent := D.tiles_congruent

theorem relabelTarget_carrier (σ : Equiv.Perm (Fin 3)) :
    (relabelTarget D σ).target.carrier = D.target.carrier := by
  show convexHull ℝ (Set.range (D.target.pts ∘ σ)) = convexHull ℝ (Set.range D.target.pts)
  rw [Set.range_comp, σ.range_eq_univ, Set.image_univ]

/-- Links of a relabelled tiling are links of the tiling. -/
theorem isLink_of_relabel (σ : Equiv.Perm (Fin 3)) {isθ : Fin N × Fin 3 → Prop} {Q R : Plane}
    (h : IsLink (relabelTarget D σ).toDissection isθ Q R) : IsLink D.toDissection isθ Q R := by
  obtain ⟨g, c, h⟩ := h
  exact ⟨g, c, ⟨h.ne, h.hg, h.hQ, h.hR, h.cov, h.inner, h.start, h.past, h.across⟩⟩

open Classical in
/-- The tile edges lying on side `i` of the target cover it. -/
theorem side_cover (i : Fin 3) :
    (⋃ e ∈ Finset.univ.filter fun e : Fin N × Fin 3 =>
        (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (D.tile e.1).edge e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk i
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    exact (Finset.mem_filter.mp he).2 hye
  · intro y hy
    rw [← hcov] at hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
      rw [← hcov]
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
    exact Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩, hye⟩

/-- Two sides of a triangle meet only at their common corner. -/
theorem sides_meet (T : Tri) (m : Fin 3) {x : Plane}
    (h1 : x ∈ segment ℝ (T.pts m) (T.pts (m + 1)))
    (h2 : x ∈ segment ℝ (T.pts (m + 2)) (T.pts (m + 2 + 1))) : x = T.pts m := by
  have c1 := T.coord_eq_zero_of_mem_edge m h1
  have c2 := T.coord_eq_zero_of_mem_edge (m + 2) h2
  have hsum := Tri.coord_sum T x
  rw [show m + 2 + 2 = m + 1 by fin_cases m <;> rfl] at c2
  apply T.basis.ext_elem
  intro j
  rw [Tri.coord_vertex]
  fin_cases m <;> fin_cases j <;> simp at c1 c2 hsum ⊢ <;> linarith

variable (hright : tileγ D = Real.pi / 2) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hright hirr

open Classical in
/-- **No side mixes `c` edges with others**, unless there is a relation. -/
theorem no_mixed_side (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) (i : Fin 3)
    {e e' : Fin N × Fin 3}
    (he : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (he' : (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (hθ : edgeType D (tileγ D) e) : edgeType D (tileγ D) e' := by
  by_contra hθ'
  set D' := relabelTarget D (Equiv.addRight i)
  have h0 : D'.target.pts 0 = D.target.pts i := by
    show D.target.pts (0 + i) = _; rw [zero_add]
  have h1 : D'.target.pts 1 = D.target.pts (i + 1) := by
    show D.target.pts (1 + i) = _; rw [add_comm]
  set part := Finset.univ.filter fun e : Fin N × Fin 3 =>
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1))
  have hcov : (⋃ e ∈ part, (D'.tile e.1).edge e.2) =
      segment ℝ (D'.target.pts 0) (D'.target.pts 1) := by
    rw [h0, h1]; exact side_cover D i
  have hgood : ∀ Q ∈ openSegment ℝ (D'.target.pts 0) (D'.target.pts 1),
      (∃ j k, (D'.tile j).pts k = Q) →
        (∀ j : Fin N, ∀ m : Fin 3,
          Q ∉ openSegment ℝ ((D'.tile j).pts m) ((D'.tile j).pts (m + 1)))
          ∧ Even ((edgesAt D'.toDissection Q).filter (edgeType D (tileγ D))).card := by
    intro Q hQ ⟨j, k, hjk⟩
    rw [h0, h1] at hQ
    have hfr : Q ∈ frontier D.target.carrier :=
      tri_side_subset_frontier D.target i (openSegment_subset_segment _ _ _ hQ)
    have hnc : Q ∉ Set.range D.target.pts := by
      rintro ⟨m, hm⟩
      exact Tri.vertex_not_mem_openSegment D.target m i (hm ▸ hQ)
    refine ⟨right_side_no_relint D hright hirr hfr hnc hjk, right_c_even D hright hirr (t := 2) ?_⟩
    rw [D.target.localAngle_frontier hfr hnc]; push_cast; ring
  obtain ⟨Q₀, hQ₀, R, hR⟩ := side_start D'.toDissection (edgeType D (tileγ D)) part hcov
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩)
    hθ hθ' hgood hnorel
  rw [relabelTarget_carrier] at hQ₀
  exact hnorel (relation_of_start D.toDissection _
    (fun _ _ _ _ hl => right_c_even D hright hirr (t := 4) (by
      rw [Tri.localAngle_interior _ hl.end_interior]; push_cast; ring))
    ⟨Q₀, hQ₀, R, isLink_of_relabel D _ hR⟩)

open Classical in
/-- **The tile at a corner with angle `β`.** At a corner of the target with angle `β` there is a
single tile; of its two edges along the two sides at the corner, exactly one is a `c` edge. -/
theorem corner_edges (m : Fin 3) (hm : D.target.localAngle (D.target.pts m) = tileβ D) :
    ∃ e e' : Fin N × Fin 3,
      (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts m) (D.target.pts (m + 1)) ∧
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts (m + 2)) (D.target.pts (m + 2 + 1)) ∧
      ((edgeType D (tileγ D) e ∧ ¬ edgeType D (tileγ D) e') ∨
        (¬ edgeType D (tileγ D) e ∧ edgeType D (tileγ D) e')) := by
  set A := D.target.pts m
  have hsep := anglesSep_right D hright hirr
  have hβ := right_beta D hright
  -- One tile has its `β` at `A`, and no tile has anything else there.
  have hloc : D.target.localAngle A = (-1 : ℤ) * tileα D + (1 : ℤ) * (Real.pi / 2) := by
    rw [hm, hβ]; push_cast; ring
  obtain ⟨h1, h2⟩ := vertex_relations_right D hright hirr A (-1) 1 hloc
  have hval : ∀ i, (D.tile i).localAngle A = tileβ D ∨ (D.tile i).localAngle A = 0 := by
    intro i
    rcases localAngle_mem D A i with h | h | h | h | h | h
    · exfalso; have := angleCount_pos D (show (D.tile i).localAngle A = tileα D from h); omega
    · exact Or.inl h
    · exfalso; have := angleCount_pos D (show (D.tile i).localAngle A = tileγ D from h); omega
    · exfalso; have := angleCount_pos D h; omega
    · exfalso; have := angleCount_pos D h; omega
    · exact Or.inr h
  have huniq : ∀ i i', (D.tile i).localAngle A = tileβ D → (D.tile i').localAngle A = tileβ D →
      i = i' := by
    intro i i' hi hi'
    have hle : angleCount D A (tileβ D) ≤ 1 := by omega
    exact Finset.card_le_one.mp hle i (by simp [hi]) i' (by simp [hi'])
  -- An edge of a side at `A` belongs to the tile with its `β` at `A`, and ends at `A`.
  have hat : ∀ (j : Fin 3) (y : Plane), (y = D.target.pts (j + 1) ∧ A = D.target.pts j) ∨
      (y = D.target.pts j ∧ A = D.target.pts (j + 1)) →
      ∃ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1))
        ∧ e ∈ edgesAt D.toDissection A ∧ (D.tile e.1).localAngle A = tileβ D := by
    intro j y hy
    have hA : A ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) := by
      rcases hy with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact left_mem_segment _ _ _
      · rw [h]; exact right_mem_segment _ _ _
    rw [← side_cover D j] at hA
    obtain ⟨e, he, hAe⟩ := Set.mem_iUnion₂.mp hA
    have hsub := (Finset.mem_filter.mp he).2
    refine ⟨e, hsub, ?_, ?_⟩
    · have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      rw [Tri.edge] at hAe
      rcases hy with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h] at hAe ⊢
        rcases eq_endpoint_of_mem_segment hu hv hAe with h' | h'
        · exact (mem_edgesAt _).mpr (Or.inl h'.symm)
        · exact (mem_edgesAt _).mpr (Or.inr h'.symm)
      · rw [segment_symm] at hu hv
        rw [h] at hAe ⊢
        rcases eq_endpoint_of_mem_segment hu hv hAe with h' | h'
        · exact (mem_edgesAt _).mpr (Or.inl h'.symm)
        · exact (mem_edgesAt _).mpr (Or.inr h'.symm)
    · rcases hval e.1 with h | h
      · exact h
      · exact absurd h (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _
          ((D.tile e.1).edge_subset_carrier e.2 hAe))
  obtain ⟨e, hes, heA, heβ⟩ := hat m (D.target.pts (m + 1)) (Or.inl ⟨rfl, rfl⟩)
  have hm2 : m + 2 + 1 = m := by fin_cases m <;> rfl
  obtain ⟨e', hes', heA', heβ'⟩ := hat (m + 2) (D.target.pts (m + 2))
    (Or.inr ⟨rfl, by rw [hm2]⟩)
  have hii : e'.1 = e.1 := huniq _ _ heβ' heβ
  refine ⟨e, e', hes, hes', ?_⟩
  -- The two edges are the two edges of that tile at `A`.
  obtain ⟨i, k⟩ := e
  obtain ⟨i', k'⟩ := e'
  simp only at hii
  rw [hii] at heA' hes' heβ' ⊢
  set T := D.tile i
  obtain ⟨k0, hk0⟩ : ∃ k0, T.pts k0 = A := by
    rcases (mem_edgesAt _).mp heA with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have hinj := T.indep.injective
  have hidx : ∀ j : Fin 3, (i, j) ∈ edgesAt D.toDissection A → j = k0 ∨ j = k0 + 2 := by
    intro j hj
    rcases (mem_edgesAt _).mp hj with h | h
    · exact Or.inl (hinj (h.trans hk0.symm))
    · right
      have := hinj (h.trans hk0.symm)
      rw [← this]; fin_cases j <;> rfl
  have hne : k ≠ k' := by
    rintro rfl
    have hF : T.pts (k + 1) ∈ segment ℝ (D.target.pts m) (D.target.pts (m + 1)) :=
      hes (right_mem_segment _ _ _)
    have hF' : T.pts (k + 1) ∈ segment ℝ (D.target.pts (m + 2)) (D.target.pts (m + 2 + 1)) :=
      hes' (right_mem_segment _ _ _)
    have hE : T.pts k ∈ segment ℝ (D.target.pts m) (D.target.pts (m + 1)) :=
      hes (left_mem_segment _ _ _)
    have hE' : T.pts k ∈ segment ℝ (D.target.pts (m + 2)) (D.target.pts (m + 2 + 1)) :=
      hes' (left_mem_segment _ _ _)
    exact tri_pts_succ_ne T k ((sides_meet D.target m hE hE').trans
      (sides_meet D.target m hF hF').symm)
  -- The corners other than `A` carry `α` and `π/2`, one each.
  have hcnt := (tile_angle_count_sep D hsep i).2.2
  simp only [← Tri.localAngle_vertex] at hcnt
  have h3 := card_three k0 (fun j => T.localAngle (T.pts j) = tileγ D)
  rw [hcnt] at h3
  have hk0γ : ¬ T.localAngle (T.pts k0) = tileγ D := by
    rw [hk0, heβ]
    have := hsep.2.ne (show (1 : Fin 5) ≠ 2 by decide)
    exact this
  rw [if_neg hk0γ] at h3
  have hk2 : k0 + 2 + 2 = k0 + 1 := by fin_cases k0 <;> rfl
  have ht : ∀ j, edgeType D (tileγ D) (i, j) ↔ T.localAngle (T.pts (j + 2)) = tileγ D :=
    fun j => Iff.rfl
  rcases hidx k heA with rfl | rfl <;> rcases hidx k' heA' with rfl | rfl
  · exact absurd rfl hne
  · rw [ht, ht, hk2]
    by_cases hc : T.localAngle (T.pts (k + 2)) = tileγ D
    · rw [if_pos hc] at h3
      have : ¬ T.localAngle (T.pts (k + 1)) = tileγ D := by
        intro h; rw [if_pos h] at h3; omega
      exact Or.inl ⟨hc, this⟩
    · rw [if_neg hc] at h3
      have : T.localAngle (T.pts (k + 1)) = tileγ D := by
        by_contra h; rw [if_neg h] at h3; omega
      exact Or.inr ⟨hc, this⟩
  · rw [ht, ht, hk2]
    by_cases hc : T.localAngle (T.pts (k' + 2)) = tileγ D
    · rw [if_pos hc] at h3
      have : ¬ T.localAngle (T.pts (k' + 1)) = tileγ D := by
        intro h; rw [if_pos h] at h3; omega
      exact Or.inr ⟨this, hc⟩
    · rw [if_neg hc] at h3
      have : T.localAngle (T.pts (k' + 1)) = tileγ D := by
        by_contra h; rw [if_neg h] at h3; omega
      exact Or.inl ⟨this, hc⟩
  · exact absurd rfl hne

open Classical in
/-- **Lemma `lemma:Gamma`.** At the end `R` of a link of `Γ_c`, some ray carries a `c` edge
together with an `a` or `b` edge: two adjacent tiles at `R` whose common boundary contains a `c`
edge of one and an `a` or `b` edge of the other. -/
theorem Gamma {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (h : LinkData D.toDissection (edgeType D (tileγ D)) Q R g c) :
    ∃ x ∈ edgesAt D.toDissection R, ∃ y ∈ edgesAt D.toDissection R,
      Partners D.toDissection R x y ∧ edgeType D (tileγ D) x ∧ ¬ edgeType D (tileγ D) y := by
  obtain ⟨e₀, he₀, hθ₀, hl₀, huniq⟩ := h.lonely_marked
  exact mixed_of_parity D.toDissection _ he₀ hθ₀ (fun e' he' h' => hl₀ e' he' h')
    (fun e he hθ hl => huniq e he hθ (fun e' he' h' => hl e' he' h'))
    (right_c_even D hright hirr (t := 4) (by
      rw [Tri.localAngle_interior _ h.end_interior]; push_cast; ring))

open Classical in
/-- **Lemma `lemma:propagation`.** Without a relation `j c = u a + v b`:
(i) every link of `Γ_c` is followed by another; (ii) at every vertex the in-degree and the
out-degree of `Γ_c` are equal and at most `1`. -/
theorem propagation (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) :
    (∀ Q R, IsLink D.toDissection (edgeType D (tileγ D)) Q R →
      ∃ R', IsLink D.toDissection (edgeType D (tileγ D)) R R') ∧
    ∀ v ∈ vertexFinset D.toDissection,
      ((vertexFinset D.toDissection).filter
          fun w => IsLink D.toDissection (edgeType D (tileγ D)) v w).card
        = ((vertexFinset D.toDissection).filter
          fun u => IsLink D.toDissection (edgeType D (tileγ D)) u v).card ∧
      ((vertexFinset D.toDissection).filter
          fun u => IsLink D.toDissection (edgeType D (tileγ D)) u v).card ≤ 1 := by
  set θ := edgeType D (tileγ D)
  set V := vertexFinset D.toDissection
  have hi : ∀ Q R, IsLink D.toDissection θ Q R → ∃ R', IsLink D.toDissection θ R R' := by
    rintro Q R ⟨g, c, hl⟩
    exact out_of_in D.toDissection θ hl (right_c_even D hright hirr (t := 4) (by
      rw [Tri.localAngle_interior _ hl.end_interior]; push_cast; ring)) hnorel
  refine ⟨hi, ?_⟩
  have hge : ∀ v ∈ V, (V.filter fun u => IsLink D.toDissection θ u v).card ≤
      (V.filter fun w => IsLink D.toDissection θ v w).card := by
    intro v _
    rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D.toDissection θ u v).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨R', hR'⟩ := hi u v (Finset.mem_filter.mp hu).2
      have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
        Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr
          ⟨(link_mem_vertexFinset D.toDissection θ hR').2, hR'⟩⟩
      linarith [in_le_one D.toDissection θ V v]
  have heq := (Finset.sum_eq_sum_iff_of_le hge).mp (sum_out_eq_sum_in D.toDissection θ V).symm
  exact fun v hv => ⟨(heq v hv).symm, in_le_one D.toDissection θ V v⟩

variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
include hA hC

/-- **Corollary `corollary:allc`.** Let the isosceles triangle `ABC` with base `AC` and base angles
`β` be tiled by the right-angled tile `(α, β, π/2)`, `α ∉ ℚπ`, with no relation `j c = u a + v b`
(`j > 0`). Then either `AC` consists of `c` edges and `AB`, `BC` carry none, or `AB` and `BC`
consist of `c` edges and `AC` carries none. -/
theorem allc (hnorel : ¬ ∃ j u v : ℕ, 0 < j ∧
      (j : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
        = u * dist (D.model.pts 1) (D.model.pts 2) + v * dist (D.model.pts 2) (D.model.pts 0)) :
    ((∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) →
        ¬ edgeType D (tileγ D) e) ∨
    ((∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        ¬ edgeType D (tileγ D) e) := by
  have hnorelE : ¬ HasRelation D.toDissection (edgeType D (tileγ D)) := fun h =>
    hnorel (c_relation_of_edges D (anglesSep_right D hright hirr) h)
  have mix := no_mixed_side D hright hirr hnorelE
  -- The sides, with the indices normalized.
  have m0 : ∀ {e e'}, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) →
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) →
        edgeType D (tileγ D) e → edgeType D (tileγ D) e' := fun he he' => mix 0 he he'
  have m1 : ∀ {e e'}, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) →
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) →
        edgeType D (tileγ D) e → edgeType D (tileγ D) e' := fun he he' => mix 1 he he'
  have m2 : ∀ {e e'}, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        edgeType D (tileγ D) e → edgeType D (tileγ D) e' := fun he he' => mix 2 he he'
  -- The corners `A` and `C`.
  have hmA : D.target.localAngle (D.target.pts 0) = tileβ D := by
    rw [Tri.localAngle_vertex]; exact hA
  have hmC : D.target.localAngle (D.target.pts 2) = tileβ D := by
    rw [Tri.localAngle_vertex]
    show ∠ (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    rw [angle_comm]; exact hC
  obtain ⟨e, e', he, he', hA'⟩ := corner_edges D hright hirr 0 hmA
  obtain ⟨f, f', hf, hf', hC'⟩ := corner_edges D hright hirr 2 hmC
  change (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) at he'
  change (D.tile f.1).edge f.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) at hf
  change (D.tile f'.1).edge f'.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) at hf'
  rcases hA' with ⟨hc, hnc⟩ | ⟨hnc, hc⟩
  · -- `AB` has a `c` edge, `AC` an `a` edge.
    have hAC : ∀ x, (D.tile x.1).edge x.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        ¬ edgeType D (tileγ D) x := fun x hx hcx => hnc (m2 hx he' hcx)
    rcases hC' with ⟨hc2, -⟩ | ⟨-, hc1⟩
    · exact absurd hc2 (hAC f hf)
    · right
      refine ⟨fun x hx => ?_, hAC⟩
      rcases hx with hx | hx
      · exact m0 he hx hc
      · exact m1 hf' hx hc1
  · -- `AC` has a `c` edge, `AB` an `a` edge.
    have hAB : ∀ x, (D.tile x.1).edge x.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) →
        ¬ edgeType D (tileγ D) x := fun x hx hcx => hnc (m0 hx he hcx)
    rcases hC' with ⟨-, hn1⟩ | ⟨hn2, -⟩
    · left
      refine ⟨fun x hx => m2 he' hx hc, fun x hx => ?_⟩
      rcases hx with hx | hx
      · exact hAB x hx
      · exact fun hcx => hn1 (m1 hx hf' hcx)
    · exact absurd (m2 he' hf hc) hn2

end TriangleTiling
