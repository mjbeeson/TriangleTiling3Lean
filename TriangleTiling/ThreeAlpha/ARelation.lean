/-
The `a`-relation in the triquadratic case (part of `theorem:arelation` of M. Beeson, *Triangle tiling:
the case 3α + 2β = π*, arXiv 1206.2229v4), with `α ∉ ℚπ` as a hypothesis.

As in the paper's proof (its opening paragraph and Case 4): the one tile at the `β` corner of `ABC`
has its `a` edge on a side of `ABC`; that side also carries a `c` edge (pigeonhole on the `γ`
angles); so a link of `Γ_a` starts on the boundary, which is impossible without an `a`-relation
(`lemma:apropagation`). The structure follows the isosceles paper's `lemma:crelation`
(`Gamma120/CRelation.lean`).

To use the isosceles files, whose names `tileα D`, `tileβ D`, `tileγ D` are the model's angles at
its vertices `0, 1, 2`, the model is relabelled so that these are `α`, `β`, `γ` (`relabelModel`);
the tiles, hence edges, links and relations, are unchanged.
-/
import TriangleTiling.ThreeAlpha.Gamma
import TriangleTiling.Isosceles.LengthRelations
import TriangleTiling.RightTile.Helper3
import TriangleTiling.RightTile.AllC
import TriangleTiling.Gamma120.CRelation
import Erdos634.MirrorGauge

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-- The tiling with the model's vertices relabelled by `τ`. -/
noncomputable def relabelModel (τ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  toDissection := D.toDissection
  model := ⟨D.model.pts ∘ τ, D.model.indep.comp_embedding τ.toEmbedding⟩
  tiles_congruent i := by
    obtain ⟨g, σ, hg⟩ := D.tiles_congruent i
    exact ⟨g, σ.trans τ.symm, fun k => by simp [hg]⟩

variable {α β a b c : ℝ}

/-- Each vertex `x` is followed by the other two, in one order or the other. -/
theorem others (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by
  revert x y z; decide

/-- After relabelling the model by the permutation of `ThreeAlphaData`, `tileα`, `tileβ`, `tileγ`
are `α`, `β`, `γ`, and the sides opposite them are `a`, `b`, `c`. -/
theorem relabel_facts (h : D.model.ThreeAlphaData α β a b c) :
    ∃ τ : Equiv.Perm (Fin 3), tileα (relabelModel D τ) = α ∧ tileβ (relabelModel D τ) = β ∧
      tileγ (relabelModel D τ) = 2 * α + β ∧
      dist ((relabelModel D τ).model.pts 1) ((relabelModel D τ).model.pts 2) = a ∧
      dist ((relabelModel D τ).model.pts 2) ((relabelModel D τ).model.pts 0) = b ∧
      dist ((relabelModel D τ).model.pts 0) ((relabelModel D τ).model.pts 1) = c := by
  obtain ⟨σ, h0, l0, h1, l1, h2, l2⟩ := h
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [tileα, tileβ, tileγ, relabelModel, Function.comp]
    have d01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have d02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
    have d12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  · rw [← h0]; unfold Tri.angleAt cornerAngle
    rcases others _ _ _ d01 d02 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact EuclideanGeometry.angle_comm _ _ _
  · rw [← h1]; unfold Tri.angleAt cornerAngle
    rcases others _ _ _ d12 d01.symm d02.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2]
    exact EuclideanGeometry.angle_comm _ _ _
  · rw [← h2]; unfold Tri.angleAt cornerAngle
    rcases others _ _ _ d02.symm d12.symm d01 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact EuclideanGeometry.angle_comm _ _ _
  · rw [← l0]; unfold Tri.oppLen
    rcases others _ _ _ d01 d02 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact dist_comm _ _
  · rw [← l1]; unfold Tri.oppLen
    rcases others _ _ _ d12 d01.symm d02.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2]
    exact dist_comm _ _
  · rw [← l2]; unfold Tri.oppLen
    rcases others _ _ _ d02.symm d12.symm d01 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact dist_comm _ _

section Relation

variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h

/-- **An edge relation for the `a` edges is an `a`-relation.** -/
theorem arel_of_edges (hr : HasRelation D.toDissection (edgeType D α)) : ARelation a b c := by
  obtain ⟨τ, t0, t1, t2, d0, d1, d2⟩ := relabel_facts D h
  set D' := relabelModel D τ
  have h' : D'.model.ThreeAlphaData α β a b c := ⟨1, t0, d0, t1, d1, t2, d2⟩
  have hsep := anglesSep D' hirr hrel h'
  have hr' : HasRelation D'.toDissection (edgeType D' (tileα D')) := by rw [t0]; exact hr
  obtain ⟨J, p, q, hJ, e⟩ := a_relation_of_edges D' hsep hr'
  rw [d0, d1, d2] at e
  exact ⟨J, p, q, hJ, e⟩

/-- **The counts at a point** with angle sum `t π`: `nα + 2nγ = 3(t - p)`, `nβ + nγ = 2(t - p)`,
`p = nπ + 2 n₂π`. -/
theorem counts_lin (P : Plane) (t : ℕ) (ht : D.target.localAngle P = t * Real.pi) :
    ((angleCount D P α : ℤ) + 2 * angleCount D P (2 * α + β)
        = 3 * (t - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) ∧
      ((angleCount D P β : ℤ) + angleCount D P (2 * α + β)
        = 2 * (t - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) := by
  have hs := counts_sum D hirr hrel h P
  rw [ht] at hs
  set nα := angleCount D P α
  set nβ := angleCount D P β
  set nγ := angleCount D P (2 * α + β)
  set nπ := angleCount D P Real.pi
  set n2 := angleCount D P (2 * Real.pi)
  have key := int_indep hirr hrel (x := nα + 2 * nγ - 3 * (t - (nπ + 2 * n2)))
    (y := nβ + nγ - 2 * (t - (nπ + 2 * n2)))
    (by push_cast; linear_combination hs + ((nπ : ℝ) + 2 * n2 - t) * hrel)
  omega

/-- A tile vertex at `P` gives an `α`, `β` or `γ` there. -/
theorem vertex_pos {P : Plane} {i : Fin N} {k : Fin 3} (hk : (D.tile i).pts k = P) :
    1 ≤ angleCount D P α + angleCount D P β + angleCount D P (2 * α + β) := by
  have := localAngle_pts (D.tile i) k
  rw [hk] at this
  rcases tile_angle_mem D h i k with e | e | e <;> rw [e] at this
  · have := angleCount_pos D this; omega
  · have := angleCount_pos D this; omega
  · have := angleCount_pos D this; omega

/-- At a point of `∂ABC` other than a corner, the angle sum is `π`. -/
theorem side_counts {P : Plane} (hP : P ∈ frontier D.target.carrier)
    (hnc : P ∉ Set.range D.target.pts) :
    ((angleCount D P α : ℤ) + 2 * angleCount D P (2 * α + β)
        = 3 * (1 - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) ∧
      ((angleCount D P β : ℤ) + angleCount D P (2 * α + β)
        = 2 * (1 - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) :=
  counts_lin D hirr hrel h P 1 (by rw [Tri.localAngle_frontier _ hP hnc]; push_cast; ring)

open Classical in
/-- At a tile vertex strictly inside a side, no tile has the point inside an edge, and exactly two
`a` edges end there. -/
theorem side_good3 (i : Fin 3) :
    ∀ Q ∈ openSegment ℝ (D.target.pts i) (D.target.pts (i + 1)), (∃ j k, (D.tile j).pts k = Q) →
      (∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
        ∧ Even ((edgesAt D.toDissection Q).filter (edgeType D α)).card := by
  intro Q hQ ⟨j, k, hjk⟩
  have hQfr : Q ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target i (openSegment_subset_segment _ _ _ hQ)
  have hQnc : Q ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m i (hm ▸ hQ)
  obtain ⟨e1, e2⟩ := side_counts D hirr hrel h hQfr hQnc
  have hpos := vertex_pos D hirr hrel h hjk
  refine ⟨fun j' m hQ' => ?_, ?_⟩
  · have := angleCount_pos D (Tri.localAngle_openSegment _ m hQ')
    omega
  · rw [card_a D hirr hrel h Q]
    exact ⟨1, by omega⟩

end Relation

section TQ

variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h

/-- The values `tileα D, tileβ D, tileγ D` are `α, β, γ` in some order. -/
theorem tile_vals (x : ℝ) : (x = tileα D ∨ x = tileβ D ∨ x = tileγ D) ↔
    (x = α ∨ x = β ∨ x = 2 * α + β) := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  have e0 : tileα D = D.model.angleAt 0 := rfl
  have e1 : tileβ D = D.model.angleAt 1 := rfl
  have e2 : tileγ D = D.model.angleAt 2 := rfl
  rw [e0, e1, e2]
  have hk : ∀ y, (y = D.model.angleAt 0 ∨ y = D.model.angleAt 1 ∨ y = D.model.angleAt 2) ↔
      ∃ k, y = D.model.angleAt k := by
    intro y; constructor
    · rintro (h | h | h) <;> exact ⟨_, h⟩
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  have hk' : ∀ y, (y = α ∨ y = β ∨ y = 2 * α + β) ↔ ∃ m, y = D.model.angleAt (σ m) := by
    intro y; rw [← h2, ← h0, ← h1]; constructor
    · rintro (h | h | h) <;> exact ⟨_, h⟩
    · rintro ⟨m, rfl⟩; fin_cases m <;> simp
  rw [hk, hk']
  constructor
  · rintro ⟨k, rfl⟩; obtain ⟨m, rfl⟩ := σ.surjective k; exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩; exact ⟨_, rfl⟩

/-- A tile's angles are distinct, so its vertex with a given angle is unique. -/
theorem tile_angle_inj (i : Fin N) {k k' : Fin 3}
    (e : (D.tile i).angleAt k = (D.tile i).angleAt k') : k = k' := by
  obtain ⟨ρ, h0, -, h1, -, h2, -⟩ := tile_threeAlpha D h i
  obtain ⟨hv0, hinj⟩ := values_sep D hirr hrel h
  have v : ∀ m : Fin 3, (D.tile i).angleAt (ρ m) = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi]
      (Fin.castLE (by norm_num) m) := by
    intro m; fin_cases m <;> simp [h0, h1, h2]
  obtain ⟨m, rfl⟩ := ρ.surjective k
  obtain ⟨m', rfl⟩ := ρ.surjective k'
  rw [v, v] at e
  rw [Fin.castLE_injective _ (hinj e)]

open Classical in
/-- **`theorem:arelation` when `ABC` has a `β` corner** (the paper's Cases 2 and 4, among them the
triquadratic case), as edges. -/
theorem lone_beta_hasRelation
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β))
    (hβc : ∃ k, D.target.angleAt k = β) :
    HasRelation D.toDissection (edgeType D α) := by
  by_contra hnorel
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact hns hs
  have hsep := anglesSep D hirr hrel h
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  -- The `β` corner.
  obtain ⟨k, hk⟩ := hβc
  have hck := corner_eq D hirr hrel h hz k
  rw [hk] at hck
  obtain ⟨cα, cβ⟩ := indep hirr hrel (p := vcount D k α) (q := vcount D k β) (p' := 0) (q' := 1)
    (by rw [← hck]; push_cast; ring)
  set V := D.target.pts k
  have nα : angleCount D V α = 0 := cα
  have nβ : angleCount D V β = 1 := cβ
  have nγ : ∀ m, angleCount D (D.target.pts m) (2 * α + β) = 0 := hz
  -- The edges at `V` on the two sides at `V` are `a` or `c` edges of the one tile there.
  have atV : ∀ {e : Fin N × Fin 3}, ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) →
      (D.tile e.1).localAngle V = β ∧ (edgeType D α e ∨ edgeType D (2 * α + β) e) := by
    intro e hV
    have hang : (D.tile e.1).localAngle V = β := by
      rcases (tile_vals D hirr hrel h _).1 (angle_at_end D hV) with e1 | e1 | e1
      · exact absurd e1 (ne_of_angleCount_zero D nα e.1)
      · exact e1
      · exact absurd e1 (ne_of_angleCount_zero D (nγ k) e.1)
    refine ⟨hang, ?_⟩
    have hnot := edge_type_ne D hsep hV ((tile_vals D hirr hrel h β).2 (Or.inr (Or.inl rfl))) hang
    rcases (tile_vals D hirr hrel h _).1 (localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)) with
      e1 | e1 | e1
    · exact Or.inl e1
    · exact absurd e1 hnot
    · exact Or.inr e1
  -- At most one `γ` at a point of a side.
  have htwo : ∀ i : Fin 3, ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (Finset.univ.filter fun j => (D.tile j).localAngle P = 2 * α + β).card ≤ 1 := by
    intro i P hP
    change angleCount D P (2 * α + β) ≤ 1
    by_cases hPc : P ∈ Set.range D.target.pts
    · obtain ⟨m, rfl⟩ := hPc
      rw [nγ m]; omega
    · obtain ⟨e1, -⟩ := side_counts D hirr hrel h (tri_side_subset_frontier D.target i hP) hPc
      omega
  have hγv : 2 * α + β = tileα D ∨ 2 * α + β = tileβ D ∨ 2 * α + β = tileγ D :=
    (tile_vals D hirr hrel h _).2 (Or.inr (Or.inr rfl))
  -- A side `j` with an `a` edge starts a link of `Γ_a`.
  have start : ∀ j : Fin 3, ∀ part : Finset (Fin N × Fin 3),
      (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts j) (D.target.pts (j + 1)) →
      (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
        ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton) →
      ∀ ea ∈ part, edgeType D α ea → False := by
    intro j part hcov hdisj ea hea hθa
    obtain ⟨ec, hec, hθc⟩ := side_has_edge_sep D hsep _ hγv j part hcov hdisj
      (fun e _ _ => ne_of_angleCount_zero D (nγ j) e.1)
      (fun e _ _ => ne_of_angleCount_zero D (nγ (j + 1)) e.1) (htwo j)
    have hnθ : ¬ edgeType D α ec := fun e' => by
      have : (2 * α + β) = α := hθc.symm.trans e'
      linarith
    set ρ : Equiv.Perm (Fin 3) := Equiv.addRight j
    set D' := relabelTarget D ρ
    have hcov' : (⋃ e ∈ part, (D'.tile e.1).edge e.2) =
        segment ℝ (D'.target.pts 0) (D'.target.pts 1) := by
      show _ = segment ℝ (D.target.pts (0 + j)) (D.target.pts (1 + j))
      rw [zero_add, add_comm]; exact hcov
    have hgood : ∀ Q ∈ openSegment ℝ (D'.target.pts 0) (D'.target.pts 1),
        (∃ i k, (D'.tile i).pts k = Q) →
        (∀ i : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D'.tile i).pts m) ((D'.tile i).pts (m + 1)))
          ∧ Even ((edgesAt D'.toDissection Q).filter (edgeType D α)).card := by
      have e0 : D'.target.pts 0 = D.target.pts j := by show D.target.pts (0 + j) = _; rw [zero_add]
      have e1 : D'.target.pts 1 = D.target.pts (j + 1) := by
        show D.target.pts (1 + j) = _; rw [add_comm]
      rw [e0, e1]
      exact side_good3 D hirr hrel h j
    obtain ⟨Q₀, hQ₀, R, hR⟩ := side_start D'.toDissection (edgeType D α) part hcov' hea hec hθa
      hnθ hgood (fun hr => hnorel hr)
    have hQ₀' : Q₀ ∈ frontier D.target.carrier := by rwa [relabelTarget_carrier] at hQ₀
    exact hnorel (relation_of_start D.toDissection (edgeType D α)
      (fun _ _ _ _ hl => a_even_end D hirr hrel h hl) ⟨Q₀, hQ₀', R, isLink_of_relabel D ρ hR⟩)
  obtain ⟨partk, hcovk, hdisjk, -⟩ := D.toDissection.side_walk k
  obtain ⟨part2, hcov2, hdisj2, -⟩ := D.toDissection.side_walk (k + 2)
  have hcov2' : (⋃ e ∈ part2, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts (k + 2)) (D.target.pts k) := by
    rw [hcov2, show k + 2 + 1 = k by fin_cases k <;> rfl]
  obtain ⟨e0, he0, hV0⟩ := side_edge_at_end D hcovk (V := V) (Or.inl rfl)
  obtain ⟨e2, he2, hV2⟩ := side_edge_at_end D hcov2' (V := V) (Or.inr rfl)
  obtain ⟨hβ0, ht0⟩ := atV hV0
  obtain ⟨hβ2, ht2⟩ := atV hV2
  rcases ht0 with ha0 | hc0
  · exact start k partk hcovk hdisjk e0 he0 ha0
  rcases ht2 with ha2 | hc2
  · exact start (k + 2) part2 hcov2 hdisj2 e2 he2 ha2
  -- Both edges at `V` are the `c` edge of the one tile at `V`: the same edge.
  have h1 : e0.1 = e2.1 := eq_of_angleCount_le_one D nβ.le hβ0 hβ2
  have h2 : e0.2 = e2.2 := by
    have a0 : (D.tile e0.1).angleAt (e0.2 + 2) = 2 * α + β := (localAngle_pts _ _).symm.trans hc0
    have a2 : (D.tile e0.1).angleAt (e2.2 + 2) = 2 * α + β := by
      rw [h1]; exact (localAngle_pts _ _).symm.trans hc2
    have := tile_angle_inj D hirr hrel h e0.1 (a0.trans a2.symm)
    simpa using this
  have he : e0 = e2 := Prod.ext h1 h2
  subst he
  have hsub0 : (D.tile e0.1).edge e0.2 ⊆ segment ℝ (D.target.pts k) (D.target.pts (k + 1)) := by
    rw [← hcovk]; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e0, he0, hy⟩
  have hsub2 : (D.tile e0.1).edge e0.2 ⊆
      segment ℝ (D.target.pts (k + 2)) (D.target.pts (k + 2 + 1)) := by
    rw [← hcov2]; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e0, he2, hy⟩
  have hm : ∀ x ∈ (D.tile e0.1).edge e0.2, x = D.target.pts k := fun x hx =>
    sides_meet D.target k (hsub0 hx) (hsub2 hx)
  exact (D.tile e0.1).indep.injective.ne (fin3_ne_add_one e0.2)
    ((hm _ (left_mem_segment ℝ _ _)).trans (hm _ (right_mem_segment ℝ _ _)).symm)

end TQ

end TriangleTiling.ThreeAlpha
