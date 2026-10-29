/-
`lemma:crelation` (Section 11 of M. Beeson, *Tilings of an isosceles triangle*): if the isosceles
triangle `ABC` with base angles `α` (`α ∉ ℚπ`) is `N`-tiled by `(α, β, 2π/3)`, there is a relation
`j c = p a + q b` with `j > 0`.

The proof follows `lemma:crelation4` (the case `γ = 2α`, `RationalTile.lean`):

* at every point inside the target or inside a side the `α` and `β` angles pair up, so the `c`
  edges there (one for each tile with its `α` or `β` there) are even in number
  (`c_count_even120`); this replaces `lemma:extendlink`, and lets every link of `Γ_c` be followed
  by another (`out_of_in`);
* a side carrying both a `c` edge and another edge starts a link of `Γ_c` on the boundary
  (`side_start`), where no link ends. The paper's pigeonhole puts a `c` edge on `AB` and on `AC`,
  and the tile at `A` has its `b` edge on one of them.
-/
import TriangleTiling.Gamma120.Angles
import TriangleTiling.Isosceles.RationalTile
import TriangleTiling.RightTile.AllC
import TriangleTiling.RightTile.Helper3

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Set

/-- **The side pigeonhole** (as `side_has_edge`, for any tile with distinct angles). -/
theorem side_has_edge_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (θ : ℝ)
    (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D) (i : Fin 3) (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hAθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts i ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts i) →
        (D.tile e.1).localAngle (D.target.pts i) ≠ θ)
    (hBθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts (i + 1) ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts (i + 1)) →
        (D.tile e.1).localAngle (D.target.pts (i + 1)) ≠ θ)
    (htwo : ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card ≤ 1) :
    ∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = θ := by
  classical
  by_contra hno
  push Not at hno
  have hcorner : ∀ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = θ ∨
      (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) = θ := by
    intro e he
    have hcnt := tile_angle_count_sep D hsep e.1
    have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile e.1).pts (k + 1))
        ((D.tile e.1).pts k) ((D.tile e.1).pts (k + 2)) = θ).card = 1 := by
      rcases hθ with rfl | rfl | rfl
      · exact hcnt.1
      · exact hcnt.2.1
      · exact hcnt.2.2
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hkθ : cornerAngle ((D.tile e.1).pts (k + 1)) ((D.tile e.1).pts k)
        ((D.tile e.1).pts (k + 2)) = θ := by
      have : k ∈ Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile e.1).pts (k + 1))
          ((D.tile e.1).pts k) ((D.tile e.1).pts (k + 2)) = θ := by rw [hk]; simp
      exact (Finset.mem_filter.mp this).2
    have hloc : (D.tile e.1).localAngle ((D.tile e.1).pts k) = θ := by
      rw [Tri.localAngle_vertex]; exact hkθ
    have hk2 : k ≠ e.2 + 2 := fun h => hno e he (h ▸ hloc)
    have : k = e.2 ∨ k = e.2 + 1 := by
      obtain ⟨_, j⟩ := e
      fin_cases j <;> fin_cases k <;> simp at hk2 ⊢
    rcases this with rfl | rfl
    · exact Or.inl hloc
    · exact Or.inr hloc
  exact side_pigeonhole D θ i part hcov hdisj hcorner hAθ hBθ htwo

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * Real.pi / 3)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr

open Classical in
/-- **`c` edges pair up** where the `α` and `β` angles do. -/
theorem c_count_even120 {P : Plane} (h : angleCount D P (tileα D) = angleCount D P (tileβ D)) :
    Even ((edgesAt D.toDissection P).filter (edgeType D (tileγ D))).card := by
  have hcm := card_marked D (angle_values120 D hγ hirr).2 P (φ := tileγ D) (Or.inr (Or.inr rfl))
  exact ⟨angleCount D P (tileβ D), by omega⟩

open Classical in
/-- At a tile vertex strictly inside a side, no tile has the point inside an edge, and the `c`
edges are even in number. -/
theorem side_good (i : Fin 3) :
    ∀ Q ∈ openSegment ℝ (D.target.pts i) (D.target.pts (i + 1)), (∃ j k, (D.tile j).pts k = Q) →
      (∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
        ∧ Even ((edgesAt D.toDissection Q).filter (edgeType D (tileγ D))).card := by
  intro Q hQ ⟨j, k, hjk⟩
  have hQfr : Q ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target i (openSegment_subset_segment _ _ _ hQ)
  have hQnc : Q ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m i (hm ▸ hQ)
  have hQc : Q ∈ D.target.carrier := by
    rw [← D.target.isCompact.isClosed.closure_eq]; exact hQfr.1
  obtain ⟨heq, hcase⟩ := counts_noncorner D hγ hirr hQc hQnc
  have hrel : (angleCount D Q (tileβ D) : ℤ) + 2 * angleCount D Q (tileγ D)
      + 3 * angleCount D Q Real.pi + 6 * angleCount D Q (2 * Real.pi) = 3 := by
    rcases hcase with ⟨hint, -⟩ | ⟨-, h⟩
    · exact absurd hint hQfr.2
    · exact h
  have hpos := vertex_counts_pos D hjk
  refine ⟨fun j' m hQ' => ?_, c_count_even120 D hγ hirr heq⟩
  have := angleCount_pos D (Tri.localAngle_openSegment _ m hQ')
  omega

variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hA hC

/-- The relabelling taking the base `CA` to the first side. -/
def σCA : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

open Classical in
/-- **`Γ_c` starts on the boundary**, unless there is a relation. -/
theorem gamma_c_start120 (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D.toDissection (edgeType D (tileγ D)) Q₀ R := by
  have hsep := (angle_values120 D hγ hirr).2
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨⟨cA0, cA1, cA2⟩, ⟨cC0, cC1, cC2⟩, ⟨cB0, cB1, cB2⟩⟩ := corner_counts120 D hγ hirr hA hC
  obtain ⟨part0, hcov0, hdisj0, -⟩ := D.toDissection.side_walk 0
  obtain ⟨part2, hcov2, hdisj2, -⟩ := D.toDissection.side_walk 2
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [i01] at hcov0
  have hcov2' : (⋃ e ∈ part2, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 2) (D.target.pts 0) := by rw [hcov2, i20]
  -- At most one `γ` at a point of a side.
  have htwo : ∀ i : Fin 3, ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (Finset.univ.filter fun j => (D.tile j).localAngle P = tileγ D).card ≤ 1 := by
    intro i P hP
    change angleCount D P (tileγ D) ≤ 1
    by_cases hPc : P ∈ Set.range D.target.pts
    · obtain ⟨m, rfl⟩ := hPc
      fin_cases m <;> simp [cA2, cB2, cC2]
    · have hPfr := tri_side_subset_frontier D.target i hP
      have hPcar : P ∈ D.target.carrier := by
        rw [← D.target.isCompact.isClosed.closure_eq]; exact hPfr.1
      obtain ⟨-, hcase⟩ := counts_noncorner D hγ hirr hPcar hPc
      rcases hcase with ⟨hint, -⟩ | ⟨-, h⟩
      · exact absurd hint hPfr.2
      · omega
  have noγ : ∀ (P : Plane), angleCount D P (tileγ D) = 0 → ∀ j, (D.tile j).localAngle P ≠ tileγ D :=
    fun P h j => ne_of_angleCount_zero D h j
  -- A `c` edge on `AB` and one on `AC`.
  obtain ⟨c0, hc0, hθc0⟩ := side_has_edge_sep D hsep _ (Or.inr (Or.inr rfl)) 0 part0
    (by rw [i01]; exact hcov0) hdisj0 (fun e _ _ => noγ _ cA2 e.1) (fun e _ _ => noγ _ cB2 e.1)
    (htwo 0)
  obtain ⟨c2, hc2, hθc2⟩ := side_has_edge_sep D hsep _ (Or.inr (Or.inr rfl)) 2 part2 hcov2 hdisj2
    (fun e _ _ => noγ _ cC2 e.1) (fun e _ _ => noγ _ cA2 e.1) (htwo 2)
  -- The edges at `A` on `AB` and on `AC`: not `a` edges.
  have atA : ∀ {e : Fin N × Fin 3}, ((D.tile e.1).pts e.2 = D.target.pts 0 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 0) →
        (D.tile e.1).localAngle (D.target.pts 0) = tileα D ∧
          (edgeType D (tileβ D) e ∨ edgeType D (tileγ D) e) := by
    intro e hV
    have hα : (D.tile e.1).localAngle (D.target.pts 0) = tileα D := by
      rcases angle_at_end D hV with h | h | h
      · exact h
      · exact absurd h (ne_of_angleCount_zero D cA1 e.1)
      · exact absurd h (ne_of_angleCount_zero D cA2 e.1)
    refine ⟨hα, ?_⟩
    have hnot := edge_type_ne D hsep hV (Or.inl rfl) hα
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · exact absurd h hnot
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨e0, he0, hV0⟩ := side_edge_at_end D hcov0 (V := D.target.pts 0) (Or.inl rfl)
  obtain ⟨e2, he2, hV2⟩ := side_edge_at_end D hcov2' (V := D.target.pts 0) (Or.inr rfl)
  obtain ⟨hα0, ht0⟩ := atA hV0
  obtain ⟨hα2, ht2⟩ := atA hV2
  by_cases hb0 : edgeType D (tileβ D) e0
  · -- `AB` carries a `b` edge and a `c` edge.
    exact side_start D.toDissection (edgeType D (tileγ D)) part0 hcov0 hc0 he0 hθc0
      (fun h => hβγ (hb0.symm.trans h)) (side_good D hγ hirr 0) hnorel
  by_cases hb2 : edgeType D (tileβ D) e2
  · -- `AC` carries a `b` edge and a `c` edge: relabel so that `CA` is the first side.
    set D' := relabelTarget D σCA
    have hcov' : (⋃ e ∈ part2, (D'.tile e.1).edge e.2) =
        segment ℝ (D'.target.pts 0) (D'.target.pts 1) := hcov2'
    obtain ⟨Q₀, hQ₀, R, hR⟩ := side_start D'.toDissection (edgeType D (tileγ D)) part2
      hcov' hc2 he2 hθc2 (fun h => hβγ (hb2.symm.trans h)) (side_good D hγ hirr 2)
      (fun h => hnorel h)
    exact ⟨Q₀, by rwa [relabelTarget_carrier] at hQ₀, R, isLink_of_relabel D σCA hR⟩
  -- Otherwise both edges at `A` are `c` edges of the one tile at `A`: the same edge.
  exfalso
  have hc0' := ht0.resolve_left hb0
  have hc2' := ht2.resolve_left hb2
  have h1 : e0.1 = e2.1 := eq_of_angleCount_le_one D cA0.le hα0 hα2
  have h2 : e0.2 = e2.2 := by
    have hu := (tile_angle_count_sep D hsep e0.1).2.2
    have m0 : e0.2 + 2 ∈ Finset.univ.filter fun k : Fin 3 =>
        cornerAngle ((D.tile e0.1).pts (k + 1)) ((D.tile e0.1).pts k)
          ((D.tile e0.1).pts (k + 2)) = tileγ D := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← Tri.localAngle_vertex]; exact hc0'
    have m2 : e2.2 + 2 ∈ Finset.univ.filter fun k : Fin 3 =>
        cornerAngle ((D.tile e0.1).pts (k + 1)) ((D.tile e0.1).pts k)
          ((D.tile e0.1).pts (k + 2)) = tileγ D := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← Tri.localAngle_vertex, h1]; exact hc2'
    have := Finset.card_le_one.mp hu.le _ m0 _ m2
    simpa using this
  have he : e0 = e2 := Prod.ext h1 h2
  subst he
  have hsub0 : (D.tile e0.1).edge e0.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov0]; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e0, he0, hy⟩
  have hsub2 : (D.tile e0.1).edge e0.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) := by
    rw [← hcov2']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e0, he2, hy⟩
  have hm : ∀ x ∈ (D.tile e0.1).edge e0.2, x = D.target.pts 0 := fun x hx =>
    sides_meet D.target 0 (hsub0 hx) (hsub2 hx)
  exact (D.tile e0.1).indep.injective.ne (fin3_ne_add_one e0.2)
    ((hm _ (left_mem_segment ℝ _ _)).trans (hm _ (right_mem_segment ℝ _ _)).symm)

open Classical in
/-- **`lemma:crelation`, as edges.** -/
theorem crelation_edges : HasRelation D.toDissection (edgeType D (tileγ D)) := by
  by_contra hnorel
  exact hnorel (relation_of_start D.toDissection _
    (fun _ R _ _ hl => by
      have hRint := hl.end_interior
      have hRc : R ∉ Set.range D.target.pts := by
        rintro ⟨m, hm⟩; exact corner_not_interior D m (hm ▸ hRint)
      exact c_count_even120 D hγ hirr
        (counts_noncorner D hγ hirr (interior_subset hRint) hRc).1)
    (gamma_c_start120 D hγ hirr hA hC hnorel))

/-- **Lemma `lemma:crelation`.** Let the isosceles triangle `ABC` with base angles `α`
(`α ∉ ℚπ`) be `N`-tiled by `(α, β, 2π/3)`. Then `j c = p a + q b` with `j > 0`. -/
theorem crelation : ∃ j p q : ℕ, 0 < j ∧
    (j : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 2) (D.model.pts 0) :=
  c_relation_of_edges D (angle_values120 D hγ hirr).2 (crelation_edges D hγ hirr hA hC)

end TriangleTiling
