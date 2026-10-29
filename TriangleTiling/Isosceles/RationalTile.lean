/-
`theorem:rationaltile`: if the isosceles triangle `ABC` with base angles `α` (`α ∉ ℚπ`) is
`N`-tiled by the tile `(α, β, 2α)`, the tile is rational: the ratios of its sides are rational.

The paper's proof combines `lemma:essentialsegments` (relations `j b = u a + v c` and
`J a = U b + V c`, from Laczkovich's graphs `Γ_b` and `Γ_a`) with `lemma:crelation4` (a relation
`j c = p a + q b`, from `Γ_c`). Here only two of the three are used: the relation for `c` and the
one for `a` already determine `a : b : c`. The graph `Γ_b` is not needed.

* `crelation4`: by contradiction, every link of `Γ_c` is followed by another (`out_of_in`; the
  `c` edges at any vertex are even in number) and one starts on the boundary
  (`boundary_start`), where no link ends: so links outnumber themselves.
* `arelation`: the same with `Γ_a`, where a link may die at a star, but one starts at every
  center, and the centers outnumber the stars (`starsandcenters`).

The paper establishes "a link is followed by another" through the figures `GammaA`, `GammaB`;
here it is a parity count of the edges at a vertex (`mixed_of_parity`).
-/
import TriangleTiling.Isosceles.GammaStart
import TriangleTiling.Isosceles.LengthRelations
import TriangleTiling.Isosceles.N45

namespace TriangleTiling

open Erdos634.Geometry Set EuclideanGeometry

variable {N : ℕ} (D : CongruentDissection N)

/-- The mirror image has the same tiled region. -/
theorem swapAC_carrier : (swapAC D).target.carrier = D.target.carrier := by
  show convexHull ℝ (Set.range ![D.target.pts 2, D.target.pts 1, D.target.pts 0]) =
    convexHull ℝ (Set.range D.target.pts)
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- A corner of the target is not interior to it. -/
theorem corner_not_interior (m : Fin 3) : D.target.pts m ∉ interior D.target.carrier := by
  intro h
  have := (Tri.mem_interior_iff_coord_pos D.target _).mp h (m + 1)
  rw [Tri.coord_vertex] at this
  have hne : ¬ (m + 1 = m) := by fin_cases m <;> decide
  simp [hne] at this

/-- Links of the mirror image are links of the tiling. -/
theorem isLink_of_swapAC {isθ : Fin N × Fin 3 → Prop} {Q R : Plane}
    (h : IsLink (swapAC D).toDissection isθ Q R) : IsLink D.toDissection isθ Q R := by
  obtain ⟨g, c, h⟩ := h
  exact ⟨g, c, ⟨h.ne, h.hg, h.hQ, h.hR, h.cov, h.inner, h.start, h.past, h.across⟩⟩

/-- The ends of links are vertices of the tiling. -/
theorem link_mem_vertices {isθ : Fin N × Fin 3 → Prop} {u w : Plane}
    (h : IsLink D.toDissection isθ u w) : u ∈ tilingVertices D ∧ w ∈ tilingVertices D := by
  obtain ⟨g, c, h⟩ := h
  obtain ⟨i, k, hik⟩ := h.start_vertex
  obtain ⟨i', k', hik'⟩ := h.end_vertex
  exact ⟨(mem_tilingVertices D).mpr ⟨i, k, hik⟩, (mem_tilingVertices D).mpr ⟨i', k', hik'⟩⟩

/-- **The algebra of `theorem:rationaltile`.** Relations `J c = p a + q b` and `J' a = p' b + q' c`
(with `J, J' > 0`) and `c² = a² + a b` make `b / a` and `c / a` rational. -/
theorem rational_of_relations {a b c : ℝ} (ha : 0 < a) (hcab : c ^ 2 = a ^ 2 + a * b)
    (hRc : ∃ J p q : ℕ, 0 < J ∧ (J : ℝ) * c = p * a + q * b)
    (hRa : ∃ J p q : ℕ, 0 < J ∧ (J : ℝ) * a = p * b + q * c) :
    ∃ r s : ℚ, b = r * a ∧ c = s * a := by
  obtain ⟨j', p', q', hj', hc'⟩ := hRc
  obtain ⟨j, p, q, hj, ha'⟩ := hRa
  have hj'R : (0 : ℝ) < j' := by exact_mod_cast hj'
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  -- Eliminate `c`: `(j j' - q p') a = (j' p + q q') b`.
  have key : ((j : ℝ) * j' - q * p') * a = ((j' : ℝ) * p + q * q') * b := by
    have e1 : (j' : ℝ) * (j * a) = j' * p * b + q * (j' * c) := by rw [ha']; ring
    rw [hc'] at e1
    linear_combination e1
  by_cases hden : (j' : ℕ) * p + q * q' = 0
  · -- Then `p = 0`, `q' = 0` and `j a = q c`.
    have hp : p = 0 := by
      rcases Nat.eq_zero_of_add_eq_zero hden with ⟨h1, -⟩
      rcases Nat.mul_eq_zero.mp h1 with h | h
      · omega
      · exact h
    have hdenR : ((j' : ℝ) * p + q * q') = 0 := by exact_mod_cast hden
    rw [hdenR, zero_mul] at key
    have hq : q ≠ 0 := by
      rintro rfl
      rw [hp] at ha'
      simp at ha'
      rcases ha' with h | h
      · omega
      · exact ha.ne' h
    have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    rw [hp, Nat.cast_zero, zero_mul, zero_add] at ha'
    have hcs : c = ((j : ℚ) / q : ℚ) * a := by
      push_cast; field_simp; linarith
    refine ⟨((j : ℚ) / q) ^ 2 - 1, (j : ℚ) / q, ?_, hcs⟩
    have : a * b = a * ((((j : ℚ) / q) ^ 2 - 1 : ℚ) * a) := by
      rw [show a * b = c ^ 2 - a ^ 2 by linarith, hcs]; push_cast; ring
    exact mul_left_cancel₀ ha.ne' this
  · have hdenR : ((j' : ℝ) * p + q * q') ≠ 0 := by exact_mod_cast hden
    have hb : b = ((((j : ℚ) * j' - q * p') / (j' * p + q * q') : ℚ)) * a := by
      push_cast
      field_simp
      linarith
    refine ⟨((j : ℚ) * j' - q * p') / (j' * p + q * q'),
      (p' + q' * (((j : ℚ) * j' - q * p') / (j' * p + q * q'))) / j', hb, ?_⟩
    have hc2 : c = (p' * a + q' * b) / j' := by field_simp; linarith
    rw [hc2, hb]
    push_cast
    field_simp

variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr

include hA hC in
open Classical in
/-- **`Γ_c` starts somewhere on the boundary**, unless there is a relation. -/
theorem gamma_c_start (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D.toDissection (edgeType D (tileγ D)) Q₀ R := by
  obtain ⟨-, -, hinj⟩ := angle_values D hγ hirr
  have hβγ : tileβ D ≠ tileγ D := by
    have ne : ∀ x y : Fin 5, x ≠ y →
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
          ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
    exact ne 1 2 (by decide)
  obtain ⟨part₀, hcov₀, hdisj₀, -⟩ := D.toDissection.side_walk 0
  obtain ⟨part₁, hcov₁, hdisj₁, -⟩ := D.toDissection.side_walk 1
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h01] at hcov₀
  rw [h12] at hcov₁
  obtain ⟨-, -, -, -, -, cγB, -, -⟩ := counts_at_corners D hγ hirr hA hC
  have hα : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts 1 →
      (D.tile i).localAngle (D.target.pts 1) ≠ tileβ D →
        (D.tile i).localAngle (D.target.pts 1) = tileα D := by
    intro i j hj hβ
    rcases localAngle_at_own_vertex_mem' D i j with h | h | h <;> rw [hj] at h
    · exact h
    · exact absurd h hβ
    · exact absurd h (ne_of_angleCount_zero D cγB i)
  have hvert : ∀ e : Fin N × Fin 3, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        ∃ j : Fin 3, (D.tile e.1).pts j = D.target.pts 1 := by
    intro e h
    rcases h with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  rcases beta_at_apex D hγ hirr hA hC part₀ part₁ hcov₀ hcov₁ with hB | hB
  · obtain ⟨⟨eb, heb, hθb⟩, ⟨ec, hec, hθc⟩⟩ := qandrnotzero D hγ hirr hA hC part₀ hcov₀ hdisj₀
      (fun e he hend => by
        obtain ⟨j, hj⟩ := hvert e hend
        exact hα e.1 j hj (hB e he hend))
    exact boundary_start D hγ hirr part₀ hcov₀ hec heb hθc
      (fun h => hβγ (hθb.symm.trans h)) hnorel
  · -- Side `BC`, on the mirror image.
    have hcov' : (⋃ e ∈ part₁, ((swapAC D).tile e.1).edge e.2) =
        segment ℝ ((swapAC D).target.pts 0) ((swapAC D).target.pts 1) :=
      hcov₁.trans (segment_symm ℝ _ _)
    obtain ⟨⟨eb, heb, hθb⟩, ⟨ec, hec, hθc⟩⟩ := qandrnotzero (swapAC D) hγ hirr hC hA part₁ hcov'
      hdisj₁ (fun e he hend => by
        obtain ⟨j, hj⟩ := hvert e hend
        exact hα e.1 j hj (hB e he hend))
    obtain ⟨Q₀, hQ₀, R, hR⟩ := boundary_start (swapAC D) hγ hirr part₁ hcov' hec heb hθc
      (fun h => hβγ (hθb.symm.trans h)) hnorel
    exact ⟨Q₀, by rwa [swapAC_carrier] at hQ₀, R, isLink_of_swapAC D hR⟩

include hA hC in
open Classical in
/-- **`lemma:crelation4`, as edges**: some marked `c` edges and some edges including a non-`c`
edge have equal total lengths. -/
theorem crelation4_edges : HasRelation D.toDissection (edgeType D (tileγ D)) := by
  by_contra hnorel
  exact hnorel (relation_of_start D.toDissection _
    (fun _ _ _ _ hl => c_count_even D hγ hirr (localAngle_interior' D hl.end_interior))
    (gamma_c_start D hγ hirr hA hC hnorel))

include hA hC in
open Classical in
/-- **`lemma:essentialsegments` (the relation for `a`), as edges**: some `a` edges and some edges
including a non-`a` edge have equal total lengths. -/
theorem arelation_edges : HasRelation D.toDissection (edgeType D (tileα D)) := by
  by_contra hnorel
  set θ := edgeType D (tileα D)
  set V := tilingVertices D
  let star : Plane → Prop := fun v => v ∉ Set.range D.target.pts ∧ vertexType D v = (3, 1, 0)
  let center : Plane → Prop := fun v => v ∉ Set.range D.target.pts ∧ vertexType D v = (0, 2, 3)
  have key : ∀ v ∈ V, (V.filter fun u => IsLink D.toDissection θ u v).card
      + (if center v then 1 else 0) ≤
      (V.filter fun w => IsLink D.toDissection θ v w).card + (if star v then 1 else 0) := by
    intro v hv
    have hle1 := in_le_one D.toDissection θ V v
    by_cases hc : center v
    · have hns : ¬ star v := fun hs => by
        have := hs.2.symm.trans hc.2
        simp at this
      rw [if_pos hc, if_neg hns]
      have hin0 : (V.filter fun u => IsLink D.toDissection θ u v).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro u - ⟨g, c, hl⟩
        obtain ⟨-, hπ, -⟩ := center_facts D hγ hirr hv hc.1 hc.2
        obtain ⟨ε, -, hRε⟩ := hl.across
        have := angleCount_pos D (Tri.localAngle_openSegment _ ε.2 hRε)
        omega
      obtain ⟨R, hR⟩ := center_out D hγ hirr hv hc.1 hc.2 hnorel
      have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
        Finset.card_pos.mpr ⟨R, Finset.mem_filter.mpr ⟨(link_mem_vertices D hR).2, hR⟩⟩
      omega
    · rw [if_neg hc]
      by_cases hs : star v
      · rw [if_pos hs]; omega
      · rw [if_neg hs]
        rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D.toDissection θ u v).card
          with h0 | hpos
        · omega
        · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
          obtain ⟨-, g, c, hl⟩ := Finset.mem_filter.mp hu
          rcases link_end_a D hγ hirr hl with ht | heven
          · exfalso
            refine hs ⟨?_, ht⟩
            rintro ⟨m, hm⟩
            exact corner_not_interior D m (hm ▸ hl.end_interior)
          · obtain ⟨R', hR'⟩ := out_of_in D.toDissection θ hl heven hnorel
            have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
              Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr
                ⟨(link_mem_vertices D hR').2, hR'⟩⟩
            omega
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter,
    ← Finset.card_filter, sum_out_eq_sum_in] at hsum
  have hsc := starsandcenters D hγ hirr hA hC
  change _ + typeCount D (0, 2, 3) ≤ _ + typeCount D (3, 1, 0) at hsum
  omega

include hA hC in
/-- **The relation for `c`** (`lemma:crelation4`): `J c = p a + q b` with `J > 0`. -/
theorem crelation4 : ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 2) (D.model.pts 0) :=
  c_relation_of_edges D (anglesSep_of_two_alpha D hγ hirr) (crelation4_edges D hγ hirr hA hC)

include hA hC in
/-- **The relation for `a`** (from `Γ_a`, as in `lemma:essentialsegments`): `J a = p b + q c` with
`J > 0`. -/
theorem arelation : ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      = p * dist (D.model.pts 2) (D.model.pts 0) + q * dist (D.model.pts 0) (D.model.pts 1) :=
  a_relation_of_edges D (anglesSep_of_two_alpha D hγ hirr) (arelation_edges D hγ hirr hA hC)

include hA hC in
/-- **Theorem `theorem:rationaltile`.** Let the isosceles triangle `ABC` with base angles `α`
(`α` not a rational multiple of `π`) be `N`-tiled by a tile with angles `(α, β, 2α)`. Then the tile
is rational: its sides `a, b, c` (opposite `α, β, γ`) satisfy `b = r a` and `c = s a` with `r, s`
rational. -/
theorem rationaltile : ∃ r s : ℚ,
    dist (D.model.pts 2) (D.model.pts 0) = r * dist (D.model.pts 1) (D.model.pts 2) ∧
    dist (D.model.pts 0) (D.model.pts 1) = s * dist (D.model.pts 1) (D.model.pts 2) := by
  obtain ⟨ha, -, -⟩ := model_sides_pos D
  have hcab := (twoalphatiles (tri_indep D.model) rfl rfl rfl).mp hγ
  exact rational_of_relations ha hcab (crelation4 D hγ hirr hA hC) (arelation D hγ hirr hA hC)

end TriangleTiling
