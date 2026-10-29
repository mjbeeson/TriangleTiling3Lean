/-
A wall `PR` with no edge running past its ends, for `lemma:twocs`.

Let `PR` be a segment of the line `{g = c}` inside the tiled triangle, lying in no tile's interior,
such that no edge of the chain on the side `{g ≤ c}` has `P` or `R` strictly inside it. Then the
chain edges that meet `PR` in more than a point lie inside `PR`, they cover `PR`, any two meet in at
most a point, and their lengths add up to `|PR|`.
-/
import TriangleTiling.Tiling.LineParams
import TriangleTiling.Tiling.WallSum
import TriangleTiling.Tiling.SegmentChain

namespace TriangleTiling.TwoCs

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {P R : Plane}
  (hg : g ≠ 0) (hPR : P ≠ R) (hP : g P = c) (hR : g R = c)
  (hendP : ∀ e ∈ D.lineChain g c,
    P ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  (hendR : ∀ e ∈ D.lineChain g c,
    R ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))

include hg hPR hP hR in
/-- A point of a chain edge and of `PR`, in parameters. -/
theorem param_of_mem {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {y : Plane}
    (hy : y ∈ (D.tile e.1).edge e.2) (hy' : y ∈ segment ℝ P R) :
    ∃ t, y = AffineMap.lineMap P R t ∧ t ∈ Icc (0 : ℝ) 1 ∧
      t ∈ Icc (edgeLo P R (D.tile e.1) e.2) (edgeHi P R (D.tile e.1) e.2) := by
  rw [segment_eq_image_lineMap] at hy'
  obtain ⟨t, ht, rfl⟩ := hy'
  exact ⟨t, rfl, ht, (chain_mem_edge_iff D hg hPR hP hR he t).mp hy⟩

include hg hPR hP hR hendP hendR in
/-- Each chain edge lies in `PR` or meets it in at most a point. -/
theorem chain_dich {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    (D.tile e.1).edge e.2 ⊆ segment ℝ P R ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ P R).Subsingleton := by
  set lo := edgeLo P R (D.tile e.1) e.2
  set hi := edgeHi P R (D.tile e.1) e.2
  obtain ⟨h1, h2⟩ := lineChain_ends D he
  have hP0 : AffineMap.lineMap P R (0 : ℝ) = P := AffineMap.lineMap_apply_zero P R
  have hR1 : AffineMap.lineMap P R (1 : ℝ) = R := AffineMap.lineMap_apply_one P R
  have nP : ¬ (0 : ℝ) ∈ Ioo lo hi := fun h =>
    hendP e he (hP0 ▸ (lineMap_mem_openSegment_iff hg hPR hP hR _ _ h1 h2 0).mpr h)
  have nR : ¬ (1 : ℝ) ∈ Ioo lo hi := fun h =>
    hendR e he (hR1 ▸ (lineMap_mem_openSegment_iff hg hPR hP hR _ _ h1 h2 1).mpr h)
  by_cases hsub : 0 ≤ lo ∧ hi ≤ 1
  · left
    intro y hy
    rw [edge_eq_image hg hPR hP hR _ _ h1 h2] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨le_trans hsub.1 ht.1, le_trans ht.2 hsub.2⟩, rfl⟩
  · right
    rintro y ⟨hy, hy'⟩ z ⟨hz, hz'⟩
    obtain ⟨t, rfl, ht, ht'⟩ := param_of_mem D hg hPR hP hR he hy hy'
    obtain ⟨s, rfl, hs, hs'⟩ := param_of_mem D hg hPR hP hR he hz hz'
    have hlh := chain_lo_lt_hi D hg hPR hP hR he
    simp only [mem_Ioo, not_and_or, not_lt] at nP nR
    push Not at hsub
    have : t = s := by
      rcases le_or_gt 0 lo with h0 | h0
      · have hh := hsub h0
        rcases nR with h | h <;> simp only [mem_Icc] at ht ht' hs hs' <;> linarith
      · rcases nP with h | h <;> simp only [mem_Icc] at ht ht' hs hs' <;> linarith
    rw [this]

include hg hPR hP hR hendP hendR in
open Classical in
/-- **The chain covers the wall.** -/
theorem chain_cover
    (hint : openSegment ℝ P R ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier) :
    (⋃ e ∈ (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R),
      (D.tile e.1).edge e.2) = segment ℝ P R := by
  classical
  set S := (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R)
  apply Subset.antisymm
  · exact iUnion₂_subset fun e he => (Finset.mem_filter.mp he).2
  set U := ⋃ e ∈ S, (D.tile e.1).edge e.2
  have hU : IsClosed U := by
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet S) fun e _ => ?_
    exact (D.tile e.1).isClosed_edge e.2
  -- Every non-vertex point of the open wall is in `U`.
  have hgood : ∀ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap P R t ∉ D.vertexSet →
      AffineMap.lineMap P R t ∈ U := by
    intro t ht hv
    have hP0 : AffineMap.lineMap P R (0 : ℝ) = P := AffineMap.lineMap_apply_zero P R
    have hR1 : AffineMap.lineMap P R (1 : ℝ) = R := AffineMap.lineMap_apply_one P R
    obtain ⟨e, he, hte⟩ := wall_cover_param D hg hPR hP hR zero_lt_one
      (by rw [hP0, hR1]; exact hint) (by rw [hP0, hR1]; exact hwall) ht hv
    obtain ⟨h1, h2⟩ := lineChain_ends D he
    set lo := edgeLo P R (D.tile e.1) e.2
    set hi := edgeHi P R (D.tile e.1) e.2
    -- `t` is not an end of the edge (those are vertices).
    have hlo : lo ≠ t := by
      intro h
      apply hv
      have : AffineMap.lineMap P R lo ∈ D.vertexSet := by
        simp only [lo, edgeLo]
        rcases le_total (lineParam P R ((D.tile e.1).pts e.2))
          (lineParam P R ((D.tile e.1).pts (e.2 + 1))) with hle | hle
        · rw [min_eq_left hle, eq_lineMap_lineParam hg hPR hP hR h1]
          exact mem_iUnion.mpr ⟨e.1, mem_iUnion.mpr ⟨e.2, rfl⟩⟩
        · rw [min_eq_right hle, eq_lineMap_lineParam hg hPR hP hR h2]
          exact mem_iUnion.mpr ⟨e.1, mem_iUnion.mpr ⟨e.2 + 1, rfl⟩⟩
      rwa [h] at this
    have hhi : hi ≠ t := by
      intro h
      apply hv
      have : AffineMap.lineMap P R hi ∈ D.vertexSet := by
        simp only [hi, edgeHi]
        rcases le_total (lineParam P R ((D.tile e.1).pts e.2))
          (lineParam P R ((D.tile e.1).pts (e.2 + 1))) with hle | hle
        · rw [max_eq_right hle, eq_lineMap_lineParam hg hPR hP hR h2]
          exact mem_iUnion.mpr ⟨e.1, mem_iUnion.mpr ⟨e.2 + 1, rfl⟩⟩
        · rw [max_eq_left hle, eq_lineMap_lineParam hg hPR hP hR h1]
          exact mem_iUnion.mpr ⟨e.1, mem_iUnion.mpr ⟨e.2, rfl⟩⟩
      rwa [h] at this
    have htlo : lo < t := lt_of_le_of_ne hte.1 hlo
    have hthi : t < hi := lt_of_le_of_ne hte.2 hhi.symm
    have heS : e ∈ S := by
      refine Finset.mem_filter.mpr ⟨he, ?_⟩
      rcases chain_dich D hg hPR hP hR hendP hendR he with h | h
      · exact h
      · exfalso
        -- A second common point.
        set t' := (t + min hi 1) / 2
        have ht'1 : t < t' := by
          simp only [t']; have := lt_min hthi ht.2; linarith
        have ht'2 : t' < min hi 1 := by
          simp only [t']; have := lt_min hthi ht.2; linarith
        have m1 : AffineMap.lineMap P R t ∈ (D.tile e.1).edge e.2 ∩ segment ℝ P R := by
          refine ⟨(chain_mem_edge_iff D hg hPR hP hR he t).mpr hte, ?_⟩
          rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
        have m2 : AffineMap.lineMap P R t' ∈ (D.tile e.1).edge e.2 ∩ segment ℝ P R := by
          refine ⟨(chain_mem_edge_iff D hg hPR hP hR he t').mpr
            ⟨by linarith, by linarith [min_le_left hi 1]⟩, ?_⟩
          rw [segment_eq_image_lineMap]
          exact ⟨t', ⟨by linarith [ht.1], by linarith [min_le_right hi 1]⟩, rfl⟩
        have := AffineMap.lineMap_injective ℝ hPR (h m1 m2)
        linarith
    exact mem_biUnion heS ((chain_mem_edge_iff D hg hPR hP hR he t).mpr hte)
  -- Closure.
  intro y hy
  by_contra hyU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU.isOpen_compl y hyU
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨t0, ht0, rfl⟩ := hy
  have hd : 0 < dist P R := dist_pos.mpr hPR
  set ε := δ / (2 * dist P R)
  have hε : 0 < ε := by positivity
  set lo := max 0 (t0 - ε)
  set hi := min 1 (t0 + ε)
  have hlohi : lo < hi := by
    simp only [lo, hi, max_lt_iff, lt_min_iff]
    constructor <;> constructor <;> linarith [ht0.1, ht0.2]
  have hinf : (AffineMap.lineMap P R '' Ioo lo hi).Infinite :=
    (Ioo_infinite hlohi).image (AffineMap.lineMap_injective ℝ hPR).injOn
  obtain ⟨_, ⟨t, ht, rfl⟩, htv⟩ := (hinf.diff D.vertexSet_finite).nonempty
  have ht01 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hmem := hgood t ht01 htv
  apply hball _ hmem
  rw [Metric.mem_ball, dist_lineMap_lineMap, Real.dist_eq]
  have h1 : t0 - ε < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have h2 : t < t0 + ε := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have habs : |t - t0| < ε := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  calc |t - t0| * dist P R ≤ ε * dist P R := by gcongr
    _ = δ / 2 := by simp only [ε]; field_simp
    _ < δ := by linarith

include hg hPR hP hR hendP hendR in
open Classical in
/-- **The lengths add up.** -/
theorem chain_sum
    (hint : openSegment ℝ P R ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P R := by
  classical
  have hS : segment ℝ P R ⊆ {y | g y = c} := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨s, -, rfl⟩
    exact level_lineMap hP hR s
  convert wall_sum D g c hg hPR hS hint hwall
    (fun e he => chain_dich D hg hPR hP hR hendP hendR he)

include hg in
/-- Two chain edges meet in at most a point. -/
theorem chain_disj {e₁ e₂ : Fin N × Fin 3} (h₁ : e₁ ∈ D.lineChain g c)
    (h₂ : e₂ ∈ D.lineChain g c) (hne : e₁ ≠ e₂) :
    ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton := by
  intro y hy z hz
  by_contra hyz
  exact hne (lineChain_eq_of_two D hg h₁ h₂ hyz hy hz)

end TriangleTiling.TwoCs
