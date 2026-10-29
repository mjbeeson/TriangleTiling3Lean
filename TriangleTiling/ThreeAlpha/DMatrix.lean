/-
The `d` matrix (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv 1206.2229v4, Section on
the shape `(2α, β, α + β)`): its row `j` counts the `a`, `b`, `c` edges on the side of `ABC`
opposite vertex `j`, and the side's length is that row applied to `(a, b, c)`.

`sideEdges D j` is the set of tile edges contained in the side opposite vertex `j`; it is Bonfioli's
side partition (`Dissection.side_walk`), since an edge in the side shares infinitely many points
with an edge of the partition, and two tiles on the same side of a line share at most one point
of edges on it.
-/
import TriangleTiling.ThreeAlpha.NotPrimeArith
import TriangleTiling.TwoCs.PRSetup

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry Set Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

open Classical in
/-- The tile edges contained in the side of `ABC` opposite vertex `j`. -/
noncomputable def sideEdges (j : Fin 3) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e =>
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts (j + 1)) (D.target.pts (j + 2))

open Classical in
/-- **The `d` matrix**: the number of edges of type `θ` (opposite the angle `θ`) on the side
opposite vertex `j`. Row `0` is `(p, d, e)` (side `BC`), row `1` is `(g, n, f)` (side `AC`), row
`2` is `(h, ℓ, r)` (side `AB`), with columns `θ = α, β, γ`. -/
noncomputable def dEntry (j : Fin 3) (θ : ℝ) : ℕ :=
  ((sideEdges D j).filter (edgeType D θ)).card

/-- The level line of a side, with the triangle on the side `≤`. -/
theorem side_level (j : Fin 3) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧
      (∀ y ∈ segment ℝ (D.target.pts (j + 1)) (D.target.pts (j + 2)), g y = c) ∧
      ∀ y ∈ D.target.carrier, g y ≤ c := by
  have h1 : j ≠ j + 1 := by fin_cases j <;> decide
  have h2 : j + 2 ≠ j + 1 := by fin_cases j <;> decide
  have h3 : j ≠ j + 2 := by fin_cases j <;> decide
  obtain ⟨g, c, hg, hgp, hgq, hgr⟩ := TwoCs.edge_level D.target h1 h2 h3
  refine ⟨-g, -c, neg_ne_zero.mpr hg, fun y hy => ?_, ?_⟩
  · rw [segment_eq_image_lineMap] at hy
    obtain ⟨t, -, rfl⟩ := hy
    simp only [LinearMap.neg_apply, neg_inj]
    exact level_lineMap hgp hgq t
  · apply Tri.carrier_subset_halfplane
    intro k
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    have : k = j ∨ k = j + 1 ∨ k = j + 2 := by fin_cases j <;> fin_cases k <;> simp
    rcases this with rfl | rfl | rfl
    · exact hgr.le
    · exact hgp.ge
    · exact hgq.ge

/-- **The side's length is the sum of its edges.** -/
theorem side_sum (j : Fin 3) :
    ∑ e ∈ sideEdges D j, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      D.target.oppLen j := by
  classical
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.toDissection.side_walk (j + 1)
  have hj : j + 1 + 1 = j + 2 := by fin_cases j <;> rfl
  rw [hj] at hcov hsum
  obtain ⟨g, c, hg, hgl, hgt⟩ := side_level D j
  have hsub : ∀ k (y : Plane), y ∈ (D.tile k).carrier → y ∈ D.target.carrier := by
    intro k y hy; rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨k, hy⟩
  have heq : sideEdges D j = part := by
    ext e
    simp only [sideEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro he
      by_contra hep
      -- The edge has infinitely many points, all covered by the partition.
      have hinf : ((D.tile e.1).edge e.2).Infinite := by
        rw [Tri.edge, segment_eq_image_lineMap]
        exact (Set.Icc_infinite zero_lt_one).image
          (AffineMap.lineMap_injective ℝ (tri_pts_succ_ne _ _)).injOn
      have hcov' : ∀ e' ∈ part, (D.tile e'.1).edge e'.2 ⊆
          segment ℝ (D.target.pts (j + 1)) (D.target.pts (j + 2)) :=
        fun e' he' y hy => by rw [← hcov]; exact Set.mem_biUnion he' hy
      obtain ⟨e', he', hinf'⟩ : ∃ e' ∈ part,
          ((D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2).Infinite := by
        by_contra hall
        push Not at hall
        apply hinf
        refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet part)
          fun e' he' => hall e' he') ?_
        intro y hy
        have : y ∈ ⋃ e' ∈ part, (D.tile e'.1).edge e'.2 := by rw [hcov]; exact he hy
        obtain ⟨e', he', hy'⟩ := Set.mem_iUnion₂.mp this
        exact Set.mem_iUnion₂.mpr ⟨e', he', hy, hy'⟩
      have hne : e ≠ e' := fun h => hep (h ▸ he')
      apply hinf'
      exact (D.toDissection.sameside_edges_subsingleton g c hg hne
        (fun y hy => hgt y (hsub _ y hy)) (fun y hy => hgt y (hsub _ y hy))
        (fun y hy => hgl y (he hy)) (fun y hy => hgl y (hcov' e' he' hy))).finite
    · intro he y hy
      rw [← hcov]; exact Set.mem_biUnion he hy
  rw [heq, hsum]
  rfl

variable {α β a b c : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h

open Classical in
/-- **A row of the `d` matrix.** The side of `ABC` opposite vertex `j` has length
`d(j, α) a + d(j, β) b + d(j, γ) c`. -/
theorem dmatrix_row (j : Fin 3) :
    D.target.oppLen j = dEntry D j α * a + dEntry D j β * b + dEntry D j (2 * α + β) * c := by
  have hlen : ∀ e : Fin N × Fin 3, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = (if edgeType D α e then a else 0) + (if edgeType D β e then b else 0) +
        (if edgeType D (2 * α + β) e then c else 0) := by
    intro e
    obtain ⟨ρ, h0, l0, h1, l1, h2, l2⟩ := tile_threeAlpha D h e.1
    have hd : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        (D.tile e.1).oppLen (e.2 + 2) := by
      unfold Tri.oppLen
      rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) e.2,
        (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) e.2]
    have ht : ∀ x, edgeType D x e ↔ (D.tile e.1).angleAt (e.2 + 2) = x := by
      intro x; unfold edgeType; rw [localAngle_pts]
    simp only [ht]
    rw [hd]
    obtain ⟨u, hu⟩ := ρ.surjective (e.2 + 2)
    rw [← hu]
    obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos h
    have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
    fin_cases u
    · simp [h0, l0, hαβ, show α ≠ 2 * α + β by intro e; linarith]
    · simp [h1, l1, hαβ.symm, show β ≠ 2 * α + β by intro e; linarith]
    · simp [h2, l2, show 2 * α + β ≠ α by intro e; linarith, show 2 * α + β ≠ β by intro e; linarith]
  rw [← side_sum D j, Finset.sum_congr rfl fun e _ => hlen e, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, add_zero, nsmul_eq_mul, mul_zero, dEntry]

end TriangleTiling.ThreeAlpha
