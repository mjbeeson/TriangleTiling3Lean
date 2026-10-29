/-
`lemma:pigeonhole` of M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4).

The tile is general (possibly isosceles): only `γ > π/2` is used. Each tile has exactly one corner
with angle `γ` (two would add up to more than `π`), its edge opposite that corner is its `c`
edge, and a point inside a side of `ABC` carries at most one `γ`.
-/
import TriangleTiling.ThreeAlpha.DMatrix
import TriangleTiling.TwoCs.TwoCs

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry Set

variable {N : ℕ} (D : CongruentDissection N)

/-- **Lemma `lemma:pigeonhole`.** Suppose triangle `ABC` is `N`-tiled by a tile with angles
`(α, β, γ)` and `γ > π/2`. Suppose all the tiles along one side of `ABC` do not have their `c`
sides along that side of `ABC`. Then there is a tile with a `γ` angle at one of the endpoints of
that side of `ABC`.

The side is the one opposite vertex `j`, from `target.pts (j + 1)` to `target.pts (j + 2)`. -/
theorem pigeonhole {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) (hγ : Real.pi / 2 < γ)
    (j : Fin 3)
    (hno : ∀ (i : Fin N) (m : Fin 3),
      (D.tile i).edge m ⊆ segment ℝ (D.target.pts (j + 1)) (D.target.pts (j + 2)) →
        dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) ≠ c) :
    ∃ (i : Fin N) (l : Fin 3), ((D.tile i).pts l = D.target.pts (j + 1) ∨
      (D.tile i).pts l = D.target.pts (j + 2)) ∧ (D.tile i).angleAt l = γ := by
  classical
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  obtain ⟨hα, hβ, -, hsum⟩ := tileSides_angles D ⟨σ, h0, h1, h2, l0, l1, l2⟩
  have hπ := Real.pi_pos
  -- The model's `γ` is only at `σ 2`.
  have hmγ : ∀ x : Fin 3, D.model.angleAt x = γ → x = σ 2 := by
    intro x hx
    obtain ⟨y, rfl⟩ := σ.surjective x
    have : y = 0 ∨ y = 1 ∨ y = 2 := by fin_cases y <;> simp
    rcases this with rfl | rfl | rfl
    · rw [h0] at hx; linarith
    · rw [h1] at hx; linarith
    · rfl
  -- Each tile: its corner angles and edge lengths come from the model by a permutation.
  have hperm : ∀ i : Fin N, ∃ ρ : Equiv.Perm (Fin 3), (∀ k, (D.tile i).angleAt k =
      D.model.angleAt (ρ k)) ∧ ∀ x y, dist ((D.tile i).pts x) ((D.tile i).pts y) =
        dist (D.model.pts (ρ x)) (D.model.pts (ρ y)) := by
    intro i
    obtain ⟨ρ, hρa, hρd⟩ := corner_perm_dist (D.tiles_congruent i)
    exact ⟨ρ, fun k => (hρa k).symm, hρd⟩
  -- The edge opposite a `γ` corner has length `c`.
  have hcedge : ∀ (i : Fin N) (m : Fin 3), (D.tile i).angleAt (m + 2) = γ →
      dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = c := by
    intro i m hm
    obtain ⟨ρ, hρa, hρd⟩ := hperm i
    have hr : ρ (m + 2) = σ 2 := hmγ _ ((hρa _).symm.trans hm)
    rw [hρd, ← l2]
    unfold Tri.oppLen
    have d1 : ρ m ≠ ρ (m + 2) := ρ.injective.ne (by fin_cases m <;> decide)
    have d2 : ρ (m + 1) ≠ ρ (m + 2) := ρ.injective.ne (by fin_cases m <;> decide)
    have d3 : ρ m ≠ ρ (m + 1) := ρ.injective.ne (by fin_cases m <;> decide)
    rw [hr] at d1 d2
    rcases others _ _ _ d1.symm d2.symm d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact dist_comm _ _
  -- Each tile has one `γ` corner.
  have hγcorner : ∀ i : Fin N, ∃ k, (D.tile i).angleAt k = γ ∧
      ∀ k', (D.tile i).angleAt k' = γ → k' = k := by
    intro i
    obtain ⟨ρ, hρa, -⟩ := hperm i
    refine ⟨ρ.symm (σ 2), by rw [hρa, Equiv.apply_symm_apply, h2], fun k' hk' => ?_⟩
    have := hmγ _ ((hρa k').symm.trans hk')
    rw [← this, Equiv.symm_apply_apply]
  by_contra hnot
  push Not at hnot
  set A := D.target.pts (j + 1)
  set B := D.target.pts (j + 2)
  have hAB : A ≠ B := fun h => absurd (D.target.indep.injective h) (by fin_cases j <;> decide)
  obtain ⟨part, hcov, hdisj, -⟩ := D.toDissection.side_walk (j + 1)
  have hj : j + 1 + 1 = j + 2 := by fin_cases j <;> rfl
  rw [hj] at hcov
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B :=
    fun e he y hy => by rw [← hcov]; exact Set.mem_biUnion he hy
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1)
  have hchain := segment_chain_endpoints A B hAB part u v (fun e _ => tri_pts_succ_ne _ _)
    hcov hdisj
  set Eint := (part.image u ∪ part.image v).filter fun x => x ≠ A ∧ x ≠ B
  -- The `γ` corner of each tile on the side is at an end of its edge.
  choose kγ hkγ huniq using hγcorner
  have hend : ∀ e ∈ part, kγ e.1 = e.2 ∨ kγ e.1 = e.2 + 1 := by
    intro e he
    have hne : kγ e.1 ≠ e.2 + 2 := fun h =>
      hno e.1 e.2 (hsub e he) (hcedge e.1 e.2 (h ▸ hkγ e.1))
    revert hne; generalize kγ e.1 = x; generalize e.2 = y
    fin_cases x <;> fin_cases y <;> simp
  set φ : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (kγ e.1)
  have hφuv : ∀ e ∈ part, φ e = u e ∨ φ e = v e := by
    intro e he; rcases hend e he with h | h
    · left; simp only [φ, u, h]
    · right; simp only [φ, v, h]
  have hφseg : ∀ e ∈ part, φ e ∈ segment ℝ A B := by
    intro e he
    apply hsub e he
    rcases hφuv e he with h | h <;> rw [h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hφE : ∀ e ∈ part, φ e ∈ Eint := by
    intro e he
    refine Finset.mem_filter.mpr ⟨?_, fun h => hnot e.1 (kγ e.1) (Or.inl h) (hkγ e.1),
      fun h => hnot e.1 (kγ e.1) (Or.inr h) (hkγ e.1)⟩
    rcases hφuv e he with h | h <;> rw [h]
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
  -- Two tiles cannot both have their `γ` at a point inside the side.
  have hinj : Set.InjOn φ part := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e he) (h1 ▸ hsub e' he')
    · have hE := Finset.mem_filter.mp (hφE e he)
      have hfr : φ e ∈ frontier D.target.carrier := by
        have := tri_side_subset_frontier D.target (j + 1)
        rw [hj] at this
        exact this (hφseg e he)
      have hnc : φ e ∉ Set.range D.target.pts := by
        rintro ⟨l, hl⟩
        have h3 : l = j ∨ l = j + 1 ∨ l = j + 2 := by fin_cases j <;> fin_cases l <;> simp
        rcases h3 with rfl | rfl | rfl
        · have hseg := hφseg e he
          rw [← hl, segment_eq_image_lineMap] at hseg
          obtain ⟨t, -, ht⟩ := hseg
          exact TwoCs.vertex_ne_lineMap D.target (j' := l + 1) (j'' := l + 2)
            (by fin_cases l <;> decide) (by fin_cases l <;> decide) t ht.symm
        · exact hE.2.1 hl.symm
        · exact hE.2.2 hl.symm
      have hloc := D.target.localAngle_frontier hfr hnc
      have hs := sum_ge_two D.toDissection h1 (φ e)
      have ha1 : (D.tile e.1).localAngle (φ e) = γ := by
        simp only [φ]; rw [Tri.localAngle_vertex]; exact hkγ e.1
      have ha2 : (D.tile e'.1).localAngle (φ e) = γ := by
        rw [heq]; simp only [φ]; rw [Tri.localAngle_vertex]; exact hkγ e'.1
      rw [ha1, ha2, D.sum_localAngle_eq, hloc] at hs
      linarith
  have hcard : part.card ≤ Eint.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card fun x hx => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact hφE e he
  have := hchain.1
  omega

end TriangleTiling.ThreeAlpha
