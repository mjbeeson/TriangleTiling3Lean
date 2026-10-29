/-
"What is the least N permitting a tiling?", from Section 10 of M. Beeson,
*Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:qandrnotzero` is `qandrnotzero`.

The tiles supported by a side of `ABC` are given by Bonfioli's `side_partition`: a finite set
`part` of pairs `(tile, edge index)` whose edges cover the side and pairwise meet in at most one
point. Edge `k` of a tile joins its vertices `k` and `k + 1`, and is opposite vertex `k + 2`; so
"the tile has its `b` edge on the side" is "its angle at vertex `k + 2` is `β`".

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2`.
-/
import TriangleTiling.Isosceles.StarsAndCenters
import TriangleTiling.Isosceles.AreaEquation
import TriangleTiling.Tiling.SegmentChain

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- A side of a triangle lies in its frontier. -/
theorem tri_side_subset_frontier (T : Tri) (i : Fin 3) :
    segment ℝ (T.pts i) (T.pts (i + 1)) ⊆ frontier T.carrier := by
  intro x hx
  have hcar : x ∈ T.carrier := T.convex.segment_subset
    (subset_convexHull ℝ _ ⟨i, rfl⟩) (subset_convexHull ℝ _ ⟨i + 1, rfl⟩) hx
  refine ⟨subset_closure hcar, fun hint => ?_⟩
  have hpos := (T.mem_interior_iff_coord_pos x).mp hint (i + 2)
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, -, rfl⟩ := hx
  rw [AffineMap.apply_lineMap] at hpos
  have h1 : T.basis.coord (i + 2) (T.pts i) = 0 := by
    have : T.pts i = T.basis i := rfl
    rw [this, AffineBasis.coord_apply_ne]; fin_cases i <;> decide
  have h2 : T.basis.coord (i + 2) (T.pts (i + 1)) = 0 := by
    have : T.pts (i + 1) = T.basis (i + 1) := rfl
    rw [this, AffineBasis.coord_apply_ne]; fin_cases i <;> decide
  rw [h1, h2, AffineMap.lineMap_same_apply] at hpos
  exact lt_irrefl _ hpos

theorem fin3_ne_add_one : ∀ k : Fin 3, k ≠ k + 1 := by decide

/-- No triangle has two of its edges on one segment. -/
theorem tri_two_edges_on_segment (T : Tri) {A B : Plane} {k k' : Fin 3} (hkk : k ≠ k')
    (hk : T.edge k ⊆ segment ℝ A B) (hk' : T.edge k' ⊆ segment ℝ A B) : False := by
  have hend : ∀ m : Fin 3, T.pts m ∈ T.edge m ∧ T.pts (m + 1) ∈ T.edge m :=
    fun m => ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
  have hall : ∀ j, T.pts j ∈ segment ℝ A B := by
    intro j
    fin_cases k <;> fin_cases k' <;> fin_cases j <;> simp at hkk <;>
      first
      | exact hk (hend _).1 | exact hk (hend _).2
      | exact hk' (hend _).1 | exact hk' (hend _).2
  have hline : ∀ j, T.pts j ∈ line[ℝ, A, B] :=
    fun j => (mem_segment_iff_wbtw.mp (hall j)).mem_affineSpan
  have hcol := collinear_insert_insert_insert_of_mem_affineSpan_pair (hline 0) (hline 1) (hline 2)
  have : Collinear ℝ {T.pts 0, T.pts 1, T.pts 2} :=
    hcol.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  exact (affineIndependent_iff_not_collinear_set.mp (tri_indep T)) this

/-- **The side pigeonhole, general form.** Let `part` be the tile edges on side `i` of the
target, from `P₀` to `P₁`. Suppose every tile of `part` has local angle `θ` at an endpoint of its
edge, neither at `P₀` nor at `P₁`, and at each point of the side at most one tile has local
angle `θ`. That is impossible: these would be `|part|` distinct points strictly inside the side,
but `p` edges meet at only `p - 1` points inside it. -/
theorem side_pigeonhole {N : ℕ} (D : CongruentDissection N) (θ : ℝ) (i : Fin 3)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hcorner : ∀ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = θ ∨
      (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) = θ)
    (hAθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts i ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts i) →
        (D.tile e.1).localAngle (D.target.pts i) ≠ θ)
    (hBθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts (i + 1) ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts (i + 1)) →
        (D.tile e.1).localAngle (D.target.pts (i + 1)) ≠ θ)
    (htwo : ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card ≤ 1) : False := by
  classical
  set A := D.target.pts i
  set B := D.target.pts (i + 1)
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2 with hu
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1) with hv
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy
    rw [← hcov]
    exact Set.mem_biUnion he hy
  let φ : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).localAngle (u e) = θ then u e else v e
  have hφθ : ∀ e ∈ part, (D.tile e.1).localAngle (φ e) = θ := by
    intro e he
    simp only [φ]
    split_ifs with h
    · exact h
    · exact (hcorner e he).resolve_left h
  have hφuv : ∀ e, φ e = u e ∨ φ e = v e := by
    intro e; simp only [φ]; split_ifs <;> simp
  -- `φ e` lies inside `AB`, away from `A` and `B`.
  set Eint := (part.image u ∪ part.image v).filter fun x => x ≠ A ∧ x ≠ B
  have hφE : ∀ e ∈ part, φ e ∈ Eint := by
    intro e he
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · rcases hφuv e with h | h <;> rw [h]
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    · intro h
      refine hAθ e he ?_ (h ▸ hφθ e he)
      rcases hφuv e with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · exact Or.inr (h'.symm.trans h)
    · intro h
      refine hBθ e he ?_ (h ▸ hφθ e he)
      rcases hφuv e with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · exact Or.inr (h'.symm.trans h)
  -- `φ` is injective on `part`.
  have hinj : Set.InjOn φ part := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e he) (h1 ▸ hsub e' he')
    · have hP : φ e ∈ segment ℝ A B := by
        apply hsub e he
        rcases hφuv e with h | h <;> rw [h]
        · exact left_mem_segment _ _ _
        · exact right_mem_segment _ _ _
      have hcard := htwo (φ e) hP
      have : 1 < (Finset.univ.filter fun i => (D.tile i).localAngle (φ e) = θ).card :=
        Finset.one_lt_card.mpr ⟨e.1, by simp [hφθ e he], e'.1,
          by simp [heq, hφθ e' he'], h1⟩
      omega
  have hle := Finset.card_le_card_of_injOn φ hφE hinj
  -- But the edges of `part` meet at most `|part| - 1` times inside `AB`.
  have hAB : A ≠ B := D.target.indep.injective.ne (fin3_ne_add_one i)
  have huv : ∀ e ∈ part, u e ≠ v e :=
    fun e _ => (D.tile e.1).indep.injective.ne (fin3_ne_add_one e.2)
  have hchain : Eint.card + 1 ≤ part.card :=
    (segment_chain_endpoints A B hAB part u v huv hcov hdisj).1
  omega

/-- **The side pigeonhole.** Let `part` be the tile edges on the side from `P₀ = target.pts i`
to `P₁ = target.pts (i + 1)`. Suppose the tile of `part` ending at `P₀` does not have its angle
`θ` at `P₀`, the tile of `part` ending at `P₁` does not have its angle `θ` at `P₁`, and at each
point of the side at most one tile has its angle `θ`. Then some tile of `part` has its angle `θ`
opposite its edge on the side. (Otherwise each tile of `part` has its `θ` at an endpoint of its
edge strictly inside the side, at distinct points; but `p` edges meet at only `p - 1` points
inside the side.) -/
theorem side_has_edge {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (θ : ℝ)
    (hθ : θ = tileβ D ∨ θ = tileγ D) (i : Fin 3) (part : Finset (Fin N × Fin 3))
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
  set A := D.target.pts i
  set B := D.target.pts (i + 1)
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2 with hu
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1) with hv
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy
    rw [← hcov]
    exact Set.mem_biUnion he hy
  -- Each tile of `part` has its `θ` corner at an endpoint of its edge on `AB`.
  have hcorner : ∀ e ∈ part, (D.tile e.1).localAngle (u e) = θ ∨
      (D.tile e.1).localAngle (v e) = θ := by
    intro e he
    have hcnt := tile_angle_count D hγ hirr e.1
    have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile e.1).pts (k + 1))
        ((D.tile e.1).pts k) ((D.tile e.1).pts (k + 2)) = θ).card = 1 := by
      rcases hθ with rfl | rfl
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

/-- **Lemma `lemma:qandrnotzero`.** Let `ABC` (base `AC`, base angles `α ∉ ℚπ`) be tiled by a
tile with angles `(α, β, 2α)`, and suppose the tile at `B` supported by `AB` has its `α` angle
at `B`. Write `|AB| = p a + q b + r c` according to the tiles supported by `AB`. Then `q ≠ 0`
and `r ≠ 0`: some tile supported by `AB` has its `b` edge on `AB`, and some has its `c` edge
there. -/
theorem qandrnotzero {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hB : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) = tileα D) :
    (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D) ∧
    (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D) := by
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  -- The angle counts at `A` (angle `α`) and at `B` (angle `π - 2α`).
  have hTsum := cornerAngle_sum D.target
  have hlocA : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    have : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
    rw [this]; push_cast; ring
  have hlocB : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
    have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
      rw [cornerAngle, angle_comm]; exact hC
    push_cast; linarith
  have rA := vertex_relations D hγ hirr _ 1 0 hlocA
  have rB := vertex_relations D hγ hirr _ (-2) 1 hlocB
  have none : ∀ (P : Plane) (θ : ℝ), angleCount D P θ = 0 → ∀ i, (D.tile i).localAngle P ≠ θ := by
    intro P θ h i hi
    have : i ∈ Finset.univ.filter fun i => (D.tile i).localAngle P = θ := by simp [hi]
    rw [angleCount, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  have hβA : angleCount D (D.target.pts 0) (tileβ D) = 0 := by omega
  have hγA : angleCount D (D.target.pts 0) (tileγ D) = 0 := by omega
  have hγB : angleCount D (D.target.pts 1) (tileγ D) = 0 := by
    have : angleCount D (D.target.pts 1) (tileβ D) ≤ 1 := by omega
    interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
  have hfr : ∀ P ∈ segment ℝ (D.target.pts 0) (D.target.pts 1), P ∈ frontier D.target.carrier :=
    fun P hP => tri_side_subset_frontier D.target 0 hP
  have htb := fun P hP => twobeta D hγ hirr hA hC (hfr P hP)
  refine ⟨side_has_edge D hγ hirr _ (Or.inl rfl) 0 part hcov hdisj
      (fun e _ _ => none _ _ hβA e.1) ?_ (fun P hP => (htb P hP).1),
    side_has_edge D hγ hirr _ (Or.inr rfl) 0 part hcov hdisj (fun e _ _ => none _ _ hγA e.1)
      (fun e _ _ => none _ _ hγB e.1) (fun P hP => (htb P hP).2)⟩
  intro e he hend h
  have h' : (D.tile e.1).localAngle (D.target.pts 1) = tileβ D := h
  rw [hB e he hend] at h'
  exact hinj.ne (show (0 : Fin 5) ≠ 1 by decide) h'

end TriangleTiling
