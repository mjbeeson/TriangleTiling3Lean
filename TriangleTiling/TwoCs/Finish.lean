/-
The two endings of `lemma:twocs`, on the wall `PR` (side `g ≤ c`, away from Tile 1's `Q`).

* `noGamma_P` (fact (B)): no tile beyond `PR` with its edge inside `PR` has its `γ` at `P`.
* `finish_star`: if no other tile has its `γ` at `R` and no edge along `PR` passes through `R`,
  the pigeonhole on the wall gives a contradiction.
* `finish_1c`: if no edge along `PR` passes through `R`, the edges beyond `PR` are `a` and `b`
  edges; a `b` edge would be all of `PR`, with its `α` or `γ` at `P`, which is impossible; so `PR`
  is covered by `a` edges, and `b` is a multiple of `a`.
-/
import TriangleTiling.TwoCs.Basic
import Erdos634.CornerAnglePerm

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

/-- A point of `T` with two zero coordinates is the third vertex. -/
theorem eq_vertex_of_two_coords (T : Tri) {X : Plane} {i j l : Fin 3}
    (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (hi : T.basis.coord i X = 0)
    (hj : T.basis.coord j X = 0) : X = T.pts l := by
  have h := T.basis.linear_combination_coord_eq_self X
  have hs := Tri.coord_sum T X
  rw [Fin.sum_univ_three] at h
  have hl : T.basis.coord l X = 1 := by
    revert hij hli hlj hi hj; fin_cases i <;> fin_cases j <;> fin_cases l <;> simp <;>
      intros <;> linarith
  rw [← h]
  revert hij hli hlj hi hj hl; fin_cases i <;> fin_cases j <;> fin_cases l <;> simp <;>
    intro h1 h2 h3 <;> simp [h1, h2, h3, Tri.basis_apply']

/-- A point of the side `AB` other than `A, B` has positive coordinates at `A` and `B`. -/
theorem coords_of_side (T : Tri) {X : Plane} (hX : X ∈ segment ℝ (T.pts 0) (T.pts 1))
    (hXA : X ≠ T.pts 0) (hXB : X ≠ T.pts 1) :
    0 < T.basis.coord 0 X ∧ 0 < T.basis.coord 1 X := by
  have hc : X ∈ T.carrier := T.convex.segment_subset (subset_convexHull ℝ _ ⟨0, rfl⟩)
    (subset_convexHull ℝ _ ⟨1, rfl⟩) hX
  have h2 := coord_two_of_mem_side T hX
  have hn := (Tri.mem_carrier_iff_coord T X).mp hc
  constructor
  · rcases lt_or_eq_of_le (hn 0) with h | h
    · exact h
    · exact absurd (eq_vertex_of_two_coords T (i := 0) (j := 2) (l := 1) (by decide) (by decide)
        (by decide) h.symm h2) hXB
  · rcases lt_or_eq_of_le (hn 1) with h | h
    · exact h
    · exact absurd (eq_vertex_of_two_coords T (i := 1) (j := 2) (l := 0) (by decide) (by decide)
        (by decide) h.symm h2) hXA

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (hγ : Real.pi / 2 < tileγ D)

/-- The data at `P` (or `Q`): it is a corner with no `γ`, or a tile `T₀` has its `γ` there, with
its other vertex `X` on `AB` beyond it. -/
def PData (V W : Plane) : Prop :=
  angleCount D V (tileγ D) = 0 ∨
    ∃ (T₀ : Fin N) (jV jX : Fin 3), jX ≠ jV ∧ (D.tile T₀).pts jV = V ∧
      (D.tile T₀).localAngle V = tileγ D ∧
      D.target.basis.coord 2 ((D.tile T₀).pts jX) = 0 ∧
      ∠ ((D.tile T₀).pts jX) V W = Real.pi ∧ angleCount D V (tileγ D) ≤ 1

include hsep in
/-- **Fact (B).** No tile has its `γ` at `P` and an edge inside `PR` ending at... anywhere: such a
tile would have its other vertices on the rays `PX` and `PR`. -/
theorem noGamma_P {T₁ : Fin N} {jP jQ jR : Fin 3} (hPQ : jQ ≠ jP) (hPR : jR ≠ jP)
    (hQR : jQ ≠ jR) (hPα : (D.tile T₁).localAngle ((D.tile T₁).pts jP) = tileα D)
    (hR2 : 0 < D.target.basis.coord 2 ((D.tile T₁).pts jR))
    (hP2 : D.target.basis.coord 2 ((D.tile T₁).pts jP) = 0)
    (hPd : PData D ((D.tile T₁).pts jP) ((D.tile T₁).pts jQ))
    {e : Fin N × Fin 3}
    (hsubPR : (D.tile e.1).edge e.2 ⊆ segment ℝ ((D.tile T₁).pts jP) ((D.tile T₁).pts jR))
    (hγP : (D.tile e.1).localAngle ((D.tile T₁).pts jP) = tileγ D) : False := by
  set P := (D.tile T₁).pts jP
  set R := (D.tile T₁).pts jR
  have hne5 : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hsep.2.ne h
  have hγ0 : tileγ D ≠ 0 := hsep.1 2
  have hγπ : tileγ D ≠ Real.pi := hne5 2 3 (by decide)
  have hγ2π : tileγ D ≠ 2 * Real.pi := hne5 2 4 (by decide)
  have hPRne : P ≠ R := fun h => hPR ((D.tile T₁).indep.injective h).symm
  rcases hPd with h0 | ⟨T₀, jV, jX, hjX, hV, hγV, hX2, hXang, hle⟩
  · exact ne_of_angleCount_zero D h0 e.1 hγP
  have he1 : e.1 = T₀ := eq_of_angleCount_le_one D hle hγP hγV
  obtain ⟨mP, hmP⟩ := vertex_of_localAngle_corner (D.tile e.1) hγP
    hγ0 hγπ hγ2π
  -- Points of `PR` other than `P` are on the ray `PR`.
  have hray : ∀ y ∈ segment ℝ P R, y ≠ P → ∃ t : ℝ, 0 < t ∧ y = AffineMap.lineMap P R t := by
    intro y hy hyP
    rw [segment_eq_image_lineMap] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    refine ⟨t, lt_of_le_of_ne ht.1 ?_, rfl⟩
    rintro rfl; exact hyP (AffineMap.lineMap_apply_zero _ _)
  have hu : (D.tile e.1).pts e.2 ∈ segment ℝ P R := hsubPR (left_mem_segment _ _ _)
  have hv : (D.tile e.1).pts (e.2 + 1) ∈ segment ℝ P R := hsubPR (right_mem_segment _ _ _)
  have hf3 : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h01, h02, h12⟩ := hf3 e.2
  have hne : ∀ {x y : Fin 3}, x ≠ y → (D.tile e.1).pts x ≠ (D.tile e.1).pts y :=
    fun h e' => h ((D.tile e.1).indep.injective e')
  have h3 : mP = e.2 ∨ mP = e.2 + 1 ∨ mP = e.2 + 2 := by
    generalize e.2 = x; fin_cases mP <;> fin_cases x <;> simp
  -- The other end `Z` of the edge, on the ray `PR`; the vertex at `P` is `mP`.
  obtain ⟨jZ, hjZm, t, ht, hZ⟩ : ∃ jZ : Fin 3, jZ ≠ mP ∧ ∃ t : ℝ, 0 < t ∧
      (D.tile e.1).pts jZ = AffineMap.lineMap P R t := by
    rcases h3 with h | h | h
    · rw [h] at hmP
      obtain ⟨t, ht, hZ⟩ := hray _ hv (hmP ▸ hne h01.symm)
      exact ⟨e.2 + 1, by rw [h]; exact h01.symm, t, ht, hZ⟩
    · rw [h] at hmP
      obtain ⟨t, ht, hZ⟩ := hray _ hu (hmP ▸ hne h01)
      exact ⟨e.2, by rw [h]; exact h01, t, ht, hZ⟩
    · exfalso
      rw [h] at hmP
      obtain ⟨s, hs, hs'⟩ := hray _ hu (hmP ▸ hne h02)
      obtain ⟨s'', hs'', hs'''⟩ := hray _ hv (hmP ▸ hne h12)
      have := corner_angle_eq (D.tile e.1) (j := e.2 + 2) h02 h12 h01
      rw [hmP, hγP, hs', hs''', angle_ray hs'', angle_comm, angle_ray hs,
        angle_self_of_ne hPRne.symm] at this
      exact hγ0 this
  -- In `T₀`, `mP = jV`, and `X`, `Z` are its other two vertices.
  rw [he1] at hmP hZ
  have hmV : mP = jV := (D.tile T₀).indep.injective (hmP.trans hV.symm)
  rw [hmV] at hjZm
  have hXZ : jX ≠ jZ := by
    intro h
    rw [h, hZ, Tri.coord_lineMap, hP2] at hX2
    have : t * D.target.basis.coord 2 R = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  exact supp_contra D hsep hPQ hPR hQR rfl rfl rfl (Or.inl hPα) hXang hjX hjZm hXZ hV hγV
    one_pos ht (by rw [AffineMap.lineMap_apply_one]) hZ

/-- The open edge `PR` of a tile, as an edge `m`. -/
theorem openSegment_edge (T : Tri) {jP jR : Fin 3} (hPR : jR ≠ jP) :
    ∃ m : Fin 3, openSegment ℝ (T.pts jP) (T.pts jR) = openSegment ℝ (T.pts m) (T.pts (m + 1)) := by
  have : jR = jP + 1 ∨ jP = jR + 1 := by
    revert hPR; fin_cases jP <;> fin_cases jR <;> simp
  rcases this with h | h
  · exact ⟨jP, by rw [h]⟩
  · exact ⟨jR, by rw [h, openSegment_symm]⟩

include hsep hγ in
open Classical in
/-- **The ending by the pigeonhole on `PR`.** -/
theorem finish_star {T₁ : Fin N} {jP jQ jR : Fin 3} (hPQ : jQ ≠ jP) (hPR : jR ≠ jP)
    (hQR : jQ ≠ jR) (hPα : (D.tile T₁).localAngle ((D.tile T₁).pts jP) = tileα D)
    (hR2 : 0 < D.target.basis.coord 2 ((D.tile T₁).pts jR))
    (hP2 : D.target.basis.coord 2 ((D.tile T₁).pts jP) = 0)
    (hPd : PData D ((D.tile T₁).pts jP) ((D.tile T₁).pts jQ))
    (hPπ : angleCount D ((D.tile T₁).pts jP) Real.pi = 0)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgP : g ((D.tile T₁).pts jP) = c)
    (hgR : g ((D.tile T₁).pts jR) = c) (hgQ : c < g ((D.tile T₁).pts jQ))
    (hint : openSegment ℝ ((D.tile T₁).pts jP) ((D.tile T₁).pts jR) ⊆ interior D.target.carrier)
    (hlen : dist ((D.tile T₁).pts jP) ((D.tile T₁).pts jR) < dist (D.model.pts 0) (D.model.pts 1))
    (hR1 : ∀ i, i ≠ T₁ → (D.tile i).localAngle ((D.tile T₁).pts jR) ≠ tileγ D)
    (hRend : ∀ e ∈ D.lineChain g c, (D.tile T₁).pts jR ∉
      openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) : False := by
  set P := (D.tile T₁).pts jP
  set R := (D.tile T₁).pts jR
  have hπ := Real.pi_pos
  have hPRne : P ≠ R := fun h => hPR ((D.tile T₁).indep.injective h).symm
  obtain ⟨m, hm⟩ := openSegment_edge (D.tile T₁) hPR
  have hwall : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier := by
    rw [hm]; exact openEdge_not_interior D.toDissection T₁ m
  have hne1 : ∀ e ∈ D.lineChain g c, e.1 ≠ T₁ := lineChain_tile_ne D.toDissection g c hgQ
  refine wall_gamma D hsep hg hPRne hgP hgR (fun e he hP => ?_) hRend hint hwall
    (fun e he hsub h => ?_) (fun e he hsub h => ?_) (fun e he hsub h => hR1 e.1 (hne1 e he) h)
    (fun y hy => ?_)
  · -- `P` is inside no edge.
    obtain ⟨-, -, -⟩ := Dissection.mem_lineChain.mp he
    have := angleCount_pos D (Tri.localAngle_openSegment _ e.2 hP)
    omega
  · -- No `c` edge fits inside `PR`.
    have hl := edge_length D hsep e.1 e.2 2 h
    have hle := dist_le_of_mem_segment₂ (hsub (left_mem_segment _ _ _))
      (hsub (right_mem_segment _ _ _))
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
    linarith
  · exact noGamma_P D hsep hPQ hPR hQR hPα hR2 hP2 hPd hsub h
  · -- At most one `γ` inside `PR`.
    by_contra hlt
    push Not at hlt
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have hyπ : (D.tile T₁).localAngle y = Real.pi := by
      rw [hm] at hy; exact Tri.localAngle_openSegment _ m hy
    have hiT : i ≠ T₁ := fun h => by
      rw [h, hyπ] at hi; exact (hsep.2.ne (by decide : (2 : Fin 5) ≠ 3)) hi.symm
    have hjT : j ≠ T₁ := fun h => by
      rw [h, hyπ] at hj; exact (hsep.2.ne (by decide : (2 : Fin 5) ≠ 3)) hj.symm
    have := sum_three_le D hiT.symm hjT.symm hij y
    rw [hyπ, hi, hj] at this
    linarith

include hsep in
open Classical in
/-- **The ending of Case 1c**: `PR` is covered by `a` edges, so `b` is a multiple of `a`. -/
theorem finish_1c {T₁ : Fin N} {jP jQ jR : Fin 3} (hPQ : jQ ≠ jP) (hPR : jR ≠ jP)
    (hQR : jQ ≠ jR) (hPα : (D.tile T₁).localAngle ((D.tile T₁).pts jP) = tileα D)
    (hR2 : 0 < D.target.basis.coord 2 ((D.tile T₁).pts jR))
    (hP2 : D.target.basis.coord 2 ((D.tile T₁).pts jP) = 0)
    (hPd : PData D ((D.tile T₁).pts jP) ((D.tile T₁).pts jQ))
    (hPπ : angleCount D ((D.tile T₁).pts jP) Real.pi = 0)
    (hPα1 : angleCount D ((D.tile T₁).pts jP) (tileα D) ≤ 1)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgP : g ((D.tile T₁).pts jP) = c)
    (hgR : g ((D.tile T₁).pts jR) = c) (hgQ : c < g ((D.tile T₁).pts jQ))
    (hint : openSegment ℝ ((D.tile T₁).pts jP) ((D.tile T₁).pts jR) ⊆ interior D.target.carrier)
    (hPRb : dist ((D.tile T₁).pts jP) ((D.tile T₁).pts jR) = dist (D.model.pts 2) (D.model.pts 0))
    (hbc : dist (D.model.pts 2) (D.model.pts 0) < dist (D.model.pts 0) (D.model.pts 1))
    (hiv : ¬ ∃ n : ℕ, dist (D.model.pts 2) (D.model.pts 0) =
      n * dist (D.model.pts 1) (D.model.pts 2))
    (hRend : ∀ e ∈ D.lineChain g c, (D.tile T₁).pts jR ∉
      openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) : False := by
  set P := (D.tile T₁).pts jP
  set R := (D.tile T₁).pts jR
  have hπ := Real.pi_pos
  have hPRne : P ≠ R := fun h => hPR ((D.tile T₁).indep.injective h).symm
  obtain ⟨m, hm⟩ := openSegment_edge (D.tile T₁) hPR
  have hwall : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier := by
    rw [hm]; exact openEdge_not_interior D.toDissection T₁ m
  have hne1 : ∀ e ∈ D.lineChain g c, e.1 ≠ T₁ := lineChain_tile_ne D.toDissection g c hgQ
  have hendP : ∀ e ∈ D.lineChain g c,
      P ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he hP
    have := angleCount_pos D (Tri.localAngle_openSegment _ e.2 hP)
    omega
  have hsum := chain_sum D.toDissection hg hPRne hgP hgR hendP hRend hint hwall
  set S := (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R)
  -- Every edge of `S` is an `a` edge.
  have ha : ∀ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.model.pts 1) (D.model.pts 2) := by
    intro e he
    obtain ⟨he1, hsub⟩ := Finset.mem_filter.mp he
    have hle := dist_le_of_mem_segment₂ (hsub (left_mem_segment _ _ _))
      (hsub (right_mem_segment _ _ _))
    rcases corner_mem D hsep e.1 (e.2 + 2) with h | h | h
    · have := edge_length D hsep e.1 e.2 0 h
      simpa using this
    · -- a `b` edge would be all of `PR`
      exfalso
      have hl := edge_length D hsep e.1 e.2 1 h
      rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl] at hl
      obtain ⟨jPe, hjPe, hjmem⟩ : ∃ j : Fin 3, (D.tile e.1).pts j = P ∧ (j = e.2 ∨ j = e.2 + 1) := by
        rcases endpoints_of_full_subsegment hPRne (hsub (left_mem_segment _ _ _))
          (hsub (right_mem_segment _ _ _)) (by rw [hl, hPRb]) with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact ⟨e.2, h1, Or.inl rfl⟩
        · exact ⟨e.2 + 1, h1, Or.inr rfl⟩
      have hf3 : ∀ x : Fin 3, x + 2 ≠ x ∧ x + 2 ≠ x + 1 := by decide
      rcases corner_mem D hsep e.1 jPe with h' | h' | h' <;> rw [hjPe] at h'
      · exact hne1 e he1 (eq_of_angleCount_le_one D hPα1 h' hPα)
      · rw [← hjPe] at h'
        have := corner_unique D hsep e.1 (Or.inr (Or.inl rfl)) h h'
        rcases hjmem with h2 | h2 <;> rw [h2] at this
        · exact (hf3 e.2).1 this
        · exact (hf3 e.2).2 this
      · exact noGamma_P D hsep hPQ hPR hQR hPα hR2 hP2 hPd hsub h'
    · exfalso
      have hl := edge_length D hsep e.1 e.2 2 h
      rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
      linarith
  rw [Finset.sum_congr rfl ha, Finset.sum_const, nsmul_eq_mul, hPRb] at hsum
  exact hiv ⟨S.card, hsum.symm⟩

end TriangleTiling.TwoCs
