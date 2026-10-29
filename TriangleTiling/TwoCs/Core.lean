/-
The core of `lemma:twocs` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv
1206.2229v4): the side `AB` (`target.pts 0`, `target.pts 1`) does not carry exactly one `c` edge.

Notation as in the proof: Tile 1 is the tile `eT.1` with the `c` edge `PQ` on `AB`, its `α` at `P`,
`β` at `Q`, `γ` at `R`. The tile across `QR` at `Q` ("Tile 4") either has `R` inside an edge, or
`QR` lies on a side of `ABC`, and then the tiles beyond `PR` give too many angles `γ` (the
pigeonhole on the wall `PR`); or Tile 4 has its `β` at `Q = C` and its `a` edge on `QR` (Case 1c),
and then the tiles beyond `PR` all have their `a` edges on it, so `b` is a multiple of `a`.
-/
import TriangleTiling.TwoCs.Finish

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

variable {N : ℕ} (D : CongruentDissection N)

open Classical in
/-- **The core of `lemma:twocs`.** -/
theorem twocs_core (hsep : AnglesSep D) (hγ : Real.pi / 2 < tileγ D)
    (hirr : ¬ ∃ q : ℚ, tileα D = (q : ℝ) * tileβ D) (hαβ : tileα D < tileβ D)
    (hcorner : ∀ k, D.target.localAngle (D.target.pts k) < tileγ D)
    (hiv : ((¬ ∃ n : ℕ, dist (D.model.pts 1) (D.model.pts 2) =
          n * dist (D.model.pts 2) (D.model.pts 0)) ∧
        (¬ ∃ n : ℕ, dist (D.model.pts 2) (D.model.pts 0) =
          n * dist (D.model.pts 1) (D.model.pts 2))) ∨
      (∀ V, (V = D.target.pts 0 ∨ V = D.target.pts 1) →
        angleCount D V (tileα D) ≤ 1 ∧ angleCount D V (tileβ D) ≤ 1))
    (hsingle : dist (D.target.pts 0) (D.target.pts 1) ≠ dist (D.model.pts 0) (D.model.pts 1))
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (eT : Fin N × Fin 3)
    (heT : part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D) = {eT}) : False := by
  -- The tile, its angles and sides.
  set a := dist (D.model.pts 1) (D.model.pts 2)
  set b := dist (D.model.pts 2) (D.model.pts 0)
  set c := dist (D.model.pts 0) (D.model.pts 1)
  set A := D.target.pts 0
  set B := D.target.pts 1
  obtain ⟨hα0, hβ0, hγ0⟩ := angles_pos D hsep
  have hsum := tile_angle_sum D
  have hπ := Real.pi_pos
  obtain ⟨hab, hbc⟩ := sides_lt D hsep hγ hαβ
  have hne5 : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hsep.2.ne h
  have hαβ' : tileα D ≠ tileβ D := hne5 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := hne5 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := hne5 1 2 (by decide)
  have hγπ : tileγ D ≠ Real.pi := hne5 2 3 (by decide)
  have heTp : eT ∈ part := by
    have : eT ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := by rw [heT]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).1
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B :=
    fun e he y hy => by rw [← hcov]; exact Set.mem_biUnion he hy
  set T₁ := eT.1
  set k := eT.2
  have hRγ : (D.tile T₁).localAngle ((D.tile T₁).pts (k + 2)) = tileγ D := by
    have : eT ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := by rw [heT]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).2
  -- The ends of the `c` edge carry `α` and `β`.
  have hk2 : ∀ j : Fin 3, j ≠ k + 2 → (D.tile T₁).localAngle ((D.tile T₁).pts j) ≠ tileγ D :=
    fun j hj h => hj (corner_unique D hsep T₁ (Or.inr (Or.inr rfl)) h hRγ)
  have hf3 : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  have hf4 : ∀ x : Fin 3, x + 1 + 1 = x + 2 ∧ x + 1 + 2 = x ∧ x + 2 + 1 = x ∧ x + 2 + 2 = x + 1 := by
    decide
  obtain ⟨hk01, hk02, hk12⟩ := hf3 k
  have hkk : ∀ j : Fin 3, j ≠ k + 2 → (D.tile T₁).localAngle ((D.tile T₁).pts j) = tileα D ∨
      (D.tile T₁).localAngle ((D.tile T₁).pts j) = tileβ D := by
    intro j hj
    rcases corner_mem D hsep T₁ j with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hk2 j hj)
  obtain ⟨jP, jQ, hidx, hPα, hQβ⟩ : ∃ jP jQ : Fin 3, ((jP = k ∧ jQ = k + 1) ∨ (jP = k + 1 ∧ jQ = k)) ∧
      (D.tile T₁).localAngle ((D.tile T₁).pts jP) = tileα D ∧
      (D.tile T₁).localAngle ((D.tile T₁).pts jQ) = tileβ D := by
    rcases hkk k hk02 with h1 | h1 <;> rcases hkk (k + 1) hk12 with h2 | h2
    · exact absurd (corner_unique D hsep T₁ (Or.inl rfl) h1 h2) hk01
    · exact ⟨k, k + 1, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨k + 1, k, Or.inr ⟨rfl, rfl⟩, h2, h1⟩
    · exact absurd (corner_unique D hsep T₁ (Or.inr (Or.inl rfl)) h1 h2) hk01
  set jR := k + 2
  have hPQ : jQ ≠ jP := by rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hk01.symm; exact hk01]
  have hPR : jR ≠ jP := by rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hk02.symm; exact hk12.symm]
  have hQR : jQ ≠ jR := by rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hk12; exact hk02]
  set P := (D.tile T₁).pts jP
  set Q := (D.tile T₁).pts jQ
  set R := (D.tile T₁).pts jR
  have hPne : ∀ {x y : Fin 3}, x ≠ y → (D.tile T₁).pts x ≠ (D.tile T₁).pts y :=
    fun h e => h ((D.tile T₁).indep.injective e)
  -- The `c` edge is `PQ`, on `AB`.
  have hPQend : ((D.tile T₁).pts k = P ∧ (D.tile T₁).pts (k + 1) = Q) ∨
      ((D.tile T₁).pts k = Q ∧ (D.tile T₁).pts (k + 1) = P) := by
    rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hQPend : ((D.tile T₁).pts k = Q ∧ (D.tile T₁).pts (k + 1) = P) ∨
      ((D.tile T₁).pts k = P ∧ (D.tile T₁).pts (k + 1) = Q) := hPQend.symm
  have hedgeT : (D.tile T₁).edge k = segment ℝ P Q := by
    rcases hPQend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Tri.edge, h1, h2]
    · rw [Tri.edge, h1, h2, segment_symm]
  have hsubT : segment ℝ P Q ⊆ segment ℝ A B := hedgeT ▸ hsub eT heTp
  have hPside : P ∈ segment ℝ A B := hsubT (left_mem_segment _ _ _)
  have hQside : Q ∈ segment ℝ A B := hsubT (right_mem_segment _ _ _)
  -- `R` is off the line `AB`.
  have hR2 : 0 < D.target.basis.coord 2 R := by
    have hRt := pts_mem_target D.toDissection T₁ jR
    rcases (lt_or_eq_of_le ((Tri.mem_carrier_iff_coord _ _).mp hRt 2)) with h | h
    · exact h
    · exfalso
      have hRs : R ∈ segment ℝ A B := mem_side_of_coord_two D.target hRt h.symm
      have h1 : (D.tile T₁).edge (k + 1) ⊆ segment ℝ A B := by
        rw [Tri.edge, (hf4 k).1]
        refine (convex_segment A B).segment_subset ?_ hRs
        rcases hPQend with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
        · exact hQside
        · exact hPside
      exact tri_two_edges_on_segment (D.tile T₁) hk01 (hedgeT ▸ hsubT) h1
  -- The lengths: `|PR| = b`, `|QR| = a`.
  have hPRb : dist P R = b := by
    have := edge_length D hsep T₁ (jQ + 1) 1 (by
      rw [(hf4 jQ).2.1]; exact hQβ)
    rw [(hf4 jQ).1, dist_opp _ hPQ.symm hQR.symm hPR.symm] at this
    simpa using this
  have hQRa : dist Q R = a := by
    have := edge_length D hsep T₁ (jP + 1) 0 (by
      rw [(hf4 jP).2.1]; exact hPα)
    rw [(hf4 jP).1, dist_opp _ hPQ hPR hQR] at this
    simpa using this
  have hPQc : dist P Q = c := by
    have := edge_length D hsep T₁ k 2 hRγ
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at this
    rcases hPQend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact this
    · rw [← h1, ← h2, dist_comm]; exact this
  have hP2 : D.target.basis.coord 2 P = 0 := coord_two_of_mem_side _ hPside
  have hQ2 : D.target.basis.coord 2 Q = 0 := coord_two_of_mem_side _ hQside
  have hAB : A ≠ B := D.target.indep.injective.ne (by decide)
  -- The data at the ends of the `c` edge.
  have hinfo : ∀ V W : Plane, (((D.tile T₁).pts k = V ∧ (D.tile T₁).pts (k + 1) = W) ∨
      ((D.tile T₁).pts k = W ∧ (D.tile T₁).pts (k + 1) = V)) → V ∈ segment ℝ A B →
      PData D V W ∧ angleCount D V Real.pi = 0 ∧ ((V = A ∨ V = B) ∨
        (angleCount D V (tileα D) = 1 ∧ angleCount D V (tileβ D) = 1 ∧ V ≠ A ∧ V ≠ B)) := by
    intro V W hVW hVs
    by_cases hc : V = A ∨ V = B
    · obtain ⟨k', hk'⟩ : ∃ k' : Fin 3, V = D.target.pts k' := by
        rcases hc with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      obtain ⟨c1, c2, -⟩ := corner_counts D hsep hγ k' (hcorner k')
      rw [← hk'] at c1 c2
      exact ⟨Or.inl c1, c2, Or.inl hc⟩
    · push Not at hc
      obtain ⟨T₀, jV, jX, hjX, hV, hγV, hXs, hXang⟩ :=
        side_data D hsep hγ hcorner part hcov hdisj eT heT hVW hc.1 hc.2
      have hfr := tri_side_subset_frontier D.target 0 hVs
      have hnc : V ∉ Set.range D.target.pts := by
        rintro ⟨j, hj⟩
        fin_cases j
        · exact hc.1 hj.symm
        · exact hc.2 hj.symm
        · have := coord_two_of_mem_side _ hVs
          rw [← hj, Tri.coord_vertex] at this
          simp at this
      obtain ⟨c1, c2, c3, c4, -⟩ := side_counts D hsep hγ hirr hfr hnc (angleCount_pos D hγV)
      exact ⟨Or.inr ⟨T₀, jV, jX, hjX, hV, hγV, coord_two_of_mem_side _ hXs, hXang, c3.le⟩, c4,
        Or.inr ⟨c1, c2, hc⟩⟩
  obtain ⟨hPd, hPπ, hPc⟩ := hinfo P Q hPQend hPside
  obtain ⟨hQd, hQπ, hQc⟩ := hinfo Q P hQPend hQside
  -- If `Q` is a corner, `P` is not (else `AB` would be the single `c` edge `PQ`).
  have hPnc : (Q = A ∨ Q = B) →
      angleCount D P (tileα D) = 1 ∧ angleCount D P (tileβ D) = 1 ∧ P ≠ A ∧ P ≠ B := by
    intro hQ
    rcases hPc with hP | hP
    · exfalso
      have hPQne : P ≠ Q := hPne hPQ.symm
      apply hsingle
      rw [← hPQc]
      rcases hP with hP | hP <;> rcases hQ with hQ | hQ
      · exact absurd (hP.trans hQ.symm) hPQne
      · rw [hP, hQ]
      · rw [hP, hQ, dist_comm]
      · exact absurd (hP.trans hQ.symm) hPQne
    · exact hP
  -- The line `PR`, with `Q` on the side `g > c`.
  obtain ⟨g, cc, hg, hgP, hgR, hgQ⟩ := edge_level (D.tile T₁) hPQ hPR hQR
  have hne1 : ∀ e ∈ D.lineChain g cc, e.1 ≠ T₁ := lineChain_tile_ne D.toDissection g cc hgQ
  have hRt := pts_mem_target D.toDissection T₁ jR
  have hPt := pts_mem_target D.toDissection T₁ jP
  have hQt := pts_mem_target D.toDissection T₁ jQ
  have hγRne : ∀ {i : Fin N} {x : Plane}, (D.tile i).localAngle x = Real.pi →
      (D.tile i).localAngle x ≠ tileγ D := fun h h' => hγπ (h'.symm.trans h)
  have hlen : dist P R < c := by rw [hPRb]; exact hbc
  -- **The case `R` inside an edge of a tile `j'` at `Q`.**
  have hRpi : ∀ (j' : Fin N) (m' : Fin 3), j' ≠ T₁ →
      ((D.tile j').pts m' = Q ∨ (D.tile j').pts (m' + 1) = Q) →
      R ∈ openSegment ℝ ((D.tile j').pts m') ((D.tile j').pts (m' + 1)) → False := by
    intro j' m' hj' hQm hRm
    have hj'π := Tri.localAngle_openSegment _ m' hRm
    have hRint : R ∈ interior D.target.carrier := by
      apply mem_interior_of_sum_gt D.toDissection
      have := sum_ge_two D.toDissection hj'.symm R
      rw [hRγ, hj'π] at this
      linarith
    refine finish_star D hsep hγ hPQ hPR hQR hPα hR2 hP2 hPd hPπ hg hgP hgR hgQ
      (openSegment_subset_interior D.target hPt hRt fun j => Or.inr
        (coord_pos_of_interior _ hRint j)) hlen (fun i hi h => ?_) (fun e he hR => ?_)
    · have hij : i ≠ j' := by rintro rfl; exact hγRne hj'π h
      have := sum_three_le D hj'.symm hi.symm hij.symm R
      rw [hRγ, hj'π, h] at this
      linarith
    · have he1 := hne1 e he
      by_cases hej : e.1 = j'
      · have hm := Tri.openSegment_edge_unique (D.tile j') hRm (hej ▸ hR)
        have hee : e = (j', m') := Prod.ext hej hm.symm
        obtain ⟨a1, a2, -⟩ := Dissection.mem_lineChain.mp he
        rw [hee] at a1 a2
        rcases hQm with h | h
        · rw [h] at a1; linarith
        · rw [h] at a2; linarith
      · have hπe := Tri.localAngle_openSegment _ e.2 hR
        have := sum_three_le D hj'.symm he1.symm (fun h => hej h.symm) R
        rw [hRγ, hj'π, hπe] at this
        linarith
  by_cases hL : ∀ j, 0 < D.target.basis.coord j Q ∨ 0 < D.target.basis.coord j R
  · -- **Case A**: the open segment `QR` is interior.
    have hQRint := openSegment_subset_interior D.target hQt hRt hL
    obtain ⟨mQR, hmQRi⟩ : ∃ m : Fin 3, (m = jQ ∧ m + 1 = jR) ∨ (m = jR ∧ m + 1 = jQ) :=
      (by decide : ∀ q r : Fin 3, q ≠ r → ∃ m : Fin 3, (m = q ∧ m + 1 = r) ∨ (m = r ∧ m + 1 = q))
        jQ jR hQR
    have hmQR : ((D.tile T₁).pts mQR = Q ∧ (D.tile T₁).pts (mQR + 1) = R) ∨
        ((D.tile T₁).pts mQR = R ∧ (D.tile T₁).pts (mQR + 1) = Q) := by
      rcases hmQRi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
      · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
    set eQR : Fin N × Fin 3 := (T₁, mQR)
    have heQR : eQR ∈ edgesAt D.toDissection Q := by
      rw [mem_edgesAt]; rcases hmQR with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have hfar : farEnd D.toDissection Q eQR = R := by
      simp only [farEnd, eQR]
      rcases hmQR with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1, h2]
      · rw [if_neg (by rw [h1]; exact hPne hQR.symm), h1]
    have hmid : AffineMap.lineMap Q (farEnd D.toDissection Q eQR) (1 / 2 : ℝ) ∈
        interior D.target.carrier := by
      rw [hfar]; apply hQRint; rw [openSegment_eq_image_lineMap]
      exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    by_cases hray : ∃ e' ∈ edgesAt D.toDissection Q, e' ≠ eQR ∧
        SameRayAt D.toDissection Q eQR e'
    · obtain ⟨e', he', hne', t, ht, hZ⟩ := hray
      rw [hfar] at hZ
      set Z := farEnd D.toDissection Q e'
      -- The indices of `Q`, `Z` and the opposite corner in the tile `j' = e'.1`.
      obtain ⟨jq, jz, hjqz, hjq, hjz, hmem⟩ : ∃ jq jz : Fin 3, jq ≠ jz ∧ (D.tile e'.1).pts jq = Q ∧
          (D.tile e'.1).pts jz = Z ∧ ((jq = e'.2 ∧ jz = e'.2 + 1) ∨ (jq = e'.2 + 1 ∧ jz = e'.2)) := by
        rcases edgesAt_ends D.toDissection he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨e'.2, e'.2 + 1, fin3_ne_add_one _, h1, h2, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨e'.2 + 1, e'.2, (fin3_ne_add_one _).symm, h2, h1, Or.inr ⟨rfl, rfl⟩⟩
      obtain ⟨h01, h02, h12⟩ := hf3 e'.2
      have hjo1 : e'.2 + 2 ≠ jq := by
        rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact h02.symm
        · exact h12.symm
      have hjo2 : e'.2 + 2 ≠ jz := by
        rcases hmem with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact h12.symm
        · exact h02.symm
      -- `R` is inside `e'` when `e'` is longer than `QR`.
      have hlong : a < dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) →
          R ∈ openSegment ℝ ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) := by
        intro hgt
        have hdZ : dist Q Z = t * a := by
          rw [hZ, dist_left_lineMap, Real.norm_eq_abs, abs_of_pos ht, hQRa]
        have hd : dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = dist Q Z := by
          rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hjq, hjz]
          · rw [hjq, hjz, dist_comm]
        have ha0 : 0 < a := dist_pos.mpr (fun h => absurd (D.model.indep.injective h) (by decide))
        have ht1 : 1 < t := by
          rw [hd, hdZ] at hgt
          by_contra h; push Not at h; nlinarith
        have hRZ : R ∈ openSegment ℝ Q Z := by
          rw [openSegment_eq_image_lineMap]
          refine ⟨1 / t, ⟨by positivity, by rw [div_lt_one (by linarith)]; exact ht1⟩, ?_⟩
          rw [hZ, lineMap_lineMap_eq, one_div, inv_mul_cancel₀ ht.ne', AffineMap.lineMap_apply_one]
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hjq, hjz]; exact hRZ
        · rw [hjq, hjz, openSegment_symm]; exact hRZ
      -- `e'` is not an edge of Tile 1.
      have hj' : e'.1 ≠ T₁ := by
        intro hT
        rw [hT] at hjq hjz
        have hjqQ : jq = jQ := (D.tile T₁).indep.injective hjq
        by_cases hzR : jz = jR
        · apply hne'
          have hm : e'.2 = mQR := by
            rw [hjqQ, hzR] at hmem
            exact (by decide : ∀ m m' q r : Fin 3, q ≠ r → ((q = m ∧ r = m + 1) ∨ (q = m + 1 ∧ r = m)) →
              ((m' = q ∧ m' + 1 = r) ∨ (m' = r ∧ m' + 1 = q)) → m = m') e'.2 mQR jQ jR hQR hmem
              hmQRi
          exact Prod.ext hT hm
        · have hzP : jz = jP :=
            (by decide : ∀ x p q r : Fin 3, q ≠ p → r ≠ p → q ≠ r → x ≠ q → x ≠ r → x = p)
              jz jP jQ jR hPQ hPR hQR (hjqQ ▸ hjqz.symm) hzR
          rw [hzP, hZ] at hjz
          exact vertex_ne_lineMap (D.tile T₁) hPQ hPR t hjz
      set j' := e'.1
      have hQm' : (D.tile j').pts e'.2 = Q ∨ (D.tile j').pts (e'.2 + 1) = Q :=
        (mem_edgesAt D.toDissection).mp he'
      have hdQZ : dist ((D.tile j').pts e'.2) ((D.tile j').pts (e'.2 + 1)) = dist Q Z := by
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hjq, hjz]
        · rw [hjq, hjz, dist_comm]
      have hθq : ∀ θ, (D.tile j').localAngle Q = θ → (D.tile j').localAngle ((D.tile j').pts jq) = θ :=
        fun θ h => by rw [hjq]; exact h
      rcases corner_mem D hsep j' jq with hθ | hθ | hθ <;> rw [hjq] at hθ
      · -- `α` at `Q`: `e'` is a `b` or `c` edge, longer than `QR`.
        apply hRpi j' e'.2 hj' hQm' (hlong ?_)
        have hopp : (D.tile j').localAngle ((D.tile j').pts (e'.2 + 2)) ≠ tileα D := fun h =>
          hjo1 (corner_unique D hsep j' (Or.inl rfl) h (hθq _ hθ))
        rcases corner_mem D hsep j' (e'.2 + 2) with h | h | h
        · exact absurd h hopp
        · rw [edge_length D hsep j' e'.2 1 h]; exact hab
        · rw [edge_length D hsep j' e'.2 2 h]; exact hab.trans hbc
      · -- `β` at `Q`: `Q` is a corner (one `β` inside a side).
        rcases hQc with hQcor | ⟨-, hβ1, -⟩
        · have hopp : (D.tile j').localAngle ((D.tile j').pts (e'.2 + 2)) ≠ tileβ D := fun h =>
            hjo1 (corner_unique D hsep j' (Or.inr (Or.inl rfl)) h (hθq _ hθ))
          rcases corner_mem D hsep j' (e'.2 + 2) with h | h | h
          · -- **Case 1c**: an `a` edge, so `Z = R`, with `γ` at `R`.
            have hl := edge_length D hsep j' e'.2 0 h
            have ha0 : 0 < a := dist_pos.mpr (fun h => absurd (D.model.indep.injective h)
              (by decide))
            have ht1 : t = 1 := by
              have hdZ : dist Q Z = t * a := by
                rw [hZ, dist_left_lineMap, Real.norm_eq_abs, abs_of_pos ht, hQRa]
              rw [hdQZ, hdZ] at hl
              have : (t - 1) * a = 0 := by
                have hl' : t * a = a := hl
                linarith
              rcases mul_eq_zero.mp this with h | h
              · linarith
              · linarith
            have hZR : Z = R := by rw [hZ, ht1, AffineMap.lineMap_apply_one]
            have hγR' : (D.tile j').localAngle R = tileγ D := by
              rw [← hZR, ← hjz]
              rcases corner_mem D hsep j' jz with h' | h' | h'
              · exact absurd (corner_unique D hsep j' (Or.inl rfl) h' h) hjo2.symm
              · exact absurd (corner_unique D hsep j' (Or.inr (Or.inl rfl)) h' (hθq _ hθ))
                  hjqz.symm
              · exact h'
            have hRint : R ∈ interior D.target.carrier := by
              apply mem_interior_of_sum_gt D.toDissection
              have := sum_ge_two D.toDissection hj'.symm R
              rw [hRγ, hγR'] at this
              linarith
            rcases hiv with ⟨-, hiv2⟩ | hiv2
            · obtain ⟨hPα1, -, -, -⟩ := hPnc hQcor
              refine finish_1c D hsep hPQ hPR hQR hPα hR2 hP2 hPd hPπ hPα1.le hg hgP hgR hgQ
                (openSegment_subset_interior D.target hPt hRt fun j => Or.inr
                  (coord_pos_of_interior _ hRint j)) hPRb hbc hiv2 (fun e he hR => ?_)
              have hπe := Tri.localAngle_openSegment _ e.2 hR
              have h1 : e.1 ≠ T₁ := hne1 e he
              have h2 : e.1 ≠ j' := fun h => hγRne hπe (h ▸ hγR')
              have := sum_three_le D hj'.symm h1.symm (fun h => h2 h.symm) R
              rw [hRγ, hγR', hπe] at this
              linarith
            · exact hj' (eq_of_angleCount_le_one D (hiv2 Q hQcor).2 hθ hQβ)
          · exact absurd h hopp
          · exact hRpi j' e'.2 hj' hQm' (hlong (by
              rw [edge_length D hsep j' e'.2 2 h]; exact hab.trans hbc))
        · exact hj' (eq_of_angleCount_le_one D hβ1.le hθ hQβ)
      · -- `γ` at `Q`: the supplementary angle.
        rcases hQd with h0 | ⟨T₀, jV, jX, hjX, hV, hγV, hX2, hXang, hle⟩
        · exact ne_of_angleCount_zero D h0 j' hθ
        · have hjT : j' = T₀ := eq_of_angleCount_le_one D hle hθ hγV
          rw [hjT] at hjq hjz
          have hjV : jq = jV := (D.tile T₀).indep.injective (hjq.trans hV.symm)
          have hZ' : (D.tile T₀).pts jz = AffineMap.lineMap Q R t := hjz.trans hZ
          have hXZ : jX ≠ jz := by
            intro h
            rw [h, hZ', Tri.coord_lineMap, hQ2] at hX2
            have : t * D.target.basis.coord 2 R = 0 := by linarith
            rcases mul_eq_zero.mp this with h | h <;> linarith
          exact supp_contra D hsep hPQ.symm hQR.symm hPR.symm rfl rfl rfl (Or.inr hQβ) hXang hjX
            (hjV ▸ hjqz.symm) hXZ hV hγV one_pos ht (by rw [AffineMap.lineMap_apply_one]) hZ'
    · -- `QR` alone on its ray: `Q` would be inside an edge.
      push Not at hray
      exfalso
      obtain ⟨g', c', hg', hg'Q, hg'R⟩ := ray_level (farEnd_ne D.toDissection heQR)
      have hlonely : ∀ e' ∈ edgesAt D.toDissection Q, e' ≠ eQR →
          ¬ SameRayAt D.toDissection Q eQR e' := hray
      rcases edgesAt_chain D.toDissection heQR hg'Q hg'R with hch | hch
      · obtain ⟨e₂, -, hQe⟩ := lonely_openSegment D.toDissection heQR hg' hg'Q hg'R hch hlonely
          (τ := 1 / 2) ⟨by norm_num, by norm_num⟩ hmid
        have := angleCount_pos D (Tri.localAngle_openSegment _ e₂.2 hQe)
        omega
      · obtain ⟨e₂, -, hQe⟩ := lonely_openSegment D.toDissection heQR (neg_ne_zero.mpr hg')
          (by simp [hg'Q]) (by simp [hg'R]) hch hlonely (τ := 1 / 2) ⟨by norm_num, by norm_num⟩ hmid
        have := angleCount_pos D (Tri.localAngle_openSegment _ e₂.2 hQe)
        omega
  · -- **Case B**: `QR` lies on a side of `ABC`.
    push Not at hL
    obtain ⟨j0, hq0, hr0⟩ := hL
    have hq0' : D.target.basis.coord j0 Q = 0 :=
      le_antisymm hq0 ((Tri.mem_carrier_iff_coord _ _).mp hQt j0)
    have hr0' : D.target.basis.coord j0 R = 0 :=
      le_antisymm hr0 ((Tri.mem_carrier_iff_coord _ _).mp hRt j0)
    have hQcor : Q = A ∨ Q = B := by
      fin_cases j0
      · exact Or.inr (eq_vertex_of_two_coords D.target (i := 0) (j := 2) (l := 1) (by decide)
          (by decide) (by decide) hq0' hQ2)
      · exact Or.inl (eq_vertex_of_two_coords D.target (i := 1) (j := 2) (l := 0) (by decide)
          (by decide) (by decide) hq0' hQ2)
      · exact absurd hr0' hR2.ne'
    obtain ⟨-, -, hPA, hPB⟩ := hPnc hQcor
    obtain ⟨cP0, cP1⟩ := coords_of_side D.target hPside hPA hPB
    have hintPR : openSegment ℝ P R ⊆ interior D.target.carrier := by
      refine openSegment_subset_interior D.target hPt hRt fun j => ?_
      fin_cases j
      · exact Or.inl cP0
      · exact Or.inl cP1
      · exact Or.inr hR2
    have hRnint : R ∉ interior D.target.carrier := fun h => by
      have := coord_pos_of_interior _ h j0; linarith
    have hRfr : R ∈ frontier D.target.carrier := ⟨subset_closure hRt, hRnint⟩
    have hle1 : (D.tile T₁).localAngle R ≤ D.target.localAngle R := by
      rw [← D.sum_localAngle_eq]
      exact Finset.single_le_sum (f := fun i => (D.tile i).localAngle R)
        (fun i _ => (D.tile i).localAngle_nonneg R) (Finset.mem_univ T₁)
    have hRnc : R ∉ Set.range D.target.pts := by
      rintro ⟨j, hj⟩
      fin_cases j
      · rw [← hj, Tri.coord_vertex] at hR2; simp at hR2
      · rw [← hj, Tri.coord_vertex] at hR2; simp at hR2
      · have h2 : D.target.localAngle R < tileγ D := by rw [← hj]; exact hcorner 2
        rw [hRγ] at hle1
        linarith
    have hRloc := D.target.localAngle_frontier hRfr hRnc
    refine finish_star D hsep hγ hPQ hPR hQR hPα hR2 hP2 hPd hPπ hg hgP hgR hgQ hintPR hlen
      (fun i hi h => ?_) (fun e he hR => ?_)
    · have := sum_ge_two D.toDissection hi.symm R
      rw [hRγ, h, D.sum_localAngle_eq, hRloc] at this
      linarith
    · have hπe := Tri.localAngle_openSegment _ e.2 hR
      have := sum_ge_two D.toDissection (hne1 e he).symm R
      rw [hRγ, hπe, D.sum_localAngle_eq, hRloc] at this
      linarith

end TriangleTiling.TwoCs