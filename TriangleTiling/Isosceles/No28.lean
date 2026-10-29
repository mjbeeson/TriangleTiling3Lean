/-
`lemma:no28`, from Section 10 of M. Beeson, *Tilings of an isosceles triangle*: the side `AB` does not support exactly one tile with its `c` edge on `AB`.

The tiles supported by `AB` are `part` (as given by Bonfioli's `side_partition`); edge `k` of a
tile joins its vertices `k` and `k + 1` and is opposite vertex `k + 2`.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`.
-/
import TriangleTiling.Isosceles.No28Lines

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- **Step 2 of `lemma:no28`.** If exactly one tile `eT` supported by `AB` has its `c` edge on
`AB`, then at every vertex strictly inside `AB` one of the other supported tiles has its `γ`
angle, at an end of its edge. (The other `p - 1` tiles each have a `γ` at an end of their edge,
at distinct points strictly inside `AB`, of which there are at most `p - 1`.) -/
theorem no28_step2 {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (eT : Fin N × Fin 3)
    (heT : part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D) = {eT})
    {V : Plane} (hV : V ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
      part.image (fun e => (D.tile e.1).pts (e.2 + 1))))
    (hVA : V ≠ D.target.pts 0) (hVB : V ≠ D.target.pts 1) :
    ∃ e ∈ part, e ≠ eT ∧ ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) ∧
      (D.tile e.1).localAngle V = tileγ D := by
  classical
  set A := D.target.pts 0
  set B := D.target.pts 1
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2 with hu
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1) with hv
  set Eint := (part.image u ∪ part.image v).filter fun x => x ≠ A ∧ x ≠ B
  obtain ⟨cβA, cγA, -, -, -, cγB, -, -⟩ := counts_at_corners D hγ hirr hA hC
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy; rw [← hcov]; exact Set.mem_biUnion he hy
  set s := part.erase eT
  -- Each tile of `s` has its `γ` at an end of its edge.
  have hγend : ∀ e ∈ s, (D.tile e.1).localAngle (u e) = tileγ D ∨
      (D.tile e.1).localAngle (v e) = tileγ D := by
    intro e he
    obtain ⟨hne, hep⟩ := Finset.mem_erase.mp he
    refine corner_at_endpoint D hγ hirr e.1 e.2 (Or.inr (Or.inr rfl)) fun h => hne ?_
    have : e ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := Finset.mem_filter.mpr ⟨hep, h⟩
    rw [heT] at this
    exact Finset.mem_singleton.mp this
  let φ : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).localAngle (u e) = tileγ D then u e else v e
  have hφγ : ∀ e ∈ s, (D.tile e.1).localAngle (φ e) = tileγ D := by
    intro e he
    simp only [φ]
    split_ifs with h
    · exact h
    · exact (hγend e he).resolve_left h
  have hφuv : ∀ e, φ e = u e ∨ φ e = v e := by
    intro e; simp only [φ]; split_ifs <;> simp
  have hφE : ∀ e ∈ s, φ e ∈ Eint := by
    intro e he
    have hep := (Finset.mem_erase.mp he).2
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · rcases hφuv e with h | h <;> rw [h]
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hep)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hep)
    · intro h; have := hφγ e he; rw [h] at this; exact ne_of_angleCount_zero D cγA e.1 this
    · intro h; have := hφγ e he; rw [h] at this; exact ne_of_angleCount_zero D cγB e.1 this
  have hφseg : ∀ e ∈ s, φ e ∈ segment ℝ A B := by
    intro e he
    apply hsub e (Finset.mem_erase.mp he).2
    rcases hφuv e with h | h <;> rw [h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  -- `φ` is injective on `s`.
  have hinj : Set.InjOn φ s := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e (Finset.mem_erase.mp he).2)
        (h1 ▸ hsub e' (Finset.mem_erase.mp he').2)
    · have hfr : φ e ∈ frontier D.target.carrier := tri_side_subset_frontier D.target 0 (hφseg e he)
      have hnc : φ e ∉ Set.range D.target.pts := by
        rintro ⟨j, hj⟩
        have hE := Finset.mem_filter.mp (hφE e he)
        have hc2 := coord_two_of_mem_side D.target (hφseg e he)
        rw [← hj, Tri.coord_vertex] at hc2
        fin_cases j
        · exact hE.2.1 hj.symm
        · exact hE.2.2 hj.symm
        · simp at hc2
      have hle := (counts_at_side_le D hγ hirr hfr hnc).2
      exact h1 (eq_of_angleCount_le_one D hle (hφγ e he) (heq ▸ hφγ e' he'))
  -- So `φ` maps `s` onto the interior endpoints.
  have hAB : A ≠ B := D.target.indep.injective.ne (by decide)
  have huv : ∀ e ∈ part, u e ≠ v e :=
    fun e _ => (D.tile e.1).indep.injective.ne (fin3_ne_add_one e.2)
  have hchain : Eint.card + 1 ≤ part.card :=
    (segment_chain_endpoints A B hAB part u v huv hcov hdisj).1
  have heTp : eT ∈ part := by
    have : eT ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := by rw [heT]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).1
  have hscard : s.card + 1 = part.card := Finset.card_erase_add_one heTp
  have himg : s.image φ = Eint := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact hφE e he
    · rw [Finset.card_image_of_injOn hinj]; omega
  have hVE : V ∈ Eint := Finset.mem_filter.mpr ⟨hV, hVA, hVB⟩
  rw [← himg] at hVE
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hVE
  obtain ⟨hne, hep⟩ := Finset.mem_erase.mp he
  exact ⟨e, hep, hne, (hφuv e).imp Eq.symm Eq.symm, hφγ e he⟩

theorem fin3_add_one_add_one : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
theorem fin3_three : ∀ j k : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by decide
theorem fin3_add_one_add_two : ∀ k : Fin 3, k + 1 + 2 = k := by decide
theorem fin3_add_two_ne : ∀ k : Fin 3, k + 2 ≠ k ∧ k + 2 ≠ k + 1 := by decide

/-- **Step 1 of `lemma:no28`.** If exactly one tile `eT` supported by `AB` has its `c` edge on
`AB`, it is not the tile at `A`.

The paper's argument identifies the tile in the middle at the far end `P` of the tile `T₁` at `A`.
Here, instead: `T₁` fills the corner `A`, so its third vertex `Q'` lies on `AC` and its `a` edge
`PQ'` is a chord. The tile edges along `PQ'` on the other side add up to `a`. If one of them is an
`a` edge it is all of `PQ'`, and its tile has its `β` or `γ` at `P`; but `P` already carries the
single `β` (of `T₁`) and the single `γ` (of a tile on `AB`, by Step 2), and that tile cannot have
an edge along `PQ'`. Otherwise all are `b` edges (a `c` edge is too long), so `b ∣ a`. -/
theorem no28_step1 {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
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
        (D.tile e.1).localAngle (D.target.pts 1) = tileα D)
    (eT : Fin N × Fin 3)
    (heT : part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D) = {eT})
    (e : Fin N × Fin 3) (he : e ∈ part)
    (hAe : (D.tile e.1).pts e.2 = D.target.pts 0 ∨ (D.tile e.1).pts (e.2 + 1) = D.target.pts 0) :
    e ≠ eT := by
  classical
  intro hEq
  obtain ⟨hβval, hv0, hinj⟩ := angle_values D hγ hirr
  have ne5 : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne5 0 1 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne5 1 2 (by decide)
  have hα0 : tileα D ≠ 0 := hv0 0
  obtain ⟨cβA, cγA, -, -, -, -, -, -⟩ := counts_at_corners D hγ hirr hA hC
  set A := D.target.pts 0 with hAdef
  set B := D.target.pts 1 with hBdef
  set C := D.target.pts 2 with hCdef
  set T1 := D.tile e.1 with hT1
  set k := e.2 with hk
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy; rw [← hcov]; exact Set.mem_biUnion he hy
  have htgt : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j ∈ D.target.carrier := by
    intro i j
    have : (D.tile i).pts j ∈ (D.tile i).carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
    rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨i, this⟩
  -- The angle of `T₁` opposite its edge on `AB` is `γ`.
  have hopp : T1.localAngle (T1.pts (k + 2)) = tileγ D := by
    have : e ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := by rw [heT, hEq]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).2
  -- Its vertices: `A` (index `iA`), `P` (index `iP`), `Q'` (index `k + 2`).
  obtain ⟨iA, iP, hiA, hidx⟩ : ∃ iA iP : Fin 3, T1.pts iA = A ∧
      ((iA = k ∧ iP = k + 1) ∨ (iA = k + 1 ∧ iP = k)) := by
    rcases hAe with h | h
    · exact ⟨k, k + 1, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨k + 1, k, h, Or.inr ⟨rfl, rfl⟩⟩
  have hiAP : iA ≠ iP := by
    rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fin3_ne_add_one k
    · exact (fin3_ne_add_one k).symm
  have hiA2 : iA ≠ k + 2 := by
    rcases hidx with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (fin3_add_two_ne k).1.symm
    · exact (fin3_add_two_ne k).2.symm
  have hiP2 : iP ≠ k + 2 := by
    rcases hidx with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (fin3_add_two_ne k).2.symm
    · exact (fin3_add_two_ne k).1.symm
  set P := T1.pts iP with hPdef
  set Q' := T1.pts (k + 2) with hQ'def
  have hPend : (D.tile e.1).pts e.2 = P ∨ (D.tile e.1).pts (e.2 + 1) = P := by
    rcases hidx with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  -- `T₁` has `α` at `A` and `β` at `P`.
  have hTA : T1.localAngle A = tileα D := by
    rcases localAngle_at_own_vertex_mem' D e.1 iA with h | h | h <;> rw [hiA] at h
    · exact h
    · exact absurd h (ne_of_angleCount_zero D cβA e.1)
    · exact absurd h (ne_of_angleCount_zero D cγA e.1)
  have hTP : T1.localAngle P = tileβ D := by
    rcases localAngle_at_own_vertex_mem' D e.1 iP with h | h | h
    · exact absurd (corner_unique D hγ hirr e.1 (Or.inl rfl) h (by rw [hiA]; exact hTA))
        hiAP.symm
    · exact h
    · exact absurd (corner_unique D hγ hirr e.1 (Or.inr (Or.inr rfl)) h hopp) hiP2
  have hPA : P ≠ A := fun h => hiAP (T1.indep.injective (hiA.trans h.symm))
  have hPB : P ≠ B := by
    intro h
    have h1 := hB e he (by rw [← h]; exact hPend)
    have h2 : T1.localAngle B = tileβ D := by rw [← h]; exact hTP
    exact hαβ (h1.symm.trans h2)
  have hPseg : P ∈ segment ℝ A B := by
    apply hsub e he
    rcases hPend with h | h
    · rw [← h]; exact left_mem_segment _ _ _
    · rw [← h]; exact right_mem_segment _ _ _
  -- The corner of `T₁` at `A` is `∠PAQ' = α`, so `∠BAQ' = ∠BAC`.
  have hcornerA : ∠ P A Q' = tileα D := by
    have h := Tri.localAngle_vertex T1 iA
    rw [corner_eq_of_two T1 iA iP (k + 2) hiAP.symm hiA2.symm hiP2, hiA, hTA] at h
    exact h.symm
  have hBAQ : ∠ B A Q' = ∠ B A C := by
    rw [← (mem_segment_iff_wbtw.mp hPseg).angle_eq_left Q' hPA, hcornerA]; exact hA.symm
  -- `Q'` lies on the same side of `AB` as `C`.
  have hAB : A ≠ B := D.target.indep.injective.ne (by decide)
  have hAC : A ≠ C := D.target.indep.injective.ne (by decide)
  have hc2C : D.target.basis.coord 2 C = 1 := by rw [Tri.coord_vertex]; simp
  have hκ : cross (B - A) (C - A) ≠ 0 := by
    intro h0
    obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (sub_ne_zero.mpr hAB.symm) h0
    have hCl : C = AffineMap.lineMap A B τ := by
      rw [AffineMap.lineMap_apply_module', ← hτ]; abel
    have := hc2C
    rw [hCl, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex] at this
    simp at this
  have hQc : 0 < D.target.basis.coord 2 Q' := by
    rcases ((Tri.mem_carrier_iff_coord D.target Q').mp (htgt e.1 (k + 2)) 2).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have hQseg := mem_side_of_coord_two D.target (htgt e.1 (k + 2)) h.symm
      have hAseg : A ∈ segment ℝ A B := left_mem_segment _ _ _
      have hall : ∀ j : Fin 3, T1.pts j ∈ segment ℝ A B := by
        intro j
        have : j = iA ∨ j = iP ∨ j = k + 2 := by
          have h3 := fin3_three j k
          rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
          · exact h3
          · rcases h3 with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
        rcases this with rfl | rfl | rfl
        · rw [hiA]; exact hAseg
        · exact hPseg
        · exact hQseg
      have hE : ∀ m : Fin 3, T1.edge m ⊆ segment ℝ A B := fun m =>
        (convex_segment (𝕜 := ℝ) A B).segment_subset (hall m) (hall (m + 1))
      exact tri_two_edges_on_segment T1 (fin3_ne_add_one 0) (hE 0) (hE 1)
  have hside : 0 < cross (B - A) (Q' - A) * cross (B - A) (C - A) := by
    have h1 := cross_eq_coord D.target Q'
    have h2 := cross_eq_coord D.target C
    rw [hc2C, one_mul] at h2
    rw [h1, h2]
    have := mul_pos hQc (mul_self_pos.mpr hκ)
    nlinarith
  have hQA : Q' ≠ A := fun h => hiA2 (T1.indep.injective (hiA.trans h.symm))
  obtain ⟨t, ht0, htQ⟩ := same_ray_of_angle_eq (sub_ne_zero.mpr hAB.symm)
    (sub_ne_zero.mpr hQA) (sub_ne_zero.mpr hAC.symm) hBAQ hside
  have hQl : Q' = AffineMap.lineMap A C t := by
    rw [AffineMap.lineMap_apply_module', ← htQ]; abel
  have ht1 : t ≤ 1 := by
    have h := (Tri.mem_carrier_iff_coord D.target Q').mp (htgt e.1 (k + 2)) 0
    rw [hQl, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex] at h
    simp at h; linarith
  have hQc2 : D.target.basis.coord 2 Q' = t := by
    rw [hQl, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]; simp
  -- `P = lineMap A B s` with `0 < s < 1`.
  obtain ⟨s, ⟨hs0, hs1⟩, hPl⟩ := (segment_eq_image_lineMap ℝ A B ▸ hPseg :
    P ∈ AffineMap.lineMap A B '' Set.Icc (0 : ℝ) 1)
  have hs0' : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hPA; rw [← hPl, ← h, AffineMap.lineMap_apply_zero]
  have hs1' : s < 1 := by
    rcases hs1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hPB; rw [← hPl, h, AffineMap.lineMap_apply_one]
  -- The chord `PQ'`.
  have hint : openSegment ℝ P Q' ⊆ interior D.target.carrier := by
    intro x hx
    rw [openSegment_eq_image_lineMap] at hx
    obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hx
    have v : ∀ i j : Fin 3, D.target.basis.coord i (D.target.pts j) = if i = j then 1 else 0 :=
      fun i j => Tri.coord_vertex D.target i j
    have a0 : D.target.basis.coord 0 A = 1 := by rw [v]; rfl
    have a1 : D.target.basis.coord 1 A = 0 := by rw [v]; rfl
    have a2 : D.target.basis.coord 2 A = 0 := by rw [v]; rfl
    have b0 : D.target.basis.coord 0 B = 0 := by rw [v]; rfl
    have b1 : D.target.basis.coord 1 B = 1 := by rw [v]; rfl
    have b2 : D.target.basis.coord 2 B = 0 := by rw [v]; rfl
    have c0 : D.target.basis.coord 0 C = 0 := by rw [v]; rfl
    have c1 : D.target.basis.coord 1 C = 0 := by rw [v]; rfl
    have c2 : D.target.basis.coord 2 C = 1 := by rw [v]; rfl
    have cP : ∀ i : Fin 3, D.target.basis.coord i P = D.target.basis.coord i A
        + s * (D.target.basis.coord i B - D.target.basis.coord i A) := by
      intro i; rw [← hPl, Tri.coord_lineMap]
    have cQ : ∀ i : Fin 3, D.target.basis.coord i Q' = D.target.basis.coord i A
        + t * (D.target.basis.coord i C - D.target.basis.coord i A) := by
      intro i; rw [hQl, Tri.coord_lineMap]
    have hst : (1 - l) * s + l * t < 1 := by
      nlinarith only [hs1', ht1, hl0, hl1, mul_pos (sub_pos.mpr hl1) (sub_pos.mpr hs1')]
    rw [Tri.mem_interior_iff_coord_pos]
    intro i
    rw [Tri.coord_lineMap, cP, cQ]
    rcases fin3_three i 0 with h | h | h <;> rw [h]
    · rw [a0, b0, c0]; nlinarith only [hst]
    · rw [show (0 : Fin 3) + 1 = 1 from rfl, a1, b1, c1]
      nlinarith only [mul_pos hs0' (sub_pos.mpr hl1)]
    · rw [show (0 : Fin 3) + 2 = 2 from rfl, a2, b2, c2]
      nlinarith only [mul_pos hl0 ht0]
  have hPfr : P ∉ interior D.target.carrier := fun h =>
    (tri_side_subset_frontier D.target 0 hPseg).2 h
  have hQseg : Q' ∈ segment ℝ C A := by
    rw [segment_symm, segment_eq_image_lineMap]; exact ⟨t, ⟨ht0.le, ht1⟩, hQl.symm⟩
  have hQfr : Q' ∉ interior D.target.carrier := fun h =>
    (tri_side_subset_frontier D.target 2 hQseg).2 h
  -- The edge `m` of `T₁` joining `P` and `Q'`; its opposite vertex is `A`.
  obtain ⟨m, hmP, hmQ, hmA⟩ : ∃ m : Fin 3, ((T1.pts m = P ∧ T1.pts (m + 1) = Q') ∨
      (T1.pts m = Q' ∧ T1.pts (m + 1) = P)) ∧ True ∧ T1.pts (m + 2) = A := by
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨k + 1, Or.inl ⟨by rw [hPdef, h2], by rw [fin3_add_one_add_one]⟩, trivial, ?_⟩
      rw [fin3_add_one_add_two, ← h1]; exact hiA
    · refine ⟨k + 2, Or.inr ⟨rfl, by rw [fin3_add_two_add_one, hPdef, h2]⟩, trivial, ?_⟩
      rw [fin3_add_two_add_two, ← h1]; exact hiA
  have hedgeM : T1.edge m = segment ℝ P Q' := by
    rw [Tri.edge]
    rcases hmP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
  have hm1 : T1.pts m ∉ interior D.target.carrier := by
    rcases hmP with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact hPfr
    · exact hQfr
  have hm2 : T1.pts (m + 1) ∉ interior D.target.carrier := by
    rcases hmP with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact hQfr
    · exact hPfr
  have hmint : openSegment ℝ (T1.pts m) (T1.pts (m + 1)) ⊆ interior D.target.carrier := by
    rcases hmP with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hint
    · rw [openSegment_symm]; exact hint
  have hdm : dist (T1.pts m) (T1.pts (m + 1)) = dist P Q' := by
    rcases hmP with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact dist_comm _ _
  obtain ⟨f, cc, hf, hline, hsubF, hnear, hfar⟩ :=
    chord_two_sided D.toDissection e.1 m hm1 hm2 hmint
  -- `A` is strictly off the line of `PQ'`.
  have hfA : f A ≠ cc := by
    intro hfa
    have hPQ : T1.pts m ≠ T1.pts (m + 1) := T1.indep.injective.ne (fin3_ne_add_one m)
    obtain ⟨τ, hτ⟩ := eq_lineMap_of_level hf hPQ (hline _ (left_mem_segment _ _ _))
      (hline _ (right_mem_segment _ _ _)) hfa
    have h := Tri.coord_vertex T1 (m + 2) (m + 2)
    rw [hmA, hτ, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex] at h
    simp [(fin3_add_two_ne m).1, (fin3_add_two_ne m).2] at h
  -- The chain on the side away from `T₁`.
  obtain ⟨F, hFnot, hFsub, hFsum⟩ : ∃ F : Finset (Fin N × Fin 3), (∀ e' ∈ F, e'.1 ≠ e.1) ∧
      (∀ e' ∈ F, (D.tile e'.1).edge e'.2 ⊆ segment ℝ P Q') ∧
      ∑ e' ∈ F, dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = dist P Q' := by
    rcases lt_or_gt_of_ne hfA with hlt | hgt
    · refine ⟨D.lineChain (-f) (-cc), fun e' he' h1 => ?_, fun e' he' => ?_, hfar.trans hdm⟩
      · obtain ⟨-, -, hall⟩ := Dissection.mem_lineChain.mp he'
        have := hall (m + 2)
        simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
        rw [h1, hmA] at this
        linarith
      · rw [← hedgeM]; exact hsubF e' (Finset.mem_union_right _ he')
    · refine ⟨D.lineChain f cc, fun e' he' h1 => ?_, fun e' he' => ?_, hnear.trans hdm⟩
      · obtain ⟨-, -, hall⟩ := Dissection.mem_lineChain.mp he'
        have := hall (m + 2)
        rw [h1, hmA] at this
        linarith
      · rw [← hedgeM]; exact hsubF e' (Finset.mem_union_left _ he')
  -- `|PQ'| = a`.
  have hPQa : dist P Q' = a := by
    have h := (opp_side D hγ hirr e.1 iA).1 (by rw [hiA]; exact hTA)
    rw [ha] at h
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h
      rw [hPdef, h2]; exact h
    · rw [h1, fin3_add_one_add_two, fin3_add_one_add_one] at h
      rw [hPdef, h2, dist_comm]; exact h
  -- The integer tile.
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨n1, n2, n3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at n1 n2 n3
  have n1' : a < b + c := by exact_mod_cast n1
  have n2' : b < c + a := by exact_mod_cast n2
  have n3' : c < a + b := by exact_mod_cast n3
  obtain ⟨hac, hab, hndvd⟩ := int_tile_facts hcop hcab n1' (by omega) n3'
  have hacR : (a : ℝ) < c := by exact_mod_cast hac
  have habR : (a : ℝ) ≠ b := by exact_mod_cast hab
  have hlen : ∀ e' ∈ F, dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = a ∨
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = b := by
    intro e' he'
    have hle : dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) ≤ a := by
      rw [← hPQa]
      exact dist_le_of_mem_segment₂ (hFsub e' he' (left_mem_segment _ _ _))
        (hFsub e' he' (right_mem_segment _ _ _))
    rcases edge_len_mem D e'.1 e'.2 with h | h | h
    · left; rw [h, ha]
    · right; rw [h, hb]
    · rw [h, hc] at hle; linarith
  by_cases hexa : ∃ e' ∈ F, dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = a
  · obtain ⟨e', he'F, hlena⟩ := hexa
    set X := D.tile e'.1 with hX
    -- `e'` is all of `PQ'`.
    have hPQ : P ≠ Q' := fun h => hiP2 (T1.indep.injective h)
    have hends := endpoints_of_full_subsegment hPQ (hFsub e' he'F (left_mem_segment _ _ _))
      (hFsub e' he'F (right_mem_segment _ _ _)) (hlena.trans hPQa.symm)
    -- Its angle opposite is `α`.
    have hXopp : X.localAngle (X.pts (e'.2 + 2)) = tileα D := by
      have hs := opp_side D hγ hirr e'.1 (e'.2 + 2)
      rw [fin3_add_two_add_one, fin3_add_two_add_two] at hs
      rcases localAngle_at_own_vertex_mem' D e'.1 (e'.2 + 2) with h | h | h
      · exact h
      · exfalso; have := hs.2.1 h; rw [hb] at this; exact habR (hlena.symm.trans this)
      · exfalso; have := hs.2.2 h; rw [hc] at this; linarith [hlena.symm.trans this]
    -- So `X` has its `β` or `γ` at `P`.
    obtain ⟨jP, hjP, hjP2⟩ : ∃ jP : Fin 3, X.pts jP = P ∧ jP ≠ e'.2 + 2 := by
      rcases hends with ⟨h, -⟩ | ⟨-, h⟩
      · exact ⟨e'.2, h, (fin3_add_two_ne e'.2).1.symm⟩
      · exact ⟨e'.2 + 1, h, (fin3_add_two_ne e'.2).2.symm⟩
    obtain ⟨jQ, hjQ, hjQ2⟩ : ∃ jQ : Fin 3, X.pts jQ = Q' ∧ jQ ≠ e'.2 + 2 := by
      rcases hends with ⟨-, h⟩ | ⟨h, -⟩
      · exact ⟨e'.2 + 1, h, (fin3_add_two_ne e'.2).2.symm⟩
      · exact ⟨e'.2, h, (fin3_add_two_ne e'.2).1.symm⟩
    have hXP : X.localAngle P = tileβ D ∨ X.localAngle P = tileγ D := by
      rcases localAngle_at_own_vertex_mem' D e'.1 jP with h | h | h <;> rw [hjP] at h
      · exact absurd (corner_unique D hγ hirr e'.1 (Or.inl rfl) (by rw [hjP]; exact h) hXopp)
          hjP2
      · exact Or.inl h
      · exact Or.inr h
    -- `P` carries one `β` (of `T₁`) and one `γ` (of a tile on `AB`).
    have hPE : P ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
        part.image (fun e => (D.tile e.1).pts (e.2 + 1))) := by
      rcases hPend with h | h
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, h⟩)
    obtain ⟨eS, heS, heSne, heSend, heSγ⟩ :=
      no28_step2 D hγ hirr hA hC part hcov hdisj eT heT hPE hPA hPB
    have hPfront : P ∈ frontier D.target.carrier := tri_side_subset_frontier D.target 0 hPseg
    have hPnc : P ∉ Set.range D.target.pts := by
      rintro ⟨j, hj⟩
      have hc2 := coord_two_of_mem_side D.target hPseg
      rw [← hj, Tri.coord_vertex] at hc2
      fin_cases j
      · exact hPA hj.symm
      · exact hPB hj.symm
      · simp at hc2
    obtain ⟨-, cβP, cγP, -, -⟩ :=
      counts_at_side D hγ hirr hPfront hPnc (angleCount_pos D heSγ)
    rcases hXP with hXβ | hXγ
    · exact hFnot e' he'F (eq_of_angleCount_le_one D cβP.le hXβ hTP)
    · -- `X` is the tile `S` on `AB` with its `γ` at `P`; but its angle at `P` is `β` or `π - β`.
      have hXS : e'.1 = eS.1 := eq_of_angleCount_le_one D cγP.le hXγ heSγ
      obtain ⟨jP', jY, hjP', hYseg, hjPY, -⟩ : ∃ jP' jY : Fin 3, X.pts jP' = P ∧
          X.pts jY ∈ segment ℝ A B ∧ X.pts jY ≠ P ∧ True := by
        rcases heSend with h | h
        · refine ⟨eS.2, eS.2 + 1, by rw [hX, hXS]; exact h, ?_, ?_, trivial⟩
          · rw [hX, hXS]; exact hsub eS heS (right_mem_segment _ _ _)
          · rw [hX, hXS, ← h]
            exact (D.tile eS.1).indep.injective.ne (fin3_ne_add_one eS.2).symm
        · refine ⟨eS.2 + 1, eS.2, by rw [hX, hXS]; exact h, ?_, ?_, trivial⟩
          · rw [hX, hXS]; exact hsub eS heS (left_mem_segment _ _ _)
          · rw [hX, hXS, ← h]
            exact (D.tile eS.1).indep.injective.ne (fin3_ne_add_one eS.2)
      have hjPP : jP' = jP := X.indep.injective (hjP'.trans hjP.symm)
      subst hjPP
      set Y := X.pts jY
      have hYQ : Y ≠ Q' := by
        intro h
        have h1 := coord_two_of_mem_side D.target hYseg
        rw [h, hQc2] at h1
        linarith
      have hjYP : jY ≠ jP' := fun h => hjPY (by show X.pts jY = P; rw [h]; exact hjP')
      have hjQP : jQ ≠ jP' := fun h => hPQ (hjP'.symm.trans (h ▸ hjQ))
      have hjYQ : jY ≠ jQ := fun h => hYQ (by show X.pts jY = Q'; rw [h]; exact hjQ)
      have hSP : ∠ Y P Q' = tileγ D := by
        have h := Tri.localAngle_vertex X jP'
        rw [corner_eq_of_two X jP' jY jQ hjYP hjQP hjYQ, hjP', hjQ, hXγ] at h
        exact h.symm
      have hTPang : ∠ A P Q' = tileβ D := by
        have h := Tri.localAngle_vertex T1 iP
        rw [corner_eq_of_two T1 iP iA (k + 2) hiAP hiP2.symm hiA2, hiA, hTP] at h
        exact h.symm
      -- `Y` and `A` on the line `AB` through `P`.
      obtain ⟨y, ⟨hy0, hy1⟩, hYl⟩ := (segment_eq_image_lineMap ℝ A B ▸ hYseg :
        Y ∈ AffineMap.lineMap A B '' Set.Icc (0 : ℝ) 1)
      have hys : y ≠ s := fun h => hjPY (by rw [← hYl, h, hPl])
      have h0s : (0 : ℝ) ≠ s := hs0'.ne
      have hon := angle_on_line' (A := A) (B := B) (R := Q') hys h0s
      rw [hYl, hPl, AffineMap.lineMap_apply_zero, angle_comm Q' P Y, angle_comm Q' P A,
        hSP, hTPang] at hon
      have hsum3 : tileα D + tileβ D + tileγ D = Real.pi := cornerAngle_sum D.model
      rcases hon with h | h
      · exact hβγ h.symm
      · exact hα0 (by linarith)
  · push Not at hexa
    -- All the edges are `b` edges, so `b ∣ a`.
    have hallb : ∀ e' ∈ F,
        dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = b :=
      fun e' he' => (hlen e' he').resolve_left (hexa e' he')
    rw [Finset.sum_congr rfl hallb, Finset.sum_const, nsmul_eq_mul, hPQa] at hFsum
    have : a = F.card * b := by exact_mod_cast hFsum.symm
    exact hndvd ⟨F.card, by rw [this, mul_comm]⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma `lemma:no28`.** Let the isosceles triangle `ABC` with base `AC` and base angles `α`
(`α ∉ ℚπ`) be tiled by a tile with angles `(α, β, 2α)` and integer sides `(a, b, c)` without
common factor, and suppose the tile at `B` supported by `AB` has its `α` angle at `B`. Then `AB`
does not support exactly one tile with its `c` edge on `AB`.

The tiles supported by `AB` are `part` (Bonfioli's `side_partition`); "the tile has its `c` edge
on `AB`" is "its angle opposite its edge on `AB` is `γ`". -/
theorem no28 {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
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
    (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D).card ≠ 1 := by
  classical
  intro hone
  obtain ⟨eT, heT⟩ := Finset.card_eq_one.mp hone
  obtain ⟨hβval, hv0, hinj⟩ := angle_values D hγ hirr
  have ne5 : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne5 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne5 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne5 1 2 (by decide)
  have hα0 : tileα D ≠ 0 := hv0 0
  have hsum3 : tileα D + tileβ D + tileγ D = Real.pi := cornerAngle_sum D.model
  obtain ⟨cβA, cγA, cβC, cγC, cβB, cγB, -, cαB⟩ := counts_at_corners D hγ hirr hA hC
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆
      segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    intro e he y hy; rw [← hcov]; exact Set.mem_biUnion he hy
  have htgt : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j ∈ D.target.carrier := by
    intro i j
    have : (D.tile i).pts j ∈ (D.tile i).carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
    rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨i, this⟩
  have heTmem : eT ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D) := by rw [heT]; exact Finset.mem_singleton_self _
  have heTp : eT ∈ part := (Finset.mem_filter.mp heTmem).1
  have hopp : (D.tile eT.1).localAngle ((D.tile eT.1).pts (eT.2 + 2)) = tileγ D :=
    (Finset.mem_filter.mp heTmem).2
  -- The integer tile.
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨n1, n2, n3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at n1 n2 n3
  have n1' : a < b + c := by exact_mod_cast n1
  have n2' : b < c + a := by exact_mod_cast n2
  have n3' : c < a + b := by exact_mod_cast n3
  obtain ⟨hac, hab, hndvd⟩ := int_tile_facts hcop hcab n1' (by omega) n3'
  obtain ⟨er1, er2, er3⟩ := edgerelations a b c (by omega) (by omega) (by omega) hcab hcop
  have hacR : (a : ℝ) < c := by exact_mod_cast hac
  have habR : (a : ℝ) ≠ b := by exact_mod_cast hab
  have ha0R : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0R : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- The tile `T` with its `c` edge on `AB`: `α` at `P`, `β` at `Q`, `γ` at `R`.
  set T := D.tile eT.1 with hTdef
  set k := eT.2 with hkdef
  obtain ⟨iP, iQ, hidx, hTPα, hTQβ⟩ : ∃ iP iQ : Fin 3,
      ((iP = k ∧ iQ = k + 1) ∨ (iP = k + 1 ∧ iQ = k)) ∧
      T.localAngle (T.pts iP) = tileα D ∧ T.localAngle (T.pts iQ) = tileβ D := by
    have hαend := corner_at_endpoint D hγ hirr eT.1 k (Or.inl rfl) (by rw [hopp]; exact hαγ.symm)
    have hβend := corner_at_endpoint D hγ hirr eT.1 k (Or.inr (Or.inl rfl))
      (by rw [hopp]; exact hβγ.symm)
    rcases hαend with h | h
    · refine ⟨k, k + 1, Or.inl ⟨rfl, rfl⟩, h, ?_⟩
      rcases hβend with h' | h'
      · exact absurd (h.symm.trans h') hαβ
      · exact h'
    · refine ⟨k + 1, k, Or.inr ⟨rfl, rfl⟩, h, ?_⟩
      rcases hβend with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hαβ
  obtain ⟨P, hP⟩ : ∃ P, T.pts iP = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, T.pts iQ = Q := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, T.pts (k + 2) = R := ⟨_, rfl⟩
  rw [hP] at hTPα
  rw [hQ] at hTQβ
  have hTRγ : T.localAngle R = tileγ D := by rw [← hR]; exact hopp
  have hiPQ : iP ≠ iQ := by
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact fin3_ne_add_one k
    · exact (fin3_ne_add_one k).symm
  have hiP2 : iP ≠ k + 2 := by
    rcases hidx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact (fin3_add_two_ne k).1.symm
    · exact (fin3_add_two_ne k).2.symm
  have hiQ2 : iQ ≠ k + 2 := by
    rcases hidx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact (fin3_add_two_ne k).2.symm
    · exact (fin3_add_two_ne k).1.symm
  have hPQ : P ≠ Q := fun h => hiPQ (T.indep.injective (hP.trans (h.trans hQ.symm)))
  have hPR : P ≠ R := fun h => hiP2 (T.indep.injective (hP.trans (h.trans hR.symm)))
  have hQR : Q ≠ R := fun h => hiQ2 (T.indep.injective (hQ.trans (h.trans hR.symm)))
  have hPend : T.pts k = P ∨ T.pts (k + 1) = P := by
    rcases hidx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (h1 ▸ hP)
    · exact Or.inr (h1 ▸ hP)
  have hQend : T.pts k = Q ∨ T.pts (k + 1) = Q := by
    rcases hidx with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr (h2 ▸ hQ)
    · exact Or.inl (h2 ▸ hQ)
  have hPseg : P ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    apply hsub eT heTp
    rcases hPend with h | h <;> rw [← h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hQseg : Q ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    apply hsub eT heTp
    rcases hQend with h | h <;> rw [← h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  -- `P, Q ≠ A` (Step 1) and `Q ≠ B`.
  have hPA : P ≠ D.target.pts 0 := by
    intro h
    have hend : T.pts k = D.target.pts 0 ∨ T.pts (k + 1) = D.target.pts 0 := by
      rcases hPend with h' | h'
      · exact Or.inl (h'.trans h)
      · exact Or.inr (h'.trans h)
    exact no28_step1 D ha hb hc hcop hγ hirr hA hC part hcov hdisj hB eT heT eT heTp hend rfl
  have hQA : Q ≠ D.target.pts 0 := by
    intro h
    have hend : T.pts k = D.target.pts 0 ∨ T.pts (k + 1) = D.target.pts 0 := by
      rcases hQend with h' | h'
      · exact Or.inl (h'.trans h)
      · exact Or.inr (h'.trans h)
    exact no28_step1 D ha hb hc hcop hγ hirr hA hC part hcov hdisj hB eT heT eT heTp hend rfl
  have hQB : Q ≠ D.target.pts 1 := by
    intro h
    have hend : T.pts k = D.target.pts 1 ∨ T.pts (k + 1) = D.target.pts 1 := by
      rcases hQend with h' | h'
      · exact Or.inl (h'.trans h)
      · exact Or.inr (h'.trans h)
    have h1 := hB eT heTp hend
    rw [← h] at h1
    exact hαβ (h1.symm.trans hTQβ)
  -- `R` is strictly off `AB`.
  have hRc : 0 < D.target.basis.coord 2 R := by
    rcases ((Tri.mem_carrier_iff_coord D.target R).mp (hR ▸ htgt eT.1 (k + 2)) 2).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have hRseg := mem_side_of_coord_two D.target (hR ▸ htgt eT.1 (k + 2)) h.symm
      have hall : ∀ j : Fin 3, T.pts j ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
        intro j
        rcases fin3_three j k with h1 | h1 | h1 <;> rw [h1]
        · rcases hidx with ⟨h2, -⟩ | ⟨-, h2⟩ <;> rw [← h2]
          · rw [hP]; exact hPseg
          · rw [hQ]; exact hQseg
        · rcases hidx with ⟨-, h2⟩ | ⟨h2, -⟩ <;> rw [← h2]
          · rw [hQ]; exact hQseg
          · rw [hP]; exact hPseg
        · rw [hR]; exact hRseg
      have hE : ∀ m : Fin 3, T.edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := fun m =>
        (convex_segment (𝕜 := ℝ) _ _).segment_subset (hall m) (hall (m + 1))
      exact tri_two_edges_on_segment T (fin3_ne_add_one 0) (hE 0) (hE 1)
  have hRtgt : R ∈ D.target.carrier := hR ▸ htgt eT.1 (k + 2)
  -- Points of `AB` as parameters.
  have hparam : ∀ X ∈ segment ℝ (D.target.pts 0) (D.target.pts 1),
      ∃ x ∈ Set.Icc (0 : ℝ) 1, X = AffineMap.lineMap (D.target.pts 0) (D.target.pts 1) x := by
    intro X hX
    rw [segment_eq_image_lineMap] at hX
    obtain ⟨x, hx, rfl⟩ := hX
    exact ⟨x, hx, rfl⟩
  obtain ⟨q, hq, hQl⟩ := hparam Q hQseg
  obtain ⟨p, hp, hPl⟩ := hparam P hPseg
  have hpq : p ≠ q := fun h => hPQ (by rw [hPl, hQl, h])
  have hq0 : 0 < q := by
    rcases hq.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hQA; rw [hQl, ← h, AffineMap.lineMap_apply_zero]
  have hq1 : q < 1 := by
    rcases hq.2.lt_or_eq with h | h
    · exact h
    · exfalso; apply hQB; rw [hQl, h, AffineMap.lineMap_apply_one]
  -- Corners of `T` at `P` and `Q`.
  have hcornerQ : ∠ P Q R = tileβ D := by
    have h := Tri.localAngle_vertex T iQ
    rw [corner_eq_of_two T iQ iP (k + 2) hiPQ hiQ2.symm hiP2, hP, hQ, hR, hTQβ] at h
    exact h.symm
  have hcornerP : ∠ Q P R = tileα D := by
    have h := Tri.localAngle_vertex T iP
    rw [corner_eq_of_two T iP iQ (k + 2) hiPQ.symm hiP2.symm hiQ2, hP, hQ, hR, hTPα] at h
    exact h.symm
  -- The angle counts at `Q`: one each of `α, β, γ`.
  have hQfr : Q ∈ frontier D.target.carrier := tri_side_subset_frontier D.target 0 hQseg
  have hQnc : Q ∉ Set.range D.target.pts := by
    rintro ⟨j, hj⟩
    have hc2 := coord_two_of_mem_side D.target hQseg
    rw [← hj, Tri.coord_vertex] at hc2
    fin_cases j
    · exact hQA hj.symm
    · exact hQB hj.symm
    · simp at hc2
  have hQE : Q ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
      part.image (fun e => (D.tile e.1).pts (e.2 + 1))) := by
    rcases hQend with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨eT, heTp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨eT, heTp, h⟩)
  obtain ⟨eSQ, heSQ, -, heSQend, heSQγ⟩ :=
    no28_step2 D hγ hirr hA hC part hcov hdisj eT heT hQE hQA hQB
  obtain ⟨cαQ, cβQ, cγQ, cπQ, -⟩ := counts_at_side D hγ hirr hQfr hQnc (angleCount_pos D heSQγ)
  -- The line `QR`, oriented so that `P` is on the side `g > c'`.
  obtain ⟨mQR, hmQR, hmP⟩ : ∃ m : Fin 3, T.edge m = segment ℝ Q R ∧ T.pts (m + 2) = P := by
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨k + 1, ?_, ?_⟩
      · rw [Tri.edge, fin3_add_one_add_one, ← h2, hQ, hR]
      · rw [fin3_add_one_add_two, ← h1, hP]
    · refine ⟨k + 2, ?_, ?_⟩
      · rw [Tri.edge, fin3_add_two_add_one, hR, ← h2, hQ, segment_symm]
      · rw [fin3_add_two_add_two, ← h1, hP]
  obtain ⟨g, cg, hg, hgline, hgP⟩ := edge_level_oriented T mQR
  rw [hmQR] at hgline
  rw [hmP] at hgP
  have hgQ : g Q = cg := hgline Q (left_mem_segment _ _ _)
  have hgR : g R = cg := hgline R (right_mem_segment _ _ _)
  have hSQR : segment ℝ Q R ⊆ {y | g y = cg} := fun y hy => hgline y hy
  have hFQnot : ∀ e ∈ D.lineChain g cg, e.1 ≠ eT.1 :=
    lineChain_tile_ne D.toDissection g cg (i := eT.1) (j := iP) (by rw [hP]; exact hgP)
  have hQRint : openSegment ℝ Q R ⊆ interior D.target.carrier := by
    intro x hx
    rw [openSegment_eq_image_lineMap] at hx
    obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hx
    rw [Tri.mem_interior_iff_coord_pos]
    have hcR := (Tri.mem_carrier_iff_coord D.target R).mp hRtgt
    have v : ∀ i j : Fin 3, D.target.basis.coord i (D.target.pts j) = if i = j then 1 else 0 :=
      fun i j => Tri.coord_vertex D.target i j
    intro i
    rw [Tri.coord_lineMap, hQl, Tri.coord_lineMap, v, v]
    rcases fin3_three i 0 with h | h | h <;> rw [h]
    · have := hcR 0
      norm_num
      nlinarith only [this, hl0, hl1, hq1, mul_pos (sub_pos.mpr hl1) (sub_pos.mpr hq1)]
    · have := hcR 1
      norm_num
      nlinarith only [this, hl0, hl1, hq0, mul_pos (sub_pos.mpr hl1) hq0]
    · simp only [show ¬((2 : Fin 3) = 0) from by decide, show ¬((2 : Fin 3) = 1) from by decide,
        if_false, show (0 : Fin 3) + 2 = 2 from rfl]
      nlinarith only [hRc, hl0, mul_pos hl0 hRc]
  have hwallQR : ∀ y ∈ openSegment ℝ Q R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have : y ∈ T.edge mQR := by rw [hmQR]; exact openSegment_subset_segment _ _ _ hy
    exact D.toDissection.edge_point_not_interior this
  -- The first edge along `QR` at `Q`, on the side away from `T`: an edge of the tile `G`
  -- with its `α` at `Q`.
  obtain ⟨e1, he1, hQe1, x1, hx1, hx1e⟩ :=
    exists_chain_edge_at D.toDissection g cg hg hQR hSQR hQRint hwallQR
  have hX1ne : e1.1 ≠ eT.1 := hFQnot e1 he1
  have hQend1 := endpoint_of_ne_pi (D.tile e1.1) e1.2 hQe1
    (fun h => by have := angleCount_pos D h; omega)
  set X := D.tile e1.1 with hXdef
  obtain ⟨jQ, jW, hjidx, hjQ⟩ : ∃ jQ jW : Fin 3,
      ((jQ = e1.2 ∧ jW = e1.2 + 1) ∨ (jQ = e1.2 + 1 ∧ jW = e1.2)) ∧ X.pts jQ = Q := by
    rcases hQend1 with h | h
    · exact ⟨e1.2, e1.2 + 1, Or.inl ⟨rfl, rfl⟩, h.symm⟩
    · exact ⟨e1.2 + 1, e1.2, Or.inr ⟨rfl, rfl⟩, h.symm⟩
  have hjQW : jW ≠ jQ := by
    rcases hjidx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact (fin3_ne_add_one e1.2).symm
    · exact fin3_ne_add_one e1.2
  have hedge1 : X.edge e1.2 = segment ℝ Q (X.pts jW) := by
    rcases hjidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Tri.edge, ← h2, ← h1, hjQ]
    · rw [Tri.edge, ← h1, ← h2, hjQ, segment_symm]
  have hgW : g (X.pts jW) = cg := by
    obtain ⟨hu, hv, -⟩ := Dissection.mem_lineChain.mp he1
    rcases hjidx with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact hv
    · exact hu
  obtain ⟨w, hWl⟩ := eq_lineMap_of_level hg hQR hgQ hgR hgW
  -- `W = lineMap Q R w` with `w > 0`, since the edge contains `x₁` inside `QR`.
  have hw : 0 < w := by
    rw [openSegment_eq_image_lineMap] at hx1
    obtain ⟨l1, ⟨hl0, hl1⟩, rfl⟩ := hx1
    rw [hedge1, hWl] at hx1e
    have h0 : AffineMap.lineMap Q R l1 ∈ segment ℝ (AffineMap.lineMap Q R (0 : ℝ))
        (AffineMap.lineMap Q R w) := by rwa [AffineMap.lineMap_apply_zero]
    rw [lineMap_mem_segment_iff hQR, segment_eq_uIcc] at h0
    rcases Set.mem_uIcc.mp h0 with h | h
    · linarith [h.2]
    · linarith [h.1, h.2]
  have hXQα : X.localAngle Q = tileα D := by
    rcases localAngle_at_own_vertex_mem' D e1.1 jQ with h | h | h <;> rw [hjQ] at h
    · exact h
    · exact absurd (eq_of_angleCount_le_one D cβQ.le h hTQβ) hX1ne
    · -- Then `X` is the tile on `AB` with its `γ` at `Q`; its angle there is `β` or `π - β`.
      exfalso
      have hXS : e1.1 = eSQ.1 := eq_of_angleCount_le_one D cγQ.le h heSQγ
      obtain ⟨jY, hjYQ, hYseg⟩ : ∃ jY : Fin 3, X.pts jY ≠ Q ∧
          X.pts jY ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
        rcases heSQend with h' | h'
        · refine ⟨eSQ.2 + 1, ?_, ?_⟩
          · rw [hXdef, hXS, ← h']
            exact (D.tile eSQ.1).indep.injective.ne (fin3_ne_add_one eSQ.2).symm
          · rw [hXdef, hXS]; exact hsub eSQ heSQ (right_mem_segment _ _ _)
        · refine ⟨eSQ.2, ?_, ?_⟩
          · rw [hXdef, hXS, ← h']
            exact (D.tile eSQ.1).indep.injective.ne (fin3_ne_add_one eSQ.2)
          · rw [hXdef, hXS]; exact hsub eSQ heSQ (left_mem_segment _ _ _)
      obtain ⟨y, -, hYl⟩ := hparam _ hYseg
      have hjYQ' : jY ≠ jQ := fun h => hjYQ (by rw [h, hjQ])
      have hjYW : jY ≠ jW := by
        intro h
        have h1 := coord_two_of_mem_side D.target hYseg
        rw [h, hWl, Tri.coord_lineMap, coord_two_of_mem_side D.target hQseg] at h1
        have : 0 < w * D.target.basis.coord 2 R := mul_pos hw hRc
        linarith
      have hyq : y ≠ q := fun h => hjYQ (by rw [hYl, hQl, h])
      have hcorner := corner_from_line X hjYQ' hjQW hjYW (A := D.target.pts 0)
        (B := D.target.pts 1) (R := R) (v := q) (y := y) (z := p) (w := w)
        (by rw [hjQ, hQl]) hYl (by rw [hWl, ← hQl]) hw hyq hpq
      rw [← hPl, ← hQl, hcornerQ, ← Tri.localAngle_vertex, hjQ, h] at hcorner
      rcases hcorner with h' | h'
      · exact hβγ h'.symm
      · exact hα0 (by linarith)
  -- So the edge `e₁` is a `b` or `c` edge.
  have hlen1 : dist (X.pts e1.2) (X.pts (e1.2 + 1)) = b ∨ dist (X.pts e1.2) (X.pts (e1.2 + 1)) = c := by
    have hs := opp_side D hγ hirr e1.1 (e1.2 + 2)
    rw [fin3_add_two_add_one, fin3_add_two_add_two, hb, hc] at hs
    have hne : e1.2 + 2 ≠ jQ := by
      rcases hjidx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact (fin3_add_two_ne e1.2).1
      · exact (fin3_add_two_ne e1.2).2
    rcases localAngle_at_own_vertex_mem' D e1.1 (e1.2 + 2) with h | h | h
    · exact absurd (corner_unique D hγ hirr e1.1 (Or.inl rfl) h (by rw [hjQ]; exact hXQα)) hne
    · exact Or.inl (hs.2.1 h)
    · exact Or.inr (hs.2.2 h)
  -- `|QR| = a`.
  have hQRa : dist Q R = a := by
    have h := (opp_side D hγ hirr eT.1 iP).1 (by rw [hP]; exact hTPα)
    rw [ha] at h
    have hQ' := hQ
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, hR] at h
      rw [h2] at hQ'
      rw [hQ'] at h; exact h
    · rw [h1, fin3_add_one_add_one, fin3_add_one_add_two, hR] at h
      rw [h2] at hQ'
      rw [hQ'] at h; rw [dist_comm]; exact h
  -- Chain edges on the line `QR`: parameters along it.
  have hpar := lineChain_params D.toDissection g cg hg hQR hgQ hgR hQseg hRc
  have hlineQR : ∀ e ∈ D.lineChain g cg, (D.tile e.1).carrier ⊆ {y | g y ≤ cg} := by
    intro e he y hy
    obtain ⟨-, -, hall⟩ := Dissection.mem_lineChain.mp he
    exact Tri.carrier_subset_halfplane _ g cg hall y hy
  have hedgeline : ∀ e ∈ D.lineChain g cg, ∀ y ∈ (D.tile e.1).edge e.2, g y = cg :=
    fun e he => D.toDissection.lineChain_edge_subset he
  -- **Step 4.** No chain edge along `QR` ends at `R`.
  have hRnot : ∀ eR ∈ D.lineChain g cg,
      ¬ ((D.tile eR.1).pts eR.2 = R ∨ (D.tile eR.1).pts (eR.2 + 1) = R) := by
    intro eR heR hRend
    obtain ⟨σu, σv, hσu, hσv, hσul, hσvl⟩ := hpar eR heR
    -- `eR` runs from `R` (parameter `1`) to parameter `σ ≠ 1`.
    obtain ⟨σ, hσ1, hRedge⟩ : ∃ σ : ℝ, σ ≠ 1 ∧
        (D.tile eR.1).edge eR.2 = segment ℝ R (AffineMap.lineMap Q R σ) := by
      have hne : σu ≠ σv := fun h => (D.tile eR.1).indep.injective.ne (fin3_ne_add_one eR.2)
        (by rw [hσul, hσvl, h])
      rcases hRend with h | h
      · have hu1 : σu = 1 := (AffineMap.lineMap_injective ℝ hQR)
          (by rw [← hσul, h, AffineMap.lineMap_apply_one])
        refine ⟨σv, fun h' => hne (hu1.trans h'.symm), ?_⟩
        rw [Tri.edge, h, hσvl]
      · have hv1 : σv = 1 := (AffineMap.lineMap_injective ℝ hQR)
          (by rw [← hσvl, h, AffineMap.lineMap_apply_one])
        refine ⟨σu, fun h' => hne (h'.trans hv1.symm), ?_⟩
        rw [Tri.edge, h, hσul, segment_symm]
    -- Every chain edge lies in `QR` or meets it in at most one point.
    have hdich : ∀ e ∈ D.lineChain g cg, (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∨
        ((D.tile e.1).edge e.2 ∩ segment ℝ Q R).Subsingleton := by
      intro e he
      obtain ⟨τu, τv, hτu, hτv, hτul, hτvl⟩ := hpar e he
      have hE : (D.tile e.1).edge e.2 = segment ℝ (AffineMap.lineMap Q R τu)
          (AffineMap.lineMap Q R τv) := by rw [Tri.edge, hτul, hτvl]
      by_cases h1 : τu ≤ 1 ∧ τv ≤ 1
      · left; rw [hE]; exact segment_param_subset ⟨hτu, h1.1⟩ ⟨hτv, h1.2⟩
      by_cases h2 : 1 ≤ τu ∧ 1 ≤ τv
      · right; rw [hE]; exact segment_param_inter_subsingleton hQR h2.1 h2.2
      exfalso
      -- `e` straddles `R`, so it overlaps `eR` along a segment.
      have hmin : min τu τv < 1 := by
        by_contra h; push Not at h; exact h2 ⟨(min_le_left _ _).trans' h, (min_le_right _ _).trans' h⟩
      have hmax : 1 < max τu τv := by
        by_contra h; push Not at h; exact h1 ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
      have hRe : R ∈ (D.tile e.1).edge e.2 := by
        have h1' : AffineMap.lineMap Q R (1 : ℝ) ∈ (D.tile e.1).edge e.2 := by
          rw [hE, lineMap_mem_segment_iff hQR, segment_eq_Icc']
          exact ⟨hmin.le, hmax.le⟩
        rwa [AffineMap.lineMap_apply_one] at h1'
      have hneR : e ≠ eR := by
        rintro rfl
        rcases hRend with h | h
        · have : τu = 1 := (AffineMap.lineMap_injective ℝ hQR)
            (by rw [← hτul, h, AffineMap.lineMap_apply_one])
          rw [this] at hmin hmax
          rcases le_total 1 τv with h' | h'
          · rw [min_eq_left h'] at hmin; linarith
          · rw [max_eq_left h'] at hmax; linarith
        · have : τv = 1 := (AffineMap.lineMap_injective ℝ hQR)
            (by rw [← hτvl, h, AffineMap.lineMap_apply_one])
          rw [this] at hmin hmax
          rcases le_total τu 1 with h' | h'
          · rw [max_eq_right h'] at hmax; linarith
          · rw [min_eq_right h'] at hmin; linarith
      -- A second common point, on the same side of `R` as the other end of `eR`.
      obtain ⟨z, hz1, hze, hzR⟩ : ∃ z : ℝ, z ≠ 1 ∧ z ∈ Set.Icc (min τu τv) (max τu τv) ∧
          z ∈ segment ℝ (1 : ℝ) σ := by
        rcases lt_or_gt_of_ne hσ1 with h | h
        · refine ⟨max σ (min τu τv), ne_of_lt (max_lt h hmin),
            ⟨le_max_right _ _, max_le (le_of_lt (h.trans hmax)) min_le_max⟩, ?_⟩
          rw [segment_eq_Icc', min_eq_right h.le, max_eq_left h.le]
          exact ⟨le_max_left _ _, (max_lt h hmin).le⟩
        · refine ⟨min σ (max τu τv), ne_of_gt (lt_min h hmax),
            ⟨le_min (le_of_lt (hmin.trans h)) min_le_max, min_le_right _ _⟩, ?_⟩
          rw [segment_eq_Icc', min_eq_left h.le, max_eq_right h.le]
          exact ⟨(lt_min h hmax).le, min_le_left _ _⟩
      have hz_e : AffineMap.lineMap Q R z ∈ (D.tile e.1).edge e.2 := by
        rw [hE, lineMap_mem_segment_iff hQR, segment_eq_Icc']; exact hze
      have hz_eR : AffineMap.lineMap Q R z ∈ (D.tile eR.1).edge eR.2 := by
        have : AffineMap.lineMap Q R z ∈ segment ℝ (AffineMap.lineMap Q R (1 : ℝ))
            (AffineMap.lineMap Q R σ) := (lineMap_mem_segment_iff hQR).mpr hzR
        rwa [AffineMap.lineMap_apply_one, ← hRedge] at this
      have hR_eR : R ∈ (D.tile eR.1).edge eR.2 := by rw [hRedge]; exact left_mem_segment _ _ _
      have hsubs := D.toDissection.sameside_edges_subsingleton g cg hg hneR (hlineQR e he)
        (hlineQR eR heR) (hedgeline e he) (hedgeline eR heR)
      have h1R : AffineMap.lineMap Q R (1 : ℝ) = R := AffineMap.lineMap_apply_one Q R
      have := hsubs ⟨hRe, hR_eR⟩ ⟨hz_e, hz_eR⟩
      exact hz1 ((AffineMap.lineMap_injective ℝ hQR) (h1R.trans this)).symm
    -- So the chain edges inside `QR` add up to `a`.
    have hsumQR := wall_sum D.toDissection g cg hg hQR hSQR hQRint hwallQR hdich
    rw [hQRa] at hsumQR
    set Fin' := (D.lineChain g cg).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Q R)
    have hlenF : ∀ e ∈ Fin', dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∨
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b := by
      intro e he
      have hsubQ := (Finset.mem_filter.mp he).2
      have hle : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≤ a := by
        rw [← hQRa]
        exact dist_le_of_mem_segment₂ (hsubQ (left_mem_segment _ _ _))
          (hsubQ (right_mem_segment _ _ _))
      rcases edge_len_mem D e.1 e.2 with h | h | h
      · left; rw [h, ha]
      · right; rw [h, hb]
      · rw [h, hc] at hle; linarith
    -- `e₁` is in it, and is a `b` edge.
    have hx1Q : x1 ≠ Q := by
      intro h; rw [h] at hx1; exact hQR (left_mem_openSegment_iff.mp hx1)
    have he1F : e1 ∈ Fin' := by
      refine Finset.mem_filter.mpr ⟨he1, ?_⟩
      refine (hdich e1 he1).resolve_right fun hs => hx1Q ?_
      exact hs ⟨hx1e, openSegment_subset_segment _ _ _ hx1⟩ ⟨hQe1, left_mem_segment _ _ _⟩
    have hb1 : dist (X.pts e1.2) (X.pts (e1.2 + 1)) = b := by
      rcases hlenF e1 he1F with h' | h'
      · exfalso
        rcases hlen1 with h | h <;> rw [h] at h'
        · exact habR h'.symm
        · exact absurd h' (by exact_mod_cast hac.ne')
      · exact h'
    by_cases hexa : ∃ e ∈ Fin', dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a
    · obtain ⟨e, heF, hea⟩ := hexa
      have hne : e ≠ e1 := by
        rintro rfl; exact habR (hea.symm.trans hb1)
      have h2 : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          + dist (X.pts e1.2) (X.pts (e1.2 + 1)) ≤ a := by
        rw [← hsumQR]
        have hsub2 : ({e, e1} : Finset (Fin N × Fin 3)) ⊆ Fin' := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact heF
          · rw [Finset.mem_singleton.mp hx]; exact he1F
        have := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) hsub2
          (fun _ _ _ => dist_nonneg)
        rw [Finset.sum_pair hne] at this
        exact this
      rw [hea, hb1] at h2
      linarith
    · push Not at hexa
      have hallb : ∀ e ∈ Fin', dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b :=
        fun e he => (hlenF e he).resolve_left (hexa e he)
      rw [Finset.sum_congr rfl hallb, Finset.sum_const, nsmul_eq_mul] at hsumQR
      have : a = Fin'.card * b := by exact_mod_cast hsumQR.symm
      exact hndvd ⟨Fin'.card, by rw [this, mul_comm]⟩
  -- **Step 5.** The chain edge through `R`: `R` is strictly inside an edge of a tile `T*` on the
  -- far side of `QR`.
  obtain ⟨eS, heS, hReS, -⟩ := exists_chain_edge_at D.toDissection g cg hg hQR.symm
    (by rw [segment_symm]; exact hSQR) (by rw [openSegment_symm]; exact hQRint)
    (by rw [openSegment_symm]; exact hwallQR)
  set TS := D.tile eS.1 with hTSdef
  have hRopen : R ∈ openSegment ℝ (TS.pts eS.2) (TS.pts (eS.2 + 1)) :=
    mem_openSegment_of_ne_left_right (fun h => hRnot eS heS (Or.inl h))
      (fun h => hRnot eS heS (Or.inr h)) hReS
  have hTSpi : TS.localAngle R = Real.pi := Tri.localAngle_openSegment TS eS.2 hRopen
  have hTSne : eS.1 ≠ eT.1 := hFQnot eS heS
  have hγpos : 0 < tileγ D := by
    rcases (angle_nonneg (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)).lt_or_eq with h | h
    · exact h
    · exact absurd h.symm (hv0 2)
  -- `R` is interior to `ABC`: the angles there exceed `π`.
  have hRint : R ∈ interior D.target.carrier := by
    by_contra hRi
    have hRfr : R ∈ frontier D.target.carrier := ⟨subset_closure hRtgt, hRi⟩
    have h2 : TS.localAngle R + T.localAngle R ≤ D.target.localAngle R := by
      rw [← D.toDissection.sum_localAngle_eq R]
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun i => (D.tile i).localAngle R) (Finset.subset_univ {eS.1, eT.1})
        (fun i _ _ => (D.tile i).localAngle_nonneg R)
      rw [Finset.sum_pair hTSne] at hsub
      exact hsub
    rw [hTSpi, hTRγ] at h2
    by_cases hv : R ∈ Set.range D.target.pts
    · obtain ⟨j, hj⟩ := hv
      rw [← hj, Tri.localAngle_vertex] at h2
      have := angle_le_pi (D.target.pts (j + 1)) (D.target.pts j) (D.target.pts (j + 2))
      rw [cornerAngle] at h2
      linarith
    · rw [D.target.localAngle_frontier hRfr hv] at h2
      linarith
  -- Just beyond `R` on the line `PR` lies inside `T*`.
  obtain ⟨cR0, cR1, cR2⟩ := Tri.coord_openSegment TS eS.2 hRopen
  obtain ⟨hgu, hgv, hgall⟩ := Dissection.mem_lineChain.mp heS
  have hlev := level_eq_coord TS g cg (eS.2 + 2) (by rw [fin3_add_two_add_one]; exact hgu)
    (by rw [fin3_add_two_add_two]; exact hgv)
  have hgk : g (TS.pts (eS.2 + 2)) < cg := by
    rcases (hgall (eS.2 + 2)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hg
      have hall : ∀ Y, g Y = cg := fun Y => by have := hlev Y; rw [h, sub_self, mul_zero] at this; linarith
      have hc0 : cg = 0 := by rw [← hall 0, map_zero]
      ext Y; simp [hall Y, hc0]
  have hcP : TS.basis.coord (eS.2 + 2) P < 0 := by
    have h := hlev P
    by_contra hge; push Not at hge
    have : TS.basis.coord (eS.2 + 2) P * (g (TS.pts (eS.2 + 2)) - cg) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hge (by linarith)
    linarith
  obtain ⟨ε1, hε1, hε1p⟩ := exists_small_pos (b := TS.basis.coord eS.2 R - TS.basis.coord eS.2 P) cR0
  obtain ⟨ε2, hε2, hε2p⟩ := exists_small_pos
    (b := TS.basis.coord (eS.2 + 1) R - TS.basis.coord (eS.2 + 1) P) cR1
  have hbeyond : ∀ ε : ℝ, 0 < ε → ε < min ε1 ε2 →
      AffineMap.lineMap P R (1 + ε) ∈ interior TS.carrier := by
    intro ε hε hεlt
    rw [Tri.mem_interior_iff_coord_pos]
    intro i
    have hY : ∀ j : Fin 3, TS.basis.coord j (AffineMap.lineMap P R (1 + ε))
        = TS.basis.coord j R + ε * (TS.basis.coord j R - TS.basis.coord j P) := by
      intro j; rw [Tri.coord_lineMap]; ring
    rcases fin3_three i eS.2 with h | h | h <;> rw [h, hY]
    · exact hε1p ε hε (lt_of_lt_of_le hεlt (min_le_left _ _))
    · exact hε2p ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
    · rw [cR2]; nlinarith
  -- The line `PR`, oriented so that `Q` is on the side `h > ch`.
  obtain ⟨mPR, hmPR, hmQ⟩ : ∃ m : Fin 3, T.edge m = segment ℝ P R ∧ T.pts (m + 2) = Q := by
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨k + 2, ?_, ?_⟩
      · rw [Tri.edge, fin3_add_two_add_one, hR, ← h1, hP, segment_symm]
      · rw [fin3_add_two_add_two, ← h2, hQ]
    · refine ⟨k + 1, ?_, ?_⟩
      · rw [Tri.edge, fin3_add_one_add_one, hR, ← h1, hP]
      · rw [fin3_add_one_add_two, ← h2, hQ]
  obtain ⟨hh, ch, hhne, hhline, hhQ⟩ := edge_level_oriented T mPR
  rw [hmPR] at hhline
  rw [hmQ] at hhQ
  have hhP : hh P = ch := hhline P (left_mem_segment _ _ _)
  have hhR : hh R = ch := hhline R (right_mem_segment _ _ _)
  have hSPR : segment ℝ P R ⊆ {y | hh y = ch} := fun y hy => hhline y hy
  have hFPnot : ∀ e ∈ D.lineChain hh ch, e.1 ≠ eT.1 :=
    lineChain_tile_ne D.toDissection hh ch (i := eT.1) (j := iQ) (by rw [hQ]; exact hhQ)
  have hPtgt : P ∈ D.target.carrier := hP ▸ htgt eT.1 iP
  have hPRint : openSegment ℝ P R ⊆ interior D.target.carrier := by
    rw [openSegment_symm]
    exact D.target.convex.openSegment_interior_closure_subset_interior hRint
      (subset_closure hPtgt)
  have hwallPR : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have : y ∈ T.edge mPR := by rw [hmPR]; exact openSegment_subset_segment _ _ _ hy
    exact D.toDissection.edge_point_not_interior this
  have hparP := lineChain_params D.toDissection hh ch hhne hPR hhP hhR hPseg hRc
  -- No chain edge along `PR` reaches past `R`: past `R` is inside `T*`.
  have hdichP : ∀ e ∈ D.lineChain hh ch, (D.tile e.1).edge e.2 ⊆ segment ℝ P R ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ P R).Subsingleton := by
    intro e he
    obtain ⟨τu, τv, hτu, hτv, hτul, hτvl⟩ := hparP e he
    have hE : (D.tile e.1).edge e.2 = segment ℝ (AffineMap.lineMap P R τu)
        (AffineMap.lineMap P R τv) := by rw [Tri.edge, hτul, hτvl]
    by_cases h1 : τu ≤ 1 ∧ τv ≤ 1
    · left; rw [hE]; exact segment_param_subset ⟨hτu, h1.1⟩ ⟨hτv, h1.2⟩
    right
    have hmax : 1 < max τu τv := by
      by_contra h; push Not at h; exact h1 ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
    by_cases h2 : 1 < min τu τv
    · rw [hE]
      exact segment_param_inter_subsingleton hPR ((min_le_left _ _).trans' h2.le)
        ((min_le_right _ _).trans' h2.le)
    exfalso
    push Not at h2
    set ε := min (min ε1 ε2) (max τu τv - 1) / 2 with hεdef
    have hε0 : 0 < ε := by
      have : 0 < min (min ε1 ε2) (max τu τv - 1) := lt_min (lt_min hε1 hε2) (by linarith)
      positivity
    have hεlt : ε < min ε1 ε2 := by
      have := min_le_left (min ε1 ε2) (max τu τv - 1)
      have : 0 < min ε1 ε2 := lt_min hε1 hε2
      linarith
    have hεmax : 1 + ε ≤ max τu τv := by
      have := min_le_right (min ε1 ε2) (max τu τv - 1)
      linarith
    have hin : AffineMap.lineMap P R (1 + ε) ∈ (D.tile e.1).edge e.2 := by
      rw [hE, lineMap_mem_segment_iff hPR, segment_eq_Icc']
      exact ⟨by linarith, hεmax⟩
    exact D.toDissection.edge_point_not_interior hin eS.1 (hbeyond ε hε0 hεlt)
  have hsumPR := wall_sum D.toDissection hh ch hhne hPR hSPR hPRint hwallPR hdichP
  -- `|PR| = b`.
  have hPRb : dist P R = b := by
    have h := (opp_side D hγ hirr eT.1 iQ).2.1 (by rw [hQ]; exact hTQβ)
    rw [hb] at h
    have hP' := hP
    rcases hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, fin3_add_one_add_one, fin3_add_one_add_two, hR] at h
      rw [h1] at hP'
      rw [hP'] at h; rw [dist_comm]; exact h
    · rw [h2, hR] at h
      rw [h1] at hP'
      rw [hP'] at h; exact h
  rw [hPRb] at hsumPR
  -- The first edge along `PR` at `P`: its tile has its `β` at `P`.
  obtain ⟨e2, he2, hPe2, x2, hx2, hx2e⟩ :=
    exists_chain_edge_at D.toDissection hh ch hhne hPR hSPR hPRint hwallPR
  have hX2ne : e2.1 ≠ eT.1 := hFPnot e2 he2
  set X2 := D.tile e2.1 with hX2def
  -- The angle counts at `P`.
  have hPfr : P ∈ frontier D.target.carrier := tri_side_subset_frontier D.target 0 hPseg
  have hcP : angleCount D P Real.pi = 0 ∧ angleCount D P (tileα D) ≤ 1 := by
    have hαP := angleCount_pos D (i := eT.1) hTPα
    by_cases hPB : P = D.target.pts 1
    · have hloc : D.target.localAngle P = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
        rw [hPB, Tri.localAngle_vertex]
        show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
        have hTsum := cornerAngle_sum D.target
        have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
        have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
          rw [cornerAngle, angle_comm]; exact hC
        push_cast; linarith
      have := vertex_relations D hγ hirr P (-2) 1 hloc
      constructor <;> omega
    · have hPnc : P ∉ Set.range D.target.pts := by
        rintro ⟨j, hj⟩
        have hc2 := coord_two_of_mem_side D.target hPseg
        rw [← hj, Tri.coord_vertex] at hc2
        fin_cases j
        · exact hPA hj.symm
        · exact hPB hj.symm
        · simp at hc2
      have hPE : P ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
          part.image (fun e => (D.tile e.1).pts (e.2 + 1))) := by
        rcases hPend with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨eT, heTp, h'⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨eT, heTp, h'⟩)
      obtain ⟨eSP, -, -, -, heSPγ⟩ :=
        no28_step2 D hγ hirr hA hC part hcov hdisj eT heT hPE hPA hPB
      obtain ⟨cαP, -, -, cπP, -⟩ := counts_at_side D hγ hirr hPfr hPnc (angleCount_pos D heSPγ)
      exact ⟨cπP, cαP.le⟩
  have hPend2 := endpoint_of_ne_pi X2 e2.2 hPe2
    (fun h => by have := angleCount_pos D h; omega)
  obtain ⟨jP, jW2, hjidx2, hjP⟩ : ∃ jP jW : Fin 3,
      ((jP = e2.2 ∧ jW = e2.2 + 1) ∨ (jP = e2.2 + 1 ∧ jW = e2.2)) ∧ X2.pts jP = P := by
    rcases hPend2 with h | h
    · exact ⟨e2.2, e2.2 + 1, Or.inl ⟨rfl, rfl⟩, h.symm⟩
    · exact ⟨e2.2 + 1, e2.2, Or.inr ⟨rfl, rfl⟩, h.symm⟩
  have hjPW : jW2 ≠ jP := by
    rcases hjidx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact (fin3_ne_add_one e2.2).symm
    · exact fin3_ne_add_one e2.2
  have hedge2 : X2.edge e2.2 = segment ℝ P (X2.pts jW2) := by
    rcases hjidx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Tri.edge, ← h2, ← h1, hjP]
    · rw [Tri.edge, ← h1, ← h2, hjP, segment_symm]
  have hhW : hh (X2.pts jW2) = ch := by
    obtain ⟨hu, hv, -⟩ := Dissection.mem_lineChain.mp he2
    rcases hjidx2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact hv
    · exact hu
  obtain ⟨w2, hW2l⟩ := eq_lineMap_of_level hhne hPR hhP hhR hhW
  have hw2 : 0 < w2 := by
    rw [openSegment_eq_image_lineMap] at hx2
    obtain ⟨l2, ⟨hl0, hl1⟩, rfl⟩ := hx2
    rw [hedge2, hW2l] at hx2e
    have h0 : AffineMap.lineMap P R l2 ∈ segment ℝ (AffineMap.lineMap P R (0 : ℝ))
        (AffineMap.lineMap P R w2) := by rwa [AffineMap.lineMap_apply_zero]
    rw [lineMap_mem_segment_iff hPR, segment_eq_uIcc] at h0
    rcases Set.mem_uIcc.mp h0 with h | h
    · linarith [h.2]
    · linarith [h.1, h.2]
  have hX2β : X2.localAngle P = tileβ D := by
    rcases localAngle_at_own_vertex_mem' D e2.1 jP with h | h | h <;> rw [hjP] at h
    · exact absurd (eq_of_angleCount_le_one D hcP.2 h hTPα) hX2ne
    · exact h
    · exfalso
      by_cases hPB : P = D.target.pts 1
      · rw [hPB] at h; exact ne_of_angleCount_zero D cγB e2.1 h
      -- `X₂` is the tile on `AB` with its `γ` at `P`; its angle there is `α` or `π - α`.
      have hPE : P ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
          part.image (fun e => (D.tile e.1).pts (e.2 + 1))) := by
        rcases hPend with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨eT, heTp, h'⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨eT, heTp, h'⟩)
      obtain ⟨eSP, heSP, -, heSPend, heSPγ⟩ :=
        no28_step2 D hγ hirr hA hC part hcov hdisj eT heT hPE hPA hPB
      have hPnc : P ∉ Set.range D.target.pts := by
        rintro ⟨j, hj⟩
        have hc2 := coord_two_of_mem_side D.target hPseg
        rw [← hj, Tri.coord_vertex] at hc2
        fin_cases j
        · exact hPA hj.symm
        · exact hPB hj.symm
        · simp at hc2
      obtain ⟨-, -, cγP, -, -⟩ := counts_at_side D hγ hirr hPfr hPnc (angleCount_pos D heSPγ)
      have hXS : e2.1 = eSP.1 := eq_of_angleCount_le_one D cγP.le h heSPγ
      obtain ⟨jY, hjYP, hYseg⟩ : ∃ jY : Fin 3, X2.pts jY ≠ P ∧
          X2.pts jY ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
        rcases heSPend with h' | h'
        · refine ⟨eSP.2 + 1, ?_, ?_⟩
          · rw [hX2def, hXS, ← h']
            exact (D.tile eSP.1).indep.injective.ne (fin3_ne_add_one eSP.2).symm
          · rw [hX2def, hXS]; exact hsub eSP heSP (right_mem_segment _ _ _)
        · refine ⟨eSP.2, ?_, ?_⟩
          · rw [hX2def, hXS, ← h']
            exact (D.tile eSP.1).indep.injective.ne (fin3_ne_add_one eSP.2)
          · rw [hX2def, hXS]; exact hsub eSP heSP (left_mem_segment _ _ _)
      obtain ⟨y, -, hYl⟩ := hparam _ hYseg
      have hjYP' : jY ≠ jP := fun h => hjYP (by rw [h, hjP])
      have hjYW : jY ≠ jW2 := by
        intro h
        have h1 := coord_two_of_mem_side D.target hYseg
        rw [h, hW2l, Tri.coord_lineMap, coord_two_of_mem_side D.target hPseg] at h1
        have : 0 < w2 * D.target.basis.coord 2 R := mul_pos hw2 hRc
        linarith
      have hyp : y ≠ p := fun h => hjYP (by rw [hYl, hPl, h])
      have hcorner := corner_from_line X2 hjYP' hjPW hjYW (A := D.target.pts 0)
        (B := D.target.pts 1) (R := R) (v := p) (y := y) (z := q) (w := w2)
        (by rw [hjP, hPl]) hYl (by rw [hW2l, ← hPl]) hw2 hyp hpq.symm
      rw [← hPl, ← hQl, hcornerP, ← Tri.localAngle_vertex, hjP, h] at hcorner
      rcases hcorner with h' | h'
      · exact hαγ h'.symm
      · rw [hγ] at h'
        exact hirr ⟨1 / 3, by push_cast; linarith⟩
  -- So `e₂` is an `a` or `c` edge, not a `b` edge.
  have hbc : (b : ℝ) ≠ c := by
    intro h
    have h' : b = c := by exact_mod_cast h
    exact er2 ⟨0, 1, by rw [h']; ring⟩
  have hlen2 : dist (X2.pts e2.2) (X2.pts (e2.2 + 1)) = a ∨
      dist (X2.pts e2.2) (X2.pts (e2.2 + 1)) = c := by
    have hs := opp_side D hγ hirr e2.1 (e2.2 + 2)
    rw [fin3_add_two_add_one, fin3_add_two_add_two, ha, hc] at hs
    have hne : e2.2 + 2 ≠ jP := by
      rcases hjidx2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact (fin3_add_two_ne e2.2).1
      · exact (fin3_add_two_ne e2.2).2
    rcases localAngle_at_own_vertex_mem' D e2.1 (e2.2 + 2) with h | h | h
    · exact Or.inl (hs.1 h)
    · exact absurd (corner_unique D hγ hirr e2.1 (Or.inr (Or.inl rfl)) h
        (by rw [hjP]; exact hX2β)) hne
    · exact Or.inr (hs.2.2 h)
  -- The edges along `PR` add up to `b`, so `b = p a + q c`.
  set FP := (D.lineChain hh ch).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R)
  have hx2P : x2 ≠ P := by
    intro h; rw [h] at hx2; exact hPR (left_mem_openSegment_iff.mp hx2)
  have he2F : e2 ∈ FP := by
    refine Finset.mem_filter.mpr ⟨he2, ?_⟩
    refine (hdichP e2 he2).resolve_right fun hs => hx2P ?_
    exact hs ⟨hx2e, openSegment_subset_segment _ _ _ hx2⟩ ⟨hPe2, left_mem_segment _ _ _⟩
  have hacR' : (a : ℝ) ≠ c := hacR.ne
  by_cases hexb : ∃ e ∈ FP, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b
  · obtain ⟨e, heF, heb⟩ := hexb
    have hne : e ≠ e2 := by
      rintro rfl
      rcases hlen2 with h | h
      · exact habR (h.symm.trans heb)
      · exact hbc (heb.symm.trans h)
    have h2 : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        + dist (X2.pts e2.2) (X2.pts (e2.2 + 1)) ≤ b := by
      rw [← hsumPR]
      have hsub2 : ({e, e2} : Finset (Fin N × Fin 3)) ⊆ FP := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact heF
        · rw [Finset.mem_singleton.mp hx]; exact he2F
      have := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) hsub2
        (fun _ _ _ => dist_nonneg)
      rw [Finset.sum_pair hne] at this
      exact this
    rw [heb] at h2
    rcases hlen2 with h | h <;> rw [h] at h2
    · linarith
    · have : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
      linarith
  · push Not at hexb
    have hac' : ∀ e ∈ FP, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∨
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c := by
      intro e he
      rcases edge_len_mem D e.1 e.2 with h | h | h
      · left; rw [h, ha]
      · exact absurd (by rw [h, hb]) (hexb e he)
      · right; rw [h, hc]
    have hpt : ∀ e ∈ FP, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        (if dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a then (a : ℝ) else 0)
        + (if dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c then (c : ℝ) else 0) := by
      intro e he
      rcases hac' e he with h | h
      · rw [if_pos h, if_neg (by rw [h]; exact hacR'), h]; ring
      · rw [if_neg (by rw [h]; exact hacR'.symm), if_pos h, h]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_filter,
      ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      at hsumPR
    obtain ⟨p', q', hpq⟩ : ∃ p' q' : ℕ, (p' : ℝ) * a + q' * c = b := ⟨_, _, hsumPR⟩
    exact er2 ⟨p', q', by exact_mod_cast hpq.symm⟩

end TriangleTiling
