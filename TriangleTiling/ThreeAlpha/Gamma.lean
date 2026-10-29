/-
Laczkovich's graph `Γ_a` for the tile with `3α + 2β = π` (Section 4 of M. Beeson, *Triangle tiling:
the case 3α + 2β = π*, arXiv 1206.2229v4): propagation (`lemma:apropagation`), with `α ∉ ℚπ` as a
hypothesis. The labeled statement is in `TriangleTiling.Laczkovich.ThreeAlphaTriquadratic`.

At the end `R` of a link, the angle sum of the tiles with a vertex at `R` is `π` (one tile has `R`
inside an edge), so `R` has type `(3, 2, 0)` or `(1, 1, 1)`, and exactly two `a` edges end at `R`
(one from each tile with its `β` or `γ` angle there). Bonfioli's parity argument (`out_of_in`) then
continues the link.
-/
import TriangleTiling.ThreeAlpha.Relations
import TriangleTiling.ThreeAlpha.Coloring
import TriangleTiling.Isosceles.TwoBeta
import TriangleTiling.Isosceles.GammaStart
import TriangleTiling.ThreeAlpha.Areas

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
  (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel

omit D in
/-- `α` and `β` are linearly independent over `ℤ`. -/
theorem int_indep {x y : ℤ} (e : (x : ℝ) * α + y * β = 0) : x = 0 ∧ y = 0 := by
  have key : ((x : ℝ) - 3 * y / 2) * α = -((y : ℝ) / 2) * Real.pi := by
    linear_combination e - (y : ℝ) / 2 * hrel
  by_cases hc : (x : ℝ) - 3 * y / 2 = 0
  · have hy : (y : ℝ) * Real.pi = 0 := by rw [hc, zero_mul] at key; linarith
    have hy' : (y : ℝ) = 0 := by
      rcases mul_eq_zero.mp hy with e | e
      · exact e
      · exact absurd e Real.pi_ne_zero
    have hx' : (x : ℝ) = 0 := by rw [hy'] at hc; linarith
    exact ⟨by exact_mod_cast hx', by exact_mod_cast hy'⟩
  · exfalso
    apply hirr
    refine ⟨-((y : ℚ) / 2) / ((x : ℚ) - 3 * y / 2), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hc]
    linear_combination key

include h

/-- The model's angles at its vertices `0, 1, 2` are `α`, `β`, `2α + β` in some order. -/
theorem model_angles : ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = α ∧
    D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = 2 * α + β := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  exact ⟨σ, h0, h1, h2⟩

/-- The values `α, β, γ, π, 2π` (`γ = 2α + β`) are distinct and nonzero. -/
theorem values_sep :
    (∀ j, ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] j ≠ 0) ∧
      Function.Injective ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] := by
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · fin_cases j <;> simp <;> linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | exact hαβ hij | exact hαβ hij.symm | linarith

/-- The model's angles at vertices `0, 1, 2` (`tileα D`, `tileβ D`, `tileγ D` of the isosceles
files) are separated, as `card_marked` needs. -/
theorem anglesSep : AnglesSep D := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  obtain ⟨hv0, hinj⟩ := values_sep D hirr hrel h
  have hm : ∀ k : Fin 3, D.model.angleAt k = α ∨ D.model.angleAt k = β ∨
      D.model.angleAt k = 2 * α + β := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    fin_cases m
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  have e0 : tileα D = D.model.angleAt 0 := rfl
  have e1 : tileβ D = D.model.angleAt 1 := rfl
  have e2 : tileγ D = D.model.angleAt 2 := rfl
  have hd : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := by
    intro i j hij e
    obtain ⟨m, rfl⟩ := σ.surjective i
    obtain ⟨m', rfl⟩ := σ.surjective j
    have hmm : m ≠ m' := fun h => hij (by rw [h])
    have v : ∀ m : Fin 3, D.model.angleAt (σ m) = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi]
        (Fin.castLE (by norm_num) m) := by
      intro m; fin_cases m <;> simp [h0, h1, h2]
    rw [v, v] at e
    exact hmm (Fin.castLE_injective _ (hinj e))
  have hp : ∀ k, 0 < D.model.angleAt k := fun k => D.model.angleAt_pos' k
  have hl : ∀ k, D.model.angleAt k < Real.pi := fun k => tri_angle_lt_pi D.model k
  have hπ := Real.pi_pos
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · fin_cases j <;> simp [e0, e1, e2]
    · exact (hp 0).ne'
    · exact (hp 1).ne'
    · exact (hp 2).ne'
  · fin_cases i <;> fin_cases j <;> simp [e0, e1, e2] at hij ⊢ <;>
      first
      | exact hd _ _ (by decide) hij
      | (have := hl 0; linarith) | (have := hl 1; linarith) | (have := hl 2; linarith)
      | linarith

/-- Each tile has at `P` one of the angles `α, β, γ`, a straight angle, a full angle, or nothing. -/
theorem localAngle_cases (P : Plane) (i : Fin N) :
    (∃ j, (D.tile i).localAngle P = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] j) ∨
      (D.tile i).localAngle P = 0 := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  have hm : ∀ k : Fin 3, ∃ j : Fin 5, D.model.angleAt k = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] j := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    fin_cases m
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  rcases localAngle_mem D P i with e | e | e | e | e | e
  · obtain ⟨j, hj⟩ := hm 0; exact Or.inl ⟨j, e.trans hj⟩
  · obtain ⟨j, hj⟩ := hm 1; exact Or.inl ⟨j, e.trans hj⟩
  · obtain ⟨j, hj⟩ := hm 2; exact Or.inl ⟨j, e.trans hj⟩
  · exact Or.inl ⟨3, e⟩
  · exact Or.inl ⟨4, e⟩
  · exact Or.inr e

/-- **The angle sum at a point**, in the counts of the angles there. -/
theorem counts_sum (P : Plane) :
    (angleCount D P α : ℝ) * α + angleCount D P β * β + angleCount D P (2 * α + β) * (2 * α + β)
      + angleCount D P Real.pi * Real.pi + angleCount D P (2 * Real.pi) * (2 * Real.pi)
      = D.target.localAngle P := by
  classical
  obtain ⟨hv0, hinj⟩ := values_sep D hirr hrel h
  have hc := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj
    (localAngle_cases D hirr hrel h P)
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five] at hc
  rw [hc]
  simp only [angleCount]
  rfl

open Classical in
/-- The `a` edges at `Q` are counted by the tiles with their `β` or `γ` angle there. -/
theorem card_a (Q : Plane) :
    ((edgesAt D.toDissection Q).filter (edgeType D α)).card
      = angleCount D Q β + angleCount D Q (2 * α + β) := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  have hφ : α = tileα D ∨ α = tileβ D ∨ α = tileγ D := by
    have : ∀ k : Fin 3, D.model.angleAt k = tileα D ∨ D.model.angleAt k = tileβ D ∨
        D.model.angleAt k = tileγ D := by
      intro k; fin_cases k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases this (σ 0) with e | e | e <;> rw [h0] at e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  have hcm := card_marked D (anglesSep D hirr hrel h) Q hφ
  have hsum : angleCount D Q (tileα D) + angleCount D Q (tileβ D) + angleCount D Q (tileγ D)
      = angleCount D Q α + angleCount D Q β + angleCount D Q (2 * α + β) := by
    have e := Equiv.sum_comp σ (fun k => angleCount D Q (D.model.angleAt k))
    simp only [Fin.sum_univ_three] at e
    rw [h0, h1, h2] at e
    exact e.symm
  omega

open Classical in
/-- **At the end of a link of `Γ_a` exactly two `a` edges end**; in particular an even number. -/
theorem a_even_end {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c₀ : ℝ}
    (hl : LinkData D.toDissection (edgeType D α) Q R g c₀) :
    Even ((edgesAt D.toDissection R).filter (edgeType D α)).card := by
  have hs := counts_sum D hirr hrel h R
  rw [Tri.localAngle_interior _ hl.end_interior] at hs
  obtain ⟨ε, -, hRε⟩ := hl.across
  have hπ1 := angleCount_pos D (Tri.localAngle_openSegment _ ε.2 hRε)
  obtain ⟨i, k, hik⟩ := hl.end_vertex
  have hv : 1 ≤ angleCount D R α + angleCount D R β + angleCount D R (2 * α + β) := by
    have := localAngle_pts (D.tile i) k
    rw [hik] at this
    rcases tile_angle_mem D h i k with e | e | e <;> rw [e] at this
    · have := angleCount_pos D this; omega
    · have := angleCount_pos D this; omega
    · have := angleCount_pos D this; omega
  set nα := angleCount D R α
  set nβ := angleCount D R β
  set nγ := angleCount D R (2 * α + β)
  set nπ := angleCount D R Real.pi
  set n2 := angleCount D R (2 * Real.pi)
  have key := int_indep hirr hrel (x := nα + 2 * nγ + 3 * (nπ + 2 * n2) - 6)
    (y := nβ + nγ + 2 * (nπ + 2 * n2) - 4) (by push_cast; linear_combination hs + (nπ + 2 * n2 - 2 : ℝ) * hrel)
  rw [card_a D hirr hrel h R]
  exact ⟨1, by omega⟩

open Classical in
/-- `lemma:apropagation`, with `α ∉ ℚπ`. -/
theorem propagation_irr (hnorel : ¬ HasRelation D.toDissection (edgeType D α)) :
    (∀ P Q, IsLink D.toDissection (edgeType D α) P Q →
      ∃ R, IsLink D.toDissection (edgeType D α) Q R) ∧
    (∀ v : Plane, (∃ w, IsLink D.toDissection (edgeType D α) v w ∨
        IsLink D.toDissection (edgeType D α) w v) →
      ((vertexFinset D.toDissection).filter
          fun u => IsLink D.toDissection (edgeType D α) u v).card = 1 ∧
      ((vertexFinset D.toDissection).filter
          fun w => IsLink D.toDissection (edgeType D α) v w).card = 1) ∧
    (∀ X Y, IsLink D.toDissection (edgeType D α) X Y → X ∉ frontier D.target.carrier) := by
  set θ := edgeType D α
  set V := vertexFinset D.toDissection
  have hi : ∀ Q R, IsLink D.toDissection θ Q R → ∃ R', IsLink D.toDissection θ R R' := by
    rintro Q R ⟨g, c, hl⟩
    exact out_of_in D.toDissection θ hl (a_even_end D hirr hrel h hl) hnorel
  have hge : ∀ v ∈ V, (V.filter fun u => IsLink D.toDissection θ u v).card ≤
      (V.filter fun w => IsLink D.toDissection θ v w).card := by
    intro v _
    rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D.toDissection θ u v).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨R', hR'⟩ := hi u v (Finset.mem_filter.mp hu).2
      have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
        Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr
          ⟨(link_mem_vertexFinset D.toDissection θ hR').2, hR'⟩⟩
      linarith [in_le_one D.toDissection θ V v]
  have heq := (Finset.sum_eq_sum_iff_of_le hge).mp (sum_out_eq_sum_in D.toDissection θ V).symm
  have hdeg : ∀ v ∈ V, (V.filter fun u => IsLink D.toDissection θ u v).card
      = (V.filter fun w => IsLink D.toDissection θ v w).card ∧
      (V.filter fun u => IsLink D.toDissection θ u v).card ≤ 1 :=
    fun v hv => ⟨heq v hv, in_le_one D.toDissection θ V v⟩
  refine ⟨hi, fun v hv => ?_, fun X Y hXY hX => ?_⟩
  · obtain ⟨w, hw | hw⟩ := hv
    · have hvV := (link_mem_vertexFinset D.toDissection θ hw).1
      have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
        Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr
          ⟨(link_mem_vertexFinset D.toDissection θ hw).2, hw⟩⟩
      obtain ⟨e1, e2⟩ := hdeg v hvV
      omega
    · have hvV := (link_mem_vertexFinset D.toDissection θ hw).2
      have : 1 ≤ (V.filter fun u => IsLink D.toDissection θ u v).card :=
        Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr
          ⟨(link_mem_vertexFinset D.toDissection θ hw).1, hw⟩⟩
      obtain ⟨e1, e2⟩ := hdeg v hvV
      omega
  · have hXV := (link_mem_vertexFinset D.toDissection θ hXY).1
    have hout : 1 ≤ (V.filter fun w => IsLink D.toDissection θ X w).card :=
      Finset.card_pos.mpr ⟨Y, Finset.mem_filter.mpr
        ⟨(link_mem_vertexFinset D.toDissection θ hXY).2, hXY⟩⟩
    obtain ⟨e1, -⟩ := hdeg X hXV
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (V.filter fun u => IsLink D.toDissection θ u X).card
      by omega)
    obtain ⟨g, c, hl⟩ := (Finset.mem_filter.mp hu).2
    exact hX.2 hl.end_interior

end TriangleTiling.ThreeAlpha
