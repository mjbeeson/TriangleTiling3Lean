/-
Tile counts at the vertices of `ABC`, the five shapes, and the coloring theorem for
M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4), Sections 2–4.

Here `α ∉ ℚπ` is a hypothesis: it is `lemma:angles` (Laczkovich), proved in
`TriangleTiling.Laczkovich.ThreeAlpha`, where the theorems named after the paper's labels are
stated as printed. The tile is given by Bonfioli's `ThreeAlphaData α β a b c` (angles `α`, `β`,
`2α + β` opposite `a`, `b`, `c`).

* Counts (`lemma:nogamma`, `lemma:shapes`): Bonfioli's `lemma6` and `lemma11`, translated from his
  `vcount` (tiles by local angle) to `tilesAt` and `anglesAt`.
* Coloring (`lemma:signedtiles`, `theorem:coloring`, `lemma:Mnotzero`): Bonfioli's flux coloring
  (`flux_colouring`, the sign of the `Φ₁`-value of each tile) and the uniqueness of proper
  colorings up to sign (`colouring_unique'`). The paper's normalization (a tile at `B` with an
  edge on `AB` is black) is proved here: such a tile's edge on `AB` has the direction of `AB`
  (`eDir_of_side`), so its sign is the weight of that direction.
-/
import Erdos634.Draft.BeesonShapesL5L6L11
import Erdos634.Draft.BeesonColoringThm1Colour
import Erdos634.Draft.BeesonColoringConn
import Erdos634.Draft.FluxBoundary
import Erdos634.Draft.FluxCRow12
import TriangleTiling.ThreeAlpha.Defs

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-! ### Local angles at the vertices of `ABC` -/

theorem localAngle_pts (T : Tri) (l : Fin 3) : T.localAngle (T.pts l) = T.angleAt l :=
  T.localAngle_vertex l

/-- A local angle other than `0`, `π`, `2π` is taken at a vertex. -/
theorem vertex_of_localAngle (T : Tri) {p : Plane} {x : ℝ} (h : T.localAngle p = x)
    (h0 : x ≠ 0) (hπ : x ≠ Real.pi) (h2π : x ≠ 2 * Real.pi) : ∃ l, T.pts l = p := by
  classical
  unfold Tri.localAngle at h
  split_ifs at h with h1
  · exact ⟨h1.choose, h1.choose_spec.symm⟩
  · exact absurd h.symm h2π
  · exact absurd h.symm hπ
  · exact absurd h.symm h0

/-- A tile at a point has the local angle there of its angle at that vertex. -/
theorem localAngle_iff (T : Tri) (p : Plane) {x : ℝ} (h0 : x ≠ 0) (hπ : x ≠ Real.pi)
    (h2π : x ≠ 2 * Real.pi) : T.localAngle p = x ↔ ∃ l, T.pts l = p ∧ T.angleAt l = x := by
  constructor
  · intro h
    obtain ⟨l, rfl⟩ := vertex_of_localAngle T h h0 hπ h2π
    exact ⟨l, rfl, (localAngle_pts T l).symm.trans h⟩
  · rintro ⟨l, rfl, hl⟩
    exact (localAngle_pts T l).trans hl

variable {α β a b c : ℝ}

/-- Every tile is a copy of the tile `(α, β, 2α + β)`. -/
theorem tile_threeAlpha (h : D.model.ThreeAlphaData α β a b c) (i : Fin N) :
    (D.tile i).ThreeAlphaData α β a b c := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := h
  obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
  refine ⟨σ.trans τ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.trans_apply, (hτ _).1, (hτ _).2, Equiv.apply_symm_apply] <;> assumption

theorem tile_angle_mem (h : D.model.ThreeAlphaData α β a b c) (i : Fin N) (l : Fin 3) :
    (D.tile i).angleAt l = α ∨ (D.tile i).angleAt l = β ∨ (D.tile i).angleAt l = 2 * α + β := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := tile_threeAlpha D h i
  obtain ⟨m, rfl⟩ := σ.surjective l
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm with rfl | rfl | rfl
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

theorem angles_pos (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) :
    0 < α ∧ 0 < β ∧ α < Real.pi / 3 ∧ β < Real.pi / 2 := by
  obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos h
  refine ⟨hα, hβ, by linarith, by linarith⟩

/-- `vcount` (tiles by local angle) is `anglesAt` for the tile's angles. -/
theorem vcount_eq_anglesAt (k : Fin 3) {x : ℝ} (hx0 : x ≠ 0) (hxπ : x ≠ Real.pi)
    (hx2π : x ≠ 2 * Real.pi) : vcount D k x = anglesAt D k x := by
  unfold vcount anglesAt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact localAngle_iff _ _ hx0 hxπ hx2π

/-- Three distinct elements of `Fin 3` are the values of a permutation. -/
theorem perm3 (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ τ : Equiv.Perm (Fin 3), τ 0 = i ∧ τ 1 = j ∧ τ 2 = k := by
  revert i j k; decide

section Counts

variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h

omit hirr in
theorem anglesAt_eq_vcount_α (k : Fin 3) : anglesAt D k α = vcount D k α := by
  obtain ⟨hα, -, hα3, -⟩ := angles_pos D hrel h
  have := Real.pi_pos
  exact (vcount_eq_anglesAt D k hα.ne' (by linarith) (by linarith)).symm

omit hirr in
theorem anglesAt_eq_vcount_β (k : Fin 3) : anglesAt D k β = vcount D k β := by
  obtain ⟨-, hβ, -, hβ2⟩ := angles_pos D hrel h
  have := Real.pi_pos
  exact (vcount_eq_anglesAt D k hβ.ne' (by linarith) (by linarith)).symm

/-- With no `γ` angle at vertex `k`, the tiles there are those with an `α` or a `β` angle there. -/
theorem tilesAt_eq (k : Fin 3) (hz : vcount D k (2 * α + β) = 0) :
    tilesAt D k = vcount D k α + vcount D k β := by
  classical
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  rw [anglesAt_eq_vcount_α D hrel h k |>.symm, anglesAt_eq_vcount_β D hrel h k |>.symm]
  unfold tilesAt anglesAt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, TileAt]
    constructor
    · rintro ⟨l, hl⟩
      rcases tile_angle_mem D h i l with e | e | e
      · exact Or.inl ⟨l, hl, e⟩
      · exact Or.inr ⟨l, hl, e⟩
      · exfalso
        have hγ0 : 2 * α + β ≠ 0 := by linarith
        have hγπ : 2 * α + β ≠ Real.pi := by linarith
        have hγ2π : 2 * α + β ≠ 2 * Real.pi := by linarith
        have hmem : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α + β} :
            Finset (Fin N)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (localAngle_iff _ _ hγ0 hγπ hγ2π).mpr ⟨l, hl, e⟩
        unfold vcount at hz
        rw [Finset.card_eq_zero] at hz
        rw [hz] at hmem
        exact Finset.notMem_empty _ hmem
    · rintro (⟨l, hl, -⟩ | ⟨l, hl, -⟩) <;> exact ⟨l, hl⟩
  · rw [Finset.disjoint_filter]
    rintro i - ⟨l, hl, e⟩ ⟨l', hl', e'⟩
    have : l = l' := (D.tile i).indep.injective (hl.trans hl'.symm)
    subst this
    exact hαβ (e.symm.trans e')

/-- `lemma:nogamma`, with `α ∉ ℚπ` and "not similar" in Bonfioli's form. -/
theorem nogamma_irr
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) :
    (∀ (k : Fin 3) (i : Fin N) (l : Fin 3),
        (D.tile i).pts l = D.target.pts k → (D.tile i).angleAt l ≠ 2 * α + β) ∧
      ∑ k, tilesAt D k = 5 := by
  classical
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, h5⟩
  · exact absurd hs hns
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  refine ⟨fun k i l hl e => ?_, ?_⟩
  · have hmem : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α + β} :
        Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (localAngle_iff _ _ (by linarith) (by linarith) (by linarith)).mpr ⟨l, hl, e⟩
    have hz' := hz k
    unfold vcount at hz'
    rw [Finset.card_eq_zero] at hz'
    rw [hz'] at hmem
    exact Finset.notMem_empty _ hmem
  · rw [← h5]
    exact Finset.sum_congr rfl fun k _ => tilesAt_eq D hirr hrel h k (hz k)

/-- `lemma:shapes`, with `α ∉ ℚπ` and "not similar" in Bonfioli's form. -/
theorem shapes_irr
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) :
    FiveShapes (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β ∧
      ∑ k, anglesAt D k α = 3 ∧ ∑ k, anglesAt D k β = 2 := by
  obtain ⟨h5, h3, h2, -, -⟩ := lemma11 D hirr hrel h hns
  refine ⟨h5, ?_, ?_⟩
  · exact (Finset.sum_congr rfl fun k _ => anglesAt_eq_vcount_α D hrel h k).trans h3
  · exact (Finset.sum_congr rfl fun k _ => anglesAt_eq_vcount_β D hrel h k).trans h2

end Counts

/-! ### The coloring -/

/-- The negative of a proper coloring is proper. -/
theorem proper_neg {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) :
    D.toDissection.ProperColouring (fun i => - ε i) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rcases hε.1 i with e | e <;> simp [e]
  · have := hε.2 i j hij; simp only; omega

/-- A tile at `B` with an edge on `AB` has an edge contained in the side `AB`. -/
theorem edge_of_AtBOnAB {i : Fin N} (hi : AtBOnAB D i) :
    ∃ e : Fin 3, (D.tile i).edge e ⊆ D.target.edge 0 := by
  obtain ⟨l, l', hll', hl, hl'⟩ := hi
  have hAB : D.target.edge 0 = segment ℝ (D.target.pts 0) (D.target.pts 1) := rfl
  have hB : D.target.pts 1 ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) :=
    right_mem_segment ℝ _ _
  have hcases : ∀ l l' : Fin 3, l ≠ l' → l' = l + 1 ∨ l = l' + 1 := by decide
  rcases hcases l l' hll' with e | e
  · refine ⟨l, ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hB hl'
  · refine ⟨l', ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hl' hB

section Colouring

variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel

omit D in
/-- `α` and `β` are linearly independent over `ℕ`. -/
theorem indep {p q p' q' : ℕ} (e : (p : ℝ) * α + q * β = p' * α + q' * β) : p = p' ∧ q = q' := by
  have key : (((p : ℝ) - p') - 3 * ((q : ℝ) - q') / 2) * α = -(((q : ℝ) - q') / 2) * Real.pi := by
    linear_combination e - ((q : ℝ) - q') / 2 * hrel
  by_cases hc : ((p : ℝ) - p') - 3 * ((q : ℝ) - q') / 2 = 0
  · have hq : ((q : ℝ) - q') * Real.pi = 0 := by
      rw [hc, zero_mul] at key; linarith
    have hq' : (q : ℝ) = q' := by
      rcases mul_eq_zero.mp hq with e | e
      · linarith
      · exact absurd e Real.pi_ne_zero
    have hp' : (p : ℝ) = p' := by rw [hq'] at hc; linarith
    exact ⟨by exact_mod_cast hp', by exact_mod_cast hq'⟩
  · exfalso
    apply hirr
    refine ⟨-(((q : ℚ) - q') / 2) / (((p : ℚ) - p') - 3 * ((q : ℚ) - q') / 2), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hc]
    linear_combination key

omit D in
/-- The character `χ₋` on the exterior angle `π - (pα + qβ)`: `1` if `p + q` is odd, else `-1`. -/
theorem chi_ext (p q : ℕ) :
    (chiAt α hirr 1 0).chi (((Real.pi - ((p : ℝ) * α + q * β)) : ℝ) : Real.Angle)
      = if Even (p + q) then -1 else 1 := by
  have hrep : Real.pi - ((p : ℝ) * α + q * β)
      = ((1 - 2 * q + p : ℤ) : ℝ) * Real.pi + ((3 * q - 2 * p : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    push_cast
    linear_combination (-(q : ℝ) / 2) * hrel
  rw [hrep, chiAt_chi]
  have key : ((1 - 2 * q + p : ℤ) : ZMod 2) + 1 * ((3 * q - 2 * p : ℤ) : ZMod 2)
      = (((1 - 2 * q + p) + (3 * q - 2 * p) : ℤ) : ZMod 2) := by push_cast; ring
  rw [key]
  split_ifs with h1 h2 h2
  · exfalso
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h1
    obtain ⟨r, hr⟩ := h2
    omega
  · rfl
  · rfl
  · exfalso
    apply h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Nat.not_even_iff_odd] at h2
    obtain ⟨r, hr⟩ := h2
    exact ⟨(q : ℤ) - r, by omega⟩

omit D in
theorem mem_L (p q : ℕ) :
    ((((p : ℝ) * α + q * β) : ℝ) : Real.Angle) ∈ (chiAt α hirr 1 0).L := by
  have hrep : (p : ℝ) * α + q * β
      = ((2 * q - p : ℤ) : ℝ) * Real.pi + ((2 * p - 3 * q : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    push_cast
    linear_combination (q : ℝ) / 2 * hrel
  rw [hrep]
  exact chiAt_mem _ _ _ _ _ _

include h

/-- The angle of `ABC` at vertex `k` is `pα + qβ`, `p` and `q` its numbers of `α`, `β` tiles. -/
theorem corner_eq (hz : ∀ k, vcount D k (2 * α + β) = 0) (k : Fin 3) :
    D.target.angleAt k = (vcount D k α : ℝ) * α + (vcount D k β : ℝ) * β := by
  have := (corner_fig D hirr hrel h k).2
  rw [hz k] at this
  push_cast at this
  linarith

/-- **The sign of a tile at `B` with an edge on `AB`**: in the flux coloring it is the weight of
the direction of `AB`. -/
theorem sign_at_B {ε : Fin N → ℤ}
    (hflux : ∀ i, (D.tile i).flux (chiAt α hirr 1 0).weight
      = (ε i : ℝ) * (chiAt α hirr 1 0).tileValue D.model)
    {i : Fin N} (hi : AtBOnAB D i) :
    (ε i : ℝ) = (chiAt α hirr 1 0).weight (D.target.leftUnit 0) := by
  obtain ⟨e, he⟩ := edge_of_AtBOnAB D hi
  have hT := tile_threeAlpha D h i
  have hdir : (D.tile i).leftUnit e = D.target.leftUnit 0 :=
    D.toDissection.eDir_of_side (e := (i, e)) he
  have hf := Tri.flux_eq_edgeSign (chiAt α hirr 1 0) (chiAt_sq _ _ _ _) (D.tile i)
    ((D.tile i).threeAlpha_angles_mem hirr hrel hT 1) e
  have hext := model_hext (D.tile i) hirr hT hrel (e + 2)
  have hK : (chiAt α hirr 1 0).tileValue D.model = a + b + c :=
    threeAlpha_tileValue_minus D.model hirr hrel h
  have hKi : (chiAt α hirr 1 0).tileValue (D.tile i) = a + b + c :=
    threeAlpha_tileValue_minus (D.tile i) hirr hrel hT
  unfold GridChar.edgeSign at hf
  rw [hext, hdir, one_mul, hKi, hflux i, hK] at hf
  obtain ⟨ha, hb, hc, -, -⟩ := model_abc_pos h
  have hpos : 0 < a + b + c := by linarith
  exact mul_right_cancel₀ hpos.ne' hf

/-- **The target's flux**: `χ(π - C) · w · Σ_k χ(π - θ_k) · |side k|`, with `w` the weight of the
direction of `AB`. -/
theorem target_flux (hz : ∀ k, vcount D k (2 * α + β) = 0) :
    D.target.flux (chiAt α hirr 1 0).weight
      = (chiAt α hirr 1 0).chi ((Real.pi - D.target.angleAt 2 : ℝ) : Real.Angle)
        * (chiAt α hirr 1 0).weight (D.target.leftUnit 0)
        * ∑ k : Fin 3, (chiAt α hirr 1 0).chi ((Real.pi - D.target.angleAt k : ℝ) : Real.Angle)
            * D.target.oppLen k := by
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hirr 1 0).L := by
    intro k
    rw [corner_eq D hirr hrel h hz k]
    exact mem_L hirr hrel _ _
  rw [Tri.flux_eq_edgeSign (chiAt α hirr 1 0) (chiAt_sq _ _ _ _) D.target htarget 0]
  rfl

/-- `lemma:signedtiles`, with `α ∉ ℚπ`: the flux coloring, with its sign chosen so that a given
tile is black. -/
theorem signedtiles_irr (i₀ : Fin N) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ε i₀ = 1 := by
  obtain ⟨ε, hε, -, -⟩ := D.flux_colouring (chiAt α hirr 1 0) (chiAt_sq _ _ _ _)
    (D.model.threeAlpha_angles_mem hirr hrel h 1) (model_hext D.model hirr h hrel)
  rcases hε.1 i₀ with e | e
  · exact ⟨ε, hε, e⟩
  · exact ⟨fun i => - ε i, proper_neg D hε, by simp [e]⟩

/-- The flux coloring `ε₀` and the identity `(Σ ε₀)(a + b + c) = χ(π - C) · w · Σ_k χ(π - θ_k)|side k|`. -/
theorem flux_identity
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) :
    ∃ ε₀ : Fin N → ℤ, D.toDissection.ProperColouring ε₀ ∧
      (∀ i, AtBOnAB D i → (ε₀ i : ℝ) = (chiAt α hirr 1 0).weight (D.target.leftUnit 0)) ∧
      ((∑ i, ε₀ i : ℤ) : ℝ) * (a + b + c)
        = (if Even (tilesAt D 2) then -1 else 1)
          * (chiAt α hirr 1 0).weight (D.target.leftUnit 0)
          * ∑ k : Fin 3, (if Even (tilesAt D k) then -1 else 1) * D.target.oppLen k := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact absurd hs hns
  obtain ⟨ε₀, hε₀, hflux, hS⟩ := D.flux_colouring (chiAt α hirr 1 0) (chiAt_sq _ _ _ _)
    (D.model.threeAlpha_angles_mem hirr hrel h 1) (model_hext D.model hirr h hrel)
  have hK : (chiAt α hirr 1 0).tileValue D.model = a + b + c :=
    threeAlpha_tileValue_minus D.model hirr hrel h
  have hchi : ∀ k, (chiAt α hirr 1 0).chi ((Real.pi - D.target.angleAt k : ℝ) : Real.Angle)
      = if Even (tilesAt D k) then -1 else 1 := by
    intro k
    rw [corner_eq D hirr hrel h hz k, chi_ext hirr hrel, tilesAt_eq D hirr hrel h k (hz k)]
  refine ⟨ε₀, hε₀, fun i hi => sign_at_B D hirr hrel h hflux hi, ?_⟩
  rw [← hK, ← hS, target_flux D hirr hrel h hz, hchi]
  simp only [hchi]

/-- `theorem:coloring`, with `α ∉ ℚπ` and "not similar" in Bonfioli's form. -/
theorem coloring_irr
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) :
    (∃ σ : Equiv.Perm (Fin 3), tilesAt D (σ 0) = tilesAt D (σ 2)) ∧
      (tilesAt D 0 = tilesAt D 2 → ∀ (ε : Fin N → ℤ) (i₀ : Fin N),
        D.toDissection.ProperColouring ε → AtBOnAB D i₀ → ε i₀ = 1 →
        ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β) →
          ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
            = D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2) ∧
        (¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) →
          ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
            = D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2)) := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, hP, hQ, -⟩
  · exact absurd hs hns
  obtain ⟨-, -, -, -, hpos⟩ := lemma11 D hirr hrel h hns
  have hn : ∀ k, tilesAt D k = vcount D k α + vcount D k β :=
    fun k => tilesAt_eq D hirr hrel h k (hz k)
  rw [Fin.sum_univ_three] at hP hQ
  have p0 := hpos 0
  have p1 := hpos 1
  have p2 := hpos 2
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  refine ⟨?_, ?_⟩
  · have : tilesAt D 0 = tilesAt D 2 ∨ tilesAt D 0 = tilesAt D 1 ∨ tilesAt D 1 = tilesAt D 2 := by
      omega
    rcases this with e | e | e
    · exact ⟨1, e⟩
    · obtain ⟨τ, t0, -, t2⟩ := perm3 0 2 1 (by decide) (by decide) (by decide)
      exact ⟨τ, by rw [t0, t2, e]⟩
    · obtain ⟨τ, t0, -, t2⟩ := perm3 1 0 2 (by decide) (by decide) (by decide)
      exact ⟨τ, by rw [t0, t2, e]⟩
  intro h02 ε i₀ hε hi₀ hεi₀
  obtain ⟨ε₀, hε₀, hB, hid⟩ := flux_identity D hirr hrel h hns
  set w := (chiAt α hirr 1 0).weight (D.target.leftUnit 0) with hwdef
  have hw := hB i₀ hi₀
  -- `ε = w ε₀`, since proper colorings agree up to sign and `ε` is `1` at the tile `i₀`.
  have hM : ((∑ i, ε i : ℤ) : ℝ) = w * ((∑ i, ε₀ i : ℤ) : ℝ) := by
    rcases Dissection.colouring_unique' D.toDissection hε₀ hε with e | e
    · subst e
      rw [← hw, hεi₀]
      simp
    · subst e
      have : (ε₀ i₀ : ℝ) = -1 := by
        have : ε₀ i₀ = -1 := by simp only at hεi₀; omega
        exact_mod_cast this
      rw [← hw, this, Finset.sum_neg_distrib]
      push_cast
      ring
  have hw2 : w * w = 1 := (chiAt α hirr 1 0).val_sq (chiAt_sq _ _ _ _) _
  have key : ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
      = (if Even (tilesAt D 2) then -1 else 1)
          * ∑ k : Fin 3, (if Even (tilesAt D k) then -1 else 1) * D.target.oppLen k := by
    rw [hM, mul_assoc, hid]
    linear_combination ((if Even (tilesAt D 2) then (-1 : ℝ) else 1)
      * ∑ k : Fin 3, (if Even (tilesAt D k) then (-1 : ℝ) else 1) * D.target.oppLen k) * hw2
  rw [Fin.sum_univ_three] at key
  -- The plus sign occurs exactly when there is one tile at `A`.
  have hiff : ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
      (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) ↔ tilesAt D 0 = 1 := by
    have c0 := corner_eq D hirr hrel h hz 0
    have c1 := corner_eq D hirr hrel h hz 1
    have c2 := corner_eq D hirr hrel h hz 2
    constructor
    · rintro (⟨e0, -⟩ | ⟨e0, -⟩)
      · have := indep hirr hrel (p := vcount D 0 α) (q := vcount D 0 β) (p' := 1) (q' := 0)
          (by rw [← c0, e0]; push_cast; ring)
        omega
      · have := indep hirr hrel (p := vcount D 0 α) (q := vcount D 0 β) (p' := 0) (q' := 1)
          (by rw [← c0, e0]; push_cast; ring)
        omega
    · intro h1
      have hcase : (vcount D 0 α = 1 ∧ vcount D 0 β = 0 ∨ vcount D 0 α = 0 ∧ vcount D 0 β = 1) ∧
          (vcount D 2 α = 1 ∧ vcount D 2 β = 0 ∨ vcount D 2 α = 0 ∧ vcount D 2 β = 1) := by
        omega
      rcases hcase with ⟨⟨a0, b0⟩ | ⟨a0, b0⟩, ⟨a2, b2⟩ | ⟨a2, b2⟩⟩
      · left
        rw [c0, c2, a0, b0, a2, b2]; push_cast; constructor <;> ring
      · exfalso; apply hns
        have a1 : vcount D 1 α = 2 := by omega
        have b1 : vcount D 1 β = 1 := by omega
        right; left
        rw [c0, c1, c2, a0, b0, a1, b1, a2, b2]; push_cast
        exact ⟨by ring, by ring, by ring⟩
      · exfalso; apply hns
        have a1 : vcount D 1 α = 2 := by omega
        have b1 : vcount D 1 β = 1 := by omega
        right; right; right; left
        rw [c0, c1, c2, a0, b0, a1, b1, a2, b2]; push_cast
        exact ⟨by ring, by ring, by ring⟩
      · right
        rw [c0, c2, a0, b0, a2, b2]; push_cast; constructor <;> ring
  have e1 : ¬ Even 1 := by decide
  have e2 : Even 2 := by decide
  have e3 : ¬ Even 3 := by decide
  refine ⟨fun hp => ?_, fun hnp => ?_⟩
  · have h0 : tilesAt D 0 = 1 := hiff.mp hp
    have h2 : tilesAt D 2 = 1 := by omega
    have h1 : tilesAt D 1 = 3 := by omega
    rw [h0, h1, h2, if_neg e1, if_neg e3] at key
    linarith
  · have h0 : tilesAt D 0 = 2 := by
      have := mt hiff.mpr hnp
      omega
    have h2 : tilesAt D 2 = 2 := by omega
    have h1 : tilesAt D 1 = 1 := by omega
    rw [h0, h1, h2, if_pos e2, if_neg e1] at key
    linarith

/-- `lemma:Mnotzero`, with `α ∉ ℚπ` and "not similar" in Bonfioli's form. -/
theorem Mnotzero_irr
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β))
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) : ∑ i, ε i ≠ 0 := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, hP, hQ, -⟩
  · exact absurd hs hns
  obtain ⟨-, -, -, -, hpos⟩ := lemma11 D hirr hrel h hns
  have hn : ∀ k, tilesAt D k = vcount D k α + vcount D k β :=
    fun k => tilesAt_eq D hirr hrel h k (hz k)
  rw [Fin.sum_univ_three] at hP hQ
  have p0 := hpos 0
  have p1 := hpos 1
  have p2 := hpos 2
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  obtain ⟨ε₀, hε₀, -, hid⟩ := flux_identity D hirr hrel h hns
  set w := (chiAt α hirr 1 0).weight (D.target.leftUnit 0) with hwdef
  have hw2 : w * w = 1 := (chiAt α hirr 1 0).val_sq (chiAt_sq _ _ _ _) _
  -- `Σ ε = ± Σ ε₀`, so it suffices that `Σ ε₀ ≠ 0`.
  suffices hne : ((∑ i, ε₀ i : ℤ) : ℝ) ≠ 0 by
    intro h0
    rcases Dissection.colouring_unique' D.toDissection hε₀ hε with e | e
    · subst e; exact hne (by exact_mod_cast h0)
    · subst e
      apply hne
      rw [Finset.sum_neg_distrib, neg_eq_zero] at h0
      exact_mod_cast h0
  intro h0
  rw [h0, zero_mul, Fin.sum_univ_three] at hid
  have t0 : D.target.oppLen 0 < D.target.oppLen 1 + D.target.oppLen 2 := D.target.oppLen_lt 0
  have t1 : D.target.oppLen 1 < D.target.oppLen 2 + D.target.oppLen 0 := D.target.oppLen_lt 1
  have t2 : D.target.oppLen 2 < D.target.oppLen 0 + D.target.oppLen 1 := D.target.oppLen_lt 2
  have q0 := D.target.oppLen_pos 0
  have q1 := D.target.oppLen_pos 1
  have q2 := D.target.oppLen_pos 2
  have hw0 : w ≠ 0 := fun e => by rw [e] at hw2; norm_num at hw2
  have e1 : ¬ Even 1 := by decide
  have e2 : Even 2 := by decide
  have e3 : ¬ Even 3 := by decide
  have hcases : (tilesAt D 0 = 1 ∧ tilesAt D 1 = 1 ∧ tilesAt D 2 = 3) ∨
      (tilesAt D 0 = 1 ∧ tilesAt D 1 = 3 ∧ tilesAt D 2 = 1) ∨
      (tilesAt D 0 = 3 ∧ tilesAt D 1 = 1 ∧ tilesAt D 2 = 1) ∨
      (tilesAt D 0 = 1 ∧ tilesAt D 1 = 2 ∧ tilesAt D 2 = 2) ∨
      (tilesAt D 0 = 2 ∧ tilesAt D 1 = 1 ∧ tilesAt D 2 = 2) ∨
      (tilesAt D 0 = 2 ∧ tilesAt D 1 = 2 ∧ tilesAt D 2 = 1) := by omega
  have hs : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → ∀ S : ℝ, 0 = x * y * S → S = 0 := by
    intro x y hx hy S hS
    rcases mul_eq_zero.mp hS.symm with e | e
    · exact absurd e (mul_ne_zero hx hy)
    · exact e
  rcases hcases with ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ |
      ⟨a0, a1, a2⟩ <;>
    simp only [a0, a1, a2, if_pos e2, if_neg e1, if_neg e3] at hid <;>
    have := hs _ _ (by norm_num) hw0 _ hid <;> linarith

end Colouring

end TriangleTiling.ThreeAlpha
