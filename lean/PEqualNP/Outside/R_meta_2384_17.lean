import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2384_17
    (hZeroCentrelessSmallU :
      let G11 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G11 C →
        PEqualNP.TopForm.TopForm G11 C →
        2 ≤ (PEqualNP.TopForm.junk G11 C).card →
        have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G11 C
        have B : ℕ := 2 * (PEqualNP.TopForm.centreless G11 C).card + (PEqualNP.TopForm.junk G11 C).card +
          (PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C).card
        U.card ≤ B →
        B < 2 * U.card →
        B ≤ U.card + 6 →
        PEqualNP.TopForm.centreless G11 C = ∅ ∧ 2 ≤ U.card ∧ U.card ≤ 3 →
        (∀ K1 K2 : Finset (Fin 11),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G11.deleteEdges ↑U) K1 →
          G11.IsVertexCover ↑(K1 ∪ K2) →
          B - U.card < K2.card) →
        False)
    (hZeroCentrelessLargeU :
      let G11 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G11 C →
        PEqualNP.TopForm.TopForm G11 C →
        2 ≤ (PEqualNP.TopForm.junk G11 C).card →
        have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G11 C
        have B : ℕ := 2 * (PEqualNP.TopForm.centreless G11 C).card + (PEqualNP.TopForm.junk G11 C).card +
          (PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C).card
        U.card ≤ B →
        B < 2 * U.card →
        B ≤ U.card + 6 →
        PEqualNP.TopForm.centreless G11 C = ∅ ∧ 4 ≤ U.card →
        (∀ K1 K2 : Finset (Fin 11),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G11.deleteEdges ↑U) K1 →
          G11.IsVertexCover ↑(K1 ∪ K2) →
          B - U.card < K2.card) →
        False)
    (hHasCentrelessZeroOr :
      let G11 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G11 C →
        PEqualNP.TopForm.TopForm G11 C →
        2 ≤ (PEqualNP.TopForm.junk G11 C).card →
        have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G11 C
        have B : ℕ := 2 * (PEqualNP.TopForm.centreless G11 C).card + (PEqualNP.TopForm.junk G11 C).card +
          (PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C).card
        U.card ≤ B →
        B < 2 * U.card →
        B ≤ U.card + 6 →
        (PEqualNP.TopForm.centreless G11 C).Nonempty ∧
          PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C = ∅ ∧
          3 ≤ U.card →
        (∀ K1 K2 : Finset (Fin 11),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G11.deleteEdges ↑U) K1 →
          G11.IsVertexCover ↑(K1 ∪ K2) →
          B - U.card < K2.card) →
        False)
    (hHasCentrelessHasOr :
      let G11 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G11 C →
        PEqualNP.TopForm.TopForm G11 C →
        2 ≤ (PEqualNP.TopForm.junk G11 C).card →
        have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G11 C
        have B : ℕ := 2 * (PEqualNP.TopForm.centreless G11 C).card + (PEqualNP.TopForm.junk G11 C).card +
          (PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C).card
        U.card ≤ B →
        B < 2 * U.card →
        B ≤ U.card + 6 →
        (PEqualNP.TopForm.centreless G11 C).Nonempty ∧
          (PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C).Nonempty ∧
          3 ≤ U.card →
        (∀ K1 K2 : Finset (Fin 11),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G11.deleteEdges ↑U) K1 →
          G11.IsVertexCover ↑(K1 ∪ K2) →
          B - U.card < K2.card) →
        False) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → ∃ (x11 : Finset (Fin (11 : ℕ))) (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x11 ∧ x1.IsVertexCover ↑(x11 ∪ x12) ∧ x12.card ≤ x8 - x7.card := by
  intro G11 C hsz hleast htf hjunk U B hUB hB2U
  by_contra hNoExt_raw
  have hNoExt : ∀ K1 K2 : Finset (Fin 11),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G11.deleteEdges ↑U) K1 →
      G11.IsVertexCover ↑(K1 ∪ K2) →
      B - U.card < K2.card := by
    intro K1 K2 hK1 hK12
    by_contra hle
    exact hNoExt_raw ⟨K1, K2, hK1, hK12, by omega⟩
  have hmin_cov_ex : ∀ k : ℕ, ∀ K : Finset (Fin 11), K.card = k →
      (G11.deleteEdges ↑U).IsVertexCover (K : Set (Fin 11)) →
      ∃ K1 : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G11.deleteEdges ↑U) K1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro K hKcard hKcov
      by_cases hmin : ∀ K' : Finset (Fin 11),
          (G11.deleteEdges ↑U).IsVertexCover (K' : Set (Fin 11)) → K.card ≤ K'.card
      · exact ⟨K, hKcov, hmin⟩
      · have hlt : ∃ K' : Finset (Fin 11),
            (G11.deleteEdges ↑U).IsVertexCover (K' : Set (Fin 11)) ∧ K'.card < K.card := by
          by_contra hno
          apply hmin
          intro K' hK'
          by_contra hge
          exact hno ⟨K', hK', by omega⟩
        obtain ⟨K', hK'cov, hK'lt⟩ := hlt
        exact ih K'.card (by omega) K' rfl hK'cov
  have huniv_cov : (G11.deleteEdges ↑U).IsVertexCover ((Finset.univ : Finset (Fin 11)) : Set (Fin 11)) := by
    intro v _ _
    exact Or.inl (Finset.mem_coe.mpr (Finset.mem_univ v))
  obtain ⟨K1, hK1⟩ := hmin_cov_ex (Finset.univ : Finset (Fin 11)).card Finset.univ rfl huniv_cov
  let K7 : Finset (Fin 11) := {4, 5, 6, 7, 8, 9, 10}
  have hK7_card : K7.card = 7 := by decide
  have hK7_cov : ∀ v w : Fin 11, G11.Adj v w → v ∈ K7 ∨ w ∈ K7 := by
    dsimp only [G11, K7]; decide
  have hK17_cov : G11.IsVertexCover ↑(K1 ∪ K7) := by
    intro v w hadj
    rcases hK7_cov v w hadj with hv | hw
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right K1 hv))
    · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right K1 hw))
  have hB6 : B ≤ U.card + 6 := by
    have hlt7 := hNoExt K1 K7 hK1 hK17_cov
    rw [hK7_card] at hlt7
    omega
  have hU_ge2 : 2 ≤ U.card := by
    have hB_ge : 2 ≤ B := by dsimp only [B]; omega
    omega
  by_cases hc : PEqualNP.TopForm.centreless G11 C = ∅
  · by_cases hU3 : U.card ≤ 3
    · exact hZeroCentrelessSmallU C hsz hleast htf hjunk hUB hB2U hB6 ⟨hc, hU_ge2, hU3⟩ hNoExt
    · have hU4 : 4 ≤ U.card := by omega
      exact hZeroCentrelessLargeU C hsz hleast htf hjunk hUB hB2U hB6 ⟨hc, hU4⟩ hNoExt
  · have hc_ne : (PEqualNP.TopForm.centreless G11 C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hc
    have hc_pos : 1 ≤ (PEqualNP.TopForm.centreless G11 C).card := Finset.card_pos.mpr hc_ne
    have hU_ge3 : 3 ≤ U.card := by
      have hB_ge4 : 4 ≤ B := by dsimp only [B]; omega
      omega
    by_cases hor : PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C = ∅
    · exact hHasCentrelessZeroOr C hsz hleast htf hjunk hUB hB2U hB6 ⟨hc_ne, hor, hU_ge3⟩ hNoExt
    · have hor_ne : (PEqualNP.TopForm.orN G11 C \ PEqualNP.TopForm.lam G11 C).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hor
      exact hHasCentrelessHasOr C hsz hleast htf hjunk hUB hB2U hB6 ⟨hc_ne, hor_ne, hU_ge3⟩ hNoExt
