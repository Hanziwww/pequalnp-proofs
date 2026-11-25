import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2379_17
    (hSmallSame :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ (D : AndCountCircuit 42),
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        9 ≤ D.size → D.size ≤ 18 →
        ∀ i0 : Fin D.size, i0 ∉ D.outGates →
          (∀ j : Fin D.size, j < i0 → ∀ U : Finset (Fin 42), D.gateVal U j = true →
            ∃ u ∈ U, ∃ v ∈ U, PG4.Adj u v) →
          (0 : Fin 42) ∈ D.leftVars i0 →
          (1 : Fin 42) ∈ D.rightVars i0 →
          False)
    (hSmallCross :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ (D : AndCountCircuit 42),
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        9 ≤ D.size → D.size ≤ 18 →
        ∀ i0 : Fin D.size, i0 ∉ D.outGates →
          (∀ j : Fin D.size, j < i0 → ∀ U : Finset (Fin 42), D.gateVal U j = true →
            ∃ u ∈ U, ∃ v ∈ U, PG4.Adj u v) →
          (0 : Fin 42) ∈ D.leftVars i0 →
          (22 : Fin 42) ∈ D.rightVars i0 →
          False)
    (hLargeSame :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ (D : AndCountCircuit 42),
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        19 ≤ D.size → D.size ≤ 20 →
        ∀ i0 : Fin D.size, i0 ∉ D.outGates →
          (∀ j : Fin D.size, j < i0 → ∀ U : Finset (Fin 42), D.gateVal U j = true →
            ∃ u ∈ U, ∃ v ∈ U, PG4.Adj u v) →
          (0 : Fin 42) ∈ D.leftVars i0 →
          (1 : Fin 42) ∈ D.rightVars i0 →
          False)
    (hLargeCross :
      let PG4 : SimpleGraph (Fin 42) :=
        SimpleGraph.fromRel (fun a b : Fin 42 =>
          a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ (D : AndCountCircuit 42),
        D.WellFormed → D.Computes PG4 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        19 ≤ D.size → D.size ≤ 20 →
        ∀ i0 : Fin D.size, i0 ∉ D.outGates →
          (∀ j : Fin D.size, j < i0 → ∀ U : Finset (Fin 42), D.gateVal U j = true →
            ∃ u ∈ U, ∃ v ∈ U, PG4.Adj u v) →
          (0 : Fin 42) ∈ D.leftVars i0 →
          (22 : Fin 42) ∈ D.rightVars i0 →
          False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  let S : List ℕ := [0, 5, 7, 17, 20]
  let pg4Rel : Fin 42 → Fin 42 → Prop := fun a b =>
    a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ S
  let PG4 : SimpleGraph (Fin 42) := SimpleGraph.fromRel pg4Rel
  let pg4B : Fin 42 → Fin 42 → Bool := fun a b =>
    (decide (a.val < 21) && decide (21 ≤ b.val) && decide ((b.val + 21 - a.val) % 21 ∈ S)) ||
    (decide (b.val < 21) && decide (21 ≤ a.val) && decide ((a.val + 21 - b.val) % 21 ∈ S))
  have hPG4_iff : ∀ a b : Fin 42, PG4.Adj a b ↔ pg4B a b = true := by
    intro a b
    change (a ≠ b ∧ (pg4Rel a b ∨ pg4Rel b a)) ↔ pg4B a b = true
    dsimp only [pg4Rel, pg4B]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
      · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by intro hab; subst hab; omega, Or.inl ⟨h1, h2, h3⟩⟩
      · exact ⟨by intro hab; subst hab; omega, Or.inr ⟨h1, h2, h3⟩⟩
  let m9L : List (ℕ × ℕ) :=
    [(15, 35), (12, 38), (5, 31), (6, 23), (13, 30), (20, 37), (1, 21), (19, 24), (8, 28)]
  let m9 : Fin 9 → Fin 42 × Fin 42 := fun k =>
    (⟨(m9L.getD k.val (0, 0)).1 % 42, Nat.mod_lt _ (by omega)⟩,
     ⟨(m9L.getD k.val (0, 0)).2 % 42, Nat.mod_lt _ (by omega)⟩)
  have hM9_adj : ∀ k : Fin 9, pg4B (m9 k).1 (m9 k).2 = true := by
    dsimp only [pg4B, S, m9, m9L]
    decide
  have hM9_ne : ∀ k : Fin 9, (m9 k).1 ≠ (m9 k).2 := by
    dsimp only [m9, m9L]
    decide
  have hM9_disj : ∀ k1 k2 : Fin 9, k1 ≠ k2 →
      (m9 k1).1 ≠ (m9 k2).1 ∧ (m9 k1).1 ≠ (m9 k2).2 ∧
      (m9 k1).2 ≠ (m9 k2).1 ∧ (m9 k1).2 ≠ (m9 k2).2 ∧
      pg4B (m9 k1).1 (m9 k2).1 = false ∧ pg4B (m9 k1).1 (m9 k2).2 = false ∧
      pg4B (m9 k1).2 (m9 k2).1 = false ∧ pg4B (m9 k1).2 (m9 k2).2 = false := by
    dsimp only [pg4B, S, m9, m9L]
    decide
  have hAff1S : ∀ d : Fin 21, decide (d.val ∈ S) = decide ((2 * d.val + 7) % 21 ∈ S) := by
    dsimp only [S]
    decide
  let aff1F : Fin 42 → Fin 42 := fun x =>
    if x.val < 21 then ⟨(2 * x.val) % 21, by omega⟩
    else ⟨21 + (2 * (x.val - 21) + 7) % 21, by omega⟩
  let aff1InvF : Fin 42 → Fin 42 := fun x =>
    if x.val < 21 then ⟨(11 * x.val) % 21, by omega⟩
    else ⟨21 + (11 * (x.val - 21) + 7) % 21, by omega⟩
  have hOrbitSame : ∀ b : Fin 21, b.val ≠ 0 →
      ∃ k : Fin 6, (Nat.iterate aff1F k.val ⟨b.val, by omega⟩).val ∈ ([1, 3, 7] : List ℕ) ∨
        (Nat.iterate aff1F k.val ⟨(21 - b.val) % 21, by omega⟩).val ∈ ([1, 3, 7] : List ℕ) := by
    dsimp only [aff1F]
    decide
  have hOrbitCross : ∀ b : Fin 21, pg4B 0 ⟨21 + b.val, by omega⟩ = false →
      ∃ k : Fin 6, (Nat.iterate aff1F k.val ⟨21 + b.val, by omega⟩).val ∈ ([22, 23, 24, 35] : List ℕ) := by
    dsimp only [aff1F, pg4B, S]
    decide
  let pAL : List ℕ :=
    [0, 8, 15, 1, 7, 19, 5, 20, 3, 9, 18, 13, 12, 14, 11, 16, 2, 10, 17, 6, 4,
     28, 36, 22, 27, 24, 26, 25, 41, 29, 35, 39, 33, 40, 31, 37, 23, 30, 38, 34, 32, 21]
  let pAInvL : List ℕ :=
    [0, 3, 16, 8, 20, 6, 19, 4, 1, 9, 17, 14, 12, 11, 13, 2, 15, 18, 10, 5, 7,
     41, 23, 36, 25, 27, 26, 24, 21, 29, 37, 34, 40, 32, 39, 30, 22, 35, 38, 31, 33, 28]
  let pBL : List ℕ :=
    [0, 11, 14, 15, 2, 10, 18, 1, 4, 12, 19, 16, 6, 20, 8, 3, 7, 5, 9, 17, 13,
     28, 31, 35, 22, 30, 38, 39, 21, 32, 40, 36, 23, 27, 25, 29, 24, 33, 26, 37, 34, 41]
  let pBInvL : List ℕ :=
    [0, 7, 4, 15, 8, 17, 12, 16, 14, 18, 5, 1, 9, 20, 2, 3, 11, 19, 6, 10, 13,
     28, 24, 32, 36, 34, 38, 33, 21, 35, 25, 22, 29, 37, 40, 23, 31, 39, 26, 27, 30, 41]
  let pCL : List ℕ :=
    [0, 7, 14, 3, 8, 18, 10, 1, 4, 17, 6, 16, 19, 13, 2, 15, 11, 9, 5, 12, 20,
     28, 35, 31, 29, 25, 38, 27, 21, 24, 34, 23, 36, 39, 30, 22, 32, 37, 26, 33, 40, 41]
  let mkMap : List ℕ → Fin 42 → Fin 42 := fun L x => ⟨L.getD x.val 0 % 42, Nat.mod_lt _ (by omega)⟩
  have hPA_inv : ∀ x : Fin 42, mkMap pAInvL (mkMap pAL x) = x ∧ mkMap pAL (mkMap pAInvL x) = x := by
    dsimp only [mkMap, pAL, pAInvL]
    decide
  have hPA_side : ∀ x : Fin 42, decide ((mkMap pAL x).val < 21) = decide (x.val < 21) := by
    dsimp only [mkMap, pAL]
    decide
  have hPA_edge : ∀ a b : Fin 21,
      pg4B (mkMap pAL ⟨a.val, by omega⟩) (mkMap pAL ⟨21 + b.val, by omega⟩) =
      pg4B ⟨a.val, by omega⟩ ⟨21 + b.val, by omega⟩ := by
    dsimp only [mkMap, pAL, pg4B, S]
    decide
  have hPB_inv : ∀ x : Fin 42, mkMap pBInvL (mkMap pBL x) = x ∧ mkMap pBL (mkMap pBInvL x) = x := by
    dsimp only [mkMap, pBL, pBInvL]
    decide
  have hPB_side : ∀ x : Fin 42, decide ((mkMap pBL x).val < 21) = decide (x.val < 21) := by
    dsimp only [mkMap, pBL]
    decide
  have hPB_edge : ∀ a b : Fin 21,
      pg4B (mkMap pBL ⟨a.val, by omega⟩) (mkMap pBL ⟨21 + b.val, by omega⟩) =
      pg4B ⟨a.val, by omega⟩ ⟨21 + b.val, by omega⟩ := by
    dsimp only [mkMap, pBL, pg4B, S]
    decide
  have hPC_inv : ∀ x : Fin 42, mkMap pCL (mkMap pCL x) = x := by
    dsimp only [mkMap, pCL]
    decide
  have hPC_side : ∀ x : Fin 42, decide ((mkMap pCL x).val < 21) = decide (x.val < 21) := by
    dsimp only [mkMap, pCL]
    decide
  have hPC_edge : ∀ a b : Fin 21,
      pg4B (mkMap pCL ⟨a.val, by omega⟩) (mkMap pCL ⟨21 + b.val, by omega⟩) =
      pg4B ⟨a.val, by omega⟩ ⟨21 + b.val, by omega⟩ := by
    dsimp only [mkMap, pCL, pg4B, S]
    decide
  have hP_pts :
      mkMap pAL 0 = 0 ∧ mkMap pAL 3 = 1 ∧ mkMap pAL 23 = 22 ∧
      mkMap pBL 0 = 0 ∧ mkMap pBL 7 = 1 ∧ mkMap pBL 24 = 22 ∧
      mkMap pCL 0 = 0 ∧ mkMap pCL 35 = 22 := by
    dsimp only [mkMap, pAL, pBL, pCL]
    decide
  have hSideEdgePres : ∀ (f : Fin 42 → Fin 42),
      (∀ x : Fin 42, decide ((f x).val < 21) = decide (x.val < 21)) →
      (∀ a b : Fin 21, pg4B (f ⟨a.val, by omega⟩) (f ⟨21 + b.val, by omega⟩) =
        pg4B ⟨a.val, by omega⟩ ⟨21 + b.val, by omega⟩) →
      ∀ x y : Fin 42, PG4.Adj (f x) (f y) ↔ PG4.Adj x y := by
    intro f hside hedge x y
    rw [hPG4_iff, hPG4_iff]
    have hfx : (f x).val < 21 ↔ x.val < 21 := by
      have h := congrArg (fun b => b = true) (hside x)
      exact iff_of_eq (by simpa only [decide_eq_true_eq] using h)
    have hfy : (f y).val < 21 ↔ y.val < 21 := by
      have h := congrArg (fun b => b = true) (hside y)
      exact iff_of_eq (by simpa only [decide_eq_true_eq] using h)
    by_cases hx : x.val < 21
    · by_cases hy : y.val < 21
      · have hfx' : (f x).val < 21 := hfx.mpr hx
        have hfy' : (f y).val < 21 := hfy.mpr hy
        dsimp only [pg4B]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> (rintro (⟨⟨_, h2⟩, _⟩ | ⟨⟨_, h2⟩, _⟩) <;> omega)
      · have hy' : 21 ≤ y.val := by omega
        have hxEq : (⟨x.val, by omega⟩ : Fin 42) = x := Fin.ext rfl
        have hyEq : (⟨21 + (y.val - 21), by omega⟩ : Fin 42) = y := Fin.ext (by dsimp only []; omega)
        have h := hedge ⟨x.val, hx⟩ ⟨y.val - 21, by omega⟩
        simp only [hxEq, hyEq] at h
        rw [h]
    · by_cases hy : y.val < 21
      · have hx' : 21 ≤ x.val := by omega
        have hyEq : (⟨y.val, by omega⟩ : Fin 42) = y := Fin.ext rfl
        have hxEq : (⟨21 + (x.val - 21), by omega⟩ : Fin 42) = x := Fin.ext (by dsimp only []; omega)
        have h := hedge ⟨y.val, hy⟩ ⟨x.val - 21, by omega⟩
        simp only [hyEq, hxEq] at h
        have hsym : ∀ u v : Fin 42, pg4B u v = pg4B v u := by
          intro u v
          dsimp only [pg4B]
          exact Bool.or_comm _ _
        rw [hsym (f x) (f y), h, hsym y x]
      · have hfx' : 21 ≤ (f x).val := by omega
        have hfy' : 21 ≤ (f y).val := by omega
        dsimp only [pg4B]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> (rintro (⟨⟨h1, _⟩, _⟩ | ⟨⟨h1, _⟩, _⟩) <;> omega)
  have hDualPerm : ∃ e : Equiv.Perm (Fin 42),
      (∀ x : Fin 42, e x = if x.val < 21 then ⟨21 + (21 - x.val) % 21, by omega⟩
        else ⟨(21 - (x.val - 21)) % 21, by omega⟩) ∧
      (∀ x y : Fin 42, PG4.Adj (e x) (e y) ↔ PG4.Adj x y) := by
    let df : Fin 42 → Fin 42 := fun x =>
      if x.val < 21 then ⟨21 + (21 - x.val) % 21, by omega⟩
      else ⟨(21 - (x.val - 21)) % 21, by omega⟩
    have hdf_inv : ∀ x : Fin 42, df (df x) = x := by
      intro x
      dsimp only [df]
      split_ifs with h1 h2 h3
      · dsimp only [] at h2; omega
      · apply Fin.ext
        dsimp only []
        omega
      · apply Fin.ext
        dsimp only []
        omega
      · dsimp only [] at h3; omega
    refine ⟨⟨df, df, hdf_inv, hdf_inv⟩, fun x => rfl, ?_⟩
    intro x y
    change PG4.Adj (df x) (df y) ↔ PG4.Adj x y
    rw [hPG4_iff, hPG4_iff]
    dsimp only [df, pg4B]
    split_ifs with hx hy hy
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor <;> (rintro (⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩) <;> omega)
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨⟨h1, h2⟩, _⟩ | ⟨⟨_, _⟩, h3⟩)
        · omega
        · left
          refine ⟨⟨hx, by omega⟩, ?_⟩
          have heq : (21 + (21 - x.val) % 21 + 21 - (21 - (y.val - 21)) % 21) % 21 =
              (y.val + 21 - x.val) % 21 := by omega
          rwa [heq] at h3
      · rintro (⟨⟨_, _⟩, h3⟩ | ⟨⟨h1, _⟩, _⟩)
        · right
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          have heq : (21 + (21 - x.val) % 21 + 21 - (21 - (y.val - 21)) % 21) % 21 =
              (y.val + 21 - x.val) % 21 := by omega
          rwa [heq]
        · omega
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨⟨_, _⟩, h3⟩ | ⟨⟨h1, _⟩, _⟩)
        · right
          refine ⟨⟨hy, by omega⟩, ?_⟩
          have heq : (21 + (21 - y.val) % 21 + 21 - (21 - (x.val - 21)) % 21) % 21 =
              (x.val + 21 - y.val) % 21 := by omega
          rwa [heq] at h3
        · omega
      · rintro (⟨⟨h1, _⟩, _⟩ | ⟨⟨_, _⟩, h3⟩)
        · omega
        · left
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          have heq : (21 + (21 - y.val) % 21 + 21 - (21 - (x.val - 21)) % 21) % 21 =
              (x.val + 21 - y.val) % 21 := by omega
          rwa [heq]
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor <;> (rintro (⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩) <;> omega)
  have hShiftPerm : ∀ s : Fin 21, ∃ e : Equiv.Perm (Fin 42),
      (∀ x : Fin 42, e x = if x.val < 21 then ⟨(x.val + s.val) % 21, by omega⟩
        else ⟨21 + (x.val - 21 + s.val) % 21, by omega⟩) ∧
      (∀ x y : Fin 42, PG4.Adj (e x) (e y) ↔ PG4.Adj x y) := by
    intro s
    let sf : Fin 21 → Fin 42 → Fin 42 := fun t x =>
      if x.val < 21 then ⟨(x.val + t.val) % 21, by omega⟩
      else ⟨21 + (x.val - 21 + t.val) % 21, by omega⟩
    let sInv : Fin 21 := ⟨(21 - s.val) % 21, by omega⟩
    have hlinv : ∀ x : Fin 42, sf sInv (sf s x) = x := by
      intro x
      dsimp only [sf, sInv]
      split_ifs with h1 h2 h3
      · apply Fin.ext
        dsimp only []
        omega
      · dsimp only [] at h2; omega
      · dsimp only [] at h3; omega
      · apply Fin.ext
        dsimp only []
        omega
    have hrinv : ∀ x : Fin 42, sf s (sf sInv x) = x := by
      intro x
      dsimp only [sf, sInv]
      split_ifs with h1 h2 h3
      · apply Fin.ext
        dsimp only []
        omega
      · dsimp only [] at h2; omega
      · dsimp only [] at h3; omega
      · apply Fin.ext
        dsimp only []
        omega
    refine ⟨⟨sf s, sf sInv, hlinv, hrinv⟩, fun x => rfl, ?_⟩
    apply hSideEdgePres (sf s)
    · intro x
      dsimp only [sf]
      split_ifs with h1
      · simp only [h1, decide_true]
        exact decide_eq_true (by omega)
      · simp only [h1, decide_false]
        exact decide_eq_false (by omega)
    · intro a b
      dsimp only [sf, pg4B]
      have ha : a.val < 21 := a.isLt
      have hb : ¬ (21 + b.val < 21) := by omega
      simp only [ha, hb, ↓reduceIte]
      have heq : (21 + (21 + b.val - 21 + s.val) % 21 + 21 - (a.val + s.val) % 21) % 21 =
          (21 + b.val + 21 - a.val) % 21 := by omega
      have h1 : (a.val + s.val) % 21 < 21 := by omega
      have h2 : 21 ≤ 21 + (21 + b.val - 21 + s.val) % 21 := by omega
      have h3 : ¬ (21 + (21 + b.val - 21 + s.val) % 21 < 21) := by omega
      have h4 : 21 ≤ 21 + b.val := by omega
      simp only [h1, h2, h3, h4, decide_true, decide_false, Bool.true_and,
        Bool.false_and, Bool.or_false, heq]
  have hAff1Perm : ∃ e : Equiv.Perm (Fin 42),
      (∀ x : Fin 42, e x = aff1F x) ∧
      (∀ x y : Fin 42, PG4.Adj (e x) (e y) ↔ PG4.Adj x y) := by
    have hlinv : ∀ x : Fin 42, aff1InvF (aff1F x) = x := by
      intro x
      dsimp only [aff1F, aff1InvF]
      split_ifs with h1 h2 h3
      · apply Fin.ext
        dsimp only []
        omega
      · dsimp only [] at h2; omega
      · dsimp only [] at h3; omega
      · apply Fin.ext
        dsimp only []
        omega
    have hrinv : ∀ x : Fin 42, aff1F (aff1InvF x) = x := by
      intro x
      dsimp only [aff1F, aff1InvF]
      split_ifs with h1 h2 h3
      · apply Fin.ext
        dsimp only []
        omega
      · dsimp only [] at h2; omega
      · dsimp only [] at h3; omega
      · apply Fin.ext
        dsimp only []
        omega
    refine ⟨⟨aff1F, aff1InvF, hlinv, hrinv⟩, fun x => rfl, ?_⟩
    apply hSideEdgePres aff1F
    · intro x
      dsimp only [aff1F]
      split_ifs with h1
      · simp only [h1, decide_true]
        exact decide_eq_true (by omega)
      · simp only [h1, decide_false]
        exact decide_eq_false (by omega)
    · intro a b
      dsimp only [aff1F, pg4B]
      have ha : a.val < 21 := a.isLt
      have hb : ¬ (21 + b.val < 21) := by omega
      simp only [ha, hb, ↓reduceIte]
      have h1 : (2 * a.val) % 21 < 21 := by omega
      have h2 : 21 ≤ 21 + (2 * (21 + b.val - 21) + 7) % 21 := by omega
      have h3 : ¬ (21 + (2 * (21 + b.val - 21) + 7) % 21 < 21) := by omega
      have h4 : 21 ≤ 21 + b.val := by omega
      simp only [h1, h2, h3, h4, decide_true, decide_false, Bool.true_and,
        Bool.false_and, Bool.or_false]
      let d : Fin 21 := ⟨(21 + b.val + 21 - a.val) % 21, by omega⟩
      have heq : (21 + (2 * (21 + b.val - 21) + 7) % 21 + 21 - (2 * a.val) % 21) % 21 =
          (2 * d.val + 7) % 21 := by
        dsimp only [d]
        omega
      rw [heq]
      exact (hAff1S d).symm
  have hFuelStable : ∀ (C : AndCountCircuit 42) (U : Finset (Fin 42)) (d d' : ℕ) (i : Fin C.size),
      i.val < d → i.val < d' → C.gateValFuel U d i = C.gateValFuel U d' i := by
    intro C U d
    induction d with
    | zero =>
      intro d' i hi _
      omega
    | succ d ih =>
      intro d' i hi hi'
      cases d' with
      | zero => omega
      | succ d' =>
        change (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U d) &&
            AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U d)) =
          (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U d') &&
            AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U d'))
        have hSide : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
            AndCountCircuit.sideTrue U B F i (C.gateValFuel U d) =
              AndCountCircuit.sideTrue U B F i (C.gateValFuel U d') := by
          intro B F
          change decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateValFuel U d j = true) =
            decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateValFuel U d' j = true)
          apply Bool.eq_iff_iff.mpr
          rw [decide_eq_true_iff, decide_eq_true_iff]
          constructor
          · rintro (h | ⟨j, hjF, hji, hjv⟩)
            · exact Or.inl h
            · refine Or.inr ⟨j, hjF, hji, ?_⟩
              rw [← ih d' j (by omega) (by omega)]
              exact hjv
          · rintro (h | ⟨j, hjF, hji, hjv⟩)
            · exact Or.inl h
            · refine Or.inr ⟨j, hjF, hji, ?_⟩
              rw [ih d' j (by omega) (by omega)]
              exact hjv
        rw [hSide (C.leftVars i) (C.leftGates i), hSide (C.rightVars i) (C.rightGates i)]
  have hGateValIff : ∀ (C : AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin C.size),
      C.gateVal U i = true ↔
        ((∃ v ∈ C.leftVars i, v ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
        ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true) := by
    intro C U i
    have hstep : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
      hFuelStable C U C.size (i.val + 1) i i.isLt (by omega)
    rw [hstep]
    change (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U i.val) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U i.val)) = true ↔ _
    rw [Bool.and_eq_true]
    have hS : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
        AndCountCircuit.sideTrue U B F i (C.gateValFuel U i.val) = true ↔
          (∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateVal U j = true := by
      intro B F
      change decide _ = true ↔ _
      rw [decide_eq_true_iff]
      constructor
      · rintro (h | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl h
        · refine Or.inr ⟨j, hjF, hji, ?_⟩
          have hst : C.gateValFuel U i.val j = C.gateVal U j :=
            hFuelStable C U i.val C.size j hji j.isLt
          rwa [hst] at hjv
      · rintro (h | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl h
        · refine Or.inr ⟨j, hjF, hji, ?_⟩
          have hst : C.gateValFuel U i.val j = C.gateVal U j :=
            hFuelStable C U i.val C.size j hji j.isLt
          rwa [hst]
    rw [hS (C.leftVars i) (C.leftGates i), hS (C.rightVars i) (C.rightGates i)]
  have hEvalIff : ∀ (C : AndCountCircuit 42) (U : Finset (Fin 42)),
      C.eval U = true ↔ (∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true := by
    intro C U
    change decide _ = true ↔ _
    exact decide_eq_true_iff
  let evalRep : (A : AndCountCircuit 42) →
      Option (Finset (Fin 42) × Finset (Fin A.size)) → Finset (Fin 42) → Bool :=
    fun A r U =>
      Option.casesOn r true (fun p =>
        decide ((∃ v ∈ p.1, v ∈ U) ∨ ∃ j ∈ p.2, A.gateVal U j = true))
  let appendGate : (A : AndCountCircuit 42) →
      Finset (Fin 42) → Finset (Fin A.size) →
      Finset (Fin 42) → Finset (Fin A.size) → AndCountCircuit 42 :=
    fun A L1 G1 L2 G2 =>
      { size := A.size + 1
        leftVars := Fin.snoc A.leftVars L1
        leftGates := Fin.snoc (fun i => (A.leftGates i).map Fin.castSuccEmb) (G1.map Fin.castSuccEmb)
        rightVars := Fin.snoc A.rightVars L2
        rightGates := Fin.snoc (fun i => (A.rightGates i).map Fin.castSuccEmb) (G2.map Fin.castSuccEmb)
        outVars := ∅
        outGates := ∅ }
  have hAppendWF : ∀ (A : AndCountCircuit 42) (L1 : Finset (Fin 42)) (G1 : Finset (Fin A.size))
      (L2 : Finset (Fin 42)) (G2 : Finset (Fin A.size)),
      A.WellFormed → (appendGate A L1 G1 L2 G2).WellFormed := by
    intro A L1 G1 L2 G2 hWF i
    refine Fin.lastCases ?_ ?_ i
    · dsimp only [appendGate]
      rw [Fin.snoc_last, Fin.snoc_last]
      constructor
      · intro j hj
        rw [Finset.mem_map] at hj
        obtain ⟨j', _, rfl⟩ := hj
        exact Fin.castSucc_lt_last j'
      · intro j hj
        rw [Finset.mem_map] at hj
        obtain ⟨j', _, rfl⟩ := hj
        exact Fin.castSucc_lt_last j'
    · intro i'
      dsimp only [appendGate]
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      constructor
      · intro j hj
        rw [Finset.mem_map] at hj
        obtain ⟨j', hj', rfl⟩ := hj
        exact Fin.castSucc_lt_castSucc_iff.mpr ((hWF i').1 j' hj')
      · intro j hj
        rw [Finset.mem_map] at hj
        obtain ⟨j', hj', rfl⟩ := hj
        exact Fin.castSucc_lt_castSucc_iff.mpr ((hWF i').2 j' hj')
  have hAppendOld : ∀ (A : AndCountCircuit 42) (L1 : Finset (Fin 42)) (G1 : Finset (Fin A.size))
      (L2 : Finset (Fin 42)) (G2 : Finset (Fin A.size)) (U : Finset (Fin 42)) (i : Fin A.size),
      (appendGate A L1 G1 L2 G2).gateVal U i.castSucc = A.gateVal U i := by
    intro A L1 G1 L2 G2 U
    have hInd : ∀ (k : ℕ) (hk : k < A.size),
        (appendGate A L1 G1 L2 G2).gateVal U (Fin.castSucc ⟨k, hk⟩) = A.gateVal U ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro hk
        apply Bool.eq_iff_iff.mpr
        rw [hGateValIff, hGateValIff]
        dsimp only [appendGate]
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        have hS : ∀ (F : Finset (Fin A.size)),
            (∃ j ∈ F.map Fin.castSuccEmb, j < Fin.castSucc ⟨k, hk⟩ ∧
              (appendGate A L1 G1 L2 G2).gateVal U j = true) ↔
            (∃ j ∈ F, j < ⟨k, hk⟩ ∧ A.gateVal U j = true) := by
          intro F
          constructor
          · rintro ⟨j, hj, hji, hjv⟩
            rw [Finset.mem_map] at hj
            obtain ⟨j', hj', rfl⟩ := hj
            have hjlt : j' < ⟨k, hk⟩ := Fin.castSucc_lt_castSucc_iff.mp hji
            refine ⟨j', hj', hjlt, ?_⟩
            have heq := ih j'.val hjlt j'.isLt
            rwa [← heq]
          · rintro ⟨j', hj', hjlt, hjv⟩
            refine ⟨j'.castSucc, Finset.mem_map.mpr ⟨j', hj', rfl⟩,
              Fin.castSucc_lt_castSucc_iff.mpr hjlt, ?_⟩
            have heq := ih j'.val hjlt j'.isLt
            rwa [heq]
        rw [hS (A.leftGates ⟨k, hk⟩), hS (A.rightGates ⟨k, hk⟩)]
    intro i
    exact hInd i.val i.isLt
  have hAppendLast : ∀ (A : AndCountCircuit 42) (L1 : Finset (Fin 42)) (G1 : Finset (Fin A.size))
      (L2 : Finset (Fin 42)) (G2 : Finset (Fin A.size)) (U : Finset (Fin 42)),
      (appendGate A L1 G1 L2 G2).gateVal U (Fin.last A.size) =
        (evalRep A (some (L1, G1)) U && evalRep A (some (L2, G2)) U) := by
    intro A L1 G1 L2 G2 U
    apply Bool.eq_iff_iff.mpr
    rw [hGateValIff, Bool.and_eq_true]
    dsimp only [appendGate, evalRep]
    rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_last, Fin.snoc_last,
      decide_eq_true_iff, decide_eq_true_iff]
    have hS : ∀ (G : Finset (Fin A.size)),
        (∃ j ∈ G.map Fin.castSuccEmb, j < Fin.last A.size ∧
          (appendGate A L1 G1 L2 G2).gateVal U j = true) ↔
        (∃ j ∈ G, A.gateVal U j = true) := by
      intro G
      constructor
      · rintro ⟨j, hj, _, hjv⟩
        rw [Finset.mem_map] at hj
        obtain ⟨j', hj', rfl⟩ := hj
        change (appendGate A L1 G1 L2 G2).gateVal U j'.castSucc = true at hjv
        rw [hAppendOld] at hjv
        exact ⟨j', hj', hjv⟩
      · rintro ⟨j', hj', hjv⟩
        refine ⟨j'.castSucc, Finset.mem_map.mpr ⟨j', hj', rfl⟩, Fin.castSucc_lt_last j', ?_⟩
        rw [hAppendOld]
        exact hjv
    rw [hS G1, hS G2]
  let liftRep : {A : AndCountCircuit 42} → {L1 L2 : Finset (Fin 42)} →
      {G1 G2 : Finset (Fin A.size)} →
      Option (Finset (Fin 42) × Finset (Fin A.size)) →
      Option (Finset (Fin 42) × Finset (Fin (appendGate A L1 G1 L2 G2).size)) :=
    fun r => Option.casesOn r none (fun p => some (p.1, p.2.map Fin.castSuccEmb))
  have hLiftEval : ∀ (A : AndCountCircuit 42) (L1 : Finset (Fin 42)) (G1 : Finset (Fin A.size))
      (L2 : Finset (Fin 42)) (G2 : Finset (Fin A.size))
      (r : Option (Finset (Fin 42) × Finset (Fin A.size))) (U : Finset (Fin 42)),
      evalRep (appendGate A L1 G1 L2 G2) (@liftRep A L1 L2 G1 G2 r) U = evalRep A r U := by
    intro A L1 G1 L2 G2 r U
    cases r with
    | none => rfl
    | some p =>
      apply Bool.eq_iff_iff.mpr
      dsimp only [liftRep, evalRep]
      rw [decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro (h | ⟨j, hj, hjv⟩)
        · exact Or.inl h
        · rw [Finset.mem_map] at hj
          obtain ⟨j', hj', rfl⟩ := hj
          change (appendGate A L1 G1 L2 G2).gateVal U j'.castSucc = true at hjv
          rw [hAppendOld] at hjv
          exact Or.inr ⟨j', hj', hjv⟩
      · rintro (h | ⟨j', hj', hjv⟩)
        · exact Or.inl h
        · refine Or.inr ⟨j'.castSucc, Finset.mem_map.mpr ⟨j', hj', rfl⟩, ?_⟩
          rw [hAppendOld]
          exact hjv
  have hStrip : ∀ (C : AndCountCircuit 42), C.WellFormed →
      ∃ D : AndCountCircuit 42,
        D.size = C.size ∧ D.WellFormed ∧
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) ∧
        (∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false) ∧
        (∀ U : Finset (Fin 42), D.eval U = C.eval U) := by
    intro C hWF
    let unitSet : Fin C.size → Finset (Fin 42) := fun i =>
      Finset.univ.filter (fun v : Fin 42 => C.gateVal {v} i = true)
    let Lext : Fin C.size → Finset (Fin 42) := fun i =>
      C.leftVars i ∪ (C.leftGates i).biUnion unitSet
    let Rext : Fin C.size → Finset (Fin 42) := fun i =>
      C.rightVars i ∪ (C.rightGates i).biUnion unitSet
    let D : AndCountCircuit 42 :=
      { size := C.size
        leftVars := fun i => Lext i \ unitSet i
        leftGates := C.leftGates
        rightVars := fun i => Rext i \ unitSet i
        rightGates := C.rightGates
        outVars := C.outVars ∪ C.outGates.biUnion unitSet
        outGates := C.outGates }
    have hUnitChar : ∀ (i : Fin C.size) (v : Fin 42),
        v ∈ unitSet i ↔ v ∈ Lext i ∧ v ∈ Rext i := by
      intro i v
      dsimp only [unitSet, Lext, Rext]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_biUnion]
      rw [hGateValIff]
      have hS : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
          (∀ j ∈ F, j < i) →
          (((∃ w ∈ B, w ∈ ({v} : Finset (Fin 42))) ∨
            ∃ j ∈ F, j < i ∧ C.gateVal {v} j = true) ↔
           (v ∈ B ∨ ∃ j ∈ F, C.gateVal {v} j = true)) := by
        intro B F hF
        constructor
        · rintro (⟨w, hwB, hwv⟩ | ⟨j, hjF, _, hjv⟩)
          · rw [Finset.mem_singleton] at hwv
            subst hwv
            exact Or.inl hwB
          · exact Or.inr ⟨j, hjF, hjv⟩
        · rintro (hvB | ⟨j, hjF, hjv⟩)
          · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
          · exact Or.inr ⟨j, hjF, hF j hjF, hjv⟩
      rw [hS (C.leftVars i) (C.leftGates i) (hWF i).1,
          hS (C.rightVars i) (C.rightGates i) (hWF i).2]
    have hDisj : ∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i) := by
      intro i
      rw [Finset.disjoint_left]
      intro v hvL hvR
      dsimp only [D] at hvL hvR
      rw [Finset.mem_sdiff] at hvL hvR
      exact hvL.2 ((hUnitChar i v).mpr ⟨hvL.1, hvR.1⟩)
    have hUnitFree : ∀ (i : Fin D.size) (v : Fin 42), D.gateVal {v} i = false := by
      have hInd : ∀ (k : ℕ) (hk : k < D.size) (v : Fin 42), D.gateVal {v} ⟨k, hk⟩ = false := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ih =>
          intro hk v
          cases hval : D.gateVal {v} ⟨k, hk⟩
          · rfl
          · exfalso
            rw [hGateValIff] at hval
            have hL : v ∈ D.leftVars ⟨k, hk⟩ := by
              rcases hval.1 with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
              · rw [Finset.mem_singleton] at hwv
                subst hwv
                exact hw
              · have h0 := ih j.val hji j.isLt v
                rw [h0] at hjv
                exact False.elim (Bool.false_ne_true hjv)
            have hR : v ∈ D.rightVars ⟨k, hk⟩ := by
              rcases hval.2 with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
              · rw [Finset.mem_singleton] at hwv
                subst hwv
                exact hw
              · have h0 := ih j.val hji j.isLt v
                rw [h0] at hjv
                exact False.elim (Bool.false_ne_true hjv)
            exact Finset.disjoint_left.mp (hDisj ⟨k, hk⟩) hL hR
      intro i v
      exact hInd i.val i.isLt v
    have hGateEquiv : ∀ (U : Finset (Fin 42)) (i : Fin C.size),
        C.gateVal U i = true ↔ (∃ v ∈ unitSet i, v ∈ U) ∨ D.gateVal U i = true := by
      intro U
      have hInd : ∀ (k : ℕ) (hk : k < C.size),
          C.gateVal U ⟨k, hk⟩ = true ↔
            (∃ v ∈ unitSet ⟨k, hk⟩, v ∈ U) ∨ D.gateVal U ⟨k, hk⟩ = true := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ih =>
          intro hk
          let i : Fin C.size := ⟨k, hk⟩
          rw [hGateValIff C U i, hGateValIff D U i]
          have hSide : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
              (∀ j ∈ F, j < i) →
              (unitSet i ⊆ B ∪ F.biUnion unitSet) →
              (((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ C.gateVal U j = true) ↔
               ((∃ v ∈ unitSet i, v ∈ U) ∨
                ((∃ v ∈ (B ∪ F.biUnion unitSet) \ unitSet i, v ∈ U) ∨
                 ∃ j ∈ F, j < i ∧ D.gateVal U j = true))) := by
            intro B F hF hsub
            constructor
            · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
              · by_cases hvu : v ∈ unitSet i
                · exact Or.inl ⟨v, hvu, hvU⟩
                · exact Or.inr (Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hvB, hvu⟩, hvU⟩)
              · have hEq := (ih j.val hji j.isLt).mp hjv
                rcases hEq with ⟨v, hvuj, hvU⟩ | hDv
                · by_cases hvu : v ∈ unitSet i
                  · exact Or.inl ⟨v, hvu, hvU⟩
                  · refine Or.inr (Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ ?_, hvu⟩, hvU⟩)
                    exact Finset.mem_biUnion.mpr ⟨j, hjF, hvuj⟩
                · exact Or.inr (Or.inr ⟨j, hjF, hji, hDv⟩)
            · rintro (⟨v, hvu, hvU⟩ | ⟨v, hvs, hvU⟩ | ⟨j, hjF, hji, hDv⟩)
              · have hvE := hsub hvu
                rw [Finset.mem_union] at hvE
                rcases hvE with hvB | hvBi
                · exact Or.inl ⟨v, hvB, hvU⟩
                · rw [Finset.mem_biUnion] at hvBi
                  obtain ⟨j, hjF, hvuj⟩ := hvBi
                  have hji := hF j hjF
                  exact Or.inr ⟨j, hjF, hji, (ih j.val hji j.isLt).mpr (Or.inl ⟨v, hvuj, hvU⟩)⟩
              · have hvE := (Finset.mem_sdiff.mp hvs).1
                rw [Finset.mem_union] at hvE
                rcases hvE with hvB | hvBi
                · exact Or.inl ⟨v, hvB, hvU⟩
                · rw [Finset.mem_biUnion] at hvBi
                  obtain ⟨j, hjF, hvuj⟩ := hvBi
                  have hji := hF j hjF
                  exact Or.inr ⟨j, hjF, hji, (ih j.val hji j.isLt).mpr (Or.inl ⟨v, hvuj, hvU⟩)⟩
              · exact Or.inr ⟨j, hjF, hji, (ih j.val hji j.isLt).mpr (Or.inr hDv)⟩
          have hSubL : unitSet i ⊆ Lext i := fun v hv => (hUnitChar i v).mp hv |>.1
          have hSubR : unitSet i ⊆ Rext i := fun v hv => (hUnitChar i v).mp hv |>.2
          rw [hSide (C.leftVars i) (C.leftGates i) (hWF i).1 hSubL,
              hSide (C.rightVars i) (C.rightGates i) (hWF i).2 hSubR]
          dsimp only [D, Lext, Rext]
          constructor
          · rintro ⟨hP | hA, hP' | hB⟩
            · exact Or.inl hP
            · exact Or.inl hP
            · exact Or.inl hP'
            · exact Or.inr ⟨hA, hB⟩
          · rintro (hP | ⟨hA, hB⟩)
            · exact ⟨Or.inl hP, Or.inl hP⟩
            · exact ⟨Or.inr hA, Or.inr hB⟩
      intro i
      exact hInd i.val i.isLt
    refine ⟨D, rfl, hWF, hDisj, hUnitFree, ?_⟩
    intro U
    apply Bool.eq_iff_iff.mpr
    rw [hEvalIff D U, hEvalIff C U]
    dsimp only [D]
    constructor
    · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
      · rw [Finset.mem_union] at hvO
        rcases hvO with hv1 | hv2
        · exact Or.inl ⟨v, hv1, hvU⟩
        · rw [Finset.mem_biUnion] at hv2
          obtain ⟨j, hjO, hvuj⟩ := hv2
          exact Or.inr ⟨j, hjO, (hGateEquiv U j).mpr (Or.inl ⟨v, hvuj, hvU⟩)⟩
      · exact Or.inr ⟨j, hjO, (hGateEquiv U j).mpr (Or.inr hjv)⟩
    · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
      · exact Or.inl ⟨v, Finset.mem_union_left _ hvO, hvU⟩
      · rcases (hGateEquiv U j).mp hjv with ⟨v, hvuj, hvU⟩ | hDv
        · exact Or.inl ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjO, hvuj⟩), hvU⟩
        · exact Or.inr ⟨j, hjO, hDv⟩
  let InducedMatching : (m : ℕ) → (Fin m → Fin 42 × Fin 42) → Prop := fun m M =>
    (∀ k : Fin m, (M k).1 ≠ (M k).2) ∧
    (∀ k1 k2 : Fin m, k1 ≠ k2 →
      (M k1).1 ≠ (M k2).1 ∧ (M k1).1 ≠ (M k2).2 ∧
      (M k1).2 ≠ (M k2).1 ∧ (M k1).2 ≠ (M k2).2)
  let vertsM : (m : ℕ) → (Fin m → Fin 42 × Fin 42) → Finset (Fin 42) := fun m M =>
    Finset.univ.biUnion (fun k : Fin m => {(M k).1, (M k).2})
  have hMatchingLB : ∀ (m : ℕ) (M : Fin m → Fin 42 × Fin 42),
      InducedMatching m M →
      ∀ (C : AndCountCircuit 42), C.WellFormed →
        (∀ U : Finset (Fin 42), U ⊆ vertsM m M →
          (C.eval U = true ↔ ∃ k : Fin m, (M k).1 ∈ U ∧ (M k).2 ∈ U)) →
        m ≤ C.size := by
    intro m
    induction m with
    | zero =>
      intro _ _ _ _ _
      exact Nat.zero_le _
    | succ m ih =>
      intro M hIM C hWF hEvalM
      obtain ⟨D, hDsz, hDWF, hDDisj, _, hDEval⟩ := hStrip C hWF
      let V : Finset (Fin 42) := vertsM (m + 1) M
      let D' : AndCountCircuit 42 :=
        { size := D.size
          leftVars := fun i => D.leftVars i ∩ V
          leftGates := D.leftGates
          rightVars := fun i => D.rightVars i ∩ V
          rightGates := D.rightGates
          outVars := D.outVars ∩ V
          outGates := D.outGates }
      have hD'Disj : ∀ i : Fin D'.size, Disjoint (D'.leftVars i) (D'.rightVars i) := by
        intro i
        exact (hDDisj i).mono Finset.inter_subset_left Finset.inter_subset_left
      have hD'Gate : ∀ (U : Finset (Fin 42)), U ⊆ V →
          ∀ i : Fin D'.size, D'.gateVal U i = D.gateVal U i := by
        intro U hUV
        have hInd : ∀ (k : ℕ) (hk : k < D.size),
            D'.gateVal U ⟨k, hk⟩ = D.gateVal U ⟨k, hk⟩ := by
          intro k
          induction k using Nat.strongRecOn with
          | ind k ihk =>
            intro hk
            apply Bool.eq_iff_iff.mpr
            rw [hGateValIff D' U ⟨k, hk⟩, hGateValIff D U ⟨k, hk⟩]
            dsimp only [D']
            have hS : ∀ (B : Finset (Fin 42)) (F : Finset (Fin D.size)),
                ((∃ v ∈ B ∩ V, v ∈ U) ∨ ∃ j ∈ F, j < ⟨k, hk⟩ ∧ D'.gateVal U j = true) ↔
                ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < ⟨k, hk⟩ ∧ D.gateVal U j = true) := by
              intro B F
              constructor
              · rintro (⟨v, hv, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
                · exact Or.inl ⟨v, (Finset.mem_inter.mp hv).1, hvU⟩
                · rw [ihk j.val hji j.isLt] at hjv
                  exact Or.inr ⟨j, hjF, hji, hjv⟩
              · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
                · exact Or.inl ⟨v, Finset.mem_inter.mpr ⟨hvB, hUV hvU⟩, hvU⟩
                · rw [← ihk j.val hji j.isLt] at hjv
                  exact Or.inr ⟨j, hjF, hji, hjv⟩
            rw [hS (D.leftVars ⟨k, hk⟩) (D.leftGates ⟨k, hk⟩),
                hS (D.rightVars ⟨k, hk⟩) (D.rightGates ⟨k, hk⟩)]
        intro i
        exact hInd i.val i.isLt
      have hD'Eval : ∀ (U : Finset (Fin 42)), U ⊆ V →
          (D'.eval U = true ↔ ∃ k : Fin (m + 1), (M k).1 ∈ U ∧ (M k).2 ∈ U) := by
        intro U hUV
        have hEq : D'.eval U = D.eval U := by
          apply Bool.eq_iff_iff.mpr
          rw [hEvalIff D' U, hEvalIff D U]
          dsimp only [D']
          constructor
          · rintro (⟨v, hv, hvU⟩ | ⟨j, hjO, hjv⟩)
            · exact Or.inl ⟨v, (Finset.mem_inter.mp hv).1, hvU⟩
            · rw [hD'Gate U hUV j] at hjv
              exact Or.inr ⟨j, hjO, hjv⟩
          · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
            · exact Or.inl ⟨v, Finset.mem_inter.mpr ⟨hvO, hUV hvU⟩, hvU⟩
            · rw [← hD'Gate U hUV j] at hjv
              exact Or.inr ⟨j, hjO, hjv⟩
        rw [hEq, hDEval U]
        exact hEvalM U hUV
      have hD'OutEmpty : D'.outVars = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        have hvV : v ∈ V := (Finset.mem_inter.mp hv).2
        have hsub : ({v} : Finset (Fin 42)) ⊆ V := Finset.singleton_subset_iff.mpr hvV
        have htr : D'.eval {v} = true :=
          (hEvalIff D' {v}).mpr (Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩)
        obtain ⟨k, h1, h2⟩ := (hD'Eval {v} hsub).mp htr
        rw [Finset.mem_singleton] at h1 h2
        exact hIM.1 k (h1.trans h2.symm)
      have hPos : 0 < D'.size := by
        have hsub : ({(M 0).1, (M 0).2} : Finset (Fin 42)) ⊆ V := by
          intro x hx
          exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hx⟩
        have htr : D'.eval {(M 0).1, (M 0).2} = true :=
          (hD'Eval _ hsub).mpr ⟨0, Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        rw [hEvalIff, hD'OutEmpty] at htr
        rcases htr with ⟨_, hv, _⟩ | ⟨j, _, _⟩
        · exact False.elim (Finset.notMem_empty _ hv)
        · exact Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
      let g0 : Fin D'.size := ⟨0, hPos⟩
      have hg0LG : D'.leftGates g0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        have hlt := (hDWF g0).1 j hj
        exact Nat.not_lt_zero j.val hlt
      have hg0RG : D'.rightGates g0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        have hlt := (hDWF g0).2 j hj
        exact Nat.not_lt_zero j.val hlt
      rcases (D'.leftVars g0).eq_empty_or_nonempty with hEmpty | ⟨v, hvL0⟩
      · have hg0False : ∀ U : Finset (Fin 42), D'.gateVal U g0 = false := by
          intro U
          cases hgv : D'.gateVal U g0
          · rfl
          · exfalso
            rw [hGateValIff, hEmpty, hg0LG] at hgv
            rcases hgv.1 with ⟨_, hx, _⟩ | ⟨_, hx, _⟩ <;> exact Finset.notMem_empty _ hx
        let s : ℕ := D'.size - 1
        let idx : Fin s → Fin D'.size := fun i => ⟨i.val + 1, by omega⟩
        let shiftG : Finset (Fin D'.size) → Finset (Fin s) := fun F =>
          Finset.univ.filter (fun j : Fin s => idx j ∈ F)
        let E : AndCountCircuit 42 :=
          { size := s
            leftVars := fun i => D'.leftVars (idx i)
            leftGates := fun i => shiftG (D'.leftGates (idx i))
            rightVars := fun i => D'.rightVars (idx i)
            rightGates := fun i => shiftG (D'.rightGates (idx i))
            outVars := D'.outVars
            outGates := shiftG D'.outGates }
        have hEWF : E.WellFormed := by
          intro i
          dsimp only [E, shiftG]
          constructor
          · intro j hj
            have hj' : idx j ∈ D'.leftGates (idx i) := (Finset.mem_filter.mp hj).2
            have hlt : idx j < idx i := (hDWF (idx i)).1 (idx j) hj'
            change j.val < i.val
            change j.val + 1 < i.val + 1 at hlt
            omega
          · intro j hj
            have hj' : idx j ∈ D'.rightGates (idx i) := (Finset.mem_filter.mp hj).2
            have hlt : idx j < idx i := (hDWF (idx i)).2 (idx j) hj'
            change j.val < i.val
            change j.val + 1 < i.val + 1 at hlt
            omega
        have hEGate : ∀ (U : Finset (Fin 42)) (i : Fin s), E.gateVal U i = D'.gateVal U (idx i) := by
          intro U
          have hInd : ∀ (k : ℕ) (hk : k < s), E.gateVal U ⟨k, hk⟩ = D'.gateVal U (idx ⟨k, hk⟩) := by
            intro k
            induction k using Nat.strongRecOn with
            | ind k ihk =>
              intro hk
              apply Bool.eq_iff_iff.mpr
              rw [hGateValIff E U ⟨k, hk⟩, hGateValIff D' U (idx ⟨k, hk⟩)]
              dsimp only [E]
              have hS : ∀ (F : Finset (Fin D'.size)),
                  (∃ j ∈ shiftG F, j < ⟨k, hk⟩ ∧ E.gateVal U j = true) ↔
                  (∃ j ∈ F, j < idx ⟨k, hk⟩ ∧ D'.gateVal U j = true) := by
                intro F
                constructor
                · rintro ⟨j, hj, hji, hjv⟩
                  have hjF : idx j ∈ F := (Finset.mem_filter.mp hj).2
                  rw [ihk j.val hji j.isLt] at hjv
                  refine ⟨idx j, hjF, ?_, hjv⟩
                  change j.val + 1 < k + 1
                  have hjlt : j.val < k := hji
                  omega
                · rintro ⟨j, hjF, hji, hjv⟩
                  have hjpos : 0 < j.val := by
                    by_contra h0
                    have hj0 : j = g0 := Fin.ext (by dsimp only [g0]; omega)
                    rw [hj0, hg0False U] at hjv
                    exact Bool.false_ne_true hjv
                  let j' : Fin s := ⟨j.val - 1, by omega⟩
                  have hjEq : idx j' = j := Fin.ext (by dsimp only [idx, j']; omega)
                  have hjlt : j' < ⟨k, hk⟩ := by
                    change j.val - 1 < k
                    change j.val < k + 1 at hji
                    omega
                  refine ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hjEq]⟩, hjlt, ?_⟩
                  rw [ihk j'.val hjlt j'.isLt, hjEq]
                  exact hjv
              rw [hS (D'.leftGates (idx ⟨k, hk⟩)), hS (D'.rightGates (idx ⟨k, hk⟩))]
          intro i
          exact hInd i.val i.isLt
        let M' : Fin m → Fin 42 × Fin 42 := fun k => M k.succ
        have hIM' : InducedMatching m M' := by
          refine ⟨fun k => hIM.1 k.succ, fun k1 k2 hne =>
            hIM.2 k1.succ k2.succ (fun h => hne (Fin.succ_injective _ h))⟩
        have hEEval : ∀ U : Finset (Fin 42), U ⊆ vertsM m M' →
            (E.eval U = true ↔ ∃ k : Fin m, (M' k).1 ∈ U ∧ (M' k).2 ∈ U) := by
          intro U hUV'
          have hUV : U ⊆ V := by
            intro x hx
            obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp (hUV' hx)
            exact Finset.mem_biUnion.mpr ⟨k.succ, Finset.mem_univ _, hxk⟩
          have hEeq : E.eval U = D'.eval U := by
            apply Bool.eq_iff_iff.mpr
            rw [hEvalIff E U, hEvalIff D' U]
            dsimp only [E]
            constructor
            · rintro (h | ⟨j, hj, hjv⟩)
              · exact Or.inl h
              · rw [hEGate U j] at hjv
                exact Or.inr ⟨idx j, (Finset.mem_filter.mp hj).2, hjv⟩
            · rintro (h | ⟨j, hjO, hjv⟩)
              · exact Or.inl h
              · have hjpos : 0 < j.val := by
                  by_contra h0
                  have hj0 : j = g0 := Fin.ext (by dsimp only [g0]; omega)
                  rw [hj0, hg0False U] at hjv
                  exact Bool.false_ne_true hjv
                let j' : Fin s := ⟨j.val - 1, by omega⟩
                have hjEq : idx j' = j := Fin.ext (by dsimp only [idx, j']; omega)
                refine Or.inr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hjEq]⟩, ?_⟩
                rw [hEGate U j', hjEq]
                exact hjv
          rw [hEeq, hD'Eval U hUV]
          constructor
          · rintro ⟨k, h1, h2⟩
            revert h1 h2
            refine Fin.cases ?_ ?_ k
            · intro h1 _
              exfalso
              obtain ⟨k', _, hxk⟩ := Finset.mem_biUnion.mp (hUV' h1)
              have hne := hIM.2 0 k'.succ (Fin.succ_ne_zero k').symm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hxk
              rcases hxk with h | h
              · exact hne.1 h
              · exact hne.2.1 h
            · intro k' h1 h2
              exact ⟨k', h1, h2⟩
          · rintro ⟨k', h1, h2⟩
            exact ⟨k'.succ, h1, h2⟩
        have hLB := ih M' hIM' E hEWF hEEval
        dsimp only [E, s] at hLB
        have hCsz : D'.size = C.size := hDsz
        omega
      · have hvV : v ∈ V := (Finset.mem_inter.mp hvL0).2
        obtain ⟨k0, _, hvk0⟩ := Finset.mem_biUnion.mp hvV
        have hvNotR0 : v ∉ D'.rightVars g0 := Finset.disjoint_left.mp (hD'Disj g0) hvL0
        have hFold : ∀ (r : ℕ) (hr : r < D'.size),
            ∃ (A : AndCountCircuit 42)
              (rep : Fin (r + 1) → Option (Finset (Fin 42) × Finset (Fin A.size))),
              A.WellFormed ∧ A.size ≤ r ∧
              ∀ (U : Finset (Fin 42)), v ∉ U →
                ∀ (j : Fin (r + 1)),
                  evalRep A (rep j) U = D'.gateVal (insert v U) ⟨j.val, by omega⟩ := by
          intro r
          induction r with
          | zero =>
            intro hr
            let A0 : AndCountCircuit 42 :=
              { size := 0
                leftVars := Fin.elim0
                leftGates := Fin.elim0
                rightVars := Fin.elim0
                rightGates := Fin.elim0
                outVars := ∅
                outGates := ∅ }
            refine ⟨A0, fun _ => some (D'.rightVars g0, ∅), fun i => Fin.elim0 i, le_refl 0, ?_⟩
            intro U hvU j
            have hj0 : (⟨j.val, by omega⟩ : Fin D'.size) = g0 :=
              Fin.ext (by dsimp only [g0]; omega)
            rw [hj0]
            apply Bool.eq_iff_iff.mpr
            rw [hGateValIff D' (insert v U) g0]
            dsimp only [evalRep]
            rw [decide_eq_true_iff, hg0LG, hg0RG]
            constructor
            · rintro (⟨u, huR, huU⟩ | ⟨_, h, _⟩)
              · exact ⟨Or.inl ⟨v, hvL0, Finset.mem_insert_self v U⟩,
                  Or.inl ⟨u, huR, Finset.mem_insert_of_mem huU⟩⟩
              · exact False.elim (Finset.notMem_empty _ h)
            · rintro ⟨_, ⟨u, huR, huI⟩ | ⟨_, h, _⟩⟩
              · rw [Finset.mem_insert] at huI
                rcases huI with rfl | huU
                · exact False.elim (hvNotR0 huR)
                · exact Or.inl ⟨u, huR, huU⟩
              · exact False.elim (Finset.notMem_empty _ h)
          | succ r ihr =>
            intro hr
            obtain ⟨A, rep, hAWF, hAsz, hAEv⟩ := ihr (by omega)
            let gi : Fin D'.size := ⟨r + 1, hr⟩
            have hSideRep : ∀ (B : Finset (Fin 42)) (F : Finset (Fin D'.size)),
                (∀ j ∈ F, j < gi) →
                ∃ rS : Option (Finset (Fin 42) × Finset (Fin A.size)),
                  ∀ (U : Finset (Fin 42)), v ∉ U →
                    (evalRep A rS U = true ↔
                      (∃ u ∈ B, u ∈ insert v U) ∨
                      ∃ j ∈ F, j < gi ∧ D'.gateVal (insert v U) j = true) := by
              intro B F hF
              let F' : Finset (Fin (r + 1)) :=
                Finset.univ.filter (fun j : Fin (r + 1) => (⟨j.val, by omega⟩ : Fin D'.size) ∈ F)
              by_cases hTriv : v ∈ B ∨ ∃ j ∈ F', rep j = none
              · refine ⟨none, ?_⟩
                intro U hvU
                dsimp only [evalRep]
                simp only [true_iff]
                rcases hTriv with hvB | ⟨j, hjF', hjn⟩
                · exact Or.inl ⟨v, hvB, Finset.mem_insert_self v U⟩
                · have hjF : (⟨j.val, by omega⟩ : Fin D'.size) ∈ F := (Finset.mem_filter.mp hjF').2
                  have hgv : D'.gateVal (insert v U) ⟨j.val, by omega⟩ = true := by
                    rw [← hAEv U hvU j, hjn]
                  exact Or.inr ⟨⟨j.val, by omega⟩, hjF, hF _ hjF, hgv⟩
              · push Not at hTriv
                let BV : Finset (Fin 42) :=
                  B ∪ F'.biUnion (fun j => Option.casesOn (motive := fun _ => Finset (Fin 42)) (rep j) ∅ Prod.fst)
                let FG : Finset (Fin A.size) :=
                  F'.biUnion (fun j => Option.casesOn (motive := fun _ => Finset (Fin A.size)) (rep j) ∅ Prod.snd)
                refine ⟨some (BV, FG), ?_⟩
                intro U hvU
                dsimp only [evalRep]
                rw [decide_eq_true_iff]
                have hRepSome : ∀ j ∈ F',
                    evalRep A (rep j) U = true ↔
                      (∃ u ∈ Option.casesOn (motive := fun _ => Finset (Fin 42)) (rep j) ∅ Prod.fst, u ∈ U) ∨
                      ∃ g ∈ Option.casesOn (motive := fun _ => Finset (Fin A.size)) (rep j) ∅ Prod.snd,
                        A.gateVal U g = true := by
                  intro j hjF'
                  cases hrep : rep j with
                  | none => exact False.elim (hTriv.2 j hjF' hrep)
                  | some p =>
                    dsimp only [evalRep]
                    exact decide_eq_true_iff
                constructor
                · rintro (⟨u, huBV, huU⟩ | ⟨g, hgFG, hgv⟩)
                  · rw [Finset.mem_union] at huBV
                    rcases huBV with huB | huBi
                    · exact Or.inl ⟨u, huB, Finset.mem_insert_of_mem huU⟩
                    · rw [Finset.mem_biUnion] at huBi
                      obtain ⟨j, hjF', hu1⟩ := huBi
                      have hjF : (⟨j.val, by omega⟩ : Fin D'.size) ∈ F :=
                        (Finset.mem_filter.mp hjF').2
                      refine Or.inr ⟨⟨j.val, by omega⟩, hjF, hF _ hjF, ?_⟩
                      rw [← hAEv U hvU j]
                      exact (hRepSome j hjF').mpr (Or.inl ⟨u, hu1, huU⟩)
                  · rw [Finset.mem_biUnion] at hgFG
                    obtain ⟨j, hjF', hg1⟩ := hgFG
                    have hjF : (⟨j.val, by omega⟩ : Fin D'.size) ∈ F :=
                      (Finset.mem_filter.mp hjF').2
                    refine Or.inr ⟨⟨j.val, by omega⟩, hjF, hF _ hjF, ?_⟩
                    rw [← hAEv U hvU j]
                    exact (hRepSome j hjF').mpr (Or.inr ⟨g, hg1, hgv⟩)
                · rintro (⟨u, huB, huI⟩ | ⟨j, hjF, hji, hjv⟩)
                  · rw [Finset.mem_insert] at huI
                    rcases huI with rfl | huU
                    · exact False.elim (hTriv.1 huB)
                    · exact Or.inl ⟨u, Finset.mem_union_left _ huB, huU⟩
                  · have hjlt : j.val < r + 1 := hji
                    let j' : Fin (r + 1) := ⟨j.val, hjlt⟩
                    have hj'F : j' ∈ F' :=
                      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjF⟩
                    rw [← hAEv U hvU j'] at hjv
                    rcases (hRepSome j' hj'F).mp hjv with ⟨u, hu1, huU⟩ | ⟨g, hg1, hgv⟩
                    · exact Or.inl ⟨u, Finset.mem_union_right _
                        (Finset.mem_biUnion.mpr ⟨j', hj'F, hu1⟩), huU⟩
                    · exact Or.inr ⟨g, Finset.mem_biUnion.mpr ⟨j', hj'F, hg1⟩, hgv⟩
            obtain ⟨rL, hrL⟩ := hSideRep (D'.leftVars gi) (D'.leftGates gi) (hDWF gi).1
            obtain ⟨rR, hrR⟩ := hSideRep (D'.rightVars gi) (D'.rightGates gi) (hDWF gi).2
            have hAndEv : ∀ U : Finset (Fin 42), v ∉ U →
                (evalRep A rL U && evalRep A rR U) = D'.gateVal (insert v U) gi := by
              intro U hvU
              apply Bool.eq_iff_iff.mpr
              rw [Bool.and_eq_true, hrL U hvU, hrR U hvU, hGateValIff D' (insert v U) gi]
            cases hrLc : rL with
            | none =>
              refine ⟨A, Fin.snoc rep rR, hAWF, by omega, ?_⟩
              intro U hvU j
              refine Fin.lastCases ?_ ?_ j
              · rw [Fin.snoc_last]
                have h := hAndEv U hvU
                rw [hrLc] at h
                exact h
              · intro j'
                rw [Fin.snoc_castSucc]
                exact hAEv U hvU j'
            | some pL =>
              cases hrRc : rR with
              | none =>
                refine ⟨A, Fin.snoc rep (some pL), hAWF, by omega, ?_⟩
                intro U hvU j
                refine Fin.lastCases ?_ ?_ j
                · rw [Fin.snoc_last]
                  have h := hAndEv U hvU
                  rw [hrLc, hrRc] at h
                  change evalRep A (some pL) U = D'.gateVal (insert v U) gi
                  simpa only [evalRep, Bool.and_true] using h
                · intro j'
                  rw [Fin.snoc_castSucc]
                  exact hAEv U hvU j'
              | some pR =>
                let B := appendGate A pL.1 pL.2 pR.1 pR.2
                let repB : Fin (r + 2) → Option (Finset (Fin 42) × Finset (Fin B.size)) :=
                  Fin.snoc (fun j => @liftRep A pL.1 pR.1 pL.2 pR.2 (rep j))
                    (some (∅, {Fin.last A.size}))
                refine ⟨B, repB, hAppendWF A pL.1 pL.2 pR.1 pR.2 hAWF, by dsimp only [B, appendGate]; omega, ?_⟩
                intro U hvU j
                refine Fin.lastCases ?_ ?_ j
                · dsimp only [repB]
                  rw [Fin.snoc_last]
                  have h1 : evalRep B (some (∅, {Fin.last A.size})) U =
                      B.gateVal U (Fin.last A.size) := by
                    apply Bool.eq_iff_iff.mpr
                    dsimp only [evalRep]
                    rw [decide_eq_true_iff]
                    constructor
                    · rintro (⟨_, hx, _⟩ | ⟨g, hg, hgv⟩)
                      · exact False.elim (Finset.notMem_empty _ hx)
                      · rw [Finset.mem_singleton] at hg
                        rwa [hg] at hgv
                    · intro hgv
                      exact Or.inr ⟨Fin.last A.size, Finset.mem_singleton_self _, hgv⟩
                  rw [h1, hAppendLast, ← hrLc, ← hrRc]
                  exact hAndEv U hvU
                · intro j'
                  dsimp only [repB]
                  rw [Fin.snoc_castSucc, hLiftEval]
                  exact hAEv U hvU j'
        obtain ⟨A, rep, hAWF, hAsz, hAEv⟩ := hFold (D'.size - 1) (by omega)
        have hSizeEq : D'.size - 1 + 1 = D'.size := by omega
        let rep' : Fin D'.size → Option (Finset (Fin 42) × Finset (Fin A.size)) :=
          fun j => rep ⟨j.val, by omega⟩
        have hRep'Ev : ∀ (U : Finset (Fin 42)), v ∉ U → ∀ j : Fin D'.size,
            evalRep A (rep' j) U = D'.gateVal (insert v U) j := by
          intro U hvU j
          exact hAEv U hvU ⟨j.val, by omega⟩
        have hNoNone : ∀ j ∈ D'.outGates, rep' j ≠ none := by
          intro j hjO hjn
          have hgv : D'.gateVal {v} j = true := by
            have h := hRep'Ev ∅ (Finset.notMem_empty v) j
            rw [hjn] at h
            change D'.gateVal (insert v ∅) j = true
            exact h.symm
          have hev : D'.eval {v} = true := (hEvalIff D' {v}).mpr (Or.inr ⟨j, hjO, hgv⟩)
          have hsub : ({v} : Finset (Fin 42)) ⊆ V := Finset.singleton_subset_iff.mpr hvV
          obtain ⟨k, h1, h2⟩ := (hD'Eval {v} hsub).mp hev
          rw [Finset.mem_singleton] at h1 h2
          exact hIM.1 k (h1.trans h2.symm)
        let E : AndCountCircuit 42 :=
          { size := A.size
            leftVars := A.leftVars
            leftGates := A.leftGates
            rightVars := A.rightVars
            rightGates := A.rightGates
            outVars := D'.outGates.biUnion (fun j => Option.casesOn (motive := fun _ => Finset (Fin 42)) (rep' j) ∅ Prod.fst)
            outGates := D'.outGates.biUnion (fun j => Option.casesOn (motive := fun _ => Finset (Fin A.size)) (rep' j) ∅ Prod.snd) }
        let M' : Fin m → Fin 42 × Fin 42 := fun k => M (k0.succAbove k)
        have hIM' : InducedMatching m M' := by
          refine ⟨fun k => hIM.1 (k0.succAbove k), fun k1 k2 hne =>
            hIM.2 (k0.succAbove k1) (k0.succAbove k2) (fun h => hne (Fin.succAbove_right_injective h))⟩
        have hEEval : ∀ U : Finset (Fin 42), U ⊆ vertsM m M' →
            (E.eval U = true ↔ ∃ k : Fin m, (M' k).1 ∈ U ∧ (M' k).2 ∈ U) := by
          intro U hUV'
          have hNotK0 : ∀ x ∈ U, x ≠ (M k0).1 ∧ x ≠ (M k0).2 := by
            intro x hx
            obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp (hUV' hx)
            have hne := hIM.2 (k0.succAbove k) k0 (Fin.succAbove_ne k0 k)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxk
            rcases hxk with rfl | rfl
            · exact ⟨hne.1, hne.2.1⟩
            · exact ⟨hne.2.2.1, hne.2.2.2⟩
          have hvU : v ∉ U := by
            intro hvIn
            have hnk := hNotK0 v hvIn
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvk0
            rcases hvk0 with h | h
            · exact hnk.1 h
            · exact hnk.2 h
          have hUV : insert v U ⊆ V := by
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hxU
            · exact hvV
            · obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp (hUV' hxU)
              exact Finset.mem_biUnion.mpr ⟨k0.succAbove k, Finset.mem_univ _, hxk⟩
          have hEFuel : ∀ (d : ℕ) (i : Fin A.size), E.gateValFuel U d i = A.gateValFuel U d i := by
            intro d
            induction d with
            | zero => intro _; rfl
            | succ d ihd =>
              intro i
              change (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (E.gateValFuel U d) &&
                  AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (E.gateValFuel U d)) =
                (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateValFuel U d) &&
                  AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateValFuel U d))
              have hfn : E.gateValFuel U d = A.gateValFuel U d := funext ihd
              rw [hfn]
          have hEeq : E.eval U = D'.eval (insert v U) := by
            apply Bool.eq_iff_iff.mpr
            rw [hEvalIff E U, hEvalIff D' (insert v U), hD'OutEmpty]
            have hEGV : ∀ g : Fin A.size, E.gateVal U g = A.gateVal U g :=
              fun g => hEFuel A.size g
            simp only [hEGV]
            dsimp only [E]
            have hRepSome : ∀ j ∈ D'.outGates,
                evalRep A (rep' j) U = true ↔
                  (∃ u ∈ Option.casesOn (motive := fun _ => Finset (Fin 42)) (rep' j) ∅ Prod.fst, u ∈ U) ∨
                  ∃ g ∈ Option.casesOn (motive := fun _ => Finset (Fin A.size)) (rep' j) ∅ Prod.snd,
                    A.gateVal U g = true := by
              intro j hjO
              cases hrep : rep' j with
              | none => exact False.elim (hNoNone j hjO hrep)
              | some p =>
                dsimp only [evalRep]
                exact decide_eq_true_iff
            constructor
            · rintro (⟨u, huO, huU⟩ | ⟨g, hgO, hgv⟩)
              · rw [Finset.mem_biUnion] at huO
                obtain ⟨j, hjO, hu1⟩ := huO
                refine Or.inr ⟨j, hjO, ?_⟩
                rw [← hRep'Ev U hvU j]
                exact (hRepSome j hjO).mpr (Or.inl ⟨u, hu1, huU⟩)
              · rw [Finset.mem_biUnion] at hgO
                obtain ⟨j, hjO, hg1⟩ := hgO
                refine Or.inr ⟨j, hjO, ?_⟩
                rw [← hRep'Ev U hvU j]
                exact (hRepSome j hjO).mpr (Or.inr ⟨g, hg1, hgv⟩)
            · rintro (⟨_, hx, _⟩ | ⟨j, hjO, hjv⟩)
              · exact False.elim (Finset.notMem_empty _ hx)
              · rw [← hRep'Ev U hvU j] at hjv
                rcases (hRepSome j hjO).mp hjv with ⟨u, hu1, huU⟩ | ⟨g, hg1, hgv⟩
                · exact Or.inl ⟨u, Finset.mem_biUnion.mpr ⟨j, hjO, hu1⟩, huU⟩
                · exact Or.inr ⟨g, Finset.mem_biUnion.mpr ⟨j, hjO, hg1⟩, hgv⟩
          rw [hEeq, hD'Eval (insert v U) hUV]
          constructor
          · rintro ⟨k, h1, h2⟩
            have hne : k ≠ k0 := by
              intro hkEq
              subst hkEq
              rw [Finset.mem_insert] at h1 h2
              rcases h1 with h1v | h1U
              · rcases h2 with h2v | h2U
                · exact hIM.1 k (h1v.trans h2v.symm)
                · exact (hNotK0 _ h2U).2 rfl
              · exact (hNotK0 _ h1U).1 rfl
            obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hne
            have hneK := hIM.2 (k0.succAbove k') k0 hne
            have hvNe1 : (M (k0.succAbove k')).1 ≠ v := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvk0
              rcases hvk0 with rfl | rfl
              · exact hneK.1
              · exact hneK.2.1
            have hvNe2 : (M (k0.succAbove k')).2 ≠ v := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvk0
              rcases hvk0 with rfl | rfl
              · exact hneK.2.2.1
              · exact hneK.2.2.2
            rw [Finset.mem_insert] at h1 h2
            refine ⟨k', ?_, ?_⟩
            · rcases h1 with h | h
              · exact False.elim (hvNe1 h)
              · exact h
            · rcases h2 with h | h
              · exact False.elim (hvNe2 h)
              · exact h
          · rintro ⟨k', h1, h2⟩
            exact ⟨k0.succAbove k', Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
        have hLB := ih M' hIM' E hAWF hEEval
        dsimp only [E] at hLB
        have hCsz : D'.size = C.size := hDsz
        omega
  intro x1 hMono hSpec
  by_contra hNotGE
  have hAndLT : {x4 : Fin x1.gates.length | (x1.gates.get x4).op = GateOp.and}.ncard ≤ 20 := by omega
  let isAnd : GateOp → Bool := fun op =>
    GateOp.casesOn op true false false (fun _ => false) false
  have hIsAnd : ∀ op : GateOp, isAnd op = true ↔ op = GateOp.and := by
    intro op
    cases op <;> simp [isAnd]
  have hCountEq : ∀ gs : List Gate,
      (gs.filter (fun g => isAnd g.op)).length =
        ∑ i : Fin gs.length, cond (isAnd (gs.get i).op) (1 : ℕ) 0 := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      change (List.filter (fun g => isAnd g.op) (g :: gs)).length =
        ∑ i : Fin (gs.length + 1), cond (isAnd ((g :: gs).get i).op) (1 : ℕ) 0
      rw [Fin.sum_univ_succ]
      change (List.filter (fun g => isAnd g.op) (g :: gs)).length =
        cond (isAnd g.op) (1 : ℕ) 0 +
          ∑ i : Fin gs.length, cond (isAnd (gs.get i).op) (1 : ℕ) 0
      rw [← ih]
      simp only [List.filter_cons]
      cases isAnd g.op
      · simp
      · simp
        omega
  have hFilterLE : (x1.gates.filter (fun g => isAnd g.op)).length ≤ 20 := by
    classical
    rw [hCountEq x1.gates]
    have hsum : ∑ i : Fin x1.gates.length, cond (isAnd (x1.gates.get i).op) (1 : ℕ) 0 =
        (Finset.univ.filter (fun i : Fin x1.gates.length => (x1.gates.get i).op = GateOp.and)).card := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl ?_
      intro i _
      cases (x1.gates.get i).op <;> simp [isAnd]
    have hnc : {x4 : Fin x1.gates.length | (x1.gates.get x4).op = GateOp.and}.ncard =
        (Finset.univ.filter (fun x4 : Fin x1.gates.length => (x1.gates.get x4).op = GateOp.and)).card := by
      have hset : {x4 : Fin x1.gates.length | (x1.gates.get x4).op = GateOp.and} =
          ((Finset.univ.filter (fun x4 : Fin x1.gates.length => (x1.gates.get x4).op = GateOp.and) : Finset _) : Set _) := by
        ext i
        simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hset, Set.ncard_coe_finset]
    omega
  let xU : Finset (Fin 42) → Fin 42 → Bool := fun U v => decide (v ∈ U)
  have hStmtMem : ∀ a b : Fin 42,
      (a.val, b.val) ∈ List.flatMap (fun (x6 : ℕ) =>
        [(x6, 21 + (x6 + 20) % 21), (x6, 21 + x6), (x6, 21 + (x6 + 5) % 21),
         (x6, 21 + (x6 + 7) % 21), (x6, 21 + (x6 + 17) % 21)]) (List.range 21) ↔
      pg4Rel a b := by
    intro a b
    rw [List.mem_flatMap]
    dsimp only [pg4Rel, S]
    simp only [List.mem_range, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    constructor
    · rintro ⟨x6, hx6, (⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩)⟩
      · refine ⟨hx6, by omega, ?_⟩
        have h : (b.val + 21 - a.val) % 21 = 20 := by omega
        rw [h]
        omega
      · refine ⟨hx6, by omega, ?_⟩
        have h : (b.val + 21 - a.val) % 21 = 0 := by omega
        rw [h]
        omega
      · refine ⟨hx6, by omega, ?_⟩
        have h : (b.val + 21 - a.val) % 21 = 5 := by omega
        rw [h]
        omega
      · refine ⟨hx6, by omega, ?_⟩
        have h : (b.val + 21 - a.val) % 21 = 7 := by omega
        rw [h]
        omega
      · refine ⟨hx6, by omega, ?_⟩
        have h : (b.val + 21 - a.val) % 21 = 17 := by omega
        rw [h]
        omega
    · rintro ⟨ha, hb, hd⟩
      refine ⟨a.val, ha, ?_⟩
      rcases hd with h | h | h | h | h
      · right; left; exact ⟨rfl, by omega⟩
      · right; right; left; exact ⟨rfl, by omega⟩
      · right; right; right; left; exact ⟨rfl, by omega⟩
      · right; right; right; right; exact ⟨rfl, by omega⟩
      · left; exact ⟨rfl, by omega⟩
  have hX1Spec : ∀ U : Finset (Fin 42),
      x1.eval (List.ofFn (xU U)) = true ↔ ∃ a ∈ U, ∃ c ∈ U, PG4.Adj a c := by
    intro U
    rw [hSpec (xU U)]
    dsimp only [xU]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, haU, hbU⟩
      have hrel := (hStmtMem a b).mp hab
      have hne : a ≠ b := by
        intro h
        subst h
        exact absurd hrel.2.1 (by omega)
      exact ⟨a, haU, b, hbU, hne, Or.inl hrel⟩
    · rintro ⟨a, haU, b, hbU, _, (hrel | hrel)⟩
      · exact ⟨a, b, (hStmtMem a b).mpr hrel, haU, hbU⟩
      · exact ⟨b, a, (hStmtMem b a).mpr hrel, hbU, haU⟩
  have hCompile : ∀ gs : List Gate,
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∃ (A : AndCountCircuit 42)
        (reps : List (Option (Finset (Fin 42) × Finset (Fin A.size)))),
        A.WellFormed ∧
        A.size ≤ (gs.filter (fun g => isAnd g.op)).length ∧
        reps.length = 42 + gs.length ∧
        ∀ (U : Finset (Fin 42)),
          let ws := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn (xU U))
          ws.length = 42 + gs.length ∧
          ∀ w : ℕ, evalRep A (reps.getD w (some (∅, ∅))) U = ws.getD w false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      let A0 : AndCountCircuit 42 :=
        { size := 0
          leftVars := Fin.elim0
          leftGates := Fin.elim0
          rightVars := Fin.elim0
          rightGates := Fin.elim0
          outVars := ∅
          outGates := ∅ }
      let reps0 : List (Option (Finset (Fin 42) × Finset (Fin A0.size))) :=
        List.ofFn (fun v : Fin 42 => some ({v}, ∅))
      refine ⟨A0, reps0, fun i => Fin.elim0 i, le_refl 0, by simp [reps0], ?_⟩
      intro U
      refine ⟨by simp, ?_⟩
      intro w
      change evalRep A0 (reps0.getD w (some (∅, ∅))) U = (List.ofFn (xU U)).getD w false
      by_cases hw : w < 42
      · have h1 : reps0.getD w (some (∅, ∅)) = some ({⟨w, hw⟩}, ∅) := by
          dsimp only [reps0]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hw, ↓reduceDIte]
          rfl
        have h2 : (List.ofFn (xU U)).getD w false = decide ((⟨w, hw⟩ : Fin 42) ∈ U) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hw, ↓reduceDIte]
          rfl
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        dsimp only [evalRep]
        rw [decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro (⟨v, hv, hvU⟩ | ⟨_, h, _⟩)
          · rw [Finset.mem_singleton] at hv
            rwa [hv] at hvU
          · exact False.elim (Finset.notMem_empty _ h)
        · intro hmem
          exact Or.inl ⟨⟨w, hw⟩, Finset.mem_singleton_self _, hmem⟩
      · have h1 : reps0.getD w (some (∅, ∅)) = some (∅, ∅) := by
          dsimp only [reps0]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hw, ↓reduceDIte]
          rfl
        have h2 : (List.ofFn (xU U)).getD w false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hw, ↓reduceDIte]
          rfl
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        dsimp only [evalRep]
        rw [decide_eq_true_iff]
        simp
    | append_singleton gs g ih =>
      intro hgs
      have hgs0 : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_append_left _ hg')
      have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        hgs g (List.mem_append_right _ (List.mem_singleton_self g))
      obtain ⟨A, reps, hAWF, hAsz, hRlen, hEv⟩ := ih hgs0
      have hAppendWire : ∀ (A' : AndCountCircuit 42)
          (reps' : List (Option (Finset (Fin 42) × Finset (Fin A'.size))))
          (rNew : Option (Finset (Fin 42) × Finset (Fin A'.size))),
          reps'.length = 42 + gs.length →
          (∀ U w, evalRep A' (reps'.getD w (some (∅, ∅))) U =
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
              (List.ofFn (xU U))).getD w false) →
          (∀ U, evalRep A' rNew U =
            g.op.eval (g.inputs.map fun i =>
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                (List.ofFn (xU U))).getD i false)) →
          (reps' ++ [rNew]).length = 42 + (gs ++ [g]).length ∧
          ∀ U : Finset (Fin 42),
            let ws := (gs ++ [g]).foldl
              (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
              (List.ofFn (xU U))
            ws.length = 42 + (gs ++ [g]).length ∧
            ∀ w : ℕ, evalRep A' ((reps' ++ [rNew]).getD w (some (∅, ∅))) U = ws.getD w false := by
        intro A' reps' rNew hLen' hOld hNew
        refine ⟨by simp [hLen']; omega, ?_⟩
        intro U
        let ws0 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn (xU U))
        have hws0Len : ws0.length = 42 + gs.length := (hEv U).1
        have hwsEq : (gs ++ [g]).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn (xU U)) =
            ws0 ++ [g.op.eval (g.inputs.map fun i => ws0.getD i false)] := by
          simp [ws0, List.foldl_append]
        refine ⟨by rw [hwsEq]; simp [hws0Len]; omega, ?_⟩
        intro w
        rw [hwsEq]
        by_cases hw1 : w < 42 + gs.length
        · have hL : (reps' ++ [rNew]).getD w (some (∅, ∅)) = reps'.getD w (some (∅, ∅)) := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hLen', hw1]
          have hR : (ws0 ++ [g.op.eval (g.inputs.map fun i => ws0.getD i false)]).getD w false =
              ws0.getD w false := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hws0Len, hw1]
          rw [hL, hR]
          exact hOld U w
        · by_cases hw2 : w = 42 + gs.length
          · subst hw2
            have hL : (reps' ++ [rNew]).getD (42 + gs.length) (some (∅, ∅)) = rNew := by
              simp [List.getD_eq_getElem?_getD, hLen']
            have hR : (ws0 ++ [g.op.eval (g.inputs.map fun i => ws0.getD i false)]).getD
                (42 + gs.length) false =
                g.op.eval (g.inputs.map fun i => ws0.getD i false) := by
              simp [List.getD_eq_getElem?_getD, hws0Len]
            rw [hL, hR]
            exact hNew U
          · have hgt : 42 + gs.length + 1 ≤ w := by omega
            have hL : (reps' ++ [rNew]).getD w (some (∅, ∅)) = some (∅, ∅) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hLen']; omega)]
              rfl
            have hR : (ws0 ++ [g.op.eval (g.inputs.map fun i => ws0.getD i false)]).getD w false =
                false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hws0Len]; omega)]
              rfl
            rw [hL, hR]
            apply Bool.eq_iff_iff.mpr
            dsimp only [evalRep]
            rw [decide_eq_true_iff]
            simp
      have hFilterStep : (gs.filter (fun g' => isAnd g'.op)).length +
          cond (isAnd g.op) 1 0 =
          ((gs ++ [g]).filter (fun g' => isAnd g'.op)).length := by
        simp only [List.filter_append, List.filter_cons, List.filter_nil, List.length_append]
        cases isAnd g.op <;> simp
      rcases hg.1 with hop | hop
      · have hFInc : A.size + 1 ≤ ((gs ++ [g]).filter (fun g' => isAnd g'.op)).length := by
          rw [← hFilterStep, hop]
          change A.size + 1 ≤ _ + 1
          omega
        cases hin : g.inputs with
        | nil =>
          have hRes := hAppendWire A reps none hRlen (fun U w => (hEv U).2 w) (by
            intro U
            rw [hop, hin]
            rfl)
          exact ⟨A, reps ++ [none], hAWF, by omega, hRes.1, hRes.2⟩
        | cons u t =>
          cases ht : t with
          | nil =>
            let rU := reps.getD u (some (∅, ∅))
            have hRes := hAppendWire A reps rU hRlen (fun U w => (hEv U).2 w) (by
              intro U
              rw [hop, hin, ht]
              change evalRep A (reps.getD u (some (∅, ∅))) U = _
              rw [(hEv U).2 u]
              change _ = ((_ && true))
              exact (Bool.and_true _).symm)
            exact ⟨A, reps ++ [rU], hAWF, by omega, hRes.1, hRes.2⟩
          | cons v t2 =>
            cases ht2 : t2 with
            | cons _ _ =>
              have hlen := hg.2
              rw [hin, ht, ht2] at hlen
              simp at hlen
            | nil =>
              let rU := reps.getD u (some (∅, ∅))
              let rV := reps.getD v (some (∅, ∅))
              have hGoalEv : ∀ U : Finset (Fin 42),
                  g.op.eval (g.inputs.map fun i =>
                    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                      (List.ofFn (xU U))).getD i false) =
                  (evalRep A rU U && evalRep A rV U) := by
                intro U
                rw [hop, hin, ht, ht2]
                dsimp only [rU, rV]
                rw [(hEv U).2 u, (hEv U).2 v]
                have h2 : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
                  intro a b; cases a <;> cases b <;> rfl
                exact h2 _ _
              cases hrU : rU with
              | none =>
                have hRes := hAppendWire A reps rV hRlen (fun U w => (hEv U).2 w) (by
                  intro U
                  rw [hGoalEv U, hrU]
                  rfl)
                exact ⟨A, reps ++ [rV], hAWF, by omega, hRes.1, hRes.2⟩
              | some pU =>
                cases hrV : rV with
                | none =>
                  have hRes := hAppendWire A reps (some pU) hRlen (fun U w => (hEv U).2 w) (by
                    intro U
                    rw [hGoalEv U, hrU, hrV]
                    exact (Bool.and_true _).symm)
                  exact ⟨A, reps ++ [some pU], hAWF, by omega, hRes.1, hRes.2⟩
                | some pV =>
                  let B := appendGate A pU.1 pU.2 pV.1 pV.2
                  let repsB := reps.map (@liftRep A pU.1 pV.1 pU.2 pV.2)
                  let rNew : Option (Finset (Fin 42) × Finset (Fin B.size)) :=
                    some (∅, {Fin.last A.size})
                  have hOldB : ∀ U w, evalRep B (repsB.getD w (some (∅, ∅))) U =
                      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                        (List.ofFn (xU U))).getD w false := by
                    intro U w
                    by_cases hw : w < reps.length
                    · have h1 : repsB.getD w (some (∅, ∅)) =
                          @liftRep A pU.1 pV.1 pU.2 pV.2 (reps.getD w (some (∅, ∅))) := by
                        simp [repsB, List.getD_eq_getElem?_getD, hw]
                      rw [h1, hLiftEval]
                      exact (hEv U).2 w
                    · have h1 : repsB.getD w (some (∅, ∅)) = some (∅, ∅) := by
                        simp [repsB, List.getD_eq_getElem?_getD, Nat.not_lt.mp hw]
                      have h2 : reps.getD w (some (∅, ∅)) = some (∅, ∅) := by
                        simp [List.getD_eq_getElem?_getD, Nat.not_lt.mp hw]
                      rw [h1, ← (hEv U).2 w, h2]
                      apply Bool.eq_iff_iff.mpr
                      dsimp only [evalRep]
                      rw [decide_eq_true_iff, decide_eq_true_iff]
                      simp
                  have hNewB : ∀ U, evalRep B rNew U =
                      g.op.eval (g.inputs.map fun i =>
                        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                          (List.ofFn (xU U))).getD i false) := by
                    intro U
                    rw [hGoalEv U, hrU, hrV]
                    have h1 : evalRep B rNew U = B.gateVal U (Fin.last A.size) := by
                      apply Bool.eq_iff_iff.mpr
                      dsimp only [evalRep, rNew]
                      rw [decide_eq_true_iff]
                      constructor
                      · rintro (⟨_, hx, _⟩ | ⟨j, hj, hjv⟩)
                        · exact False.elim (Finset.notMem_empty _ hx)
                        · rw [Finset.mem_singleton] at hj
                          rwa [hj] at hjv
                      · intro hjv
                        exact Or.inr ⟨Fin.last A.size, Finset.mem_singleton_self _, hjv⟩
                    rw [h1]
                    exact hAppendLast A pU.1 pU.2 pV.1 pV.2 U
                  have hRes := hAppendWire B repsB rNew (by simp [repsB, hRlen]) hOldB hNewB
                  exact ⟨B, repsB ++ [rNew], hAppendWF A pU.1 pU.2 pV.1 pV.2 hAWF, hFInc, hRes.1, hRes.2⟩
      · have hFSame : A.size ≤ ((gs ++ [g]).filter (fun g' => isAnd g'.op)).length := by
          rw [← hFilterStep]
          omega
        cases hin : g.inputs with
        | nil =>
          have hRes := hAppendWire A reps (some (∅, ∅)) hRlen (fun U w => (hEv U).2 w) (by
            intro U
            rw [hop, hin]
            change evalRep A (some (∅, ∅)) U = false
            apply Bool.eq_iff_iff.mpr
            dsimp only [evalRep]
            rw [decide_eq_true_iff]
            simp)
          exact ⟨A, reps ++ [some (∅, ∅)], hAWF, hFSame, hRes.1, hRes.2⟩
        | cons u t =>
          cases ht : t with
          | nil =>
            let rU := reps.getD u (some (∅, ∅))
            have hRes := hAppendWire A reps rU hRlen (fun U w => (hEv U).2 w) (by
              intro U
              rw [hop, hin, ht]
              dsimp only [rU]
              rw [(hEv U).2 u]
              change _ = ((_ || false))
              exact (Bool.or_false _).symm)
            exact ⟨A, reps ++ [rU], hAWF, hFSame, hRes.1, hRes.2⟩
          | cons v t2 =>
            cases ht2 : t2 with
            | cons _ _ =>
              have hlen := hg.2
              rw [hin, ht, ht2] at hlen
              simp at hlen
            | nil =>
              let rU := reps.getD u (some (∅, ∅))
              let rV := reps.getD v (some (∅, ∅))
              let rOr : Option (Finset (Fin 42) × Finset (Fin A.size)) :=
                Option.casesOn rU none (fun p1 =>
                  Option.casesOn rV none (fun p2 => some (p1.1 ∪ p2.1, p1.2 ∪ p2.2)))
              have hRes := hAppendWire A reps rOr hRlen (fun U w => (hEv U).2 w) (by
                intro U
                rw [hop, hin, ht, ht2]
                have hGoal : GateOp.or.eval (List.map (fun i =>
                    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                      (List.ofFn (xU U))).getD i false) [u, v]) =
                    (evalRep A rU U || evalRep A rV U) := by
                  dsimp only [rU, rV]
                  rw [(hEv U).2 u, (hEv U).2 v]
                  have h2 : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
                    intro a b; cases a <;> cases b <;> rfl
                  exact h2 _ _
                rw [hGoal]
                cases hrU : rU with
                | none =>
                  dsimp only [rOr]
                  rw [hrU]
                  rfl
                | some p1 =>
                  cases hrV : rV with
                  | none =>
                    dsimp only [rOr]
                    rw [hrU, hrV]
                    exact (Bool.or_true _).symm
                  | some p2 =>
                    dsimp only [rOr]
                    rw [hrU, hrV]
                    apply Bool.eq_iff_iff.mpr
                    dsimp only [evalRep]
                    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
                    constructor
                    · rintro (⟨w, hw, hwU⟩ | ⟨j, hj, hjv⟩)
                      · rw [Finset.mem_union] at hw
                        rcases hw with hw1 | hw2
                        · exact Or.inl (Or.inl ⟨w, hw1, hwU⟩)
                        · exact Or.inr (Or.inl ⟨w, hw2, hwU⟩)
                      · rw [Finset.mem_union] at hj
                        rcases hj with hj1 | hj2
                        · exact Or.inl (Or.inr ⟨j, hj1, hjv⟩)
                        · exact Or.inr (Or.inr ⟨j, hj2, hjv⟩)
                    · rintro ((⟨w, hw1, hwU⟩ | ⟨j, hj1, hjv⟩) | (⟨w, hw2, hwU⟩ | ⟨j, hj2, hjv⟩))
                      · exact Or.inl ⟨w, Finset.mem_union_left _ hw1, hwU⟩
                      · exact Or.inr ⟨j, Finset.mem_union_left _ hj1, hjv⟩
                      · exact Or.inl ⟨w, Finset.mem_union_right _ hw2, hwU⟩
                      · exact Or.inr ⟨j, Finset.mem_union_right _ hj2, hjv⟩)
              exact ⟨A, reps ++ [rOr], hAWF, hFSame, hRes.1, hRes.2⟩
  obtain ⟨A, reps, hAWF, hAsz, _, hAEval⟩ := hCompile x1.gates hMono
  let rOut := reps.getD x1.output (some (∅, ∅))
  have hROutEv : ∀ U : Finset (Fin 42), evalRep A rOut U = x1.eval (List.ofFn (xU U)) := by
    intro U
    exact (hAEval U).2 x1.output
  cases hrOut : rOut with
  | none =>
    have h0 : x1.eval (List.ofFn (xU ∅)) = true := by
      rw [← hROutEv ∅, hrOut]
    obtain ⟨a, ha, _⟩ := (hX1Spec ∅).mp h0
    exact Finset.notMem_empty a ha
  | some pOut =>
    let C0 : AndCountCircuit 42 :=
      { size := A.size
        leftVars := A.leftVars
        leftGates := A.leftGates
        rightVars := A.rightVars
        rightGates := A.rightGates
        outVars := pOut.1
        outGates := pOut.2 }
    have hC0Fuel : ∀ (U : Finset (Fin 42)) (d : ℕ) (i : Fin A.size),
        C0.gateValFuel U d i = A.gateValFuel U d i := by
      intro U d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro i
        change (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (C0.gateValFuel U d) &&
            AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (C0.gateValFuel U d)) =
          (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateValFuel U d) &&
            AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateValFuel U d))
        have hfn : C0.gateValFuel U d = A.gateValFuel U d := funext ih
        rw [hfn]
    have hC0Comp : C0.Computes PG4 := by
      intro U
      have heq : C0.eval U = evalRep A (some pOut) U := by
        apply Bool.eq_iff_iff.mpr
        rw [hEvalIff C0 U]
        have hgv : ∀ j : Fin A.size, C0.gateVal U j = A.gateVal U j :=
          fun j => hC0Fuel U A.size j
        simp only [hgv]
        dsimp only [C0, evalRep]
        rw [decide_eq_true_iff]
      rw [heq, ← hrOut, hROutEv U]
      exact hX1Spec U
    obtain ⟨D, hDsz, hDWF, hDDisj, hDUnit, hDEval⟩ := hStrip C0 hAWF
    have hDComp : D.Computes PG4 := by
      intro U
      rw [hDEval U]
      exact hC0Comp U
    have hDOutEmpty : D.outVars = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      have htr : D.eval {v} = true :=
        (hEvalIff D {v}).mpr (Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩)
      obtain ⟨a, ha, c, hc, hadj⟩ := (hDComp {v}).mp htr
      rw [Finset.mem_singleton] at ha hc
      subst ha; subst hc
      exact PG4.loopless.irrefl _ hadj
    have hDHi : D.size ≤ 20 := by
      have h1 : D.size = A.size := hDsz
      omega
    have hDLo : 9 ≤ D.size := by
      apply hMatchingLB 9 m9
      · refine ⟨hM9_ne, fun k1 k2 hne => ?_⟩
        have h := hM9_disj k1 k2 hne
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      · exact hDWF
      · intro U hUV
        rw [hDComp U]
        constructor
        · rintro ⟨a, haU, c, hcU, hadj⟩
          obtain ⟨k1, _, hak1⟩ := Finset.mem_biUnion.mp (hUV haU)
          obtain ⟨k2, _, hck2⟩ := Finset.mem_biUnion.mp (hUV hcU)
          have hkEq : k1 = k2 := by
            by_contra hne
            have hd := hM9_disj k1 k2 hne
            have hadjB : pg4B a c = true := (hPG4_iff a c).mp hadj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hak1 hck2
            rcases hak1 with rfl | rfl <;> rcases hck2 with rfl | rfl
            · rw [hd.2.2.2.2.1] at hadjB; exact Bool.false_ne_true hadjB
            · rw [hd.2.2.2.2.2.1] at hadjB; exact Bool.false_ne_true hadjB
            · rw [hd.2.2.2.2.2.2.1] at hadjB; exact Bool.false_ne_true hadjB
            · rw [hd.2.2.2.2.2.2.2] at hadjB; exact Bool.false_ne_true hadjB
          subst hkEq
          have hac : a ≠ c := PG4.ne_of_adj hadj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hak1 hck2
          rcases hak1 with rfl | rfl <;> rcases hck2 with rfl | rfl
          · exact False.elim (hac rfl)
          · exact ⟨k1, haU, hcU⟩
          · exact ⟨k1, hcU, haU⟩
          · exact False.elim (hac rfl)
        · rintro ⟨k, h1, h2⟩
          exact ⟨(m9 k).1, h1, (m9 k).2, h2, (hPG4_iff _ _).mpr (hM9_adj k)⟩
    let SoundG : (C : AndCountCircuit 42) → Fin C.size → Prop := fun C i =>
      ∀ U : Finset (Fin 42), C.gateVal U i = true → ∃ u ∈ U, ∃ v ∈ U, PG4.Adj u v
    have hExUnsound : ∃ t : ℕ, ∃ ht : t < D.size, ¬ SoundG D ⟨t, ht⟩ := by
      by_contra hNone
      push Not at hNone
      have hAllSound : ∀ i : Fin D.size, SoundG D i := fun i => hNone i.val i.isLt
      have hExGate : ∀ k : Fin 21, ∃ t : ℕ, ∃ ht : t < D.size,
          D.gateVal {⟨k.val, by omega⟩, ⟨21 + k.val, by omega⟩} ⟨t, ht⟩ = true := by
        intro k
        let pk : Fin 42 := ⟨k.val, by omega⟩
        let lk : Fin 42 := ⟨21 + k.val, by omega⟩
        have hadj : PG4.Adj pk lk := by
          rw [hPG4_iff]
          dsimp only [pg4B, pk, lk, S]
          have h1 : k.val < 21 := k.isLt
          have h2 : 21 ≤ 21 + k.val := by omega
          have h3 : (21 + k.val + 21 - k.val) % 21 = 0 := by omega
          simp [h1, h2, h3]
        have hev : D.eval {pk, lk} = true :=
          (hDComp _).mpr ⟨pk, Finset.mem_insert_self _ _, lk,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hadj⟩
        rw [hEvalIff, hDOutEmpty] at hev
        rcases hev with ⟨_, h, _⟩ | ⟨j, _, hjv⟩
        · exact False.elim (Finset.notMem_empty _ h)
        · exact ⟨j.val, j.isLt, hjv⟩
      classical
      let f : Fin 21 → Fin D.size := fun k =>
        ⟨Nat.find (hExGate k), (Nat.find_spec (hExGate k)).1⟩
      have hfVal : ∀ k : Fin 21,
          D.gateVal {⟨k.val, by omega⟩, ⟨21 + k.val, by omega⟩} (f k) = true :=
        fun k => (Nat.find_spec (hExGate k)).2
      have hfSplit : ∀ k : Fin 21,
          let pk : Fin 42 := ⟨k.val, by omega⟩
          let lk : Fin 42 := ⟨21 + k.val, by omega⟩
          (pk ∈ D.leftVars (f k) ∧ lk ∈ D.rightVars (f k)) ∨
          (lk ∈ D.leftVars (f k) ∧ pk ∈ D.rightVars (f k)) := by
        intro k
        let pk : Fin 42 := ⟨k.val, by omega⟩
        let lk : Fin 42 := ⟨21 + k.val, by omega⟩
        have hgv := hfVal k
        rw [hGateValIff] at hgv
        have hMin : ∀ j : Fin D.size, j < f k → D.gateVal {pk, lk} j = false := by
          intro j hj
          cases hv : D.gateVal {pk, lk} j
          · rfl
          · exfalso
            exact Nat.find_min (hExGate k) hj ⟨j.isLt, hv⟩
        have hL : ∃ u ∈ D.leftVars (f k), u ∈ ({pk, lk} : Finset (Fin 42)) := by
          rcases hgv.1 with h | ⟨j, _, hji, hjv⟩
          · exact h
          · rw [hMin j hji] at hjv
            exact False.elim (Bool.false_ne_true hjv)
        have hR : ∃ w ∈ D.rightVars (f k), w ∈ ({pk, lk} : Finset (Fin 42)) := by
          rcases hgv.2 with h | ⟨j, _, hji, hjv⟩
          · exact h
          · rw [hMin j hji] at hjv
            exact False.elim (Bool.false_ne_true hjv)
        obtain ⟨u, huL, huM⟩ := hL
        obtain ⟨w, hwR, hwM⟩ := hR
        have huw : u ≠ w := by
          intro h
          subst h
          exact Finset.disjoint_left.mp (hDDisj (f k)) huL hwR
        simp only [Finset.mem_insert, Finset.mem_singleton] at huM hwM
        rcases huM with rfl | rfl <;> rcases hwM with rfl | rfl
        · exact False.elim (huw rfl)
        · exact Or.inl ⟨huL, hwR⟩
        · exact Or.inr ⟨huL, hwR⟩
        · exact False.elim (huw rfl)
      have hfInj : Function.Injective f := by
        intro k1 k2 hEq
        by_contra hne
        let p1 : Fin 42 := ⟨k1.val, by omega⟩
        let l1 : Fin 42 := ⟨21 + k1.val, by omega⟩
        let p2 : Fin 42 := ⟨k2.val, by omega⟩
        let l2 : Fin 42 := ⟨21 + k2.val, by omega⟩
        have hFire : ∀ a b : Fin 42, a ∈ D.leftVars (f k1) → b ∈ D.rightVars (f k1) → PG4.Adj a b := by
          intro a b ha hb
          have hgv : D.gateVal {a, b} (f k1) = true :=
            (hGateValIff D {a, b} (f k1)).mpr
              ⟨Or.inl ⟨a, ha, Finset.mem_insert_self _ _⟩,
               Or.inl ⟨b, hb, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩⟩
          obtain ⟨u, hu, w, hw, hadj⟩ := hAllSound (f k1) {a, b} hgv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
          rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
          · exact False.elim (PG4.loopless.irrefl _ hadj)
          · exact hadj
          · exact hadj.symm
          · exact False.elim (PG4.loopless.irrefl _ hadj)
        have hNoPP : ¬ PG4.Adj p1 p2 := by
          intro h
          rw [hPG4_iff] at h
          dsimp only [pg4B, p1, p2] at h
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨_, h2⟩, _⟩ | ⟨⟨_, h2⟩, _⟩ <;> omega
        have hNoDiag : PG4.Adj p1 l2 → PG4.Adj p2 l1 → False := by
          intro h1 h2
          rw [hPG4_iff] at h1 h2
          dsimp only [pg4B, p1, l1, p2, l2, S] at h1 h2
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          have hneV : k1.val ≠ k2.val := fun h => hne (Fin.ext h)
          rcases h1 with ⟨⟨_, _⟩, hd1⟩ | ⟨⟨hbad, _⟩, _⟩
          · rcases h2 with ⟨⟨_, _⟩, hd2⟩ | ⟨⟨hbad, _⟩, _⟩
            · omega
            · omega
          · omega
        have hS1 := hfSplit k1
        have hS2 := hfSplit k2
        rw [← hEq] at hS2
        rcases hS1 with ⟨hp1L, hl1R⟩ | ⟨hl1L, hp1R⟩ <;> rcases hS2 with ⟨hp2L, hl2R⟩ | ⟨hl2L, hp2R⟩
        · exact hNoDiag (hFire p1 l2 hp1L hl2R) (hFire p2 l1 hp2L hl1R)
        · exact hNoPP (hFire p1 p2 hp1L hp2R)
        · exact hNoPP (hFire p2 p1 hp2L hp1R).symm
        · exact hNoDiag (hFire l2 p1 hl2L hp1R).symm (hFire l1 p2 hl1L hp2R).symm
      have hCard := Fintype.card_le_of_injective f hfInj
      simp only [Fintype.card_fin] at hCard
      omega
    classical
    let i0 : Fin D.size := ⟨Nat.find hExUnsound, (Nat.find_spec hExUnsound).1⟩
    have hi0Unsound : ¬ SoundG D i0 := (Nat.find_spec hExUnsound).2
    have hi0Min : ∀ j : Fin D.size, j < i0 → SoundG D j := by
      intro j hj
      by_contra hns
      exact Nat.find_min hExUnsound hj ⟨j.isLt, hns⟩
    have hExWitness : ∃ U : Finset (Fin 42),
        D.gateVal U i0 = true ∧ ∀ u ∈ U, ∀ v ∈ U, ¬ PG4.Adj u v := by
      by_contra h
      push Not at h
      exact hi0Unsound h
    obtain ⟨U0, hU0Val, hU0Indep⟩ := hExWitness
    have hi0NotOut : i0 ∉ D.outGates := by
      intro hmem
      have hev : D.eval U0 = true := (hEvalIff D U0).mpr (Or.inr ⟨i0, hmem, hU0Val⟩)
      obtain ⟨u, hu, v, hv, hadj⟩ := (hDComp U0).mp hev
      exact hU0Indep u hu v hv hadj
    have hEarlierFalse : ∀ j : Fin D.size, j < i0 → D.gateVal U0 j = false := by
      intro j hj
      cases hv : D.gateVal U0 j
      · rfl
      · exfalso
        obtain ⟨u, hu, v, hvU, hadj⟩ := hi0Min j hj U0 hv
        exact hU0Indep u hu v hvU hadj
    have hGV0 := (hGateValIff D U0 i0).mp hU0Val
    have hExA : ∃ a ∈ D.leftVars i0, a ∈ U0 := by
      rcases hGV0.1 with h | ⟨j, _, hji, hjv⟩
      · exact h
      · rw [hEarlierFalse j hji] at hjv
        exact False.elim (Bool.false_ne_true hjv)
    have hExB : ∃ b ∈ D.rightVars i0, b ∈ U0 := by
      rcases hGV0.2 with h | ⟨j, _, hji, hjv⟩
      · exact h
      · rw [hEarlierFalse j hji] at hjv
        exact False.elim (Bool.false_ne_true hjv)
    obtain ⟨a0, ha0L, ha0U⟩ := hExA
    obtain ⟨b0, hb0R, hb0U⟩ := hExB
    have hab0Ne : a0 ≠ b0 := by
      intro h
      subst h
      exact Finset.disjoint_left.mp (hDDisj i0) ha0L hb0R
    have hab0NonAdj : ¬ PG4.Adj a0 b0 := hU0Indep a0 ha0U b0 hb0U
    let Good : (C : AndCountCircuit 42) → Fin C.size → Fin 42 → Fin 42 → Prop :=
      fun C i a b =>
        C.WellFormed ∧ C.Computes PG4 ∧ C.outVars = ∅ ∧
        (∀ (j : Fin C.size) (v : Fin 42), C.gateVal {v} j = false) ∧
        (∀ j : Fin C.size, Disjoint (C.leftVars j) (C.rightVars j)) ∧
        9 ≤ C.size ∧ C.size ≤ 20 ∧ i ∉ C.outGates ∧
        (∀ j : Fin C.size, j < i → SoundG C j) ∧
        a ∈ C.leftVars i ∧ b ∈ C.rightVars i
    have hGoodRelabel : ∀ (e : Equiv.Perm (Fin 42)),
        (∀ x y : Fin 42, PG4.Adj (e x) (e y) ↔ PG4.Adj x y) →
        ∀ (C : AndCountCircuit 42) (i : Fin C.size) (a b : Fin 42),
          Good C i a b →
          ∃ (C' : AndCountCircuit 42) (i' : Fin C'.size), Good C' i' (e a) (e b) := by
      intro e he C i a b hG
      let C' : AndCountCircuit 42 :=
        { size := C.size
          leftVars := fun j => (C.leftVars j).map e.toEmbedding
          leftGates := C.leftGates
          rightVars := fun j => (C.rightVars j).map e.toEmbedding
          rightGates := C.rightGates
          outVars := C.outVars.map e.toEmbedding
          outGates := C.outGates }
      have hC'Gate : ∀ (U : Finset (Fin 42)) (j : Fin C.size),
          C'.gateVal U j = C.gateVal (U.map e.symm.toEmbedding) j := by
        intro U
        have hInd : ∀ (k : ℕ) (hk : k < C.size),
            C'.gateVal U ⟨k, hk⟩ = C.gateVal (U.map e.symm.toEmbedding) ⟨k, hk⟩ := by
          intro k
          induction k using Nat.strongRecOn with
          | ind k ihk =>
            intro hk
            apply Bool.eq_iff_iff.mpr
            rw [hGateValIff C' U ⟨k, hk⟩, hGateValIff C _ ⟨k, hk⟩]
            dsimp only [C']
            have hS : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
                ((∃ v ∈ B.map e.toEmbedding, v ∈ U) ∨
                  ∃ j ∈ F, j < ⟨k, hk⟩ ∧ C'.gateVal U j = true) ↔
                ((∃ v ∈ B, v ∈ U.map e.symm.toEmbedding) ∨
                  ∃ j ∈ F, j < ⟨k, hk⟩ ∧ C.gateVal (U.map e.symm.toEmbedding) j = true) := by
              intro B F
              constructor
              · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
                · rw [Finset.mem_map] at hvB
                  obtain ⟨w, hwB, rfl⟩ := hvB
                  refine Or.inl ⟨w, hwB, Finset.mem_map.mpr ⟨e w, hvU, ?_⟩⟩
                  exact e.symm_apply_apply w
                · rw [ihk j.val hji j.isLt] at hjv
                  exact Or.inr ⟨j, hjF, hji, hjv⟩
              · rintro (⟨w, hwB, hwU⟩ | ⟨j, hjF, hji, hjv⟩)
                · rw [Finset.mem_map] at hwU
                  obtain ⟨v, hvU, hvw⟩ := hwU
                  have hvEq : e w = v := by
                    rw [← hvw]
                    exact e.apply_symm_apply v
                  refine Or.inl ⟨v, Finset.mem_map.mpr ⟨w, hwB, hvEq⟩, hvU⟩
                · rw [← ihk j.val hji j.isLt] at hjv
                  exact Or.inr ⟨j, hjF, hji, hjv⟩
            rw [hS (C.leftVars ⟨k, hk⟩) (C.leftGates ⟨k, hk⟩),
                hS (C.rightVars ⟨k, hk⟩) (C.rightGates ⟨k, hk⟩)]
        intro j
        exact hInd j.val j.isLt
      refine ⟨C', i, hG.1, ?_, ?_, ?_, ?_, hG.2.2.2.2.2.1, hG.2.2.2.2.2.2.1,
        hG.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
      · intro U
        have hEq : C'.eval U = C.eval (U.map e.symm.toEmbedding) := by
          apply Bool.eq_iff_iff.mpr
          rw [hEvalIff C' U, hEvalIff C _]
          have hOutC' : C'.outVars = ∅ := by
            dsimp only [C']
            rw [hG.2.2.1, Finset.map_empty]
          rw [hOutC', hG.2.2.1]
          simp only [Finset.notMem_empty, false_and, exists_false, false_or]
          constructor
          · rintro ⟨j, hjO, hjv⟩
            rw [hC'Gate] at hjv
            exact ⟨j, hjO, hjv⟩
          · rintro ⟨j, hjO, hjv⟩
            rw [← hC'Gate] at hjv
            exact ⟨j, hjO, hjv⟩
        rw [hEq, hG.2.1 (U.map e.symm.toEmbedding)]
        constructor
        · rintro ⟨u, hu, w, hw, hadj⟩
          rw [Finset.mem_map] at hu hw
          obtain ⟨u', hu', rfl⟩ := hu
          obtain ⟨w', hw', rfl⟩ := hw
          have hadj' : PG4.Adj u' w' := by
            have h := (he (e.symm u') (e.symm w')).mpr hadj
            simpa only [Equiv.apply_symm_apply] using h
          exact ⟨u', hu', w', hw', hadj'⟩
        · rintro ⟨u, hu, w, hw, hadj⟩
          refine ⟨e.symm u, Finset.mem_map.mpr ⟨u, hu, rfl⟩,
            e.symm w, Finset.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
          have h := (he (e.symm u) (e.symm w)).mp
          rw [e.apply_symm_apply, e.apply_symm_apply] at h
          exact h hadj
      · dsimp only [C']
        rw [hG.2.2.1, Finset.map_empty]
      · intro j v
        rw [hC'Gate {v} j, Finset.map_singleton]
        exact hG.2.2.2.1 j (e.symm v)
      · intro j
        dsimp only [C']
        exact Finset.disjoint_map e.toEmbedding |>.mpr (hG.2.2.2.2.1 j)
      · intro j hj U hgv
        rw [hC'Gate U j] at hgv
        obtain ⟨u, hu, w, hw, hadj⟩ := hG.2.2.2.2.2.2.2.2.1 j hj (U.map e.symm.toEmbedding) hgv
        rw [Finset.mem_map] at hu hw
        obtain ⟨u', hu', rfl⟩ := hu
        obtain ⟨w', hw', rfl⟩ := hw
        have hadj' : PG4.Adj u' w' := by
          have h := (he (e.symm u') (e.symm w')).mpr hadj
          simpa only [Equiv.apply_symm_apply] using h
        exact ⟨u', hu', w', hw', hadj'⟩
      · exact Finset.mem_map.mpr ⟨a, hG.2.2.2.2.2.2.2.2.2.1, rfl⟩
      · exact Finset.mem_map.mpr ⟨b, hG.2.2.2.2.2.2.2.2.2.2, rfl⟩
    have hGoodSwap : ∀ (C : AndCountCircuit 42) (i : Fin C.size) (a b : Fin 42),
        Good C i a b → ∃ (C' : AndCountCircuit 42) (i' : Fin C'.size), Good C' i' b a := by
      intro C i a b hG
      let C' : AndCountCircuit 42 :=
        { size := C.size
          leftVars := fun j => if j = i then C.rightVars j else C.leftVars j
          leftGates := fun j => if j = i then C.rightGates j else C.leftGates j
          rightVars := fun j => if j = i then C.leftVars j else C.rightVars j
          rightGates := fun j => if j = i then C.leftGates j else C.rightGates j
          outVars := C.outVars
          outGates := C.outGates }
      have hC'Gate : ∀ (U : Finset (Fin 42)) (j : Fin C.size), C'.gateVal U j = C.gateVal U j := by
        intro U
        have hInd : ∀ (k : ℕ) (hk : k < C.size),
            C'.gateVal U ⟨k, hk⟩ = C.gateVal U ⟨k, hk⟩ := by
          intro k
          induction k using Nat.strongRecOn with
          | ind k ihk =>
            intro hk
            apply Bool.eq_iff_iff.mpr
            rw [hGateValIff C' U ⟨k, hk⟩, hGateValIff C U ⟨k, hk⟩]
            have hS : ∀ (F : Finset (Fin C.size)),
                (∃ j ∈ F, j < ⟨k, hk⟩ ∧ C'.gateVal U j = true) ↔
                (∃ j ∈ F, j < ⟨k, hk⟩ ∧ C.gateVal U j = true) := by
              intro F
              constructor
              · rintro ⟨j, hjF, hji, hjv⟩
                rw [ihk j.val hji j.isLt] at hjv
                exact ⟨j, hjF, hji, hjv⟩
              · rintro ⟨j, hjF, hji, hjv⟩
                rw [← ihk j.val hji j.isLt] at hjv
                exact ⟨j, hjF, hji, hjv⟩
            dsimp only [C']
            split_ifs
            · rw [hS (C.rightGates ⟨k, hk⟩), hS (C.leftGates ⟨k, hk⟩)]
              exact and_comm
            · rw [hS (C.leftGates ⟨k, hk⟩), hS (C.rightGates ⟨k, hk⟩)]
        intro j
        exact hInd j.val j.isLt
      refine ⟨C', i, ?_, ?_, hG.2.2.1, ?_, ?_, hG.2.2.2.2.2.1, hG.2.2.2.2.2.2.1,
        hG.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
      · intro j
        dsimp only [C']
        split_ifs
        · exact ⟨(hG.1 j).2, (hG.1 j).1⟩
        · exact hG.1 j
      · intro U
        have hEq : C'.eval U = C.eval U := by
          apply Bool.eq_iff_iff.mpr
          rw [hEvalIff C' U, hEvalIff C U]
          simp only [hC'Gate]
          rfl
        rw [hEq]
        exact hG.2.1 U
      · intro j v
        rw [hC'Gate]
        exact hG.2.2.2.1 j v
      · intro j
        dsimp only [C']
        split_ifs
        · exact (hG.2.2.2.2.1 j).symm
        · exact hG.2.2.2.2.1 j
      · intro j hj U hgv
        rw [hC'Gate] at hgv
        exact hG.2.2.2.2.2.2.2.2.1 j hj U hgv
      · dsimp only [C']
        simp only [↓reduceIte]
        exact hG.2.2.2.2.2.2.2.2.2.2
      · dsimp only [C']
        simp only [↓reduceIte]
        exact hG.2.2.2.2.2.2.2.2.2.1
    have hFinalSame : ∀ (C : AndCountCircuit 42) (i : Fin C.size), Good C i 0 1 → False := by
      intro C i hG
      by_cases h18 : C.size ≤ 18
      · exact hSmallSame C hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2.1 h18
          i hG.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.2
      · exact hLargeSame C hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 (by omega) hG.2.2.2.2.2.2.1
          i hG.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.2
    have hFinalCross : ∀ (C : AndCountCircuit 42) (i : Fin C.size), Good C i 0 22 → False := by
      intro C i hG
      by_cases h18 : C.size ≤ 18
      · exact hSmallCross C hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2.1 h18
          i hG.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.2
      · exact hLargeCross C hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 (by omega) hG.2.2.2.2.2.2.1
          i hG.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.1 hG.2.2.2.2.2.2.2.2.2.2
    have hGood0 : Good D i0 a0 b0 :=
      ⟨hDWF, hDComp, hDOutEmpty, hDUnit, hDDisj, hDLo, hDHi, hi0NotOut, hi0Min, ha0L, hb0R⟩
    have hStep1 : ∃ (C1 : AndCountCircuit 42) (i1 : Fin C1.size) (a1 b1 : Fin 42),
        Good C1 i1 a1 b1 ∧ a1.val < 21 ∧ a1 ≠ b1 ∧ ¬ PG4.Adj a1 b1 := by
      by_cases ha : a0.val < 21
      · exact ⟨D, i0, a0, b0, hGood0, ha, hab0Ne, hab0NonAdj⟩
      · obtain ⟨eD, heDF, heDAdj⟩ := hDualPerm
        obtain ⟨C1, i1, hG1⟩ := hGoodRelabel eD heDAdj D i0 a0 b0 hGood0
        refine ⟨C1, i1, eD a0, eD b0, hG1, ?_, fun h => hab0Ne (eD.injective h), ?_⟩
        · rw [heDF a0]
          simp only [ha, ↓reduceIte]
          omega
        · intro hadj
          exact hab0NonAdj ((heDAdj a0 b0).mp hadj)
    obtain ⟨C1, i1, a1, b1, hG1, ha1Lt, hab1Ne, hab1NonAdj⟩ := hStep1
    obtain ⟨eS, heSF, heSAdj⟩ := hShiftPerm ⟨(21 - a1.val) % 21, by omega⟩
    obtain ⟨C2, i2, hG2⟩ := hGoodRelabel eS heSAdj C1 i1 a1 b1 hG1
    have ha2Zero : eS a1 = 0 := by
      rw [heSF a1]
      simp only [ha1Lt, ↓reduceIte]
      apply Fin.ext
      dsimp only []
      omega
    rw [ha2Zero] at hG2
    let b2 : Fin 42 := eS b1
    have hb2Ne : b2 ≠ 0 := by
      intro h
      exact hab1Ne (eS.injective (ha2Zero.trans h.symm))
    have hb2NonAdj : ¬ PG4.Adj 0 b2 := by
      intro h
      rw [← ha2Zero] at h
      exact hab1NonAdj ((heSAdj a1 b1).mp h)
    obtain ⟨eAff, heAffF, heAffAdj⟩ := hAff1Perm
    have hAffIter : ∀ (k : ℕ) (C : AndCountCircuit 42) (i : Fin C.size) (b : Fin 42),
        Good C i 0 b →
        ∃ (C' : AndCountCircuit 42) (i' : Fin C'.size), Good C' i' 0 (Nat.iterate aff1F k b) := by
      intro k
      induction k with
      | zero =>
        intro C i b hG
        exact ⟨C, i, hG⟩
      | succ k ihk =>
        intro C i b hG
        obtain ⟨C', i', hG'⟩ := ihk C i b hG
        obtain ⟨C'', i'', hG''⟩ := hGoodRelabel eAff heAffAdj C' i' 0 (Nat.iterate aff1F k b) hG'
        have h0 : eAff 0 = 0 := by
          rw [heAffF 0]
          rfl
        have hb : eAff (Nat.iterate aff1F k b) = Nat.iterate aff1F (k + 1) b := by
          rw [heAffF, Function.iterate_succ_apply']
        rw [h0, hb] at hG''
        exact ⟨C'', i'', hG''⟩
    let pAPerm : Equiv.Perm (Fin 42) :=
      ⟨mkMap pAL, mkMap pAInvL, fun x => (hPA_inv x).1, fun x => (hPA_inv x).2⟩
    let pBPerm : Equiv.Perm (Fin 42) :=
      ⟨mkMap pBL, mkMap pBInvL, fun x => (hPB_inv x).1, fun x => (hPB_inv x).2⟩
    let pCPerm : Equiv.Perm (Fin 42) :=
      ⟨mkMap pCL, mkMap pCL, hPC_inv, hPC_inv⟩
    have hPAAdj : ∀ x y, PG4.Adj (pAPerm x) (pAPerm y) ↔ PG4.Adj x y :=
      hSideEdgePres (mkMap pAL) hPA_side hPA_edge
    have hPBAdj : ∀ x y, PG4.Adj (pBPerm x) (pBPerm y) ↔ PG4.Adj x y :=
      hSideEdgePres (mkMap pBL) hPB_side hPB_edge
    have hPCAdj : ∀ x y, PG4.Adj (pCPerm x) (pCPerm y) ↔ PG4.Adj x y :=
      hSideEdgePres (mkMap pCL) hPC_side hPC_edge
    by_cases hb2Lt : b2.val < 21
    · have hb2NZ : b2.val ≠ 0 := fun h => hb2Ne (Fin.ext h)
      obtain ⟨k, hk⟩ := hOrbitSame ⟨b2.val, hb2Lt⟩ hb2NZ
      have hHitSame : ∃ (C3 : AndCountCircuit 42) (i3 : Fin C3.size) (b3 : Fin 42),
          Good C3 i3 0 b3 ∧ b3.val ∈ ([1, 3, 7] : List ℕ) := by
        rcases hk with hDir | hRev
        · obtain ⟨C3, i3, hG3⟩ := hAffIter k.val C2 i2 b2 hG2
          have hb2Eq : (⟨b2.val, by omega⟩ : Fin 42) = b2 := Fin.ext rfl
          rw [hb2Eq] at hDir
          exact ⟨C3, i3, Nat.iterate aff1F k.val b2, hG3, hDir⟩
        · obtain ⟨C2s, i2s, hG2s⟩ := hGoodSwap C2 i2 0 b2 hG2
          obtain ⟨eS2, heS2F, heS2Adj⟩ := hShiftPerm ⟨(21 - b2.val) % 21, by omega⟩
          obtain ⟨C2t, i2t, hG2t⟩ := hGoodRelabel eS2 heS2Adj C2s i2s b2 0 hG2s
          have hb2Z : eS2 b2 = 0 := by
            rw [heS2F b2]
            simp only [hb2Lt, ↓reduceIte]
            apply Fin.ext
            dsimp only []
            omega
          have h0Img : eS2 0 = ⟨(21 - b2.val) % 21, by omega⟩ := by
            rw [heS2F 0]
            simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte]
            apply Fin.ext
            dsimp only []
            omega
          rw [hb2Z, h0Img] at hG2t
          obtain ⟨C3, i3, hG3⟩ := hAffIter k.val C2t i2t ⟨(21 - b2.val) % 21, by omega⟩ hG2t
          exact ⟨C3, i3, Nat.iterate aff1F k.val ⟨(21 - b2.val) % 21, by omega⟩, hG3, hRev⟩
      obtain ⟨C3, i3, b3, hG3, hb3Mem⟩ := hHitSame
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb3Mem
      rcases hb3Mem with h1 | h3 | h7
      · have hb3Eq : b3 = 1 := Fin.ext h1
        rw [hb3Eq] at hG3
        exact hFinalSame C3 i3 hG3
      · have hb3Eq : b3 = 3 := Fin.ext h3
        rw [hb3Eq] at hG3
        obtain ⟨C4, i4, hG4⟩ := hGoodRelabel pAPerm hPAAdj C3 i3 0 3 hG3
        have h0 : pAPerm 0 = 0 := hP_pts.1
        have h3' : pAPerm 3 = 1 := hP_pts.2.1
        rw [h0, h3'] at hG4
        exact hFinalSame C4 i4 hG4
      · have hb3Eq : b3 = 7 := Fin.ext h7
        rw [hb3Eq] at hG3
        obtain ⟨C4, i4, hG4⟩ := hGoodRelabel pBPerm hPBAdj C3 i3 0 7 hG3
        have h0 : pBPerm 0 = 0 := hP_pts.2.2.2.1
        have h7' : pBPerm 7 = 1 := hP_pts.2.2.2.2.1
        rw [h0, h7'] at hG4
        exact hFinalSame C4 i4 hG4
    · have hb2B : pg4B 0 ⟨21 + (b2.val - 21), by omega⟩ = false := by
        have hb2Eq : (⟨21 + (b2.val - 21), by omega⟩ : Fin 42) = b2 :=
          Fin.ext (by dsimp only []; omega)
        rw [hb2Eq]
        cases hv : pg4B 0 b2
        · rfl
        · exact False.elim (hb2NonAdj ((hPG4_iff 0 b2).mpr hv))
      obtain ⟨k, hk⟩ := hOrbitCross ⟨b2.val - 21, by omega⟩ hb2B
      have hb2Eq : (⟨21 + (b2.val - 21), by omega⟩ : Fin 42) = b2 :=
        Fin.ext (by dsimp only []; omega)
      rw [hb2Eq] at hk
      obtain ⟨C3, i3, hG3⟩ := hAffIter k.val C2 i2 b2 hG2
      let b3 : Fin 42 := Nat.iterate aff1F k.val b2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h22 | h23 | h24 | h35
      · have hb3Eq : b3 = 22 := Fin.ext h22
        change Good C3 i3 0 b3 at hG3
        rw [hb3Eq] at hG3
        exact hFinalCross C3 i3 hG3
      · have hb3Eq : b3 = 23 := Fin.ext h23
        change Good C3 i3 0 b3 at hG3
        rw [hb3Eq] at hG3
        obtain ⟨C4, i4, hG4⟩ := hGoodRelabel pAPerm hPAAdj C3 i3 0 23 hG3
        have h0 : pAPerm 0 = 0 := hP_pts.1
        have h23' : pAPerm 23 = 22 := hP_pts.2.2.1
        rw [h0, h23'] at hG4
        exact hFinalCross C4 i4 hG4
      · have hb3Eq : b3 = 24 := Fin.ext h24
        change Good C3 i3 0 b3 at hG3
        rw [hb3Eq] at hG3
        obtain ⟨C4, i4, hG4⟩ := hGoodRelabel pBPerm hPBAdj C3 i3 0 24 hG3
        have h0 : pBPerm 0 = 0 := hP_pts.2.2.2.1
        have h24' : pBPerm 24 = 22 := hP_pts.2.2.2.2.2.1
        rw [h0, h24'] at hG4
        exact hFinalCross C4 i4 hG4
      · have hb3Eq : b3 = 35 := Fin.ext h35
        change Good C3 i3 0 b3 at hG3
        rw [hb3Eq] at hG3
        obtain ⟨C4, i4, hG4⟩ := hGoodRelabel pCPerm hPCAdj C3 i3 0 35 hG3
        have h0 : pCPerm 0 = 0 := hP_pts.2.2.2.2.2.2.1
        have h35' : pCPerm 35 = 22 := hP_pts.2.2.2.2.2.2.2
        rw [h0, h35'] at hG4
        exact hFinalCross C4 i4 hG4
