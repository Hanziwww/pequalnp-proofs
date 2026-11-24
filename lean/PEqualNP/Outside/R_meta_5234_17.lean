import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_5234_17
    (hNot1RawOrMono :
      have p10 : (Fin 10 → Bool) → Bool := fun x =>
        [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun k =>
          x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10));
      ∀ w ∈ ([0, 1, 3, 6, 8, 10] : List ℕ),
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 D →
          PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 D →
          D.size ≤ 17 →
          ∃ x : Fin 10 → Bool,
            have xs : List Bool := List.ofFn x ++ [x 0 || x 2];
            D.eval (xs ++ [!xs.getD w false]) ≠ p10 x)
    (hNot1Internal :
      have p10 : (Fin 10 → Bool) → Bool := fun x =>
        [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun k =>
          x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10));
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 D →
        D.size ≤ 18 →
        D.output = 10 + D.size →
        PEqualNP.NotBracket.notCount D = 1 →
        (∃ j < D.size - 1, ∃ g w,
          D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            g.inputs.head? = some w ∧ 11 ≤ w) →
        ∃ x : Fin 10 → Bool,
          D.eval (List.ofFn x ++ [x 0 || x 2]) ≠ p10 x)
    (hNot2RawSlide :
      have p10 : (Fin 10 → Bool) → Bool := fun x =>
        [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun k =>
          x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10));
      ∀ w ∈ ([0, 1, 3, 6, 8, 10] : List ℕ),
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D →
          PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 D →
          D.size ≤ 17 →
          PEqualNP.NotBracket.notCount D = 1 →
          ∃ x : Fin 10 → Bool,
            have xs : List Bool := List.ofFn x ++ [x 0 || x 2];
            D.eval (xs ++ [!xs.getD w false]) ≠ p10 x)
    (hNot2Internal :
      have p10 : (Fin 10 → Bool) → Bool := fun x =>
        [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun k =>
          x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10));
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 D →
        D.size ≤ 18 →
        D.output = 10 + D.size →
        PEqualNP.NotBracket.notCount D = 2 →
        (∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not →
          ∃ w, g.inputs.head? = some w ∧ 11 ≤ w) →
        ∃ x : Fin 10 → Bool,
          D.eval (List.ofFn x ++ [x 0 || x 2]) ≠ p10 x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  intro C hFan hRB hSz houtLo houtHi hNotLo hNotHi
  let p10 : (Fin 10 → Bool) → Bool := fun x =>
    [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun k =>
      x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10))
  let p10raw : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have hp10_eq (x : Fin 10 → Bool) : p10raw x = p10 x := by
    change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) =
      (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 ||
      (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))))))
    rw [Bool.or_false]
    ac_rfl
  let edges10 : List (Fin 10 × Fin 10) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  have hp10_edges (x : Fin 10 → Bool) : p10 x = edges10.any (fun e => x e.1 && x e.2) := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 ||
      (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || (x 8 && x 5 || false))))))))))))))) =
      (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 ||
      (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))))))
    rfl
  let xs : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 2]
  have hxs_len (x : Fin 10 → Bool) : (xs x).length = 11 := by
    simp only [xs, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have hxs_read (x : Fin 10 → Bool) (i : Fin 10) : (xs x).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simp only [List.length_ofFn]; exact i.isLt
    dsimp only [xs]
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hxs_read10 (x : Fin 10 → Bool) : (xs x).getD 10 false = (x 0 || x 2) := by
    have h10 : (List.ofFn x).length = 10 := List.length_ofFn
    dsimp only [xs]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [h10, Nat.sub_self, List.getD_cons_zero]
  let isNot : Gate → Bool := fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)
  have hisNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not :=
    @decide_eq_true_iff _ (lineDegreeGateOpDecEq g.op GateOp.not)
  have hisNot_false (g : Gate) : isNot g = false ↔ g.op ≠ GateOp.not :=
    @decide_eq_false_iff_not _ (lineDegreeGateOpDecEq g.op GateOp.not)
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      rw [ih (step w g)]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_append (gs1 gs2 : List Gate) (w : List Bool) :
      run (gs1 ++ gs2) w = run gs2 (run gs1 w) := List.foldl_append
  have run_keep (gs : List Gate) (w : List Bool) :
      ∀ i < w.length, (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => intro i _; rfl
    | cons g rest ih =>
      intro i hi
      simp only [run, List.foldl_cons] at ih ⊢
      have hi' : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step w g) i hi']
      exact List.getD_append _ _ _ _ hi
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
  have remap_bijection (f : ℕ → ℕ) (L0 : ℕ)
      (hf_lt : ∀ i, i < L0 → f i < L0) (hf_ge : ∀ i, L0 ≤ i → f i = i)
      (gs : List Gate) (wA wB : List Bool)
      (hlen_w : wA.length = wB.length) (hL0 : L0 ≤ wA.length)
      (hrel : ∀ i, wB.getD (f i) false = wA.getD i false) :
      ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map f)) wB).getD (f i) false =
        (run gs wA).getD i false := by
    induction gs generalizing wA wB with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hinp : (g.inputs.map f).map (fun i => wB.getD i false) =
          g.inputs.map (fun i => wA.getD i false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hrel i
      let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
      have hstepB : step wB (Gate.mk g.op (g.inputs.map f)) = wB ++ [b] := by
        dsimp only [step, b]; rw [hinp]
      rw [hstepB]
      apply ih (step wA g) (wB ++ [b])
      · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        by_cases hi : i = wA.length
        · subst hi
          have hfi : f wA.length = wB.length := by rw [hf_ge wA.length hL0, hlen_w]
          rw [hfi, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
        · have hfi : f i ≠ wB.length := by
            intro hfeq
            by_cases hlt : i < L0
            · have := hf_lt i hlt; omega
            · have := hf_ge i (by omega); omega
          rw [getD_snoc_ne wB b false (f i) hfi, getD_snoc_ne wA b false i hi]
          exact hrel i
  have hMap_notCount (f : ℕ → ℕ) (gs : List Gate) :
      ((gs.map fun g => Gate.mk g.op (g.inputs.map f)).filter isNot).length = (gs.filter isNot).length := by
    induction gs with
    | nil => rfl
    | cons g rest ih =>
      simp only [List.map_cons, List.filter_cons]
      have hsame : isNot (Gate.mk g.op (g.inputs.map f)) = isNot g := rfl
      rw [hsame]
      cases isNot g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ih]
  have hMono_of_not0 (D : Circuit) (hDF : FanInTwo D) (hDN : notCount D = 0) : Monotone2 D := by
    intro g hg
    have hfg := hDF g hg
    refine ⟨?_, hfg.2⟩
    have hne : g.op ≠ GateOp.not := by
      intro heq
      have hmem : g ∈ D.gates.filter isNot := List.mem_filter.mpr ⟨hg, (hisNot_iff g).mpr heq⟩
      have hpos : 0 < (D.gates.filter isNot).length := List.length_pos_of_mem hmem
      have h0 : (D.gates.filter isNot).length = 0 := hDN
      omega
    rcases hfg.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hne
  have hLift11to12 (D : Circuit) (hDF : FanInTwo D) (hDRB : ReadsBack 11 D) (hDSz : D.size ≤ 17)
      (hDN : notCount D ≤ 1) :
      ∃ x : Fin 10 → Bool, D.eval (xs x) ≠ p10 x := by
    let lift : ℕ → ℕ := fun i => if i < 11 then i else i + 1
    let D' : Circuit := ⟨D.gates.map (fun g => Gate.mk g.op (g.inputs.map lift)), lift D.output⟩
    have hD'F : FanInTwo D' := by
      intro g hg
      simp only [D', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hf := hDF g0 hg0
      exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
    have hD'Sz : D'.size ≤ 17 := by
      change (D.gates.map _).length ≤ 17
      rw [List.length_map]; exact hDSz
    have hD'RB : ReadsBack 12 D' := by
      intro j hj u hu
      change j < (D.gates.map _).length at hj
      rw [List.length_map] at hj
      have hgetD' : (D'.gates.getD j ⟨GateOp.or, []⟩) =
          Gate.mk (D.gates.getD j ⟨GateOp.or, []⟩).op ((D.gates.getD j ⟨GateOp.or, []⟩).inputs.map lift) := by
        dsimp only [D']
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
            List.getD_eq_getElem _ _ hj]
      change u ∈ (D'.gates.getD j ⟨GateOp.or, []⟩).inputs at hu
      rw [hgetD'] at hu
      simp only [List.mem_map] at hu
      obtain ⟨i, hi, rfl⟩ := hu
      have hilt : i < 11 + j := hDRB j hj i hi
      dsimp only [lift]
      split_ifs <;> omega
    have hD'N : notCount D' = notCount D := hMap_notCount lift D.gates
    have hD'eval (x : Fin 10 → Bool) : D'.eval (xs x ++ [!(xs x).getD 0 false]) = D.eval (xs x) := by
      have hstep_sim (gs : List Gate) (wA wB : List Bool)
          (hwA : 11 ≤ wA.length) (hwB : wB.length = wA.length + 1)
          (hrel : ∀ i, wB.getD (lift i) false = wA.getD i false) :
          ∀ i, (run (gs.map fun g => Gate.mk g.op (g.inputs.map lift)) wB).getD (lift i) false =
            (run gs wA).getD i false := by
        induction gs generalizing wA wB with
        | nil => exact hrel
        | cons g rest ih =>
          simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
          have hinp : (g.inputs.map lift).map (fun i => wB.getD i false) =
              g.inputs.map (fun i => wA.getD i false) := by
            rw [List.map_map]; apply List.map_congr_left
            intro i _; exact hrel i
          let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
          have hstepB : step wB (Gate.mk g.op (g.inputs.map lift)) = wB ++ [b] := by
            dsimp only [step, b]; rw [hinp]
          rw [hstepB]
          apply ih (step wA g) (wB ++ [b])
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · intro i
            dsimp only [step]
            by_cases hi : i = wA.length
            · subst hi
              have hli : lift wA.length = wB.length := by dsimp only [lift]; split_ifs <;> omega
              rw [hli, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
            · have hli : lift i ≠ wB.length := by dsimp only [lift]; split_ifs <;> omega
              rw [getD_snoc_ne wB b false (lift i) hli, getD_snoc_ne wA b false i hi]
              exact hrel i
      have hrel0 : ∀ i, (xs x ++ [!(xs x).getD 0 false]).getD (lift i) false = (xs x).getD i false := by
        intro i
        by_cases hi : i < 11
        · have hli : lift i = i := by simp only [lift, hi, ↓reduceIte]
          rw [hli]
          exact List.getD_append _ _ _ _ (by rw [hxs_len x]; exact hi)
        · have hli : lift i = i + 1 := by simp only [lift, hi, ↓reduceIte]
          rw [hli,
              List.getD_eq_default (xs x ++ [!(xs x).getD 0 false]) false (n := i + 1)
                (by simp only [List.length_append, hxs_len x, List.length_cons, List.length_nil]; omega),
              List.getD_eq_default (xs x) false (n := i) (by rw [hxs_len x]; omega)]
      exact hstep_sim D.gates (xs x) (xs x ++ [!(xs x).getD 0 false])
        (by rw [hxs_len x])
        (by simp only [List.length_append, hxs_len x, List.length_cons, List.length_nil])
        hrel0 D.output
    have h0mem : (0 : ℕ) ∈ ([0, 1, 3, 6, 8, 10] : List ℕ) := List.mem_cons_self
    by_cases hDN0 : notCount D = 0
    · obtain ⟨x, hx⟩ := hNot1RawOrMono 0 h0mem D' (hMono_of_not0 D' hD'F (by rw [hD'N]; exact hDN0)) hD'RB hD'Sz
      exact ⟨x, by rw [← hD'eval x]; exact hx⟩
    · have hD'N1 : notCount D' = 1 := by omega
      obtain ⟨x, hx⟩ := hNot2RawSlide 0 h0mem D' hD'F hD'RB hD'Sz hD'N1
      exact ⟨x, by rw [← hD'eval x]; exact hx⟩
  let k : ℕ := C.output - 11 + 1
  have hk_pos : 1 ≤ k := by dsimp only [k]; omega
  have hk_le : k ≤ C.gates.length := by
    have : C.output < 11 + C.gates.length := houtHi
    dsimp only [k]; omega
  let C1 : Circuit := ⟨C.gates.take k, C.output⟩
  have hC1_len : C1.gates.length = k := by
    dsimp only [C1]; rw [List.length_take]; omega
  have hC1_sz_le : C1.size ≤ 18 := by
    change C1.gates.length ≤ 18
    have : C.gates.length ≤ 18 := hSz
    omega
  have hC1_out : C1.output = 10 + C1.size := by
    change C.output = 10 + C1.gates.length
    rw [hC1_len]; dsimp only [k]; omega
  have hC1_fan : FanInTwo C1 := fun g hg => hFan g (List.mem_of_mem_take hg)
  have hC1_rb : ReadsBack 11 C1 := by
    intro j hj i hi
    have hj_k : j < k := by rw [← hC1_len]; exact hj
    have hj_C : j < C.gates.length := by omega
    have hget : C1.gates.getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩ := by
      dsimp only [C1]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; omega), List.getElem_take,
          List.getD_eq_getElem _ _ hj_C]
    change i ∈ (C1.gates.getD j ⟨GateOp.or, []⟩).inputs at hi
    rw [hget] at hi
    exact hRB j hj_C i hi
  have hC1_eval (x : Fin 10 → Bool) : C1.eval (xs x) = C.eval (xs x) := by
    have hsp : C.gates = C1.gates ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    change (run C1.gates (xs x)).getD C.output false = (run C.gates (xs x)).getD C.output false
    conv_rhs => rw [hsp, run_append]
    have hlt : C.output < (run C1.gates (xs x)).length := by
      rw [run_len, hxs_len x, hC1_len]; dsimp only [k]; omega
    exact (run_keep (C.gates.drop k) (run C1.gates (xs x)) C.output hlt).symm
  have hC1_not_le : notCount C1 ≤ notCount C := by
    have hsp : C.gates = C1.gates ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    change (C1.gates.filter isNot).length ≤ (C.gates.filter isNot).length
    conv_rhs => rw [hsp, List.filter_append, List.length_append]
    omega
  have hDone (h : ∃ x : Fin 10 → Bool, C1.eval (xs x) ≠ p10 x) :
      ∃ x : Fin 10 → Bool, C.eval (xs x) ≠ p10raw x := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, by rw [← hC1_eval x, hp10_eq x]; exact hx⟩
  apply hDone
  by_cases hC1_not0 : notCount C1 = 0
  · have hC1_sz17 : C1.size ≤ 17 := by
      have hsp : C.gates = C1.gates ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
      have hnc : (C.gates.filter isNot).length = (C1.gates.filter isNot).length + ((C.gates.drop k).filter isNot).length := by
        conv_lhs => rw [hsp, List.filter_append, List.length_append]
      have hdrop_pos : 1 ≤ ((C.gates.drop k).filter isNot).length := by
        have h1 : 1 ≤ (C.gates.filter isNot).length := hNotLo
        have h0 : (C1.gates.filter isNot).length = 0 := hC1_not0
        omega
      have hdrop_len : 1 ≤ (C.gates.drop k).length :=
        Nat.le_trans hdrop_pos (List.length_filter_le isNot (C.gates.drop k))
      have hlen_sum : C.gates.length = C1.gates.length + (C.gates.drop k).length := by
        conv_lhs => rw [hsp, List.length_append]
      have hC18 : C.gates.length ≤ 18 := hSz
      change C1.gates.length ≤ 17
      omega
    exact hLift11to12 C1 hC1_fan hC1_rb hC1_sz17 (by omega)
  · have hC1_notLo : 1 ≤ notCount C1 := by omega
    have hC1_notHi : notCount C1 ≤ 2 := by omega
    by_cases hEmptyNot : ∃ g ∈ C1.gates, g.op = GateOp.not ∧ g.inputs = []
    · let sval : List Bool → Bool ⊕ ℕ → Bool := fun w => Sum.elim id (fun i => w.getD i false)
      let svalid : ℕ → Bool ⊕ ℕ → Prop := fun m => Sum.elim (fun _ => True) (fun i => i < m)
      let simpNot : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
        List.casesOn ins (none, Sum.inl true) (fun a _ =>
          Sum.elim (fun b => (none, Sum.inl (!b))) (fun i => (some (Gate.mk GateOp.not [i]), Sum.inr m)) a)
      let simpAnd : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
        List.casesOn ins (none, Sum.inl true) (fun a rest =>
          List.casesOn rest (none, a) (fun b _ =>
            Sum.elim
              (fun ba => if ba then (none, b) else (none, Sum.inl false))
              (fun ia => Sum.elim
                (fun bb => if bb then (none, Sum.inr ia) else (none, Sum.inl false))
                (fun ib => (some (Gate.mk GateOp.and [ia, ib]), Sum.inr m))
                b)
              a))
      let simpOr : ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m ins =>
        List.casesOn ins (none, Sum.inl false) (fun a rest =>
          List.casesOn rest (none, a) (fun b _ =>
            Sum.elim
              (fun ba => if ba then (none, Sum.inl true) else (none, b))
              (fun ia => Sum.elim
                (fun bb => if bb then (none, Sum.inl true) else (none, Sum.inr ia))
                (fun ib => (some (Gate.mk GateOp.or [ia, ib]), Sum.inr m))
                b)
              a))
      let simplify : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun op m ins =>
        GateOp.rec (simpAnd m ins) (simpOr m ins) (simpNot m ins) (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op
      have simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
          (hv : ∀ s ∈ ins, svalid m s) :
          (∀ g ∈ (simplify op m ins).1.toList,
            g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 ∧
              (∀ i ∈ g.inputs, i < m) ∧ (isNot g = true → op = GateOp.not)) := by
        cases op with
        | and =>
          cases ins with
          | nil => intro g hg; cases hg
          | cons a t =>
            cases t with
            | nil => intro g hg; cases hg
            | cons b t2 =>
              cases a with
              | inl ba => cases ba <;> (intro g hg; cases hg)
              | inr ia =>
                cases b with
                | inl bb => cases bb <;> (intro g hg; cases hg)
                | inr ib =>
                  intro g hg
                  change g ∈ [Gate.mk GateOp.and [ia, ib]] at hg
                  rw [List.mem_singleton] at hg; subst hg
                  have hia : ia < m := hv (Sum.inr ia) List.mem_cons_self
                  have hib : ib < m := hv (Sum.inr ib) (List.mem_cons_of_mem _ List.mem_cons_self)
                  refine ⟨Or.inl rfl, Nat.le_refl 2, ?_, fun hn => by have := (hisNot_iff _).mp hn; cases this⟩
                  intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> assumption
        | or =>
          cases ins with
          | nil => intro g hg; cases hg
          | cons a t =>
            cases t with
            | nil => intro g hg; cases hg
            | cons b t2 =>
              cases a with
              | inl ba => cases ba <;> (intro g hg; cases hg)
              | inr ia =>
                cases b with
                | inl bb => cases bb <;> (intro g hg; cases hg)
                | inr ib =>
                  intro g hg
                  change g ∈ [Gate.mk GateOp.or [ia, ib]] at hg
                  rw [List.mem_singleton] at hg; subst hg
                  have hia : ia < m := hv (Sum.inr ia) List.mem_cons_self
                  have hib : ib < m := hv (Sum.inr ib) (List.mem_cons_of_mem _ List.mem_cons_self)
                  refine ⟨Or.inr (Or.inl rfl), Nat.le_refl 2, ?_, fun hn => by have := (hisNot_iff _).mp hn; cases this⟩
                  intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> assumption
        | not =>
          cases ins with
          | nil => intro g hg; cases hg
          | cons a t =>
            cases a with
            | inl ba => intro g hg; cases hg
            | inr ia =>
              intro g hg
              change g ∈ [Gate.mk GateOp.not [ia]] at hg
              rw [List.mem_singleton] at hg; subst hg
              have hia : ia < m := hv (Sum.inr ia) List.mem_cons_self
              refine ⟨Or.inr (Or.inr rfl), Nat.le_succ 1, ?_, fun _ => rfl⟩
              intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              subst hi; exact hia
        | mod _ => intro g hg; cases hg
        | maj => intro g hg; cases hg
      have simplify_sound (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
          (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
          (hv : ∀ s ∈ ins, svalid w.length s) :
          svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
          sval (run (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
            op.eval (ins.map (sval w)) := by
        rcases hop with rfl | rfl | rfl
        · cases ins with
          | nil => exact ⟨trivial, rfl⟩
          | cons a t =>
            cases t with
            | nil =>
              have ha := hv a List.mem_cons_self
              refine ⟨by simpa only [simplify, simpAnd, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
              change sval w a = (sval w a && true); exact (Bool.and_true _).symm
            | cons b t2 =>
              cases t2 with
              | cons _ _ => simp only [List.length_cons] at hlen; omega
              | nil =>
                have ha := hv a List.mem_cons_self
                have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
                cases a with
                | inl ba =>
                  cases ba with
                  | true =>
                    refine ⟨by simpa only [simplify, simpAnd, Sum.elim_inl, ite_true, Option.toList_none, List.length_nil, Nat.add_zero] using hb, ?_⟩
                    change sval w b = (true && (sval w b && true)); cases sval w b <;> rfl
                  | false => exact ⟨trivial, rfl⟩
                | inr ia =>
                  cases b with
                  | inl bb =>
                    cases bb with
                    | true =>
                      refine ⟨by simpa only [simplify, simpAnd, Sum.elim_inr, Sum.elim_inl, ite_true, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
                      change w.getD ia false = (w.getD ia false && (true && true)); cases w.getD ia false <;> rfl
                    | false =>
                      refine ⟨trivial, ?_⟩
                      change false = (w.getD ia false && (false && true)); cases w.getD ia false <;> rfl
                  | inr ib =>
                    refine ⟨show w.length < w.length + 1 by omega, ?_⟩
                    change (w ++ [(w.getD ia false && (w.getD ib false && true))]).getD w.length false =
                      (w.getD ia false && (w.getD ib false && true))
                    exact getD_snoc_eq w _ false
        · cases ins with
          | nil => exact ⟨trivial, rfl⟩
          | cons a t =>
            cases t with
            | nil =>
              have ha := hv a List.mem_cons_self
              refine ⟨by simpa only [simplify, simpOr, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
              change sval w a = (sval w a || false); exact (Bool.or_false _).symm
            | cons b t2 =>
              cases t2 with
              | cons _ _ => simp only [List.length_cons] at hlen; omega
              | nil =>
                have ha := hv a List.mem_cons_self
                have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
                cases a with
                | inl ba =>
                  cases ba with
                  | true => exact ⟨trivial, rfl⟩
                  | false =>
                    refine ⟨by simpa only [simplify, simpOr, Sum.elim_inl, Bool.false_eq_true, ite_false, Option.toList_none, List.length_nil, Nat.add_zero] using hb, ?_⟩
                    change sval w b = (false || (sval w b || false)); cases sval w b <;> rfl
                | inr ia =>
                  cases b with
                  | inl bb =>
                    cases bb with
                    | true =>
                      refine ⟨trivial, ?_⟩
                      change true = (w.getD ia false || (true || false)); cases w.getD ia false <;> rfl
                    | false =>
                      refine ⟨by simpa only [simplify, simpOr, Sum.elim_inr, Sum.elim_inl, Bool.false_eq_true, ite_false, Option.toList_none, List.length_nil, Nat.add_zero] using ha, ?_⟩
                      change w.getD ia false = (w.getD ia false || (false || false)); cases w.getD ia false <;> rfl
                  | inr ib =>
                    refine ⟨show w.length < w.length + 1 by omega, ?_⟩
                    change (w ++ [(w.getD ia false || (w.getD ib false || false))]).getD w.length false =
                      (w.getD ia false || (w.getD ib false || false))
                    exact getD_snoc_eq w _ false
        · cases ins with
          | nil => exact ⟨trivial, rfl⟩
          | cons a t =>
            cases a with
            | inl ba => exact ⟨trivial, rfl⟩
            | inr ia =>
              refine ⟨show w.length < w.length + 1 by omega, ?_⟩
              change (w ++ [!(w.getD ia false)]).getD w.length false = !(w.getD ia false)
              exact getD_snoc_eq w _ false
      let elimStep : List (Bool ⊕ ℕ) × List Gate → Gate → List (Bool ⊕ ℕ) × List Gate := fun acc g =>
        let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
        let r := simplify g.op (11 + acc.2.length) ins
        (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
      let elim : List Gate → List (Bool ⊕ ℕ) × List Gate → List (Bool ⊕ ℕ) × List Gate := fun gs acc =>
        gs.foldl elimStep acc
      have hopt_len (o : Option Gate) : o.toList.length ≤ 1 := by cases o <;> simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons] <;> omega
      have elim_len_not (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
          (hacc_sv : ∀ i, svalid (11 + acc.2.length) (acc.1.getD i (Sum.inl false)))
          (hacc_fan : FanInTwo ⟨acc.2, 0⟩) (hacc_rb : ReadsBack 11 ⟨acc.2, 0⟩)
          (hgs_fan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
          (elim gs acc).2.length ≤ acc.2.length + gs.length ∧
          ((∃ g ∈ gs, g.op = GateOp.not ∧ g.inputs = []) → (elim gs acc).2.length < acc.2.length + gs.length) ∧
          ((elim gs acc).2.filter isNot).length ≤ (acc.2.filter isNot).length + (gs.filter isNot).length ∧
          ((∃ g ∈ gs, g.op = GateOp.not ∧ g.inputs = []) → ((elim gs acc).2.filter isNot).length < (acc.2.filter isNot).length + (gs.filter isNot).length) ∧
          FanInTwo ⟨(elim gs acc).2, 0⟩ ∧
          ReadsBack 11 ⟨(elim gs acc).2, 0⟩ := by
        induction gs generalizing acc with
        | nil =>
          refine ⟨?_, ?_, ?_, ?_, hacc_fan, hacc_rb⟩
          · simp only [elim, List.foldl_nil, List.length_nil, Nat.add_zero]; exact Nat.le_refl _
          · rintro ⟨_, h, _⟩; cases h
          · simp only [elim, List.foldl_nil, List.filter_nil, List.length_nil, Nat.add_zero]; exact Nat.le_refl _
          · rintro ⟨_, h, _⟩; cases h
        | cons g rest ih =>
          simp only [elim, List.foldl_cons] at ih ⊢
          have hgF := hgs_fan g List.mem_cons_self
          have hrestF := fun g' hg' => hgs_fan g' (List.mem_cons_of_mem g hg')
          let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
          let r := simplify g.op (11 + acc.2.length) ins
          have hins_v : ∀ s ∈ ins, svalid (11 + acc.2.length) s := by
            intro s hs
            simp only [ins, List.mem_map] at hs
            obtain ⟨i, _, rfl⟩ := hs
            exact hacc_sv i
          have hrok := simplify_ok g.op (11 + acc.2.length) ins hins_v
          have hr_sv : svalid (11 + acc.2.length + r.1.toList.length) r.2 :=
            (simplify_sound g.op hgF.1 (List.replicate (11 + acc.2.length) false) ins
              (by simp only [ins, List.length_map]; exact hgF.2)
              (by simpa only [List.length_replicate] using hins_v)).1 |> fun h => by
                simpa only [List.length_replicate] using h
          have hacc'_sv : ∀ i, svalid (11 + (elimStep acc g).2.length) ((elimStep acc g).1.getD i (Sum.inl false)) := by
            intro i
            dsimp only [elimStep]
            rw [List.length_append, ← Nat.add_assoc]
            by_cases hi : i = acc.1.length
            · subst hi; rw [getD_snoc_eq acc.1 r.2 (Sum.inl false)]; exact hr_sv
            · rw [getD_snoc_ne acc.1 r.2 (Sum.inl false) i hi]
              have hv := hacc_sv i
              cases hsi : acc.1.getD i (Sum.inl false) with
              | inl b => exact trivial
              | inr idx =>
                rw [hsi] at hv
                change idx < 11 + acc.2.length at hv
                change idx < 11 + acc.2.length + r.1.toList.length
                omega
          have hacc'_fan : FanInTwo ⟨(elimStep acc g).2, 0⟩ := by
            intro g' hg'
            simp only [elimStep, List.mem_append] at hg'
            rcases hg' with h1 | h2
            · exact hacc_fan g' h1
            · have h := hrok g' h2; exact ⟨h.1, h.2.1⟩
          have hacc'_rb : ReadsBack 11 ⟨(elimStep acc g).2, 0⟩ := by
            intro j hj u hu
            dsimp only [elimStep] at hj hu ⊢
            change j < (acc.2 ++ r.1.toList).length at hj
            rw [List.length_append] at hj
            by_cases hlt : j < acc.2.length
            · have hget : (acc.2 ++ r.1.toList).getD j ⟨GateOp.or, []⟩ = acc.2.getD j ⟨GateOp.or, []⟩ :=
                List.getD_append _ _ _ _ hlt
              change u ∈ ((acc.2 ++ r.1.toList).getD j ⟨GateOp.or, []⟩).inputs at hu
              rw [hget] at hu
              exact hacc_rb j hlt u hu
            · have hrlen : r.1.toList.length ≤ 1 := hopt_len r.1
              have hjeq : j = acc.2.length := by omega
              subst hjeq
              cases hro : r.1 with
              | none => rw [hro, Option.toList_none, List.length_nil] at hj; omega
              | some gnew =>
                have hget : (acc.2 ++ r.1.toList).getD acc.2.length ⟨GateOp.or, []⟩ = gnew := by
                  rw [hro, Option.toList_some]; exact getD_snoc_eq acc.2 gnew ⟨GateOp.or, []⟩
                change u ∈ ((acc.2 ++ r.1.toList).getD acc.2.length ⟨GateOp.or, []⟩).inputs at hu
                rw [hget] at hu
                exact (hrok gnew (by rw [hro, Option.toList_some]; exact List.mem_cons_self)).2.2.1 u hu
          obtain ⟨hL1, hL2, hN1, hN2, hF', hRB'⟩ := ih (elimStep acc g) hacc'_sv hacc'_fan hacc'_rb hrestF
          have hstep_len : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
            dsimp only [elimStep]; rw [List.length_append]; have := hopt_len r.1; dsimp only [r, ins] at this; omega
          have hstep_not : ((elimStep acc g).2.filter isNot).length ≤
              (acc.2.filter isNot).length + (if isNot g then 1 else 0) := by
            dsimp only [elimStep]; rw [List.filter_append, List.length_append]
            cases hro : r.1 with
            | none => simp only [Option.toList_none, List.filter_nil, List.length_nil]; split_ifs <;> omega
            | some gnew =>
              simp only [Option.toList_some, List.filter_cons, List.filter_nil]
              cases hgn : isNot gnew with
              | false => simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil]; split_ifs <;> omega
              | true =>
                have hgop : g.op = GateOp.not := (hrok gnew (by rw [hro, Option.toList_some]; exact List.mem_cons_self)).2.2.2 hgn
                have hg_is : isNot g = true := (hisNot_iff g).mpr hgop
                simp only [hg_is, ↓reduceIte, List.length_cons, List.length_nil]; omega
          have hflt_cons : ((g :: rest).filter isNot).length =
              (if isNot g then 1 else 0) + (rest.filter isNot).length := by
            simp only [List.filter_cons]
            cases isNot g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
          have hstep_empty (hgop : g.op = GateOp.not) (hgin : g.inputs = []) :
              (elimStep acc g).2.length = acc.2.length ∧
              ((elimStep acc g).2.filter isNot).length = (acc.2.filter isNot).length ∧
              isNot g = true := by
            have hrin : ins = [] := by simp only [ins, hgin, List.map_nil]
            have hrnone : r.1 = none := by dsimp only [r]; rw [hgop, hrin]
            refine ⟨?_, ?_, (hisNot_iff g).mpr hgop⟩
            · dsimp only [elimStep]; rw [hrnone, Option.toList_none, List.append_nil]
            · dsimp only [elimStep]; rw [hrnone, Option.toList_none, List.append_nil]
          refine ⟨by simp only [List.length_cons]; omega, ?_, by rw [hflt_cons]; omega, ?_, hF', hRB'⟩
          · rintro ⟨ge, hge, hgeop, hgein⟩
            simp only [List.mem_cons] at hge
            rcases hge with rfl | hrest_mem
            · have he := hstep_empty hgeop hgein
              simp only [List.length_cons]; omega
            · have := hL2 ⟨ge, hrest_mem, hgeop, hgein⟩
              simp only [List.length_cons]; omega
          · rintro ⟨ge, hge, hgeop, hgein⟩
            simp only [List.mem_cons] at hge
            rcases hge with rfl | hrest_mem
            · have he := hstep_empty hgeop hgein
              rw [hflt_cons, he.2.2]; simp only [↓reduceIte]; omega
            · have := hN2 ⟨ge, hrest_mem, hgeop, hgein⟩
              rw [hflt_cons]; omega
      let Inv (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
        w.length = 11 ∧ acc.1.length = z.length ∧
          ∀ i, svalid (11 + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
            sval (run acc.2 w) (acc.1.getD i (Sum.inl false)) = z.getD i false
      have elim_inv (gs : List Gate) (w z : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
          (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
          (hinv : Inv w z acc) :
          Inv w (run gs z) (elim gs acc) := by
        induction gs generalizing z acc with
        | nil => exact hinv
        | cons g rest ih =>
          simp only [elim, run, List.foldl_cons] at ih ⊢
          apply ih (step z g) (elimStep acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
          obtain ⟨hwl, hml, hmap⟩ := hinv
          have hgF := hgs g List.mem_cons_self
          let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
          let w' := run acc.2 w
          have hw'len : w'.length = 11 + acc.2.length := by rw [run_len, hwl]
          have hins_len : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact hgF.2
          have hins_v : ∀ s ∈ ins, svalid w'.length s := by
            intro s hs; simp only [ins, List.mem_map] at hs
            obtain ⟨i, _, rfl⟩ := hs; rw [hw'len]; exact (hmap i).1
          have hvals : ins.map (sval w') = g.inputs.map (fun i => z.getD i false) := by
            dsimp only [ins]; rw [List.map_map]; apply List.map_congr_left
            intro i _; exact (hmap i).2
          let r := simplify g.op w'.length ins
          have hrs := simplify_sound g.op hgF.1 w' ins hins_len hins_v
          have hstep_run : run (acc.2 ++ r.1.toList) w = run r.1.toList w' := List.foldl_append
          have heq_r : simplify g.op (11 + acc.2.length) ins = r := by rw [← hw'len]
          refine ⟨hwl, ?_, ?_⟩
          · simp only [elimStep, step, List.length_append, hml, List.length_cons, List.length_nil]
          · intro i
            dsimp only [elimStep]
            change svalid (11 + (acc.2 ++ (simplify g.op (11 + acc.2.length) ins).1.toList).length)
                ((acc.1 ++ [(simplify g.op (11 + acc.2.length) ins).2]).getD i (Sum.inl false)) ∧
              sval (run (acc.2 ++ (simplify g.op (11 + acc.2.length) ins).1.toList) w)
                ((acc.1 ++ [(simplify g.op (11 + acc.2.length) ins).2]).getD i (Sum.inl false)) =
              (z ++ [g.op.eval (g.inputs.map fun j => z.getD j false)]).getD i false
            rw [heq_r, hstep_run, List.length_append, ← Nat.add_assoc, ← hw'len]
            by_cases hi : i = acc.1.length
            · subst hi
              rw [getD_snoc_eq acc.1 r.2 (Sum.inl false), hml, getD_snoc_eq z _ false]
              exact ⟨hrs.1, hrs.2.trans (congrArg g.op.eval hvals)⟩
            · have hi' : i ≠ z.length := by rw [← hml]; exact hi
              rw [getD_snoc_ne acc.1 r.2 (Sum.inl false) i hi, getD_snoc_ne z _ false i hi']
              have hmi := hmap i
              rw [← hw'len] at hmi
              cases hsi : acc.1.getD i (Sum.inl false) with
              | inl b => rw [hsi] at hmi; exact ⟨trivial, hmi.2⟩
              | inr idx =>
                rw [hsi] at hmi
                have hidx_lt : idx < w'.length := hmi.1
                refine ⟨show idx < w'.length + r.1.toList.length by omega, ?_⟩
                change (run r.1.toList w').getD idx false = z.getD i false
                rw [run_keep r.1.toList w' idx hidx_lt]
                exact hmi.2
      let M0 : List (Bool ⊕ ℕ) := (List.range 11).map (Sum.inr : ℕ → Bool ⊕ ℕ)
      have hM0_len : M0.length = 11 := by simp only [M0, List.length_map, List.length_range]
      have hM0_lt (i : ℕ) (hi : i < 11) : M0.getD i (Sum.inl false) = Sum.inr i := by
        dsimp only [M0]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi),
            List.getElem_map, List.getElem_range]
      have hM0_sv (i : ℕ) : svalid (11 + ([] : List Gate).length) (M0.getD i (Sum.inl false)) := by
        by_cases hi : i < 11
        · rw [hM0_lt i hi]; exact hi
        · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by rw [hM0_len]; omega)]; exact trivial
      have hbase (x : Fin 10 → Bool) : Inv (xs x) (xs x) (M0, []) := by
        refine ⟨hxs_len x, by rw [hM0_len, hxs_len x], ?_⟩
        intro i
        by_cases hi : i < 11
        · rw [hM0_lt i hi]; exact ⟨by simp only [List.length_nil, Nat.add_zero]; exact hi, rfl⟩
        · rw [List.getD_eq_default M0 (Sum.inl false) (n := i) (by rw [hM0_len]; omega),
              List.getD_eq_default (xs x) false (n := i) (by rw [hxs_len x]; omega)]
          exact ⟨trivial, rfl⟩
      let res := elim C1.gates (M0, [])
      obtain ⟨_, hres_sz, _, hres_not, hres_fan, hres_rb⟩ := elim_len_not C1.gates (M0, []) hM0_sv
        (fun _ h => by cases h) (fun j hj => by cases hj) hC1_fan
      have hfin (x : Fin 10 → Bool) := elim_inv C1.gates (xs x) (xs x) (M0, []) hC1_fan (hbase x)
      cases hout : res.1.getD C1.output (Sum.inl false) with
      | inl b =>
        by_contra hno
        have hagree (x : Fin 10 → Bool) : C1.eval (xs x) = p10 x := by
          by_contra hne; exact hno ⟨x, hne⟩
        have hf0 : b = p10 (fun _ => false) := by
          have h := ((hfin (fun _ => false)).2.2 C1.output).2
          rw [hout] at h; exact h.trans (hagree (fun _ => false))
        have hf1 : b = p10 (fun _ => true) := by
          have h := ((hfin (fun _ => true)).2.2 C1.output).2
          rw [hout] at h; exact h.trans (hagree (fun _ => true))
        have hne : p10 (fun _ => false) ≠ p10 (fun _ => true) := by decide
        exact hne (hf0.symm.trans hf1)
      | inr out =>
        let D : Circuit := ⟨res.2, out⟩
        have hD_sz : D.size ≤ 17 := by
          have h := hres_sz hEmptyNot
          change (elim C1.gates (M0, [])).2.length ≤ 17
          have h18 : C1.gates.length ≤ 18 := hC1_sz_le
          simp only [List.length_nil, Nat.zero_add] at h
          omega
        have hD_not : notCount D ≤ 1 := by
          have h := hres_not hEmptyNot
          change ((elim C1.gates (M0, [])).2.filter isNot).length ≤ 1
          have h2 : (C1.gates.filter isNot).length ≤ 2 := hC1_notHi
          simp only [List.filter_nil, List.length_nil, Nat.zero_add] at h
          omega
        obtain ⟨x, hx⟩ := hLift11to12 D hres_fan hres_rb hD_sz hD_not
        have hev : D.eval (xs x) = C1.eval (xs x) := by
          have h := ((hfin x).2.2 C1.output).2
          rw [hout] at h; exact h
        exact ⟨x, by rw [← hev]; exact hx⟩
    · have hAllNotNonempty : ∀ g ∈ C1.gates, g.op = GateOp.not → ∃ w, g.inputs.head? = some w := by
        intro g hg hgop
        cases hin : g.inputs with
        | nil => exact absurd ⟨g, hg, hgop, hin⟩ hEmptyNot
        | cons w _ => exact ⟨w, rfl⟩
      by_cases hRawNot : ∃ j < C1.gates.length, ∃ g w,
          C1.gates[j]? = some g ∧ g.op = GateOp.not ∧ g.inputs.head? = some w ∧ w < 11
      · obtain ⟨j, hj, g0, w, hgetj, hg0op, hg0head, hwlt⟩ := hRawNot
        let pre : List Gate := C1.gates.take j
        let suf : List Gate := C1.gates.drop (j + 1)
        have hpre_len : pre.length = j := by dsimp only [pre]; rw [List.length_take]; omega
        have hC1_split : C1.gates = pre ++ g0 :: suf := by
          have hdrop : C1.gates.drop j = g0 :: suf := by
            have hge : C1.gates[j] = g0 := by
              rw [List.getElem?_eq_getElem hj] at hgetj; cases hgetj; rfl
            dsimp only [suf]
            rw [List.drop_eq_getElem_cons hj, hge]
          rw [← hdrop]; exact (List.take_append_drop j C1.gates).symm
        let fj : ℕ → ℕ := fun i =>
          if i < 11 then i else if i < 11 + j then i + 1 else if i = 11 + j then 11 else i
        let mapFj : Gate → Gate := fun g => Gate.mk g.op (g.inputs.map fj)
        let D : Circuit := ⟨(pre ++ suf).map mapFj, fj C1.output⟩
        have hD_fan : FanInTwo D := by
          intro g hg
          simp only [D, List.mem_map, List.mem_append] at hg
          obtain ⟨g', hg', rfl⟩ := hg
          have hg'C : g' ∈ C1.gates := by
            rw [hC1_split, List.mem_append, List.mem_cons]
            rcases hg' with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          have hf := hC1_fan g' hg'C
          exact ⟨hf.1, by simp only [mapFj, List.length_map]; exact hf.2⟩
        have hD_sz : D.size ≤ 17 := by
          change ((pre ++ suf).map mapFj).length ≤ 17
          have hlenC : C1.gates.length = pre.length + 1 + suf.length := by
            conv_lhs => rw [hC1_split, List.length_append, List.length_cons]
            omega
          have h18 : C1.gates.length ≤ 18 := hC1_sz_le
          rw [List.length_map, List.length_append]
          omega
        have hD_not : notCount D = notCount C1 - 1 := by
          change (((pre ++ suf).map mapFj).filter isNot).length = (C1.gates.filter isNot).length - 1
          rw [hMap_notCount fj (pre ++ suf), List.filter_append, List.length_append]
          have hC1n : (C1.gates.filter isNot).length =
              (pre.filter isNot).length + 1 + (suf.filter isNot).length := by
            conv_lhs => rw [hC1_split, List.filter_append, List.filter_cons]
            have hg0n : isNot g0 = true := (hisNot_iff g0).mpr hg0op
            simp only [hg0n, ↓reduceIte, List.length_append, List.length_cons]
            omega
          omega
        have hD_rb : ReadsBack 12 D := by
          intro idx hidx u hu
          change idx < ((pre ++ suf).map mapFj).length at hidx
          rw [List.length_map, List.length_append] at hidx
          have hgetD : D.gates.getD idx ⟨GateOp.or, []⟩ = mapFj ((pre ++ suf).getD idx ⟨GateOp.or, []⟩) := by
            dsimp only [D]
            rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_append]; exact hidx),
                List.getElem_map, List.getD_eq_getElem _ _ (by rw [List.length_append]; exact hidx)]
          change u ∈ (D.gates.getD idx ⟨GateOp.or, []⟩).inputs at hu
          rw [hgetD] at hu
          simp only [mapFj, List.mem_map] at hu
          obtain ⟨i, hi, rfl⟩ := hu
          by_cases hlt : idx < j
          · have hgp : (pre ++ suf).getD idx ⟨GateOp.or, []⟩ = C1.gates.getD idx ⟨GateOp.or, []⟩ := by
              rw [List.getD_append _ _ _ _ (by rw [hpre_len]; exact hlt)]
              dsimp only [pre]
              rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; omega), List.getElem_take,
                  List.getD_eq_getElem _ _ (by omega)]
            rw [hgp] at hi
            have hilt : i < 11 + idx := hC1_rb idx (by omega) i hi
            dsimp only [fj]; split_ifs <;> omega
          · have hidx1 : idx + 1 < C1.gates.length := by
              have hlenC : C1.gates.length = pre.length + 1 + suf.length := by
                conv_lhs => rw [hC1_split, List.length_append, List.length_cons]
                omega
              omega
            have hgs : (pre ++ suf).getD idx ⟨GateOp.or, []⟩ = C1.gates.getD (idx + 1) ⟨GateOp.or, []⟩ := by
              rw [List.getD_append_right _ _ _ _ (by rw [hpre_len]; omega)]
              dsimp only [suf]
              have hsub : idx - pre.length < (C1.gates.drop (j + 1)).length := by
                rw [List.length_drop]; omega
              rw [List.getD_eq_getElem _ _ hsub, List.getElem_drop, List.getD_eq_getElem _ _ hidx1]
              congr 1; omega
            rw [hgs] at hi
            have hilt : i < 11 + (idx + 1) := hC1_rb (idx + 1) hidx1 i hi
            dsimp only [fj]; split_ifs <;> omega
        have hD_eval (x : Fin 10 → Bool) :
            D.eval (xs x ++ [!(xs x).getD w false]) = C1.eval (xs x) := by
          have hphase1 (gs : List Gate) (wA wB : List Bool)
              (hwA : 11 ≤ wA.length) (hwB : wB.length = wA.length + 1)
              (hlen : wA.length + gs.length ≤ 11 + j)
              (hrb : ∀ t < gs.length, ∀ i ∈ (gs.getD t ⟨GateOp.or, []⟩).inputs, i < wA.length + t)
              (hrel : ∀ i < wA.length, wB.getD (fj i) false = wA.getD i false) :
              ∀ i < wA.length + gs.length,
                (run (gs.map mapFj) wB).getD (fj i) false = (run gs wA).getD i false := by
            induction gs generalizing wA wB with
            | nil => simpa only [List.map_nil, run, List.foldl_nil, List.length_nil, Nat.add_zero] using hrel
            | cons g rest ih =>
              simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
              have hg_rb : ∀ i ∈ g.inputs, i < wA.length := by
                have h0 := hrb 0 (Nat.zero_lt_succ _)
                simpa only [List.getD_cons_zero, Nat.add_zero] using h0
              have hinp : (g.inputs.map fj).map (fun i => wB.getD i false) =
                  g.inputs.map (fun i => wA.getD i false) := by
                rw [List.map_map]; apply List.map_congr_left
                intro i hi; exact hrel i (hg_rb i hi)
              let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
              have hstepB : step wB (mapFj g) = wB ++ [b] := by dsimp only [step, mapFj, b]; rw [hinp]
              rw [hstepB]
              have hrest := ih (step wA g) (wB ++ [b])
                (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
                (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
                (by simp only [step, List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
                (by
                  intro t ht i hi
                  have h1 := hrb (t + 1) (Nat.succ_lt_succ ht) i (by simpa only [List.getD_cons_succ] using hi)
                  simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
                (by
                  intro i hi
                  simp only [step, List.length_append, List.length_cons, List.length_nil] at hi
                  dsimp only [step]
                  by_cases heq : i = wA.length
                  · subst heq
                    have hf_eq : fj wA.length = wB.length := by
                      simp only [List.length_cons] at hlen
                      dsimp only [fj]; split_ifs <;> omega
                    rw [hf_eq, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
                  · have hlt : i < wA.length := by omega
                    have hf_ne : fj i ≠ wB.length := by
                      simp only [List.length_cons] at hlen
                      dsimp only [fj]; split_ifs <;> omega
                    rw [getD_snoc_ne wB b false (fj i) hf_ne, getD_snoc_ne wA b false i heq]
                    exact hrel i hlt)
              intro i hi
              exact hrest i (by simp only [step, List.length_append, List.length_cons, List.length_nil] at hi ⊢; omega)
          let wA0 := xs x
          let wB0 := xs x ++ [!(xs x).getD w false]
          let wA1 := run pre wA0
          let wB1 := run (pre.map mapFj) wB0
          have hwA1_len : wA1.length = 11 + j := by rw [run_len, hxs_len x, hpre_len]
          have hwB1_len : wB1.length = 12 + j := by
            rw [run_len, List.length_map, hpre_len]
            simp only [wB0, List.length_append, hxs_len x, List.length_cons, List.length_nil]
          have hp1 : ∀ i < 11 + j, wB1.getD (fj i) false = wA1.getD i false := by
            have h := hphase1 pre wA0 wB0
              (by rw [hxs_len x])
              (by simp only [wA0, wB0, List.length_append, hxs_len x, List.length_cons, List.length_nil])
              (by rw [hxs_len x, hpre_len])
              (by
                intro t ht i hi
                have ht' : t < j := by rw [← hpre_len]; exact ht
                have hgp : pre.getD t ⟨GateOp.or, []⟩ = C1.gates.getD t ⟨GateOp.or, []⟩ := by
                  dsimp only [pre]
                  rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; omega), List.getElem_take,
                      List.getD_eq_getElem _ _ (by omega)]
                rw [hgp] at hi
                rw [hxs_len x]; exact hC1_rb t (by omega) i hi)
              (by
                intro i hi
                rw [hxs_len x] at hi
                have hfi : fj i = i := by simp only [fj, hi, ↓reduceIte]
                rw [hfi]
                exact List.getD_append _ _ _ _ (by rw [hxs_len x]; exact hi))
            rw [hxs_len x, hpre_len] at h
            exact h
          let wA2 := step wA1 g0
          have hwA2_len : wA2.length = 12 + j := by
            simp only [wA2, step, List.length_append, hwA1_len, List.length_cons, List.length_nil]; omega
          have hmid : ∀ i, wB1.getD (fj i) false = wA2.getD i false := by
            intro i
            by_cases hlt : i < 11 + j
            · rw [hp1 i hlt]
              dsimp only [wA2, step]
              exact (getD_snoc_ne wA1 _ false i (by omega)).symm
            · by_cases heq : i = 11 + j
              · subst heq
                have hf11 : fj (11 + j) = 11 := by
                  dsimp only [fj]
                  split_ifs <;> omega
                rw [hf11]
                have hB11 : wB1.getD 11 false = !(xs x).getD w false := by
                  rw [run_keep (pre.map mapFj) wB0 11 (by simp only [wB0, List.length_append, hxs_len x, List.length_cons, List.length_nil]; omega)]
                  have h11 : (xs x).length = 11 := hxs_len x
                  dsimp only [wB0]
                  rw [← h11]; exact getD_snoc_eq (xs x) _ false
                have hA11 : wA2.getD (11 + j) false = !(xs x).getD w false := by
                  dsimp only [wA2, step]
                  rw [← hwA1_len, getD_snoc_eq wA1 _ false]
                  cases hg0in : g0.inputs with
                  | nil => rw [hg0in] at hg0head; cases hg0head
                  | cons w' tl =>
                    rw [hg0in] at hg0head; cases hg0head
                    rw [hg0op]
                    change (!(wA1.getD w false)) = (!((xs x).getD w false))
                    rw [run_keep pre wA0 w (by rw [hxs_len x]; exact hwlt)]
                rw [hB11, hA11]
              · have hge : 12 + j ≤ i := by omega
                have hfi : fj i = i := by dsimp only [fj]; split_ifs <;> omega
                rw [hfi,
                    List.getD_eq_default wB1 false (n := i) (by omega),
                    List.getD_eq_default wA2 false (n := i) (by omega)]
          have hphase2 := remap_bijection fj (12 + j)
            (fun i hi => by dsimp only [fj]; split_ifs <;> omega)
            (fun i hi => by dsimp only [fj]; split_ifs <;> omega)
            suf wA2 wB1 (by omega) (by omega) hmid C1.output
          change (run ((pre ++ suf).map mapFj) wB0).getD (fj C1.output) false =
            (run C1.gates wA0).getD C1.output false
          rw [List.map_append, run_append, hphase2]
          conv_rhs => rw [hC1_split, run_append]
          rfl
        let permTable : List (List ℕ) :=
          [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
           [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
           [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
           [2, 1, 0, 5, 7, 3, 6, 4, 8, 9]]
        let permNat : ℕ → ℕ → ℕ := fun m i => (permTable.getD m []).getD i i
        have hperm_row_len : ∀ m : Fin 4, (permTable.getD m.val []).length = 10 := by
          dsimp only [permTable]; decide
        have hperm_lt : ∀ m : Fin 4, ∀ i : Fin 10, permNat m.val i.val < 10 := by
          dsimp only [permNat, permTable]; decide
        have hperm_ge (m : Fin 4) (i : ℕ) (hi : 10 ≤ i) : permNat m.val i = i := by
          dsimp only [permNat]
          exact List.getD_eq_default (permTable.getD m.val []) i (n := i) (by rw [hperm_row_len m]; exact hi)
        have hperm_inv_fin : ∀ m : Fin 4, ∀ i : Fin 10, permNat m.val (permNat m.val i.val) = i.val := by
          dsimp only [permNat, permTable]; decide
        let permFin : Fin 4 → Fin 10 → Fin 10 := fun m i => ⟨permNat m.val i.val, hperm_lt m i⟩
        have hpermFin_inv (m : Fin 4) (i : Fin 10) : permFin m (permFin m i) = i :=
          Fin.ext (hperm_inv_fin m i)
        have hedges10_perm : ∀ m : Fin 4, ∀ e ∈ edges10,
            (∃ e' ∈ edges10, e'.1.val = permNat m.val e.1.val ∧ e'.2.val = permNat m.val e.2.val) ∨
            (∃ e' ∈ edges10, e'.1.val = permNat m.val e.2.val ∧ e'.2.val = permNat m.val e.1.val) := by
          dsimp only [edges10, permNat, permTable]; decide
        have hp10_perm (m : Fin 4) (x : Fin 10 → Bool) : p10 (fun i => x (permFin m i)) = p10 x := by
          have hdir : ∀ (y : Fin 10 → Bool), p10 (fun i => y (permFin m i)) = true → p10 y = true := by
            intro y hy
            rw [hp10_edges (fun i => y (permFin m i))] at hy
            rw [hp10_edges y]
            rw [List.any_eq_true] at hy ⊢
            obtain ⟨e, he, hbe⟩ := hy
            rcases hedges10_perm m e he with ⟨e', he', h1, h2⟩ | ⟨e', he', h1, h2⟩
            · exact ⟨e', he', by rw [show e'.1 = permFin m e.1 from Fin.ext h1, show e'.2 = permFin m e.2 from Fin.ext h2]; exact hbe⟩
            · exact ⟨e', he', by rw [show e'.1 = permFin m e.2 from Fin.ext h1, show e'.2 = permFin m e.1 from Fin.ext h2, Bool.and_comm]; exact hbe⟩
          apply Bool.eq_iff_iff.mpr
          constructor
          · exact hdir x
          · intro hx
            have hcomp : (fun i : Fin 10 => x (permFin m (permFin m i))) = x := by
              funext i; rw [hpermFin_inv m i]
            have h2 := hdir (fun i => x (permFin m i))
            rw [hcomp] at h2; exact h2 hx
        have h02_perm_or (m : Fin 4) (x : Fin 10 → Bool) :
            (x (permFin m 0) || x (permFin m 2)) = (x 0 || x 2) := by
          have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by have := m.isLt; omega
          rcases hcases with rfl | rfl | rfl | rfl
          · rfl
          · rfl
          · exact Bool.or_comm _ _
          · exact Bool.or_comm _ _
        have hrep : ∃ m : Fin 4, permNat m.val w ∈ ([0, 1, 3, 6, 8, 10] : List ℕ) := by
          have hfin : ∀ k : Fin 11, ∃ m : Fin 4, permNat m.val k.val ∈ ([0, 1, 3, 6, 8, 10] : List ℕ) := by
            dsimp only [permNat, permTable]; decide
          exact hfin ⟨w, hwlt⟩
        obtain ⟨m, hwm⟩ := hrep
        let D' : Circuit := ⟨D.gates.map (fun g => Gate.mk g.op (g.inputs.map (permNat m.val))), permNat m.val D.output⟩
        have hD'fan : FanInTwo D' := by
          intro g hg; simp only [D', List.mem_map] at hg
          obtain ⟨g', hg', rfl⟩ := hg; have hf := hD_fan g' hg'
          exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
        have hD'sz : D'.size ≤ 17 := by
          change (D.gates.map _).length ≤ 17; rw [List.length_map]; exact hD_sz
        have hD'not : notCount D' = notCount D := hMap_notCount (permNat m.val) D.gates
        have hD'rb : ReadsBack 12 D' := by
          intro idx hidx u hu
          change idx < (D.gates.map _).length at hidx; rw [List.length_map] at hidx
          have hget : D'.gates.getD idx ⟨GateOp.or, []⟩ =
              Gate.mk (D.gates.getD idx ⟨GateOp.or, []⟩).op ((D.gates.getD idx ⟨GateOp.or, []⟩).inputs.map (permNat m.val)) := by
            dsimp only [D']
            rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hidx), List.getElem_map,
                List.getD_eq_getElem _ _ hidx]
          change u ∈ (D'.gates.getD idx ⟨GateOp.or, []⟩).inputs at hu
          rw [hget] at hu; simp only [List.mem_map] at hu
          obtain ⟨i, hi, rfl⟩ := hu
          have hilt : i < 12 + idx := hD_rb idx hidx i hi
          by_cases hi10 : i < 10
          · have hpi : permNat m.val i < 10 := hperm_lt m ⟨i, hi10⟩; omega
          · rw [hperm_ge m i (by omega)]; exact hilt
        have hD'eval (x : Fin 10 → Bool) :
            D'.eval (xs x ++ [!(xs x).getD (permNat m.val w) false]) =
              D.eval (xs (fun i => x (permFin m i)) ++ [!(xs (fun i => x (permFin m i))).getD w false]) := by
          let y : Fin 10 → Bool := fun i => x (permFin m i)
          let wA := xs y ++ [!(xs y).getD w false]
          let wB := xs x ++ [!(xs x).getD (permNat m.val w) false]
          have hrel : ∀ i, wB.getD (permNat m.val i) false = wA.getD i false := by
            intro i
            by_cases hi10 : i < 10
            · have hpi : permNat m.val i < 10 := hperm_lt m ⟨i, hi10⟩
              dsimp only [wA, wB]
              rw [List.getD_append (xs x) _ _ _ (by rw [hxs_len x]; omega),
                  List.getD_append (xs y) _ _ _ (by rw [hxs_len y]; omega)]
              have h1 := hxs_read x ⟨permNat m.val i, hpi⟩
              have h2 := hxs_read y ⟨i, hi10⟩
              rw [h1, h2]
            · by_cases hi_eq10 : i = 10
              · subst hi_eq10
                rw [hperm_ge m 10 (by omega)]
                dsimp only [wA, wB]
                rw [List.getD_append (xs x) _ _ _ (by rw [hxs_len x]; omega),
                    List.getD_append (xs y) _ _ _ (by rw [hxs_len y]; omega),
                    hxs_read10 x, hxs_read10 y]
                exact (h02_perm_or m x).symm
              · by_cases hi_eq11 : i = 11
                · subst hi_eq11
                  rw [hperm_ge m 11 (by omega)]
                  dsimp only [wA, wB]
                  rw [show 11 = (xs x).length from (hxs_len x).symm, getD_snoc_eq (xs x) _ false,
                      show (xs x).length = (xs y).length from (hxs_len x).trans (hxs_len y).symm,
                      getD_snoc_eq (xs y) _ false]
                  congr 1
                  by_cases hw10 : w < 10
                  · have hpw := hperm_lt m ⟨w, hw10⟩
                    have h1 := hxs_read x ⟨permNat m.val w, hpw⟩
                    have h2 := hxs_read y ⟨w, hw10⟩
                    rw [h1, h2]
                  · have hw10e : w = 10 := by omega
                    subst hw10e
                    rw [hperm_ge m 10 (by omega), hxs_read10 x, hxs_read10 y]
                    exact (h02_perm_or m x).symm
                · rw [hperm_ge m i (by omega),
                      List.getD_eq_default wB false (n := i) (by simp only [wB, List.length_append, hxs_len x, List.length_cons, List.length_nil]; omega),
                      List.getD_eq_default wA false (n := i) (by simp only [wA, List.length_append, hxs_len y, List.length_cons, List.length_nil]; omega)]
          exact remap_bijection (permNat m.val) 10 (fun i hi => hperm_lt m ⟨i, hi⟩) (hperm_ge m)
            D.gates wA wB
            (by simp only [wA, wB, List.length_append, hxs_len y, hxs_len x, List.length_cons, List.length_nil])
            (by simp only [wA, List.length_append, hxs_len y, List.length_cons, List.length_nil]; omega)
            hrel D.output
        by_cases hC1n1 : notCount C1 = 1
        · have hD'n0 : notCount D' = 0 := by omega
          obtain ⟨x, hx⟩ := hNot1RawOrMono (permNat m.val w) hwm D' (hMono_of_not0 D' hD'fan hD'n0) hD'rb hD'sz
          refine ⟨fun i => x (permFin m i), ?_⟩
          rw [← hD_eval (fun i => x (permFin m i)), ← hD'eval x, hp10_perm m x]
          exact hx
        · have hD'n1 : notCount D' = 1 := by omega
          obtain ⟨x, hx⟩ := hNot2RawSlide (permNat m.val w) hwm D' hD'fan hD'rb hD'sz hD'n1
          refine ⟨fun i => x (permFin m i), ?_⟩
          rw [← hD_eval (fun i => x (permFin m i)), ← hD'eval x, hp10_perm m x]
          exact hx
      · have hAllNotGe11 : ∀ g ∈ C1.gates, g.op = GateOp.not → ∃ w, g.inputs.head? = some w ∧ 11 ≤ w := by
          intro g hg hgop
          obtain ⟨w, hw⟩ := hAllNotNonempty g hg hgop
          refine ⟨w, hw, ?_⟩
          by_contra hlt
          obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hg
          have hget? : C1.gates[j]? = some g := by rw [List.getElem?_eq_getElem hj, hget]
          exact hRawNot ⟨j, hj, g, w, hget?, hgop, hw, by omega⟩
        by_cases hC1n1 : notCount C1 = 1
        · have hex_not : ∃ g ∈ C1.gates, g.op = GateOp.not := by
            have hpos : 0 < (C1.gates.filter isNot).length := by change 0 < notCount C1; omega
            cases hf : C1.gates.filter isNot with
            | nil => rw [hf] at hpos; cases hpos
            | cons g _ =>
              have hmem : g ∈ C1.gates.filter isNot := by rw [hf]; exact List.mem_cons_self
              obtain ⟨hg, hgn⟩ := List.mem_filter.mp hmem
              exact ⟨g, hg, (hisNot_iff g).mp hgn⟩
          obtain ⟨g0, hg0mem, hg0op⟩ := hex_not
          obtain ⟨j, hj, hgetj⟩ := List.getElem_of_mem hg0mem
          have hgetj? : C1.gates[j]? = some g0 := by rw [List.getElem?_eq_getElem hj, hgetj]
          obtain ⟨w, hwhead, hw11⟩ := hAllNotGe11 g0 hg0mem hg0op
          by_cases hjlt : j < C1.size - 1
          · exact hNot1Internal C1 hC1_fan hC1_rb hC1_sz_le hC1_out hC1n1 ⟨j, hjlt, g0, w, hgetj?, hg0op, hwhead, hw11⟩
          · have hjeq : j + 1 = C1.gates.length := by
              change ¬j < C1.gates.length - 1 at hjlt; omega
            let pre : List Gate := C1.gates.take j
            have hpre_len : pre.length = j := by dsimp only [pre]; rw [List.length_take]; omega
            have hC1_snoc : C1.gates = pre ++ [g0] := by
              have hdrop : C1.gates.drop j = [g0] := by
                rw [List.drop_eq_getElem_cons hj, hgetj, List.drop_eq_nil_of_le (by omega)]
              rw [← hdrop]; exact (List.take_append_drop j C1.gates).symm
            have hpre_mono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
              intro g hg
              have hpre_n0 : (pre.filter isNot).length = 0 := by
                have h1 : (C1.gates.filter isNot).length = 1 := hC1n1
                rw [hC1_snoc, List.filter_append, List.filter_cons, List.filter_nil,
                    (hisNot_iff g0).mpr hg0op] at h1
                simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil] at h1
                omega
              have hne : g.op ≠ GateOp.not := by
                intro heq
                have hmem : g ∈ pre.filter isNot := List.mem_filter.mpr ⟨hg, (hisNot_iff g).mpr heq⟩
                have hpos := List.length_pos_of_mem hmem
                omega
              have hf := hC1_fan g (by rw [hC1_snoc]; exact List.mem_append_left _ hg)
              rcases hf.1 with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact absurd h hne
            have hmono_run (gs : List Gate) (hgm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
                (wA wB : List Bool) (hlen : wA.length = wB.length)
                (hle : ∀ i, wA.getD i false = true → wB.getD i false = true) :
                ∀ i, (run gs wA).getD i false = true → (run gs wB).getD i false = true := by
              induction gs generalizing wA wB with
              | nil => exact hle
              | cons g rest ih =>
                simp only [run, List.foldl_cons] at ih ⊢
                apply ih (fun g' hg' => hgm g' (List.mem_cons_of_mem g hg')) (step wA g) (step wB g)
                · simp only [step, List.length_append, hlen, List.length_cons, List.length_nil]
                · intro i hi
                  dsimp only [step] at hi ⊢
                  by_cases heq : i = wA.length
                  · subst heq
                    rw [getD_snoc_eq wA _ false] at hi
                    rw [hlen, getD_snoc_eq wB _ false]
                    rcases hgm g List.mem_cons_self with hop | hop
                    · rw [hop] at hi ⊢
                      change (g.inputs.map fun u => wA.getD u false).all id = true at hi
                      change (g.inputs.map fun u => wB.getD u false).all id = true
                      rw [List.all_eq_true] at hi ⊢
                      intro b hb; simp only [List.mem_map] at hb
                      obtain ⟨u, hu, rfl⟩ := hb
                      exact hle u (hi (wA.getD u false) (List.mem_map.mpr ⟨u, hu, rfl⟩))
                    · rw [hop] at hi ⊢
                      change (g.inputs.map fun u => wA.getD u false).any id = true at hi
                      change (g.inputs.map fun u => wB.getD u false).any id = true
                      rw [List.any_eq_true] at hi ⊢
                      obtain ⟨b, hb, hbt⟩ := hi
                      simp only [List.mem_map] at hb
                      obtain ⟨u, hu, rfl⟩ := hb
                      exact ⟨wB.getD u false, List.mem_map.mpr ⟨u, hu, rfl⟩, hle u hbt⟩
                  · have heq2 : i ≠ wB.length := by rw [← hlen]; exact heq
                    rw [getD_snoc_ne wA _ false i heq] at hi
                    rw [getD_snoc_ne wB _ false i heq2]
                    exact hle i hi
            let x0 : Fin 10 → Bool := fun _ => false
            let x1 : Fin 10 → Bool := fun _ => true
            have hp0 : p10 x0 = false := by decide
            have hp1 : p10 x1 = true := by decide
            have hle01 : ∀ i, (xs x0).getD i false = true → (xs x1).getD i false = true := by
              intro i hi
              by_cases hi10 : i < 10
              · have h := hxs_read x0 ⟨i, hi10⟩
                rw [h] at hi; cases hi
              · by_cases hi_eq10 : i = 10
                · subst hi_eq10; rw [hxs_read10 x0] at hi; cases hi
                · rw [List.getD_eq_default (xs x0) false (n := i) (by rw [hxs_len x0]; omega)] at hi
                  cases hi
            have heval_not (x : Fin 10 → Bool) : C1.eval (xs x) = !((run pre (xs x)).getD w false) := by
              change (run C1.gates (xs x)).getD C1.output false = _
              rw [hC1_snoc, run_append]
              have hout_eq : C1.output = (run pre (xs x)).length := by
                rw [run_len, hxs_len x, hpre_len]
                have h := hC1_out
                change C1.output = 10 + C1.gates.length at h
                omega
              rw [hout_eq]
              change (step (run pre (xs x)) g0).getD (run pre (xs x)).length false = _
              dsimp only [step]
              rw [getD_snoc_eq (run pre (xs x)) _ false]
              cases hg0in : g0.inputs with
              | nil => rw [hg0in] at hwhead; cases hwhead
              | cons w' tl =>
                rw [hg0in] at hwhead; cases hwhead
                rw [hg0op]; rfl
            by_cases hc0 : C1.eval (xs x0) = false
            · refine ⟨x1, ?_⟩
              rw [hp1, heval_not x1]
              rw [heval_not x0] at hc0
              have hw0t : (run pre (xs x0)).getD w false = true := by
                cases hv : (run pre (xs x0)).getD w false
                · rw [hv] at hc0; cases hc0
                · rfl
              have hw1t : (run pre (xs x1)).getD w false = true :=
                hmono_run pre hpre_mono (xs x0) (xs x1) ((hxs_len x0).trans (hxs_len x1).symm) hle01 w hw0t
              rw [hw1t]; decide
            · exact ⟨x0, by rw [hp0]; exact hc0⟩
        · have hC1n2 : notCount C1 = 2 := by omega
          exact hNot2Internal C1 hC1_fan hC1_rb hC1_sz_le hC1_out hC1n2 hAllNotGe11
