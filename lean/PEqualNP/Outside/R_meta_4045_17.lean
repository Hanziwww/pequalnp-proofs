import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_4045_17
    (hCleanUncovered :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 C →
        C.size ≤ 62 →
        (∀ j < C.size, PEqualNP.ReadTwo.in0 C j ≠ PEqualNP.ReadTwo.in1 C j) →
        (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C x =
          decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) →
        (∀ v : Fin 26,
          ((Finset.range C.size).filter (fun k =>
            ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.contains v.val ||
             (List.range C.size).any (fun j =>
               (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [] &&
               (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.contains v.val &&
               (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.contains (26 + j))) = true)).card ≤ 4) →
        (∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
            PEqualNP.ReadTwo.orp C 26 (26 + j) C.output ∧
            PEqualNP.ReadTwo.orp C 26 p.val a ∧
            PEqualNP.ReadTwo.orp C 26 (13 + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd C j →
          ∀ x : Fin 26 → Bool,
            PEqualNP.MetaComplexity.circuitFun 26 C x = false →
            PEqualNP.ReadTwo.wval C x (26 + j) = false) →
        False)
    (hDirtyOneHot :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 C →
        C.size ≤ 62 →
        (∀ j < C.size, PEqualNP.ReadTwo.in0 C j ≠ PEqualNP.ReadTwo.in1 C j) →
        (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C x =
          decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) →
        (∀ v : Fin 26,
          ((Finset.range C.size).filter (fun k =>
            ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.contains v.val ||
             (List.range C.size).any (fun j =>
               (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [] &&
               (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.contains v.val &&
               (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.contains (26 + j))) = true)).card ≤ 4) →
        (∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
            PEqualNP.ReadTwo.orp C 26 (26 + j) C.output ∧
            PEqualNP.ReadTwo.orp C 26 p.val a ∧
            PEqualNP.ReadTwo.orp C 26 (13 + l.val) b) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd C j ∧
          ∃ v : Fin 26, PEqualNP.ReadTwo.wval C (fun i => decide (i = v)) (26 + j) = true) →
        False)
    (hDirtyNoOneHot :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 26 C →
        C.size ≤ 62 →
        (∀ j < C.size, PEqualNP.ReadTwo.in0 C j ≠ PEqualNP.ReadTwo.in1 C j) →
        (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C x =
          decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) →
        (∀ v : Fin 26,
          ((Finset.range C.size).filter (fun k =>
            ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.contains v.val ||
             (List.range C.size).any (fun j =>
               (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [] &&
               (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.contains v.val &&
               (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.contains (26 + j))) = true)).card ≤ 4) →
        (∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
            PEqualNP.ReadTwo.orp C 26 (26 + j) C.output ∧
            PEqualNP.ReadTwo.orp C 26 p.val a ∧
            PEqualNP.ReadTwo.orp C 26 (13 + l.val) b) →
        (∀ j : ℕ, PEqualNP.ReadTwo.isAnd C j →
          ∀ v : Fin 26, PEqualNP.ReadTwo.wval C (fun i => decide (i = v)) (26 + j) = false) →
        (∃ j : ℕ, PEqualNP.ReadTwo.isAnd C j ∧
          ∃ x : Fin 26 → Bool,
            PEqualNP.MetaComplexity.circuitFun 26 C x = false ∧
            PEqualNP.ReadTwo.wval C x (26 + j) = true) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate),
        x1.gates[x3]? = Option.some x4 →
        (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) →
      x1.size ≤ (62 : ℕ) →
      (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) →
      (∀ (x6 : Fin (26 : ℕ) → Bool),
        x2 x6 x1.output = Bool.true ↔
          ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧
              x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ),
        (5 : ℕ) ≤ x8.card ∧
          ∀ x9 ∈ x8,
            x9 < x1.size ∧
              ∃ (x11 : Bool) (x12 : Bool),
                ∃ x13 < (26 : ℕ) + x9,
                  ∀ (x14 : Fin (26 : ℕ) → Bool),
                    x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  intro C x2 hstrict hCsize hx2 hout
  let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  have hgate_some : ∀ j < C.gates.length, C.gates[j]? = some (gateAt C j) := by
    intro j hj
    change C.gates[j]? = some (C.gates.getD j ⟨GateOp.or, []⟩)
    rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  have hCAO2 : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_iff_getElem] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hs := hstrict j C.gates[j] (List.getElem?_eq_getElem hj)
      exact hs.1
    · intro j hj i hi
      obtain ⟨_, a, b, hab, _, ha, hb⟩ := hstrict j (gateAt C j) (hgate_some j hj)
      rw [hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      rw [List.mem_iff_getElem] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      obtain ⟨_, a, b, hab, _, _, _⟩ := hstrict j C.gates[j] (List.getElem?_eq_getElem hj)
      rw [hab]; rfl
  have hdist : ∀ j < C.size, PEqualNP.ReadTwo.in0 C j ≠ PEqualNP.ReadTwo.in1 C j := by
    intro j hj
    have hj' : j < C.gates.length := hj
    obtain ⟨_, a, b, hab, hne, _, _⟩ := hstrict j (gateAt C j) (hgate_some j hj')
    have h0 : PEqualNP.ReadTwo.in0 C j = a := by change (gateAt C j).inputs.getD 0 0 = a; rw [hab]; rfl
    have h1 : PEqualNP.ReadTwo.in1 C j = b := by change (gateAt C j).inputs.getD 1 0 = b; rw [hab]; rfl
    rw [h0, h1]; exact hne
  have hC_exact : ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C x =
      decide (∃ (p l : Fin 13), I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    have hx2out : x2 x C.output = PEqualNP.MetaComplexity.circuitFun 26 C x := hx2 x C.output
    rw [← hx2out]
    exact hout x
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
  have hRB : ReadsBack 26 C := hCAO2.2.1
  have wireVal_input (i : Fin 26) (x : Fin 26 → Bool) :
      wireVal 26 C i.val x = x i := by
    change (run C.gates (List.ofFn x)).getD i.val false = x i
    rw [run_keep C.gates (List.ofFn x) i.val (by simp [i.isLt])]
    rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
  have wireVal_gate (k : ℕ) (hk : k < C.gates.length) (x : Fin 26 → Bool) :
      wireVal 26 C (26 + k) x =
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireVal 26 C i x) := by
    change (run C.gates (List.ofFn x)).getD (26 + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (run C.gates (List.ofFn x)).getD i false)
    have hsplit : C.gates = C.gates.take k ++ [gateAt C k] ++ C.gates.drop (k + 1) := by
      have h1 : C.gates = C.gates.take (k + 1) ++ C.gates.drop (k + 1) :=
        (List.take_append_drop (k + 1) C.gates).symm
      conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk]
      rfl
    let w0 := run (C.gates.take k) (List.ofFn x)
    have hw0_len : w0.length = 26 + k := by
      dsimp only [w0]; rw [run_len, List.length_ofFn, List.length_take]; omega
    have hw_lt : ∀ i < 26 + k, (run C.gates (List.ofFn x)).getD i false = w0.getD i false := by
      intro i hi
      conv_lhs => rw [← List.take_append_drop k C.gates]
      have hfold : run (C.gates.take k ++ C.gates.drop k) (List.ofFn x) = run (C.gates.drop k) w0 := by
        dsimp only [run, w0]; exact List.foldl_append
      rw [hfold]
      exact run_keep (C.gates.drop k) w0 i (by omega)
    have hrun_split : run C.gates (List.ofFn x) = run (C.gates.drop (k + 1)) (step w0 (gateAt C k)) := by
      have h1 : run C.gates (List.ofFn x) = run (C.gates.take k ++ [gateAt C k] ++ C.gates.drop (k + 1)) (List.ofFn x) :=
        congrArg (fun gs => run gs (List.ofFn x)) hsplit
      rw [h1]
      dsimp only [run, w0]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv_lhs => rw [hrun_split]
    rw [run_keep _ _ (26 + k) (by simp only [step, List.length_append, hw0_len, List.length_cons, List.length_nil]; omega)]
    dsimp only [step]
    rw [show 26 + k = w0.length from hw0_len.symm, getD_snoc_eq w0 _ false]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact (hw_lt i (hRB k hk i hi)).symm
  have wireVal_and_pair {k a b : ℕ} (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
      (hin : (gateAt C k).inputs = [a, b]) (x : Fin 26 → Bool) :
      wireVal 26 C (26 + k) x = (wireVal 26 C a x && wireVal 26 C b x) := by
    rw [wireVal_gate k hk x, hand, hin]
    change [wireVal 26 C a x, wireVal 26 C b x].all id = (wireVal 26 C a x && wireVal 26 C b x)
    simp
  have wireVal_or_pair {k a b : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
      (hin : (gateAt C k).inputs = [a, b]) (x : Fin 26 → Bool) :
      wireVal 26 C (26 + k) x = (wireVal 26 C a x || wireVal 26 C b x) := by
    rw [wireVal_gate k hk x, hor, hin]
    change [wireVal 26 C a x, wireVal 26 C b x].any id = (wireVal 26 C a x || wireVal 26 C b x)
    simp
  have wireVal_or_mem {k a : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
      (ha : a ∈ (gateAt C k).inputs) (x : Fin 26 → Bool)
      (hva : wireVal 26 C a x = true) :
      wireVal 26 C (26 + k) x = true := by
    rw [wireVal_gate k hk x, hor]
    change ((gateAt C k).inputs.map fun i => wireVal 26 C i x).any id = true
    rw [List.any_eq_true]
    exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
  let S : Fin 26 → Finset ℕ := fun v =>
    (Finset.range C.size).filter (fun k =>
      ((gateAt C k).inputs.contains v.val ||
       (List.range C.size).any (fun j =>
         (gateAt C j).op.eval [] &&
         (gateAt C j).inputs.contains v.val &&
         (gateAt C k).inputs.contains (26 + j))) = true)
  by_cases hS5 : ∃ v : Fin 26, 5 ≤ (S v).card
  · obtain ⟨v, hv5⟩ := hS5
    refine ⟨v, S v, hv5, ?_⟩
    intro k hkS
    obtain ⟨hk_ran, hk_cond⟩ := Finset.mem_filter.mp hkS
    have hk_lt : k < C.size := Finset.mem_range.mp hk_ran
    have hk_glen : k < C.gates.length := hk_lt
    refine ⟨hk_lt, ?_⟩
    obtain ⟨hop, a, b, hab, _, ha_lt, hb_lt⟩ := hstrict k (gateAt C k) (hgate_some k hk_glen)
    have hz_ex : ∃ z, (z = a ∨ z = b) ∧ ∀ x : Fin 26 → Bool, x v = false → wireVal 26 C z x = false := by
      rw [Bool.or_eq_true] at hk_cond
      rcases hk_cond with hdir | hind
      · rw [List.contains_eq_mem, decide_eq_true_eq, hab] at hdir
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hdir
        refine ⟨v.val, hdir, ?_⟩
        intro x hxv
        rw [wireVal_input v x, hxv]
      · rw [List.any_eq_true] at hind
        obtain ⟨j, hj_ran, hj_cond⟩ := hind
        have hj_lt : j < C.gates.length := List.mem_range.mp hj_ran
        simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hj_cond
        obtain ⟨⟨hj_op_ev, hj_in_v⟩, hk_in_j⟩ := hj_cond
        obtain ⟨hj_op, a', b', hab', _, _, _⟩ := hstrict j (gateAt C j) (hgate_some j hj_lt)
        have hj_and : (gateAt C j).op = GateOp.and := by
          rcases hj_op with h | h
          · exact h
          · rw [h] at hj_op_ev; cases hj_op_ev
        rw [hab] at hk_in_j
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_in_j
        refine ⟨26 + j, hk_in_j, ?_⟩
        intro x hxv
        rw [wireVal_and_pair hj_lt hj_and hab' x]
        rw [hab'] at hj_in_v
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_in_v
        rcases hj_in_v with rfl | rfl
        · rw [wireVal_input v x, hxv]; rfl
        · rw [wireVal_input v x, hxv, Bool.and_false]
    obtain ⟨z, hz_ab, hz_zero⟩ := hz_ex
    rcases hz_ab with rfl | rfl
    · rcases hop with hand | hor
      · refine ⟨false, false, b, hb_lt, ?_⟩
        intro x hxv
        rw [hx2 x (26 + k), hx2 x b]
        change wireVal 26 C (26 + k) x = (false && wireVal 26 C b x || false)
        rw [wireVal_and_pair hk_glen hand hab x, hz_zero x hxv]
        rfl
      · refine ⟨true, false, b, hb_lt, ?_⟩
        intro x hxv
        rw [hx2 x (26 + k), hx2 x b]
        change wireVal 26 C (26 + k) x = (true && wireVal 26 C b x || false)
        rw [wireVal_or_pair hk_glen hor hab x, hz_zero x hxv]
        simp
    · rcases hop with hand | hor
      · refine ⟨false, false, a, ha_lt, ?_⟩
        intro x hxv
        rw [hx2 x (26 + k), hx2 x a]
        change wireVal 26 C (26 + k) x = (false && wireVal 26 C a x || false)
        rw [wireVal_and_pair hk_glen hand hab x, hz_zero x hxv]
        simp
      · refine ⟨true, false, a, ha_lt, ?_⟩
        intro x hxv
        rw [hx2 x (26 + k), hx2 x a]
        change wireVal 26 C (26 + k) x = (true && wireVal 26 C a x || false)
        rw [wireVal_or_pair hk_glen hor hab x, hz_zero x hxv]
        simp
  · exfalso
    have hSle4 : ∀ v : Fin 26, (S v).card ≤ 4 := by
      intro v
      by_contra hgt
      exact hS5 ⟨v, by omega⟩
    by_cases hall : ∀ (p l : Fin 13), I p l →
        ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
          PEqualNP.ReadTwo.orp C 26 (26 + j) C.output ∧
          PEqualNP.ReadTwo.orp C 26 p.val a ∧
          PEqualNP.ReadTwo.orp C 26 (13 + l.val) b
    · have hNoC4 : ∀ (p1 p2 l1 l2 : Fin 13), p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
        have hdiff : ∀ a ∈ ([0, 1, 3, 9] : List (Fin 13)), ∀ b ∈ ([0, 1, 3, 9] : List (Fin 13)),
            ∀ c ∈ ([0, 1, 3, 9] : List (Fin 13)), ∀ d ∈ ([0, 1, 3, 9] : List (Fin 13)),
            a ≠ b → a ≠ c → a + d ≠ b + c := by decide
        have hI_mem (p l : Fin 13) (h : I p l) : p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rcases h with rfl | rfl | rfl | rfl
          · exact Or.inl (sub_self _)
          · exact Or.inr (Or.inl (add_sub_cancel_left _ _))
          · exact Or.inr (Or.inr (Or.inl (add_sub_cancel_left _ _)))
          · exact Or.inr (Or.inr (Or.inr (add_sub_cancel_left _ _)))
        intro p1 p2 l1 l2 hp hl h
        obtain ⟨h11, h12, h21, h22⟩ := h
        apply hdiff (p1 - l1) (hI_mem p1 l1 h11) (p1 - l2) (hI_mem p1 l2 h12)
          (p2 - l1) (hI_mem p2 l1 h21) (p2 - l2) (hI_mem p2 l2 h22)
        · intro heq
          have h := congrArg (fun z => p1 - z) heq
          simp only [sub_sub_cancel] at h
          exact hl h
        · intro heq; exact hp (by simpa only [sub_add_cancel] using congrArg (· + l1) heq)
        · abel
      have hidx : ∀ i j : Fin 4, ([0, 1, 3, 9] : List (Fin 13)).getD i.val 0 =
          ([0, 1, 3, 9] : List (Fin 13)).getD j.val 0 → i = j := by decide
      classical
      let E : Finset (Fin 13 × Fin 13) := PEqualNP.ReadTwo.incid I
      have hmem_E (p l : Fin 13) : (p, l) ∈ E ↔ I p l := by
        change (p, l) ∈ @Finset.filter (Fin 13 × Fin 13) (fun e => I e.1 e.2) (Classical.decPred _) Finset.univ ↔ I p l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hE_card : E.card = 52 := by
        let f : Fin 13 × Fin 4 → Fin 13 × Fin 13 := fun q =>
          (q.1 + ([0, 1, 3, 9] : List (Fin 13)).getD q.2.val 0, q.1)
        have hf_inj : Function.Injective f := by
          intro a b h
          have h2 : a.1 = b.1 := congrArg Prod.snd h
          have h1 : a.1 + ([0, 1, 3, 9] : List (Fin 13)).getD a.2.val 0 =
              b.1 + ([0, 1, 3, 9] : List (Fin 13)).getD b.2.val 0 := congrArg Prod.fst h
          rw [h2] at h1
          have hd := add_left_cancel h1
          exact Prod.ext h2 (hidx a.2 b.2 hd)
        have hE_eq : E = Finset.univ.image f := by
          ext e
          obtain ⟨p, l⟩ := e
          rw [hmem_E p l, Finset.mem_image]
          constructor
          · intro hpl
            rcases hpl with rfl | rfl | rfl | rfl
            · exact ⟨(p, 0), Finset.mem_univ _, by simp [f]⟩
            · exact ⟨(l, 1), Finset.mem_univ _, by simp [f]⟩
            · exact ⟨(l, 2), Finset.mem_univ _, by simp [f]⟩
            · exact ⟨(l, 3), Finset.mem_univ _, by simp [f]⟩
          · rintro ⟨⟨l0, k⟩, _, heq⟩
            have hl : l0 = l := congrArg Prod.snd heq
            have hp : l0 + ([0, 1, 3, 9] : List (Fin 13)).getD k.val 0 = p := congrArg Prod.fst heq
            subst hl; subst hp
            have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by have := k.isLt; omega
            rcases hk with rfl | rfl | rfl | rfl
            · exact Or.inl (by change l0 + 0 = l0; exact add_zero l0)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
        rw [hE_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      let OrPath : ℕ → ℕ → Prop := fun w target =>
        ∀ Q : ℕ → Prop,
          Q target →
          (∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
            ∀ a ∈ (gateAt C k).inputs, Q a → Q (26 + k)) →
          Q w
      have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
      have orPath_step {k a t : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
          (ha : a ∈ (gateAt C k).inputs) (hp : OrPath a t) : OrPath (26 + k) t :=
        fun Q ht hs => hs k hk hor a ha (hp Q ht hs)
      have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
        fun Q hw hs => huv Q (hvw Q hw hs) hs
      have orPath_cases {w t : ℕ} (h : OrPath w t) :
          w = t ∨ ∃ k < C.gates.length, w = 26 + k ∧ (gateAt C k).op = GateOp.or ∧
            ∃ a ∈ (gateAt C k).inputs, OrPath a t := by
        apply h (fun x => x = t ∨ ∃ k < C.gates.length, x = 26 + k ∧ (gateAt C k).op = GateOp.or ∧
            ∃ a ∈ (gateAt C k).inputs, OrPath a t)
        · exact Or.inl rfl
        · intro k hk hor a ha hPa
          refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
          rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
          · exact orPath_refl _
          · exact orPath_step hk' hor' ha' hp'
      have orPath_parent {w t : ℕ} (h : OrPath w t) (hne : w ≠ t) :
          ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
            OrPath w (26 + y) ∧ t ∈ (gateAt C y).inputs := by
        have hdisj : w = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
            OrPath w (26 + y) ∧ t ∈ (gateAt C y).inputs := by
          apply h (fun x => x = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
              OrPath x (26 + y) ∧ t ∈ (gateAt C y).inputs)
          · exact Or.inl rfl
          · intro k hk hor a ha hPa
            rcases hPa with rfl | ⟨y, hy, hory, hpy, hty⟩
            · exact Or.inr ⟨k, hk, hor, orPath_refl (26 + k), ha⟩
            · exact Or.inr ⟨y, hy, hory, orPath_step hk hor ha hpy, hty⟩
        rcases hdisj with heq | hex
        · exact (hne heq).elim
        · exact hex
      have orp_to_orPath {t w : ℕ} (h : PEqualNP.ReadTwo.orp C 26 t w) : OrPath w t := by
        change Relation.ReflTransGen (fun a b => a < b ∧ ∃ j, b = 26 + j ∧ isOr C j ∧ a ∈ (gateAt C j).inputs) t w at h
        induction h with
        | refl => exact orPath_refl t
        | tail _ hstep ih =>
          obtain ⟨_, j, rfl, ⟨hj, hor⟩, ha⟩ := hstep
          exact orPath_step hj hor ha ih
      have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin 26 → Bool)
          (ht : wireVal 26 C t x = true) : wireVal 26 C w x = true := by
        apply hp (fun u => wireVal 26 C u x = true) ht
        intro k hk hor a ha hva
        exact wireVal_or_mem hk hor ha x hva
      have isAO2_gate_inputs {k : ℕ} (hk : k < C.gates.length) :
          ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a < 26 + k ∧ b < 26 + k := by
        obtain ⟨_, a, b, hab, _, ha, hb⟩ := hstrict k (gateAt C k) (hgate_some k hk)
        exact ⟨a, b, hab, ha, hb⟩
      let mergeStep : ∀ {α : Type} [DecidableEq α], Finset (Finset α) → α → α → Finset (Finset α) :=
        fun P u v =>
          let hit := P.filter (fun B => u ∈ B ∨ v ∈ B)
          let rest := P.filter (fun B => ¬ (u ∈ B ∨ v ∈ B))
          if hit.Nonempty then insert (hit.biUnion id) rest else P
      let IsPartition : ∀ {α : Type} [DecidableEq α], Finset α → Finset (Finset α) → Prop :=
        fun U P =>
          (∀ B ∈ P, B.Nonempty) ∧
          (∀ B1 ∈ P, ∀ B2 ∈ P, B1 ≠ B2 → Disjoint B1 B2) ∧
          P.biUnion id = U
      have partition_unique_block {α : Type} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
          (hP : IsPartition U P) {x : α} {B1 B2 : Finset α}
          (h1 : B1 ∈ P) (h2 : B2 ∈ P) (hx1 : x ∈ B1) (hx2 : x ∈ B2) : B1 = B2 := by
        by_contra hne
        exact Finset.disjoint_left.mp (hP.2.1 B1 h1 B2 h2 hne) hx1 hx2
      have partition_exists_block {α : Type} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
          (hP : IsPartition U P) {x : α} (hx : x ∈ U) : ∃ B ∈ P, x ∈ B := by
        rw [← hP.2.2, Finset.mem_biUnion] at hx
        obtain ⟨B, hB, hxB⟩ := hx
        exact ⟨B, hB, hxB⟩
      have mergeStep_props {α : Type} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
          (hP : IsPartition U P) {u v : α} (hu : u ∈ U) (hv : v ∈ U) :
          IsPartition U (mergeStep P u v) ∧
          P.card ≤ (mergeStep P u v).card + 1 ∧
          (∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B) ∧
          (∃ B ∈ mergeStep P u v, u ∈ B ∧ v ∈ B) := by
        obtain ⟨Bu, hBuP, huBu⟩ := partition_exists_block hP hu
        obtain ⟨Bv, hBvP, hvBv⟩ := partition_exists_block hP hv
        let hit := P.filter (fun B => u ∈ B ∨ v ∈ B)
        let rest := P.filter (fun B => ¬ (u ∈ B ∨ v ∈ B))
        have hBu_hit : Bu ∈ hit := Finset.mem_filter.mpr ⟨hBuP, Or.inl huBu⟩
        have hBv_hit : Bv ∈ hit := Finset.mem_filter.mpr ⟨hBvP, Or.inr hvBv⟩
        have hhit_ne : hit.Nonempty := ⟨Bu, hBu_hit⟩
        have hhit_sub : hit ⊆ {Bu, Bv} := by
          intro B hB
          obtain ⟨hBP, hor⟩ := Finset.mem_filter.mp hB
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hor with huB | hvB
          · exact Or.inl (partition_unique_block hP hBP hBuP huB huBu)
          · exact Or.inr (partition_unique_block hP hBP hBvP hvB hvBv)
        have hhit_card : hit.card ≤ 2 :=
          (Finset.card_le_card hhit_sub).trans Finset.card_le_two
        have hmerge_eq : mergeStep P u v = insert (hit.biUnion id) rest := by
          dsimp only [mergeStep]
          simp only [hit, rest, hhit_ne, ↓reduceIte]
        have hnot_mem_rest : hit.biUnion id ∉ rest := by
          intro hmem
          have hno := (Finset.mem_filter.mp hmem).2
          apply hno
          exact Or.inl (Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩)
        have hdisj_hr : Disjoint hit rest := by
          rw [Finset.disjoint_left]
          intro B h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        have hunion_hr : hit ∪ rest = P := by
          ext B
          simp only [hit, rest, Finset.mem_union, Finset.mem_filter]
          tauto
        have hpart : IsPartition U (mergeStep P u v) := by
          rw [hmerge_eq]
          refine ⟨?_, ?_, ?_⟩
          · intro B hB
            rcases Finset.mem_insert.mp hB with rfl | hBr
            · exact ⟨u, Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩⟩
            · exact hP.1 B (Finset.mem_filter.mp hBr).1
          · intro B1 h1 B2 h2 hne
            rcases Finset.mem_insert.mp h1 with rfl | h1r <;>
              rcases Finset.mem_insert.mp h2 with rfl | h2r
            · exact (hne rfl).elim
            · rw [Finset.disjoint_left]
              intro x hx1 hx2
              obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx1
              have hB'P := (Finset.mem_filter.mp hB'h).1
              have hB2P := (Finset.mem_filter.mp h2r).1
              have heq := partition_unique_block hP hB'P hB2P hxB' hx2
              subst heq
              exact (Finset.mem_filter.mp h2r).2 (Finset.mem_filter.mp hB'h).2
            · rw [Finset.disjoint_left]
              intro x hx1 hx2
              obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx2
              have hB'P := (Finset.mem_filter.mp hB'h).1
              have hB1P := (Finset.mem_filter.mp h1r).1
              have heq := partition_unique_block hP hB'P hB1P hxB' hx1
              subst heq
              exact (Finset.mem_filter.mp h1r).2 (Finset.mem_filter.mp hB'h).2
            · exact hP.2.1 B1 (Finset.mem_filter.mp h1r).1 B2 (Finset.mem_filter.mp h2r).1 hne
          · rw [Finset.biUnion_insert]
            change hit.biUnion id ∪ rest.biUnion id = U
            ext x
            rw [← hP.2.2, ← hunion_hr]
            simp only [Finset.mem_union, Finset.mem_biUnion, id]
            constructor
            · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
              · exact ⟨B, Or.inl hB, hx⟩
              · exact ⟨B, Or.inr hB, hx⟩
            · rintro ⟨B, hB | hB, hx⟩
              · exact Or.inl ⟨B, hB, hx⟩
              · exact Or.inr ⟨B, hB, hx⟩
        have hcard : P.card ≤ (mergeStep P u v).card + 1 := by
          rw [hmerge_eq, Finset.card_insert_of_notMem hnot_mem_rest, ← hunion_hr,
            Finset.card_union_of_disjoint hdisj_hr]
          omega
        have hmono : ∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B := by
          rintro x y ⟨B, hBP, hxB, hyB⟩
          rw [hmerge_eq]
          by_cases hhit : u ∈ B ∨ v ∈ B
          · refine ⟨hit.biUnion id, Finset.mem_insert_self _ _, ?_, ?_⟩
            · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hBP, hhit⟩, hxB⟩
            · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hBP, hhit⟩, hyB⟩
          · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hBP, hhit⟩), hxB, hyB⟩
        have hpair : ∃ B ∈ mergeStep P u v, u ∈ B ∧ v ∈ B := by
          rw [hmerge_eq]
          exact ⟨hit.biUnion id, Finset.mem_insert_self _ _,
            Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩,
            Finset.mem_biUnion.mpr ⟨Bv, hBv_hit, hvBv⟩⟩
        exact ⟨hpart, hcard, hmono, hpair⟩
      have mergeFold_props {α : Type} [DecidableEq α] (U : Finset α) (pairs : List (α × α)) :
          ∀ (P : Finset (Finset α)),
            IsPartition U P →
            (∀ pr ∈ pairs, pr.1 ∈ U ∧ pr.2 ∈ U) →
            let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P
            IsPartition U Q ∧
            P.card ≤ pairs.length + Q.card ∧
            (∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ Q, x ∈ B ∧ y ∈ B) ∧
            (∀ pr ∈ pairs, ∃ B ∈ Q, pr.1 ∈ B ∧ pr.2 ∈ B) := by
        induction pairs with
        | nil =>
          intro P hP _
          exact ⟨hP, by simp, fun _ _ h => h, fun _ h => by cases h⟩
        | cons pr rest ih =>
          intro P hP hmem
          have hpr := hmem pr List.mem_cons_self
          have hrest : ∀ pr' ∈ rest, pr'.1 ∈ U ∧ pr'.2 ∈ U :=
            fun pr' h' => hmem pr' (List.mem_cons_of_mem _ h')
          obtain ⟨hP1, hcard1, hmono1, hpair1⟩ := mergeStep_props hP hpr.1 hpr.2
          obtain ⟨hQ, hcard2, hmono2, hpair2⟩ := ih (mergeStep P pr.1 pr.2) hP1 hrest
          refine ⟨hQ, by simp only [List.foldl_cons, List.length_cons]; omega,
            fun x y hxy => hmono2 x y (hmono1 x y hxy), ?_⟩
          intro pr' hpr'
          rcases List.mem_cons.mp hpr' with rfl | hrest'
          · exact hmono2 pr'.1 pr'.2 hpair1
          · exact hpair2 pr' hrest'
      have side_component_bound {X : Type} [Fintype X] [DecidableEq X]
          (wireOf : X → ℕ) (hwire_lt : ∀ x : X, wireOf x < 26)
          (hwire_inj : Function.Injective wireOf)
          (S_gates : Finset (Fin C.gates.length))
          (opWire : Fin C.gates.length → ℕ)
          (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath (opWire j) (wireOf x)) :
          let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
          let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
          let O_S : Finset (Fin C.gates.length) :=
            Finset.univ.filter (fun o =>
              (gateAt C o.val).op = GateOp.or ∧
              2 ≤ (reach (26 + o.val)).card ∧
              ∃ j ∈ S_gates, OrPath (opWire j) (26 + o.val))
          E_S.card ≤ O_S.card + S_gates.card := by
        let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
        let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
        let O_S : Finset (Fin C.gates.length) :=
          Finset.univ.filter (fun o =>
            (gateAt C o.val).op = GateOp.or ∧
            2 ≤ (reach (26 + o.val)).card ∧
            ∃ j ∈ S_gates, OrPath (opWire j) (26 + o.val))
        let pairOf (o : Fin C.gates.length) : Option (X × X) :=
          let a := (gateAt C o.val).inputs.getD 0 0
          let b := (gateAt C o.val).inputs.getD 1 0
          if h : (reach a).Nonempty ∧ (reach b).Nonempty then some (h.1.choose, h.2.choose) else none
        let pairs : List (X × X) := O_S.toList.filterMap pairOf
        have hpairs_len : pairs.length ≤ O_S.card := by
          have h1 := List.length_filterMap_le pairOf O_S.toList
          rw [Finset.length_toList] at h1
          exact h1
        have hpairs_in : ∀ pr ∈ pairs, pr.1 ∈ E_S ∧ pr.2 ∈ E_S := by
          intro pr hpr
          obtain ⟨o, ho_list, hpair_eq⟩ := List.mem_filterMap.mp hpr
          have ho : o ∈ O_S := Finset.mem_toList.mp ho_list
          obtain ⟨hor, _, j, hjS, hjo⟩ := (Finset.mem_filter.mp ho).2
          obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs o.isLt
          have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
          have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
          dsimp only [pairOf] at hpair_eq
          rw [ha_get, hb_get] at hpair_eq
          split_ifs at hpair_eq with hne
          injection hpair_eq with hpr_eq
          rw [← hpr_eq]
          have hu : hne.1.choose ∈ reach a := hne.1.choose_spec
          have hv : hne.2.choose ∈ reach b := hne.2.choose_spec
          have hua : OrPath a (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
          have hvb : OrPath b (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
          have ha_mem : a ∈ (gateAt C o.val).inputs := by rw [hab]; exact List.mem_cons_self
          have hb_mem : b ∈ (gateAt C o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
          refine ⟨Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              orPath_trans hjo (orPath_step o.isLt hor ha_mem hua)⟩⟩,
            Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              orPath_trans hjo (orPath_step o.isLt hor hb_mem hvb)⟩⟩⟩
        let P0 : Finset (Finset X) := E_S.image (fun x => {x})
        have hP0_part : IsPartition E_S P0 := by
          refine ⟨?_, ?_, ?_⟩
          · intro B hB
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hB
            exact ⟨x, Finset.mem_singleton_self x⟩
          · intro B1 h1 B2 h2 hne
            obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp h1
            obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp h2
            rw [Finset.disjoint_singleton]
            intro heq; subst heq; exact hne rfl
          · ext x
            simp only [P0, Finset.mem_biUnion, Finset.mem_image, id]
            constructor
            · rintro ⟨B, ⟨y, hy, rfl⟩, hx⟩
              rw [Finset.mem_singleton.mp hx]; exact hy
            · intro hx
              exact ⟨{x}, ⟨x, hx, rfl⟩, Finset.mem_singleton_self x⟩
        have hP0_card : P0.card = E_S.card := by
          rw [Finset.card_image_of_injective _ (fun a b h => Finset.singleton_injective h)]
        let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P0
        obtain ⟨hQ_part, hQ_card, _, hQ_pairs⟩ := mergeFold_props E_S pairs P0 hP0_part hpairs_in
        have hsame_wire : ∀ w : ℕ, (∃ j ∈ S_gates, OrPath (opWire j) w) →
            ∀ x1 ∈ reach w, ∀ x2 ∈ reach w, ∃ B ∈ Q, x1 ∈ B ∧ x2 ∈ B := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            rintro ⟨j, hjS, hjw⟩ x1 hx1 x2 hx2
            have hp1 : OrPath w (wireOf x1) := (Finset.mem_filter.mp hx1).2
            have hp2 : OrPath w (wireOf x2) := (Finset.mem_filter.mp hx2).2
            by_cases h12 : x1 = x2
            · subst h12
              have hx1E : x1 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjw hp1⟩⟩
              obtain ⟨B, hBQ, hxB⟩ := partition_exists_block hQ_part hx1E
              exact ⟨B, hBQ, hxB, hxB⟩
            · have hne_w : wireOf x1 ≠ wireOf x2 := fun h => h12 (hwire_inj h)
              have hstep_ex : ∃ k < C.gates.length, w = 26 + k ∧ (gateAt C k).op = GateOp.or := by
                rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
                · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                  · exact (hne_w h2).elim
                  · exact ⟨k, hk, hwk, hor⟩
                · exact ⟨k, hk, hwk, hor⟩
              obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
              let o : Fin C.gates.length := ⟨k, hk⟩
              have h2card : 2 ≤ (reach (26 + o.val)).card := by
                rw [← hwk]
                exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
              have ho_mem : o ∈ O_S :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hor, h2card, j, hjS, hwk ▸ hjw⟩
              obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := isAO2_gate_inputs hk
              have ha_mem : a ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_self
              have hb_mem : b ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hja : OrPath (opWire j) a :=
                orPath_trans hjw (hwk ▸ orPath_step hk hor ha_mem (orPath_refl a))
              have hjb : OrPath (opWire j) b :=
                orPath_trans hjw (hwk ▸ orPath_step hk hor hb_mem (orPath_refl b))
              have hsplit_x : ∀ x ∈ reach w, x ∈ reach a ∨ x ∈ reach b := by
                intro x hx
                have hpx : OrPath w (wireOf x) := (Finset.mem_filter.mp hx).2
                have hlt_x : wireOf x < 26 := hwire_lt x
                rcases orPath_cases hpx with hxeq | ⟨k', _, hwk', _, c, hc, hpc⟩
                · omega
                · have hkeq : k' = k := by omega
                  subst hkeq
                  rw [hab] at hc
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                  rcases hc with rfl | rfl
                  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
                  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
              rcases hsplit_x x1 hx1 with h1a | h1b <;> rcases hsplit_x x2 hx2 with h2a | h2b
              · exact ih a (by omega) ⟨j, hjS, hja⟩ x1 h1a x2 h2a
              · have hne_ab : (reach a).Nonempty ∧ (reach b).Nonempty := ⟨⟨x1, h1a⟩, ⟨x2, h2b⟩⟩
                have hpair_in : (hne_ab.1.choose, hne_ab.2.choose) ∈ pairs := by
                  apply List.mem_filterMap.mpr
                  refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
                  dsimp only [pairOf]
                  have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                  have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
                  rw [ha_get, hb_get]; split_ifs; rfl
                obtain ⟨B1, hB1Q, hx1B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x1 h1a hne_ab.1.choose hne_ab.1.choose_spec
                obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
                obtain ⟨B3, hB3Q, hvB3, hx2B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x2 h2b
                have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
                have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
                subst h12B; subst h23B
                exact ⟨B1, hB1Q, hx1B1, hx2B3⟩
              · have hne_ab : (reach a).Nonempty ∧ (reach b).Nonempty := ⟨⟨x2, h2a⟩, ⟨x1, h1b⟩⟩
                have hpair_in : (hne_ab.1.choose, hne_ab.2.choose) ∈ pairs := by
                  apply List.mem_filterMap.mpr
                  refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
                  dsimp only [pairOf]
                  have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                  have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
                  rw [ha_get, hb_get]; split_ifs; rfl
                obtain ⟨B1, hB1Q, hx2B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x2 h2a hne_ab.1.choose hne_ab.1.choose_spec
                obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
                obtain ⟨B3, hB3Q, hvB3, hx1B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x1 h1b
                have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
                have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
                subst h12B; subst h23B
                exact ⟨B1, hB1Q, hx1B3, hx2B1⟩
              · exact ih b (by omega) ⟨j, hjS, hjb⟩ x1 h1b x2 h2b
        let blk (j : Fin C.gates.length) : Finset X :=
          if hj : j ∈ S_gates then
            have hx : (hnonempty j hj).choose ∈ E_S :=
              Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hj).choose_spec⟩⟩
            (partition_exists_block hQ_part hx).choose
          else ∅
        have hQ_sub : Q ⊆ S_gates.image blk := by
          intro B hBQ
          obtain ⟨x, hxB⟩ := hQ_part.1 B hBQ
          have hxE : x ∈ E_S := by
            rw [← hQ_part.2.2]
            exact Finset.mem_biUnion.mpr ⟨B, hBQ, hxB⟩
          obtain ⟨j, hjS, hxj⟩ := Finset.mem_biUnion.mp hxE
          refine Finset.mem_image.mpr ⟨j, hjS, ?_⟩
          let x0 := (hnonempty j hjS).choose
          have hx0j : x0 ∈ reach (opWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hjS).choose_spec⟩
          obtain ⟨B', hB'Q, hxB', hx0B'⟩ := hsame_wire (opWire j) ⟨j, hjS, orPath_refl _⟩ x hxj x0 hx0j
          have hBB' := partition_unique_block hQ_part hBQ hB'Q hxB hxB'
          have hblk_spec : blk j ∈ Q ∧ x0 ∈ blk j := by
            dsimp only [blk]
            simp only [hjS, ↓reduceDIte]
            have hx0E : x0 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS, hx0j⟩
            exact (partition_exists_block hQ_part hx0E).choose_spec
          have hB'blk := partition_unique_block hQ_part hB'Q hblk_spec.1 hx0B' hblk_spec.2
          exact (hBB'.trans hB'blk).symm
        have hQ_le_S : Q.card ≤ S_gates.card :=
          (Finset.card_le_card hQ_sub).trans Finset.card_image_le
        change P0.card ≤ pairs.length + Q.card at hQ_card
        change E_S.card ≤ O_S.card + S_gates.card
        omega
      let pts (w : ℕ) : Finset (Fin 13) :=
        Finset.univ.filter (fun p => OrPath w p.val)
      let lns (w : ℕ) : Finset (Fin 13) :=
        Finset.univ.filter (fun l => OrPath w (13 + l.val))
      have hComp_wire (x : Fin 26 → Bool) :
          wireVal 26 C C.output x =
            decide (∃ (p l : Fin 13), (p, l) ∈ E ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
        have h := hC_exact x
        change wireVal 26 C C.output x = _ at h
        rw [h]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, hmem_E]
      have hno_pts_only (x : Fin 26 → Bool) (h0 : ∀ l : Fin 13, x (Fin.natAdd 13 l) = false) :
          wireVal 26 C C.output x = false := by
        rw [hComp_wire, decide_eq_false_iff_not]
        rintro ⟨p, l, _, _, hl⟩
        rw [h0 l] at hl; cases hl
      have hno_lns_only (x : Fin 26 → Bool) (h0 : ∀ p : Fin 13, x (Fin.castAdd 13 p) = false) :
          wireVal 26 C C.output x = false := by
        rw [hComp_wire, decide_eq_false_iff_not]
        rintro ⟨p, l, _, hp, _⟩
        rw [h0 p] at hp; cases hp
      have hedge_covered : ∀ p l : Fin 13, (p, l) ∈ E →
          ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
            OrPath C.output (26 + j.val) ∧
            ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
              ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
               (OrPath a (13 + l.val) ∧ OrPath b p.val)) := by
        intro p l hpl
        obtain ⟨j, a, b, handOn, htop, hpa, hlb⟩ := hall p l ((hmem_E p l).mp hpl)
        obtain ⟨⟨hjlt, hjand⟩, hor_ab⟩ := handOn
        obtain ⟨a0, b0, hab0, _, _⟩ := isAO2_gate_inputs hjlt
        have hin0 : in0 C j = a0 := by change (gateAt C j).inputs.getD 0 0 = a0; rw [hab0]; rfl
        have hin1 : in1 C j = b0 := by change (gateAt C j).inputs.getD 1 0 = b0; rw [hab0]; rfl
        refine ⟨⟨j, hjlt⟩, hjand, orp_to_orPath htop, a0, b0, hab0, ?_⟩
        rcases hor_ab with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
          exact Or.inl ⟨orp_to_orPath hpa, orp_to_orPath hlb⟩
        · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
          exact Or.inr ⟨orp_to_orPath hlb, orp_to_orPath hpa⟩
      let Tstar : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun j =>
          (gateAt C j.val).op = GateOp.and ∧
          OrPath C.output (26 + j.val) ∧
          ∃ p l : Fin 13, ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
             (OrPath a (13 + l.val) ∧ OrPath b p.val)))
      let pWire (j : Fin C.gates.length) : ℕ :=
        let a := (gateAt C j.val).inputs.getD 0 0
        let b := (gateAt C j.val).inputs.getD 1 0
        if (pts a).Nonempty then a else b
      let lWire (j : Fin C.gates.length) : ℕ :=
        let a := (gateAt C j.val).inputs.getD 0 0
        let b := (gateAt C j.val).inputs.getD 1 0
        if (pts a).Nonempty then b else a
      let pSide (j : Fin C.gates.length) : Finset (Fin 13) := pts (pWire j)
      let lSide (j : Fin C.gates.length) : Finset (Fin 13) := lns (lWire j)
      have hTstar_props : ∀ j ∈ Tstar,
          (gateAt C j.val).op = GateOp.and ∧
          OrPath C.output (26 + j.val) ∧
          (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
          lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
          (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
          ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
        intro j hj
        obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
        have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
        have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
        have hand_sound : ∀ x : Fin 26 → Bool,
            wireVal 26 C a x = true → wireVal 26 C b x = true → wireVal 26 C C.output x = true := by
          intro x hxa hxb
          apply orPath_sound htop x
          rw [wireVal_and_pair j.isLt hand hab x, hxa, hxb]
          rfl
        have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
          rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
          let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p1 ∨ i = Fin.castAdd 13 p2)
          have h1 : wireVal 26 C p1.val x = true := by
            have := wireVal_input (Fin.castAdd 13 p1) x
            simpa [x] using this
          have h2 : wireVal 26 C p2.val x = true := by
            have := wireVal_input (Fin.castAdd 13 p2) x
            simpa [x] using this
          have hxa := orPath_sound (Finset.mem_filter.mp hp1).2 x h1
          have hxb := orPath_sound (Finset.mem_filter.mp hp2).2 x h2
          have ht := hand_sound x hxa hxb
          have hf := hno_pts_only x (fun l => by
            simp only [x, decide_eq_false_iff_not]
            rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
          rw [ht] at hf; cases hf
        have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
          rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
          let x : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l1 ∨ i = Fin.natAdd 13 l2)
          have h1 : wireVal 26 C (13 + l1.val) x = true := by
            have := wireVal_input (Fin.natAdd 13 l1) x
            simpa [x, Nat.add_comm] using this
          have h2 : wireVal 26 C (13 + l2.val) x = true := by
            have := wireVal_input (Fin.natAdd 13 l2) x
            simpa [x, Nat.add_comm] using this
          have hxa := orPath_sound (Finset.mem_filter.mp hl1).2 x h1
          have hxb := orPath_sound (Finset.mem_filter.mp hl2).2 x h2
          have ht := hand_sound x hxa hxb
          have hf := hno_lns_only x (fun p => by
            simp only [x, decide_eq_false_iff_not]
            rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
          rw [ht] at hf; cases hf
        have hbiclique : ∀ p l : Fin 13,
            ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
          intro p l hpl
          let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          have hxp : wireVal 26 C p.val x = true := by
            have := wireVal_input (Fin.castAdd 13 p) x
            simpa [x] using this
          have hxl : wireVal 26 C (13 + l.val) x = true := by
            have := wireVal_input (Fin.natAdd 13 l) x
            simpa [x, Nat.add_comm] using this
          have hout_t : wireVal 26 C C.output x = true := by
            rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
            · exact hand_sound x
                (orPath_sound (Finset.mem_filter.mp hpa).2 x hxp)
                (orPath_sound (Finset.mem_filter.mp hlb).2 x hxl)
            · exact hand_sound x
                (orPath_sound (Finset.mem_filter.mp hla).2 x hxl)
                (orPath_sound (Finset.mem_filter.mp hpb).2 x hxp)
          rw [hComp_wire, decide_eq_true_eq] at hout_t
          obtain ⟨p', l', hp'l', hxp', hxl'⟩ := hout_t
          simp only [x, decide_eq_true_eq] at hxp' hxl'
          have hp_eq : p' = p := by
            rcases hxp' with h1 | h2
            · exact Fin.ext (by simpa using congrArg Fin.val h1)
            · have := congrArg Fin.val h2; simp at this; omega
          have hl_eq : l' = l := by
            rcases hxl' with h1 | h2
            · have := congrArg Fin.val h1; simp at this; omega
            · exact Fin.ext (by have := congrArg Fin.val h2; simp at this; omega)
          rw [← hp_eq, ← hl_eq]; exact hp'l'
        have hsides : (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
            lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
            (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) := by
          rcases hlr0 with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
          · have hpa_ne : (pts a).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩⟩
            have hlb_ne : (lns b).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩⟩
            have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
            have hlW : lWire j = b := by dsimp only [lWire]; simp only [ha_get, hb_get, hpa_ne, ↓reduceIte]
            have hla_em : lns a = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨h, hlb_ne⟩)
            have hpb_em : pts b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_pts ⟨hpa_ne, h⟩)
            refine ⟨by simpa [pSide, hpW] using hpa_ne, by simpa [lSide, hlW] using hlb_ne,
              by rw [hpW]; exact hla_em, by rw [hlW]; exact hpb_em, ?_⟩
            intro p hp l hl
            rw [show pSide j = pts a by simp [pSide, hpW]] at hp
            rw [show lSide j = lns b by simp [lSide, hlW]] at hl
            exact hbiclique p l (Or.inl ⟨hp, hl⟩)
          · have hla_ne : (lns a).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩⟩
            have hpb_ne : (pts b).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩⟩
            have hpa_not : ¬ (pts a).Nonempty := fun h => hno_both_pts ⟨h, hpb_ne⟩
            have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
            have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
            have hlb_em : lns b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨hla_ne, h⟩)
            have hpa_em : pts a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpa_not
            refine ⟨by simpa [pSide, hpW] using hpb_ne, by simpa [lSide, hlW] using hla_ne,
              by rw [hpW]; exact hlb_em, by rw [hlW]; exact hpa_em, ?_⟩
            intro p hp l hl
            rw [show pSide j = pts b by simp [pSide, hpW]] at hp
            rw [show lSide j = lns a by simp [lSide, hlW]] at hl
            exact hbiclique p l (Or.inr ⟨hp, hl⟩)
        have hstar : (pSide j).card = 1 ∨ (lSide j).card = 1 := by
          have hp1 : 1 ≤ (pSide j).card := Finset.card_pos.mpr hsides.1
          have hl1 : 1 ≤ (lSide j).card := Finset.card_pos.mpr hsides.2.1
          by_contra hneither
          have hp2 : 1 < (pSide j).card := by omega
          have hl2 : 1 < (lSide j).card := by omega
          obtain ⟨p1, hp1m, p2, hp2m, hpne⟩ := Finset.one_lt_card.mp hp2
          obtain ⟨l1, hl1m, l2, hl2m, hlne⟩ := Finset.one_lt_card.mp hl2
          exact hNoC4 p1 p2 l1 l2 hpne hlne
            ⟨(hmem_E p1 l1).mp (hsides.2.2.2.2 p1 hp1m l1 hl1m),
             (hmem_E p1 l2).mp (hsides.2.2.2.2 p1 hp1m l2 hl2m),
             (hmem_E p2 l1).mp (hsides.2.2.2.2 p2 hp2m l1 hl1m),
             (hmem_E p2 l2).mp (hsides.2.2.2.2 p2 hp2m l2 hl2m)⟩
        exact ⟨hand, htop, hsides.1, hsides.2.1, hsides.2.2.1, hsides.2.2.2.1, hsides.2.2.2.2, hstar⟩
      have hE_in_Tstar : ∀ p l : Fin 13, (p, l) ∈ E →
          ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
        intro p l hpl
        obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
        have hjT : j ∈ Tstar :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
        have hprops := hTstar_props j hjT
        have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
        have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
        refine ⟨j, hjT, ?_⟩
        rcases hlr with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
        · have hpa_m : p ∈ pts a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩
          have hlb_m : l ∈ lns b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩
          have hpa_ne : (pts a).Nonempty := ⟨p, hpa_m⟩
          have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
          have hlW : lWire j = b := by dsimp only [lWire]; simp only [ha_get, hb_get, hpa_ne, ↓reduceIte]
          exact ⟨by simpa [pSide, hpW] using hpa_m, by simpa [lSide, hlW] using hlb_m⟩
        · have hla_m : l ∈ lns a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩
          have hpb_m : p ∈ pts b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩
          have hpa_not : ¬ (pts a).Nonempty := by
            intro hpa_ne
            have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
            have hlem := hprops.2.2.2.2.1
            rw [hpW] at hlem
            rw [hlem] at hla_m; cases hla_m
          have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
          have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
          exact ⟨by simpa [pSide, hpW] using hpb_m, by simpa [lSide, hlW] using hla_m⟩
      let Tpt : Finset (Fin C.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
      let Tln : Finset (Fin C.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
      have hTpt_Tln_disj : Disjoint Tpt Tln := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
        ext j; simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]; tauto
      have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
        rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
      let centerP (j : Fin C.gates.length) : Fin 13 :=
        if h : (pSide j).Nonempty then h.choose else 0
      let centerL (j : Fin C.gates.length) : Fin 13 :=
        if h : (lSide j).Nonempty then h.choose else 0
      have hcenterP_eq : ∀ j ∈ Tpt, ∀ p ∈ pSide j, p = centerP j := by
        intro j hj p hp
        have hjT := (Finset.mem_filter.mp hj).1
        have hcard1 := (Finset.mem_filter.mp hj).2
        have hne := (hTstar_props j hjT).2.2.1
        have hmem_c : centerP j ∈ pSide j := by
          dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
        exact Finset.card_le_one.mp (le_of_eq hcard1) p hp (centerP j) hmem_c
      have hcenterL_eq : ∀ j ∈ Tln, ∀ l ∈ lSide j, l = centerL j := by
        intro j hj l hl
        have hjT := (Finset.mem_filter.mp hj).1
        have hne1 := (Finset.mem_filter.mp hj).2
        have hprops := hTstar_props j hjT
        have hcard1 : (lSide j).card = 1 := by
          rcases hprops.2.2.2.2.2.2.2 with h | h
          · exact (hne1 h).elim
          · exact h
        have hne := hprops.2.2.2.1
        have hmem_c : centerL j ∈ lSide j := by
          dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
        exact Finset.card_le_one.mp (le_of_eq hcard1) l hl (centerL j) hmem_c
      have hcenterP_mem : ∀ j ∈ Tpt, centerP j ∈ pSide j := by
        intro j hj
        have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.1
        dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
      have hcenterL_mem : ∀ j ∈ Tln, centerL j ∈ lSide j := by
        intro j hj
        have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.2.1
        dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
      let A : Finset (Fin 13) := Tpt.image centerP
      let B : Finset (Fin 13) := Tln.image centerL
      have hAB_card : A.card + B.card ≤ Tstar.card := by
        have hA : A.card ≤ Tpt.card := Finset.card_image_le
        have hB : B.card ≤ Tln.card := Finset.card_image_le
        omega
      have hcover : ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B := by
        intro e he
        obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
        by_cases h1 : (pSide j).card = 1
        · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
          exact Or.inl (Finset.mem_image.mpr ⟨j, hjpt, (hcenterP_eq j hjpt e.1 hpj).symm⟩)
        · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
          exact Or.inr (Finset.mem_image.mpr ⟨j, hjln, (hcenterL_eq j hjln e.2 hlj).symm⟩)
      have hAB_ge13 : 13 ≤ A.card + B.card := by
        have hE_cov_sub : E ⊆
            A.biUnion (fun p => ({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))) ∪
            B.biUnion (fun l => ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l))) := by
          intro e hpl
          obtain ⟨p, l⟩ := e
          have hIpl : I p l := (hmem_E p l).mp hpl
          rcases hcover (p, l) hpl with hpA | hlB
          · apply Finset.mem_union_left
            refine Finset.mem_biUnion.mpr ⟨p, hpA, Finset.mem_image.mpr ⟨l, ?_, rfl⟩⟩
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hIpl with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl (add_sub_cancel_right l 1).symm)
            · exact Or.inr (Or.inr (Or.inl (add_sub_cancel_right l 3).symm))
            · exact Or.inr (Or.inr (Or.inr (add_sub_cancel_right l 9).symm))
          · apply Finset.mem_union_right
            refine Finset.mem_biUnion.mpr ⟨l, hlB, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact hIpl
        have hcard4p (p : Fin 13) : (({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))).card ≤ 4 := by
          refine le_trans Finset.card_image_le ?_
          exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
            (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
              (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))))
        have hcard4l (l : Fin 13) : (({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l))).card ≤ 4 := by
          refine le_trans Finset.card_image_le ?_
          exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
            (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
              (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))))
        have hbound : E.card ≤ 4 * A.card + 4 * B.card := by
          calc E.card
              ≤ (A.biUnion (fun p => ({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))) ∪
                 B.biUnion (fun l => ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l)))).card :=
                  Finset.card_le_card hE_cov_sub
            _ ≤ (A.biUnion _).card + (B.biUnion _).card := Finset.card_union_le _ _
            _ ≤ (∑ p ∈ A, (({p, p - 1, p - 3, p - 9} : Finset (Fin 13)).image (fun l => (p, l))).card) +
                (∑ l ∈ B, (({l, l + 1, l + 3, l + 9} : Finset (Fin 13)).image (fun p => (p, l))).card) :=
                  Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
            _ ≤ (∑ _p ∈ A, 4) + (∑ _l ∈ B, 4) :=
                  Nat.add_le_add (Finset.sum_le_sum fun p _ => hcard4p p) (Finset.sum_le_sum fun l _ => hcard4l l)
            _ = 4 * A.card + 4 * B.card := by simp only [Finset.sum_const, smul_eq_mul]; omega
        omega
      let Otop : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt C o.val).op = GateOp.or ∧
          OrPath C.output (26 + o.val) ∧
          ∃ a ∈ Tstar, OrPath (26 + o.val) (26 + a.val))
      have hOtop_disj_Tstar : Disjoint Otop Tstar := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        have hor := (Finset.mem_filter.mp h1).2.1
        have hand := (hTstar_props j h2).1
        rw [hor] at hand; cases hand
      have hTstar_le_Otop : Tstar.card ≤ Otop.card + 1 := by
        by_cases hle1 : Tstar.card ≤ 1
        · omega
        · have hlt : 1 < Tstar.card := by omega
          obtain ⟨a1, ha1, a2, ha2, hne12⟩ := Finset.one_lt_card.mp hlt
          have hop1 := (hTstar_props a1 ha1).2.1
          have hop2 := (hTstar_props a2 ha2).2.1
          have hroot_ex : ∃ root ∈ Otop, C.output = 26 + root.val := by
            rcases orPath_cases hop1 with heq1 | ⟨k, hk, hok, hork, _, _, _⟩
            · rcases orPath_cases hop2 with heq2 | ⟨k, hk, hok, hork, _, _, _⟩
              · have : a1.val = a2.val := by omega
                exact (hne12 (Fin.ext this)).elim
              · have : k = a1.val := by omega
                subst this
                have hand1 := (hTstar_props a1 ha1).1
                rw [hork] at hand1; cases hand1
            · refine ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hork,
                hok ▸ orPath_refl _, a1, ha1, hok ▸ hop1⟩, hok⟩
          obtain ⟨root, hrootO, hroot_eq⟩ := hroot_ex
          let H := Otop ∪ Tstar
          have hrootH : root ∈ H := Finset.mem_union_left _ hrootO
          have hH_card : H.card = Otop.card + Tstar.card :=
            Finset.card_union_of_disjoint hOtop_disj_Tstar
          have hpar_ex : ∀ x ∈ H.erase root,
              ∃ y ∈ Otop, 26 + x.val ∈ (gateAt C y.val).inputs := by
            intro x hx
            have hxne : x ≠ root := (Finset.mem_erase.mp hx).1
            have hxH : x ∈ H := (Finset.mem_erase.mp hx).2
            have hx_out : OrPath C.output (26 + x.val) := by
              rcases Finset.mem_union.mp hxH with hO | hT
              · exact (Finset.mem_filter.mp hO).2.2.1
              · exact (hTstar_props x hT).2.1
            have hx_a : ∃ a ∈ Tstar, OrPath (26 + x.val) (26 + a.val) := by
              rcases Finset.mem_union.mp hxH with hO | hT
              · exact (Finset.mem_filter.mp hO).2.2.2
              · exact ⟨x, hT, orPath_refl _⟩
            have hne_out : C.output ≠ 26 + x.val := by
              rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
            obtain ⟨y, hy, hory, hpy, hxin⟩ := orPath_parent hx_out hne_out
            obtain ⟨a, haT, hxa⟩ := hx_a
            refine ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hory, hpy,
              a, haT, orPath_step hy hory hxin hxa⟩, hxin⟩
          let par (x : Fin C.gates.length) : Fin C.gates.length :=
            if hx : x ∈ H.erase root then (hpar_ex x hx).choose else root
          have hpar_mem : ∀ x ∈ H.erase root, par x ∈ Otop := by
            intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.1
          have hpar_in : ∀ x ∈ H.erase root, 26 + x.val ∈ (gateAt C (par x).val).inputs := by
            intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.2
          have hfiber_le2 : ∀ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ 2 := by
            intro y _
            let F := (H.erase root).filter (fun x => par x = y)
            have hsub : F.image (fun x : Fin C.gates.length => 26 + x.val) ⊆ (gateAt C y.val).inputs.toFinset := by
              intro w hw
              obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hw
              obtain ⟨hxH, hxy⟩ := Finset.mem_filter.mp hxF
              rw [List.mem_toFinset, ← hxy]
              exact hpar_in x hxH
            have hinj : Function.Injective (fun x : Fin C.gates.length => 26 + x.val) := by
              intro a b h; dsimp only at h; exact Fin.ext (by omega)
            have h1 : F.card = (F.image (fun x : Fin C.gates.length => 26 + x.val)).card :=
              (Finset.card_image_of_injective F hinj).symm
            have h2 : (F.image (fun x : Fin C.gates.length => 26 + x.val)).card ≤ ((gateAt C y.val).inputs.toFinset).card :=
              Finset.card_le_card hsub
            have h3 : ((gateAt C y.val).inputs.toFinset).card ≤ (gateAt C y.val).inputs.length :=
              List.toFinset_card_le _
            have h4 : (gateAt C y.val).inputs.length = 2 := by
              obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs y.isLt
              rw [hab]; rfl
            change F.card ≤ 2
            omega
          have hsum_eq : (H.erase root).card = ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card :=
            Finset.card_eq_sum_card_fiberwise (f := par) hpar_mem
          have hsum_le : ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ ∑ _y ∈ Otop, 2 :=
            Finset.sum_le_sum hfiber_le2
          simp only [Finset.sum_const, smul_eq_mul] at hsum_le
          have herase : (H.erase root).card + 1 = H.card := Finset.card_erase_add_one hrootH
          omega
      let Tpt_p (p : Fin 13) : Finset (Fin C.gates.length) := Tpt.filter (fun j => centerP j = p)
      let E_p (p : Fin 13) : Finset (Fin 13) := (Tpt_p p).biUnion lSide
      let Obot_p (p : Fin 13) : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt C o.val).op = GateOp.or ∧
          2 ≤ (lns (26 + o.val)).card ∧
          ∃ j ∈ Tpt_p p, OrPath (lWire j) (26 + o.val))
      let Tln_l (l : Fin 13) : Finset (Fin C.gates.length) := Tln.filter (fun j => centerL j = l)
      let E_l (l : Fin 13) : Finset (Fin 13) := (Tln_l l).biUnion pSide
      let Obot_l (l : Fin 13) : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt C o.val).op = GateOp.or ∧
          2 ≤ (pts (26 + o.val)).card ∧
          ∃ j ∈ Tln_l l, OrPath (pWire j) (26 + o.val))
      have hEp_bound : ∀ p ∈ A, (E_p p).card ≤ (Obot_p p).card + (Tpt_p p).card := by
        intro p _
        exact side_component_bound
          (fun l : Fin 13 => 13 + l.val) (fun l => by omega)
          (fun l1 l2 h => Fin.ext (by dsimp only at h; omega))
          (Tpt_p p) lWire
          (fun j hj => by
            obtain ⟨l, hl⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.2.1
            exact ⟨l, (Finset.mem_filter.mp hl).2⟩)
      have hEl_bound : ∀ l ∈ B, (E_l l).card ≤ (Obot_l l).card + (Tln_l l).card := by
        intro l _
        exact side_component_bound
          (fun p : Fin 13 => p.val) (fun p => by omega)
          (fun p1 p2 h => Fin.ext h)
          (Tln_l l) pWire
          (fun j hj => by
            obtain ⟨p, hp⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.1
            exact ⟨p, (Finset.mem_filter.mp hp).2⟩)
      have hObot_p_disj : Set.PairwiseDisjoint (A : Set (Fin 13)) Obot_p := by
        intro p1 _ p2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro o h1 h2
        obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
        obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
        obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lns (26 + o.val)).card)
        have hj1pt := (Finset.mem_filter.mp hj1).1
        have hj1p := (Finset.mem_filter.mp hj1).2
        have hj2pt := (Finset.mem_filter.mp hj2).1
        have hj2p := (Finset.mem_filter.mp hj2).2
        have hp1_in : p1 ∈ pSide j1 := hj1p ▸ hcenterP_mem j1 hj1pt
        have hp2_in : p2 ∈ pSide j2 := hj2p ▸ hcenterP_mem j2 hj2pt
        have hl1_j1 : l1 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo1 (Finset.mem_filter.mp hl1).2⟩
        have hl2_j1 : l2 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo1 (Finset.mem_filter.mp hl2).2⟩
        have hl1_j2 : l1 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo2 (Finset.mem_filter.mp hl1).2⟩
        have hl2_j2 : l2 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo2 (Finset.mem_filter.mp hl2).2⟩
        have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1pt).1).2.2.2.2.2.2.1
        have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2pt).1).2.2.2.2.2.2.1
        exact hNoC4 p1 p2 l1 l2 hne hlne
          ⟨(hmem_E p1 l1).mp (hpr1 p1 hp1_in l1 hl1_j1),
           (hmem_E p1 l2).mp (hpr1 p1 hp1_in l2 hl2_j1),
           (hmem_E p2 l1).mp (hpr2 p2 hp2_in l1 hl1_j2),
           (hmem_E p2 l2).mp (hpr2 p2 hp2_in l2 hl2_j2)⟩
      have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin 13)) Obot_l := by
        intro l1 _ l2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro o h1 h2
        obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
        obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
        obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (pts (26 + o.val)).card)
        have hj1ln := (Finset.mem_filter.mp hj1).1
        have hj1l := (Finset.mem_filter.mp hj1).2
        have hj2ln := (Finset.mem_filter.mp hj2).1
        have hj2l := (Finset.mem_filter.mp hj2).2
        have hl1_in : l1 ∈ lSide j1 := hj1l ▸ hcenterL_mem j1 hj1ln
        have hl2_in : l2 ∈ lSide j2 := hj2l ▸ hcenterL_mem j2 hj2ln
        have hp1_j1 : p1 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo1 (Finset.mem_filter.mp hp1).2⟩
        have hp2_j1 : p2 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo1 (Finset.mem_filter.mp hp2).2⟩
        have hp1_j2 : p1 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo2 (Finset.mem_filter.mp hp1).2⟩
        have hp2_j2 : p2 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo2 (Finset.mem_filter.mp hp2).2⟩
        have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1ln).1).2.2.2.2.2.2.1
        have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2ln).1).2.2.2.2.2.2.1
        exact hNoC4 p1 p2 l1 l2 hpne hne
          ⟨(hmem_E p1 l1).mp (hpr1 p1 hp1_j1 l1 hl1_in),
           (hmem_E p1 l2).mp (hpr2 p1 hp1_j2 l2 hl2_in),
           (hmem_E p2 l1).mp (hpr1 p2 hp2_j1 l1 hl1_in),
           (hmem_E p2 l2).mp (hpr2 p2 hp2_j2 l2 hl2_in)⟩
      let ObotA := A.biUnion Obot_p
      let ObotB := B.biUnion Obot_l
      have hObotAB_disj : Disjoint ObotA ObotB := by
        rw [Finset.disjoint_left]
        intro o hA hB
        obtain ⟨p, _, hoA⟩ := Finset.mem_biUnion.mp hA
        obtain ⟨l, _, hoB⟩ := Finset.mem_biUnion.mp hB
        have hcard_l := (Finset.mem_filter.mp hoA).2.2.1
        obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (26 + o.val)).card)
        obtain ⟨j, hj, hjo⟩ := (Finset.mem_filter.mp hoB).2.2.2
        have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        have hlem := (hTstar_props j hjT).2.2.2.2.1
        have hl0_in : l0 ∈ lns (pWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          orPath_trans hjo (Finset.mem_filter.mp hl0).2⟩
        rw [hlem] at hl0_in; cases hl0_in
      let Obot := ObotA ∪ ObotB
      have hObot_card : Obot.card = (∑ p ∈ A, (Obot_p p).card) + (∑ l ∈ B, (Obot_l l).card) := by
        rw [Finset.card_union_of_disjoint hObotAB_disj,
          Finset.card_biUnion hObot_p_disj, Finset.card_biUnion hObot_l_disj]
      have hObot_disj_Tstar : Disjoint Obot Tstar := by
        rw [Finset.disjoint_left]
        intro o h1 h2
        have hand := (hTstar_props o h2).1
        rcases Finset.mem_union.mp h1 with hA | hB
        · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
          have hor := (Finset.mem_filter.mp ho).2.1
          rw [hor] at hand; cases hand
        · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
          have hor := (Finset.mem_filter.mp ho).2.1
          rw [hor] at hand; cases hand
      have hObot_disj_Otop : Disjoint Obot Otop := by
        rw [Finset.disjoint_left]
        intro o hbot htop
        have hop_out := (Finset.mem_filter.mp htop).2.2.1
        rcases Finset.mem_union.mp hbot with hA | hB
        · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
          have hcard := (Finset.mem_filter.mp ho).2.2.1
          obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (26 + o.val)).card)
          have hop := orPath_trans hop_out (Finset.mem_filter.mp hl0).2
          let x : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l0)
          have hx_l : wireVal 26 C (13 + l0.val) x = true := by
            have := wireVal_input (Fin.natAdd 13 l0) x
            simpa [x, Nat.add_comm] using this
          have ht := orPath_sound hop x hx_l
          have hf := hno_lns_only x (fun p' => by
            simp only [x, decide_eq_false_iff_not]
            intro h; have := congrArg Fin.val h; simp at this; omega)
          rw [ht] at hf; cases hf
        · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
          have hcard := (Finset.mem_filter.mp ho).2.2.1
          obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < (pts (26 + o.val)).card)
          have hop := orPath_trans hop_out (Finset.mem_filter.mp hp0).2
          let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p0)
          have hx_p : wireVal 26 C p0.val x = true := by
            have := wireVal_input (Fin.castAdd 13 p0) x
            simpa [x] using this
          have ht := orPath_sound hop x hx_p
          have hf := hno_pts_only x (fun l' => by
            simp only [x, decide_eq_false_iff_not]
            intro h; have := congrArg Fin.val h; simp at this; omega)
          rw [ht] at hf; cases hf
      have hTpt_sum : ∑ p ∈ A, (Tpt_p p).card = Tpt.card :=
        (Finset.card_eq_sum_card_fiberwise (f := centerP) (fun j hj => Finset.mem_image_of_mem centerP hj)).symm
      have hTln_sum : ∑ l ∈ B, (Tln_l l).card = Tln.card :=
        (Finset.card_eq_sum_card_fiberwise (f := centerL) (fun j hj => Finset.mem_image_of_mem centerL hj)).symm
      have hE_sub : E ⊆ A.biUnion (fun p => (E_p p).image (fun l => (p, l))) ∪
          B.biUnion (fun l => (E_l l).image (fun p => (p, l))) := by
        intro e he
        obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
        by_cases h1 : (pSide j).card = 1
        · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
          have hcp : centerP j = e.1 := (hcenterP_eq j hjpt e.1 hpj).symm
          apply Finset.mem_union_left
          refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image.mpr ⟨j, hjpt, hcp⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨e.2, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjpt, hcp⟩, hlj⟩, rfl⟩
        · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
          have hcl : centerL j = e.2 := (hcenterL_eq j hjln e.2 hlj).symm
          apply Finset.mem_union_right
          refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image.mpr ⟨j, hjln, hcl⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨e.1, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjln, hcl⟩, hpj⟩, rfl⟩
      have hE_le_sum : E.card ≤ (∑ p ∈ A, (E_p p).card) + (∑ l ∈ B, (E_l l).card) := by
        calc E.card
            ≤ (A.biUnion (fun p => (E_p p).image (fun l => (p, l))) ∪
                B.biUnion (fun l => (E_l l).image (fun p => (p, l)))).card := Finset.card_le_card hE_sub
          _ ≤ (A.biUnion (fun p => (E_p p).image (fun l => (p, l)))).card +
                (B.biUnion (fun l => (E_l l).image (fun p => (p, l)))).card := Finset.card_union_le _ _
          _ ≤ (∑ p ∈ A, ((E_p p).image (fun l => (p, l))).card) +
                (∑ l ∈ B, ((E_l l).image (fun p => (p, l))).card) :=
              Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
          _ ≤ (∑ p ∈ A, (E_p p).card) + (∑ l ∈ B, (E_l l).card) :=
              Nat.add_le_add
                (Finset.sum_le_sum fun p _ => Finset.card_image_le)
                (Finset.sum_le_sum fun l _ => Finset.card_image_le)
      have hsum_A : ∑ p ∈ A, (E_p p).card ≤ (∑ p ∈ A, (Obot_p p).card) + Tpt.card := by
        calc ∑ p ∈ A, (E_p p).card
            ≤ ∑ p ∈ A, ((Obot_p p).card + (Tpt_p p).card) := Finset.sum_le_sum hEp_bound
          _ = (∑ p ∈ A, (Obot_p p).card) + (∑ p ∈ A, (Tpt_p p).card) := Finset.sum_add_distrib
          _ = (∑ p ∈ A, (Obot_p p).card) + Tpt.card := by rw [hTpt_sum]
      have hsum_B : ∑ l ∈ B, (E_l l).card ≤ (∑ l ∈ B, (Obot_l l).card) + Tln.card := by
        calc ∑ l ∈ B, (E_l l).card
            ≤ ∑ l ∈ B, ((Obot_l l).card + (Tln_l l).card) := Finset.sum_le_sum hEl_bound
          _ = (∑ l ∈ B, (Obot_l l).card) + (∑ l ∈ B, (Tln_l l).card) := Finset.sum_add_distrib
          _ = (∑ l ∈ B, (Obot_l l).card) + Tln.card := by rw [hTln_sum]
      have h3disj : Tstar.card + Obot.card + Otop.card ≤ C.size := by
        have hdisj1 : Disjoint (Tstar ∪ Obot) Otop := by
          rw [Finset.disjoint_union_left]
          exact ⟨hOtop_disj_Tstar.symm, hObot_disj_Otop⟩
        have hcard_u : ((Tstar ∪ Obot) ∪ Otop).card = Tstar.card + Obot.card + Otop.card := by
          rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hObot_disj_Tstar.symm]
        have hle : ((Tstar ∪ Obot) ∪ Otop).card ≤ (Finset.univ : Finset (Fin C.gates.length)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        simp only [Finset.card_univ, Fintype.card_fin] at hle
        change Tstar.card + Obot.card + Otop.card ≤ C.gates.length
        omega
      omega
    · have huncov : ∃ (p l : Fin 13), I p l ∧
          ¬ ∃ (j a b : ℕ), PEqualNP.ReadTwo.andOn C j a b ∧
            PEqualNP.ReadTwo.orp C 26 (26 + j) C.output ∧
            PEqualNP.ReadTwo.orp C 26 p.val a ∧
            PEqualNP.ReadTwo.orp C 26 (13 + l.val) b := by
        by_contra hno
        apply hall
        intro p l hpl
        by_contra hnot
        exact hno ⟨p, l, hpl, hnot⟩
      by_cases hclean : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd C j →
          ∀ x : Fin 26 → Bool,
            PEqualNP.MetaComplexity.circuitFun 26 C x = false →
            PEqualNP.ReadTwo.wval C x (26 + j) = false
      · exact hCleanUncovered C hCAO2 hCsize hdist hC_exact hSle4 huncov hclean
      · have hdirty : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd C j ∧
            ∃ x : Fin 26 → Bool,
              PEqualNP.MetaComplexity.circuitFun 26 C x = false ∧
              PEqualNP.ReadTwo.wval C x (26 + j) = true := by
          by_contra hno
          apply hclean
          intro j hj x hx0
          by_contra hne
          exact hno ⟨j, hj, x, hx0, Bool.eq_true_of_not_eq_false hne⟩
        by_cases honehot : ∃ j : ℕ, PEqualNP.ReadTwo.isAnd C j ∧
            ∃ v : Fin 26, PEqualNP.ReadTwo.wval C (fun i => decide (i = v)) (26 + j) = true
        · exact hDirtyOneHot C hCAO2 hCsize hdist hC_exact hSle4 huncov honehot
        · have hno1 : ∀ j : ℕ, PEqualNP.ReadTwo.isAnd C j →
              ∀ v : Fin 26, PEqualNP.ReadTwo.wval C (fun i => decide (i = v)) (26 + j) = false := by
            intro j hj v
            by_contra hne
            exact honehot ⟨j, hj, v, Bool.eq_true_of_not_eq_false hne⟩
          exact hDirtyNoOneHot C hCAO2 hCsize hdist hC_exact hSle4 huncov hno1 hdirty
